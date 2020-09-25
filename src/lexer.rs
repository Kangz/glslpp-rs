use crate::token::{Location, PreprocessorError, Punct};
use std::convert::TryFrom;
use std::iter::Peekable;

type CharAndLocation = (char, Location);

// GLSL ES 3.20 specification section 3.10. Logical Phases of Compilation
// This iterator implements phases 4 and 5 of the logical phases of compilation:
//
//   4. Each {carriage-return, line-feed} and {line-feed, carriage return} sequence is replaced by
//      a single newline. All remaining carriage-return and line-feed characters are then each
//      replaced by a newline.
//
//   5. Line numbering for each character, which is equal to the number of preceding newlines plus
//      one, is noted. Note this can only be subsequently changed by the #line directive and is not
//      affected by the removal of newlines in phase 6 of compilation.
//
// It expects that phases 1 to 3 are already done and that valid utf8 is passed in.
#[derive(Clone, Copy)]
struct CharsAndLocation<'a> {
    input: &'a str,
    loc: Location,
}

impl<'a> CharsAndLocation<'a> {
    fn new(input: &'a str) -> Self {
        CharsAndLocation {
            input,
            loc: Location { line: 1, pos: 0 },
        }
    }
}

impl<'a> Iterator for CharsAndLocation<'a> {
    type Item = CharAndLocation;

    fn next(&mut self) -> Option<Self::Item> {
        let mut chars = self.input.chars();
        let current = chars.next()?;
        let current_loc = self.loc;

        match current {
            '\n' => {
                // Consume the token but see if we can grab a \r that follows
                self.input = chars.as_str();
                if chars.next() == Some('\r') {
                    self.input = chars.as_str();
                }

                self.loc.line += 1;
                self.loc.pos = 0;
                Some(('\n', current_loc))
            }
            '\r' => {
                // Consume the token but see if we can grab a \r that follows
                self.input = chars.as_str();
                if chars.next() == Some('\n') {
                    self.input = chars.as_str();
                }

                self.loc.line += 1;
                self.loc.pos = 0;
                Some(('\n', current_loc))
            }

            _ => {
                self.input = chars.as_str();

                self.loc.pos += 1;
                Some((current, current_loc))
            }
        }
    }
}

// An iterator that adds stage 6 on top of CharsAndLocation:
//
//  6. Wherever a backslash ('\') occurs immediately before a newline, both are deleted. Note that
//     no whitespace is substituted, thereby allowing a single preprocessing token to span a
//     newline. This operation is not recursive; any new {backslash newline} sequences generated
//     are not removed.
#[derive(Clone, Copy)]
struct SkipBackslashNewline<'a> {
    inner: CharsAndLocation<'a>,
}

impl<'a> SkipBackslashNewline<'a> {
    fn new(input: &'a str) -> Self {
        SkipBackslashNewline {
            inner: CharsAndLocation::new(input),
        }
    }
}

impl<'a> Iterator for SkipBackslashNewline<'a> {
    type Item = CharAndLocation;

    fn next(&mut self) -> Option<Self::Item> {
        let mut current = self.inner.next()?;

        while current.0 == '\\' {
            let mut save_point = self.inner;
            if let Some(('\n', _)) = save_point.next() {
                self.inner = save_point;
                current = self.next()?;
            } else {
                return Some(current);
            }
        }

        Some(current)
    }
}

// An iterator that adds stage 7 on top of SkipBackslashNewline:
//
//   7. All comments are replaced with a single space. All (non-zero) characters and invalid UTF-8
//      byte sequences are allowed within comments. '//' style comments include the initial '//'
//      marker and continue up to, but not including, the terminating newline. '/…/' comments
//      include both the start and end marker.
#[derive(Clone, Copy)]
struct ReplaceComments<'a> {
    inner: SkipBackslashNewline<'a>,
}

impl<'a> ReplaceComments<'a> {
    fn new(input: &'a str) -> Self {
        ReplaceComments {
            inner: SkipBackslashNewline::new(input),
        }
    }
}

impl<'a> Iterator for ReplaceComments<'a> {
    type Item = CharAndLocation;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.inner.next()?;

        if current.0 != '/' {
            return Some(current);
        }

        let mut save_point = self.inner;
        match self.next() {
            // The // case, consume until but not including the next \n
            Some(('/', _)) => {
                save_point = self.inner;
                while let Some((next, _)) = self.inner.next() {
                    if next == '\n' {
                        break;
                    }
                    save_point = self.inner
                }
                self.inner = save_point;
                Some((' ', current.1))
            }

            // The /* case, consume until the next */
            Some(('*', _)) => {
                let mut was_star = false;
                while let Some((next, _)) = self.inner.next() {
                    if was_star && next == '/' {
                        break;
                    }
                    was_star = next == '*';
                }
                Some((' ', current.1))
            }

            // Not // or /*, do nothing
            _ => {
                self.inner = save_point;
                Some(current)
            }
        }
    }
}

// A lexer for GLSL tokens that also emits a couple extra tokens that are useful to the
// preprocessor: # and newlines. It also include metadata for the token for whether it is at the
// start of the line, or if it has leading whitespace.

// A superset of the token value returned by the preprocessor
#[derive(Clone, PartialEq, Debug)]
pub enum TokenValue {
    // Preprocessor specific token values
    Hash,
    NewLine,

    // Regular token values
    Ident(String),
    Int(i32),
    UInt(u32),
    //Float(f32), // TODO
    Punct(Punct),
}

impl From<Punct> for TokenValue {
    fn from(punct: Punct) -> Self {
        TokenValue::Punct(punct)
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct Token {
    pub value: TokenValue,
    pub location: Location,
    pub leading_whitespace: bool,
    pub start_of_line: bool,
}

type LexerItem = Result<Token, (PreprocessorError, Location)>;
pub struct Lexer<'a> {
    inner: Peekable<ReplaceComments<'a>>,
    leading_whitespace: bool,
    start_of_line: bool,
    last_location: Location,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        // TODO bail out on source that is too large.
        Lexer {
            inner: ReplaceComments::new(input).peekable(),
            leading_whitespace: true,
            start_of_line: true,
            last_location: Location { line: 0, pos: 0 },
        }
    }

    fn parse_identifier(&mut self) -> Result<TokenValue, PreprocessorError> {
        let mut identifier = String::default();

        while let Some(&(current, _)) = self.inner.peek() {
            match current {
                'a'..='z' | 'A'..='Z' | '_' | '0'..='9' => {
                    self.inner.next();
                    identifier.push(current);
                }
                _ => {
                    break;
                }
            }
        }

        // TODO check if identifier is larger than the limit.
        Ok(TokenValue::Ident(identifier))
    }

    // Parses the u or U suffix for integers and returns the correct Token variant.
    fn modify_with_integer_suffix(
        &mut self,
        unsigned_value: u32,
    ) -> Result<TokenValue, PreprocessorError> {
        match self.inner.peek() {
            Some(('u', _)) | Some(('U', _)) => {
                self.inner.next();
                Ok(TokenValue::UInt(unsigned_value))
            }
            _ => match i32::try_from(unsigned_value) {
                Err(_) => Err(PreprocessorError::IntegerOverflow),
                Ok(value) => Ok(TokenValue::Int(value)),
            },
        }
    }

    fn parse_number_radix(
        &mut self,
        radix: u32,
        filter: impl Fn(char) -> bool,
    ) -> Result<u32, PreprocessorError> {
        let mut number = String::default();

        while let Some(&(current, _)) = self.inner.peek() {
            if filter(current) {
                self.inner.next();
                number.push(current);
            } else {
                break;
            }
        }

        u32::from_str_radix(&number, radix).map_err(|_err| PreprocessorError::IntegerOverflow)
    }

    fn parse_number(&mut self) -> Result<TokenValue, PreprocessorError> {
        // 0 is used as the first char for non-decimal numbers
        if let Some(('0', _)) = self.inner.peek() {
            self.inner.next();

            let unsigned_value = match self.inner.peek() {
                Some(('x', _)) => {
                    self.inner.next();
                    self.parse_number_radix(16, |c| match c {
                        '0'..='9' | 'a'..='f' | 'A'..='F' => true,
                        _ => false,
                    })?
                }
                Some(('0'..='7', _)) => self.parse_number_radix(8, |c| c >= '0' && c <= '7')?,
                _ => 0u32,
            };

            self.modify_with_integer_suffix(unsigned_value)
        } else {
            let unsigned_value = self.parse_number_radix(10, |c| c >= '0' && c <= '9')?;
            self.modify_with_integer_suffix(unsigned_value)

            //TODO handle floats?
        }
    }

    fn parse_punctuation(&mut self) -> Result<TokenValue, PreprocessorError> {
        let save_point = self.inner.clone();

        let char0 = self.inner.next().map(|(c, _)| c).unwrap_or('\0');
        let char1 = self.inner.next().map(|(c, _)| c).unwrap_or('\0');
        let char2 = self.inner.next().map(|(c, _)| c).unwrap_or('\0');

        let maybe_punct = match (char0, char1, char2) {
            ('<', '<', '=') => Some((Punct::LeftShiftAssign, 3)),
            ('<', '<', _) => Some((Punct::LeftShift, 2)),
            ('<', '=', _) => Some((Punct::LessEqual, 2)),
            ('<', _, _) => Some((Punct::LeftAngle, 1)),

            ('>', '>', '=') => Some((Punct::RightShiftAssign, 3)),
            ('>', '>', _) => Some((Punct::RightShift, 2)),
            ('>', '=', _) => Some((Punct::GreaterEqual, 2)),
            ('>', _, _) => Some((Punct::RightAngle, 1)),

            ('+', '+', _) => Some((Punct::Increment, 2)),
            ('+', '=', _) => Some((Punct::AddAssign, 2)),
            ('+', _, _) => Some((Punct::Plus, 1)),

            ('-', '-', _) => Some((Punct::Decrement, 2)),
            ('-', '=', _) => Some((Punct::SubAssign, 2)),
            ('-', _, _) => Some((Punct::Minus, 1)),

            ('&', '&', _) => Some((Punct::LogicalAnd, 2)),
            ('&', '=', _) => Some((Punct::AndAssign, 2)),
            ('&', _, _) => Some((Punct::Ampersand, 1)),

            ('|', '|', _) => Some((Punct::LogicalOr, 2)),
            ('|', '=', _) => Some((Punct::OrAssign, 2)),
            ('|', _, _) => Some((Punct::Pipe, 1)),

            ('^', '^', _) => Some((Punct::LogicalXor, 2)),
            ('^', '=', _) => Some((Punct::XorAssign, 2)),
            ('^', _, _) => Some((Punct::Caret, 1)),

            ('=', '=', _) => Some((Punct::EqualEqual, 2)),
            ('=', _, _) => Some((Punct::Equal, 1)),
            ('!', '=', _) => Some((Punct::NotEqual, 2)),
            ('!', _, _) => Some((Punct::Bang, 1)),

            ('*', '=', _) => Some((Punct::MulAssign, 2)),
            ('*', _, _) => Some((Punct::Star, 1)),
            ('/', '=', _) => Some((Punct::DivAssign, 2)),
            ('/', _, _) => Some((Punct::Slash, 1)),
            ('%', '=', _) => Some((Punct::ModAssign, 2)),
            ('%', _, _) => Some((Punct::Percent, 1)),

            ('(', _, _) => Some((Punct::LeftParen, 1)),
            (')', _, _) => Some((Punct::RightParen, 1)),
            ('{', _, _) => Some((Punct::LeftBrace, 1)),
            ('}', _, _) => Some((Punct::RightBrace, 1)),
            ('[', _, _) => Some((Punct::LeftBracket, 1)),
            (']', _, _) => Some((Punct::RightBracket, 1)),

            ('.', _, _) => Some((Punct::Dot, 1)),
            (',', _, _) => Some((Punct::Comma, 1)),
            (';', _, _) => Some((Punct::Semicolon, 1)),
            (':', _, _) => Some((Punct::Colon, 1)),
            ('~', _, _) => Some((Punct::Tilde, 1)),
            ('?', _, _) => Some((Punct::Question, 1)),

            _ => None,
        };

        if let Some((punct, size)) = maybe_punct {
            self.inner = save_point;
            for _i in 0..size {
                self.inner.next();
            }
            Ok(punct.into())
        } else if char0 == '#' {
            self.inner = save_point;
            self.inner.next();
            Ok(TokenValue::Hash)
        } else {
            Err(PreprocessorError::UnexpectedCharacter)
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = LexerItem;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(&(current_char, current_loc)) = self.inner.peek() {
            let had_leading_whitespace = self.leading_whitespace;
            self.leading_whitespace = false;

            let was_start_of_line = self.start_of_line;
            self.start_of_line = false;

            let value = match current_char {
                ' ' | '\t' | '\x0b' | '\x0c' => {
                    self.start_of_line = was_start_of_line;
                    self.leading_whitespace = true;
                    self.inner.next();
                    continue;
                }
                '\n' => {
                    self.leading_whitespace = true;
                    self.start_of_line = true;
                    self.inner.next();
                    Ok(TokenValue::NewLine)
                }

                'a'..='z' | 'A'..='Z' | '_' => self.parse_identifier(),
                '0'..='9' => self.parse_number(),
                // TODO handle .float
                _ => self.parse_punctuation(),
            };

            self.last_location = current_loc;

            return Some(value.map_err(|e| (e, current_loc)).map(|t| Token {
                value: t,
                location: current_loc,
                leading_whitespace: had_leading_whitespace,
                start_of_line: was_start_of_line,
            }));
        }

        // Do the C hack of always ending with a newline so that preprocessor directives are ended.
        if !self.start_of_line {
            self.start_of_line = true;

            self.last_location.pos += 1;
            Some(Ok(Token {
                value: TokenValue::NewLine,
                location: self.last_location,
                leading_whitespace: self.leading_whitespace,
                start_of_line: false,
            }))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn c(line: u32, pos: u32, c: char) -> Option<(char, Location)> {
        Some((c, Location { line, pos }))
    }

    fn unwrap_token(item: Option<LexerItem>) -> Token {
        item.unwrap().unwrap()
    }

    fn unwrap_token_value(item: Option<LexerItem>) -> TokenValue {
        unwrap_token(item).value
    }

    fn unwrap_error(item: Option<LexerItem>) -> PreprocessorError {
        item.unwrap().unwrap_err().0
    }

    fn expect_lexer_end(lexer: &mut Lexer) {
        assert_eq!(unwrap_token_value(lexer.next()), TokenValue::NewLine);
        assert_eq!(lexer.next(), None);
    }

    #[test]
    fn chars_and_location() {
        // Test handling of characters in a line.
        let mut it = CharsAndLocation::new("abc");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, 'b'));
        assert_eq!(it.next(), c(1, 2, 'c'));
        assert_eq!(it.next(), None);

        // Test handling of \n in the regular case.
        let mut it = CharsAndLocation::new("a\nb");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, '\n'));
        assert_eq!(it.next(), c(2, 0, 'b'));
        assert_eq!(it.next(), None);

        // Test handling of \r in the regular case.
        let mut it = CharsAndLocation::new("a\rb");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, '\n'));
        assert_eq!(it.next(), c(2, 0, 'b'));
        assert_eq!(it.next(), None);

        // Test handling of \n\r.
        let mut it = CharsAndLocation::new("a\n\rb");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, '\n'));
        assert_eq!(it.next(), c(2, 0, 'b'));
        assert_eq!(it.next(), None);

        // Test handling of \r\n.
        let mut it = CharsAndLocation::new("a\r\nb");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, '\n'));
        assert_eq!(it.next(), c(2, 0, 'b'));
        assert_eq!(it.next(), None);

        // Test handling of a mix of \r and \n
        let mut it = CharsAndLocation::new("\n\r\n\r\r\r\n");
        assert_eq!(it.next(), c(1, 0, '\n'));
        assert_eq!(it.next(), c(2, 0, '\n'));
        assert_eq!(it.next(), c(3, 0, '\n'));
        assert_eq!(it.next(), c(4, 0, '\n'));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn skip_backslash_newline() {
        // Test a simple case.
        let mut it = SkipBackslashNewline::new("a\\\nb");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(2, 0, 'b'));
        assert_eq!(it.next(), None);

        // Test a double case that requires the loop in the algorithm.
        let mut it = SkipBackslashNewline::new("a\\\n\\\nb");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(3, 0, 'b'));
        assert_eq!(it.next(), None);

        // Test a backslash on its own
        let mut it = SkipBackslashNewline::new("a\\b");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, '\\'));
        assert_eq!(it.next(), c(1, 2, 'b'));
        assert_eq!(it.next(), None);

        // Test a case just before EOF
        let mut it = SkipBackslashNewline::new("\\\n");
        assert_eq!(it.next(), None);
    }

    #[test]
    fn replace_comments() {
        // Test a slash that's not a comment
        let mut it = ReplaceComments::new("a/b");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, '/'));
        assert_eq!(it.next(), c(1, 2, 'b'));
        assert_eq!(it.next(), None);

        // Test a slash with nothing afterwards
        let mut it = ReplaceComments::new("a/");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, '/'));
        assert_eq!(it.next(), None);

        // Test a single-line comment
        let mut it = ReplaceComments::new("a//foo\nb");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, ' '));
        assert_eq!(it.next(), c(1, 6, '\n'));
        assert_eq!(it.next(), c(2, 0, 'b'));
        assert_eq!(it.next(), None);

        // Test a single-line comment without an ending newline
        let mut it = ReplaceComments::new("//foo");
        assert_eq!(it.next(), c(1, 0, ' '));
        assert_eq!(it.next(), None);

        // Test a single-line comment without nothing afterwards
        let mut it = ReplaceComments::new("//");
        assert_eq!(it.next(), c(1, 0, ' '));
        assert_eq!(it.next(), None);

        // Test a single-line comment with a line continuation
        let mut it = ReplaceComments::new("//foo\\\na");
        assert_eq!(it.next(), c(1, 0, ' '));
        assert_eq!(it.next(), None);

        // Test a single-line comment with a line continuation
        let mut it = ReplaceComments::new("//foo\\\na");
        assert_eq!(it.next(), c(1, 0, ' '));
        assert_eq!(it.next(), None);

        // Test a multi-line comment
        let mut it = ReplaceComments::new("a/*fo\n\no*/b");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, ' '));
        assert_eq!(it.next(), c(3, 3, 'b'));
        assert_eq!(it.next(), None);

        // Test a multi-line comment, without a proper ending (only the *)
        let mut it = ReplaceComments::new("a/*fo\n\no*");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, ' '));
        assert_eq!(it.next(), None);

        // Test a multi-line comment, without a proper ending (nothing)
        let mut it = ReplaceComments::new("a/*fo\n\no");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, ' '));
        assert_eq!(it.next(), None);

        // Test a multi-line comment, or /*/ not being a complete one
        let mut it = ReplaceComments::new("a/*/b");
        assert_eq!(it.next(), c(1, 0, 'a'));
        assert_eq!(it.next(), c(1, 1, ' '));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn lex_whitespace() {
        // Empty input gives nothing.
        let mut it = Lexer::new("");
        assert_eq!(it.next(), None);

        // Pure whitespace give nothing too
        let mut it = Lexer::new("/**/\t //a");
        assert_eq!(it.next(), None);
    }

    #[test]
    fn lex_newline() {
        let mut it = Lexer::new("\r\n\n");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
        assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
        assert_eq!(it.next(), None);

        // Check a newline is added only if the last token wasn't a newline
        let mut it = Lexer::new("\r\n\n\t/**/ //");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
        expect_lexer_end(&mut it);

        let mut it = Lexer::new("\r\n\n#");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
        assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Hash);
        assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn lex_hash() {
        let mut it = Lexer::new("a#b");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("a".to_string())
        );
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Hash);
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("b".to_string())
        );
        expect_lexer_end(&mut it);
    }

    #[test]
    fn lex_metadata() {
        // Test the metadata of the first token
        let mut it = Lexer::new("1");
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: TokenValue::Int(1),
                location: Location { line: 1, pos: 0 },
                leading_whitespace: true,
                start_of_line: true
            }
        );
        expect_lexer_end(&mut it);

        // Test various whitespaces are recognized (or lack of)
        let mut it = Lexer::new(" 1/*\n*/2\t3+\n4");
        // 1 is the first token and the whitespace doesn't prevent it from being the start of the
        // line
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: TokenValue::Int(1),
                location: Location { line: 1, pos: 1 },
                leading_whitespace: true,
                start_of_line: true
            }
        );
        // 2 is not at the start of the line because the \n in the /**/ doesn't count, however its
        // location correctly lists the second line.
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: TokenValue::Int(2),
                location: Location { line: 2, pos: 2 },
                leading_whitespace: true,
                start_of_line: false
            }
        );
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: TokenValue::Int(3),
                location: Location { line: 2, pos: 4 },
                leading_whitespace: true,
                start_of_line: false
            }
        );
        // + doesn't have a leading whitespace
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: Punct::Plus.into(),
                location: Location { line: 2, pos: 5 },
                leading_whitespace: false,
                start_of_line: false
            }
        );
        // The newline is correctly tagged on the preceeding line
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: TokenValue::NewLine,
                location: Location { line: 2, pos: 6 },
                leading_whitespace: false,
                start_of_line: false
            }
        );
        // 4 is after a newline that correctly sets start_of_line
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: TokenValue::Int(4),
                location: Location { line: 3, pos: 0 },
                leading_whitespace: true,
                start_of_line: true
            }
        );
        // The final newline added by the lexer is at the correct position
        assert_eq!(
            unwrap_token(it.next()),
            Token {
                value: TokenValue::NewLine,
                location: Location { line: 3, pos: 1 },
                leading_whitespace: false,
                start_of_line: false
            }
        );
        assert_eq!(it.next(), None);
    }

    #[test]
    fn lex_identifiers() {
        // Test some basic identifier cases
        let mut it = Lexer::new("foo BA_R baz0");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("foo".to_string())
        );
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("BA_R".to_string())
        );
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("baz0".to_string())
        );
        expect_lexer_end(&mut it);

        // Test _ is a valid identifier
        let mut it = Lexer::new("_");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("_".to_string())
        );
        expect_lexer_end(&mut it);

        // Test that identifiers are not split by escaped newlines
        let mut it = Lexer::new("a\\\nb");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("ab".to_string())
        );
        expect_lexer_end(&mut it);

        // Test that identifiers are split by other whitespace like /**/
        let mut it = Lexer::new("a/**/b");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("a".to_string())
        );
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("b".to_string())
        );
        expect_lexer_end(&mut it);
    }

    #[test]
    fn lex_decimal() {
        // Test some basic cases
        let mut it = Lexer::new("1 0u 42 65536U");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(1));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::UInt(0));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(42));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::UInt(65536));
        expect_lexer_end(&mut it);

        // Test splitting with identifiers
        let mut it = Lexer::new("31ab");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(31));
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("ab".to_string())
        );
        expect_lexer_end(&mut it);

        // Test splitting with whitespace
        let mut it = Lexer::new("31/**/32");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(31));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(32));
        expect_lexer_end(&mut it);

        // Test splitting with punctuation
        let mut it = Lexer::new("31+32");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(31));
        assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(32));
        expect_lexer_end(&mut it);

        // Test 2^31 - 1 works in signed mode.
        let mut it = Lexer::new("2147483647");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(2147483647));
        expect_lexer_end(&mut it);

        // Test 2^31 signed overflows and is an error
        let mut it = Lexer::new("2147483648");
        assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);

        // Test 2^31 works in unsigned mode
        let mut it = Lexer::new("2147483648u");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::UInt(2147483648u32)
        );
        expect_lexer_end(&mut it);

        // Test 2^32 - 1 works in unsigned mode.
        let mut it = Lexer::new("4294967295u");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::UInt(4294967295u32)
        );
        expect_lexer_end(&mut it);

        // Test 2^32 unsigned overflows and is an error
        let mut it = Lexer::new("4294967296u");
        assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);
    }

    #[test]
    fn lex_hexadecimal() {
        // Test some basic cases
        let mut it = Lexer::new("0x1 0x0u 0xBaFfe 0xcaFeU");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(1));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::UInt(0));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(0xBAFFE));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::UInt(0xCAFE));
        expect_lexer_end(&mut it);

        // Test with redundant zeroes
        let mut it = Lexer::new("0x000 0x000000000000001");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(0));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(1));
        expect_lexer_end(&mut it);

        // Test splitting with identifiers
        let mut it = Lexer::new("0x31zb");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(0x31));
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("zb".to_string())
        );
        expect_lexer_end(&mut it);

        // Test splitting with whitespace
        let mut it = Lexer::new("0x31/**/32");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(0x31));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(32));
        expect_lexer_end(&mut it);

        // Test splitting with punctuation
        let mut it = Lexer::new("0x31+32");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(0x31));
        assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(32));
        expect_lexer_end(&mut it);

        // Test 2^31 - 1 works in signed mode.
        let mut it = Lexer::new("0x7FFFFFFF");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(2147483647));
        expect_lexer_end(&mut it);

        // Test 2^31 signed overflows and is an error
        let mut it = Lexer::new("0x80000000");
        assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);

        // Test 2^31 works in unsigned mode
        let mut it = Lexer::new("0x80000000u");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::UInt(2147483648u32)
        );
        expect_lexer_end(&mut it);

        // Test 2^32 - 1 works in unsigned mode.
        let mut it = Lexer::new("0xFFFFFFFFu");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::UInt(4294967295u32)
        );
        expect_lexer_end(&mut it);

        // Test 2^32 unsigned overflows and is an error
        let mut it = Lexer::new("0x100000000u");
        assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);
    }

    #[test]
    fn lex_octal() {
        // Test some basic cases
        let mut it = Lexer::new("01 00u 07654 01234u");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(1));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::UInt(0));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(4012));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::UInt(668));
        expect_lexer_end(&mut it);

        // Test with redundant zeroes
        let mut it = Lexer::new("0000 0000000000000001");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(0));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(1));
        expect_lexer_end(&mut it);

        // Test splitting with identifiers
        let mut it = Lexer::new("031zb");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(25));
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("zb".to_string())
        );
        expect_lexer_end(&mut it);

        // Test splitting with whitespace
        let mut it = Lexer::new("031/**/32");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(25));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(32));
        expect_lexer_end(&mut it);

        // Test splitting with 8 and 9
        let mut it = Lexer::new("039 038");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(3));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(9));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(3));
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(8));
        expect_lexer_end(&mut it);

        // Test splitting with punctuation
        let mut it = Lexer::new("031+32");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(25));
        assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(32));
        expect_lexer_end(&mut it);

        // Test 2^31 - 1 works in signed mode.
        let mut it = Lexer::new("017777777777");
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(2147483647));
        expect_lexer_end(&mut it);

        // Test 2^31 signed overflows and is an error
        let mut it = Lexer::new("020000000000");
        assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);

        // Test 2^31 works in unsigned mode
        let mut it = Lexer::new("020000000000u");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::UInt(2147483648u32)
        );
        expect_lexer_end(&mut it);

        // Test 2^32 - 1 works in unsigned mode.
        let mut it = Lexer::new("037777777777u");
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::UInt(4294967295u32)
        );
        expect_lexer_end(&mut it);

        // Test 2^32 unsigned overflows and is an error
        let mut it = Lexer::new("040000000000u");
        assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);
    }

    #[test]
    fn lex_punctuation() {
        // Test parsing some of the token (but not all, that'd be too many tests!)
        let mut it = Lexer::new("+ != <<=");
        assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
        assert_eq!(unwrap_token_value(it.next()), Punct::NotEqual.into());
        assert_eq!(unwrap_token_value(it.next()), Punct::LeftShiftAssign.into());
        expect_lexer_end(&mut it);

        // Test parsing a token that's a prefix of another one just before EOF
        let mut it = Lexer::new("<");
        assert_eq!(unwrap_token_value(it.next()), Punct::LeftAngle.into());
        expect_lexer_end(&mut it);

        // Test \\\n doesn't split the token
        let mut it = Lexer::new("=\\\n=");
        assert_eq!(unwrap_token_value(it.next()), Punct::EqualEqual.into());
        expect_lexer_end(&mut it);

        // Test whitespace splits the token
        let mut it = Lexer::new("+/**/=");
        assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
        assert_eq!(unwrap_token_value(it.next()), Punct::Equal.into());
        expect_lexer_end(&mut it);

        // Test a number stops processing the token
        let mut it = Lexer::new("!1");
        assert_eq!(unwrap_token_value(it.next()), Punct::Bang.into());
        assert_eq!(unwrap_token_value(it.next()), TokenValue::Int(1));
        expect_lexer_end(&mut it);

        // Test an identifier stops processing the token
        let mut it = Lexer::new("&a");
        assert_eq!(unwrap_token_value(it.next()), Punct::Ampersand.into());
        assert_eq!(
            unwrap_token_value(it.next()),
            TokenValue::Ident("a".to_string())
        );
        expect_lexer_end(&mut it);

        // Test whitespace splits the token
        let mut it = Lexer::new(">/**/>");
        assert_eq!(unwrap_token_value(it.next()), Punct::RightAngle.into());
        assert_eq!(unwrap_token_value(it.next()), Punct::RightAngle.into());
        expect_lexer_end(&mut it);

        // Test that tokens are parsed greedily: `a+++++b` is `a ++ ++ + b` (invalid GLSL) and not
        // `(a ++) + (++ b)` (valid GLSL)
        let mut it = Lexer::new("+++++");
        assert_eq!(unwrap_token_value(it.next()), Punct::Increment.into());
        assert_eq!(unwrap_token_value(it.next()), Punct::Increment.into());
        assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
        expect_lexer_end(&mut it);

        // Test that an invalid char produces and error
        let mut it = Lexer::new("@");
        assert_eq!(
            unwrap_error(it.next()),
            PreprocessorError::UnexpectedCharacter
        );
    }

    // TODO test has_whitespace
}
