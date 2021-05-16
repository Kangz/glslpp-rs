use crate::token::{Float, Integer, Location, PreprocessorError, Punct};
use std::{iter::Peekable, str::Chars};
use unicode_xid::UnicodeXID;

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
#[derive(Clone)]
pub struct CharsAndLocation<'a> {
    chars: Peekable<Chars<'a>>,
    loc: Location,
}

impl<'a> CharsAndLocation<'a> {
    pub fn new(input: &'a str) -> Self {
        CharsAndLocation {
            chars: input.chars().peekable(),
            loc: Location::default(),
        }
    }
}

impl<'a> Iterator for CharsAndLocation<'a> {
    type Item = CharAndLocation;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.chars.next()?;
        self.loc.start = self.loc.end;
        self.loc.end += current.len_utf8() as u32;

        match current {
            '\n' => {
                // Consume the token but see if we can grab a \r that follows
                if self.chars.peek() == Some(&'\r') {
                    self.chars.next();
                    self.loc.end += 1;
                }

                let res = Some(('\n', self.loc));
                self.loc.line += 1;
                res
            }
            '\r' => {
                // Consume the token but see if we can grab a \n that follows
                if self.chars.peek() == Some(&'\n') {
                    self.chars.next();
                    self.loc.end += 1;
                }

                let res = Some(('\n', self.loc));
                self.loc.line += 1;
                res
            }

            _ => Some((current, self.loc)),
        }
    }
}

// An iterator that adds stage 6 on top of CharsAndLocation:
//
//  6. Wherever a backslash ('\') occurs immediately before a newline, both are deleted. Note that
//     no whitespace is substituted, thereby allowing a single preprocessing token to span a
//     newline. This operation is not recursive; any new {backslash newline} sequences generated
//     are not removed.
#[derive(Clone)]
pub struct SkipBackslashNewline<'a> {
    inner: CharsAndLocation<'a>,
}

impl<'a> SkipBackslashNewline<'a> {
    pub fn new(input: &'a str) -> Self {
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
            let mut save_point = self.inner.clone();
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
#[derive(Clone)]
pub struct ReplaceComments<'a> {
    inner: SkipBackslashNewline<'a>,
}

// The lexer wants to know when whitespace is a comment to know if a comment was ever processed.
// To avoid adding state we use a sentinel value of '\r' because all '\r' have been consumed and
// turned into '\n' by CharsAndLocation.
pub const COMMENT_SENTINEL_VALUE: char = '\r';

impl<'a> ReplaceComments<'a> {
    pub fn new(input: &'a str) -> Self {
        ReplaceComments {
            inner: SkipBackslashNewline::new(input),
        }
    }
}

impl<'a> Iterator for ReplaceComments<'a> {
    type Item = CharAndLocation;

    fn next(&mut self) -> Option<Self::Item> {
        let mut current = self.inner.next()?;

        if current.0 != '/' {
            debug_assert!(current.0 != COMMENT_SENTINEL_VALUE);
            return Some(current);
        }

        let mut save_point = self.inner.clone();
        match self.next() {
            // The // case, consume until but not including the next \n
            Some(('/', _)) => {
                current.1.end += 1;

                save_point = self.inner.clone();
                while let Some((next, loc)) = self.inner.next() {
                    if next == '\n' {
                        current.1.end = loc.start;
                        break;
                    }
                    current.1.end = loc.end;
                    save_point = self.inner.clone()
                }
                self.inner = save_point;

                Some((COMMENT_SENTINEL_VALUE, current.1))
            }

            // The /* case, consume until the next */
            Some(('*', _)) => {
                current.1.end += 1;

                let mut was_star = false;
                while let Some((next, loc)) = self.inner.next() {
                    current.1.end = loc.end;
                    if was_star && next == '/' {
                        break;
                    }
                    was_star = next == '*';
                }

                Some((COMMENT_SENTINEL_VALUE, current.1))
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
    Integer(Integer),
    Float(Float),
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

pub type LexerItem = Result<Token, (PreprocessorError, Location)>;
pub struct Lexer<'a> {
    inner: Peekable<ReplaceComments<'a>>,
    leading_whitespace: bool,
    start_of_line: bool,
    last_location: Location,
    had_comments: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        // TODO bail out on source that is too large.
        Lexer {
            inner: ReplaceComments::new(input).peekable(),
            leading_whitespace: true,
            start_of_line: true,
            last_location: Location::default(),
            had_comments: false,
        }
    }

    pub fn had_comments(&self) -> bool {
        self.had_comments
    }

    // TODO: Make a runtime flag to toggle unicode identifiers support
    // The glsl spec only allows ascii identifiers
    fn parse_identifier(&mut self) -> Result<TokenValue, PreprocessorError> {
        let mut identifier = String::default();

        if self
            .inner
            .peek()
            .map_or(false, |c| c.0.is_xid_start() || c.0 == '_')
        {
            identifier.push(self.inner.next().unwrap().0);
        }

        let rest = self.consume_chars(|c| c.is_xid_continue());
        identifier.push_str(&rest);

        // TODO check if identifier is larger than the limit.
        Ok(TokenValue::Ident(identifier))
    }

    fn parse_integer_signedness_suffix(&mut self) -> bool {
        match self.inner.peek() {
            Some(&('u', loc)) | Some(&('U', loc)) => {
                self.inner.next();
                self.last_location.end = loc.end;
                false
            }
            _ => true,
        }
    }

    fn parse_integer_width_suffix(&mut self) -> Result<i32, PreprocessorError> {
        match self.inner.peek() {
            Some(('l', _)) | Some(('L', _)) => Err(PreprocessorError::NotSupported64BitLiteral),
            Some(('s', _)) | Some(('S', _)) => Err(PreprocessorError::NotSupported16BitLiteral),
            _ => Ok(32),
        }
    }

    fn parse_float_width_suffix(&mut self) -> Result<i32, PreprocessorError> {
        match self.inner.peek() {
            Some(('l', _)) | Some(('L', _)) => Err(PreprocessorError::NotSupported64BitLiteral),
            Some(('h', _)) | Some(('H', _)) => Err(PreprocessorError::NotSupported16BitLiteral),
            Some(&('f', loc)) | Some(&('F', loc)) => {
                self.inner.next();
                self.last_location.end = loc.end;
                Ok(32)
            }
            _ => Ok(32),
        }
    }

    fn consume_chars(&mut self, filter: impl Fn(char) -> bool) -> String {
        let mut result: String = Default::default();

        while let Some(&(current, loc)) = self.inner.peek() {
            if filter(current) {
                self.inner.next();
                self.last_location.end = loc.end;
                result.push(current);
            } else {
                break;
            }
        }

        result
    }

    fn parse_number(&mut self, first_char: char) -> Result<TokenValue, PreprocessorError> {
        let mut is_float = false;
        let mut integer_radix = 10;
        let mut raw: String = Default::default();
        raw.push(first_char);

        // Handle hexadecimal numbers that needs to consume a..f in addition to digits.
        if first_char == '0' {
            match self.inner.peek() {
                Some(&('x', loc)) | Some(&('X', loc)) => {
                    self.inner.next();
                    self.last_location.end = loc.end;

                    raw += &self.consume_chars(|c| matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F'));
                    integer_radix = 16;
                }

                // Octal numbers can also be the prefix of floats, so we need to parse all digits
                // and not just 0..7 in case it is a float like 00009.0f, the parsing of all digits
                // is done below, but we still need to remember the radix.
                Some(('0'..='9', _)) => {
                    integer_radix = 8;
                }
                _ => {}
            };
        }

        if first_char == '.' {
            is_float = true;
        } else {
            // Parse any digits at the end of integers, or for the non-fractional part of floats.
            raw += &self.consume_chars(|c| ('0'..='9').contains(&c));

            if let Some(&('.', loc)) = self.inner.peek() {
                self.inner.next();
                self.last_location.end = loc.end;
                raw.push('.');
                is_float = true;
            }
        }

        // At this point either we're an integer missing only suffixes, or we're a float with
        // everything up to the . consumed.
        if is_float {
            raw += &self.consume_chars(|c| ('0'..='9').contains(&c));
        }

        // Handle scientific notation with a (e|E)(+|-|)\d+ suffix when we're a float or an
        // an integer that could turn into a float if we add a exponent to it (so 0x1E-1
        // isn't recognized as a float).
        if (is_float || integer_radix == 8 || integer_radix == 10)
            && matches!(self.inner.peek(), Some(('e', _)) | Some(('E', _)))
        {
            self.inner.next();
            raw.push('e');
            is_float = true;

            match self.inner.peek() {
                Some(('+', _)) => {
                    self.inner.next();
                    raw.push('+');
                }
                Some(('-', _)) => {
                    self.inner.next();
                    raw.push('-');
                }
                _ => {}
            }

            // TODO: what should we do when there is no number after the exponent?
            raw += &self.consume_chars(|c| ('0'..='9').contains(&c));
        }

        if is_float {
            // TODO: Depending on the GLSL version make it an error to not have the suffix.
            let width = self.parse_float_width_suffix()?;

            Ok(TokenValue::Float(Float {
                value: raw
                    .parse::<f32>()
                    .map_err(|_| PreprocessorError::FloatParsingError)?,
                width,
            }))
        } else {
            let signed = self.parse_integer_signedness_suffix();
            let width = self.parse_integer_width_suffix()?;

            // Skip the initial 0 in hexa or octal (in hexa we never added the 'x').
            if integer_radix != 10 {
                raw = raw.split_off(1);
            }

            Ok(TokenValue::Integer(Integer {
                value: u64::from_str_radix(&raw, integer_radix)
                    .map_err(|_err| PreprocessorError::IntegerOverflow)?,
                signed,
                width,
            }))
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
            for _ in 0..size {
                self.inner.next();
            }
            self.last_location.end += size - 1;
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

            self.last_location = current_loc;

            let value = match current_char {
                ' ' | '\t' | '\x0b' | '\x0c' | COMMENT_SENTINEL_VALUE => {
                    if current_char == COMMENT_SENTINEL_VALUE {
                        self.had_comments = true;
                    }
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

                c @ '0'..='9' => {
                    self.inner.next();
                    self.parse_number(c)
                }

                // Special case . as a punctuation because it can be the start of a float.
                '.' => {
                    self.inner.next();

                    match self.inner.peek() {
                        Some(('0'..='9', _)) => self.parse_number('.'),
                        _ => Ok(TokenValue::Punct(Punct::Dot)),
                    }
                }
                _ => {
                    // TODO: see todo in `parse_identifier` for information
                    if current_char.is_xid_start() || current_char == '_' {
                        self.parse_identifier()
                    } else {
                        self.parse_punctuation()
                    }
                }
            };

            return Some(value.map_err(|e| (e, current_loc)).map(|t| Token {
                value: t,
                location: self.last_location,
                leading_whitespace: had_leading_whitespace,
                start_of_line: was_start_of_line,
            }));
        }

        // Do the C hack of always ending with a newline so that preprocessor directives are ended.
        if !self.start_of_line {
            self.start_of_line = true;
            self.last_location.start = self.last_location.end;

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
