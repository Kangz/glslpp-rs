use super::lexer::{
    CharsAndLine, Lexer, LexerItem, ReplaceComments, SkipBackslashNewline, Token, TokenValue,
    COMMENT_SENTINEL_VALUE,
};
use super::token::{Location, PreprocessorError, Punct};
use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;
use core::ops::Range;

fn c(c: char, line: u32) -> Option<(char, u32)> {
    Some((c, line))
}

fn l(line: u32, pos: Range<u32>) -> Location {
    Location {
        line,
        start: pos.start,
        end: pos.end,
    }
}

fn unwrap_token(item: Option<LexerItem>) -> Token {
    item.unwrap().unwrap()
}

fn unwrap_token_value(item: Option<LexerItem>) -> TokenValue {
    unwrap_token(item).value
}

fn lexed_token_values(s: &str) -> Vec<TokenValue> {
    let mut tokens: Vec<TokenValue> = Lexer::new(s).map(|t| t.unwrap().value).collect();
    assert_eq!(tokens.pop(), Some(TokenValue::NewLine));
    tokens
}

fn unwrap_error(item: Option<LexerItem>) -> PreprocessorError {
    item.unwrap().unwrap_err().0
}

fn expect_lexer_end(lexer: &mut Lexer) {
    assert_eq!(unwrap_token_value(lexer.next()), TokenValue::NewLine);
    assert_eq!(lexer.next(), None);
}

fn make_ident(s: &str) -> TokenValue {
    TokenValue::Ident(s.to_string())
}

fn make_integer(s: &str) -> TokenValue {
    TokenValue::Integer(s.to_string())
}

fn make_float(s: &str) -> TokenValue {
    TokenValue::Float(s.to_string())
}

#[test]
fn chars_and_location() {
    // Test handling of characters in a line.
    let mut it = CharsAndLine::new("abc");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('b', 1));
    assert_eq!(it.next(), c('c', 1));
    assert_eq!(it.next(), None);

    // Test handling of \n in the regular case.
    let mut it = CharsAndLine::new("a\nb");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('\n', 1));
    assert_eq!(it.next(), c('b', 2));
    assert_eq!(it.next(), None);

    // Test handling of \r in the regular case.
    let mut it = CharsAndLine::new("a\rb");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('\n', 1));
    assert_eq!(it.next(), c('b', 2));
    assert_eq!(it.next(), None);

    // Test handling of \n\r.
    let mut it = CharsAndLine::new("a\n\rb");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('\n', 1));
    assert_eq!(it.next(), c('b', 2));
    assert_eq!(it.next(), None);

    // Test handling of \r\n.
    let mut it = CharsAndLine::new("a\r\nb");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('\n', 1));
    assert_eq!(it.next(), c('b', 2));
    assert_eq!(it.next(), None);

    // Test handling of a mix of \r and \n
    let mut it = CharsAndLine::new("\n\r\n\r\r\r\n");
    assert_eq!(it.next(), c('\n', 1));
    assert_eq!(it.next(), c('\n', 2));
    assert_eq!(it.next(), c('\n', 3));
    assert_eq!(it.next(), c('\n', 4));
    assert_eq!(it.next(), None);

    // Unicode handling
    let mut it = CharsAndLine::new("a→üs🦀");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('→', 1));
    assert_eq!(it.next(), c('ü', 1));
    assert_eq!(it.next(), c('s', 1));
    assert_eq!(it.next(), c('🦀', 1));
    assert_eq!(it.next(), None);
}

#[test]
fn skip_backslash_newline() {
    // Test a simple case.
    let mut it = SkipBackslashNewline::new("a\\\nb");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('b', 2));
    assert_eq!(it.next(), None);

    // Test a double case that requires the loop in the algorithm.
    let mut it = SkipBackslashNewline::new("a\\\n\\\nb");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('b', 3));
    assert_eq!(it.next(), None);

    // Test a backslash on its own
    let mut it = SkipBackslashNewline::new("a\\b");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('\\', 1));
    assert_eq!(it.next(), c('b', 1));
    assert_eq!(it.next(), None);

    // Test a case just before EOF
    let mut it = SkipBackslashNewline::new("\\\n");
    assert_eq!(it.next(), None);
}

#[test]
fn replace_comments() {
    // Test a slash that's not a comment
    let mut it = ReplaceComments::new("a/b");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('/', 1));
    assert_eq!(it.next(), c('b', 1));
    assert_eq!(it.next(), None);

    // Test a slash with nothing afterwards
    let mut it = ReplaceComments::new("a/");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c('/', 1));
    assert_eq!(it.next(), None);

    // Test a single-line comment
    let mut it = ReplaceComments::new("a//foo\nb");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
    assert_eq!(it.next(), c('\n', 1));
    assert_eq!(it.next(), c('b', 2));
    assert_eq!(it.next(), None);

    // Test a single-line comment without an ending newline
    let mut it = ReplaceComments::new("//foo");
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
    assert_eq!(it.next(), None);

    // Test a single-line comment without nothing afterwards
    let mut it = ReplaceComments::new("//");
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
    assert_eq!(it.next(), None);

    // Test a single-line comment with a line continuation
    let mut it = ReplaceComments::new("//foo\\\na");
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
    assert_eq!(it.next(), None);

    // Test a multi-line comment
    let mut it = ReplaceComments::new("a/*fo\n\no*/b");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
    assert_eq!(it.next(), c('b', 3));
    assert_eq!(it.next(), None);

    // Test a multi-line comment, without a proper ending (only the *)
    let mut it = ReplaceComments::new("a/*fo\n\no*");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
    assert_eq!(it.next(), None);

    // Test a multi-line comment, without a proper ending (nothing)
    let mut it = ReplaceComments::new("a/*fo\n\no");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
    assert_eq!(it.next(), None);

    // Test a multi-line comment, or /*/ not being a complete one
    let mut it = ReplaceComments::new("a/*/b");
    assert_eq!(it.next(), c('a', 1));
    assert_eq!(it.next(), c(COMMENT_SENTINEL_VALUE, 1));
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
    // (lexed_token_values consumes the last newline)
    assert_eq!(lexed_token_values("\r\n\n"), vec![TokenValue::NewLine]);

    // Check a newline is added only if the last token wasn't a newline
    // (lexed_token_values consumes the last newline)
    assert_eq!(
        lexed_token_values("\r\n\n\t/**/ //"),
        vec![TokenValue::NewLine]
    );

    assert_eq!(
        lexed_token_values("r\n\n#"),
        vec![
            make_ident("r"),
            TokenValue::NewLine,
            TokenValue::NewLine,
            TokenValue::Hash,
        ]
    );
}

#[test]
fn lex_hash() {
    let mut it = Lexer::new("a#b");
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("a".to_string())
    );
    let token = unwrap_token(it.next());
    assert_eq!(token.value, TokenValue::Hash);
    assert_eq!(token.location, l(1, 1..2));
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("b".to_string())
    );
    expect_lexer_end(&mut it);

    let mut it = Lexer::new("\nvoid #");
    assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("void".into())
    );
    let token = unwrap_token(it.next());
    assert_eq!(token.value, TokenValue::Hash);
    assert_eq!(token.location, l(2, 6..7));
    expect_lexer_end(&mut it);
}

#[test]
fn lex_metadata() {
    // Test the metadata of the first token
    let mut it = Lexer::new("1");
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: make_integer("1"),
            location: l(1, 0..1),
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
            value: make_integer("1"),
            location: l(1, 1..2),
            leading_whitespace: true,
            start_of_line: true
        }
    );
    // 2 is not at the start of the line because the \n in the /**/ doesn't count, however its
    // location correctly lists the second line.
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: make_integer("2"),
            location: l(2, 7..8),
            leading_whitespace: true,
            start_of_line: false
        }
    );
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: make_integer("3"),
            location: l(2, 9..10),
            leading_whitespace: true,
            start_of_line: false
        }
    );
    // + doesn't have a leading whitespace
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: Punct::Plus.into(),
            location: l(2, 10..11),
            leading_whitespace: false,
            start_of_line: false
        }
    );
    // The newline is correctly tagged on the preceeding line
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: TokenValue::NewLine,
            location: l(2, 11..12),
            leading_whitespace: false,
            start_of_line: false
        }
    );
    // 4 is after a newline that correctly sets start_of_line
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: make_integer("4"),
            location: l(3, 12..13),
            leading_whitespace: true,
            start_of_line: true
        }
    );
    // The final newline added by the lexer is at the correct position
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: TokenValue::NewLine,
            location: l(3, 13..13),
            leading_whitespace: false,
            start_of_line: false
        }
    );
    assert_eq!(it.next(), None);
}

#[test]
fn lex_identifiers() {
    // Test some basic identifier cases with locations
    let mut it = Lexer::new("foo BA_R baz0");
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_ident("foo"));
    assert_eq!(token.location, l(1, 0..3),);
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_ident("BA_R"));
    assert_eq!(token.location, l(1, 4..8),);
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_ident("baz0"));
    assert_eq!(token.location, l(1, 9..13),);
    expect_lexer_end(&mut it);

    // Test _ is a valid identifier
    assert_eq!(lexed_token_values("_"), vec![make_ident("_")]);

    // Test that identifiers are not split by escaped newlines
    assert_eq!(lexed_token_values("a\\\nb"), vec![make_ident("ab")]);

    // Test that identifiers are split by other whitespace like /**/
    assert_eq!(
        lexed_token_values("a/**/b"),
        vec![make_ident("a"), make_ident("b")]
    );
}

#[test]
fn lex_decimal() {
    // Test some basic cases with locations
    let mut it = Lexer::new("1 0u 42 65536U");
    assert_eq!(unwrap_token_value(it.next()), make_integer("1"));
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_integer("0u"));
    assert_eq!(token.location, l(1, 2..4),);
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_integer("42"));
    assert_eq!(token.location, l(1, 5..7),);
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_integer("65536U"));
    assert_eq!(token.location, l(1, 8..14),);
    expect_lexer_end(&mut it);

    // Test splitting with identifiers
    assert_eq!(
        lexed_token_values("31ab"),
        vec![make_integer("31"), make_ident("ab")]
    );

    // Test splitting with whitespace
    assert_eq!(
        lexed_token_values("31/**/32"),
        vec![make_integer("31"), make_integer("32")]
    );

    // Test splitting with punctuation
    assert_eq!(
        lexed_token_values("31+32"),
        vec![make_integer("31"), Punct::Plus.into(), make_integer("32")]
    );

    // Test that 2^64 doesn't produce an overflow error at the lexer level.
    assert_eq!(
        lexed_token_values("18446744073709551616"),
        vec![make_integer("18446744073709551616")]
    );

    // Check that the 16bit or 64bit suffixes are parsed correctly.
    assert_eq!(
        lexed_token_values("13s 13S 13l 13L"),
        vec![
            make_integer("13s"),
            make_integer("13S"),
            make_integer("13l"),
            make_integer("13L"),
        ]
    );

    // Check that the width suffixes are parse correctly after unsigned suffixes too.
    assert_eq!(
        lexed_token_values("13uS 13Ul"),
        vec![make_integer("13uS"), make_integer("13Ul"),]
    );

    // Check that signedness suffixes are consumed only once.
    assert_eq!(
        lexed_token_values("13Uu 13Uul"),
        vec![
            make_integer("13U"),
            make_ident("u"),
            make_integer("13U"),
            make_ident("ul"),
        ]
    );

    // Check that width suffixes are consumed only once.
    assert_eq!(
        lexed_token_values("13lS"),
        vec![make_integer("13l"), make_ident("S"),]
    );
}

#[test]
fn lex_hexadecimal() {
    // Test some basic cases with locations
    let mut it = Lexer::new("0x1 0X0u 0xBaFfe 0XcaFeU");
    assert_eq!(unwrap_token_value(it.next()), make_integer("0x1"));
    assert_eq!(unwrap_token_value(it.next()), make_integer("0X0u"));
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_integer("0xBaFfe"));
    assert_eq!(token.location, l(1, 9..16),);
    let token = unwrap_token(it.next());
    assert_eq!(token.value, make_integer("0XcaFeU"));
    assert_eq!(token.location, l(1, 17..24),);
    expect_lexer_end(&mut it);

    // Test with redundant zeroes
    assert_eq!(
        lexed_token_values("0x000 0x000000000000001"),
        vec![make_integer("0x000"), make_integer("0x000000000000001")]
    );

    // Test splitting with identifiers
    assert_eq!(
        lexed_token_values("0x31zb"),
        vec![make_integer("0x31"), make_ident("zb")]
    );

    // Test splitting with whitespace
    assert_eq!(
        lexed_token_values("0x31/**/32"),
        vec![make_integer("0x31"), make_integer("32")]
    );

    // Test splitting with punctuation
    assert_eq!(
        lexed_token_values("0x31+32"),
        vec![make_integer("0x31"), Punct::Plus.into(), make_integer("32")]
    );

    // Test that 2^64 doesn't produce an overflow error at the lexer level.
    assert_eq!(
        lexed_token_values("0x10000000000000000"),
        vec![make_integer("0x10000000000000000")]
    );
}

#[test]
fn lex_octal() {
    // Test some basic cases
    assert_eq!(
        lexed_token_values("01 00u 07654 01234u"),
        vec![
            make_integer("01"),
            make_integer("00u"),
            make_integer("07654"),
            make_integer("01234u")
        ]
    );

    // Test with redundant zeroes
    assert_eq!(
        lexed_token_values("0000 0000000000000001"),
        vec![make_integer("0000"), make_integer("0000000000000001")],
    );

    // Test splitting with identifiers
    assert_eq!(
        lexed_token_values("031zb"),
        vec![make_integer("031"), make_ident("zb")],
    );

    // Test splitting with whitespace
    assert_eq!(
        lexed_token_values("031/**/32"),
        vec![make_integer("031"), make_integer("32")],
    );

    // TODO(kangz): Fix octal numbers consuming 8 and 9s as well. This can be done with extra logic
    // already but is not worth the complexity.

    // Test splitting with 8 and 9
    // let mut it = Lexer::new("039 038");
    // assert_eq!(unwrap_token_value(it.next()), 3.into());
    // assert_eq!(unwrap_token_value(it.next()), 9.into());
    // assert_eq!(unwrap_token_value(it.next()), 3.into());
    // assert_eq!(unwrap_token_value(it.next()), 8.into());
    // expect_lexer_end(&mut it);

    // Test splitting with punctuation
    assert_eq!(
        lexed_token_values("031+32"),
        vec![make_integer("031"), Punct::Plus.into(), make_integer("32")],
    );

    // Test that 2^64 doesn't produce an overflow error at the lexer level.
    assert_eq!(
        lexed_token_values("02000000000000000000000"),
        vec![make_integer("02000000000000000000000")]
    );
}

#[test]
fn lex_float() {
    // Test a couple simple cases.
    assert_eq!(
        lexed_token_values("1.0 0.0"),
        vec![make_float("1.0"), make_float("0.0")]
    );

    // Test parsing with a leading .
    assert_eq!(
        lexed_token_values(".99 0.01 .00000000"),
        vec![
            make_float(".99"),
            make_float("0.01"),
            make_float(".00000000")
        ]
    );

    // Test parsing with nothing after the .
    assert_eq!(
        lexed_token_values("42. 0."),
        vec![make_float("42."), make_float("0.")]
    );

    // Test parsing with the float suffix
    assert_eq!(
        lexed_token_values("1000.f 1.f .2F"),
        vec![make_float("1000.f"), make_float("1.f"), make_float(".2F")]
    );

    // Test parsing with exponents
    //  - with / without float suffixes
    //  - at different points in the float parsing.
    assert_eq!(
        lexed_token_values("3e10 4.1e-10f .01e12F 4.1e+10f"),
        vec![
            make_float("3e10"),
            make_float("4.1e-10f"),
            make_float(".01e12F"),
            make_float("4.1e+10f"),
        ]
    );

    // Test parsing with exponents
    //  - After values looking like octal integer (works)
    //  - After values looking like hexadecimal integer (doesn't work)

    assert_eq!(
        lexed_token_values("05e2 0x1e-2"),
        vec![
            make_float("05e2"),
            make_integer("0x1e"),
            Punct::Minus.into(),
            make_integer("2"),
        ]
    );

    // Test that parsing a partial exponent float works, even though it isn't a valid float token.
    assert_eq!(lexed_token_values("1.0e"), vec![make_float("1.0e"),]);

    // Check that 16bit and 64bit suffixes are parsed correctly,
    assert_eq!(
        lexed_token_values("1.0l 1.0L 1.0h 1.0H"),
        vec![
            make_float("1.0l"),
            make_float("1.0L"),
            make_float("1.0h"),
            make_float("1.0H"),
        ]
    );

    // Check that 16bit and 64bit suffixes are parsed once.
    assert_eq!(
        lexed_token_values("1.0lL"),
        vec![make_float("1.0l"), make_ident("L"),]
    );
}

#[test]
fn lex_punctuation() {
    // Test parsing some of the token (but not all, that'd be too many tests!), with locations.
    let mut it = Lexer::new("+ != <<=");
    assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
    let token = unwrap_token(it.next());
    assert_eq!(token.value, Punct::NotEqual.into());
    assert_eq!(token.location, l(1, 2..4),);
    let token = unwrap_token(it.next());
    assert_eq!(token.value, Punct::LeftShiftAssign.into());
    assert_eq!(token.location, l(1, 5..8),);
    expect_lexer_end(&mut it);

    // Test parsing a token that's a prefix of another one just before EOF
    assert_eq!(lexed_token_values("<"), vec![Punct::LeftAngle.into()]);

    // Test \\\n doesn't split the token
    assert_eq!(lexed_token_values("=\\\n="), vec![Punct::EqualEqual.into()]);

    // Test whitespace splits the token
    assert_eq!(
        lexed_token_values("+/**/="),
        vec![Punct::Plus.into(), Punct::Equal.into()]
    );

    // Test a number stops processing the token
    assert_eq!(
        lexed_token_values("!1"),
        vec![Punct::Bang.into(), make_integer("1")]
    );

    // Test an identifier stops processing the token
    assert_eq!(
        lexed_token_values("&a"),
        vec![Punct::Ampersand.into(), make_ident("a")]
    );

    // Test whitespace splits the token
    assert_eq!(
        lexed_token_values(">/**/>"),
        vec![Punct::RightAngle.into(), Punct::RightAngle.into()]
    );

    // Test that tokens are parsed greedily: `a+++++b` is `a ++ ++ + b` (invalid GLSL) and not
    // `(a ++) + (++ b)` (valid GLSL)
    assert_eq!(
        lexed_token_values("+++++"),
        vec![
            Punct::Increment.into(),
            Punct::Increment.into(),
            Punct::Plus.into()
        ]
    );

    // Test that an invalid char produces and error
    let mut it = Lexer::new("@");
    assert_eq!(
        unwrap_error(it.next()),
        PreprocessorError::UnexpectedCharacter
    );

    // Extra punctuation tests for code coverage.
    assert_eq!(
        lexed_token_values("<= >= += -= &= || |= | ^= { } ] ? ."),
        vec![
            Punct::LessEqual.into(),
            Punct::GreaterEqual.into(),
            Punct::AddAssign.into(),
            Punct::SubAssign.into(),
            Punct::AndAssign.into(),
            Punct::LogicalOr.into(),
            Punct::OrAssign.into(),
            Punct::Pipe.into(),
            Punct::XorAssign.into(),
            Punct::LeftBrace.into(),
            Punct::RightBrace.into(),
            Punct::RightBracket.into(),
            Punct::Question.into(),
            Punct::Dot.into(),
        ]
    );
}

#[test]
fn lex_had_comments() {
    // Test that had_comments doesn't get set to true if there is no comments.
    let mut it = Lexer::new("#version");
    assert!(!it.had_comments());
    assert_eq!(unwrap_token_value(it.next()), TokenValue::Hash);
    assert!(!it.had_comments());
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("version".to_string())
    );
    assert!(!it.had_comments());
    expect_lexer_end(&mut it);

    // Test that had_comments doesn't get triggered by its sentinel value of '\r'
    let mut it = Lexer::new("\r!");
    assert!(!it.had_comments());
    assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
    assert_eq!(unwrap_token_value(it.next()), Punct::Bang.into());
    assert!(!it.had_comments());
    expect_lexer_end(&mut it);

    // Test that had_comments gets triggered by // comments
    let mut it = Lexer::new("//\n!");
    assert!(!it.had_comments());
    assert_eq!(unwrap_token_value(it.next()), TokenValue::NewLine);
    assert!(it.had_comments());
    assert_eq!(unwrap_token_value(it.next()), Punct::Bang.into());
    assert!(it.had_comments());
    expect_lexer_end(&mut it);

    // Test that had_comments doesn't gets triggered by /**/ comments
    let mut it = Lexer::new("/**/#version");
    assert!(!it.had_comments());
    assert_eq!(unwrap_token_value(it.next()), TokenValue::Hash);
    assert!(it.had_comments());
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("version".to_string())
    );
    assert!(it.had_comments());
    expect_lexer_end(&mut it);
}

// TODO test has_whitespace
