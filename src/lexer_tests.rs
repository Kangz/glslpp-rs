use super::lexer::{
    CharsAndLocation, Lexer, LexerItem, ReplaceComments, SkipBackslashNewline, Token, TokenValue,
    COMMENT_SENTINEL_VALUE,
};
use super::token::{Integer, Location, PreprocessorError, Punct};

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

impl From<i32> for TokenValue {
    fn from(value: i32) -> Self {
        TokenValue::Integer(Integer {
            value: value as u64,
            signed: true,
            width: 32,
        })
    }
}

impl From<u32> for TokenValue {
    fn from(value: u32) -> Self {
        TokenValue::Integer(Integer {
            value: value as u64,
            signed: false,
            width: 32,
        })
    }
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
    assert_eq!(it.next(), c(1, 1, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), c(1, 6, '\n'));
    assert_eq!(it.next(), c(2, 0, 'b'));
    assert_eq!(it.next(), None);

    // Test a single-line comment without an ending newline
    let mut it = ReplaceComments::new("//foo");
    assert_eq!(it.next(), c(1, 0, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), None);

    // Test a single-line comment without nothing afterwards
    let mut it = ReplaceComments::new("//");
    assert_eq!(it.next(), c(1, 0, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), None);

    // Test a single-line comment with a line continuation
    let mut it = ReplaceComments::new("//foo\\\na");
    assert_eq!(it.next(), c(1, 0, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), None);

    // Test a single-line comment with a line continuation
    let mut it = ReplaceComments::new("//foo\\\na");
    assert_eq!(it.next(), c(1, 0, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), None);

    // Test a multi-line comment
    let mut it = ReplaceComments::new("a/*fo\n\no*/b");
    assert_eq!(it.next(), c(1, 0, 'a'));
    assert_eq!(it.next(), c(1, 1, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), c(3, 3, 'b'));
    assert_eq!(it.next(), None);

    // Test a multi-line comment, without a proper ending (only the *)
    let mut it = ReplaceComments::new("a/*fo\n\no*");
    assert_eq!(it.next(), c(1, 0, 'a'));
    assert_eq!(it.next(), c(1, 1, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), None);

    // Test a multi-line comment, without a proper ending (nothing)
    let mut it = ReplaceComments::new("a/*fo\n\no");
    assert_eq!(it.next(), c(1, 0, 'a'));
    assert_eq!(it.next(), c(1, 1, COMMENT_SENTINEL_VALUE));
    assert_eq!(it.next(), None);

    // Test a multi-line comment, or /*/ not being a complete one
    let mut it = ReplaceComments::new("a/*/b");
    assert_eq!(it.next(), c(1, 0, 'a'));
    assert_eq!(it.next(), c(1, 1, COMMENT_SENTINEL_VALUE));
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
            value: 1.into(),
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
            value: 1.into(),
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
            value: 2.into(),
            location: Location { line: 2, pos: 2 },
            leading_whitespace: true,
            start_of_line: false
        }
    );
    assert_eq!(
        unwrap_token(it.next()),
        Token {
            value: 3.into(),
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
            value: 4.into(),
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
    assert_eq!(unwrap_token_value(it.next()), 1.into());
    assert_eq!(unwrap_token_value(it.next()), 0u32.into());
    assert_eq!(unwrap_token_value(it.next()), 42.into());
    assert_eq!(unwrap_token_value(it.next()), 65536u32.into());
    expect_lexer_end(&mut it);

    // Test splitting with identifiers
    let mut it = Lexer::new("31ab");
    assert_eq!(unwrap_token_value(it.next()), 31.into());
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("ab".to_string())
    );
    expect_lexer_end(&mut it);

    // Test splitting with whitespace
    let mut it = Lexer::new("31/**/32");
    assert_eq!(unwrap_token_value(it.next()), 31.into());
    assert_eq!(unwrap_token_value(it.next()), 32.into());
    expect_lexer_end(&mut it);

    // Test splitting with punctuation
    let mut it = Lexer::new("31+32");
    assert_eq!(unwrap_token_value(it.next()), 31.into());
    assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
    assert_eq!(unwrap_token_value(it.next()), 32.into());
    expect_lexer_end(&mut it);

    // Test that 2^64 produces an overflow error but that 2^64-1 correctly parses (even if it might
    // produce an error down the line).
    let mut it = Lexer::new("18446744073709551616");
    assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);
    let mut it = Lexer::new("18446744073709551615");
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Integer(Integer {
            value: 18446744073709551615,
            signed: true,
            width: 32
        })
    );
    expect_lexer_end(&mut it);

    // Check that the 16bit or 64bit suffixes produce errors (for now).
    let mut it = Lexer::new("13s");
    assert_eq!(
        unwrap_error(it.next()),
        PreprocessorError::NotSupported16BitLiteral
    );
    let mut it = Lexer::new("13S");
    assert_eq!(
        unwrap_error(it.next()),
        PreprocessorError::NotSupported16BitLiteral
    );
    let mut it = Lexer::new("13l");
    assert_eq!(
        unwrap_error(it.next()),
        PreprocessorError::NotSupported64BitLiteral
    );
    let mut it = Lexer::new("13L");
    assert_eq!(
        unwrap_error(it.next()),
        PreprocessorError::NotSupported64BitLiteral
    );

    // Check that they produce unsupported errors even if they happen with a unsigned suffix too.
    let mut it = Lexer::new("13uS");
    assert_eq!(
        unwrap_error(it.next()),
        PreprocessorError::NotSupported16BitLiteral
    );
    let mut it = Lexer::new("13Ul");
    assert_eq!(
        unwrap_error(it.next()),
        PreprocessorError::NotSupported64BitLiteral
    );
}

#[test]
fn lex_hexadecimal() {
    // Test some basic cases
    let mut it = Lexer::new("0x1 0x0u 0xBaFfe 0xcaFeU");
    assert_eq!(unwrap_token_value(it.next()), 1.into());
    assert_eq!(unwrap_token_value(it.next()), 0u32.into());
    assert_eq!(unwrap_token_value(it.next()), 0xBAFFE.into());
    assert_eq!(unwrap_token_value(it.next()), 0xCAFEu32.into());
    expect_lexer_end(&mut it);

    // Test with redundant zeroes
    let mut it = Lexer::new("0x000 0x000000000000001");
    assert_eq!(unwrap_token_value(it.next()), 0.into());
    assert_eq!(unwrap_token_value(it.next()), 1.into());
    expect_lexer_end(&mut it);

    // Test splitting with identifiers
    let mut it = Lexer::new("0x31zb");
    assert_eq!(unwrap_token_value(it.next()), 0x31.into());
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("zb".to_string())
    );
    expect_lexer_end(&mut it);

    // Test splitting with whitespace
    let mut it = Lexer::new("0x31/**/32");
    assert_eq!(unwrap_token_value(it.next()), 0x31.into());
    assert_eq!(unwrap_token_value(it.next()), 32.into());
    expect_lexer_end(&mut it);

    // Test splitting with punctuation
    let mut it = Lexer::new("0x31+32");
    assert_eq!(unwrap_token_value(it.next()), 0x31.into());
    assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
    assert_eq!(unwrap_token_value(it.next()), 32.into());
    expect_lexer_end(&mut it);

    // Test that 2^64 produces an overflow error but that 2^64-1 correctly parses (even if it might
    // produce an error down the line).
    let mut it = Lexer::new("0x10000000000000000");
    assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);
    let mut it = Lexer::new("0xFFFFFFFFFFFFFFFF");
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Integer(Integer {
            value: 18446744073709551615,
            signed: true,
            width: 32
        })
    );
    expect_lexer_end(&mut it);
}

#[test]
fn lex_octal() {
    // Test some basic cases
    let mut it = Lexer::new("01 00u 07654 01234u");
    assert_eq!(unwrap_token_value(it.next()), 1.into());
    assert_eq!(unwrap_token_value(it.next()), 0u32.into());
    assert_eq!(unwrap_token_value(it.next()), 4012.into());
    assert_eq!(unwrap_token_value(it.next()), 668u32.into());
    expect_lexer_end(&mut it);

    // Test with redundant zeroes
    let mut it = Lexer::new("0000 0000000000000001");
    assert_eq!(unwrap_token_value(it.next()), 0.into());
    assert_eq!(unwrap_token_value(it.next()), 1.into());
    expect_lexer_end(&mut it);

    // Test splitting with identifiers
    let mut it = Lexer::new("031zb");
    assert_eq!(unwrap_token_value(it.next()), 25.into());
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Ident("zb".to_string())
    );
    expect_lexer_end(&mut it);

    // Test splitting with whitespace
    let mut it = Lexer::new("031/**/32");
    assert_eq!(unwrap_token_value(it.next()), 25.into());
    assert_eq!(unwrap_token_value(it.next()), 32.into());
    expect_lexer_end(&mut it);

    // Test splitting with 8 and 9
    let mut it = Lexer::new("039 038");
    assert_eq!(unwrap_token_value(it.next()), 3.into());
    assert_eq!(unwrap_token_value(it.next()), 9.into());
    assert_eq!(unwrap_token_value(it.next()), 3.into());
    assert_eq!(unwrap_token_value(it.next()), 8.into());
    expect_lexer_end(&mut it);

    // Test splitting with punctuation
    let mut it = Lexer::new("031+32");
    assert_eq!(unwrap_token_value(it.next()), 25.into());
    assert_eq!(unwrap_token_value(it.next()), Punct::Plus.into());
    assert_eq!(unwrap_token_value(it.next()), 32.into());
    expect_lexer_end(&mut it);

    // Test that 2^64 produces an overflow error but that 2^64-1 correctly parses (even if it might
    // produce an error down the line).
    let mut it = Lexer::new("02000000000000000000000");
    assert_eq!(unwrap_error(it.next()), PreprocessorError::IntegerOverflow);
    let mut it = Lexer::new("01777777777777777777777");
    assert_eq!(
        unwrap_token_value(it.next()),
        TokenValue::Integer(Integer {
            value: 18446744073709551615,
            signed: true,
            width: 32
        })
    );
    expect_lexer_end(&mut it);
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
    assert_eq!(unwrap_token_value(it.next()), 1.into());
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
