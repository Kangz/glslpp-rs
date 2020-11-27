use super::lexer::{
    CharsAndLocation, Lexer, LexerItem, ReplaceComments, SkipBackslashNewline, Token, TokenValue,
    COMMENT_SENTINEL_VALUE,
};
use super::token::{Location, PreprocessorError, Punct};

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
