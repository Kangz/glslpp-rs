use super::lexer::{self, Token as LexerToken, TokenValue as LexerTokenValue};
use super::pp::{convert_lexer_token, Preprocessor, PreprocessorItem};
use super::token::{Location, PreprocessorError, Punct, Token, TokenValue};

struct NoopPreprocessor<'a> {
    lexer: lexer::Lexer<'a>,
}

impl<'a> NoopPreprocessor<'a> {
    pub fn new(input: &'a str) -> NoopPreprocessor {
        NoopPreprocessor {
            lexer: lexer::Lexer::new(input),
        }
    }
}

impl<'a> Iterator for NoopPreprocessor<'a> {
    type Item = Result<Token, (PreprocessorError, Location)>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.lexer.next() {
                Some(Ok(LexerToken {
                    value: LexerTokenValue::NewLine,
                    ..
                })) => continue,
                Some(Ok(token)) => return Some(Ok(convert_lexer_token(token).unwrap())),
                None => return None,
                Some(Err(err)) => return Some(Err(err)),
            }
        }
    }
}

fn check_preprocessed_result(input: &str, expected: &str) {
    let pp_items: Vec<PreprocessorItem> = Preprocessor::new(input).collect();
    let noop_items: Vec<PreprocessorItem> = NoopPreprocessor::new(expected).collect();

    assert_eq!(pp_items.len(), noop_items.len());
    for (pp_item, noop_item) in pp_items.iter().zip(noop_items) {
        if let (Ok(pp_tok), Ok(ref noop_tok)) = (pp_item, noop_item) {
            assert_eq!(pp_tok.value, noop_tok.value);
        } else {
            unreachable!();
        }
    }
}

fn check_preprocessing_error(input: &str, expected_err: PreprocessorError) {
    for item in Preprocessor::new(input) {
        if let Err((err, _)) = item {
            assert_eq!(err, expected_err);
            return;
        }
    }
    unreachable!();
}

#[test]
fn parse_directive() {
    // Test parsing a simple directive
    check_preprocessed_result("#define A B", "");

    // Test parsing a simple directive with comment right after the hash
    check_preprocessed_result("# /**/ \tdefine A B", "");

    // Test preprocessing directive can only come after a newline
    check_preprocessing_error("42 #define A B", PreprocessorError::UnexpectedHash);

    // Test not an identifier after the hash
    check_preprocessing_error(
        "# ; A B",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Semicolon)),
    );

    // Test a fake directive
    check_preprocessing_error("#CoucouLeChat", PreprocessorError::UnknownDirective);
}

#[test]
fn parse_error() {
    // Test preprocessing directive can only come after a newline
    check_preprocessing_error("#error", PreprocessorError::ErrorDirective);
}

#[test]
fn parse_define() {
    // Test the define name must be an identifier
    check_preprocessing_error(
        "#define [",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::LeftBracket)),
    );

    // Test that there must be a name before the new line
    check_preprocessing_error(
        "#define
        A",
        PreprocessorError::UnexpectedNewLine,
    );
}

#[test]
fn parse_undef() {
    // Test the define name must be an identifier
    check_preprocessing_error(
        "#undef !",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Bang)),
    );

    // Test that there must be a name before the new line
    check_preprocessing_error(
        "#undef
        A",
        PreprocessorError::UnexpectedNewLine,
    );
}

#[test]
fn argument_less_define() {
    // Test a simple case
    check_preprocessed_result(
        "#define A B
         A",
        "B",
    );

    // Test an empty define
    check_preprocessed_result(
        "#define A
         A something",
        "something",
    );

    // Test a define containing a token that's itself
    check_preprocessed_result(
        "#define A A B C
         A",
        "A B C",
    );

    // Test a define invocation followed by () doesn't remove them
    check_preprocessed_result(
        "#define A foo
         A()",
        "foo()",
    );

    // Test nesting define
    check_preprocessed_result(
        "#define B C
         #define A B
         A",
        "C",
    );

    // Test nesting with a bunch of empty tokens
    check_preprocessed_result(
        "#define D
         #define C D D
         #define B C C D D
         #define A B B C C D D
         A truc",
        "truc",
    );

    // Test line continuation doesn't break the define
    check_preprocessed_result(
        "#define C A \\
         B
         C",
        "A B",
    );

    // Test that multiline comments don't break the define
    check_preprocessed_result(
        "#define C A /*
         */ B
         C",
        "A B",
    );

    // Test that substitution in defines happens at invocation time
    // Checks both when undefined a ident found in A and redefining it.
    check_preprocessed_result(
        "#define B stuff
         #define C stuffy stuff
         #define A B C
         #undef B
         #undef C
         #define C :)
         A",
        "B :)",
    );

    // The first token of the define can be a ( if it has whitespace after
    // the identifier
    check_preprocessed_result(
        "#define A ()
         #define B\t(!
         #define C/**/(a, b)
         A B C",
        "() (! (a, b)",
    );

    // Check that hashes are disallowed in defines
    check_preprocessing_error("#define A #", PreprocessorError::UnexpectedHash);
}

#[test]
fn function_like_define() {
    // Test calling a define with 1 argument
    check_preprocessed_result(
        "#define A(a) +a+
         A(1)",
        "+1+",
    );

    // Test calling a define with 0 arguments
    check_preprocessed_result(
        "#define A() foo
         A()",
        "foo",
    );

    // Test called a define with multiple arguments
    check_preprocessed_result(
        "#define A(a, b) b a
         A(1, 2)",
        "2 1",
    );

    // Test not calling a function-like macro just returns the identifier
    check_preprocessed_result(
        "#define A(a) foobar
         A + B",
        "A + B",
    );

    // Test that duplicate argument names are disallowed
    check_preprocessing_error("#define A(a, a) foo", PreprocessorError::DuplicateParameter);

    // Test that non ident or , are disallowed in the parameter list
    check_preprocessing_error(
        "#define A(%) foo",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Percent)),
    );
    check_preprocessing_error(
        "#define A(a, %) foo",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Percent)),
    );

    // Test that starting the param list with a comma is disallowed
    check_preprocessing_error(
        "#define A(,a) foo",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Comma)),
    );

    // Test that two identifier in a row is disallowed
    check_preprocessing_error(
        "#define A(a b) foo",
        PreprocessorError::UnexpectedToken(TokenValue::Ident("b".to_string())),
    );
    check_preprocessing_error(
        "#define A(a, b c) foo",
        PreprocessorError::UnexpectedToken(TokenValue::Ident("c".to_string())),
    );

    // Test passing too many arguments is disallowed
    check_preprocessing_error(
        "#define A(a, b) foo
         A(1, 2, 3)",
        PreprocessorError::TooManyDefineArguments,
    );

    // Test passing too few arguments is disallowed
    check_preprocessing_error(
        "#define A(a, b) foo
         A(1)",
        PreprocessorError::TooFewDefineArguments,
    );

    // Test passing no argument to a define with one parameter.
    check_preprocessed_result(
        "#define A(a) foo a
         A()",
        "foo",
    );

    // Test EOF while parsing define arguments
    check_preprocessing_error(
        "#define A(a, b) foo
         A(",
        PreprocessorError::UnexpectedEndOfInput,
    );

    // Test unknown token while parsing define arguments
    check_preprocessing_error(
        "#define A(a) foo
         A($)",
        PreprocessorError::UnexpectedCharacter,
    );

    // Test #error while parsing arguments
    check_preprocessing_error(
        "#define A(a) foo
         A(
         #error
         )",
        PreprocessorError::ErrorDirective,
    );

    // Test that commas inside () are not used to split parameters
    check_preprocessed_result(
        "#define STUFF(a, b) a + b
         STUFF((1, 2), 3)",
        "(1, 2) + 3",
    );

    // Test that commas inside more nesting
    check_preprocessed_result(
        "#define STUFF(a, b) a + b
         STUFF((((()1, 2))), 3)",
        "(((()1, 2))) + 3",
    );

    // Test that a macro can be used in its own arguments
    check_preprocessed_result(
        "#define B(foo) (foo)
         B(1 B(2))",
        "(1 (2))",
    );

    // Test that define expansion doesn't happen while parsing define call arguments. If it
    // were, the COMMA would make a third argument to A appear, which would be an error.
    check_preprocessed_result(
        "#define A(x, y) x + y
         #define COMMA ,
         A(1 COMMA 2, 3)",
        "1, 2 + 3",
    );

    // Test that define expansion of arguments happens before giving tokens in the define
    // call. If it weren't the COMMA wouldn't make a second argument to A appear, which would
    // be an error.
    check_preprocessed_result(
        "#define A(x, y) x + y
         #define COMMA ,
         #define B(foo) A(foo)
         B(1 COMMA 2)",
        "1 + 2",
    );

    // Same but checking args are fully expanded by doing some weird nesting. The inner B's
    // call to A will create the token that will cause the outer B to call A with two arguments
    check_preprocessed_result(
        "#define A(a, b) ,(a + b)
         #define B(foo) A(foo)
         #define COMMA ,
         B(1 B(2 COMMA 3))",
        ",(1 + (2 + 3))",
    );

    // Test that the ( , and ) can come from the expansion of an argument.
    check_preprocessed_result(
        "#define LPAREN (
         #define COMMA ,
         #define RPAREN )
         #define A(a, b) (a + b)
         #define B(a) a
         B(A LPAREN 1 COMMA 2 RPAREN)",
        "(1 + 2)",
    );

    // Test that a define being expanded cannot be re-expanded inside an argument to an inner
    // define call.
    check_preprocessed_result(
        "#define LPAREN (
         #define COMMA ,
         #define RPAREN )
         #define A(a) a
         #define B(a) a
         #define C B(A(C))
         C",
        "C",
    );

    // Test that an error during define argument expansion gets surfaced properly.
    check_preprocessing_error(
        "#define A(x, y) x + y
         #define COMMA ,
         #define B(foo) A(1, foo)
         B(2 COMMA 3)",
        PreprocessorError::TooManyDefineArguments,
    );
}

#[test]
fn define_redefinition() {
    // Test that it is valid to redefine a define with the same tokens.
    // Function-like case.
    check_preprocessed_result(
        "#define A(x, y) (x + y)
         #define A(x, y) (x + y)",
        "",
    );
    // Not function-like case.
    check_preprocessed_result(
        "#define A (x, y)
         #define A (x, y)",
        "",
    );

    // Oh no a token is different!
    check_preprocessing_error(
        "#define A (a, y)
         #define A (x, y)",
        PreprocessorError::DefineRedefined,
    );

    // Oh no, one has more tokens!
    check_preprocessing_error(
        "#define A a b
         #define A a",
        PreprocessorError::DefineRedefined,
    );

    // Oh no, one is function-like and not the other
    check_preprocessing_error(
        "#define A a
         #define A() a",
        PreprocessorError::DefineRedefined,
    );

    // Oh no, a parameter name is different!
    check_preprocessing_error(
        "#define A(b) a
         #define A(c) a",
        PreprocessorError::DefineRedefined,
    );

    // Oh no, the parameter count is different!
    check_preprocessing_error(
        "#define A(b, d) a
         #define A(c) a",
        PreprocessorError::DefineRedefined,
    );

    // Oh no, the parameter order is different!
    check_preprocessing_error(
        "#define A(b, d) a
         #define A(d, b) a",
        PreprocessorError::DefineRedefined,
    );
}

#[test]
fn define_undef() {
    // Basic test
    check_preprocessed_result(
        "#define A B
         #undef A
         A",
        "A",
    );

    // It is ok to undef a non-existent define
    check_preprocessed_result(
        "#undef A
         A",
        "A",
    );

    // It is ok to undef a define twice
    check_preprocessed_result(
        "#define A B
         #undef A
         #undef A
         A",
        "A",
    );
}

#[test]
fn parse_ifdef() {
    // Basic test of parsing and operations.
    check_preprocessed_result(
        "#define A
         #ifdef B
             1
         #endif
         #ifdef A
             2
         #endif",
        "2",
    );

    // Check that extra tokens after the identifier are disallowed.
    check_preprocessing_error(
        "#ifdef B ;
         #endif",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Semicolon)),
    );

    // Check that the identifier is required.
    check_preprocessing_error(
        "#ifdef
         #endif",
        PreprocessorError::UnexpectedNewLine,
    );

    // Check that extra tokens are allowed if we are skipping.
    check_preprocessed_result(
        "#if 0
         #ifdef B ;
         #endif
         #endif",
        "",
    );

    // Check that having no identifier is allowed if we are skipping.
    check_preprocessed_result(
        "#if 0
         #ifdef
         #endif
         #endif",
        "",
    );
}

#[test]
fn parse_ifndef() {
    // Basic test of parsing and operations.
    check_preprocessed_result(
        "#define A
         #ifndef B
             1
         #endif
         #ifndef A
             2
         #endif",
        "1",
    );

    // Check that extra tokens after the identifier are disallowed.
    check_preprocessing_error(
        "#ifndef B ;
         #endif",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Semicolon)),
    );

    // Check that the identifier is required.
    check_preprocessing_error(
        "#ifndef
         #endif",
        PreprocessorError::UnexpectedNewLine,
    );

    // Check that extra tokens are allowed if we are skipping.
    check_preprocessed_result(
        "#if 0
         #ifndef B ;
         #endif
         #endif",
        "",
    );

    // Check that having no identifier is allowed if we are skipping.
    check_preprocessed_result(
        "#if 0
         #ifndef
         #endif
         #endif",
        "",
    );
}

#[test]
fn parse_endif() {
    // Basic test of using endif
    check_preprocessed_result(
        "#if 0
         a
         #endif",
        "",
    );

    // Check that extra tokens are disallowed.
    check_preprocessing_error(
        "#if 1
         #endif %",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Percent)),
    );

    // Check that extra tokens are disallowed even for an inner_skipped block.
    check_preprocessing_error(
        "#if 0
         #endif %",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Percent)),
    );

    // Check that extra tokens are allowed if we are skipping.
    check_preprocessed_result(
        "#if 0
         #if 0
         #endif %
         #endif",
        "",
    );

    // Check that a missing endif triggers an error, nest and unnested case.
    check_preprocessing_error("#if 0", PreprocessorError::UnfinishedBlock);
    check_preprocessing_error(
        "#if 1
         #if 0
         #endif",
        PreprocessorError::UnfinishedBlock,
    );
}

#[test]
fn skipping_behavior() {
    // Check regular tokens are skipped
    check_preprocessed_result(
        "#if 0
         a b % 1 2u
         #endif",
        "",
    );
    // Check random hash is allowed while skipping
    check_preprocessed_result(
        "#if 0
         a # b
         #endif",
        "",
    );

    // Check that a hash at the start of the line and nothing else if valid while skipping
    check_preprocessed_result(
        "#if 0
         #
         #endif",
        "",
    );

    // Check invalid directives are allowed while skipping
    check_preprocessed_result(
        "#if 0
         #CestlafauteaNandi
         #endif",
        "",
    );

    // Check that defines skipped (otherwise there would be a redefinition error)
    check_preprocessed_result(
        "#if 0
         #define A 1
         #endif
         #define A 2",
        "",
    );

    // Check that undefs are skipped.
    check_preprocessed_result(
        "#define A 1
         #if 0
         #undef A
         #endif
         A",
        "1",
    );

    // Check that #error is skipped.
    check_preprocessed_result(
        "#if 0
         #error
         #endif",
        "",
    );
}

#[test]
fn parse_line() {
    // Test that #line with a uint and int is allowed.
    check_preprocessed_result(
        "#line 4u
         #line 3
         #line 0xF00",
        "",
    );

    // Test with something other than a number after #line (including a newline)
    check_preprocessing_error(
        "#line !",
        PreprocessorError::UnexpectedToken(TokenValue::Punct(Punct::Bang)),
    );
    check_preprocessing_error("#line", PreprocessorError::UnexpectedNewLine);
    check_preprocessing_error(
        "#line foo",
        PreprocessorError::UnexpectedToken(TokenValue::Ident("foo".into())),
    );

    // Test that #line must have a newline after the integer (this will change when #line
    // supports constant expressions)
    check_preprocessing_error("#line 1 #", PreprocessorError::UnexpectedHash);

    // Test that the integer must be non-negative.
    // TODO enabled once #line supports parsing expressions.
    // check_preprocessing_error(
    //     "#line -1",
    //     PreprocessorError::LineOverflow,
    // );

    // test that the integer must fit in a i32
    check_preprocessing_error("#line 2147483648u", PreprocessorError::LineOverflow);
    // test that the integer must fit in a i32
    check_preprocessed_result("#line 2147483647u", "");
}

#[test]
fn line_define() {
    // Test that the __LINE__ define gives the number of the line.
    check_preprocessed_result(
        "__LINE__
         __LINE__

         __LINE__",
        "1 2 4",
    );

    // Test that __LINE__ split over multiple lines gives the first line.
    check_preprocessed_result("__L\\\nINE__", "1");

    // Test that the __LINE__ define used in define gives the invocation's line
    check_preprocessed_result(
        "#define MY_DEFINE __LINE__
         MY_DEFINE
         MY\\\n_DEFINE",
        "2 3",
    );

    // Test a corner case where the __LINE__ is a peeked token for function-like
    // define parsing.
    check_preprocessed_result(
        "#define A(foo) Bleh
         A __LINE__ B",
        "A 2 B",
    );

    // Test that __LINE__ inside function like defines is the position of the closing )
    check_preprocessed_result(
        "#define B + __LINE__ +
         #define A(X, Y) X __LINE__ Y B
         A(-, -)
         A(-, -
         )",
        "- 3 - + 3 +
         - 5 - + 5 +",
    );

    // Test that the __LINE__ inside a define's argument get the correct value.
    check_preprocessed_result(
        "#define A(X) X
         A(__LINE__
         __LINE__)",
        "2 3",
    );
    check_preprocessed_result(
        "#define B(X) X
         #define A(X) B(X) + __LINE__
         A(__LINE__)",
        "3 + 3",
    );

    // Check that #line is taken into account and can modify the line number in both directions.
    check_preprocessed_result(
        "#line 1000
         __LINE__
         __LINE__

         #line 0
         __LINE__
         __LINE__",
        "1001 1002 1 2",
    );

    // Check that line computations are not allowed to overflow an i32
    check_preprocessed_result(
        "#line 2147483646
         __LINE__",
        "2147483647",
    );
    check_preprocessing_error(
        "#line 2147483647
         __LINE__",
        PreprocessorError::LineOverflow,
    );
}
