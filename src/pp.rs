use crate::lexer::{self, Token as LexerToken, TokenValue as LexerTokenValue};
use crate::token::*;
use std::{cmp::Ordering, collections::{HashMap, HashSet}, convert::TryFrom, rc::Rc};

#[derive(Clone, PartialEq, Debug)]
struct Define {
    name: String,
    function_like: bool,
    params: HashMap<String, usize>,
    tokens: Vec<Token>,
}

#[derive(Debug)]
struct DefineInvocation {
    define: Rc<Define>,
    define_position: usize,

    parameters: Vec<Vec<Token>>,
    parameter_expanding: usize,
    parameter_position: usize,
}

type Step<T> = Result<T, StepExit>;

#[derive(Clone, PartialEq, Debug)]
enum StepExit {
    Error((PreprocessorError, Location)),
    Continue,
    Finished,
}

use StepExit::Continue;
use StepExit::Finished;

impl<T> From<StepExit> for Step<T> {
    fn from(exit: StepExit) -> Step<T> {
        Err(exit)
    }
}

trait MELexer {
    fn step(&mut self) -> Step<Token>;
    fn get_define(&self, name: &str) -> Option<&Rc<Define>>;
}

fn make_unexpected_error(token: LexerToken) -> StepExit {
    let error = match token.value {
        LexerTokenValue::UInt(i) => PreprocessorError::UnexpectedToken(TokenValue::UInt(i)),
        LexerTokenValue::Int(i) => PreprocessorError::UnexpectedToken(TokenValue::Int(i)),
        LexerTokenValue::Ident(s) => PreprocessorError::UnexpectedToken(TokenValue::Ident(s)),
        LexerTokenValue::Punct(p) => PreprocessorError::UnexpectedToken(TokenValue::Punct(p)),
        LexerTokenValue::NewLine => PreprocessorError::UnexpectedNewLine,
        LexerTokenValue::Hash => PreprocessorError::UnexpectedHash,
    };
    StepExit::Error((error, token.location))
}

struct DirectiveBlock {
    start_location: Location,
    outer_skipped: bool,
}

struct DirectiveProcessor<'a> {
    lexer: lexer::Lexer<'a>,
    defines: HashMap<String, Rc<Define>>,
    skipping: bool,
    blocks: Vec<DirectiveBlock>,
}

fn convert_lexer_token(token: LexerToken) -> Step<Token> {
    let location = token.location;
    let value = match token.value {
        LexerTokenValue::UInt(i) => Ok(TokenValue::UInt(i)),
        LexerTokenValue::Int(i) => Ok(TokenValue::Int(i)),
        LexerTokenValue::Ident(s) => Ok(TokenValue::Ident(s)),
        LexerTokenValue::Punct(p) => Ok(TokenValue::Punct(p)),
        LexerTokenValue::NewLine => Err(PreprocessorError::UnexpectedNewLine),
        LexerTokenValue::Hash => Err(PreprocessorError::UnexpectedHash),
    };
    match value {
        Ok(value) => Ok(Token { value, location }),
        Err(err) => Err(StepExit::Error((err, location))),
    }
}

fn legal_redefinition(a: &Define, b: &Define) -> bool {
    assert!(a.name == b.name);
    a.function_like == b.function_like
        && a.params == b.params
        && a.tokens.len() == b.tokens.len()
        && a.tokens
            .iter()
            .zip(&b.tokens)
            .all(|(ta, tb)| ta.value == tb.value)
}

impl<'a> DirectiveProcessor<'a> {
    pub fn new(input: &'a str) -> DirectiveProcessor {
        DirectiveProcessor {
            lexer: lexer::Lexer::new(input),
            defines: Default::default(),
            skipping: false,
            blocks: Default::default(),
        }
    }

    fn get_lexer_token(&mut self) -> Step<LexerToken> {
        match self.lexer.next() {
            None => Finished.into(),
            Some(Ok(tok)) => Ok(tok),
            Some(Err(err)) => Err(StepExit::Error(err)),
        }
    }

    fn expect_a_lexer_token(&mut self, current_location: Location) -> Step<LexerToken> {
        match self.get_lexer_token() {
            Ok(token) => Ok(token),
            Err(Finished) => Err(StepExit::Error((
                PreprocessorError::UnexpectedEndOfInput,
                current_location,
            ))),
            Err(e) => Err(e),
        }
    }

    fn expect_lexer_token(
        &mut self,
        expected: LexerTokenValue,
        current_location: Location,
    ) -> Step<Location> {
        let token = self.expect_a_lexer_token(current_location)?;
        if token.value == expected {
            Ok(token.location)
        } else {
            Err(make_unexpected_error(token))
        }
    }

    fn expect_lexer_ident(&mut self, current_location: Location) -> Step<(String, Location)> {
        let token = self.expect_a_lexer_token(current_location)?;
        if let LexerTokenValue::Ident(name) = token.value {
            Ok((name, token.location))
        } else {
            Err(make_unexpected_error(token))
        }
    }

    fn consume_until_newline(&mut self) -> Step<()> {
        loop {
            if let LexerTokenValue::NewLine = self.get_lexer_token()?.value {
                return Ok(());
            }
        }
    }

    fn parse_define_directive(&mut self, directive_location: Location) -> Step<()> {
        if self.skipping {
            return self.consume_until_newline();
        }

        let (name, name_location) = self.expect_lexer_ident(directive_location)?;

        // TODO validate the name?
        let mut define = Define {
            name,
            function_like: false,
            params: Default::default(),
            tokens: Default::default(),
        };

        // TODO what if token is none? EOF but still need to check it is not a redefinition?
        let mut token = self.get_lexer_token()?;

        // The is a function-like define, parse the argument list, leaving token as the next
        // token.
        if token.value == Punct::LeftParen.into() && !token.leading_whitespace {
            define.function_like = true;
            let mut first_param = true;
            loop {
                token = self.get_lexer_token()?;
                match &token.value {
                    LexerTokenValue::Punct(Punct::RightParen) => {
                        token = self.get_lexer_token()?;
                        break;
                    }

                    LexerTokenValue::Ident(param_name) => {
                        if !first_param {
                            return Err(make_unexpected_error(token));
                        }
                        first_param = false;
                        define
                            .params
                            .insert(param_name.clone(), define.params.len());
                    }

                    LexerTokenValue::Punct(Punct::Comma) => {
                        if first_param {
                            return Err(make_unexpected_error(token));
                        }

                        let (param_name, param_location) =
                            self.expect_lexer_ident(token.location)?;
                        if define.params.contains_key(&param_name) {
                            return Err(StepExit::Error((
                                PreprocessorError::DuplicateParameter,
                                param_location,
                            )));
                        }
                        define.params.insert(param_name, define.params.len());
                    }
                    _ => {
                        return Err(make_unexpected_error(token));
                    }
                }
            }
        }

        // Tokens until the newline are that define's tokens (including the current one)
        loop {
            if token.value == LexerTokenValue::NewLine {
                break;
            }
            define.tokens.push(convert_lexer_token(token)?);
            token = self.get_lexer_token()?;
        }

        // Defines are allowed to be redefined if they are exactly the same up to token locations.
        if let Some(previous_define) = self.defines.get(&define.name) {
            if legal_redefinition(&*previous_define, &define) {
                Ok(())
            } else {
                Err(StepExit::Error((
                    PreprocessorError::DefineRedefined,
                    name_location,
                )))
            }
        } else {
            self.defines.insert(define.name.clone(), Rc::new(define));
            Ok(())
        }
    }

    fn parse_undef_directive(&mut self, directive_location: Location) -> Step<()> {
        if self.skipping {
            return self.consume_until_newline();
        }

        let (name, name_location) = self.expect_lexer_ident(directive_location)?;
        // TODO check predefined
        // It is valid to undef a name that is not defined.
        self.defines.remove(&name);

        self.expect_lexer_token(LexerTokenValue::NewLine, name_location)?;
        Ok(())
    }

    fn parse_error_directive(&mut self, directive_location: Location) -> Step<()> {
        if self.skipping {
            self.consume_until_newline()
        } else {
            // TODO consume the rest of the line and make a nice error message
            Err(StepExit::Error((
                PreprocessorError::ErrorDirective,
                directive_location,
            )))
        }
    }

    fn parse_if_directive(&mut self, directive_location: Location) -> Step<()> {
        self.parse_if_like_directive(directive_location, |this, location| {
            if let LexerTokenValue::Int(value) = this.expect_a_lexer_token(location)?.value {
                Ok(value != 0)
            } else {
                // TODO, so much to do here xD
                todo!();
            }
        })
    }

    fn parse_ifdef_directive(&mut self, directive_location: Location) -> Step<()> {
        self.parse_if_like_directive(directive_location, |this, location| {
            let (name, name_location) = this.expect_lexer_ident(location)?;
            this.expect_lexer_token(LexerTokenValue::NewLine, name_location)?;
            Ok(this.defines.contains_key(&name))
        })
    }

    fn parse_ifndef_directive(&mut self, directive_location: Location) -> Step<()> {
        self.parse_if_like_directive(directive_location, |this, location| {
            let (name, name_location) = this.expect_lexer_ident(location)?;
            this.expect_lexer_token(LexerTokenValue::NewLine, name_location)?;
            Ok(!this.defines.contains_key(&name))
        })
    }

    fn parse_endif_directive(&mut self, directive_location: Location) -> Step<()> {
        if let Some(block) = self.blocks.pop() {
            // After #endif we start processing tokens iff the block was not skipped.
            self.skipping = block.outer_skipped;

            if self.skipping {
                self.consume_until_newline()
            } else {
                self.expect_lexer_token(LexerTokenValue::NewLine, directive_location)?;
                Ok(())
            }
        } else {
            Err(StepExit::Error((
                PreprocessorError::EndifOutsideOfBlock,
                directive_location,
            )))
        }
    }

    fn parse_if_like_directive(
        &mut self,
        directive_location: Location,
        parse: impl Fn(&mut DirectiveProcessor, Location) -> Step<bool>,
    ) -> Step<()> {
        if self.skipping {
            self.blocks.push(DirectiveBlock {
                start_location: directive_location,
                outer_skipped: true,
            });
            self.consume_until_newline()
        } else {
            let result = parse(self, directive_location)?;
            self.skipping = !result;

            self.blocks.push(DirectiveBlock {
                start_location: directive_location,
                outer_skipped: false,
            });
            Ok(())
        }
    }

    fn parse_directive(&mut self, hash_location: Location) -> Step<()> {
        let token = self.expect_a_lexer_token(hash_location)?;

        if let LexerTokenValue::Ident(ref directive) = token.value {
            match directive.as_str() {
                // TODO elif line
                "error" => self.parse_error_directive(token.location),

                "define" => self.parse_define_directive(token.location),
                "undef" => self.parse_undef_directive(token.location),

                "if" => self.parse_if_directive(token.location),
                "ifdef" => self.parse_ifdef_directive(token.location),
                "ifndef" => self.parse_ifndef_directive(token.location),
                "endif" => self.parse_endif_directive(token.location),

                _ => {
                    if !self.skipping {
                        Err(StepExit::Error((
                            PreprocessorError::UnknownDirective,
                            token.location,
                        )))
                    } else {
                        Ok(())
                    }
                }
            }
        } else if !self.skipping {
            make_unexpected_error(token).into()
        } else {
            Ok(())
        }
    }
}

impl<'a> MELexer for DirectiveProcessor<'a> {
    fn step(&mut self) -> Step<Token> {
        let step = (|| {
            let lexer_token = self.get_lexer_token()?;
            match lexer_token.value {
                LexerTokenValue::NewLine => Continue.into(),
                LexerTokenValue::Hash => {
                    if lexer_token.start_of_line {
                        self.parse_directive(lexer_token.location)?;
                        Continue.into()
                    } else if !self.skipping {
                        make_unexpected_error(lexer_token).into()
                    } else {
                        Continue.into()
                    }
                }

                _ => {
                    if !self.skipping {
                        convert_lexer_token(lexer_token)
                    } else {
                        Continue.into()
                    }
                }
            }
        })();

        if step == Err(StepExit::Finished) {
            if let Some(block) = self.blocks.pop() {
                return Err(StepExit::Error((
                    PreprocessorError::UnfinishedBlock,
                    block.start_location,
                )));
            }
        }

        step
    }

    fn get_define(&self, name: &str) -> Option<&Rc<Define>> {
        self.defines.get(name)
    }
}

#[derive(Default)]
struct MacroProcessor {
    define_invocations: Vec<DefineInvocation>,
    defines_being_expanded: HashSet<String>,

    peeked: Option<Step<Token>>,
    define_line: u32,
}

impl MacroProcessor {
    fn start_define_invocation(
        &mut self,
        name: &str,
        location: Location,
        lexer: &mut dyn MELexer,
    ) -> Step<bool> {
        // Defines can be expanding only once, it is not possible to do recursive defines
        if self.defines_being_expanded.contains(name) {
            return Ok(false);
        }

        if let Some(define) = lexer.get_define(name) {
            let mut invocation = DefineInvocation {
                define: define.clone(),
                define_position: 0,

                parameters: Default::default(),
                parameter_position: 0,
                parameter_expanding: std::usize::MAX,
            };

            // If this is a not a function-like define, __LINE__ inside the define is the line of the first
            // character of the invocation. Only the line of the top-level invocation counts.
            if !self.is_expanding_define() {
                self.define_line = location.line;
            }

            if invocation.define.function_like {
                let lparen_location = match self.step_no_continue(lexer) {
                    Ok(Token {
                        value: TokenValue::Punct(Punct::LeftParen),
                        location,
                    }) => location,

                    // Function-like macros are not processed if there is no ( right after the identifier
                    token => {
                        self.peeked = Some(token);
                        return Ok(false);
                    }
                };

                // TODO still bail out if define was undefined until now? This would match
                // clang and GCC
                let (parameters, closing_location) =
                    self.parse_define_call_arguments(lexer, lparen_location)?;

                if !self.is_expanding_define() {
                    self.define_line = closing_location.line;
                }

                // Check for the number of arguments.
                match parameters.len().cmp(&invocation.define.params.len()) {
                    Ordering::Greater => {
                        let params_empty = parameters.len() == 1 && parameters[0].is_empty();
                        let expects_zero_args = invocation.define.params.is_empty();

                        if !(params_empty && expects_zero_args) {
                            return Err(StepExit::Error((
                                PreprocessorError::TooManyDefineArguments,
                                lparen_location,
                            )));
                        }
                    }
                    Ordering::Less => {
                        return Err(StepExit::Error((
                            PreprocessorError::TooFewDefineArguments,
                            lparen_location,
                        )));
                    }
                    _ => {}
                }

                // Fully expand the parameters
                for parameter in parameters {
                    invocation
                        .parameters
                        .push(self.expand_parameter(lexer, parameter)?);
                }
            }

            assert!(self
                .defines_being_expanded
                .insert(invocation.define.name.clone()));
            self.define_invocations.push(invocation);

            return Ok(true);
        }

        Ok(false)
    }

    // Parse the arguments of the function-like define starting after the first (. Also returns
    // the location of the closing ).
    fn parse_define_call_arguments(
        &mut self,
        lexer: &mut dyn MELexer,
        mut current_location: Location,
    ) -> Step<(Vec<Vec<Token>>, Location)> {
        let mut paren_nesting = 0u32;
        let mut arguments = vec![vec![]];

        loop {
            // Get the next token (without additional expansion)
            let token = match self.step_no_continue(lexer) {
                Err(StepExit::Continue) => {
                    continue;
                }
                Err(StepExit::Finished) => {
                    return Err(StepExit::Error((
                        PreprocessorError::UnexpectedEndOfInput,
                        current_location,
                    )));
                }
                Err(err @ StepExit::Error(_)) => {
                    return Err(err);
                }
                Ok(token) => token,
            };

            current_location = token.location;

            // Handle special tokens
            match token.value {
                // Avoid overflow on parenthesis nesting counting.
                TokenValue::Punct(Punct::LeftParen) => match paren_nesting.checked_add(1) {
                    // TODO figure out a way to cover this code path? Maybe make it a max nesting
                    // so that it can be set to a small value?
                    None => {
                        return Err(StepExit::Error((
                            PreprocessorError::IntegerOverflow,
                            current_location,
                        )));
                    }
                    Some(v) => paren_nesting = v,
                },

                TokenValue::Punct(Punct::RightParen) => {
                    // Return the arguments when we find our )
                    if paren_nesting == 0 {
                        return Ok((arguments, token.location));
                    }
                    paren_nesting -= 1;
                }

                TokenValue::Punct(Punct::Comma) => {
                    // Commas outside of () split arguments and must not be added to them.
                    if paren_nesting == 0 {
                        arguments.push(Default::default());
                        continue;
                    }
                }

                _ => {}
            }

            arguments.last_mut().unwrap().push(token);
        }
    }

    fn expand_parameter(&self, lexer: &mut dyn MELexer, parameter: Vec<Token>) -> Step<Vec<Token>> {
        struct ExpandParameterLexer<'a> {
            parent_lexer: &'a dyn MELexer,
            expander: &'a MacroProcessor,
            tokens: &'a Vec<Token>,
            position: usize,
        }

        impl<'a> MELexer for ExpandParameterLexer<'a> {
            fn step(&mut self) -> Step<Token> {
                if let Some(token) = self.tokens.get(self.position) {
                    self.position += 1;
                    Ok(token.clone())
                } else {
                    Finished.into()
                }
            }

            fn get_define(&self, name: &str) -> Option<&Rc<Define>> {
                if self.expander.defines_being_expanded.contains(name) {
                    None
                } else {
                    self.parent_lexer.get_define(name)
                }
            }
        }

        let mut parameter_lexer = ExpandParameterLexer {
            parent_lexer: lexer,
            expander: self,
            tokens: &parameter,
            position: 0,
        };

        let mut processor: MacroProcessor = Default::default();
        let mut expanded_parameters = Default::default();
        loop {
            match processor.step(&mut parameter_lexer) {
                Err(err @ StepExit::Error(_)) => return Err(err),
                Err(StepExit::Finished) => return Ok(expanded_parameters),
                Err(StepExit::Continue) => continue,
                Ok(token) => {
                    if let TokenValue::Ident(name) = &token.value {
                        if processor.start_define_invocation(
                            name,
                            token.location,
                            &mut parameter_lexer,
                        )? {
                            continue;
                        }
                    }

                    expanded_parameters.push(token);
                }
            }
        }
    }

    fn is_expanding_define(&self) -> bool {
        !self.define_invocations.is_empty()
    }

    fn step_internal(&mut self, lexer: &mut dyn MELexer) -> Step<Token> {
        if let Some(step) = self.peeked.take() {
            return step;
        }

        if let Some(invocation) = self.define_invocations.last_mut() {
            // Keep expanding the parameters
            if let Some(argument) = invocation.parameters.get(invocation.parameter_expanding) {
                if let Some(token) = argument.get(invocation.parameter_position) {
                    invocation.parameter_position += 1;
                    return Ok(token.clone());
                } else {
                    invocation.parameter_expanding = std::usize::MAX;
                    return Continue.into();
                }
            }

            // Take tokens from the define definition.
            if let Some(token) = invocation.define.tokens.get(invocation.define_position) {
                invocation.define_position += 1;

                // We found a parameter! Start expanding it.
                if let TokenValue::Ident(name) = &token.value {
                    if let Some(parameter_index) = invocation.define.params.get(name) {
                        invocation.parameter_expanding = *parameter_index;
                        invocation.parameter_position = 0;
                        return Continue.into();
                    }
                }

                return Ok(token.clone());
            } else {
                self.defines_being_expanded.remove(&invocation.define.name);
                self.define_invocations.pop();
                return Continue.into();
            }
        }

        Ok(lexer.step()?)
    }

    fn step(&mut self, lexer: &mut dyn MELexer) -> Step<Token> {
        let token = self.step_internal(lexer)?;

        if let TokenValue::Ident(name) = &token.value {
            if name == "__LINE__" {
                // When inside a define, __LINE__ is that define's line.
                let line = if self.is_expanding_define() {
                    self.define_line
                } else {
                    token.location.line
                };

                // TODO handle checked add with #line directive offset.

                if let Ok(int_line) = i32::try_from(line) {
                    return Ok(Token {
                        value: TokenValue::Int(int_line),
                        location: token.location,
                    });
                } else {
                    return Err(StepExit::Error((
                        PreprocessorError::ErrorDirective,
                        token.location,
                    )));
                }
            }
        }

        Ok(token)
    }

    fn step_no_continue(&mut self, lexer: &mut dyn MELexer) -> Step<Token> {
        loop {
            let step = self.step(lexer);
            if step != Continue.into() {
                return step;
            }
        }
    }
}

pub struct Preprocessor<'a> {
    directive_processor: DirectiveProcessor<'a>,
    macro_processor: MacroProcessor,
}

impl<'a> Preprocessor<'a> {
    pub fn new(input: &'a str) -> Preprocessor {
        Preprocessor {
            directive_processor: DirectiveProcessor::new(input),
            macro_processor: Default::default(),
        }
    }

    fn step(&mut self) -> Step<Token> {
        let token = self.macro_processor.step(&mut self.directive_processor)?;

        // Is this token the start of a new macro?
        if let TokenValue::Ident(name) = &token.value {
            // Returns Continue if it started the define, token otherwise.
            if self.macro_processor.start_define_invocation(
                name,
                token.location,
                &mut self.directive_processor,
            )? {
                return Continue.into();
            }
        }

        Ok(token)
    }
}

type PreprocessorItem = Result<Token, (PreprocessorError, Location)>;

impl<'a> Iterator for Preprocessor<'a> {
    type Item = PreprocessorItem;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                Ok(token) => return Some(Ok(token)),
                Err(StepExit::Error(err)) => return Some(Err(err)),
                Err(StepExit::Finished) => return None,
                Err(StepExit::Continue) => continue,
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
                assert!(false)
            }
        }
    }

    fn check_preprocessing_error(input: &str, expected_err: PreprocessorError) {
        for item in Preprocessor::new(input) {
            match item {
                Err((err, _)) => {
                    assert_eq!(err, expected_err);
                    return;
                }
                Ok(_) => {}
            }
        }
        assert!(false);
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
    }
}
