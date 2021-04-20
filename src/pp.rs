use crate::lexer::{self, Token as LexerToken, TokenValue as LexerTokenValue};
use crate::token::*;
use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
    convert::TryFrom,
    rc::Rc,
};

mod if_parser;

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

pub type Step<T> = Result<T, StepExit>;

#[derive(Clone, PartialEq, Debug)]
pub enum StepExit {
    Error((PreprocessorError, Location)),
    Continue,
    Finished,
}

use self::StepExit::Continue;
use self::StepExit::Finished;

impl<T> From<StepExit> for Step<T> {
    fn from(exit: StepExit) -> Step<T> {
        Err(exit)
    }
}

trait MELexer {
    fn step(&mut self) -> Step<Token>;
    fn get_define(&self, name: &str) -> Option<&Rc<Define>>;
    fn apply_line_offset(&self, line: u32, location: Location) -> Step<u32>;
}

fn make_unexpected_error(token: LexerToken) -> StepExit {
    let error = match token.value {
        LexerTokenValue::Integer(i) => PreprocessorError::UnexpectedToken(TokenValue::Integer(i)),
        LexerTokenValue::Float(f) => PreprocessorError::UnexpectedToken(TokenValue::Float(f)),
        LexerTokenValue::Ident(s) => PreprocessorError::UnexpectedToken(TokenValue::Ident(s)),
        LexerTokenValue::Punct(p) => PreprocessorError::UnexpectedToken(TokenValue::Punct(p)),
        LexerTokenValue::NewLine => PreprocessorError::UnexpectedNewLine,
        LexerTokenValue::Hash => PreprocessorError::UnexpectedHash,
    };
    StepExit::Error((error, token.location))
}

fn make_line_overflow_error(location: Location) -> StepExit {
    StepExit::Error((PreprocessorError::LineOverflow, location))
}

struct DirectiveBlock {
    start_location: Location,
    had_valid_segment: bool,
    had_else: bool,
    outer_skipped: bool,
}

struct DirectiveProcessor<'a> {
    lexer: lexer::Lexer<'a>,
    defines: HashMap<String, Rc<Define>>,
    skipping: bool,
    blocks: Vec<DirectiveBlock>,
    line_offset: i64,
    had_directive: bool,
    had_non_directive_token: bool,
}

pub fn convert_lexer_token(token: LexerToken) -> Result<Token, (PreprocessorError, Location)> {
    let location = token.location;
    match token.value {
        LexerTokenValue::Integer(i) => Ok(Token {
            value: TokenValue::Integer(i),
            location,
        }),
        LexerTokenValue::Float(f) => Ok(Token {
            value: TokenValue::Float(f),
            location,
        }),
        LexerTokenValue::Ident(s) => Ok(Token {
            value: TokenValue::Ident(s),
            location,
        }),
        LexerTokenValue::Punct(p) => Ok(Token {
            value: TokenValue::Punct(p),
            location,
        }),

        LexerTokenValue::NewLine => Err((PreprocessorError::UnexpectedNewLine, location)),
        LexerTokenValue::Hash => Err((PreprocessorError::UnexpectedHash, location)),
    }
}

pub fn convert_lexer_token_to_step(token: LexerToken) -> Step<Token> {
    convert_lexer_token(token).map_err(StepExit::Error)
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
            line_offset: 0,
            had_directive: false,
            had_non_directive_token: false,
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
            // TODO allow unexpected character errors because we are skipping.
            if let LexerTokenValue::NewLine = self.get_lexer_token()?.value {
                return Ok(());
            }
        }
    }

    fn gather_until_newline(&mut self) -> Step<Vec<Token>> {
        let mut tokens = Vec::new();
        loop {
            let token = self.get_lexer_token()?;
            if token.value == LexerTokenValue::NewLine {
                return Ok(tokens);
            }
            tokens.push(convert_lexer_token_to_step(token)?);
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
            define.tokens.push(convert_lexer_token_to_step(token)?);
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

    fn add_define(
        &mut self,
        name: &str,
        content: &str,
    ) -> Result<(), (PreprocessorError, Location)> {
        let mut define = Define {
            name: name.to_string(),
            function_like: false,
            params: Default::default(),
            tokens: Default::default(),
        };

        // Convert the content to tokens and add it to the define.
        let mut lexer = lexer::Lexer::new(content);
        loop {
            match lexer.next() {
                Some(Ok(lexer_token)) => {
                    // Skip over newlines (the lexer always adds a newline, which would cause an
                    // error in convert_lexer_token).
                    if lexer_token.value == LexerTokenValue::NewLine {
                        continue;
                    }

                    define.tokens.push(convert_lexer_token(lexer_token)?);
                }

                Some(Err(err)) => return Err(err),
                None => break,
            }
        }

        // Note this overwrites existing defines, we might want to add an option to make this
        // an error in the future.
        self.defines.insert(define.name.clone(), Rc::new(define));

        Ok(())
    }

    fn parse_undef_directive(&mut self, directive_location: Location) -> Step<()> {
        if self.skipping {
            return self.consume_until_newline();
        }

        let (name, name_location) = self.expect_lexer_ident(directive_location)?;
        // TODO check predefine
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

    fn parse_line_directive(&mut self, directive_location: Location) -> Step<()> {
        if self.skipping {
            return self.consume_until_newline();
        }

        let token = self.expect_a_lexer_token(directive_location)?;

        // TODO support expressions for the line number.
        // TODO figure out what to do with the file, either number or string?

        // Validates that the line is between 0 and 2^31 as per the C standard.
        match token.value {
            LexerTokenValue::Integer(i) => {
                if i.value >= (1u64 << 32u64) {
                    return Err(make_line_overflow_error(token.location));
                }
                self.line_offset = i.value as i64 - directive_location.line as i64;
            }
            _ => return Err(make_unexpected_error(token)),
        };

        self.expect_lexer_token(LexerTokenValue::NewLine, token.location)?;
        Ok(())
    }

    fn evaluate_if_expression(
        &mut self,
        location: Location,
        line: Vec<Token>,
        max_recursion_depth: usize,
    ) -> Step<bool> {
        if_parser::IfParser::new(line, max_recursion_depth, &self.defines, location).evaluate()
    }

    fn parse_if_directive(&mut self, directive_location: Location) -> Step<()> {
        self.parse_if_like_directive(directive_location, |this, location| {
            let line = this.gather_until_newline()?;
            this.evaluate_if_expression(location, line, 64)
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

    fn parse_elif_directive(&mut self, directive_location: Location) -> Step<()> {
        self.skipping = true;

        // Do checks that the #elif block is well structured even if skipping.
        let block = self.blocks.last().ok_or(StepExit::Error((
            PreprocessorError::ElifOutsideOfBlock,
            directive_location,
        )))?;

        if block.had_else {
            return Err(StepExit::Error((
                PreprocessorError::ElifAfterElse,
                directive_location,
            )));
        }

        // The condition isn't parsed if it doesn't need to (and doesn't produce errors).
        if block.outer_skipped || block.had_valid_segment {
            return self.consume_until_newline();
        }

        let line = self.gather_until_newline()?;
        if self.evaluate_if_expression(directive_location, line, 64)? {
            self.skipping = false;
            self.blocks.last_mut().unwrap().had_valid_segment = true;
        }

        Ok(())
    }

    fn parse_else_directive(&mut self, directive_location: Location) -> Step<()> {
        self.expect_lexer_token(LexerTokenValue::NewLine, directive_location)?;

        let block = self.blocks.last_mut().ok_or(StepExit::Error((
            PreprocessorError::ElseOutsideOfBlock,
            directive_location,
        )))?;

        // #else can only appear once in a block.
        if block.had_else {
            Err(StepExit::Error((
                PreprocessorError::MoreThanOneElse,
                directive_location,
            )))
        } else {
            self.skipping = block.outer_skipped || block.had_valid_segment;
            block.had_else = true;
            Ok(())
        }
    }

    fn parse_endif_directive(&mut self, directive_location: Location) -> Step<()> {
        let block = self.blocks.pop().ok_or(StepExit::Error((
            PreprocessorError::EndifOutsideOfBlock,
            directive_location,
        )))?;

        // After #endif we start processing tokens iff the block was not skipped.
        self.skipping = block.outer_skipped;

        if self.skipping {
            self.consume_until_newline()
        } else {
            self.expect_lexer_token(LexerTokenValue::NewLine, directive_location)?;
            Ok(())
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
                had_valid_segment: false,
                had_else: false,
                outer_skipped: true,
            });
            self.consume_until_newline()
        } else {
            let result = parse(self, directive_location)?;
            self.skipping = !result;

            self.blocks.push(DirectiveBlock {
                start_location: directive_location,
                had_valid_segment: !self.skipping,
                had_else: false,
                outer_skipped: false,
            });
            Ok(())
        }
    }

    fn parse_version_directive(&mut self, directive_location: Location) -> Step<Token> {
        if self.skipping {
            self.consume_until_newline()?;
            Continue.into()
        } else {
            Ok(Token {
                location: directive_location,
                value: TokenValue::Version(Version {
                    tokens: self.gather_until_newline()?,
                    is_first_directive: !(self.had_directive || self.had_non_directive_token),
                    has_comments_before: self.lexer.had_comments(),
                }),
            })
        }
    }

    fn parse_extension_directive(&mut self, directive_location: Location) -> Step<Token> {
        if self.skipping {
            self.consume_until_newline()?;
            Continue.into()
        } else {
            Ok(Token {
                location: directive_location,
                value: TokenValue::Extension(Extension {
                    tokens: self.gather_until_newline()?,
                    has_non_directive_before: self.had_non_directive_token,
                }),
            })
        }
    }

    fn parse_pragma_directive(&mut self, directive_location: Location) -> Step<Token> {
        if self.skipping {
            self.consume_until_newline()?;
            Continue.into()
        } else {
            Ok(Token {
                location: directive_location,
                value: TokenValue::Pragma(Pragma {
                    tokens: self.gather_until_newline()?,
                }),
            })
        }
    }

    fn parse_directive(&mut self, hash_location: Location) -> Step<Token> {
        let token = self.expect_a_lexer_token(hash_location)?;

        if let LexerTokenValue::Ident(ref directive) = token.value {
            match directive.as_str() {
                // TODO elif line
                "error" => self.parse_error_directive(token.location)?,
                "line" => self.parse_line_directive(token.location)?,

                "define" => self.parse_define_directive(token.location)?,
                "undef" => self.parse_undef_directive(token.location)?,

                "if" => self.parse_if_directive(token.location)?,
                "ifdef" => self.parse_ifdef_directive(token.location)?,
                "ifndef" => self.parse_ifndef_directive(token.location)?,
                "elif" => self.parse_elif_directive(token.location)?,
                "else" => self.parse_else_directive(token.location)?,
                "endif" => self.parse_endif_directive(token.location)?,

                "version" => {
                    let result = self.parse_version_directive(token.location);
                    self.had_directive = true;
                    return result;
                }
                "extension" => {
                    let result = self.parse_extension_directive(token.location);
                    self.had_directive = true;
                    return result;
                }
                "pragma" => {
                    let result = self.parse_pragma_directive(token.location);
                    self.had_directive = true;
                    return result;
                }
                _ => {
                    if !self.skipping {
                        return Err(StepExit::Error((
                            PreprocessorError::UnknownDirective,
                            token.location,
                        )));
                    }
                }
            }
            self.had_directive = true;
            Continue.into()
        } else if !self.skipping {
            make_unexpected_error(token).into()
        } else {
            Continue.into()
        }
    }
}

impl<'a> MELexer for DirectiveProcessor<'a> {
    fn step(&mut self) -> Step<Token> {
        let step = (|| {
            // TODO: if we are skipping invalid characters should be allowed.
            let lexer_token = self.get_lexer_token()?;
            match lexer_token.value {
                LexerTokenValue::NewLine => Continue.into(),
                LexerTokenValue::Hash => {
                    if lexer_token.start_of_line {
                        self.parse_directive(lexer_token.location)
                    } else if !self.skipping {
                        make_unexpected_error(lexer_token).into()
                    } else {
                        Continue.into()
                    }
                }

                _ => {
                    if !self.skipping {
                        self.had_non_directive_token = true;
                        convert_lexer_token_to_step(lexer_token)
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

    fn apply_line_offset(&self, line: u32, location: Location) -> Step<u32> {
        if let Ok(offset_line) = u32::try_from(line as i64 + self.line_offset) {
            Ok(offset_line)
        } else {
            Err(make_line_overflow_error(location))
        }
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

            fn apply_line_offset(&self, line: u32, _: Location) -> Step<u32> {
                Ok(line)
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

                return Ok(Token {
                    value: TokenValue::Integer(Integer {
                        value: lexer.apply_line_offset(line, token.location)? as u64,
                        signed: false,
                        width: 32,
                    }),
                    location: token.location,
                });
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

    pub fn add_define(
        &mut self,
        name: &str,
        content: &str,
    ) -> Result<(), (PreprocessorError, Location)> {
        self.directive_processor.add_define(name, content)
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

pub type PreprocessorItem = Result<Token, (PreprocessorError, Location)>;

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
