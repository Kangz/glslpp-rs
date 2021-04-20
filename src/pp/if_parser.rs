use crate::token::{Integer, PreprocessorError, Punct};

use super::{Define, Location, Step, StepExit, Token, TokenValue};
use std::{collections::HashMap, iter::Peekable, rc::Rc, slice::Iter, vec::IntoIter};

pub(super) struct IfParser<'macros> {
    tokens: Peekable<IntoIter<Token>>,
    defines: &'macros HashMap<String, Rc<Define>>,
    macro_expansion: Vec<Peekable<Iter<'macros, Token>>>,
    max_recursion_depth: usize,
    location: Location,
}

impl<'macros> IfParser<'macros> {
    pub fn new(
        tokens: Vec<Token>,
        max_recursion_depth: usize,
        defines: &'macros HashMap<String, Rc<Define>>,
        location: Location,
    ) -> Self {
        IfParser {
            tokens: tokens.into_iter().peekable(),
            defines,
            macro_expansion: Vec::with_capacity(max_recursion_depth),
            max_recursion_depth,
            location,
        }
    }

    fn raw_next(&mut self) -> Option<Token> {
        let token = loop {
            if let Some(define) = self.macro_expansion.last_mut() {
                if let Some(token) = define.next() {
                    break Some(token.clone());
                }

                self.macro_expansion.pop();
                continue;
            }

            break None;
        };

        token.or_else(|| self.tokens.next())
    }

    fn raw_peek(&mut self) -> Option<Token> {
        let token = loop {
            if let Some(define) = self.macro_expansion.last_mut() {
                if let Some(token) = define.peek() {
                    break Some((*token).clone());
                }

                self.macro_expansion.pop();
                continue;
            }

            break None;
        };

        token.or_else(|| self.tokens.peek().cloned())
    }

    fn next(&mut self) -> Step<Option<Token>> {
        let token = match self.raw_next() {
            Some(t) => t,
            None => return Ok(None),
        };

        Ok(match token.value {
            TokenValue::Ident(ref name) if name != "defined" => {
                match self.add_define(name, token.location)? {
                    Some(t) => Some(t),
                    None => self.next()?,
                }
            }
            _ => Some(token),
        })
    }

    fn peek(&mut self) -> Step<Option<Token>> {
        let token = match self.raw_peek() {
            Some(t) => t,
            None => return Ok(None),
        };

        Ok(match token.value {
            TokenValue::Ident(ref name) if name != "defined" => {
                self.raw_next();

                match self.add_define(name, token.location)? {
                    Some(t) => Some(t),
                    None => self.peek()?,
                }
            }
            _ => Some(token),
        })
    }

    fn expect_raw_next(&mut self) -> Step<Token> {
        let val = self.raw_next();
        val.ok_or(StepExit::Error((
            PreprocessorError::UnexpectedEndOfInput,
            self.location,
        )))
    }

    fn expect_raw_peek(&mut self) -> Step<Token> {
        let val = self.raw_peek();
        val.ok_or(StepExit::Error((
            PreprocessorError::UnexpectedEndOfInput,
            self.location,
        )))
    }

    fn expect_next(&mut self) -> Step<Token> {
        let val = self.next()?;
        val.ok_or(StepExit::Error((
            PreprocessorError::UnexpectedEndOfInput,
            self.location,
        )))
    }

    fn expect_peek(&mut self) -> Step<Token> {
        let val = self.peek()?;
        val.ok_or(StepExit::Error((
            PreprocessorError::UnexpectedEndOfInput,
            self.location,
        )))
    }

    fn add_define(&mut self, name: &str, location: Location) -> Step<Option<Token>> {
        Ok(if let Some(define) = self.defines.get(name) {
            if self.macro_expansion.len() == self.max_recursion_depth {
                return Err(StepExit::Error((
                    PreprocessorError::RecursionLimitReached,
                    location,
                )));
            }

            assert!(!define.function_like, "TODO: Handle function like defines");

            self.macro_expansion.push(define.tokens.iter().peekable());

            None
        } else {
            Some(Token {
                value: TokenValue::Integer(Integer {
                    value: 0,
                    signed: true,
                    width: 64,
                }),
                location,
            })
        })
    }

    fn handle_defined(&mut self) -> Step<i64> {
        let next = self.expect_raw_peek()?;

        match next.value {
            TokenValue::Ident(ref name) => {
                self.expect_raw_next()?;

                Ok(self.defines.get(name).is_some() as i64)
            }
            TokenValue::Punct(Punct::LeftParen) => {
                self.expect_next()?;

                let name_token = self.expect_raw_next()?;
                let name = match name_token.value {
                    TokenValue::Ident(name) => Ok(name),
                    value => Err(StepExit::Error((
                        PreprocessorError::UnexpectedToken(value),
                        name_token.location,
                    ))),
                }?;

                let close_brace = self.expect_next()?;

                match close_brace.value {
                    TokenValue::Punct(Punct::RightParen) => {
                        Ok(self.defines.get(&name).is_some() as i64)
                    }
                    value => Err(StepExit::Error((
                        PreprocessorError::UnexpectedToken(value),
                        close_brace.location,
                    ))),
                }
            }
            value => Err(StepExit::Error((
                PreprocessorError::UnexpectedToken(value),
                next.location,
            ))),
        }
    }

    fn parse_atom(&mut self) -> Step<i64> {
        let token = self.expect_next()?;

        match token.value {
            TokenValue::Ident(name) => {
                debug_assert_eq!(name, "defined");

                self.handle_defined()
            }
            TokenValue::Integer(int) => Ok(int.value as i64),
            TokenValue::Punct(Punct::LeftParen) => {
                let val = self.parse_logical_or()?;

                let close_brace = self.expect_next()?;

                match close_brace.value {
                    TokenValue::Punct(Punct::RightParen) => Ok(val),
                    value => Err(StepExit::Error((
                        PreprocessorError::UnexpectedToken(value),
                        close_brace.location,
                    ))),
                }
            }
            value => Err(StepExit::Error((
                PreprocessorError::UnexpectedToken(value),
                token.location,
            ))),
        }
    }

    fn parse_unary(&mut self) -> Step<i64> {
        match self.expect_peek()?.value {
            TokenValue::Punct(punct) => match punct {
                Punct::Plus | Punct::Minus | Punct::Bang | Punct::Tilde => {
                    self.next()?;

                    let val = self.parse_unary()?;

                    Ok(match punct {
                        Punct::Plus => val,
                        Punct::Minus => -val,
                        Punct::Bang => (val == 0) as i64,
                        Punct::Tilde => !val,
                        _ => unreachable!(),
                    })
                }
                _ => self.parse_atom(),
            },
            _ => self.parse_atom(),
        }
    }

    fn parse_multiplicative(&mut self) -> Step<i64> {
        let mut left = self.parse_unary()?;

        while let Some(TokenValue::Punct(punct)) = self.peek()?.map(|t| t.value) {
            if let Punct::Star | Punct::Slash | Punct::Percent = punct {
                self.next()?;

                let right = self.parse_unary()?;

                match punct {
                    Punct::Star => left *= right,
                    Punct::Slash => left /= right,
                    Punct::Percent => left %= right,
                    _ => unreachable!(),
                }
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_additive(&mut self) -> Step<i64> {
        let mut left = self.parse_multiplicative()?;

        while let Some(TokenValue::Punct(punct)) = self.peek()?.map(|t| t.value) {
            if let Punct::Plus | Punct::Minus = punct {
                self.next()?;

                let right = self.parse_multiplicative()?;

                match punct {
                    Punct::Plus => left += right,
                    Punct::Minus => left -= right,
                    _ => unreachable!(),
                }
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_shift(&mut self) -> Step<i64> {
        let mut left = self.parse_additive()?;

        while let Some(TokenValue::Punct(punct)) = self.peek()?.map(|t| t.value) {
            if let Punct::LeftShift | Punct::RightShift = punct {
                self.next()?;

                let right = self.parse_additive()?;

                match punct {
                    Punct::LeftShift => left <<= right,
                    Punct::RightShift => left >>= right,
                    _ => unreachable!(),
                }
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_comparative(&mut self) -> Step<i64> {
        let mut left = self.parse_shift()?;

        while let Some(TokenValue::Punct(punct)) = self.peek()?.map(|t| t.value) {
            if let Punct::LeftAngle | Punct::RightAngle | Punct::LessEqual | Punct::GreaterEqual =
                punct
            {
                self.next()?;

                let right = self.parse_shift()?;

                match punct {
                    Punct::LeftAngle => left = (left < right) as i64,
                    Punct::RightAngle => left = (left > right) as i64,
                    Punct::LessEqual => left = (left <= right) as i64,
                    Punct::GreaterEqual => left = (left >= right) as i64,
                    _ => unreachable!(),
                }
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_equality(&mut self) -> Step<i64> {
        let mut left = self.parse_comparative()?;

        while let Some(TokenValue::Punct(punct)) = self.peek()?.map(|t| t.value) {
            if let Punct::EqualEqual | Punct::NotEqual = punct {
                self.next()?;

                let right = self.parse_comparative()?;

                match punct {
                    Punct::EqualEqual => left = (left == right) as i64,
                    Punct::NotEqual => left = (left != right) as i64,
                    _ => unreachable!(),
                }
            } else {
                break;
            }
        }

        Ok(left)
    }

    fn parse_bit_and(&mut self) -> Step<i64> {
        let mut left = self.parse_equality()?;

        while let Some(TokenValue::Punct(Punct::Ampersand)) = self.peek()?.map(|t| t.value) {
            self.next()?;

            let right = self.parse_equality()?;

            left &= right
        }

        Ok(left)
    }

    fn parse_bit_xor(&mut self) -> Step<i64> {
        let mut left = self.parse_bit_and()?;

        while let Some(TokenValue::Punct(Punct::Caret)) = self.peek()?.map(|t| t.value) {
            self.next()?;

            let right = self.parse_bit_and()?;

            left ^= right
        }

        Ok(left)
    }

    fn parse_bit_or(&mut self) -> Step<i64> {
        let mut left = self.parse_bit_xor()?;

        while let Some(TokenValue::Punct(Punct::Pipe)) = self.peek()?.map(|t| t.value) {
            self.next()?;

            let right = self.parse_bit_xor()?;

            left |= right
        }

        Ok(left)
    }

    fn parse_logical_and(&mut self) -> Step<i64> {
        let mut left = self.parse_bit_or()?;

        while let Some(TokenValue::Punct(Punct::LogicalAnd)) = self.peek()?.map(|t| t.value) {
            self.next()?;

            let right = self.parse_bit_or()?;

            left = (left != 0 && right != 0) as i64;
        }

        Ok(left)
    }

    fn parse_logical_or(&mut self) -> Step<i64> {
        let mut left = self.parse_logical_and()?;

        while let Some(TokenValue::Punct(Punct::LogicalAnd)) = self.peek()?.map(|t| t.value) {
            self.next()?;

            let right = self.parse_logical_and()?;

            left = (left != 0 || right != 0) as i64;
        }

        Ok(left)
    }

    pub fn evaluate(&mut self) -> Step<bool> {
        let root = self.parse_logical_or()?;

        if let Some(token) = self.next()? {
            Err(StepExit::Error((
                PreprocessorError::UnexpectedToken(token.value),
                token.location,
            )))
        } else {
            Ok(root != 0)
        }
    }
}
