use alloc::string::String;
use alloc::vec::Vec;

//TODO: Source file
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Location {
    /// Byte offset into the source string where the first char begins
    pub start: u32,
    /// Byte offset into the source string where the first char not belonging to
    /// this `Location` begins
    pub end: u32,
    /// used internally in the `#line` directive and the `__LINE__` macro
    pub(crate) line: u32,
}

impl Default for Location {
    fn default() -> Self {
        Location {
            start: 0,
            end: 0,
            line: 1,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Punct {
    // Compound assignments
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    ModAssign,
    LeftShiftAssign,
    RightShiftAssign,
    AndAssign,
    XorAssign,
    OrAssign,

    // Two character punctuation
    Increment,
    Decrement,
    LogicalAnd,
    LogicalOr,
    LogicalXor,
    LessEqual,
    GreaterEqual,
    EqualEqual,
    NotEqual,
    LeftShift,
    RightShift,

    // Parenthesis or similar
    LeftBrace,
    RightBrace,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,

    // Other one character punctuation
    LeftAngle,
    RightAngle,
    Semicolon,
    Comma,
    Colon,
    Dot,
    Equal,
    Bang,
    Minus,
    Tilde,
    Plus,
    Star,
    Slash,
    Percent,
    Pipe,
    Caret,
    Ampersand,
    Question,
}

#[derive(Clone, PartialEq, Debug)]
// TODO location?
pub enum PreprocessorError {
    IntegerOverflow,
    FloatParsingError,
    UnexpectedCharacter,
    UnexpectedToken(TokenValue),
    UnexpectedHash,
    UnexpectedNewLine,
    UnexpectedEndOfInput,
    TooFewDefineArguments,
    TooManyDefineArguments,
    ErrorDirective,
    DuplicateParameter,
    UnknownDirective,
    DefineRedefined,
    ElifOutsideOfBlock,
    ElseOutsideOfBlock,
    EndifOutsideOfBlock,
    ElifAfterElse,
    MoreThanOneElse,
    UnfinishedBlock,
    LineOverflow,
    NotSupported16BitLiteral,
    NotSupported64BitLiteral,
    MacroNotDefined,
    RecursionLimitReached,
    DivisionByZero,
    RemainderByZero,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Integer {
    pub value: u64,
    pub signed: bool,
    pub width: i32,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Float {
    pub value: f32,
    pub width: i32,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Version {
    pub tokens: Vec<Token>,
    pub is_first_directive: bool,
    pub has_comments_before: bool,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Extension {
    pub tokens: Vec<Token>,
    pub has_non_directive_before: bool,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Pragma {
    pub tokens: Vec<Token>,
}

#[derive(Clone, PartialEq, Debug)]
pub enum TokenValue {
    Ident(String),

    Integer(String),
    Float(String),
    Punct(Punct),

    Version(Version),
    Extension(Extension),
    Pragma(Pragma),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Token {
    pub value: TokenValue,
    pub location: Location,
    // TODO macro invocation stack?
}

pub fn parse_integer(mut s: &str) -> Result<Integer, PreprocessorError> {
    let mut signed = true;
    let width = 32;
    let mut radix = 10;

    // Parse prefixes and suffixes before calling u64::from_radix_str.

    // Integers may end with an optional width suffix.
    match s.chars().last() {
        Some('l' | 'L') => return Err(PreprocessorError::NotSupported64BitLiteral),
        Some('s' | 'S') => return Err(PreprocessorError::NotSupported16BitLiteral),
        _ => {}
    }

    // Prior to that there may be an optional signedness suffix.
    if let Some('u' | 'U') = s.chars().last() {
        signed = false;
        s = &s[..s.len() - 1];
    }

    // Strip the prefix for the integer radix.
    let mut chars = s.chars();
    if chars.next() == Some('0') {
        match chars.next() {
            Some('x' | 'X') => {
                // Hexadecimal numvers, strip first '0x'.
                s = &s[2..];
                radix = 16;
            }
            Some(_) => {
                // Octal numbers, strip first '0'.
                s = &s[1..];
                radix = 8;
            }
            // Just "0" is a decimal 0.
            None => {}
        }
    }

    Ok(Integer {
        signed,
        width,
        value: u64::from_str_radix(s, radix).map_err(|_err| PreprocessorError::IntegerOverflow)?,
    })
}

pub fn parse_float(mut s: &str) -> Result<Float, PreprocessorError> {
    let width = 32;

    // floats may end with an optional width suffix.
    match s.chars().last() {
        Some('l' | 'L') => return Err(PreprocessorError::NotSupported64BitLiteral),
        Some('h' | 'H') => return Err(PreprocessorError::NotSupported16BitLiteral),
        Some('f' | 'F') => {
            s = &s[..s.len() - 1];
        }
        _ => {}
    }

    Ok(Float {
        width,
        value: s
            .parse::<f32>()
            .map_err(|_| PreprocessorError::FloatParsingError)?,
    })
}

// TODO tests for parse_*
