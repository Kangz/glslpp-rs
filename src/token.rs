use std::ops::Range;

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

impl From<Location> for Range<u32> {
    fn from(loc: Location) -> Range<u32> {
        loc.start..loc.end
    }
}

impl From<Location> for Range<usize> {
    fn from(loc: Location) -> Range<usize> {
        loc.start as usize..loc.end as usize
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

    Integer(Integer),
    Float(Float),
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
