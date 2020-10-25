#[derive(Clone, Copy, PartialEq, Debug)]
pub struct Location {
    pub line: u32,
    pub pos: u32,
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
    EndifOutsideOfBlock,
    UnfinishedBlock,
    LineOverflow,
}

#[derive(Clone, PartialEq, Debug)]
pub enum TokenValue {
    Ident(String),

    Int(i32),
    UInt(u32),
    //Float(f32), // TODO
    Punct(Punct),
}

#[derive(Clone, PartialEq, Debug)]
pub struct Token {
    pub value: TokenValue,
    pub location: Location,
    // TODO macro invocation stack?
}
