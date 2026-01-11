//! Token definitions for TERAS-LANG
//!
//! Reference: TERAS-LANG-LEXER-SPEC_v1_0_0.md

/// Source location span
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

/// Token kinds for TERAS-LANG
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    IntLiteral(i64),
    FloatLiteral(f64),
    StringLiteral(String),
    BytesLiteral(Vec<u8>),
    BoolLiteral(bool),

    // Identifiers
    Identifier(String),
    TypeIdentifier(String),

    // Keywords - Types
    KwUnit,
    KwBool,
    KwInt,
    KwFloat,
    KwString,
    KwBytes,

    // Keywords - Control
    KwIf,
    KwThen,
    KwElse,
    KwMatch,
    KwWith,
    KwLet,
    KwIn,
    KwFn,
    KwReturn,

    // Keywords - Effects
    KwEffect,
    KwPerform,
    KwHandle,
    KwResume,

    // Keywords - Security
    KwPublic,
    KwSecret,
    KwClassify,
    KwDeclassify,
    KwProve,

    // Keywords - Capabilities
    KwRequire,
    KwGrant,
    KwCap,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Ampersand,
    Pipe,
    Caret,
    Tilde,
    Bang,
    Question,
    
    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    
    // Assignment
    Assign,
    ColonEq,
    
    // Arrows
    Arrow,      // ->
    FatArrow,   // =>
    EffArrow,   // -[eff]->
    
    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    
    // Punctuation
    Comma,
    Dot,
    Colon,
    Semicolon,
    At,
    Hash,
    
    // Special
    Eof,
    Error(String),
}

/// A token with its kind and span
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}
