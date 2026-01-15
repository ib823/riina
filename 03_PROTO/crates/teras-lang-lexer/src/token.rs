//! Token Definitions

use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    #[must_use]
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    #[must_use]
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // Identifiers
    Identifier(String),
    RawIdentifier(String),
    Lifetime(String),
    Label(String),

    // Literals
    LiteralBool(bool),
    LiteralInt(String, Option<String>), // value, suffix
    LiteralFloat(String, Option<String>), // value, suffix
    LiteralChar(char),
    LiteralString(String),
    LiteralByte(u8),
    LiteralByteString(Vec<u8>),

    // Keywords
    KwFn,
    KwLet,
    KwMut,
    KwConst,
    KwStatic,
    KwType,
    KwStruct,
    KwEnum,
    KwUnion,
    KwTrait,
    KwImpl,
    KwWhere,
    KwFor,
    KwIf,
    KwElse,
    KwMatch,
    KwLoop,
    KwWhile,
    KwWith,
    KwBreak,
    KwContinue,
    KwReturn,
    KwMod,
    KwPub,
    KwUse,
    KwAs,
    KwSelfValue, // self
    KwSelfType,  // Self
    KwSuper,
    KwCrate,
    KwExtern,
    KwAsync,
    KwAwait,
    KwMove,
    KwRef,
    KwUnsafe,
    KwEffect,
    KwPerform,
    KwHandle,
    KwResume,
    KwAbort,
    KwSecret,
    KwClassify,
    KwPublic,
    KwTainted,
    KwDeclassify,
    KwProve,
    KwInl,
    KwInr,
    KwSanitize,
    KwSession,
    KwSend,
    KwRecv,
    KwSelect,
    KwBranch,
    KwEnd,
    KwCapability,
    KwRevoke,
    KwAtomic,
    KwFence,
    KwAcquire,
    KwRelease,
    KwSeqCst,
    KwRelaxed,
    KwAcqRel,
    KwProduct,
    KwCt,
    KwSpeculationSafe,
    KwCombined,
    KwZeroize,

    // Operators & Punctuation
    Plus,       // +
    Minus,      // -
    Star,       // *
    Slash,      // /
    Percent,    // %
    And,        // &
    Or,         // |
    Caret,      // ^
    Not,        // !
    Shl,        // <<
    Shr,        // >>
    
    PlusEq,     // +=
    MinusEq,    // -=
    StarEq,     // *=
    SlashEq,    // /=
    PercentEq,  // %=
    AndEq,      // &=
    OrEq,       // |=
    CaretEq,    // ^=
    ShlEq,      // <<=
    ShrEq,      // >>=

    Eq,         // =
    EqEq,       // ==
    Ne,         // !=
    Lt,         // <
    Gt,         // >
    Le,         // <=
    Ge,         // >=
    
    AndAnd,     // &&
    OrOr,       // ||
    
    Dot,        // .
    DotDot,     // ..
    DotDotEq,   // ..=
    Comma,      // ,
    Colon,      // :
    ColonEq,    // :=
    Semi,       // ;
    Question,   // ?
    At,         // @
    Hash,       // #
    Dollar,     // $
    Arrow,      // ->
    FatArrow,   // =>
    ColonColon, // ::
    
    // Delimiters
    LParen,     // (
    RParen,     // )
    LBracket,   // [
    RBracket,   // ]
    LBrace,     // {
    RBrace,     // }

    // End of File
    Eof,
}