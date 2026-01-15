//! RIINA Types (AST)
//!
//! Abstract Syntax Tree definitions corresponding to the formal Coq specification.
//! RIINA = Rigorous Immutable Integrity No-attack Assured
//! Named for: Reena + Isaac + Imaan
//!
//! Reference: `02_FORMAL/coq/foundations/Syntax.v`
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

/// Identifiers are strings.
pub type Ident = String;

/// Security Levels
///
/// RIINA uses a two-point lattice for information flow:
/// - Public: Information that can be observed by anyone
/// - Secret: Information that must be protected
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum SecurityLevel {
    Public,
    Secret,
}

/// Effects
///
/// Effects track observable behaviors of computations.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum Effect {
    Pure,
    Read,
    Write,
    Network,
    Crypto,
    System,
}

impl Effect {
    pub fn level(&self) -> u8 {
        match self {
            Effect::Pure => 0,
            Effect::Read => 1,
            Effect::Write => 2,
            Effect::Network => 3,
            Effect::Crypto => 4,
            Effect::System => 5,
        }
    }

    pub fn join(self, other: Self) -> Self {
        if self.level() < other.level() {
            other
        } else {
            self
        }
    }
}

/// Types
///
/// Core type constructors for RIINA.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Unit,
    Bool,
    Int,
    String,
    Bytes,
    /// T1 -[ε]-> T2
    Fn(Box<Ty>, Box<Ty>, Effect),
    /// T1 × T2
    Prod(Box<Ty>, Box<Ty>),
    /// T1 + T2
    Sum(Box<Ty>, Box<Ty>),
    /// Ref[T]@l
    Ref(Box<Ty>, SecurityLevel),
    /// Secret[T]
    Secret(Box<Ty>),
    /// Proof[T]
    Proof(Box<Ty>),
    /// Cap[ε]
    Capability(Effect),
}

/// Expressions
///
/// Core expression forms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    // Values
    Unit,
    Bool(bool),
    Int(u64), // Using u64 to represent nat/int
    String(String),
    Var(Ident),

    // Functions
    /// λx:T. e
    Lam(Ident, Ty, Box<Expr>),
    /// e1 e2
    App(Box<Expr>, Box<Expr>),

    // Products
    /// (e1, e2)
    Pair(Box<Expr>, Box<Expr>),
    /// fst e
    Fst(Box<Expr>),
    /// snd e
    Snd(Box<Expr>),

    // Sums
    /// inl e : T
    Inl(Box<Expr>, Ty),
    /// inr e : T
    Inr(Box<Expr>, Ty),
    /// case e of inl x => e1 | inr y => e2
    Case(Box<Expr>, Ident, Box<Expr>, Ident, Box<Expr>),

    // Control
    /// if e1 then e2 else e3
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    /// let x = e1 in e2
    Let(Ident, Box<Expr>, Box<Expr>),

    // Effects
    /// perform ε e
    Perform(Effect, Box<Expr>),
    /// handle e with x => h
    Handle(Box<Expr>, Ident, Box<Expr>),

    // References
    /// ref e @ l
    Ref(Box<Expr>, SecurityLevel),
    /// !e
    Deref(Box<Expr>),
    /// e1 := e2
    Assign(Box<Expr>, Box<Expr>),

    // Security
    /// classify e
    Classify(Box<Expr>),
    /// declassify e with proof
    Declassify(Box<Expr>, Box<Expr>),
    /// prove e
    Prove(Box<Expr>),

    // Capabilities
    /// require ε in e
    Require(Effect, Box<Expr>),
    /// grant ε to e
    Grant(Effect, Box<Expr>),
}
