//! RIINA Types (AST)
//!
//! Abstract Syntax Tree definitions corresponding to the formal Coq specification.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom
//!
//! Reference: `02_FORMAL/coq/foundations/Syntax.v`
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

/// Identifiers are strings.
pub type Ident = String;

/// Security Levels
///
/// RIINA uses a multi-level lattice for information flow control.
/// Matches Coq `security_level` in `foundations/Syntax.v`.
///
/// Lattice: Public ⊑ Internal ⊑ Session ⊑ User ⊑ System ⊑ Secret
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum SecurityLevel {
    /// Publicly observable
    Public,
    /// Internal use only
    Internal,
    /// Session-scoped
    Session,
    /// User-level sensitive
    User,
    /// System-level sensitive
    System,
    /// Maximum secrecy
    Secret,
}

impl SecurityLevel {
    /// Numeric encoding matching Coq `sec_level_num`
    #[must_use]
    pub const fn level(self) -> u8 {
        match self {
            Self::Public => 0,
            Self::Internal => 1,
            Self::Session => 2,
            Self::User => 3,
            Self::System => 4,
            Self::Secret => 5,
        }
    }

    /// Ordering: l1 ⊑ l2
    #[must_use]
    pub const fn leq(self, other: Self) -> bool {
        self.level() <= other.level()
    }

    /// Join (least upper bound)
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if self.level() <= other.level() {
            other
        } else {
            self
        }
    }

    /// Meet (greatest lower bound)
    #[must_use]
    pub const fn meet(self, other: Self) -> Self {
        if self.level() <= other.level() {
            self
        } else {
            other
        }
    }
}

/// Effects
///
/// Effects track observable behaviors of computations.
/// Matches Coq `effect` in `foundations/Syntax.v`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum Effect {
    // Base effects
    /// No observable effect
    Pure,
    /// Memory/state read
    Read,
    /// Memory/state write
    Write,
    /// File system access
    FileSystem,
    // Network effects
    /// Network I/O
    Network,
    /// Secure network (TLS)
    NetworkSecure,
    // Crypto effects
    /// Cryptographic operations
    Crypto,
    /// Random number generation
    Random,
    // System effects
    /// System calls
    System,
    /// Time/clock access
    Time,
    /// Process management
    Process,
    // RIINA product effects
    /// Panel UI operations
    Panel,
    /// Zirah API operations
    Zirah,
    /// Benteng auth operations
    Benteng,
    /// Sandi crypto operations
    Sandi,
    /// Menara device operations
    Menara,
    /// Gapura gateway operations
    Gapura,
}

/// Effect category for partial ordering.
/// Matches Coq `effect_category`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum EffectCategory {
    Pure,
    IO,
    Network,
    Crypto,
    System,
    Product,
}

impl Effect {
    /// Numeric level matching Coq `effect_level`
    #[must_use]
    pub const fn level(self) -> u8 {
        match self {
            Self::Pure => 0,
            Self::Read => 1,
            Self::Write => 2,
            Self::FileSystem => 3,
            Self::Network => 4,
            Self::NetworkSecure => 5,
            Self::Crypto => 6,
            Self::Random => 7,
            Self::System => 8,
            Self::Time => 9,
            Self::Process => 10,
            Self::Panel => 11,
            Self::Zirah => 12,
            Self::Benteng => 13,
            Self::Sandi => 14,
            Self::Menara => 15,
            Self::Gapura => 16,
        }
    }

    /// Category matching Coq `effect_cat`
    #[must_use]
    pub const fn category(self) -> EffectCategory {
        match self {
            Self::Pure => EffectCategory::Pure,
            Self::Read | Self::Write | Self::FileSystem => EffectCategory::IO,
            Self::Network | Self::NetworkSecure => EffectCategory::Network,
            Self::Crypto | Self::Random => EffectCategory::Crypto,
            Self::System | Self::Time | Self::Process => EffectCategory::System,
            Self::Panel | Self::Zirah | Self::Benteng
            | Self::Sandi | Self::Menara | Self::Gapura => EffectCategory::Product,
        }
    }

    /// Join: max in the hierarchy
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        if self.level() < other.level() {
            other
        } else {
            self
        }
    }

    /// Map effect to a default capability kind.
    /// Matches Coq `TCapabilityOld` backward-compat mapping.
    #[must_use]
    pub const fn to_capability_kind(self) -> CapabilityKind {
        match self {
            Self::Read => CapabilityKind::FileRead,
            Self::Write | Self::FileSystem => CapabilityKind::FileWrite,
            Self::Network | Self::NetworkSecure => CapabilityKind::NetConnect,
            Self::System | Self::Time => CapabilityKind::SysTime,
            Self::Random => CapabilityKind::SysRandom,
            Self::Process => CapabilityKind::ProcSpawn,
            _ => CapabilityKind::SysRandom, // fallback
        }
    }
}

/// Taint sources for untrusted data.
/// Matches Coq `taint_source` in `foundations/Syntax.v`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum TaintSource {
    NetworkExternal,
    NetworkInternal,
    UserInput,
    FileSystem,
    Database,
    Environment,
    GapuraRequest,
    ZirahEvent,
    ZirahEndpoint,
    BentengBiometric,
    SandiSignature,
    MenaraDevice,
}

/// Sanitizer markers for tainted data.
/// Matches Coq `sanitizer` in `foundations/Syntax.v`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sanitizer {
    // Web
    HtmlEscape,
    UrlEncode,
    JsEscape,
    CssEscape,
    // SQL
    SqlEscape,
    SqlParam,
    // Injection prevention
    XssFilter,
    PathTraversal,
    CommandEscape,
    LdapEscape,
    XmlEscape,
    // Validation
    JsonValidation,
    XmlValidation,
    EmailValidation,
    PhoneValidation,
    // Bound
    LengthBound(u64),
    RangeBound(u64, u64),
    RegexMatch(std::string::String),
    Whitelist(Vec<std::string::String>),
    // Crypto
    HashVerify,
    SignatureVerify,
    MacVerify,
    // RIINA product
    GapuraAuth,
    ZirahSession,
    BentengBiometric,
    SandiDecrypt,
    MenaraAttestation,
}

/// Capability kinds for access control.
/// Matches Coq `capability_kind` in `foundations/Syntax.v`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
pub enum CapabilityKind {
    FileRead,
    FileWrite,
    FileExecute,
    FileDelete,
    NetConnect,
    NetListen,
    NetBind,
    ProcSpawn,
    ProcSignal,
    SysTime,
    SysRandom,
    SysEnv,
    RootProduct,
    ProductAccess,
}

/// Capability with optional constraints.
/// Matches Coq `capability` in `foundations/Syntax.v`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Capability {
    Basic(CapabilityKind),
    Revocable(Box<Capability>),
    TimeBound(Box<Capability>, u64),
    Delegated(Box<Capability>, Ident),
}

/// Session types for binary communication protocols.
/// Matches Coq `session_type` in `foundations/Syntax.v`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SessionType {
    End,
    Send(Box<Ty>, Box<SessionType>),
    Recv(Box<Ty>, Box<SessionType>),
    Select(Box<SessionType>, Box<SessionType>),
    Branch(Box<SessionType>, Box<SessionType>),
    Rec(Ident, Box<SessionType>),
    Var(Ident),
}

/// Types
///
/// Core type constructors for RIINA.
/// Matches Coq `ty` in `foundations/Syntax.v`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    // Primitive types
    Unit,
    Bool,
    Int,
    String,
    Bytes,
    // Function types
    /// T1 -[ε]-> T2
    Fn(Box<Ty>, Box<Ty>, Effect),
    // Compound types
    /// T1 × T2
    Prod(Box<Ty>, Box<Ty>),
    /// T1 + T2
    Sum(Box<Ty>, Box<Ty>),
    /// List[T]
    List(Box<Ty>),
    /// Option[T]
    Option(Box<Ty>),
    // Reference types
    /// Ref[T]@l
    Ref(Box<Ty>, SecurityLevel),
    // Security types
    /// Secret[T] - classified data
    Secret(Box<Ty>),
    /// Labeled[T, l] - security label
    Labeled(Box<Ty>, SecurityLevel),
    /// Tainted[T, src] - tainted data
    Tainted(Box<Ty>, TaintSource),
    /// Sanitized[T, san] - sanitized data
    Sanitized(Box<Ty>, Sanitizer),
    /// Proof[T] - declassification proof
    Proof(Box<Ty>),
    // Capability types
    /// Cap[kind] - simple capability
    Capability(CapabilityKind),
    /// Full capability with constraints
    CapabilityFull(Capability),
    // Session types
    /// Chan[S] - channel with session
    Chan(SessionType),
    /// SecureChan[S, l] - secure channel
    SecureChan(SessionType, SecurityLevel),
    // Constant-time types
    /// ConstantTime[T] - for crypto
    ConstantTime(Box<Ty>),
    /// Zeroizing[T] - cleared on drop
    Zeroizing(Box<Ty>),
    /// Any type — matches any type during typechecking (for polymorphic builtins).
    /// Rust-only extension, not in Coq.
    Any,
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    // Arithmetic
    Add, Sub, Mul, Div, Mod,
    // Comparison
    Eq, Ne, Lt, Le, Gt, Ge,
    // Logical
    And, Or,
}

/// A source span (byte offsets) for LSP support.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    #[must_use]
    pub const fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Merge two spans into one covering both.
    #[must_use]
    pub const fn merge(self, other: Self) -> Self {
        Self {
            start: if self.start < other.start { self.start } else { other.start },
            end: if self.end > other.end { self.end } else { other.end },
        }
    }
}

/// A top-level declaration in a .rii file.
/// These are parsed but desugared to expressions for typechecking/codegen.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopLevelDecl {
    /// fungsi name(params) -> return_ty kesan eff { body }
    Function {
        name: Ident,
        params: Vec<(Ident, Ty)>,
        return_ty: Ty,
        effect: Effect,
        body: Box<Expr>,
    },
    /// biar name = expr;
    Binding {
        name: Ident,
        value: Box<Expr>,
    },
    /// Expression at top level (the program's main expression)
    Expr(Box<Expr>),
}

/// A spanned top-level declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedDecl {
    pub decl: TopLevelDecl,
    pub span: Span,
    /// Span of just the name (for go-to-definition).
    pub name_span: Option<Span>,
}

/// A complete .rii file
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub decls: Vec<TopLevelDecl>,
    /// Parallel span info for each decl (same length as `decls`).
    pub spans: Vec<SpannedDecl>,
}

impl Program {
    /// Create a Program without span info (backwards compat).
    #[must_use]
    pub fn new(decls: Vec<TopLevelDecl>) -> Self {
        Self { spans: Vec::new(), decls }
    }

    /// Create a Program with span info.
    #[must_use]
    pub fn with_spans(decls: Vec<TopLevelDecl>, spans: Vec<SpannedDecl>) -> Self {
        Self { decls, spans }
    }

    /// Desugar a program into a single expression.
    /// Functions become Let + Lam, bindings become Let, and the final
    /// expression is the program's value.
    #[must_use]
    pub fn desugar(self) -> Expr {
        let mut decls = self.decls;
        if decls.is_empty() {
            return Expr::Unit;
        }
        // Build from the end: last decl is the program body
        let last = decls.pop().unwrap();
        let mut result = match last {
            TopLevelDecl::Expr(e) => *e,
            TopLevelDecl::Binding { name, value } => {
                // Trailing binding with no continuation — body is Unit
                Expr::Let(name, value, Box::new(Expr::Unit))
            }
            TopLevelDecl::Function { name, params, body, .. } => {
                let lam = params.into_iter().rev().fold(*body, |acc, (p, ty)| {
                    Expr::Lam(p, ty, Box::new(acc))
                });
                Expr::Let(name, Box::new(lam), Box::new(Expr::Unit))
            }
        };
        // Wrap remaining decls from back to front
        for decl in decls.into_iter().rev() {
            result = match decl {
                TopLevelDecl::Expr(e) => {
                    Expr::Let("_".to_string(), e, Box::new(result))
                }
                TopLevelDecl::Binding { name, value } => {
                    Expr::Let(name, value, Box::new(result))
                }
                TopLevelDecl::Function { name, params, body, .. } => {
                    let lam = params.into_iter().rev().fold(*body, |acc, (p, ty)| {
                        Expr::Lam(p, ty, Box::new(acc))
                    });
                    Expr::Let(name, Box::new(lam), Box::new(result))
                }
            };
        }
        result
    }
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

    // Locations (runtime only — corresponds to Coq `ELoc : nat -> expr`)
    /// Store location (not in source; created during evaluation)
    Loc(u64),

    // Binary operations
    /// e1 op e2
    BinOp(BinOp, Box<Expr>, Box<Expr>),
}
