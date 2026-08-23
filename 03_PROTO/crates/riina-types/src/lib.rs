// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA Types (AST)
//!
//! Abstract Syntax Tree definitions corresponding to the formal Coq specification.
//! RIINA = Rigorous Immutable Invariant, No Assumptions
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

    /// Convert from numeric level back to SecurityLevel.
    #[must_use]
    pub const fn from_level(n: u8) -> Self {
        match n {
            0 => Self::Public,
            1 => Self::Internal,
            2 => Self::Session,
            3 => Self::User,
            4 => Self::System,
            _ => Self::Secret,
        }
    }
}

/// Linearity qualifiers for substructural type system.
///
/// Matches Coq `Linearity` in `domains/LinearTypes.v`.
/// Controls how many times a variable binding may be used.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Linearity {
    /// Linear: must be used exactly once
    Linear,
    /// Affine: may be used at most once (can be dropped)
    Affine,
    /// Relevant: must be used at least once (can be duplicated)
    Relevant,
    /// Unrestricted: no usage constraints (default)
    Unrestricted,
}

/// Usage count for linearity tracking.
///
/// Matches Coq `Usage` in `domains/LinearTypes.v`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Usage {
    /// Not yet used
    Zero,
    /// Used exactly once
    One,
    /// Used more than once
    Many,
}

impl Usage {
    /// Increment usage: Zero→One, One→Many, Many→Many
    #[must_use]
    pub const fn increment(self) -> Self {
        match self {
            Usage::Zero => Usage::One,
            Usage::One => Usage::Many,
            Usage::Many => Usage::Many,
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
    /// Local mutable state (for self-hosting)
    ///
    /// This effect allows local mutable variables within a function scope.
    /// Unlike Write, Mut does not escape the function boundary and is
    /// safe for self-hosting the compiler.
    ///
    /// In Bahasa Melayu: `kesan Ubah`
    ///
    /// # Example
    /// ```ignore
    /// fungsi parse_expr(tokens: &[Token]) -> (Expr, &[Token]) kesan Ubah {
    ///     biar ubah idx = 0;  // Mutable local
    ///     // ... parsing logic
    /// }
    /// ```
    Mut,
    /// Memory allocation (heap)
    ///
    /// This effect tracks heap allocation operations. Used when creating
    /// new references or growing data structures.
    Alloc,
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
            Self::Mut => 1, // Local mutation (below Read)
            Self::Read => 2,
            Self::Alloc => 3, // Heap allocation
            Self::Write => 4,
            Self::FileSystem => 5,
            Self::Network => 6,
            Self::NetworkSecure => 7,
            Self::Crypto => 8,
            Self::Random => 9,
            Self::System => 10,
            Self::Time => 11,
            Self::Process => 12,
            Self::Panel => 13,
            Self::Zirah => 14,
            Self::Benteng => 15,
            Self::Sandi => 16,
            Self::Menara => 17,
            Self::Gapura => 18,
        }
    }

    /// Category matching Coq `effect_cat`
    #[must_use]
    pub const fn category(self) -> EffectCategory {
        match self {
            Self::Pure | Self::Mut => EffectCategory::Pure, // Mut is pure from caller perspective
            Self::Read | Self::Write | Self::Alloc | Self::FileSystem => EffectCategory::IO,
            Self::Network | Self::NetworkSecure => EffectCategory::Network,
            Self::Crypto | Self::Random => EffectCategory::Crypto,
            Self::System | Self::Time | Self::Process => EffectCategory::System,
            Self::Panel
            | Self::Zirah
            | Self::Benteng
            | Self::Sandi
            | Self::Menara
            | Self::Gapura => EffectCategory::Product,
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

    /// Check if this effect is "local" (doesn't escape function scope)
    #[must_use]
    pub const fn is_local(self) -> bool {
        matches!(self, Self::Pure | Self::Mut)
    }

    /// Map effect to a default capability kind.
    /// Matches Coq `TCapabilityOld` backward-compat mapping.
    #[must_use]
    pub const fn to_capability_kind(self) -> CapabilityKind {
        match self {
            Self::Read => CapabilityKind::FileRead,
            Self::Write | Self::Alloc | Self::FileSystem => CapabilityKind::FileWrite,
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
    UrlAllowlist,
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

// ============================================================================
// Store Typing (Σ)
// ============================================================================

/// Memory location identifier.
///
/// Matches Coq `loc := nat` in `foundations/Typing.v`.
/// Locations are created during reference allocation and are unique identifiers
/// for memory cells in the store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Location(pub usize);

impl Location {
    /// Create a new location with the given index.
    #[must_use]
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// Get the raw index of this location.
    #[must_use]
    pub const fn index(self) -> usize {
        self.0
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "loc_{}", self.0)
    }
}

/// Store typing context (Σ in the Coq type judgment).
///
/// Matches Coq `store_ty := list (loc * ty * security_level)` in `foundations/Typing.v`.
///
/// The store typing maps memory locations to their types and security levels.
/// This is used during typechecking to ensure that:
/// 1. Dereferencing a location returns the correct type
/// 2. Assignments respect type compatibility
/// 3. Security levels are preserved across memory operations
///
/// # Example
/// ```ignore
/// let mut sigma = StoreTy::new();
/// let loc = sigma.extend(Ty::Int, SecurityLevel::Public);
/// assert_eq!(sigma.lookup(&loc), Some(&(Ty::Int, SecurityLevel::Public)));
/// ```
#[derive(Debug, Clone, Default)]
pub struct StoreTy {
    /// Bindings from locations to (type, security_level) pairs.
    bindings: std::collections::HashMap<Location, (Ty, SecurityLevel)>,
    /// Counter for generating fresh locations.
    next_loc: usize,
}

impl StoreTy {
    /// Create an empty store typing context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up a location in the store typing.
    ///
    /// Matches Coq `store_ty_lookup l Σ : option (ty * security_level)`.
    #[must_use]
    pub fn lookup(&self, loc: &Location) -> Option<&(Ty, SecurityLevel)> {
        self.bindings.get(loc)
    }

    /// Allocate a new location with the given type and security level.
    ///
    /// Returns the freshly allocated location. This corresponds to the
    /// typing rule T_Ref which creates new entries in Σ.
    pub fn extend(&mut self, ty: Ty, sl: SecurityLevel) -> Location {
        let loc = Location::new(self.next_loc);
        self.next_loc += 1;
        self.bindings.insert(loc, (ty, sl));
        loc
    }

    /// Update the type and security level at an existing location.
    ///
    /// This is used for strong updates where the type of a location changes.
    /// Returns `true` if the location existed and was updated.
    pub fn update(&mut self, loc: Location, ty: Ty, sl: SecurityLevel) -> bool {
        if let std::collections::hash_map::Entry::Occupied(mut e) = self.bindings.entry(loc) {
            e.insert((ty, sl));
            true
        } else {
            false
        }
    }

    /// Check if a location exists in the store typing.
    #[must_use]
    pub fn contains(&self, loc: &Location) -> bool {
        self.bindings.contains_key(loc)
    }

    /// Get the number of locations in the store typing.
    #[must_use]
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if the store typing is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Iterate over all (location, type, security_level) triples.
    pub fn iter(&self) -> impl Iterator<Item = (&Location, &Ty, &SecurityLevel)> {
        self.bindings.iter().map(|(l, (t, s))| (l, t, s))
    }
}

impl PartialEq for StoreTy {
    fn eq(&self, other: &Self) -> bool {
        self.bindings == other.bindings
    }
}

impl Eq for StoreTy {}

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
    /// The default integer type (`Nombor`) — an unbounded machine integer.
    Int,
    /// A sized integer type (numeric-tower slice): `bits` ∈ {8,16,32,64},
    /// `signed` distinguishes `iN` from `uN` (e.g. `u8` = `{bits:8, signed:false}`).
    /// Representationally compatible with `Int` for codegen; width-aware
    /// arithmetic semantics are a later numeric-tower phase.
    IntN { bits: u8, signed: bool },
    /// Arbitrary-precision signed integer (`besar`) — the numeric-tower BigInt
    /// type. A distinct type that does NOT silently interoperate with `Int`
    /// (mixing would hide a precision boundary); convert explicitly via `besar`.
    BigInt,
    /// Arbitrary-precision decimal (`perpuluhan`) — exact base-10 arithmetic for
    /// finance. A distinct type; does not silently mix with `Int`/`BigInt`.
    Decimal,
    /// Fixed-scale decimal (`wang` money / `titik_tetap`) — a `mantissa` with a
    /// *fixed* scale: arithmetic rounds half-to-even back to that scale and
    /// display preserves trailing zeros (`3.30`, `100.00`). A distinct type; does
    /// not silently mix with `Int`/`BigInt`/`Decimal`.
    Fixed,
    /// Binary fixed-point — Q-format (`qmn`): `raw / 2^frac_bits` over a bounded
    /// machine word (arithmetic wraps on overflow). A distinct type; does not
    /// silently mix with the other numeric types.
    FixedBin,
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
    // FFI types (C interop)
    /// Raw pointer (*T) for FFI boundary
    RawPtr(Box<Ty>),
    /// C char type
    CChar,
    /// C int type
    CInt,
    /// C void type
    CVoid,

    // ── JALINAN Phase 6 types ──────────────────────────────────────────
    /// Actor[State, Msg] — typed actor reference with state and message types
    Actor(Box<Ty>, Box<Ty>),
    /// Choreography[roles, protocol] — global multiparty session protocol
    Choreography(Vec<Ident>, SessionType),
    /// ContentAddressed[T] — content-addressed (Merkle) value
    ContentAddressed(Box<Ty>),
    /// CRDT[T, Op] — conflict-free replicated data type
    CRDT(Box<Ty>, Box<Ty>),
    /// Supervisor[T] — fault-tolerance supervisor for actor type T
    Supervisor(Box<Ty>),

    // ── Blockchain + Syariah Phase J6 types ─────────────────────────
    /// SmartContract[T] — capability-gated smart-contract state
    SmartContract(Box<Ty>),
    /// Token[T] — conserved transferable value
    Token(Box<Ty>),
    /// SyariahCompliant[T] — effect-constrained value
    SyariahCompliant(Box<Ty>),

    // ── CAHAYA Phase J5 types ──────────────────────────────────────
    /// Color — RGBA color with compile-time contrast checking
    Color,
    /// Element — UI element type
    Element,
    /// Layout — container for UI elements
    Layout,
    /// Style — CSS-like style properties
    UIStyle,
    /// AccessibleText — text with proven WCAG contrast
    AccessibleText,
}

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // Logical
    And,
    Or,
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
            start: if self.start < other.start {
                self.start
            } else {
                other.start
            },
            end: if self.end > other.end {
                self.end
            } else {
                other.end
            },
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
        /// The function's effect as a single lattice value (the join of the
        /// declared components) — used for effect propagation and codegen.
        effect: Effect,
        /// The *components* of a compound declared effect (`kesan (A, B, C)` ⇒
        /// `[A, B, C]`). The lattice `effect` field is lossy (it collapses a
        /// compound to the max-level component), so this preserves the full set
        /// for capability granting: each component is granted in the body, which
        /// makes capability-gating sound for compound-effect functions. For a
        /// single declared effect this is a one-element vector.
        effect_set: Vec<Effect>,
        body: Box<Expr>,
    },
    /// `biar name = expr;` at top level. `is_mut` records a `biar ubah`, which
    /// becomes an [`Expr::LetMut`] slot rather than an immutable [`Expr::Let`] —
    /// without it a top-level `selagi` counting down a top-level counter never
    /// terminates, because the write is discarded.
    Binding {
        name: Ident,
        value: Box<Expr>,
        is_mut: bool,
    },
    /// Expression at top level (the program's main expression)
    Expr(Box<Expr>),
    /// luaran "C" { ... } — extern block for FFI declarations
    ExternBlock { abi: String, decls: Vec<ExternDecl> },
    /// ujian "name" { body } — inline test block
    Test { name: String, body: Box<Expr> },
}

/// A single declaration inside an extern block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternDecl {
    pub name: Ident,
    pub params: Vec<(Ident, Ty)>,
    pub ret_ty: Ty,
    pub effect: Effect,
}

/// A spanned top-level declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedDecl {
    pub decl: TopLevelDecl,
    pub span: Span,
    /// Span of just the name (for go-to-definition).
    pub name_span: Option<Span>,
}

/// One `guna <name>;` import of a sibling `.rii` file (REQ-71).
///
/// Only a SINGLE-segment path is a file import. A multi-segment path such as
/// `guna std::teks;` names the builtin namespace, carries no file, and is not
/// recorded here — that keeps every pre-module-system example working.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Import {
    /// The module name, which is also its file stem (`kira` ⇒ `kira.rii`).
    pub module: Ident,
    /// Span of the module name, for diagnostics.
    pub span: Span,
}

/// A complete .rii file
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub decls: Vec<TopLevelDecl>,
    /// Parallel span info for each decl (same length as `decls`).
    pub spans: Vec<SpannedDecl>,
    /// Sibling modules imported with `guna <name>;`, in source order (REQ-71).
    /// Empty for a single-file program, which is why `new`/`with_spans` still
    /// build a valid `Program` without mentioning it.
    pub imports: Vec<Import>,
    /// Top-level names declared `awam` (public). Everything else is
    /// module-private and may not be named from another module (REQ-71).
    pub public_names: Vec<Ident>,
}

/// Parameter name given to a zero-parameter function's synthesised `()` param.
///
/// Leading `_` keeps it out of unused-name diagnostics, and nothing in
/// `07_EXAMPLES` or the stdlib binds it, so the synthesised binder cannot shadow
/// a name the body needs.
pub const UNIT_PARAM: &str = "_unit";

/// The program entry point, invoked automatically when a program has no
/// trailing top-level expression.
pub const ENTRY_POINT: &str = "utama";

/// The declared type of a function with these parameters, return type and
/// effect — `(A, B) -> R ! E` becomes `A -> B -> R ! E`.
///
/// A ZERO-parameter function is `Unit -> R ! E`, matching the synthesised `()`
/// parameter `build_lambda` gives it. This is the single source of truth: the
/// typechecker seeds its top-level environment from here and desugaring builds
/// the matching lambda from here, so the two cannot disagree about a function's
/// arity. They did disagree — the typechecker kept computing the old bare
/// return type for zero-parameter functions after desugaring had moved on, and
/// every zero-arg call then failed with "Expected function type, found Int".
#[must_use]
pub fn declared_fn_ty(params: &[(Ident, Ty)], return_ty: &Ty, effect: Effect) -> Ty {
    if params.is_empty() {
        return Ty::Fn(Box::new(Ty::Unit), Box::new(return_ty.clone()), effect);
    }
    params
        .iter()
        .rev()
        .fold(return_ty.clone(), |ret, (_, param_ty)| {
            Ty::Fn(Box::new(param_ty.clone()), Box::new(ret), effect)
        })
}

/// Desugar a single function decl into a LetRec binding.
#[allow(clippy::boxed_local)]
/// Build the (lambda, function-type) pair for a top-level function decl.
///
/// A zero-parameter function gets a SYNTHESISED `()` parameter, so it is a real
/// function like any other: `fungsi f() -> T kesan E` becomes
/// `Lam(_unit, Unit, body) : Unit -> T ! E`.
///
/// It used to yield its body directly, as a bare binding typed at the return
/// type — "a global thunk". That was not a function in any sense that survived
/// contact with the semantics (master plan REQ-68), and all three of these were
/// measured, with the interpreter and C backend agreeing on the wrong answer:
///   * the body ran ONCE, when the binding was evaluated, no matter how many
///     times it was called — two calls printed one line;
///   * it ran even when the function was NEVER called;
///   * it ran BEFORE `utama`, so its output preceded the program's own first
///     line, and its effects escaped their function entirely.
///
/// `pulang` was broken there too: with no `Lam` there was no IR function to
/// return from, so an early return would have returned from the CALLER (REQ-80).
#[must_use]
pub fn desugar_function(
    params: Vec<(Ident, Ty)>,
    return_ty: Ty,
    effect: Effect,
    body: Box<Expr>,
) -> (Expr, Ty) {
    let fn_ty = declared_fn_ty(&params, &return_ty, effect);
    if params.is_empty() {
        return (Expr::Lam(UNIT_PARAM.to_string(), Ty::Unit, body), fn_ty);
    }
    let lam = params.iter().rev().fold(*body, |acc, (p, ty)| {
        Expr::Lam(p.clone(), ty.clone(), Box::new(acc))
    });
    (lam, fn_ty)
}

/// Desugar an extern block into Let bindings for each extern decl.
fn desugar_extern_block(decls: Vec<ExternDecl>, continuation: Expr) -> Expr {
    let mut result = continuation;
    for decl in decls.into_iter().rev() {
        let param_names: Vec<Ident> = decl.params.iter().map(|(n, _)| n.clone()).collect();
        let args: Vec<Expr> = param_names.iter().map(|n| Expr::Var(n.clone())).collect();
        let ffi_call = Expr::FFICall {
            name: decl.name.clone(),
            args,
            ret_ty: decl.ret_ty.clone(),
        };
        let lam = decl.params.iter().rev().fold(ffi_call, |acc, (p, ty)| {
            Expr::Lam(p.clone(), ty.clone(), Box::new(acc))
        });
        result = Expr::Let(decl.name, None, Box::new(lam), Box::new(result));
    }
    result
}

impl Program {
    /// Create a Program without span info (backwards compat).
    #[must_use]
    pub fn new(decls: Vec<TopLevelDecl>) -> Self {
        Self {
            spans: Vec::new(),
            decls,
            imports: Vec::new(),
            public_names: Vec::new(),
        }
    }

    /// Create a Program with span info.
    #[must_use]
    pub fn with_spans(decls: Vec<TopLevelDecl>, spans: Vec<SpannedDecl>) -> Self {
        Self {
            decls,
            spans,
            imports: Vec::new(),
            public_names: Vec::new(),
        }
    }

    /// Create a Program carrying module metadata (REQ-71 module system).
    #[must_use]
    pub fn with_modules(
        decls: Vec<TopLevelDecl>,
        spans: Vec<SpannedDecl>,
        imports: Vec<Import>,
        public_names: Vec<Ident>,
    ) -> Self {
        Self {
            decls,
            spans,
            imports,
            public_names,
        }
    }

    /// Whether `decls` declares the entry point as a ZERO-parameter function.
    ///
    /// Only a zero-parameter `utama` is auto-invoked: one that takes arguments
    /// has nothing to pass it, so it stays a plain binding rather than becoming
    /// an application that could not type-check.
    fn declares_entry_point(decls: &[TopLevelDecl]) -> bool {
        decls.iter().any(|d| {
            matches!(
                d,
                TopLevelDecl::Function { name, params, .. }
                    if name == ENTRY_POINT && params.is_empty()
            )
        })
    }

    /// Desugar a program into a single expression.
    /// Functions become LetRec + Lam (recursive binding), bindings become Let,
    /// extern blocks introduce FFICall wrappers, and the final expression is
    /// the program's value.
    #[must_use]
    pub fn desugar(self) -> Expr {
        let mut decls = self.decls;
        if decls.is_empty() {
            return Expr::Unit;
        }

        // A trailing top-level EXPRESSION is the program body; everything else
        // (including the trailing function — usually `utama`) is a binding, so
        // all top-level functions land in the mutually-recursive group built by
        // `wrap_decls` (REQ-44 forward references).
        //
        // Otherwise the body CALLS `utama`. It used to be left as `Unit`, which
        // worked only because a zero-parameter function was a thunk: evaluating
        // its binding ran its body, so the program ran as a side effect of being
        // bound. Now that `utama` is a real `Unit -> T` function (REQ-68),
        // nothing would run unless it is applied.
        let body = if matches!(decls.last(), Some(TopLevelDecl::Expr(_))) {
            match decls.pop() {
                Some(TopLevelDecl::Expr(e)) => *e,
                _ => Expr::Unit,
            }
        } else if Self::declares_entry_point(&decls) {
            // The call is SEQUENCED, not returned: the program's value stays
            // `Unit`, exactly as when `utama`'s binding ran it. Returning it
            // instead would make every compiled program print its own exit code
            // as a trailing line (measured: `satu` became `satu\n7`), because
            // the backends print a non-Unit program value.
            Expr::Let(
                "_".to_string(),
                None,
                Box::new(Expr::App(
                    Box::new(Expr::Var(ENTRY_POINT.to_string())),
                    Box::new(Expr::Unit),
                )),
                Box::new(Expr::Unit),
            )
        } else {
            Expr::Unit
        };

        Self::wrap_decls(decls, body)
    }

    /// Desugar declarations with a specific body expression.
    ///
    /// This is useful for the test runner: desugar the non-test declarations
    /// once for each test body, without needing to push a fake TopLevelDecl::Expr.
    pub fn desugar_with_body(self, body: Expr) -> Expr {
        Self::wrap_decls(self.decls, body)
    }

    /// Wrap a body expression with a chain of Let/LetRec bindings from declarations.
    fn wrap_decls(decls: Vec<TopLevelDecl>, body: Expr) -> Expr {
        let mut result = body;
        // Consecutive top-level function decls form ONE mutually-recursive group
        // (all names in scope in every body + the continuation) so forward
        // references / mutual recursion work (REQ-44). Non-function decls flush
        // the pending group and wrap as before, preserving backward-ref scoping
        // (a function can still see an earlier top-level `biar` binding).
        // Iterating back-to-front, we accumulate functions in `pending` (reversed)
        // and flush on any non-function decl or at the end.
        let mut pending: Vec<(Ident, Ty, Expr)> = Vec::new();
        let flush = |pending: &mut Vec<(Ident, Ty, Expr)>, result: Expr| -> Expr {
            if pending.is_empty() {
                result
            } else {
                pending.reverse(); // restore source order
                Expr::LetRecGroup(std::mem::take(pending), Box::new(result))
            }
        };
        for decl in decls.into_iter().rev() {
            match decl {
                TopLevelDecl::Function {
                    name,
                    params,
                    return_ty,
                    effect,
                    body,
                    ..
                } => {
                    let (lam, fn_ty) = desugar_function(params, return_ty, effect, body);
                    pending.push((name, fn_ty, lam));
                }
                TopLevelDecl::Expr(e) => {
                    result = flush(&mut pending, result);
                    let bind_name = match e.as_ref() {
                        Expr::ActorDecl { name, .. } => name.clone(),
                        _ => "_".to_string(),
                    };
                    result = Expr::Let(bind_name, None, e, Box::new(result));
                }
                TopLevelDecl::Binding {
                    name,
                    value,
                    is_mut,
                } => {
                    result = flush(&mut pending, result);
                    result = if is_mut {
                        Expr::LetMut(name, value, Box::new(result))
                    } else {
                        Expr::Let(name, None, value, Box::new(result))
                    };
                }
                TopLevelDecl::ExternBlock { decls: edecls, .. } => {
                    result = flush(&mut pending, result);
                    result = desugar_extern_block(edecls, result);
                }
                TopLevelDecl::Test { .. } => {
                    result = flush(&mut pending, result);
                }
            }
        }
        flush(&mut pending, result)
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
    /// Sized integer literal: `42u8`, `7i32`. The numeric-tower counterpart of
    /// `Int`, carrying the bit width and signedness so it types as the distinct
    /// `Ty::IntN { bits, signed }` (not the default `Ty::Int`) and so arithmetic
    /// wraps at the declared width. `value` holds the lexed magnitude already
    /// reduced modulo `2^bits` (a leading `-` is a separate unary-minus token, so
    /// `-128i8` is `Neg(IntN{value:128,..})`). Kept as an additive variant so the
    /// hundreds of existing `Int(_)` sites are untouched.
    IntN { value: u64, bits: u8, signed: bool },
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
    /// let x = e1 in e2 (with optional linearity qualifier)
    Let(Ident, Option<Linearity>, Box<Expr>, Box<Expr>),
    /// Early return: `pulang e`. Evaluating it unwinds to the nearest enclosing
    /// function-application boundary, yielding `e` as that call's result. Its own
    /// type is `Any` (it never returns to its evaluation context), so it unifies
    /// with any branch/sequence type.
    Return(Box<Expr>),
    /// `selagi cond { body }` — iterate `body` while `cond` evaluates to true.
    ///
    /// A real loop, not a desugaring. Until 2026-08 `selagi` was rewritten by the
    /// parser into `if cond { body; () } else { ()}`, which executed the body at
    /// most ONCE while presenting itself as a loop — silently wrong output with
    /// no diagnostic. A dedicated node keeps `pulang` unwinding to the enclosing
    /// FUNCTION (a lambda-based desugaring would have caught it one iteration
    /// out) and gives `putus`/`lanjut` a scope to name.
    ///
    /// The loop's own value is always `()`; RIINA's mutable state lives in `ruj`
    /// cells (the store), so nothing is carried between iterations in a binding
    /// and the CFG needs no loop-header phi.
    While(Box<Expr>, Box<Expr>),
    /// `putus` — exit the innermost enclosing loop. Type `Any` (it never returns
    /// to its evaluation context), so it unifies with any branch type.
    Break,
    /// `lanjut` — skip to the next iteration of the innermost enclosing loop.
    /// Type `Any`, as for `Break`.
    Continue,

    // ── Mutable locals ────────────────────────────────────────────────────
    // A `biar ubah x` binding is a genuine mutable SLOT, distinct from both an
    // immutable `biar` and a first-class `ruj` cell.
    //
    // Until 2026-08 `ubah` was decorative: `x = e;` re-parsed as a shadowing
    // `biar`, so a write inside a `kalau`/loop body was discarded at the closing
    // brace with no diagnostic. Real loops make that unfixable by convention —
    // an accumulator that resets every iteration either loops forever or answers
    // wrong — so the slot is now real.
    //
    // Slots are deliberately NOT `Ref`/`Deref`/`Assign`: those carry
    // `Effect::Read`/`Effect::Write` because a `ruj` cell is first class and can
    // escape, and their rules mirror Coq `Typing.v` T_Ref/T_Deref/T_Assign,
    // which must not be weakened. A slot cannot escape — the parser emits
    // `SlotGet`/`SlotSet` only for names it has in lexical scope and never
    // exposes the slot itself as a value — so reading and writing one is
    // observationally pure, the standard encapsulated-state result. Like `While`,
    // `Return` and `BinOp`, these are compiler-level nodes with no counterpart in
    // `foundations/Syntax.v` yet; see `docs/guide/MUTABLE_STATE.md`.
    /// `biar ubah x = e1; e2` — bind a fresh mutable slot for the extent of `e2`.
    LetMut(Ident, Box<Expr>, Box<Expr>),
    /// Read the mutable slot bound to this name.
    SlotGet(Ident),
    /// `x = e` — write the mutable slot bound to this name. Value is `()`.
    SlotSet(Ident, Box<Expr>),

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

    // Recursive binding
    /// let rec f : T = e1 in e2
    LetRec(Ident, Ty, Box<Expr>, Box<Expr>),
    /// Mutually-recursive binding GROUP: `let rec f1:T1=e1 and ... and fn:Tn=en in cont`.
    /// All group names are in scope in every bound expression AND the continuation,
    /// so top-level functions can forward-reference / mutually recurse (REQ-44).
    /// Each entry is (name, declared type, bound lambda). Mechanized-sound: the
    /// recursion rule is proven type-safe in `foundations/RecursionSafety.v` (`fix`);
    /// `let rec f = lam` = `let f = fix(λf.lam)`, generalized to a group here.
    LetRecGroup(Vec<(Ident, Ty, Expr)>, Box<Expr>),

    // Binary operations
    /// e1 op e2
    BinOp(BinOp, Box<Expr>, Box<Expr>),

    // Collections
    /// List literal: [e1, e2, ...]. Empty `[]` is the empty list.
    ListLit(Vec<Expr>),
    /// Record literal: `Name { field1: e1, field2: e2, ... }`. The type name is
    /// retained for diagnostics only; records are structural (string-keyed) at
    /// runtime. Fields are stored in source order.
    RecordLit(Ident, Vec<(Ident, Expr)>),
    /// Field access: `e.field`.
    FieldAccess(Box<Expr>, Ident),

    // FFI
    /// Foreign function call
    FFICall {
        name: String,
        args: Vec<Expr>,
        ret_ty: Ty,
    },

    // ── JALINAN Phase 6 expressions ────────────────────────────────────
    /// Actor declaration: pelaku Name { keadaan: StateType, kendalikan msg { ... } }
    ActorDecl {
        name: Ident,
        state_ty: Ty,
        message_ty: Ty,
        init_state: Box<Expr>,
        handler: Box<Expr>,
    },
    /// Choreography block: koreografi ProtocolName { peranan A, B; ... }
    ChoreographyBlock {
        name: Ident,
        roles: Vec<Ident>,
        protocol: SessionType,
    },
    /// Spawn actor: lahir ActorType(init_state)
    Spawn(Box<Expr>, Box<Expr>),
    /// Send message to actor: hantar(actor, message)
    ActorSend(Box<Expr>, Box<Expr>),
    /// Receive message from actor: terima(actor)
    ActorRecv(Box<Expr>),
    /// CRDT merge: gabung(crdt1, crdt2)
    CRDTMerge(Box<Expr>, Box<Expr>),
    /// Content hash: cincang(value)
    ContentHash(Box<Expr>),
    /// Content hash verification: sahkan(expected_hash, value)
    ContentVerify(Box<Expr>, Box<Expr>),

    // ── Blockchain + Syariah Phase J6 expressions ───────────────────
    /// Smart-contract deployment: kontrak_pintar { expr }
    ContractDeploy(Box<Expr>),
    /// Token transfer: token::pindah(from, to, amount)
    TokenTransfer {
        from: Box<Expr>,
        to: Box<Expr>,
        amount: Box<Expr>,
    },
    /// Zakat calculation: zakat(expr)
    ZakatCalculate(Box<Expr>),

    // ── CAHAYA Phase J5 expressions ────────────────────────────────
    /// UI display block: paparan { ... }
    UIDisplay(Vec<Expr>),
    /// Row layout: baris { child1; child2; ... }
    UIRow(Vec<Expr>),
    /// Column layout: lajur { child1; child2; ... }
    UIColumn(Vec<Expr>),
    /// Text element: tulisan("Hello", warna(255, 255, 255))
    UIText(Box<Expr>, Box<Expr>),
    /// Button: butang("Click", handler)
    UIButton(Box<Expr>, Box<Expr>),
    /// Color literal: warna(r, g, b)
    UIColor(u8, u8, u8),
    /// Style: gaya { pelapik: 16, saiz_fon: 14 }
    UIStyleDecl {
        padding: Option<u32>,
        font_size: Option<u32>,
    },
    /// Contrast check: kontras(fg_color, bg_color) — returns Bool
    UIContrastCheck(Box<Expr>, Box<Expr>),
}
