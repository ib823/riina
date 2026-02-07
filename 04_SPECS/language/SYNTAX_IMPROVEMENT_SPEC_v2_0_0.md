# RIINA Syntax Improvement Specification v2.0.0

**Verification:** 7,929 Coq Qed (compiled, 0 Admitted, 1 policy axiom) | 10 independent provers | 852 Rust tests

**Document ID:** `SYNTAX_IMPROVEMENT_SPEC_v2_0_0`
**Date:** 2026-01-30
**Status:** AUTHORITATIVE
**Supersedes:** `SYNTAX_IMPROVEMENT_SPEC_v1_0_0` (rejected — see Appendix A)

---

## 0. DESIGN PRINCIPLES

1. **Never break Coq proofs.** Zero new `Admitted`. Zero new `Axiom`. Zero new `expr` constructors until Phase 1 axiom elimination is complete.
2. **Desugar in the parser, not the core AST.** New syntactic forms compile to existing `expr` constructors.
3. **Sync Rust to Coq first.** The Coq formalization is the source of truth. Rust must match it, not the other way around.
4. **Bahasa Melayu is not an afterthought.** Every keyword gets a BM equivalent from day one.
5. **No speculative features.** Every change must be justified by a current gap or existing specification requirement.

---

## 1. CURRENT STATE AUDIT

### 1.1 Coq ↔ Rust Divergence (Actual Gaps)

| Definition | Coq | Rust | Gap |
|------------|-----|------|-----|
| `security_level` | 6 variants | 2 variants | **Rust missing 4** |
| `effect` | 17 variants | 6 variants | **Rust missing 11** |
| `ty` | 22 variants | 12 variants | **Rust missing 10** |
| `expr` | 27 variants | 25 variants | **Rust missing 2** (`ELoc`, `EString` — `EString` exists as `String(String)`, `ELoc` is internal) |
| Keywords (BM) | N/A | 13 English-only | **Lexer missing 13 BM equivalents** |

### 1.2 Lexer BM Gaps (English-only keywords in current lexer)

These keywords currently have no Bahasa Melayu equivalent in the lexer:

| English | Proposed BM | TokenKind |
|---------|-------------|-----------|
| `union` | `gabung` | `KwUnion` |
| `where` | `di_mana` | `KwWhere` |
| `tainted` | `tercemar` | `KwTainted` |
| `sanitize` | `bersihkan` | `KwSanitize` |
| `capability` | `keupayaan` | `KwCapability` |
| `revoke` | `tarikbalik` | `KwRevoke` |
| `seqcst` | `turutan_ketat` | `KwSeqCst` |
| `relaxed` | `longgar` | `KwRelaxed` |
| `acqrel` | `peroleh_lepas` | `KwAcqRel` |
| `async` | `tak_segerak` | `KwAsync` |
| `await` | `tunggu` | `KwAwait` |
| `super` | `induk` | `KwSuper` |
| `product` | `produk` | `KwProduct` |

### 1.3 Missing Keywords (not in lexer at all)

These appear in the BM syntax spec (`01_RESEARCH/specs/bahasa/RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md`) but are absent from the lexer:

| BM | English | Purpose | Proposed TokenKind |
|----|---------|---------|-------------------|
| `dan` | `and` | Logical AND keyword | `KwAnd` |
| `atau` | `or` | Logical OR keyword | `KwOr` |
| `bukan` | `not` | Logical NOT keyword | `KwNot` |
| `dalam` | `in` | For-in loops | `KwIn` |
| `ialah` | `is` | Type checking | `KwIs` |
| `bersih` | `pure` | Pure effect keyword | `KwPure` |
| `selamat` | `safe` | Safe annotation | `KwSafe` |
| `pinjam` | `borrow` | Borrow reference | `KwBorrow` |
| `salin` | `copy` | Copy value | `KwCopy` |
| `klon` | `clone` | Clone value | `KwClone` |
| `jangka` | `lifetime` | Lifetime annotation | `KwLifetime` |
| `pastikan` | `guard` | Guard clause | `KwGuard` |
| `dasar` | `policy` | Declassification policy | `KwPolicy` |
| `sempadan` | `boundary` | Alias for `pagar` (fence) | `KwFence` (existing) |

### 1.4 Missing Operator

| Token | Symbol | Purpose |
|-------|--------|---------|
| `Pipe` | `\|>` | Pipe operator (desugar to `EApp`) |

---

## 2. TIER 0: ZERO-COQ-IMPACT CHANGES

These changes touch ONLY Rust code. Zero Coq files affected. Zero proof risk.

### 2.1 Rust SecurityLevel Sync (2 → 6)

**File:** `03_PROTO/crates/riina-types/src/lib.rs`

**Current:**
```rust
pub enum SecurityLevel {
    Public,
    Secret,
}
```

**Target (match Coq's `security_level`):**
```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SecurityLevel {
    Public,    // LPublic — Publicly observable
    Internal,  // LInternal — Internal use only
    Session,   // LSession — Session-scoped
    User,      // LUser — User-level sensitive
    System,    // LSystem — System-level sensitive
    Secret,    // LSecret — Maximum secrecy
}
```

**Downstream Rust impact:**
- `riina-parser/src/lib.rs`: `parse_security_level()` — add parsing for new levels
- `riina-typechecker/src/lib.rs`: Update all `SecurityLevel` matches
- `riina-codegen/src/lower.rs`: Update any security level references
- `riina-lexer/src/lexer.rs`: No change needed (levels are parsed from identifiers, not keywords)

**Coq reference:** `foundations/Syntax.v` lines 31-37

### 2.2 Rust Effect Sync (6 → 17)

**File:** `03_PROTO/crates/riina-types/src/lib.rs`

**Current:**
```rust
pub enum Effect {
    Pure, Read, Write, Network, Crypto, System,
}
```

**Target (match Coq's `effect`):**
```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    // Base effects
    Pure,           // EffPure — No observable effect
    Read,           // EffRead — Memory/state read
    Write,          // EffWrite — Memory/state write
    FileSystem,     // EffFileSystem — File system access
    // Network effects
    Network,        // EffNetwork — Network I/O
    NetworkSecure,  // EffNetSecure — Secure network (TLS)
    // Crypto effects
    Crypto,         // EffCrypto — Cryptographic operations
    Random,         // EffRandom — Random number generation
    // System effects
    System,         // EffSystem — System calls
    Time,           // EffTime — Time/clock access
    Process,        // EffProcess — Process management
    // RIINA product effects
    Panel,          // EffPanel — Panel UI operations
    Zirah,          // EffZirah — Zirah API operations
    Benteng,        // EffBenteng — Benteng auth operations
    Sandi,          // EffSandi — Sandi crypto operations
    Menara,         // EffMenara — Menara device operations
    Gapura,         // EffGapura — Gapura gateway operations
}
```

**Update `Effect::level()` to match Coq's `effect_level`:**
```rust
impl Effect {
    pub fn level(&self) -> u8 {
        match self {
            Effect::Pure => 0,
            Effect::Read => 1,
            Effect::Write => 2,
            Effect::FileSystem => 3,
            Effect::Network => 4,
            Effect::NetworkSecure => 5,
            Effect::Crypto => 6,
            Effect::Random => 7,
            Effect::System => 8,
            Effect::Time => 9,
            Effect::Process => 10,
            Effect::Panel => 11,
            Effect::Zirah => 12,
            Effect::Benteng => 13,
            Effect::Sandi => 14,
            Effect::Menara => 15,
            Effect::Gapura => 16,
        }
    }

    pub fn category(&self) -> EffectCategory {
        match self {
            Effect::Pure => EffectCategory::Pure,
            Effect::Read | Effect::Write | Effect::FileSystem => EffectCategory::IO,
            Effect::Network | Effect::NetworkSecure => EffectCategory::Network,
            Effect::Crypto | Effect::Random => EffectCategory::Crypto,
            Effect::System | Effect::Time | Effect::Process => EffectCategory::System,
            Effect::Panel | Effect::Zirah | Effect::Benteng |
            Effect::Sandi | Effect::Menara | Effect::Gapura => EffectCategory::Product,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectCategory {
    Pure,
    IO,
    Network,
    Crypto,
    System,
    Product,
}
```

**Downstream Rust impact:**
- `riina-parser/src/lib.rs`: `parse_effect()` — add all new effect names (English + BM)
- `riina-typechecker/src/lib.rs`: Update all `Effect` matches
- `riina-codegen/src/lower.rs`: Update effect references

**Coq reference:** `foundations/Syntax.v` lines 84-141

### 2.3 Rust Ty Sync (12 → 22)

**File:** `03_PROTO/crates/riina-types/src/lib.rs`

**Current Rust Ty has 12 variants. Coq has 22. Add these 10:**

```rust
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    // === EXISTING (keep as-is) ===
    Unit,                                          // TUnit
    Bool,                                          // TBool
    Int,                                           // TInt
    String,                                        // TString
    Bytes,                                         // TBytes
    Fn(Box<Ty>, Box<Ty>, Effect),                  // TFn
    Prod(Box<Ty>, Box<Ty>),                        // TProd
    Sum(Box<Ty>, Box<Ty>),                         // TSum
    Ref(Box<Ty>, SecurityLevel),                   // TRef
    Secret(Box<Ty>),                               // TSecret
    Proof(Box<Ty>),                                // TProof
    Capability(Effect),                            // TCapability (simplified)

    // === NEW (sync with Coq) ===
    List(Box<Ty>),                                 // TList
    Option(Box<Ty>),                               // TOption
    Labeled(Box<Ty>, SecurityLevel),               // TLabeled
    Tainted(Box<Ty>, TaintSource),                 // TTainted
    Sanitized(Box<Ty>, Sanitizer),                 // TSanitized
    CapabilityFull(CapabilitySpec),                 // TCapabilityFull
    Chan(SessionType),                             // TChan
    SecureChan(SessionType, SecurityLevel),         // TSecureChan
    ConstantTime(Box<Ty>),                         // TConstantTime
    Zeroizing(Box<Ty>),                            // TZeroizing
}
```

**New supporting types needed in Rust:**

```rust
/// Taint source tracking (match Coq taint_source)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// Sanitizer (match Coq sanitizer — core variants)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sanitizer {
    HtmlEscape,
    SqlParameterize,
    ShellEscape,
    PathCanonicalize,
    UrlEncode,
    JsonEscape,
    XmlEscape,
    LdapEscape,
    RegexEscape,
    CssEscape,
    JsEscape,
    HeaderSanitize,
    NullByteRemove,
    UnicodeNormalize,
    WhitespaceTrim,
    LengthBound(usize),
    RangeBound(i64, i64),
    RegexMatch(String),
    Whitelist(Vec<String>),
}

/// Capability specification (match Coq capability)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CapabilityKind {
    FileRead, FileWrite, FileExecute, FileDelete,
    NetConnect, NetListen, NetBind,
    ProcSpawn, ProcSignal,
    SysTime, SysRandom, SysEnv,
    RootProduct, ProductAccess,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CapabilitySpec {
    Basic(CapabilityKind),
    Revocable(Box<CapabilitySpec>),
    TimeBound(Box<CapabilitySpec>, u64),
    Delegated(Box<CapabilitySpec>, String),
}

/// Session type (match Coq session_type)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SessionType {
    End,
    Send(Box<Ty>, Box<SessionType>),
    Recv(Box<Ty>, Box<SessionType>),
    Select(Box<SessionType>, Box<SessionType>),
    Branch(Box<SessionType>, Box<SessionType>),
    Rec(String, Box<SessionType>),
    Var(String),
}
```

**Downstream Rust impact:**
- `riina-parser/src/lib.rs`: `parse_ty()` — add parsing for new type constructors
- `riina-typechecker/src/lib.rs`: Add type-checking for new types
- `riina-codegen/`: Extend lowering for new types

**Coq reference:** `foundations/Syntax.v` lines 168-316

### 2.4 Lexer: Add Missing BM Equivalents

**File:** `03_PROTO/crates/riina-lexer/src/lexer.rs`

In the `read_identifier` match, change these entries:

```rust
// BEFORE (English-only):
"union" => TokenKind::KwUnion,
"where" => TokenKind::KwWhere,
"tainted" => TokenKind::KwTainted,
"sanitize" => TokenKind::KwSanitize,
"capability" => TokenKind::KwCapability,
"revoke" => TokenKind::KwRevoke,
"seqcst" => TokenKind::KwSeqCst,
"relaxed" => TokenKind::KwRelaxed,
"acqrel" => TokenKind::KwAcqRel,
"async" => TokenKind::KwAsync,
"await" => TokenKind::KwAwait,
"super" => TokenKind::KwSuper,
"product" => TokenKind::KwProduct,

// AFTER (bilingual):
"union" | "gabung" => TokenKind::KwUnion,
"where" | "di_mana" => TokenKind::KwWhere,
"tainted" | "tercemar" => TokenKind::KwTainted,
"sanitize" | "bersihkan" => TokenKind::KwSanitize,
"capability" | "keupayaan" => TokenKind::KwCapability,
"revoke" | "tarikbalik" => TokenKind::KwRevoke,
"seqcst" | "turutan_ketat" => TokenKind::KwSeqCst,
"relaxed" | "longgar" => TokenKind::KwRelaxed,
"acqrel" | "peroleh_lepas" => TokenKind::KwAcqRel,
"async" | "tak_segerak" => TokenKind::KwAsync,
"await" | "tunggu" => TokenKind::KwAwait,
"super" | "induk" => TokenKind::KwSuper,
"product" | "produk" => TokenKind::KwProduct,
```

### 2.5 Lexer: Add New Keywords

**File:** `03_PROTO/crates/riina-lexer/src/token.rs` — Add to `TokenKind`:

```rust
// New keywords
KwAnd,        // dan / and
KwOr,         // atau / or
KwNot,        // bukan / not
KwIn,         // dalam / in
KwIs,         // ialah / is
KwPure,       // bersih / pure
KwSafe,       // selamat / safe
KwBorrow,     // pinjam / borrow
KwCopy,       // salin / copy
KwClone,      // klon / clone
KwLifetime,   // jangka / lifetime
KwGuard,      // pastikan / guard
KwPolicy,     // dasar / policy
```

**File:** `03_PROTO/crates/riina-lexer/src/lexer.rs` — Add to `read_identifier`:

```rust
// Logic keywords (English | Bahasa Melayu)
"and" | "dan" => TokenKind::KwAnd,
"or" | "atau" => TokenKind::KwOr,
"not" | "bukan" => TokenKind::KwNot,

// Additional keywords
"in" | "dalam" => TokenKind::KwIn,
"is" | "ialah" => TokenKind::KwIs,
"pure" | "bersih" => TokenKind::KwPure,
"safe" | "selamat" => TokenKind::KwSafe,

// Ownership keywords
"borrow" | "pinjam" => TokenKind::KwBorrow,
"copy" | "salin" => TokenKind::KwCopy,
"clone" | "klon" => TokenKind::KwClone,
"lifetime" | "jangka" => TokenKind::KwLifetime,

// Guard clause
"guard" | "pastikan" => TokenKind::KwGuard,

// Declassification policy
"policy" | "dasar" => TokenKind::KwPolicy,

// Fence alias (sempadan as alternative to pagar)
"fence" | "pagar" | "sempadan" => TokenKind::KwFence,
```

### 2.6 Lexer: Pipe Operator

**File:** `03_PROTO/crates/riina-lexer/src/token.rs` — Add:

```rust
Pipe,  // |>
```

**File:** `03_PROTO/crates/riina-lexer/src/lexer.rs` — In the `'|'` match arm, currently:

```rust
'|' => {
    if self.peek() == Some(&'|') {
        self.advance();
        TokenKind::OrOr
    } else if self.peek() == Some(&'=') {
        self.advance();
        TokenKind::OrEq
    } else {
        TokenKind::Or
    }
}
```

**Change to:**
```rust
'|' => {
    if self.peek() == Some(&'|') {
        self.advance();
        TokenKind::OrOr
    } else if self.peek() == Some(&'>') {
        self.advance();
        TokenKind::Pipe
    } else if self.peek() == Some(&'=') {
        self.advance();
        TokenKind::OrEq
    } else {
        TokenKind::Or
    }
}
```

### 2.7 Parser: Pipe Operator Desugaring

**File:** `03_PROTO/crates/riina-parser/src/lib.rs`

Add pipe parsing in `parse_assignment()` or a new `parse_pipe()` precedence level. Pipe is left-associative and desugars `a |> f` to `App(f, a)`:

```rust
/// Parse pipe expressions: expr (|> expr)*
/// a |> f |> g  desugars to  App(g, App(f, a))
fn parse_pipe(&mut self) -> Result<Expr, ParseError> {
    let mut expr = self.parse_assignment()?;
    while self.peek_kind() == Some(&TokenKind::Pipe) {
        self.next(); // consume |>
        let func = self.parse_assignment()?;
        expr = Expr::App(Box::new(func), Box::new(expr));
    }
    Ok(expr)
}
```

Update `parse_expr` to call `parse_pipe` instead of `parse_assignment` at the top level.

**Coq impact: NONE.** Pipe desugars to `EApp` which already exists.

### 2.8 Parser: Guard Clause Desugaring

**File:** `03_PROTO/crates/riina-parser/src/lib.rs`

Guard clause `pastikan cond lain { early_return }; continuation` desugars to `EIf`:

```rust
/// Parse guard clause:
///   pastikan <cond> lain { <else_body> };
///   <continuation>
///
/// Desugars to: if cond then continuation else else_body
fn parse_guard(&mut self) -> Result<Expr, ParseError> {
    self.consume(TokenKind::KwGuard)?;
    let cond = self.parse_expr()?;
    self.consume(TokenKind::KwElse)?;
    self.consume(TokenKind::LBrace)?;
    let else_body = self.parse_expr()?;
    self.consume(TokenKind::RBrace)?;
    self.consume(TokenKind::Semi)?;
    let continuation = self.parse_expr()?;
    Ok(Expr::If(Box::new(cond), Box::new(continuation), Box::new(else_body)))
}
```

**Coq impact: NONE.** Guard desugars to `EIf` which already exists.

### 2.9 Parser: Multi-Arm Match Desugaring

**File:** `03_PROTO/crates/riina-parser/src/lib.rs`

Multi-arm `padan` with arbitrary patterns compiles to nested `ECase`/`EIf`:

```rust
/// Parse multi-arm match:
///   padan expr {
///       pattern1 => body1,
///       pattern2 => body2,
///       _ => default_body,
///   }
///
/// Desugars to nested ECase/EIf chains.
/// Currently: only supports literal, identifier, and inl/inr patterns.
/// Full pattern compilation deferred to Pattern.v integration.
fn parse_match(&mut self) -> Result<Expr, ParseError> {
    // ... existing match parsing ...
    // Extended to handle multiple arms, compiled to nested Case/If
}
```

**Coq impact: NONE.** Compiles to existing `ECase` and `EIf`.

### 2.10 Compiler Driver: --bahasa Flag

**File:** `03_PROTO/crates/riinac/src/main.rs`

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LanguageMode {
    Both,     // Accept both English and BM (default)
    Melayu,   // BM only — English keywords produce error
    English,  // English only — BM keywords produce error
}

struct Cli {
    input: PathBuf,
    bahasa: LanguageMode,
}

fn parse_args() -> Cli {
    let args: Vec<String> = std::env::args().collect();
    let mut input = None;
    let mut bahasa = LanguageMode::Both;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--bahasa=ms" => bahasa = LanguageMode::Melayu,
            "--bahasa=en" => bahasa = LanguageMode::English,
            "--bahasa=both" => bahasa = LanguageMode::Both,
            arg if !arg.starts_with('-') => input = Some(PathBuf::from(arg)),
            _ => {
                eprintln!("Unknown flag: {}", args[i]);
                std::process::exit(1);
            }
        }
        i += 1;
    }

    Cli {
        input: input.unwrap_or_else(|| {
            eprintln!("Usage: riinac [--bahasa=ms|en|both] <input.rii>");
            std::process::exit(1);
        }),
        bahasa,
    }
}
```

**File:** `03_PROTO/crates/riina-lexer/src/error.rs` — Add:

```rust
/// Error when keyword language doesn't match --bahasa mode
KeywordLanguageMismatch {
    keyword: String,
    expected: String, // "ms" or "en"
    position: usize,
},
```

### 2.11 Error System: Bilingual Error Messages

**File:** `03_PROTO/crates/riina-lexer/src/error.rs`

Every error variant gets bilingual Display:

```rust
impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexError::UnexpectedChar(c, pos) => write!(f,
                "Ralat: Aksara tidak dijangka '{}' pada kedudukan {}\n\
                 Error: Unexpected character '{}' at position {}", c, pos, c, pos),
            LexError::UnterminatedString(pos) => write!(f,
                "Ralat: Teks tidak ditamatkan pada kedudukan {}\n\
                 Error: Unterminated string at position {}", pos, pos),
            LexError::KeywordLanguageMismatch { keyword, expected, position } => write!(f,
                "Ralat: Kata kunci '{}' tidak sepadan dengan mod bahasa '{}' pada kedudukan {}\n\
                 Error: Keyword '{}' does not match language mode '{}' at position {}",
                keyword, expected, position, keyword, expected, position),
            // ... other variants
        }
    }
}
```

---

## 3. TIER 1: PARSER-ONLY NEW FEATURES

These add new user-facing syntax but desugar entirely in the parser. Zero Coq changes.

### 3.1 For-In Loop (Parser Sugar)

`untuk x dalam expr { body }` desugars to an iterator protocol call chain.

Since RIINA does not yet have an iterator trait, the initial implementation desugars to a recursive helper or to existing `ELet`/`EApp` chains.

**Temporary desugaring (until iterator protocol exists):**
```
untuk x dalam senarai { body }
  ===
let __iter = senarai;
let __fn = fun x -> body;
map(__fn, __iter)
```

This uses `ELet` and `EApp` — both already exist in Coq.

**Coq impact: NONE.**

### 3.2 While Loop (Parser Sugar)

`selagi cond { body }` desugars to a recursive function call:

```
selagi cond { body }
  ===
let rec __loop () = if cond then (body; __loop ()) else ()
__loop ()
```

**WARNING:** Unrestricted `selagi` breaks strong normalization. Two options:

- **Option A (recommended):** Require `selagi` to carry an explicit fuel/bound: `selagi cond, had: 1000 { body }`. This desugars to a bounded recursion that provably terminates.
- **Option B:** Restrict `selagi` to functions with `kesan Sistem` effect, making it unavailable in pure code. Termination proofs only cover pure code.

**Decision required before implementation. Do not implement without choosing A or B.**

### 3.3 Loop (Parser Sugar)

`ulang { body }` is an infinite loop with `keluar` (break). Same termination concern as while.

**Same constraint as 3.2 applies.** Require fuel or effect annotation.

---

## 4. TIER 2: DEFERRED CHANGES (Phase 1+)

These require new Coq constructors or significant proof work. They MUST NOT be implemented until Phase 1 (axiom elimination: 9 axioms → 0) is complete.

### 4.1 Quantitative Declassification (Post-Phase 1)

**Rationale:** The formal model should prove *that declassification respects a policy*. The policy parameters (bit budget, rate limit) are runtime enforcement concerns.

**Design:**
1. Keep `EDeclassify` as-is in Coq core AST
2. Add a `declassification_policy` record type to Coq (for specification, not AST)
3. Prove: `declassify_respects_policy` theorem — if a program uses `dedah` with policy P, the information leakage is bounded by P's budget
4. Rust runtime: enforce budget tracking, rate limiting, audit logging
5. Rust parser: accept `dasar: "policy_name"` argument in `dedah()` calls

**Coq changes (Phase 2):**
```coq
(* In a new file: properties/DeclassificationPolicy.v *)
Record declassification_policy := {
    dp_name : ident;
    dp_leak_type : ty;
    dp_bit_budget : nat;
    dp_max_invocations : nat;
    dp_window_seconds : nat;
    dp_audit_required : bool;
}.

(* Theorem: declassification bounded by policy *)
Theorem declassify_bounded : forall e pol Gamma Sigma pc T,
    has_type Gamma Sigma pc (EDeclassify e (EProve (EBool true))) T EffPure ->
    policy_matches pol T ->
    information_leakage e <= dp_bit_budget pol.
```

**This is a ~200 line new file, NOT a modification of existing proofs.**

### 4.2 ConstantTime / SpeculationSafe Verification (Post-Phase 2)

**Rationale:** These are verification properties, not computational effects. Constant-time is a property of the *compilation target*, not the *source evaluation*.

**Design:**
1. Do NOT add `EffConstantTime` / `EffSpecSafe` to the `effect` inductive
2. Instead, define a separate analysis pass:

```coq
(* In a new file: properties/ConstantTimeAnalysis.v *)

(* A term is constant-time if its evaluation does not branch on secret data *)
Definition constant_time (Gamma : type_env) (e : expr) : Prop :=
    forall x T, lookup x Gamma = Some (TSecret T) ->
    ~ branches_on x e.

(* CT is preserved by well-typed substitution *)
Theorem ct_preservation : forall Gamma Sigma pc e T eff,
    has_type Gamma Sigma pc e T eff ->
    constant_time Gamma e ->
    forall e' st st' ctx ctx',
    (e, st, ctx) --> (e', st', ctx') ->
    constant_time Gamma e'.
```

3. Rust: The `masa_tetap { ... }` block already exists as syntax. The typechecker should verify the constant-time property. No new AST node needed.

### 4.3 Effect Rows (Post-Phase 3)

**Rationale:** Changing `TFn` from `ty -> ty -> effect -> ty` to `ty -> ty -> list effect -> ty` would break every downstream Coq file (25+ files, 40+ match sites). The current `effect_join` lattice approach is sound and sufficient.

**If effect rows are ever needed:**
1. Define `effect_row := list effect` as a type alias
2. Add `TFnRow : ty -> ty -> effect_row -> ty` as a NEW constructor alongside `TFn`
3. Prove `TFn T1 T2 e` equivalent to `TFnRow T1 T2 [e]`
4. Gradually migrate callers

**This is Phase 3+ work at minimum.**

### 4.4 New expr Constructors (Post-Phase 1)

When Phase 1 is complete (0 axioms), and ONLY then, consider adding:

| Constructor | Priority | Justification |
|-------------|----------|---------------|
| `EMatch : expr -> list (pattern * expr) -> expr` | P1 | Multi-arm match (after Pattern.v exists) |
| `EGuard : expr -> expr -> expr -> expr` | P2 | Guard clause (only if parser desugaring proves insufficient) |
| `EFor : ident -> expr -> expr -> expr` | P3 | For loops (requires iterator protocol + termination proof) |
| `EWhile : expr -> expr -> expr` | P3 | While loops (requires bounded recursion proof) |

**Each new constructor requires updating:**
- `subst` in Syntax.v
- `free_in` in Typing.v
- `step` in Semantics.v
- `has_type` in Typing.v
- `value` in Syntax.v (if applicable)
- Every `Fixpoint`/`induction`/`match` on `expr` in ALL 222 .v files

**Estimated impact per constructor: ~50-100 lines across ~25 files.**

---

## 5. EXAMPLE FILE UPDATES

### 5.1 New Example: `07_EXAMPLES/pengawal_input.rii`

Demonstrates guard clauses using `pastikan`:

```riina
// pengawal_input.rii — Guard clause examples
modul pengawal_input;

fungsi proses_input(input: Mungkin<Teks>) -> Hasil<Data, Ralat> {
    // Guard: early return if None
    pastikan biar Ada(nilai) = input lain {
        pulang Gagal(Ralat::InputKosong);
    };

    // Guard: early return if empty
    pastikan nilai.panjang() > 0 lain {
        pulang Gagal(Ralat::InputTidakSah);
    };

    // Happy path — no nesting
    parse(nilai)
}
```

### 5.2 New Example: `07_EXAMPLES/saluran_paip.rii`

Demonstrates pipe operator:

```riina
// saluran_paip.rii — Pipe operator examples
modul saluran_paip;

fungsi proses_data(data: Senarai<Nombor>) -> Nombor {
    data
        |> tapis(|x| x > 0)
        |> peta(|x| x * 2)
        |> lipat(0, |acc, x| acc + x)
}
```

### 5.3 New Example: `07_EXAMPLES/keselamatan_kuantitatif.rii`

Demonstrates quantitative declassification:

```riina
// keselamatan_kuantitatif.rii — Quantitative declassification
modul keselamatan_kuantitatif;

// Policy declaration
dasar pengesahan_kata {
    apa: Benar,
    bajet: 1,
    had: 5,
    audit: betul,
}

fungsi sahkan(kata: Rahsia<Teks>, hash: Hash) -> Benar kesan Kripto {
    masa_tetap {
        dedah(
            sama_masa_tetap(sha256(kata), hash),
            dasar: "pengesahan_kata",
        )
    }
}
```

---

## 6. FILES CHANGED (COMPLETE LIST)

### Tier 0 (implement now):

| File | Change | Lines |
|------|--------|-------|
| `03_PROTO/crates/riina-types/src/lib.rs` | SecurityLevel 2→6, Effect 6→17, Ty 12→22, add supporting types | ~300 |
| `03_PROTO/crates/riina-lexer/src/token.rs` | Add 13 new TokenKind variants + Pipe | ~20 |
| `03_PROTO/crates/riina-lexer/src/lexer.rs` | Add 13 BM equivalents, 14 new keywords, pipe operator | ~40 |
| `03_PROTO/crates/riina-lexer/src/error.rs` | Add KeywordLanguageMismatch, bilingual Display | ~30 |
| `03_PROTO/crates/riina-parser/src/lib.rs` | Add parse_pipe, parse_guard, extend parse_effect/parse_ty/parse_security_level | ~120 |
| `03_PROTO/crates/riina-typechecker/src/lib.rs` | Update all matches for expanded enums | ~80 |
| `03_PROTO/crates/riina-codegen/src/lower.rs` | Update matches | ~40 |
| `03_PROTO/crates/riina-codegen/src/interp.rs` | Update matches | ~30 |
| `03_PROTO/crates/riina-codegen/src/value.rs` | Update matches | ~20 |
| `03_PROTO/crates/riinac/src/main.rs` | Add --bahasa flag, parse_args | ~40 |
| `07_EXAMPLES/pengawal_input.rii` | New file | ~25 |
| `07_EXAMPLES/saluran_paip.rii` | New file | ~20 |
| `07_EXAMPLES/keselamatan_kuantitatif.rii` | New file | ~30 |

**Total Tier 0: ~795 lines across 13 files (10 modified + 3 new)**

### Tier 1 (implement after Tier 0 tests pass):

| File | Change | Lines |
|------|--------|-------|
| `03_PROTO/crates/riina-parser/src/lib.rs` | For/while/loop desugaring (after termination decision) | ~60 |
| `03_PROTO/crates/riina-parser/src/tests.rs` | Tests for new syntax | ~100 |

### Tier 2 (Phase 1+ only):

| File | Change | Lines |
|------|--------|-------|
| `02_FORMAL/coq/properties/DeclassificationPolicy.v` | New file: quantitative declassification | ~200 |
| `02_FORMAL/coq/properties/ConstantTimeAnalysis.v` | New file: CT verification | ~150 |
| Various .v files | New expr constructors (if needed) | ~50-100 per constructor |

---

## 7. EXECUTION ORDER

```
PHASE 0 (now):
  Step 1: riina-types/src/lib.rs — Add all new types (SecurityLevel, Effect, Ty, supporting)
  Step 2: riina-lexer/src/token.rs — Add new TokenKind variants
  Step 3: riina-lexer/src/lexer.rs — Add keyword mappings + pipe operator
  Step 4: riina-lexer/src/error.rs — Bilingual errors
  Step 5: riina-parser/src/lib.rs — Pipe desugaring, guard desugaring, expanded parse_ty/parse_effect
  Step 6: riina-typechecker/src/lib.rs — Update all match arms
  Step 7: riina-codegen/src/*.rs — Update all match arms
  Step 8: riinac/src/main.rs — --bahasa flag
  Step 9: cargo test --all — Verify everything passes
  Step 10: New .rii example files

PHASE 1 (after axiom elimination):
  Step 11: For/while/loop desugaring (after termination decision)

PHASE 2+ (after core proofs complete):
  Step 12: DeclassificationPolicy.v
  Step 13: ConstantTimeAnalysis.v
  Step 14: New expr constructors (if justified)
```

---

## 8. VERIFICATION CHECKLIST

Before merging any Tier 0 change:

```bash
cd riina/03_PROTO
cargo build --all            # Must pass
cargo test --all             # Must pass
cargo clippy -- -D warnings  # Must pass
cargo fmt --check            # Must pass

cd riina/02_FORMAL/coq
make                         # Must pass (unchanged)
grep -r "Admitted" *.v       # Must be ≤ 18 (unchanged)
```

---

## APPENDIX A: CHANGES REJECTED FROM v1.0.0

| v1 Proposal | Reason Rejected |
|-------------|-----------------|
| Add `EffConstantTime` / `EffSpecSafe` to `effect` | Category error: CT/SS are verification properties, not computational effects. Would break all 17 effect matches across 25+ Coq files. |
| Change `TFn` to take `effect_row` (list effect) | Would break every `TFn` match in all 222 .v files. `effect_join` lattice is already sound. |
| Add `EFor` / `EWhile` / `ELoop` to core `expr` | `ELoop` (infinite loop) directly contradicts `well_typed_SN` (strong normalization theorem). Loops must be bounded or effectful. |
| Add 6 new `expr` constructors + admit downstream | Explicitly violates project policy: "NO `admit.` — No tactical admits allowed." |
| Add `TFloat` / `TChar` to Coq `ty` | These already exist in the BM syntax spec as desired types, but adding them to Coq now would break all `ty` matches across 222 files for no proof benefit. Defer until Phase 2. |
| Security level 2→6 in Coq | Already done — Coq has 6 levels since initial implementation. |
| Effect 6→18 in Coq | Already done — Coq has 17 effects. The v1 spec was counting stale data. |
| Type 12→22 in Coq | Already done — Coq has 22 types. |

---

## APPENDIX B: WHAT THE ORIGINAL SPEC GOT RIGHT

| v1 Proposal | Status in v2 |
|-------------|-------------|
| 13 BM keyword equivalents | Kept (Section 2.4) |
| Pipe operator `\|>` | Kept as parser desugaring (Section 2.6-2.7) |
| Guard clause `pastikan` | Kept as parser desugaring to `EIf` (Section 2.8) |
| `--bahasa` compiler flag | Kept (Section 2.10) |
| Bilingual error messages | Kept (Section 2.11) |
| New .rii example files | Kept, reduced from 5 to 3 (Section 5) |
| SecurityLevel Rust sync | Kept (Section 2.1) |
| Effect Rust sync | Kept with correct target (Section 2.2) |
| Ty Rust sync | Kept with correct target (Section 2.3) |
| Quantitative declassification | Redesigned: separate Coq spec file, not core AST (Section 4.1) |
| Multi-arm match | Redesigned: parser desugaring to ECase, not new AST node (Section 2.9) |

---

*Document ID: SYNTAX_IMPROVEMENT_SPEC_v2_0_0*
*Status: AUTHORITATIVE*
*Approved: 2026-01-30*
*Mode: Comprehensive | Zero Trust | Zero Admits*
