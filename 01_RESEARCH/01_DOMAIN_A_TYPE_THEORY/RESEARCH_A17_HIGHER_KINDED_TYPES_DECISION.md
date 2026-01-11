# TERAS-LANG Research Track
# Session A-17: Higher-Kinded Types
# Document Type: Architecture Decision Record

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  ARCHITECTURE DECISION: HIGHER-KINDED TYPES FOR TERAS-LANG                   ║
║                                                                              ║
║  Decision: ADOPT Haskell-style HKT with monomorphization optimization        ║
║  Status: APPROVED                                                            ║
║  Impact: Core type system, Effects (A-05, A-11), Rows (A-16)                ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

## 1. Decision Statement

**TERAS-LANG shall adopt higher-kinded types with:**

1. **Haskell-style type classes** for abstraction over type constructors
2. **Full kind polymorphism** (PolyKinds equivalent)
3. **GADTs** for indexed security types and state machines
4. **Aggressive monomorphization** to eliminate dictionary overhead
5. **Integration with linear/effect systems** for security-aware HKT

This provides maximum expressiveness for security abstractions while achieving zero runtime overhead through compile-time specialization.

---

## 2. Context and Requirements

### 2.1 Security Abstraction Requirements

| Requirement | HKT Solution |
|-------------|--------------|
| Permission polymorphism | `∀f. PermFunctor f ⇒ f perms a → f perms b` |
| Effect abstraction | `∀m. EffectMonad m ⇒ m effects a` |
| State machine types | `Connection :: ConnState → Type` |
| Capability functor | `CapFunctor :: [Cap] → Type → Type` |
| Taint tracking | `TaintedT :: TaintLevel → Type → Type` |

### 2.2 Performance Requirements

| Requirement | Solution |
|-------------|----------|
| Zero dictionary overhead | Monomorphization |
| Inline type class methods | SPECIALIZE annotations |
| No boxing | Unboxed representation |
| Compile-time dispatch | Instance resolution at compile |

---

## 3. Detailed Design

### 3.1 Kind System

```
Base Kinds:
  Type                     -- Kind of runtime types
  Effect                   -- Kind of effects (A-05)
  Cap                      -- Kind of capabilities (A-14)
  Region                   -- Kind of regions (A-12)
  Row k                    -- Kind of rows (A-16)
  Constraint               -- Kind of type class constraints

Kind Constructors:
  Type → Type              -- Unary type constructor
  Type → Type → Type       -- Binary type constructor
  [k] → Type               -- Indexed by list
  k → Constraint           -- Type class
  
Kind Polymorphism:
  ∀κ. κ → Type            -- Polymorphic over kinds
```

### 3.2 Type Class Syntax

```
-- Type class declaration
trait Functor[F : Type → Type] {
  fn map[A, B](fa: F[A], f: A → B) → F[B]
}

-- Laws (checked by refinement system A-08)
laws Functor[F] {
  -- Identity
  ∀fa. map(fa, id) == fa
  -- Composition
  ∀fa f g. map(map(fa, f), g) == map(fa, g ∘ f)
}

-- Instance declaration
impl Functor[Option] {
  fn map[A, B](fa: Option[A], f: A → B) → Option[B] =
    match fa {
      None → None,
      Some(x) → Some(f(x))
    }
}
```

### 3.3 Higher-Kinded Constraints

```
-- Functor constraint
fn double_map[F : Type → Type, A, B, C]
    (fa: F[A], f: A → B, g: B → C) → F[C]
  where Functor[F]
= map(map(fa, f), g)

-- Multiple constraints
fn sequence[F : Type → Type, G : Type → Type, A]
    (fga: F[G[A]]) → G[F[A]]
  where Traversable[F], Applicative[G]
= traverse(fga, id)

-- Higher-kinded constraint
fn lift_effect[M : Effect → Type → Type, E : Effect, A]
    (ma: M[E][A]) → M[E ∪ IO][A]
  where EffectMonad[M]
```

### 3.4 GADTs for Security

```
-- State-indexed type
type Connection[S : ConnState] where {
  Disconnected : Connection[Disconnected],
  Connected    : Handle → Connection[Connected],
  Authenticated: Handle → User → Connection[Authenticated],
  Encrypted    : Handle → User → Key → Connection[Encrypted]
}

-- Permission-indexed operations
type Operation[P : [Permission], A] where {
  Read  : Path → Operation[[Read], Bytes],
  Write : Path → Bytes → Operation[[Write], ()],
  Admin : Command → Operation[[Admin], Result]
}

-- Type-safe state transitions
fn connect() → IO[Connection[Connected]]
fn auth(c: Connection[Connected], creds: Creds) 
     → IO[Connection[Authenticated]]
fn encrypt(c: Connection[Authenticated]) 
     → IO[Connection[Encrypted]]
```

### 3.5 Kind Polymorphism

```
-- Polymorphic Proxy
type Proxy[K : Kind, A : K] = ()

-- Kind-polymorphic type family
type family Apply[K : Kind, F : K → Type, A : K] : Type where {
  Apply[Type, F, A] = F[A],
  Apply[Effect, F, E] = F[E],
  Apply[Cap, F, C] = F[C]
}

-- Kind-polymorphic class
trait Indexed[K : Kind, F : K → Type → Type] {
  fn imap[I : K, A, B](fia: F[I][A], f: A → B) → F[I][B]
}
```

### 3.6 Associated Types

```
-- Type family in trait
trait Container[C : Type] {
  type Elem : Type
  fn empty() → C
  fn insert(c: C, e: Elem) → C
  fn member(c: C, e: Elem) → Bool
}

impl Container[HashSet[T]] {
  type Elem = T
  fn empty() = HashSet::new()
  fn insert(c, e) = c.insert(e)
  fn member(c, e) = c.contains(e)
}

-- Functional dependency via associated type
trait Monad[M : Type → Type] {
  type Effect : [Effect]  -- Associated effect list
  fn pure[A](a: A) → M[A]
  fn bind[A, B](ma: M[A], f: A → M[B]) → M[B]
}
```

---

## 4. Type Rules

### 4.1 Kind Formation

```
──────────────
Type : Kind

──────────────
Effect : Kind

κ₁ : Kind    κ₂ : Kind
───────────────────────
κ₁ → κ₂ : Kind

κ : Kind
────────────
[κ] : Kind
```

### 4.2 Type Constructor Application

```
Γ ⊢ F : κ₁ → κ₂    Γ ⊢ A : κ₁
────────────────────────────────
Γ ⊢ F[A] : κ₂
```

### 4.3 Type Class Constraint

```
Γ ⊢ C : κ → Constraint    Γ ⊢ T : κ
─────────────────────────────────────
Γ ⊢ C[T] : Constraint
```

### 4.4 Instance Resolution

```
instance C[T] in scope    Γ ⊢ e : τ    FV(C[T]) ⊆ Γ
────────────────────────────────────────────────────
Γ; C[T] ⊢ e : τ
```

### 4.5 GADT Pattern Match

```
Γ ⊢ e : T[I]    ∀i. Γ, (I = Iᵢ) ⊢ pᵢ → eᵢ : τ
─────────────────────────────────────────────
Γ ⊢ match e { pᵢ → eᵢ } : τ
```

---

## 5. Monomorphization Strategy

### 5.1 Specialization Algorithm

```
Monomorphization Process:

1. Collect all call sites with concrete type arguments
   map[Int, String](xs, f)  →  map_Int_String(xs, f)

2. Generate specialized instances
   fn map_Int_String(xs: List[Int], f: Int → String) → List[String]

3. Inline dictionary methods
   -- Before: functor_dict.map(xs, f)
   -- After:  list_map(xs, f)

4. Remove unused polymorphic versions
   -- Keep only specialized versions in final binary
```

### 5.2 Specialization Annotations

```
-- Force specialization
#[specialize(Int, String)]
fn map[A, B](xs: List[A], f: A → B) → List[B]

-- Inline always
#[inline(always)]
fn pure[A](a: A) → Option[A] = Some(a)

-- Prevent specialization (for code size)
#[no_specialize]
fn generic_handler[F](f: F) → () where F : Handler
```

### 5.3 Dictionary Elimination

```
Transformation Pipeline:

Source:
  fn process[M](m: M[Request]) → M[Response]
    where Monad[M], Logger[M]
  = do {
      req ← m
      log("Processing")
      pure(handle(req))
    }

After Dictionary Passing:
  fn process[M](
    monad_dict: MonadDict[M],
    logger_dict: LoggerDict[M],
    m: M[Request]
  ) → M[Response]

After Monomorphization (for IO):
  fn process_IO(m: IO[Request]) → IO[Response]
  = do {
      req ← m
      io_log("Processing")
      io_pure(handle(req))
    }
```

---

## 6. Security Integration

### 6.1 Security-Indexed Functor

```
-- Functor that preserves security label
trait SecureFunctor[L : SecurityLevel, F : Type → Type] {
  fn smap[A, B](fa: F[A], f: A → B) → F[B]
    where ∀a. Label(a) ≤ L
}

-- Cannot map over higher-classified data
impl SecureFunctor[Secret, Labeled[Secret]] {
  fn smap[A, B](fa: Labeled[Secret][A], f: A → B) → Labeled[Secret][B]
    -- f cannot leak to lower classification
}
```

### 6.2 Capability Monad

```
trait CapMonad[C : [Cap], M : Type → Type] {
  fn cap_pure[A](a: A) → M[A]
  fn cap_bind[A, B](ma: M[A], f: A → M[B]) → M[B]
  fn require_cap[C' : Cap](proof: Has[C', C]) → M[Cap[C']]
}

-- Usage with capability requirements
fn read_file[C](path: Path) → CapM[C][Bytes]
  where Has[FileRead, C]
= do {
    cap ← require_cap[FileRead]
    read_with_cap(cap, path)
  }
```

### 6.3 Effect-Indexed Monad

```
-- Monad indexed by effect row (A-11 integration)
trait EffMonad[M : Row Effect → Type → Type] {
  fn eff_pure[A](a: A) → M[()][A]
  fn eff_bind[E1, E2, A, B]
      (ma: M[E1][A], f: A → M[E2][B]) → M[E1 ∪ E2][B]
  fn eff_lift[E, A](op: Op[E][A]) → M[(E)][A]
}

-- Track IO, Crypto, Network effects
fn secure_request[E](url: URL) → Eff[E ∪ (Network, Crypto)][Response]
  where Has[Network, E], Has[Crypto, E]
```

### 6.4 State Machine via GADT

```
-- TLS connection state machine
type TLSState = ClientHello | ServerHello | KeyExchange 
              | Finished | Established | Closed

type TLS[S : TLSState] where {
  Initial     : TLS[ClientHello],
  AfterHello  : ServerParams → TLS[ServerHello],
  AfterKex    : SessionKey → TLS[KeyExchange],
  Ready       : SecureChannel → TLS[Established],
  Terminated  : TLS[Closed]
}

-- Only send data on established connection
fn send(tls: TLS[Established], data: Bytes) → IO[()]

-- State transitions enforce protocol
fn handshake() → IO[TLS[Established]] = do {
  tls ← client_hello()        -- TLS[ClientHello]
  tls ← server_hello(tls)     -- TLS[ServerHello]  
  tls ← key_exchange(tls)     -- TLS[KeyExchange]
  tls ← finish(tls)           -- TLS[Established]
  pure(tls)
}
```

---

## 7. TERAS Product Applications

### 7.1 MENARA

```
-- Permission-indexed mobile context
type MobileCtx[P : [Permission]] where {
  NoPerms   : MobileCtx[[]],
  WithCam   : MobileCtx[P] → MobileCtx[[Camera] ++ P],
  WithLoc   : MobileCtx[P] → MobileCtx[[Location] ++ P],
  WithStore : MobileCtx[P] → MobileCtx[[Storage] ++ P]
}

-- Type-safe permission usage
fn take_photo[P](ctx: MobileCtx[P]) → IO[Photo]
  where Has[Camera, P]
```

### 7.2 GAPURA

```
-- Request processing functor
trait RequestFunctor[F : Type → Type] {
  fn map_request[A, B](fa: F[A], f: A → B) → F[B]
}

-- Middleware as natural transformation
type Middleware[F, G] = ∀A. F[A] → G[A]

fn auth_middleware() → Middleware[UnauthReq, AuthReq]
fn rate_limit_middleware() → Middleware[RawReq, LimitedReq]

-- Compose middlewares
fn compose[F, G, H](
  m1: Middleware[F, G],
  m2: Middleware[G, H]
) → Middleware[F, H]
```

### 7.3 ZIRAH

```
-- Scan severity indexed
type ScanResult[S : Severity, A] where {
  Clean    : A → ScanResult[None, A],
  Low      : A → Finding → ScanResult[Low, A],
  High     : A → Finding → ScanResult[High, A],
  Critical : A → Finding → ScanResult[Critical, A]
}

-- Severity-preserving map
impl Functor[ScanResult[S]] {
  fn map[A, B](r: ScanResult[S, A], f: A → B) → ScanResult[S, B] =
    match r {
      Clean(a) → Clean(f(a)),
      Low(a, finding) → Low(f(a), finding),
      High(a, finding) → High(f(a), finding),
      Critical(a, finding) → Critical(f(a), finding)
    }
}
```

### 7.4 BENTENG

```
-- Verification workflow as indexed monad
type VerifyM[S1 : VerifyState, S2 : VerifyState, A]

trait VerifyMonad {
  fn verify_pure[S, A](a: A) → VerifyM[S, S, A]
  fn verify_bind[S1, S2, S3, A, B](
    ma: VerifyM[S1, S2, A],
    f: A → VerifyM[S2, S3, B]
  ) → VerifyM[S1, S3, B]
}

-- Type-safe verification steps
fn scan_doc() → VerifyM[Initial, DocScanned, Document]
fn match_face(doc: Document) → VerifyM[DocScanned, FaceMatched, FaceData]
fn check_liveness(face: FaceData) → VerifyM[FaceMatched, LivenessOK, LivenessProof]
fn complete() → VerifyM[LivenessOK, Verified, VerifiedIdentity]
```

### 7.5 SANDI

```
-- Key lifecycle GADT
type Key[S : KeyState, A : Algorithm] where {
  Generated : KeyMaterial[A] → Key[Fresh, A],
  Stored    : KeyId → Key[Stored, A],
  Active    : lin KeyMaterial[A] → Key[InUse, A],
  Revoked   : KeyId → Key[Revoked, A]
}

-- Linear key usage
fn sign[A](key: lin Key[InUse, A], data: Bytes) → Signature[A]

-- Key state transitions
fn store_key[A](k: Key[Fresh, A]) → IO[Key[Stored, A]]
fn load_key[A](k: Key[Stored, A]) → IO[lin Key[InUse, A]]
fn revoke_key[A, S](k: Key[S, A]) → IO[Key[Revoked, A]]
```

---

## 8. Integration with Prior Sessions

### 8.1 A-04 Linear Types

```
-- Linear functor
trait LinearFunctor[F : Type → Type] {
  fn lmap[A, B](fa: lin F[A], f: A ⊸ B) → lin F[B]
}

-- Linear monad
trait LinearMonad[M : Type → Type] : LinearFunctor[M] {
  fn lpure[A](a: lin A) → lin M[A]
  fn lbind[A, B](ma: lin M[A], f: A ⊸ lin M[B]) → lin M[B]
}
```

### 8.2 A-05/A-11 Effects

```
-- Effect row HKT
type Eff[E : Row Effect, A]

impl EffMonad[Eff] {
  -- Effect polymorphism via row types
}

-- Effect handlers as HKT transformations
fn handle_state[E, S, A](
  init: S,
  eff: Eff[(State S) ∪ E, A]
) → Eff[E, (A, S)]
```

### 8.3 A-08 Refinement Types

```
-- Refined functor preserves refinements
trait RefinedFunctor[F : Type → Type] {
  fn rmap[A, B, P, Q](
    fa: F[{a : A | P(a)}],
    f: (a : A) → {b : B | Q(a, b)}
  ) → F[{b : B | ∃a. Q(a, b)}]
}
```

### 8.4 A-16 Row Types

```
-- Row-polymorphic HKT
trait RowFunctor[F : Row Type → Type → Type] {
  fn row_map[R, A, B](fra: F[R, A], f: A → B) → F[R, B]
}

-- Record functor
impl RowFunctor[Record] {
  fn row_map[R, A, B](r: Record[R, A], f: A → B) → Record[R, B] =
    -- Map over record fields
}
```

---

## 9. Implementation Roadmap

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Kind System | 3 weeks | Kind checker, basic kinds |
| 2. Type Classes | 4 weeks | Trait system, instances |
| 3. Instance Resolution | 3 weeks | Coherence, resolution |
| 4. GADTs | 4 weeks | Indexed types, patterns |
| 5. Monomorphization | 4 weeks | Specialization pass |
| 6. Security HKT | 3 weeks | Security-indexed types |
| 7. Optimization | 3 weeks | Inlining, dead code |

**Total: 24 weeks**

---

## 10. Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Type inference complexity | Medium | High | Restrict polymorphism depth |
| Compilation time | High | Medium | Incremental compilation |
| Code size bloat | Medium | Low | Selective monomorphization |
| Instance coherence | Low | High | Orphan instance restrictions |

---

## 11. Success Criteria

| Criterion | Metric | Target |
|-----------|--------|--------|
| Type class expressiveness | Security patterns | All 5 products |
| Runtime overhead | vs hand-written | < 1% |
| Compile time | Lines/second | > 5,000 |
| Instance resolution | Deterministic | 100% |
| GADT coverage | State machines | 100% |

---

## 12. Decision Rationale

### 12.1 Why Haskell-style?

- **Proven system**: Decades of research and practice
- **Type classes**: Natural abstraction mechanism
- **GADTs**: Essential for security state machines
- **Ecosystem**: Well-understood patterns

### 12.2 Why Monomorphization?

- **Zero overhead**: No dictionary at runtime
- **Optimization**: Better inlining opportunities
- **Rust precedent**: Proven approach

### 12.3 Why Kind Polymorphism?

- **Flexibility**: Abstract over different indexed types
- **Security**: Uniform treatment of labels, effects, capabilities
- **Future-proofing**: Extensible to new indexing domains

---

## Document Metadata

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  Document ID: TERAS-RESEARCH-A17-DECISION                                    ║
║  Version: 1.0.0                                                              ║
║  Status: APPROVED                                                            ║
║  Decision: ADOPT Haskell-style HKT + Monomorphization                        ║
║                                                                              ║
║  Key Design Points:                                                          ║
║  • Type classes (traits) for HKT abstraction                                 ║
║  • Kind polymorphism for flexibility                                         ║
║  • GADTs for indexed security types                                          ║
║  • Aggressive monomorphization for zero overhead                             ║
║  • Integration with linear/effect/row systems                                ║
║                                                                              ║
║  Integration Score: 9.4/10                                                   ║
║  Next Session: A-18 (Type-Level Computation)                                 ║
╚══════════════════════════════════════════════════════════════════════════════╝
```
