# TERAS RESEARCH DECISION: DEPENDENT TYPES
## Session A-09: Dependent Type System Architecture for TERAS-LANG

**Document ID:** RESEARCH_A09_DEPENDENT_TYPES_DECISION  
**Version:** 1.0.0  
**Date:** 2026-01-03  
**Status:** APPROVED  
**Classification:** TERAS Research Track - Domain A (Type Theory)

---

## DECISION SUMMARY

| Field | Value |
|-------|-------|
| **Decision ID** | A-09-DEC |
| **Decision Title** | Dependent Type System Architecture |
| **Status** | APPROVED |
| **Date** | 2026-01-03 |

**DECISION STATEMENT:**

ADOPT a hybrid dependent type system combining Idris 2's Quantitative Type Theory (QTT) foundation with Lean 4's engineering model, providing full dependent types integrated with linear types, algebraic effects, session types, and refinement types as established in sessions A-04 through A-08.

---

## 1. CONTEXT AND MOTIVATION

### 1.1 Why Dependent Types for TERAS

Dependent types enable TERAS-LANG to express security properties directly in the type system:

1. **Protocol State Machines:** Channel types that track protocol state
2. **Bounds Checking:** Vector/buffer types indexed by length
3. **Security Labels:** Types indexed by classification level
4. **Access Control:** Capability types encoding permissions
5. **Invariant Enforcement:** Types that guarantee correctness properties

### 1.2 Integration Requirements

The dependent type system must integrate with:
- **A-04 Linear Types:** Resource management, unique references
- **A-05 Effect Systems:** Controlled side effects
- **A-06 Uniqueness Types:** Single-owner resources
- **A-07 Session Types:** Protocol verification
- **A-08 Refinement Types:** SMT-backed predicates

### 1.3 Constraints from TERAS Laws

| Law | Constraint |
|-----|------------|
| Law 1 (Self-Sufficiency) | No external proof assistants required |
| Law 2 (Formal Verification) | Type system must enable verification |
| Law 3 (Performance) | Dependent types must not impact runtime |
| Law 6 (Compile-Time) | All dependent type checking at compile time |

---

## 2. ARCHITECTURE DECISION

### 2.1 Core Type System: QTT + Dependent Types

**Foundation:** Quantitative Type Theory (Atkey 2018, McBride 2016)

```
Kinds:
  κ ::= Type_n           -- Universe at level n
      | Prop             -- Proof-irrelevant propositions
      | Effect           -- Effect kinds
      | Session          -- Session type kinds
      | Region           -- Memory region kinds

Quantities:
  q ::= 0                -- Erased (compile-time only)
      | 1                -- Linear (exactly once)
      | ω                -- Unrestricted

Types:
  A, B ::= X                           -- Type variable
         | (q x : A) → B               -- Quantitative dependent function
         | (x : A) × B                 -- Dependent pair
         | {x : A | φ}                 -- Refinement type
         | A @ (q, u)                  -- Graded type (quantity, uniqueness)
         | Chan<S>                     -- Session channel
         | eff[E] A                    -- Effectful computation
         | ∀(x : A). B                 -- Universe-polymorphic
         | A ≡ B                       -- Propositional equality
```

### 2.2 Universe Structure

```
-- Universe hierarchy (predicative)
Type₀ : Type₁ : Type₂ : ...

-- Cumulativity
A : Type_n  implies  A : Type_{n+1}

-- Proof universe (impredicative, proof-irrelevant)
Prop : Type₀

-- Rule: Prop is proof-irrelevant
-- If p : P where P : Prop, then p erased at runtime
```

**Universe Polymorphism:**
```
-- Level-polymorphic identity
fn id<l: Level, A: Type_l>(x: A) -> A = x

-- Level constraints
fn compose<l1, l2, l3: Level, A: Type_l1, B: Type_l2, C: Type_l3>
  (g: B -> C, f: A -> B) -> A -> C
  = \x => g (f x)
```

### 2.3 Dependent Function Types

```
-- Standard dependent function
type Pi(x: A) -> B(x)

-- Syntax sugar
(x: A) -> B       -- when B depends on x
A -> B            -- when B doesn't depend on x (non-dependent)

-- Quantitative dependent function
(0 x: A) -> B     -- Erased argument (compile-time only)
(1 x: A) -> B     -- Linear argument (use exactly once)
(ω x: A) -> B     -- Unrestricted argument (use any times)

-- Formation rule
Γ ⊢ A : Type_i    Γ, x:A ⊢ B : Type_j
────────────────────────────────────────
     Γ ⊢ (q x: A) → B : Type_{max(i,j)}

-- Introduction rule
    Γ, q·x:A ⊢ t : B
───────────────────────────
Γ ⊢ λx.t : (q x: A) → B

-- Elimination rule
Γ ⊢ f : (q x: A) → B    Γ ⊢ q·a : A
─────────────────────────────────────
         Γ ⊢ f a : B[a/x]
```

### 2.4 Dependent Pair Types (Sigma Types)

```
-- Dependent pair
type Sigma(x: A) × B(x)

-- Syntax
(x: A) × B        -- dependent pair type
(a, b)            -- pair introduction (a: A, b: B[a/x])

-- Formation rule
Γ ⊢ A : Type_i    Γ, x:A ⊢ B : Type_j
────────────────────────────────────────
     Γ ⊢ (x: A) × B : Type_{max(i,j)}

-- Introduction rule
Γ ⊢ a : A    Γ ⊢ b : B[a/x]
───────────────────────────────
  Γ ⊢ (a, b) : (x: A) × B

-- Elimination (projections)
Γ ⊢ p : (x: A) × B
────────────────────
   Γ ⊢ π₁ p : A

Γ ⊢ p : (x: A) × B
──────────────────────────
   Γ ⊢ π₂ p : B[π₁ p/x]
```

### 2.5 Inductive Families

```
-- Length-indexed vectors
data Vec<A: Type, n: Nat>: Type {
  Nil: Vec<A, 0>
  Cons: (1 head: A, 1 tail: Vec<A, k>) -> Vec<A, k + 1>
}

-- Bounded natural numbers
data Fin<n: Nat>: Type {
  FZero: Fin<n + 1>
  FSucc: Fin<n> -> Fin<n + 1>
}

-- Safe indexing (cannot fail)
fn index<A: Type, n: Nat>(v: Vec<A, n>, i: Fin<n>) -> A {
  match (v, i) {
    (Cons(x, _), FZero) => x,
    (Cons(_, xs), FSucc(j)) => index(xs, j),
    // No case for (Nil, _) - Fin<0> is uninhabited!
  }
}
```

### 2.6 Propositional Equality

```
-- Identity type
data Eq<A: Type>(x: A): A -> Prop {
  Refl: Eq<A>(x, x)
}

-- Notation: x ≡ y  for  Eq<A>(x, y)

-- Symmetry
fn sym<A: Type, x y: A>(p: x ≡ y) -> y ≡ x {
  match p {
    Refl => Refl
  }
}

-- Transitivity
fn trans<A: Type, x y z: A>(p: x ≡ y, q: y ≡ z) -> x ≡ z {
  match (p, q) {
    (Refl, Refl) => Refl
  }
}

-- Congruence
fn cong<A B: Type, x y: A>(f: A -> B, p: x ≡ y) -> f(x) ≡ f(y) {
  match p {
    Refl => Refl
  }
}

-- Transport (substitution)
fn transport<A: Type, P: A -> Type, x y: A>
  (p: x ≡ y, px: P(x)) -> P(y)
{
  match p {
    Refl => px
  }
}
```

---

## 3. INTEGRATION WITH PRIOR DECISIONS

### 3.1 Integration with A-04 Linear Types

```
-- Combined linear + dependent function
(1 x: Vec<A, n>) -> Vec<B, n>  -- Linear, length-preserving

-- Uniqueness + dependent
(1 x: uniq Buffer<n>) -> Result<uniq Buffer<n>, Error>

-- Linear pair (both components linear)
type LinPair<A, B> = (1 x: A) × (1 _: B)

-- Example: Safe buffer manipulation
fn split<n m: Nat>(1 buf: Buffer<n + m>) -> (Buffer<n>, Buffer<m>) {
  // Type ensures exactly n+m bytes
  // Linearity ensures no aliasing
  let (left, right) = buffer_split(buf, n);
  (left, right)
}
```

### 3.2 Integration with A-05 Effect Systems

```
-- Dependent effects: effect type depends on value
effect SecureIO<L: SecurityLevel> {
  fn read_secret() -> Secret<Bytes, L>
  fn audit(msg: String) -> ()
}

-- Effect indexed by security level
fn process<L: SecurityLevel>(secret: Secret<Data, L>) 
  -> eff[SecureIO<L>] Result<Output, Error>
{
  let data = perform read_secret();
  perform audit("Processing data");
  Ok(transform(data))
}

-- Effect polymorphism with dependent effects
fn map_effect<E: Effect, A B: Type, L: Level>
  (f: A -> eff[E] B, xs: Vec<A, n>) 
  -> eff[E] Vec<B, n>
```

### 3.3 Integration with A-06 Uniqueness Types

```
-- Unique dependent values
type UniqVec<A: Type, n: Nat> = uniq Vec<A, n>

-- Transfer ownership with length proof
fn transfer<n: Nat>(1 src: uniq Buffer<n>) 
  -> (uniq Buffer<n>, Eq<Nat>(length(src), n))
{
  (src, Refl)  // Proof that length is preserved
}

-- Unique capabilities indexed by permissions
type Cap<P: Permission> = lin uniq Capability<P>

fn use_cap<P: Permission>(1 cap: Cap<P>) -> eff[P] ()
```

### 3.4 Integration with A-07 Session Types

```
-- Session types are dependent on protocol state
session AuthProtocol {
  !Credentials.               -- Send credentials
  ?{                          -- Receive choice
    Accepted: ?Token. end,    -- If accepted, receive token
    Rejected: ?Reason. end    -- If rejected, receive reason
  }
}

-- Channel type depends on session state
type AuthChannel<S: SessionState> = lin uniq Chan<S>

-- State transition preserves session structure
fn send_creds<S: SessionState>(
  1 chan: AuthChannel<!Credentials.S>,
  creds: Credentials
) -> AuthChannel<S>
{
  channel_send(chan, creds)
}

-- Dependent branching
fn handle_response<S: SessionState>(
  1 chan: AuthChannel<?{Accepted: SA, Rejected: SR}>
) -> Either<AuthChannel<SA>, AuthChannel<SR>>
{
  match channel_offer(chan) {
    Accept(c) => Left(c),
    Reject(c) => Right(c)
  }
}
```

### 3.5 Integration with A-08 Refinement Types

```
-- Refinement + Dependent types
type BoundedVec<A: Type, n: Nat, max: Nat> = 
  { v: Vec<A, n> | n <= max }

-- Dependent refinement predicates
fn safe_access<n: Nat, i: Nat>(
  v: Vec<A, n>, 
  idx: { x: Nat | x < n }
) -> A
{
  // idx < n guaranteed by refinement
  index(v, idx)
}

-- Combining with effects
fn validated_input<n: Nat>(
  data: { d: Bytes | length(d) == n }
) -> eff[Validation] { r: Result<Valid, Error> | 
                        is_ok(r) ==> validated(r.value) }
```

---

## 4. TYPE CHECKING ALGORITHM

### 4.1 Bidirectional Dependent Type Checking

```
Mode ::= Check | Infer

-- Inference: term → type
infer(Γ, e) : (Type, Substitution)

-- Checking: term × type → success/failure
check(Γ, e, A) : Result<(), TypeError>

-- Core rules
infer(Γ, x) = lookup(Γ, x)
infer(Γ, f e) = 
  let (Π(x:A).B, σ₁) = infer(Γ, f)
  let σ₂ = check(Γ, e, A[σ₁])
  (B[e/x][σ₁∘σ₂], σ₁∘σ₂)

check(Γ, λx.t, Π(x:A).B) =
  check(Γ, x:A, t, B)

check(Γ, e, A) =
  let (A', σ) = infer(Γ, e)
  unify(A'[σ], A[σ])
```

### 4.2 Definitional Equality

```
-- Definitional equality: decided by computation
A ≡ B  iff  normalize(A) = normalize(B)

-- Normalization rules
(λx.t) a ⟶ t[a/x]           -- β-reduction
(π₁ (a, b)) ⟶ a             -- pair projection
(π₂ (a, b)) ⟶ b
match Cons(x,xs) { Cons(y,ys) => e, ... } ⟶ e[x/y, xs/ys]

-- Type-directed η-expansion for comparison
normalize((λx.f x)) = normalize(f)  -- if x ∉ fv(f)
```

### 4.3 Universe Checking

```
-- Universe level inference
infer_level(Γ, Type) = (Type₁, level + 1)
infer_level(Γ, Prop) = (Type₀, 0)

-- Universe constraint solving
Γ ⊢ A : Type_i    Γ ⊢ B : Type_j
──────────────────────────────────────
Γ ⊢ A → B : Type_{max(i, j)}

-- Predicativity check
Γ ⊢ Π(x:A).B : Type_n
  requires: level(A) ≤ n  and  level(B) ≤ n
```

### 4.4 Quantity Checking

```
-- Resource usage tracking (from A-04)
Γ = (0·x:A, 1·y:B, ω·z:C)

-- Split context for application
Γ ⊢ f : (1 x:A) → B    Δ ⊢ a : A
──────────────────────────────────────
        Γ + Δ ⊢ f a : B

-- Context addition
0·Γ + 0·Γ = 0·Γ
q·Γ + 0·Δ = q·Γ    (if Γ and Δ agree on types)
1·x + 1·x = undefined (linear used twice)
```

---

## 5. SECURITY APPLICATIONS

### 5.1 Type-Safe Protocol Implementation

```
-- TLS handshake as dependent type
session TLSHandshake {
  !ClientHello.
  ?ServerHello.
  ?Certificate.
  !ClientKeyExchange.
  !{ChangeCipherSpec}.
  ?{ChangeCipherSpec}.
  secure: end  -- Type guarantees we reach secure state
}

fn tls_connect(
  server: Address
) -> eff[Network, Crypto] Result<SecureChannel, TLSError>
{
  let (1 chan) = connect(server);  // Get linear channel
  
  // Each step is type-checked for protocol compliance
  let (1 chan) = send_client_hello(chan)?;
  let (server_hello, 1 chan) = recv_server_hello(chan)?;
  let (cert, 1 chan) = recv_certificate(chan)?;
  
  // Verify certificate (effect-tracked)
  verify_cert(cert)?;
  
  let (1 chan) = send_key_exchange(chan)?;
  let (1 chan) = send_change_cipher_spec(chan)?;
  let (1 chan) = recv_change_cipher_spec(chan)?;
  
  // chan now has type SecureChannel
  Ok(chan)
}
```

### 5.2 Memory-Safe Buffer Operations

```
-- Fixed-size buffer with compile-time bounds
struct SafeBuffer<const N: Nat> {
  data: [u8; N]
}

impl<const N: Nat> SafeBuffer<N> {
  // Index is statically bounded
  fn get(self: &Self, i: Fin<N>) -> u8 {
    // i < N guaranteed by Fin<N> type
    self.data[fin_to_nat(i)]
  }
  
  // Copy with length proof
  fn copy_from<const M: Nat>(
    self: &mut Self,
    src: &SafeBuffer<M>,
    proof: M <= N  // Compile-time proof required
  ) {
    // Safe: M <= N guaranteed
    intrinsic_copy(self.data, src.data, M)
  }
  
  // Split preserves total length
  fn split<const K: Nat>(
    self: SafeBuffer<N>
  ) -> (SafeBuffer<K>, SafeBuffer<N - K>)
    where K <= N  // Constraint checked at compile time
  {
    // Type ensures K + (N-K) = N
    intrinsic_split(self, K)
  }
}
```

### 5.3 Information Flow with Dependent Labels

```
-- Security labels form a lattice
type Label = { level: Nat, compartments: Set<String> }

fn label_join(l1: Label, l2: Label) -> Label {
  { level: max(l1.level, l2.level),
    compartments: l1.compartments ∪ l2.compartments }
}

-- Labeled type indexed by label
type Labeled<T: Type, L: Label> = struct {
  value: T
}

-- Can only combine if result label dominates inputs
fn combine<A B C: Type, L1 L2: Label>(
  x: Labeled<A, L1>,
  y: Labeled<B, L2>,
  f: (A, B) -> C
) -> Labeled<C, label_join(L1, L2)>
{
  Labeled { value: f(x.value, y.value) }
}

-- Declassification requires proof of authorization
fn declassify<T: Type, L_high L_low: Label>(
  x: Labeled<T, L_high>,
  auth: DeclassAuth<L_high, L_low>  -- Authorization proof
) -> Labeled<T, L_low>
{
  Labeled { value: x.value }
}
```

---

## 6. IMPLEMENTATION ROADMAP

### 6.1 Phased Implementation

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| **Phase 1** | Weeks 1-6 | Core dependent types (Π, Σ) |
| **Phase 2** | Weeks 7-12 | Inductive families, pattern matching |
| **Phase 3** | Weeks 13-18 | Universe polymorphism |
| **Phase 4** | Weeks 19-24 | Integration with linear types |
| **Phase 5** | Weeks 25-30 | Refinement type integration |
| **Phase 6** | Weeks 31-36 | Session type integration |
| **Phase 7** | Weeks 37-42 | Optimization and tooling |

### 6.2 Phase 1: Core Dependent Types

**Deliverables:**
1. Dependent function type (`Π`)
2. Dependent pair type (`Σ`)
3. Basic type inference
4. β-reduction and η-expansion
5. Type-in-Type (temporary, for bootstrapping)

**Validation:**
- Type `Vec<A, n>` and `Fin<n>`
- Implement `index : Vec<A, n> -> Fin<n> -> A`
- Verify type safety

### 6.3 Phase 2: Inductive Families

**Deliverables:**
1. Indexed inductive definitions
2. Dependent pattern matching
3. Coverage checking
4. Termination checking

**Validation:**
- Implement `Eq<A>(x, y)` type
- Prove `sym`, `trans`, `cong`
- Verify pattern matching totality

### 6.4 Phase 4: Linear Integration

**Deliverables:**
1. QTT resource tracking with dependent types
2. Linear dependent functions
3. Uniqueness + dependent types

**Validation:**
- `(1 x: A) -> B(x)` type works correctly
- Linear resources tracked through dependent code
- Unique buffers with dependent lengths

---

## 7. ALIGNMENT WITH TERAS PRODUCTS

### 7.1 MENARA (Mobile Security)

```
-- Device attestation with dependent types
type AttestationReport<D: DeviceClass> = struct {
  device: DeviceId,
  class_proof: IsClass<device, D>,  -- Proof device is of class D
  measurements: Vec<Hash, measurement_count(D)>
}

fn verify_attestation<D: DeviceClass>(
  report: AttestationReport<D>,
  expected: ExpectedMeasurements<D>
) -> Result<Verified<D>, AttestationError>
```

### 7.2 BENTENG (eKYC)

```
-- Identity verification stages as dependent types
data VerificationStage: Nat -> Type {
  Initial: VerificationStage<0>
  DocumentVerified: VerificationStage<1>
  BiometricMatched: VerificationStage<2>
  FullyVerified: VerificationStage<3>
}

-- Can only access PII after full verification
fn get_pii<n: Nat>(
  session: VerificationStage<n>,
  proof: n >= 3
) -> eff[AuditLog] PersonalInfo
```

### 7.3 GAPURA (WAF)

```
-- Request processing with dependent state
type RequestState<analyzed: Bool, validated: Bool>

fn analyze(
  req: RequestState<false, false>
) -> RequestState<true, false>

fn validate(
  req: RequestState<true, false>,
  rules: RuleSet
) -> Either<RequestState<true, true>, BlockedRequest>

fn forward(
  req: RequestState<true, true>  -- Only validated requests
) -> eff[Network] Response
```

---

## 8. DECISION RATIONALE

### 8.1 Why QTT Foundation

1. **Unifies linear and dependent types:** Single coherent system
2. **Well-studied theory:** Atkey 2018, McBride's work
3. **Practical:** Idris 2 demonstrates feasibility
4. **Expressive:** Can encode uniqueness, affine, relevant types

### 8.2 Why Not Pure MLTT

1. **No linear types:** Essential for security
2. **No effects:** Needed for real-world programming
3. **Research-focused:** Not practical enough for TERAS

### 8.3 Why Not Full CIC/Coq

1. **Too complex:** Impredicative universes add complexity
2. **Proof-focused:** TERAS needs programming focus
3. **No linear types:** Would need extension anyway

---

## 9. RISKS AND MITIGATIONS

| Risk | Severity | Mitigation |
|------|----------|------------|
| Type checking complexity | High | Bidirectional checking, incremental verification |
| Performance overhead | Medium | Erasure of type-level computation |
| User learning curve | Medium | Good error messages, documentation, IDE support |
| Integration complexity | High | Careful phase design, extensive testing |
| Undecidability | Low | Termination checking, user-provided proofs |

---

## 10. SUCCESS CRITERIA

1. **Correctness:** Type system is sound (no runtime type errors)
2. **Expressiveness:** Can encode all TERAS security invariants
3. **Performance:** No runtime overhead for type-level computation
4. **Usability:** Security engineers can write dependent types
5. **Integration:** Seamless with linear, effect, session, refinement types

---

## 11. APPROVAL AND SIGN-OFF

| Role | Status | Date |
|------|--------|------|
| Type Theory Lead | APPROVED | 2026-01-03 |
| Security Architect | APPROVED | 2026-01-03 |
| TERAS-LANG Lead | APPROVED | 2026-01-03 |

---

## 12. ALIGNMENT SCORE

**Overall Alignment: 9.2/10**

| Dimension | Score | Notes |
|-----------|-------|-------|
| Security Expressiveness | 10/10 | Full dependent types for invariants |
| A-04 Integration | 9/10 | QTT provides native integration |
| A-05 Integration | 9/10 | Dependent effects work well |
| A-07 Integration | 9/10 | Session types natural with linearity |
| A-08 Integration | 9/10 | Refinements as dependent subtypes |
| Practicality | 8/10 | Complexity concern, but manageable |
| Performance | 10/10 | All erased at runtime |

---

**END OF DECISION DOCUMENT**

*Document generated for TERAS Research Track - Session A-09*
*Session A-09 COMPLETE*
