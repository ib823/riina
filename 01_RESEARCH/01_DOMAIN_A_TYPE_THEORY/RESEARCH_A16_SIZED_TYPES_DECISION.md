# RESEARCH_A16_SIZED_TYPES_DECISION.md

## TERAS Research Track — Domain A: Type Theory
### Session A-16: Sized Types — Architecture Decision Record

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Architecture Decision
**Status:** APPROVED
**Decision ID:** TERAS-LANG-A16-001

---

# EXECUTIVE SUMMARY

**DECISION:** ADOPT Agda-style sized types as an optional enhancement to structural recursion for TERAS-LANG, enabling type-based termination and productivity guarantees with partial inference and zero runtime overhead.

**RATIONALE:** Sized types provide compositional termination guarantees essential for security-critical code, DoS prevention, and WCET analysis, while maintaining practical usability through default structural recursion with optional size annotations for complex cases.

---

# PART I: DECISION CONTEXT

## 1.1 Problem Statement

TERAS-LANG requires termination guarantees that:
- Ensure all recursive functions terminate
- Guarantee corecursive functions are productive
- Enable compile-time verification of bounded computation
- Support DoS prevention and WCET analysis
- Integrate with linear types, effects, and capabilities

## 1.2 Decision Drivers

| Driver | Weight | Description |
|--------|--------|-------------|
| Security | Critical | DoS prevention via bounded computation |
| D38 | Critical | Zero runtime overhead |
| Verification | High | Type-based termination proofs |
| Integration | High | Coherence with A-04, A-11, A-14, A-15 |
| Usability | Medium | Practical annotation burden |

## 1.3 Candidates Evaluated

| Candidate | Source | Core Approach |
|-----------|--------|---------------|
| Sized Types | Agda | Ordinal sizes in types |
| Decreases Clauses | F* | Manual termination measures |
| Structural Only | Standard | Syntactic termination checking |
| Ordinal Sizes | CIC^ω | Full ordinal theory |

---

# PART II: DECISION SPECIFICATION

## 2.1 Core Decision: Agda-Style Sized Types

### 2.1.1 Size Type Definition

```
Size Type System:

Sizes:
  Size             -- the type of sizes
  i, j, k          -- size variables
  ↑i               -- successor size (i + 1)
  ω                -- infinite size
  i ⊔ j            -- maximum of sizes

Sized Types:
  A^i              -- type A with size bound i
  A^ω              -- unbounded (equivalent to A)

Well-Formedness:
  A : Type    i : Size
  ─────────────────────
  A^i : Type
```

### 2.1.2 Sized Inductive Types

```
Sized Inductive Definition:

data List (A : Type) : Size → Type where
  Nil  : {i : Size} → List A (↑ i)
  Cons : {i : Size} → A → List A i → List A (↑ i)

-- Size bounds list length
-- Constructors increment size

data Nat : Size → Type where
  Zero : {i : Size} → Nat (↑ i)
  Succ : {i : Size} → Nat i → Nat (↑ i)

data Tree (A : Type) : Size → Type where
  Leaf : {i : Size} → A → Tree A (↑ i)
  Node : {i : Size} → Tree A i → Tree A i → Tree A (↑ i)

-- Size bounds tree depth
```

### 2.1.3 Termination via Sizes

```
Termination Guarantee:

Recursive function typing:
  f : ∀i. A^i → B
  f (constr x) = ... f x ...   -- x has smaller size

Rule:
  Γ, f : ∀i. A^i → B ⊢ body : B
  x : A^j where j < i in recursive calls
  ────────────────────────────────────────
  Γ ⊢ fix f. body : ∀i. A^i → B

Example:
  length : ∀i. List^i A → Nat
  length Nil = Zero
  length (Cons x xs) = Succ (length xs)
  -- xs : List^j A where j < i, terminates
```

## 2.2 Sized Coinductive Types (Productivity)

### 2.2.1 Codata with Sizes

```
Sized Coinductive Types:

codata Stream (A : Type) : Size → Type where
  head : Stream A i → A
  tail : {j : Size} → j < i → Stream A i → Stream A j

-- Observations decrease size
-- Guarantees productivity

Productive Definition:
  zeros : ∀i. Stream^i Nat
  head zeros = 0
  tail zeros = zeros  -- guarded by observation

-- Each tail observation decreases size
-- Infinite stream is productive
```

### 2.2.2 Productivity Typing Rule

```
Corecursion Typing:

  Γ, g : ∀i. A → B^i ⊢ body : B^i
  g occurs only under observations
  ────────────────────────────────────
  Γ ⊢ cofix g. body : ∀i. A → B^i

-- Corecursive calls must be guarded
-- Size ensures productivity
```

## 2.3 Size Subtyping

```
Size-Induced Subtyping:

Inductive (covariant):
  i ≤ j
  ──────────────
  A^i <: A^j

-- Smaller data fits in larger type

Coinductive (contravariant for observations):
  j ≤ i
  ──────────────────────────
  Stream^i A <: Stream^j A

-- More observations available with larger size

Universally Quantified:
  ∀i. A^i ≈ A^ω

-- No size bound
```

## 2.4 Default: Structural Recursion

### 2.4.1 Structural Recursion Fallback

```
Default Termination Checking:

When no size annotations:
  - Check structural recursion
  - Arguments must decrease on inductive types
  - Standard lexicographic ordering

Example (no sizes needed):
  map : (A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs
  -- Structurally recursive, no sizes required

When structural fails:
  - Add size annotations
  - Or provide decreases clause
```

### 2.4.2 Hybrid Approach

```
TERAS-LANG Termination Strategy:

1. First attempt: Structural recursion
   - No annotation needed
   - Fast checking
   - Covers most cases

2. If structural fails: Size annotation
   - Developer adds sizes
   - System verifies
   
3. Complex cases: Measure clause
   - decreases { measure_expr }
   - SMT-verified
```

---

# PART III: INTEGRATION SPECIFICATIONS

## 3.1 Integration with Linear Types (A-04)

```
Linear Sized Types:

Syntax:
  lin A^i       -- linear value of bounded size
  aff A^i       -- affine value of bounded size

Rules:
  Γ ⊢ e : lin A^i    i ≤ j
  ───────────────────────────
  Γ ⊢ e : lin A^j

Example:
  process : ∀i. lin Buffer^i → Result
  -- Linear buffer, processing terminates

  exhaust : ∀i. lin Resource^i → ()
  exhaust Empty = ()
  exhaust (Avail r rs) = use r; exhaust rs
  -- Linear resource fully consumed, bounded by size
```

## 3.2 Integration with Effects (A-11)

```
Sized Effects:

Effect with Size Bound:
  effect Bounded^i {
    Step : () → ()
  }
  -- At most i steps

Effectful Sized Functions:
  fn iterate(n : Nat^i) -> () ! Bounded^i {
    match n {
      Zero -> (),
      Succ m -> { step(); iterate(m) }
    }
  }
  -- Effect budget matches recursion

Handler:
  handle iterate(n)
  with BoundedHandler { remaining = i } {
    Step () → { remaining--; resume () }
  }
```

## 3.3 Integration with Capabilities (A-14)

```
Sized Capabilities:

Syntax:
  cap<R, P>^i    -- capability for i uses

Usage Decrement:
  use : cap<R, P>^(↑i) → Result × cap<R, P>^i
  -- Each use decrements remaining

Example:
  api_client : cap<API, Call>^1000 → Results
  api_client cap = 
    let (r1, cap') = call(cap, req1) in
    let (r2, cap'') = call(cap', req2) in
    ...
  -- At most 1000 calls guaranteed by type

Rate Limiting:
  struct RateLimiter<i: Size> {
    cap: cap<Service, Request>^i
  }
  
  fn request<i>(r: RateLimiter<↑i>) -> (Response, RateLimiter<i>)
```

## 3.4 Integration with Staged Types (A-15)

```
Sized Staging:

Generated Code Termination:
  code[A^i → B]    -- generated code terminates on size-i input

Example:
  compile_parser : Grammar → code[∀i. Input^i → AST]
  -- Compiled parser terminates on bounded input

Staging with Bounds:
  fn specialize<i>(pattern: Pattern) -> code[Data^i -> Bool] {
    .<fn data -> match(~pattern, data)>.
  }
  -- Specialized matcher terminates
```

---

# PART IV: TERAS PRODUCT APPLICATIONS

## 4.1 MENARA (Mobile Security)

```
Bounded Mobile Operations:

Session Handling:
  process_session : ∀i. Events^i → Actions
  -- Session processing terminates

Token Refresh:
  refresh_loop : ∀i. cap<TokenService, Refresh>^i → ()
  -- Bounded refresh attempts

Crypto Operations:
  pbkdf2 : ∀i. Nat^i → Password → Salt → Key
  -- Iterations bounded by i
```

## 4.2 GAPURA (Web Application Firewall)

```
Bounded Request Processing:

Request Parsing:
  parse_request : ∀i. Bytes^i → Request
  -- Parsing terminates, DoS prevented

Rule Evaluation:
  eval_rules : ∀i. Rules → Request^i → Decision
  -- Bounded by request size

Rate Limiting:
  throttle : ∀i. cap<Client, Request>^i → RateLimiter
  -- Per-client request bounds
```

## 4.3 ZIRAH (Endpoint Detection & Response)

```
Bounded Detection:

Signature Matching:
  match_signatures : ∀i. Patterns → Memory^i → Matches
  -- Bounded memory scan

Behavior Analysis:
  analyze_behavior : ∀i. Events^i → ThreatScore
  -- Bounded event processing

Remediation:
  remediate : ∀i. cap<System, Action>^i → Threats → ()
  -- Bounded remediation attempts
```

## 4.4 BENTENG (eKYC/Identity)

```
Bounded Verification:

Document Processing:
  process_document : ∀i. Image^i → DocumentFields
  -- Bounded image processing

Template Matching:
  match_template : ∀i. Template → Face^i → Score
  -- Bounded face matching iterations

Retry Logic:
  verify_with_retry : ∀i. cap<Verifier, Attempt>^i → Input → Result
  -- Bounded retry attempts
```

## 4.5 SANDI (Digital Signatures)

```
Bounded Crypto:

Key Derivation:
  derive_key : ∀i. Nat^i → Master → Derived
  -- Bounded iterations

Certificate Chain:
  verify_chain : ∀i. CertChain^i → Validity
  -- Bounded chain length

HSM Operations:
  hsm_sign : ∀i. cap<HSM, Sign>^i → Messages → Signatures
  -- Bounded HSM operations
```

---

# PART V: TYPE SYSTEM SPECIFICATION

## 5.1 Sized Type Formation

```
Sized Type Grammar:

SizedType ::= Type^Size
            | SizedType → SizedType
            | ∀i. SizedType
            | lin SizedType
            | cap<R, P>^Size

Size ::= SizeVar
       | ↑Size
       | Size ⊔ Size
       | ω

Well-Formedness:
  A : Type    s : Size
  ─────────────────────
  A^s : Type

Size Formation:
  ───────────
  ω : Size

  s : Size
  ──────────
  ↑s : Size
```

## 5.2 Typing Rules

```
Core Sized Typing Rules:

-- Size subtyping
s₁ ≤ s₂    Γ ⊢ e : A^s₁
──────────────────────────
Γ ⊢ e : A^s₂

-- Sized function application
Γ ⊢ f : ∀i. A^i → B    Γ ⊢ e : A^s
─────────────────────────────────────
Γ ⊢ f e : B[s/i]

-- Recursive definition
Γ, f : ∀i. A^i → B ⊢ body : B
All recursive calls on smaller sizes
──────────────────────────────────────
Γ ⊢ fix f. body : ∀i. A^i → B

-- Corecursive definition
Γ, g : ∀i. A → B^i ⊢ body : B^i
All corecursive calls guarded
──────────────────────────────────────
Γ ⊢ cofix g. body : ∀i. A → B^i
```

## 5.3 Soundness Properties

```
Sized Type Theorems:

THEOREM (Termination):
  If f : ∀i. A^i → B is well-typed,
  then f terminates on all inputs.

THEOREM (Productivity):
  If g : ∀i. A → B^i is well-typed,
  then g produces output for any number of observations.

THEOREM (Size Erasure):
  Sizes can be erased without affecting runtime behavior.
  (Zero runtime overhead)

THEOREM (Subject Reduction):
  If Γ ⊢ e : A^i and e →* e', then Γ ⊢ e' : A^i.
```

---

# PART VI: IMPLEMENTATION ROADMAP

## 6.1 Phase Structure

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| Phase 1 | Weeks 1-3 | Size type syntax and formation |
| Phase 2 | Weeks 4-6 | Structural recursion default |
| Phase 3 | Weeks 7-10 | Sized inductive types |
| Phase 4 | Weeks 11-13 | Sized coinductive types |
| Phase 5 | Weeks 14-16 | Integration with A-04, A-11, A-14 |
| Phase 6 | Weeks 17-20 | TERAS product APIs |

## 6.2 Implementation Notes

```
Phase 1: Size Syntax
  - Size type and operations
  - Size comparison and ordering
  - Parser integration

Phase 2: Structural Default
  - Standard termination checker
  - Lexicographic ordering
  - Error messages for non-termination

Phase 3: Sized Inductive
  - Sized data definitions
  - Constructor sizing
  - Size inference (partial)

Phase 4: Sized Coinductive
  - Codata with sizes
  - Productivity checking
  - Observation size decrease

Phase 5: Integration
  - lin A^i combination
  - cap<R,P>^i usage bounds
  - code[A^i → B] termination
```

---

# PART VII: DECISION RECORD

## 7.1 Decision Statement

**ADOPTED:** Agda-style sized types as optional enhancement:

1. **Default:** Structural recursion checking
   - No annotation required for simple cases
   - Standard termination checking

2. **Enhancement:** Sized types when needed
   - A^i syntax for size-bounded types
   - Partial size inference
   - For non-structural patterns

3. **Integration:** Full coherence with type system
   - lin A^i for linear bounded resources
   - cap<R,P>^i for usage-limited capabilities
   - code[A^i → B] for terminating generated code

## 7.2 Alternatives Rejected

| Alternative | Reason for Rejection |
|-------------|---------------------|
| F* decreases only | Insufficient integration, manual |
| No termination checking | Unacceptable for security code |
| Full ordinal theory | Too complex, overkill |
| Structural only | Misses useful programs |

## 7.3 Consequences

**Positive:**
- Guaranteed termination for security code
- DoS prevention via bounded computation
- Zero runtime overhead
- Compositional reasoning
- Good integration with type system

**Negative:**
- Learning curve for sized types
- Size inference not always complete
- Some annotation burden for complex cases

**Neutral:**
- Requires careful integration with other features
- Size ordering must be consistent

## 7.4 Compliance

| Requirement | Compliance | Notes |
|-------------|------------|-------|
| D38 (Performance) | ✓ Full | Zero overhead, sizes erased |
| Security | ✓ Full | Termination guarantees |
| Integration | ✓ Full | Works with all systems |
| Usability | ✓ Good | Default structural + optional sizes |

## 7.5 Approval

```
Decision: APPROVED
Date: 2026-01-03
Authority: TERAS-LANG Architecture Board (Simulated)
Review Cycle: 6 months

Alignment Score: 9.0/10

Scoring Breakdown:
  Termination Guarantee:   24/25
  Integration:             18/20
  Inference:               16/20
  Zero Overhead:           15/15
  Expressiveness:           8/10
  Formalization:            9/10
  ─────────────────────────────
  Total:                   90/100
```

---

**END OF DECISION DOCUMENT**

**Session A-16 Complete**
**Next Session:** A-17 (Type Inference Algorithms)
