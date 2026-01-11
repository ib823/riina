# RESEARCH_A08_DEPENDENT_TYPES_DECISION.md

## TERAS-LANG Research Track — Session A-08
## Architecture Decision: Dependent Types for TERAS-LANG

**Version:** 1.0.0
**Date:** 2026-01-03
**Status:** COMPLETE
**Depends On:** 
- RESEARCH_A08_DEPENDENT_TYPES_SURVEY.md
- RESEARCH_A08_DEPENDENT_TYPES_COMPARISON.md
- RESEARCH_A04_LINEAR_TYPES_DECISION.md (graded linear types)
- RESEARCH_A03_REFINEMENT_TYPES_DECISION.md (SMT refinements)

---

# PART I: EXECUTIVE SUMMARY

## 1.1 Decision Statement

**DECISION:** ADOPT Quantitative Type Theory (QTT) as the foundation for TERAS-LANG dependent types, providing unified dependent and linear types through multiplicity-annotated bindings, with a layered verification strategy that combines SMT-decidable refinements for automation with full dependent types for complex proofs.

## 1.2 Key Design Choices

| Aspect | Decision | Rationale |
|--------|----------|-----------|
| **Foundation** | QTT (à la Idris 2) | Unifies dependent and linear types |
| **Universes** | Cumulative hierarchy | Reduces annotation burden |
| **Pattern matching** | Dependent with K | Practical programming support |
| **Verification** | Layered (SMT + proofs) | Balance automation and power |
| **Erasure** | Multiplicity-based (0, 1, ω) | Efficient runtime, precise control |
| **Type inference** | Bidirectional | Decidable with predictable annotations |

## 1.3 Alignment Score

**Overall: 9.2/10**

| Criterion | Score | Notes |
|-----------|-------|-------|
| Security expressiveness | 9.5/10 | Full security property encoding |
| Linear integration | 10/10 | QTT provides native unification |
| Verification capability | 9/10 | Layered approach covers all needs |
| Performance | 9/10 | Erasure eliminates runtime overhead |
| Implementation complexity | 8/10 | QTT is well-understood |

---

# PART II: DETAILED DESIGN

## 2.1 Core Type System: QTT Foundation

### Multiplicity-Annotated Bindings

Following Idris 2's QTT, every binding carries a multiplicity annotation:

```
Multiplicities:
  0   — erased (compile-time only)
  1   — linear (used exactly once)
  ω   — unrestricted (used any number of times)
```

### Type Formation Rules

**Dependent Function Type (Π-type with multiplicity):**

```
Γ ⊢ A : Type_i    Γ, x :^m A ⊢ B : Type_j
───────────────────────────────────────────
        Γ ⊢ (m x : A) → B : Type_max(i,j)
```

Where `m` is the multiplicity of `x` in `B` and in the function body.

**Dependent Pair Type (Σ-type with multiplicity):**

```
Γ ⊢ A : Type_i    Γ, x :^m A ⊢ B : Type_j
───────────────────────────────────────────
      Γ ⊢ (m x : A) × B : Type_max(i,j)
```

### TERAS-LANG Syntax

```teras
// Erased index (0 multiplicity)
fn replicate<0 n: Nat, T>(value: T) -> Vec<T, n>

// Linear argument (1 multiplicity)
fn consume<T>(1 resource: Resource<T>) -> T

// Unrestricted (ω, default)
fn identity<T>(x: T) -> T
```

**Explicit syntax:**
```teras
// Full annotation syntax
fn example<0 n: Nat>(1 x: Vec<T, n>, y: T) -> Vec<T, n + 1>
//         ↑         ↑                ↑
//      erased    linear      unrestricted (default)
```

## 2.2 Universe Hierarchy

### Cumulative Universes

TERAS-LANG uses cumulative universes for ergonomics:

```
Type₀ : Type₁ : Type₂ : ...

// Subtyping
If A : Type_i, then A : Type_j for all j ≥ i
```

### Universe Polymorphism

For generic definitions that work at any universe level:

```teras
// Universe-polymorphic identity
fn id<level ℓ, A: Type<ℓ>>(x: A) -> A {
    x
}

// Pair type at any level
type Pair<level ℓ, A: Type<ℓ>, B: Type<ℓ>> = (A, B)
```

### Typical Universe Ambiguity

For common cases, TERAS-LANG infers the minimal universe:

```teras
// Universe automatically determined
type Container<T> = {
    data: T,
    size: Nat
}
// Inferred: Container : Type<ℓ> → Type<ℓ>
```

## 2.3 Dependent Pattern Matching

### Basic Dependent Patterns

```teras
fn head<T, 0 n: Nat>(vec: Vec<T, n + 1>) -> T {
    match vec {
        Cons(x, _) => x
        // Nil case impossible: n + 1 ≠ 0
    }
}

fn append<T, 0 m: Nat, 0 n: Nat>(
    xs: Vec<T, m>,
    ys: Vec<T, n>
) -> Vec<T, m + n> {
    match xs {
        Nil => ys,                       // m = 0, result: Vec<T, n>
        Cons(x, rest) => Cons(x, append(rest, ys))
                                         // m = m' + 1, result: Vec<T, m' + 1 + n>
    }
}
```

### With-Abstraction

For pattern matching on intermediate computations:

```teras
fn filter<T, 0 n: Nat>(
    pred: T -> Bool,
    xs: Vec<T, n>
) -> (0 m: Nat, Vec<T, m>) {
    match xs {
        Nil => (0, Nil),
        Cons(x, rest) => {
            let (m', filtered) = filter(pred, rest);
            match pred(x) {
                true => (m' + 1, Cons(x, filtered)),
                false => (m', filtered)
            }
        }
    }
}
```

### Absurd Patterns

For impossible cases:

```teras
fn impossible<T>(vec: Vec<T, 0>, elem: Elem<T, vec>) -> ! {
    // No elements in empty vector
    match elem {
        // Pattern exhausted — impossible case
    }
}
```

## 2.4 Layered Verification Strategy

### Layer 1: SMT-Decidable Refinements

For properties decidable by SMT solvers:

```teras
// Refinement types with SMT automation
type Positive = {x: Int | x > 0}
type BoundedArray<n: Nat> = {a: Array<Int> | a.len == n}

// Index bounds automatically verified
fn safe_get<0 n: Nat>(
    arr: Array<T, n>,
    idx: {i: Nat | i < n}
) -> T {
    arr[idx]  // SMT verifies bounds
}
```

### Layer 2: Full Dependent Types

For properties requiring complex proofs:

```teras
// Full dependent type for sorting proof
fn sort_preserves_length<T: Ord, 0 n: Nat>(
    xs: Vec<T, n>
) -> (ys: Vec<T, n>, proof: Sorted<ys>) {
    // Implementation with proof construction
}

// Type-level proof terms
type Sorted<xs: Vec<T, n>> = SortedProof<xs>
```

### Layer 3: External Verification (Optional)

Integration with proof assistants for highest assurance:

```teras
// Marker for externally verified functions
#[verified_in("Lean4", "proofs/crypto.lean")]
fn constant_time_compare(a: Bytes, b: Bytes) -> Bool
```

## 2.5 Security Type Integration

### With Linear Types (A-04)

QTT naturally unifies dependent and linear:

```teras
// Linear capability with dependent protocol
type Cap<0 level: SecurityLevel, 1 resource: ResourceId> = {
    level: level,
    resource: resource,
    operations: AllowedOps<level, resource>
}

// Consuming capability
fn use_cap<0 level: SecurityLevel, 0 res: ResourceId>(
    1 cap: Cap<level, res>
) -> CapResult<level, res> {
    // cap consumed, cannot be reused
}
```

### With Session Types (A-07)

Dependent session types with linear channels:

```teras
// Value-dependent protocol
session AuthProtocol = 
    !Credentials.
    ?(result: AuthResult).
    match result {
        Success(token) => !Ack. end<Success, token>,
        Failure(reason) => end<Failure, reason>
    }

// Linear channel carries dependent state
fn authenticate(1 chan: Chan<AuthProtocol>, creds: Credentials) 
    -> (result: AuthResult, proof: AuthProof<result>)
```

### With Refinement Types (A-03)

Seamless interaction:

```teras
// Dependent type with refinement
type SecureBuffer<0 n: {m: Nat | m > 0 && m <= MAX_SIZE}> = {
    data: Array<Byte, n>,
    filled: {k: Nat | k <= n}
}

// Refinement lifted to dependent index
fn extend<0 n: Nat, 0 m: Nat>(
    buf: SecureBuffer<n>,
    extra: Array<Byte, m>
) -> SecureBuffer<n + m>
where n + m <= MAX_SIZE  // Refinement constraint
```

---

# PART III: TYPE INFERENCE

## 3.1 Bidirectional Type Checking

Core algorithm with synthesis (⇒) and checking (⇐) modes:

```
// Synthesis rules
Γ ⊢ x ⇒ A                           (Var: lookup in context)
Γ ⊢ (e : A) ⇒ A                     (Anno: annotation synthesizes)
Γ ⊢ f ⇒ (m x : A) → B    Γ ⊢ e ⇐ A
────────────────────────────────────
      Γ ⊢ f(e) ⇒ B[e/x]             (App: application synthesizes)

// Checking rules
   Γ, x :^m A ⊢ e ⇐ B
──────────────────────────
Γ ⊢ λx.e ⇐ (m x : A) → B           (Lam: lambda checks)

Γ ⊢ e ⇒ A    A ≡ B
──────────────────────
    Γ ⊢ e ⇐ B                       (Conv: mode switch)
```

## 3.2 Multiplicity Inference

TERAS-LANG infers multiplicities when unambiguous:

```teras
// Multiplicity inferred as 1 (linear)
fn swap<A, B>(pair: (A, B)) -> (B, A) {
    let (a, b) = pair;  // pair used once
    (b, a)              // a and b used once each
}
// Inferred: swap : (A, B) ->_1 (B, A)

// Multiplicity inferred as 0 (erased)
fn length<T>(vec: Vec<T, n>) -> Nat {
    n  // n only appears in types
}
// Inferred: length : {0 n: Nat} -> Vec<T, n> ->_ω Nat
```

## 3.3 Implicit Arguments

Resolution order:
1. Explicit arguments match directly
2. Implicit arguments unified from usage
3. Instance arguments resolved via type class mechanism
4. Erased arguments need not be provided at runtime

```teras
// Definition with implicits
fn map<A, B, 0 n: Nat>(f: A -> B, xs: Vec<A, n>) -> Vec<B, n>

// Call site — n inferred from xs
let result = map(double, my_vec);  // n inferred
```

---

# PART IV: ERASURE AND PERFORMANCE

## 4.1 Zero-Multiplicity Erasure

Terms with multiplicity 0 are erased entirely:

```teras
// Source
fn replicate<0 n: Nat, T>(value: T) -> Vec<T, n>

// After erasure (conceptual)
fn replicate<T>(value: T) -> Vec<T>
// n completely removed from runtime representation
```

## 4.2 Index Erasure Strategy

| Pattern | Runtime Representation |
|---------|----------------------|
| `Vec<T, n>` where n is 0-mult | Same as `Vec<T>` |
| `{x: T \| P(x)}` | Same as `T` (P erased) |
| `(0 x: A) -> B` | Same as `B` (x erased) |
| `(1 x: A, B)` | Same as `(A, B)` |

## 4.3 Proof Erasure

Proofs are values of erased types:

```teras
// Proof type (erased at runtime)
type SortedProof<xs: Vec<T, n>> = {
    // ... proof structure ...
}

// Function with proof output
fn sort<T: Ord, 0 n: Nat>(xs: Vec<T, n>) 
    -> (ys: Vec<T, n>, 0 proof: SortedProof<ys>) {
    // proof erased at runtime
}
```

---

# PART V: IMPLEMENTATION ROADMAP

## 5.1 Phase Structure

| Phase | Duration | Deliverables |
|-------|----------|-------------|
| **Phase 1** | Weeks 1-6 | Core QTT type checker |
| **Phase 2** | Weeks 7-12 | Dependent pattern matching |
| **Phase 3** | Weeks 13-18 | Universe polymorphism |
| **Phase 4** | Weeks 19-24 | Layered verification integration |
| **Phase 5** | Weeks 25-30 | Erasure and optimization |

## 5.2 Phase 1: Core QTT Type Checker

**Deliverables:**
- [ ] Bidirectional type checking algorithm
- [ ] Multiplicity checking
- [ ] Π and Σ type formation
- [ ] Basic conversion checking
- [ ] Identity types with J eliminator

**Validation:**
- Type checker passes QTT soundness tests
- Performance: <100ms for typical files

## 5.3 Phase 2: Dependent Pattern Matching

**Deliverables:**
- [ ] Indexed inductive type definitions
- [ ] Dependent pattern elaboration
- [ ] Coverage and exhaustiveness checking
- [ ] Dot pattern inference
- [ ] Absurd pattern handling

**Validation:**
- Standard vector operations type check
- Equality patterns work correctly

## 5.4 Phase 3: Universe Polymorphism

**Deliverables:**
- [ ] Universe level inference
- [ ] Cumulative universe hierarchy
- [ ] Level constraints solving
- [ ] Polymorphic definitions

**Validation:**
- Generic definitions work across universe levels
- No unnecessary universe lifting

## 5.5 Phase 4: Layered Verification Integration

**Deliverables:**
- [ ] SMT refinement layer integration (from A-03)
- [ ] Lifting from refinements to dependent proofs
- [ ] Proof term generation
- [ ] Effect system interaction (from A-05)

**Validation:**
- SMT handles common cases automatically
- Complex proofs expressible when needed

## 5.6 Phase 5: Erasure and Optimization

**Deliverables:**
- [ ] Multiplicity-based erasure pass
- [ ] Index specialization
- [ ] Proof erasure
- [ ] Runtime representation optimization

**Validation:**
- Zero overhead for erased terms
- Performance meets D38 mandate

---

# PART VI: RISK ANALYSIS

## 6.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| QTT implementation complexity | Medium | High | Follow Idris 2 closely |
| Universe inference issues | Medium | Medium | Conservative defaults |
| Pattern matching elaboration | Medium | Medium | Incremental implementation |
| SMT/dependent layer interaction | Low | High | Clear separation |

## 6.2 Usability Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Steep learning curve | High | Medium | Good documentation, examples |
| Confusing error messages | High | High | Invest in error quality |
| Over-annotation | Medium | Medium | Good inference |
| Performance surprises | Low | Medium | Clear erasure rules |

---

# PART VII: VALIDATION CRITERIA

## 7.1 Correctness Tests

1. **Type Safety:** Well-typed programs don't get stuck
2. **Substitution Lemma:** Substitution preserves typing
3. **Multiplicity Soundness:** Resource usage matches annotations
4. **Universe Consistency:** No Type : Type

## 7.2 Security Tests

1. Length-indexed vectors prevent buffer overflows
2. Linear types prevent capability leakage
3. Session types ensure protocol compliance
4. Refinements catch bounds violations

## 7.3 Performance Tests

1. Erased indices have zero runtime overhead
2. Type checking completes in reasonable time
3. Generated code matches hand-written C performance

---

# PART VIII: CONCLUSION

## 8.1 Summary of Decisions

| Decision | Specification |
|----------|--------------|
| Foundation | QTT (Quantitative Type Theory) |
| Multiplicities | 0 (erased), 1 (linear), ω (unrestricted) |
| Universes | Cumulative with polymorphism |
| Pattern matching | Dependent with K, elaborated to eliminators |
| Verification | Layered: SMT refinements + dependent proofs |
| Type inference | Bidirectional with multiplicity inference |
| Erasure | Multiplicity-based, proofs erased |

## 8.2 Integration Summary

| Feature | Integration Quality |
|---------|-------------------|
| Linear types (A-04) | Native (QTT unifies) |
| Refinement types (A-03) | Layered (SMT automates) |
| Session types (A-07) | Excellent (linear + dependent) |
| Effect system (A-05) | Good (effect-indexed types) |
| Uniqueness types (A-06) | Compatible (via linearity) |

## 8.3 Expected Outcomes

1. **Security:** Full encoding of security invariants in types
2. **Safety:** Compile-time prevention of vulnerabilities
3. **Performance:** Zero runtime overhead for type information
4. **Verification:** Both automatic and manual proof options
5. **Usability:** Reasonable annotation burden with good inference

---

**Document SHA-256:** To be computed on final version
**Word Count:** ~2,500 words
**Status:** DECISION COMPLETE
**Effective Date:** 2026-01-03

---

## Appendix: Type System Summary

```
TERAS-LANG Dependent Types (QTT Foundation)

Multiplicities:
  m ::= 0 | 1 | ω

Types:
  A, B ::= Type_i                      -- Universe
         | (m x : A) → B               -- Dependent function
         | (m x : A) × B               -- Dependent pair
         | x ≡_A y                     -- Identity type
         | D(args)                     -- Inductive type
         | {x : A | P}                 -- Refinement (layer 1)

Terms:
  e ::= x                              -- Variable
      | λ(x : A). e                    -- Lambda
      | e₁ e₂                          -- Application
      | (e₁, e₂)                       -- Pair
      | e.1 | e.2                      -- Projections
      | refl                           -- Reflexivity
      | J(C, c, p)                     -- J eliminator
      | match e { patterns }           -- Pattern matching
      | (e : A)                        -- Type annotation

Contexts:
  Γ ::= · | Γ, x :^m A                 -- Variables with multiplicities

Judgments:
  Γ ⊢ A : Type_i                       -- Type well-formedness
  Γ ⊢ e : A                            -- Typing
  Γ ⊢ e ⇒ A                            -- Type synthesis
  Γ ⊢ e ⇐ A                            -- Type checking
  Γ ⊢ A ≡ B                            -- Type equality
```
