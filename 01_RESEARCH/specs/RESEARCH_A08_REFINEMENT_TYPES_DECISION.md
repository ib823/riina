# RESEARCH_A08_REFINEMENT_TYPES_DECISION.md
## TERAS-LANG Research Track A - Session 08
## Architecture Decision: Refinement Types for TERAS-LANG

**Document Version**: 1.0.0
**Created**: 2026-01-03
**Decision Status**: ADOPTED
**Decision Type**: Type System Foundation

---

## 1. DECISION SUMMARY

### 1.1 Decision Statement

**ADOPT** Liquid Types with SMT-based verification as the refinement type foundation for TERAS-LANG, combining predicate abstraction inference with effect-aware refinements and integration with the linear type system from A-04.

### 1.2 Key Design Choices

1. **Predicate subtypes**: `{v: T | P(v)}` syntax for refinement types
2. **Liquid inference**: Automatic refinement inference via predicate abstraction
3. **SMT backend**: Z3 for verification condition checking
4. **Effect integration**: Refinements track effects (combined with A-05)
5. **Linearity integration**: Refinements on linear resources (combined with A-04)
6. **Measures**: User-defined measures for algebraic types
7. **Decidability**: Restrict to SMT-decidable fragments

---

## 2. DECISION CONTEXT

### 2.1 Problem Statement

TERAS-LANG requires compile-time verification of security properties including:
- Memory safety (array bounds, buffer overflow prevention)
- Resource management (proper linear resource usage)
- Functional correctness (cryptographic primitives match specifications)
- Protocol compliance (session type adherence with value constraints)

Standard type systems cannot express these properties. Full dependent types offer expressiveness but sacrifice decidability and automation. A balanced approach is needed.

### 2.2 Requirements

| Requirement | Priority | Description |
|-------------|----------|-------------|
| REQ-R01 | Critical | Express array bounds and size constraints |
| REQ-R02 | Critical | Decidable type checking |
| REQ-R03 | Critical | Integration with linear types |
| REQ-R04 | High | Automatic refinement inference |
| REQ-R05 | High | SMT-based verification |
| REQ-R06 | High | Support for cryptographic specifications |
| REQ-R07 | Medium | User-defined measures |
| REQ-R08 | Medium | Refinement polymorphism |

### 2.3 Options Considered

1. **Full Dependent Types** (Agda/Idris style)
2. **Liquid Types** (Liquid Haskell style)
3. **Index Refinements** (DML style)
4. **Hybrid Refinement/Dependent** (F* style)
5. **Ownership + Refinements** (Flux style)

---

## 3. DECISION RATIONALE

### 3.1 Why Liquid Types Base

**Primary Reasons**:

1. **Decidable Inference**: 
   - Predicate abstraction over finite qualifier set
   - Fixed-point computation guarantees termination
   - No manual annotation for most cases

2. **SMT Integration**:
   - Z3 provides efficient, automatic verification
   - Well-understood decidable theories
   - Battle-tested in production systems

3. **Minimal Annotation Burden**:
   - Liquid Haskell: ~10-20% annotation overhead
   - Flux: ~10-15% annotation overhead
   - Far less than full dependent types

4. **Proven Track Record**:
   - HACL* verified cryptographic library
   - Tock OS isolation verification
   - 10,000+ lines verified in Liquid Haskell

### 3.2 Key Design Decisions

**Decision R-01: Predicate Subtype Syntax**
```teras
// Refinement type syntax
type T = {v: BaseType | Predicate(v)}

// Examples
type Nat = {v: Int | v >= 0}
type NonZero = {v: Int | v != 0}
type BoundedInt<N: Int> = {v: Int | 0 <= v && v < N}
```

**Decision R-02: Dependent Function Types**
```teras
// Dependent function with refinement
fn div(x: Int, y: NonZero) -> Int

// Full dependent signature
fn safe_index<T, N: Int>(arr: Array<T, N>, i: {v: Int | 0 <= v && v < N}) -> T
```

**Decision R-03: Measure Definitions**
```teras
// User-defined measure
measure len<T> : List<T> -> Int {
    len([]) = 0
    len(x :: xs) = 1 + len(xs)
}

// Refined algebraic types
type NonEmptyList<T> = {v: List<T> | len(v) > 0}
```

**Decision R-04: Liquid Type Variables**
```teras
// Compiler infers refinements via liquid variables
fn append<T>(xs: List<T>, ys: List<T>) -> List<T>
// Inferred: {v: List<T> | len(v) = len(xs) + len(ys)}
```

### 3.3 Integration Decisions

**Decision R-05: Linear Type Integration (with A-04)**
```teras
// Refinements on linear types
type SecretKey = lin {k: [u8; 32] | valid_key(k)}

// Linear resource with size constraint
fn encrypt(key: lin SecretKey, msg: {m: Bytes | len(m) <= MAX_MSG}) 
    -> lin {c: Bytes | len(c) = len(msg) + OVERHEAD}
```

**Decision R-06: Effect Integration (with A-05)**
```teras
// Effect-aware refinements
fn read_bounded(fd: FileDesc) -> IO<{data: Bytes | len(data) <= BUFFER_SIZE}>

// Stateful refinement
fn push<T, N: Int>(vec: &mut Vec<T, N>, elem: T) 
    -> ensures &mut Vec<T, N+1>
```

**Decision R-07: Session Type Integration (with A-07)**
```teras
// Refinements on session messages
session AuthProtocol {
    !{credentials: Credentials | valid_format(credentials)}
    ?{token: Token | expires_after(token, now() + TIMEOUT)}
}
```

---

## 4. TYPE SYSTEM SPECIFICATION

### 4.1 Refinement Type Grammar

```
Ï„ ::= B                           -- Base type
    | {v: B | Ï†}                  -- Refined base
    | (x: Ï„â‚) â†’ Ï„â‚‚                -- Dependent function
    | âˆ€Î±. Ï„                       -- Type polymorphism
    | âˆ€p: Ï„ â†’ Bool. Ï„             -- Refinement polymorphism (abstract refinement)
    | Ï„â‚ Ã— Ï„â‚‚                     -- Product
    | Ï„â‚ + Ï„â‚‚                     -- Sum
    | Î¼Î±. Ï„                       -- Recursive
    | lin Ï„                       -- Linear refinement
    | uniq Ï„                      -- Unique refinement

Ï† ::= true | false                -- Constants
    | v                           -- Value variable
    | c                           -- Constant
    | f(Ï†â‚, ..., Ï†â‚™)              -- Measure application
    | Ï†â‚ op Ï†â‚‚                    -- Binary operation
    | Â¬Ï† | Ï†â‚ âˆ§ Ï†â‚‚ | Ï†â‚ âˆ¨ Ï†â‚‚     -- Logical connectives
    | âˆ€x:Ï„. Ï† | âˆƒx:Ï„. Ï†           -- Quantification (restricted)
```

### 4.2 Subtyping Rules

**Sub-Base**:
```
Î“ âŠ¢ {v:B | P} <: {v:B | Q}
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Valid(Î“, v:B, P âŸ¹ Q)   [SMT]
```

**Sub-Fun**:
```
Î“ âŠ¢ Ï„â‚‚ <: Ï„â‚    Î“, x:Ï„â‚‚ âŠ¢ Ïƒâ‚ <: Ïƒâ‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ (x:Ï„â‚) â†’ Ïƒâ‚ <: (x:Ï„â‚‚) â†’ Ïƒâ‚‚
```

**Sub-Lin**:
```
Î“ âŠ¢ Ï„â‚ <: Ï„â‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ lin Ï„â‚ <: lin Ï„â‚‚
```

### 4.3 Typing Rules

**T-Var**:
```
(x : Ï„) âˆˆ Î“
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ x : Ï„
```

**T-App**:
```
Î“ âŠ¢ eâ‚ : (x:Ï„â‚) â†’ Ï„â‚‚    Î“ âŠ¢ eâ‚‚ : Ï„â‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ eâ‚ eâ‚‚ : Ï„â‚‚[eâ‚‚/x]
```

**T-Let**:
```
Î“ âŠ¢ eâ‚ : Ï„â‚    Î“, x:Ï„â‚ âŠ¢ eâ‚‚ : Ï„â‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ let x = eâ‚ in eâ‚‚ : Ï„â‚‚
```

**T-Sub**:
```
Î“ âŠ¢ e : Ï„â‚    Î“ âŠ¢ Ï„â‚ <: Ï„â‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : Ï„â‚‚
```

---

## 5. SMT INTEGRATION

### 5.1 Verification Condition Generation

```
VC(Î“ âŠ¢ {v:B | P} <: {v:B | Q}) = 
    âˆ€v:B. (encode(Î“) âˆ§ P) âŸ¹ Q
```

### 5.2 SMT Theories Used

| Theory | Usage |
|--------|-------|
| QF_LIA | Linear integer arithmetic |
| QF_LRA | Linear real arithmetic |
| QF_UF | Uninterpreted functions (measures) |
| QF_A | Arrays |
| QF_BV | Bitvectors (for crypto) |

### 5.3 Measure Encoding

```teras
measure len<T> : List<T> -> Int {
    len([]) = 0
    len(x :: xs) = 1 + len(xs)
}
```

Encoded as axioms:
```smt
(declare-fun len (List) Int)
(assert (= (len nil) 0))
(assert (forall ((x T) (xs List)) 
    (= (len (cons x xs)) (+ 1 (len xs)))))
```

Or via constructor refinements (more efficient):
```
[]  : {v: List<T> | len(v) = 0}
(::) : x:T -> xs:List<T> -> {v: List<T> | len(v) = 1 + len(xs)}
```

---

## 6. LIQUID INFERENCE ALGORITHM

### 6.1 Algorithm Overview

```
LIQUID-INFER(P: Program, Q: Qualifiers):
    1. shapes â† HM-INFER(P)           // Standard type inference
    2. templates â† TEMPLATE(shapes)    // Add liquid variables
    3. constraints â† CONSTRAIN(P, templates)  // Generate constraints
    4. solution â† SOLVE(constraints, Q)       // Fixed-point
    5. return SUBSTITUTE(templates, solution)
```

### 6.2 Template Generation

For each type, replace refinements with liquid variables:
```
template({v:Int | P}) = {v:Int | Îº}    where Îº is fresh
template((x:Ï„â‚) â†’ Ï„â‚‚) = (x:template(Ï„â‚)) â†’ template(Ï„â‚‚)
```

### 6.3 Constraint Solving

Fixed-point iteration:
```
SOLVE(C, Q):
    for each Îº: solution[Îº] â† âˆ§Q     // Start with all qualifiers
    repeat:
        for each (Îº <: Ï†) âˆˆ C:
            solution[Îº] â† solution[Îº] âˆ§ WeakestPrecondition(Ï†, Q)
    until fixed-point
    return solution
```

---

## 7. TERAS PRODUCT INTEGRATION

### 7.1 MENARA (Mobile Security)

```teras
// Biometric data with privacy constraints
type BiometricTemplate = {
    data: lin {b: [u8; 512] | valid_template(b)},
    expiry: {t: Timestamp | t > now()}
}

// Secure comparison
fn verify_biometric(
    template: lin BiometricTemplate,
    sample: {s: [u8; 512] | fresh(s)}
) -> Bool
```

### 7.2 GAPURA (WAF)

```teras
// Request validation with size bounds
type ValidRequest = {
    method: {m: HttpMethod | m in ALLOWED_METHODS},
    path: {p: String | len(p) <= MAX_PATH && safe_path(p)},
    body: {b: Bytes | len(b) <= MAX_BODY}
}

fn process_request(req: ValidRequest) -> Response
```

### 7.3 ZIRAH (EDR)

```teras
// Memory region with bounds
type MemRegion = {
    base: {a: Addr | aligned(a, PAGE_SIZE)},
    size: {s: Size | s > 0 && s <= MAX_REGION}
}

fn scan_memory(region: MemRegion) -> ScanResult
```

### 7.4 BENTENG (eKYC)

```teras
// Document verification with format constraints
type VerifiedDocument = {
    doc_type: DocumentType,
    data: {d: Bytes | valid_format(d, doc_type)},
    signature: {s: Signature | valid_sig(s, d)}
}
```

### 7.5 SANDI (Digital Signatures)

```teras
// Cryptographic key with validity constraints
type SigningKey = lin {
    key: {k: [u8; 32] | valid_key(k)},
    algorithm: SignAlgorithm,
    created: Timestamp,
    expires: {t: Timestamp | t > created}
}

fn sign(key: lin &SigningKey, msg: {m: Bytes | len(m) <= MAX_MSG}) 
    -> {s: Signature | valid_sig(s, msg)}
```

---

## 8. IMPLEMENTATION ROADMAP

### 8.1 Phase 1: Core Refinements (Weeks 1-8)

| Task | Duration | Dependencies |
|------|----------|--------------|
| Refinement type AST | 1 week | A-04 complete |
| Subtyping with SMT | 2 weeks | Z3 integration |
| Basic inference | 2 weeks | Subtyping |
| Measure support | 2 weeks | Basic inference |
| Testing & validation | 1 week | All above |

### 8.2 Phase 2: Advanced Features (Weeks 9-16)

| Task | Duration | Dependencies |
|------|----------|--------------|
| Liquid inference | 3 weeks | Phase 1 |
| Abstract refinements | 2 weeks | Liquid inference |
| Effect integration | 2 weeks | A-05 complete |
| Linear integration | 1 week | A-04 integration |

### 8.3 Phase 3: Optimization (Weeks 17-24)

| Task | Duration | Dependencies |
|------|----------|--------------|
| Incremental SMT | 2 weeks | Phase 2 |
| Caching strategies | 2 weeks | Incremental SMT |
| Error messages | 2 weeks | Full system |
| Documentation | 2 weeks | All above |

---

## 9. RISKS AND MITIGATIONS

### 9.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| SMT performance | Medium | High | Caching, incremental solving |
| Inference incompleteness | Medium | Medium | Manual annotations fallback |
| Complex measure axioms | Low | Medium | Restrict measure forms |
| Integration complexity | Medium | Medium | Phased integration |

### 9.2 Mitigations

**SMT Performance**:
- Cache verification results
- Use incremental SMT mode
- Profile and optimize hot paths

**Inference Incompleteness**:
- Allow explicit refinement annotations
- Provide good error messages for inference failures
- Document qualifier design patterns

---

## 10. SUCCESS METRICS

### 10.1 Verification Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| VC checking time | < 100ms average | Benchmark suite |
| Inference success rate | > 90% | Test programs |
| Annotation overhead | < 20% | LOC comparison |
| False positives | < 5% | Manual review |

### 10.2 Security Metrics

| Metric | Target | Measurement |
|--------|--------|-------------|
| Bounds check elimination | > 95% | Static analysis |
| Crypto spec compliance | 100% | Formal verification |
| Memory safety proof | Complete | Type soundness |

---

## 11. DECISION RECORD

### 11.1 Decision

**ADOPTED**: Liquid Types with SMT-based verification for TERAS-LANG refinement types.

### 11.2 Rationale Summary

1. Decidable type checking via predicate abstraction
2. Automatic inference minimizes annotation burden
3. SMT integration provides practical verification
4. Proven in production systems (HACL*, Flux)
5. Natural integration with linear types
6. Aligned with TERAS security verification goals

### 11.3 Alignment Score

**Overall: 9.0/10**

| Criterion | Score | Notes |
|-----------|-------|-------|
| TERAS alignment | 9/10 | Direct support for security properties |
| Technical feasibility | 9/10 | Well-understood implementation path |
| Innovation potential | 8/10 | Novel integration with linear types |
| Community alignment | 9/10 | Growing refinement types ecosystem |
| Maintenance burden | 8/10 | SMT solver dependency |

---

## 12. REFERENCES

- Rondon, Kawaguchi, Jhala (2008). "Liquid Types". PLDI.
- Vazou et al. (2014). "LiquidHaskell: Experience with Refinement Types". Haskell.
- Lehmann et al. (2023). "Flux: Liquid Types for Rust". PLDI.
- ZinzindohouÃ© et al. (2017). "HACL*: A Verified Modern Cryptographic Library". CCS.
- Jhala & Vazou (2021). "Refinement Types: A Tutorial". Foundations and Trends.

---

*Document generated as part of TERAS-LANG Research Track A*
*Session A-08: Refinement Types Architecture Decision*
