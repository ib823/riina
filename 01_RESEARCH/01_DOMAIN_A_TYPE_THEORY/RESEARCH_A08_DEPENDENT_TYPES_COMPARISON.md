# RESEARCH_A08_DEPENDENT_TYPES_COMPARISON.md

## TERAS-LANG Research Track — Session A-08
## Comparative Analysis: Dependent Type Implementations

**Version:** 1.0.0
**Date:** 2026-01-03
**Status:** COMPLETE
**Depends On:** RESEARCH_A08_DEPENDENT_TYPES_SURVEY.md

---

# PART I: COMPARISON FRAMEWORK

## 1.1 Evaluation Criteria

For TERAS-LANG, we evaluate dependent type implementations against:

| Criterion | Weight | Description |
|-----------|--------|-------------|
| **Security expressiveness** | 25% | Ability to encode security properties |
| **Linear type integration** | 20% | Compatibility with resource tracking |
| **Type inference quality** | 15% | Annotation burden and inference power |
| **Runtime efficiency** | 15% | Code generation and performance |
| **Proof automation** | 10% | Available tactics and decision procedures |
| **Ecosystem maturity** | 10% | Libraries, tools, community |
| **Learning curve** | 5% | Complexity for developers |

## 1.2 Implementations Compared

1. **Agda** — Pure type-theoretic foundation
2. **Idris 2** — QTT with linear types
3. **Lean 4** — Efficient prover with metaprogramming
4. **F*** — Dependently-typed ML with effects
5. **Coq/Rocq** — Established proof assistant

---

# PART II: FEATURE COMPARISON

## 2.1 Type System Foundation

| Feature | Agda | Idris 2 | Lean 4 | F* | Coq |
|---------|------|---------|--------|----|-----|
| **Base theory** | MLTT | QTT | CIC | λ→ + refinements | CIC |
| **Π-types** | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Σ-types** | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Identity types** | ✓ | ✓ | ✓ | Limited | ✓ |
| **Inductive families** | ✓ | ✓ | ✓ | Limited | ✓ |
| **Coinductive types** | ✓ (Sized) | ✓ | ✓ | ✗ | ✓ |
| **Universe polymorphism** | ✓ | ✓ | ✓ | Limited | ✓ |
| **Cumulative universes** | ✗ | ✓ | ✗ | ✓ | ✓ |

### Analysis

**Agda** has the most complete implementation of dependent types as described in Martin-Löf's theory, including cubical extensions for HoTT.

**Idris 2** uniquely provides linear types at the foundation level through QTT, making it the only language where linearity is intrinsic rather than added.

**Lean 4** provides practical dependent types with excellent performance characteristics, though less type-theoretically pure than Agda.

**F*** bridges the gap between dependent and refinement types, with SMT-backed automation for decidable properties.

**Coq** has the longest history and most mature ecosystem, but its separation of Prop and Set can complicate programming.

## 2.2 Linear/Resource Types Integration

| Feature | Agda | Idris 2 | Lean 4 | F* | Coq |
|---------|------|---------|--------|----|-----|
| **Built-in linear types** | ✗ | ✓ (QTT) | ✗ | ✗ | ✗ |
| **Linearity tracking** | External | Native | External | Monadic | External |
| **Multiplicity** | N/A | 0, 1, ω | N/A | N/A | N/A |
| **Erasure control** | Limited | ✓ (0) | Manual | ✓ | ✓ |
| **Session types** | Library | Native | Library | Library | Library |

### Analysis

**Idris 2's QTT is the clear winner** for linear type integration:

```idris
-- Native multiplicity annotation
lin : (1 x : a) -> (1 y : b) -> (a, b)
lin x y = (x, y)

-- Erased indices (0 multiplicity)
replicate : (0 n : Nat) -> a -> Vect n a
```

Other languages require external mechanisms:
- Agda uses libraries or external tools
- Lean 4 requires encoding linearity in types
- F* uses monadic effects for state
- Coq uses libraries like Iris

## 2.3 Pattern Matching Capabilities

| Feature | Agda | Idris 2 | Lean 4 | F* | Coq |
|---------|------|---------|--------|----|-----|
| **Dependent patterns** | ✓ | ✓ | ✓ | Limited | ✓ |
| **With-abstraction** | ✓ | ✓ | ✗ | ✗ | ✓ |
| **Dot patterns** | ✓ | ✓ | ✓ | ✗ | ✓ |
| **Absurd patterns** | ✓ | ✓ | ✓ | ✗ | ✓ |
| **Without K** | ✓ | ✗ | ✗ | N/A | ✓ |
| **Coverage checking** | ✓ | ✓ | ✓ | ✓ | ✓ |

### Analysis

**Agda** provides the most sophisticated pattern matching with full support for HoTT-compatible patterns (without K).

**Idris 2** has excellent practical pattern matching, closely following Agda but assuming K.

**Lean 4** has good pattern matching but lacks with-abstraction, compensated by tactics.

**F*** prioritizes SMT automation over complex pattern matching.

## 2.4 Type Inference and Annotations

| Feature | Agda | Idris 2 | Lean 4 | F* | Coq |
|---------|------|---------|--------|----|-----|
| **Implicit arguments** | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Instance arguments** | ✓ | ✓ | ✓ | ✗ | ✓ |
| **Bidirectional checking** | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Inference quality** | Good | Good | Very good | Excellent | Good |
| **Annotation burden** | Medium | Medium | Low | Low | High |
| **Higher-order unification** | Heuristic | Heuristic | Heuristic | SMT | Heuristic |

### Analysis

**F*** has the best automatic inference due to SMT integration for refinements:

```fstar
// Type inferred including refinements
let incr x = x + 1  // Inferred: x:int -> y:int{y = x + 1}
```

**Lean 4** has very good inference with low annotation requirements due to elaborate unification heuristics and type class resolution.

**Idris 2** includes multiplicity inference, reducing the burden of linearity annotations.

## 2.5 Runtime Performance

| Feature | Agda | Idris 2 | Lean 4 | F* | Coq |
|---------|------|---------|--------|----|-----|
| **Compilation target** | Haskell | Chez Scheme/C | C | OCaml/C | OCaml |
| **Erasure** | Limited | Excellent | Good | Good | Limited |
| **Index erasure** | Manual | Automatic (0) | Manual | Automatic | Manual |
| **Runtime overhead** | High | Medium | Low | Medium | High |
| **Memory management** | GC | GC | RefCount | GC | GC |

### Analysis

**Lean 4** has the best runtime performance:
- Reference counting enables "functional but in-place" programming
- Produces efficient C code
- Resurrection hypothesis optimization

```lean
-- In-place update when reference count is 1
def mapTree (f : α → β) : Tree α → Tree β
  | .leaf x => .leaf (f x)
  | .node l r => .node (mapTree f l) (mapTree f r)
```

**Idris 2** has good performance with automatic erasure of 0-multiplicity terms:

```idris
-- n is erased at runtime
length : {0 n : Nat} -> Vect n a -> Nat
```

## 2.6 Proof Automation

| Feature | Agda | Idris 2 | Lean 4 | F* | Coq |
|---------|------|---------|--------|----|-----|
| **Tactic language** | Reflection | Elaborator | Lean DSL | N/A | Ltac2 |
| **SMT integration** | ✗ | ✗ | ✗ | ✓ (Z3) | Plugin |
| **Decision procedures** | Limited | Limited | Grind | SMT | Omega/Ring |
| **Automation quality** | Low | Low | Medium | High | High |
| **Custom tactics** | ✓ | ✓ | ✓ | ✗ | ✓ |

### Analysis

**F*** has the best automation for decidable properties through Z3 integration:

```fstar
// Automatically verified by SMT
let max (x y : int) : z:int{z >= x /\ z >= y} =
  if x > y then x else y
```

**Lean 4** has good automation through `grind` and other tactics:

```lean
theorem and_swap (p q : Prop) : p ∧ q → q ∧ p := by grind
```

**Coq** has powerful tactics (Ltac2) but requires more manual intervention.

---

# PART III: SECURITY-SPECIFIC COMPARISON

## 3.1 Security Property Encoding

| Property | Best Language | Why |
|----------|--------------|-----|
| **Buffer bounds** | All equal | Standard indexed types |
| **Protocol states** | Idris 2 | Linear state transitions |
| **Information flow** | F* | Monadic effects + SMT |
| **Crypto verification** | F* | Refinement types |
| **Session types** | Idris 2 | QTT native support |
| **Capability safety** | Idris 2 | Linear capabilities |

## 3.2 Security Libraries/Frameworks

| Language | Security Libraries |
|----------|-------------------|
| **Agda** | Type-safe crypto proofs, protocol models |
| **Idris 2** | Linear session types, resource protocols |
| **Lean 4** | Mathlib for number theory |
| **F*** | Project Everest (verified TLS, crypto) |
| **Coq** | Iris, VST, CompCert |

### Winner: F* for Security

F* with Project Everest provides the most mature security verification:
- **HACL*** — Verified cryptographic library
- **EverCrypt** — Cryptographic provider
- **miTLS** — Verified TLS implementation
- **Vale** — Verified assembly

## 3.3 Protocol Verification Examples

### Idris 2 — Session Type Protocol

```idris
data AuthProtocol : Type where
  MkAuth : Send Credentials ->
           Recv (Either AuthToken Failure) ->
           AuthProtocol

runAuth : (1 chan : Channel AuthProtocol) -> 
          Credentials -> IO (Either AuthToken Failure)
```

### F* — Refinement-Based Protocol

```fstar
type state =
  | Init
  | Sent of bytes
  | Complete of result

val step : s:state -> msg:bytes{valid_transition s msg} -> state
```

### Lean 4 — Verified State Machine

```lean
inductive TLSState
  | clientHello | serverHello | keyExchange | encrypted

def validTransition : TLSState → TLSState → Prop
  | .clientHello, .serverHello => True
  | .serverHello, .keyExchange => True
  | .keyExchange, .encrypted => True
  | _, _ => False
```

---

# PART IV: INTEGRATION ANALYSIS

## 4.1 Integration with TERAS-LANG Features

### With Linear Types (A-04)

| Language | Integration Quality | Approach |
|----------|-------------------|----------|
| **Idris 2** | Excellent | Native QTT |
| **Agda** | Poor | External/manual |
| **Lean 4** | Poor | No native support |
| **F*** | Medium | Effect tracking |

### With Refinement Types (A-03)

| Language | Integration Quality | Approach |
|----------|-------------------|----------|
| **F*** | Excellent | Native + SMT |
| **Lean 4** | Good | Decidable tactics |
| **Idris 2** | Medium | Manual proofs |
| **Agda** | Medium | Manual proofs |

### With Session Types (A-07)

| Language | Integration Quality | Approach |
|----------|-------------------|----------|
| **Idris 2** | Excellent | Linear channels |
| **F*** | Good | Monadic encoding |
| **Others** | Medium | Library-based |

## 4.2 Ecosystem Compatibility

| Factor | Agda | Idris 2 | Lean 4 | F* |
|--------|------|---------|--------|----|
| **Rust interop** | ✗ | Limited | Good | Good |
| **C interop** | Via Haskell | ✓ | ✓ | ✓ |
| **IDE support** | Emacs | VSCode | VSCode | VSCode |
| **Build tools** | Stack | Pack | Lake | FStarMake |

---

# PART V: SUITABILITY ANALYSIS FOR TERAS-LANG

## 5.1 Scoring Matrix

| Criterion (Weight) | Agda | Idris 2 | Lean 4 | F* |
|--------------------|------|---------|--------|----|
| Security expressiveness (25%) | 8 | 9 | 8 | 9 |
| Linear type integration (20%) | 3 | 10 | 3 | 5 |
| Type inference quality (15%) | 7 | 7 | 8 | 9 |
| Runtime efficiency (15%) | 5 | 7 | 9 | 6 |
| Proof automation (10%) | 5 | 5 | 7 | 9 |
| Ecosystem maturity (10%) | 7 | 5 | 8 | 7 |
| Learning curve (5%) | 5 | 6 | 7 | 6 |
| **Weighted Total** | **6.15** | **7.50** | **6.95** | **7.40** |

## 5.2 Recommendations by Use Case

### For TERAS-LANG Core Type System

**Recommendation: Idris 2 (QTT) approach**

Rationale:
- Native linear types essential for TERAS security model
- QTT cleanly unifies dependent and linear types
- Erasure control (0 multiplicity) enables efficient indices
- Session types integrate naturally

### For Verification Automation

**Recommendation: F* approach for decidable properties**

Rationale:
- SMT automation reduces manual proof burden
- Refinement types handle common security properties
- Battle-tested in Project Everest

### For Runtime Efficiency

**Recommendation: Lean 4 techniques**

Rationale:
- Reference counting with reuse analysis
- Efficient C code generation
- Functional-but-in-place paradigm

## 5.3 Hybrid Approach for TERAS-LANG

Combine best elements:

```
TERAS-LANG Dependent Types =
    QTT Foundation (Idris 2)
  + SMT Automation (F*)
  + Efficient Codegen (Lean 4 techniques)
  + Type-theoretic purity (Agda principles)
```

### Layered Architecture

```
┌─────────────────────────────────────────────┐
│         Surface Language (ergonomic)        │
├─────────────────────────────────────────────┤
│     Refinement Layer (SMT-decidable)        │
├─────────────────────────────────────────────┤
│   QTT Core (dependent + linear unified)     │
├─────────────────────────────────────────────┤
│     Verification Backend (proof terms)      │
└─────────────────────────────────────────────┘
```

---

# PART VI: TRADEOFF ANALYSIS

## 6.1 Expressiveness vs Decidability

| Approach | Expressiveness | Decidability | Inference |
|----------|---------------|--------------|-----------|
| Full dependent | Maximum | Undecidable (type inference) | Manual |
| Refinement only | Limited | Decidable | Automatic |
| **Hybrid** | High | Mixed | Layered |

## 6.2 Performance vs Safety

| Approach | Safety Guarantees | Runtime Cost |
|----------|------------------|--------------|
| Indices retained | Full | High overhead |
| Indices erased | Full (compile-time) | Zero |
| **QTT (0 mult)** | Full | Controlled |

## 6.3 Complexity vs Power

| Factor | Simple Deps | Full Deps | QTT |
|--------|-------------|-----------|-----|
| Learning curve | Low | High | Medium-High |
| Security power | Medium | Maximum | Maximum |
| Implementation | Easy | Hard | Hard |

---

# PART VII: SUMMARY

## 7.1 Key Findings

1. **Idris 2's QTT** provides the best foundation for combining dependent and linear types
2. **F*'s SMT integration** provides superior automation for decidable properties
3. **Lean 4's code generation** achieves best runtime performance
4. **Agda's type theory** provides the purest theoretical foundation

## 7.2 TERAS-LANG Design Guidance

| Aspect | Recommendation | Source |
|--------|---------------|--------|
| Core calculus | QTT with multiplicities | Idris 2 |
| Universe handling | Cumulative | Coq/Idris |
| Pattern matching | Dependent, with K | Idris 2/Agda |
| Automation | SMT for refinements | F* |
| Codegen | Reference counting + reuse | Lean 4 |
| Erasure | Multiplicity-based | Idris 2 |

## 7.3 Next Steps

This comparison informs the decision document (RESEARCH_A08_DEPENDENT_TYPES_DECISION.md), which will specify:
1. Concrete type system design
2. Integration with existing TERAS-LANG features
3. Implementation roadmap

---

**Document SHA-256:** To be computed on final version
**Word Count:** ~2,000 words
**Status:** COMPLETE — Ready for decision document
