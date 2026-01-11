# TERAS-LANG Research Comparison A-20: Type System Soundness Proofs

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A20-COMPARISON |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## 1. Approaches Compared

| Approach | Description | Representative Work |
|----------|-------------|---------------------|
| Syntactic (Progress + Preservation) | Induction on typing/reduction | Wright & Felleisen 1994 |
| Step-Indexed Logical Relations | Indexed by computation steps | Ahmed 2006 |
| Kripke Logical Relations | Possible worlds for state | Dreyer et al. 2010 |
| Separation Logic (Iris) | Resource ownership | Jung et al. 2018 |
| Realizability | Programs as proofs | Krivine 2009 |
| Game Semantics | Programs as strategies | Abramsky et al. 1990s |

---

## 2. Feature Comparison Matrix

### 2.1 Language Features Supported

| Feature | Syntactic | Step-Idx | Kripke | Iris | Realizability |
|---------|-----------|----------|--------|------|---------------|
| STLC | ✓ | ✓ | ✓ | ✓ | ✓ |
| Polymorphism | ✓ | ✓ | ✓ | ✓ | ✓ |
| Recursive types | ◐ | ✓ | ✓ | ✓ | ✓ |
| General references | ✗ | ◐ | ✓ | ✓ | ◐ |
| Higher-order state | ✗ | ✗ | ✓ | ✓ | ✗ |
| Concurrency | ✗ | ✗ | ◐ | ✓ | ✗ |
| Linear types | ✓ | ✓ | ✓ | ✓ | ✓ |
| Effects | ◐ | ◐ | ✓ | ✓ | ◐ |
| Dependent types | ✓ | ◐ | ◐ | ◐ | ✓ |

### 2.2 Proof Properties

| Property | Syntactic | Step-Idx | Kripke | Iris | Realizability |
|----------|-----------|----------|--------|------|---------------|
| Compositionality | ◐ | ✓ | ✓ | ✓ | ✓ |
| Extensibility | ◐ | ✓ | ✓ | ✓ | ◐ |
| Unsafe code | ✗ | ◐ | ✓ | ✓ | ✗ |
| Mechanization | ✓ | ✓ | ✓ | ✓ | ◐ |
| Proof complexity | Low | Medium | High | High | High |

### 2.3 Security Properties

| Property | Syntactic | Step-Idx | Kripke | Iris | Realizability |
|----------|-----------|----------|--------|------|---------------|
| Noninterference | ◐ | ✓ | ✓ | ✓ | ✓ |
| Capability safety | ◐ | ✓ | ✓ | ✓ | ◐ |
| Linear resources | ✓ | ✓ | ✓ | ✓ | ✓ |
| Effect containment | ◐ | ◐ | ✓ | ✓ | ◐ |
| Information flow | ◐ | ✓ | ✓ | ✓ | ✓ |

---

## 3. Detailed Approach Analysis

### 3.1 Syntactic Approach (Progress + Preservation)

**Method:**
```
1. Define typing rules: Γ ⊢ e : τ
2. Define operational semantics: e → e'
3. Prove Progress: ∅ ⊢ e : τ ⟹ value(e) ∨ ∃e'. e → e'
4. Prove Preservation: Γ ⊢ e : τ ∧ e → e' ⟹ Γ ⊢ e' : τ
5. Conclude: Well-typed programs don't get stuck
```

**Strengths:**
- Simple and intuitive
- Well-understood proof techniques
- Easy to mechanize
- Good for teaching
- Sufficient for core features

**Weaknesses:**
- Struggles with mutable state
- No support for higher-order store
- Difficult for recursive types (needs coinduction)
- Not compositional
- Hard to extend

**Proof Effort:**
```
For STLC: ~50 lines of Coq
For System F: ~200 lines of Coq
For full ML: ~1000+ lines of Coq
```

### 3.2 Step-Indexed Logical Relations

**Method:**
```
1. Define ⟦τ⟧ₙ = values that behave like τ for n steps
2. Index decreases in recursive positions
3. Prove fundamental theorem: Γ ⊢ e : τ ⟹ ∀n. e ∈ ⟦τ⟧ₙ
4. Derive safety from semantic typing
```

**Key Insight:**
```
⟦τ₁ → τ₂⟧ₙ = { v | ∀k < n. ∀w ∈ ⟦τ₁⟧ₖ. 
                     if v w ↓ₙ₋ₖ v' then v' ∈ ⟦τ₂⟧ₙ₋ₖ }

The step index k is strictly less than n, ensuring well-foundedness.
```

**Strengths:**
- Handles recursive types
- Compositional
- Can express parametricity
- Extensible
- Good for impredicativity

**Weaknesses:**
- Step indices pollute definitions
- Complex for mutable state
- Doesn't handle higher-order store well
- Technical overhead

**Proof Effort:**
```
For recursive types: +100 lines over syntactic
For impredicative polymorphism: +200 lines
```

### 3.3 Kripke Logical Relations

**Method:**
```
1. Define worlds W = (heap typing, invariants)
2. Define ⟦τ⟧ᵂ = values behaving like τ in world W
3. World extension: W' ⊇ W (monotonicity)
4. Prove fundamental theorem with world threading
```

**Key Structures:**
```
World: W = (H, Σ, I) where
    H = heap
    Σ = heap typing (loc → type)
    I = invariants

Monotonicity: If v ∈ ⟦τ⟧ᵂ and W' ⊇ W, then v ∈ ⟦τ⟧ᵂ'
```

**Strengths:**
- Handles mutable state properly
- Supports invariants
- Compositional
- Can model abstract types
- Good for module systems

**Weaknesses:**
- Complex world structure
- Higher-order store still tricky
- Lots of bookkeeping
- Hard to mechanize well

### 3.4 Iris Separation Logic

**Method:**
```
1. Define semantic types as Iris predicates: ⟦τ⟧ : Val → iProp
2. Use separation logic resources for ownership
3. Use invariants for shared state
4. Prove WP (weakest precondition) specifications
5. Derive safety from WP
```

**Key Concepts:**
```
iProp: Propositions over resources
P ∗ Q: Separating conjunction (disjoint resources)
P -∗ Q: Magic wand (consuming P gives Q)
inv(N, P): Invariant named N with content P
WP e {Φ}: Weakest precondition

Semantic typing:
    ⟦τ₁ → τ₂⟧(v) = □(∀w. ⟦τ₁⟧(w) -∗ WP (v w) {⟦τ₂⟧})
```

**Strengths:**
- Handles all features (state, concurrency, etc.)
- Compositional and extensible
- Supports unsafe code verification
- Industrial strength (RustBelt)
- Active development

**Weaknesses:**
- High learning curve
- Complex logic
- Significant mechanization effort
- Requires Coq expertise

**Proof Effort:**
```
Core language: ~2000 lines Coq
With Iris setup: +5000 lines
RustBelt (full Rust): ~100,000 lines
```

### 3.5 Realizability

**Method:**
```
1. Interpret types as sets of "realizers" (programs)
2. A term realizes τ if it behaves according to τ
3. Prove: well-typed terms are realizers
4. Derive safety from realizability
```

**Strengths:**
- Deep connection to logic
- Good for dependent types
- Handles extraction well
- Principled approach

**Weaknesses:**
- Less intuitive
- Complex for effects
- Hard for mutable state
- Less mainstream

---

## 4. Mechanization Comparison

### 4.1 Proof Assistant Support

| Assistant | Syntactic | Step-Idx | Kripke | Iris |
|-----------|-----------|----------|--------|------|
| Coq | Excellent | Excellent | Good | Excellent |
| Agda | Excellent | Good | Fair | N/A |
| Lean 4 | Good | Fair | Fair | Limited |
| Isabelle | Good | Good | Good | Limited |
| F* | Good | Fair | Fair | N/A |

### 4.2 Library Support

| Library | Proof Assistant | Approach | Features |
|---------|-----------------|----------|----------|
| PLFA | Agda | Syntactic | Teaching |
| Software Foundations | Coq | Syntactic | Teaching |
| Iris | Coq | Separation | Full |
| Autosubst | Coq | Any | Binding |
| LNgen | Coq | Any | Locally nameless |
| Needle | Coq | Any | Code generation |

### 4.3 Binding Representation

| Representation | Complexity | Automation | Used By |
|----------------|------------|------------|---------|
| Named | Low | None | Teaching |
| de Bruijn | Medium | Some | Autosubst |
| Locally nameless | Medium | Good | LNgen |
| HOAS | High | Excellent | Twelf |
| Nominal | Medium | Good | Nominal Isabelle |

---

## 5. Security Proof Comparison

### 5.1 Noninterference Proofs

| Approach | Method | Complexity | Compositionality |
|----------|--------|------------|------------------|
| Syntactic | Binary relation on terms | Low | Poor |
| Step-Idx | Binary logical relation | Medium | Good |
| Kripke | World-indexed relation | High | Good |
| Iris | Binary interpretation | High | Excellent |

**Example (Step-Indexed):**
```
⟦τ @ L⟧ₙ = { (v₁, v₂) | L-related for n steps }

L-relation:
    If L = Low: v₁ = v₂
    If L = High: any pair
```

### 5.2 Capability Safety Proofs

| Approach | Method | Unsafe Code | Effort |
|----------|--------|-------------|--------|
| Syntactic | Capability in type | No | Low |
| Semantic | Capability as resource | Yes | High |
| Iris | Capability tokens | Yes | High |

**Iris approach:**
```
⟦Cap c⟧ = cap_token(c)

Operations consume/return tokens:
    read_file : cap_token(FileRead) -∗ WP read {...}
```

### 5.3 Linear Resource Safety

| Approach | Method | Higher-Order | Effort |
|----------|--------|--------------|--------|
| Syntactic | Context splitting | Yes | Medium |
| Iris | Separating conjunction | Yes | Medium |

**Key insight:** Separation logic naturally models linearity.
```
A ⊸ B ≈ A -∗ B  (magic wand = linear implication)
```

---

## 6. Case Studies

### 6.1 RustBelt (Iris)

**Scope:** Full Rust type system including unsafe code

**Approach:**
- Semantic types in Iris
- Lifetime logic for borrows
- Unsafe code via semantic typing

**Effort:** ~100,000 lines of Coq

**Key Results:**
- Mutex, RwLock, Cell, RefCell verified
- Safe API from unsafe implementation
- Foundations for Rust soundness

### 6.2 CakeML (HOL4)

**Scope:** Full ML compiler + runtime

**Approach:**
- Syntactic for type system
- Refinement for compiler

**Effort:** ~500,000 lines of proof

**Key Results:**
- End-to-end verified compiler
- From source to machine code
- Includes garbage collector

### 6.3 CompCert (Coq)

**Scope:** C compiler

**Approach:**
- Operational semantics
- Simulation proofs

**Effort:** ~100,000 lines of Coq

**Key Results:**
- Verified C compiler
- Industrial use
- Missing concurrency

---

## 7. Complexity Analysis

### 7.1 Proof Effort by Feature

| Feature | Syntactic | Step-Idx | Iris |
|---------|-----------|----------|------|
| STLC | 1x | 1.5x | 3x |
| Polymorphism | 2x | 2.5x | 4x |
| Recursive types | 3x | 2x | 4x |
| References | 5x | 4x | 5x |
| Linear types | 2x | 2x | 2x |
| Concurrency | N/A | N/A | 10x |
| Unsafe code | N/A | N/A | 5x |

(Multipliers relative to STLC baseline)

### 7.2 Maintenance Effort

| Change | Syntactic | Step-Idx | Iris |
|--------|-----------|----------|------|
| New type | Low | Low | Medium |
| New primitive | Low | Low | Low |
| New effect | Medium | Medium | Low |
| Structural change | High | Medium | Medium |

### 7.3 Learning Curve

| Approach | Prerequisites | Time to Productivity |
|----------|---------------|----------------------|
| Syntactic | Basic PLT | 1-2 weeks |
| Step-Idx | Logical relations | 1 month |
| Kripke | Model theory | 2 months |
| Iris | Separation logic | 3-6 months |

---

## 8. TERAS-LANG Suitability Analysis

### 8.1 Evaluation Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| Security coverage | 30% | Can prove security properties |
| Feature coverage | 25% | Handles all TERAS features |
| Extensibility | 15% | Easy to add new features |
| Mechanization | 15% | Can be machine-checked |
| Maintenance | 10% | Easy to update proofs |
| Effort | 5% | Development cost |

### 8.2 Weighted Scores

| Approach | Security | Features | Extend | Mech | Maint | Effort | **Total** |
|----------|----------|----------|--------|------|-------|--------|-----------|
| Syntactic | 5 | 4 | 4 | 9 | 5 | 9 | **5.40** |
| Step-Idx | 7 | 6 | 7 | 8 | 6 | 7 | **6.75** |
| Kripke | 8 | 7 | 7 | 6 | 6 | 5 | **6.95** |
| Iris | 10 | 10 | 9 | 9 | 8 | 3 | **9.00** |
| Realizability | 7 | 5 | 5 | 5 | 5 | 4 | **5.55** |

### 8.3 Recommendation

**Primary: Iris-based semantic soundness**

**Rationale:**
1. Handles all TERAS features (state, concurrency, effects)
2. Supports unsafe code verification
3. Proven for similar systems (RustBelt)
4. Excellent security property support
5. Compositional and extensible

**Secondary: Syntactic proofs for rapid prototyping**

---

## 9. Hybrid Strategy for TERAS-LANG

### 9.1 Layered Approach

```
Layer 1: Syntactic Soundness (Core)
├── Basic type safety (progress + preservation)
├── Linear type safety
├── Effect containment
└── Quick development cycle

Layer 2: Semantic Soundness (Full)
├── Iris-based interpretation
├── Handles mutable state
├── Capability safety
├── Noninterference

Layer 3: Security Proofs
├── Information flow control
├── Capability amplification
├── Session fidelity
└── State machine correctness
```

### 9.2 Development Order

| Phase | Approach | Scope | Duration |
|-------|----------|-------|----------|
| 1 | Syntactic | Core TERAS-LANG | 8 weeks |
| 2 | Syntactic | + Linear types | 4 weeks |
| 3 | Syntactic | + Effects | 4 weeks |
| 4 | Iris setup | + Framework | 6 weeks |
| 5 | Iris | + Full semantics | 8 weeks |
| 6 | Iris | + Security proofs | 8 weeks |

### 9.3 Proof Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                 TERAS-LANG Proof Architecture                │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Syntactic Layer:          Semantic Layer:                   │
│  ┌──────────────┐          ┌──────────────┐                 │
│  │ Progress     │          │ Iris Types   │                 │
│  │ Preservation │──────────│ Fundamental  │                 │
│  │ Substitution │          │ Theorem      │                 │
│  └──────────────┘          └──────────────┘                 │
│         │                         │                          │
│         ▼                         ▼                          │
│  ┌──────────────┐          ┌──────────────┐                 │
│  │ Type Safety  │          │ Full Safety  │                 │
│  └──────────────┘          └──────────────┘                 │
│         │                         │                          │
│         └────────────┬────────────┘                          │
│                      ▼                                       │
│              ┌──────────────┐                                │
│              │ Security     │                                │
│              │ Properties   │                                │
│              └──────────────┘                                │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## 10. Summary

### 10.1 Key Differentiators

| Approach | Best For | Avoid For |
|----------|----------|-----------|
| Syntactic | Simple languages, teaching | State, concurrency |
| Step-Idx | Recursive types, parametricity | Higher-order state |
| Kripke | State, modules | High complexity |
| Iris | Everything | Rapid prototyping |
| Realizability | Dependent types, extraction | Practical verification |

### 10.2 TERAS-LANG Direction

TERAS-LANG should adopt a **hybrid approach**:
1. **Syntactic proofs** for rapid development and core properties
2. **Iris-based semantics** for full soundness and security
3. **Incremental development** from simple to complex
4. **Mechanization in Coq** for all proofs

This provides both agility during development and strong guarantees for the final system.

---

*Comparison document for TERAS-LANG research track. Analysis of type system soundness proof approaches.*
