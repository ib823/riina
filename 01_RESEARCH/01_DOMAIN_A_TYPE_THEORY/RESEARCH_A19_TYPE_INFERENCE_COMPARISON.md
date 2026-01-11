# TERAS-LANG Research Comparison A-19: Type Inference Algorithms

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A19-COMPARISON |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## 1. Systems Compared

| System | Approach | Language/Context |
|--------|----------|------------------|
| Algorithm W | Classic Damas-Milner | ML, Haskell 98 |
| Algorithm J | Optimized HM | SML/NJ, OCaml |
| Bidirectional | Check/Synth modes | Agda, GHC |
| OutsideIn(X) | Constraint-based | GHC (modern) |
| Complete and Easy | Bidir + polymorphism | Research, Idris |
| Local Type Inference | Minimal annotations | Scala, Kotlin |
| Flow | Union types + inference | JavaScript |

---

## 2. Feature Comparison Matrix

### 2.1 Core Capabilities

| Feature | W | J | Bidir | OutsideIn | C&E | Local | Flow |
|---------|---|---|-------|-----------|-----|-------|------|
| Let-polymorphism | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ◐ |
| Higher-rank | ✗ | ✗ | ✓ | ✓ | ✓ | ◐ | ✗ |
| GADTs | ✗ | ✗ | ✓ | ✓ | ✓ | ✗ | ✗ |
| Type families | ✗ | ✗ | ◐ | ✓ | ◐ | ✗ | ✗ |
| Type classes | ext | ext | ext | ✓ | ext | ext | ✗ |
| Subtyping | ✗ | ✗ | ✓ | ◐ | ✓ | ✓ | ✓ |
| Refinement | ✗ | ✗ | ext | ext | ✓ | ✗ | ✗ |

### 2.2 Inference Quality

| Property | W | J | Bidir | OutsideIn | C&E | Local | Flow |
|----------|---|---|-------|-----------|-----|-------|------|
| Principal types | ✓ | ✓ | ◐ | ✓ | ✓ | ◐ | ✗ |
| Complete | ✓ | ✓ | ✓ | ✓ | ✓ | ◐ | ✗ |
| Sound | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ◐ |
| Decidable | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Predictable | ◐ | ◐ | ✓ | ◐ | ✓ | ✓ | ◐ |

### 2.3 Error Quality

| Property | W | J | Bidir | OutsideIn | C&E | Local | Flow |
|----------|---|---|-------|-----------|-----|-------|------|
| Localized errors | ◐ | ◐ | ✓ | ◐ | ✓ | ✓ | ◐ |
| Clear messages | ◐ | ◐ | ✓ | ◐ | ✓ | ✓ | ◐ |
| Suggestions | ✗ | ✗ | ◐ | ✓ | ◐ | ✓ | ✓ |
| Type holes | ✗ | ✗ | ✓ | ✓ | ✓ | ◐ | ✗ |

---

## 3. Detailed Algorithm Analysis

### 3.1 Algorithm W (Damas-Milner)

**Approach:** Recursive descent with substitution composition

**Pseudocode:**
```
W(Γ, e) returns (Substitution, Type)

W(Γ, x) = (∅, inst(Γ(x)))
W(Γ, λx.e) = let (S, τ) = W(Γ ∪ {x:α}, e) in (S, Sα → τ)
W(Γ, e₁ e₂) = let (S₁, τ₁) = W(Γ, e₁)
              let (S₂, τ₂) = W(S₁Γ, e₂)
              let S₃ = unify(S₂τ₁, τ₂ → α)
              in (S₃∘S₂∘S₁, S₃α)
W(Γ, let x = e₁ in e₂) = let (S₁, τ₁) = W(Γ, e₁)
                          let σ = gen(S₁Γ, τ₁)
                          let (S₂, τ₂) = W(S₁Γ ∪ {x:σ}, e₂)
                          in (S₂∘S₁, τ₂)
```

**Strengths:**
- Simple to implement
- Well-understood theory
- Principal types guaranteed
- Complete for HM

**Weaknesses:**
- Quadratic complexity (substitution composition)
- Poor error messages
- No subtyping
- Limited feature support

### 3.2 Algorithm J (Optimized HM)

**Approach:** Mutable references instead of substitution

**Key Optimization:**
```
Type variable: Ref<Option<Type>>
- None: unsolved
- Some(τ): solved to τ

Union-find for equivalence:
- Near-constant time unification
- Path compression
- Rank-based union
```

**Strengths:**
- Near-linear complexity
- Same coverage as W
- More efficient for large programs
- Standard in production compilers

**Weaknesses:**
- Mutable state complicates reasoning
- Same feature limitations as W
- Error messages still difficult
- Backtracking harder

### 3.3 Bidirectional Type Checking

**Approach:** Two judgment forms (check vs synthesize)

**Core Judgments:**
```
Γ ⊢ e ⇒ A  (synthesize A from e)
Γ ⊢ e ⇐ A  (check e against A)
```

**Key Rules:**
```
Var:    (x : A) ∈ Γ
        ───────────
        Γ ⊢ x ⇒ A

App:    Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
        ────────────────────────────────
        Γ ⊢ e₁ e₂ ⇒ B

Lam:    Γ, x : A ⊢ e ⇐ B
        ───────────────────────
        Γ ⊢ λx. e ⇐ A → B

Anno:   Γ ⊢ e ⇐ A
        ─────────────────
        Γ ⊢ (e : A) ⇒ A

Sub:    Γ ⊢ e ⇒ A    A <: B
        ──────────────────────
        Γ ⊢ e ⇐ B
```

**Strengths:**
- Predictable type flow
- Localized errors
- Natural for subtyping
- Higher-rank types
- Modular rules

**Weaknesses:**
- Needs annotations at mode switches
- Less inference than HM in some cases
- Design choices for subsumption

### 3.4 OutsideIn(X)

**Approach:** Implication constraints with modular solving

**Constraint Language:**
```
C ::= τ₁ ~ τ₂           (equality)
    | C₁ ∧ C₂           (conjunction)
    | ∃α. C             (existential)
    | Q ⊃ C             (implication: given Q, wanted C)
    | D τ               (type class: instance of D at τ)
```

**Solving Strategy:**
```
1. Generate constraints for whole program
2. Simplify: flatten conjunctions, reduce type families
3. Solve: unify equalities, resolve instances
4. Check: verify implications satisfied
5. Generalize: create polymorphic types
```

**Strengths:**
- Handles type families
- Type classes native
- GADTs supported
- Modular (separate compilation)
- Touchable variables prevent escape

**Weaknesses:**
- Complex implementation
- Can produce confusing errors
- Defaulting rules tricky
- Ambiguous types need resolution

### 3.5 Complete and Easy Bidirectional

**Approach:** Bidirectional + existential variables + subtyping

**Context Extension:**
```
Γ ::= · | Γ, x : A | Γ, α | Γ, α̂ | Γ, α̂ = τ | Γ, ▸α̂

α̂ = existential variable (to be solved)
▸α̂ = marker (for scoping)
```

**Key Innovation:**
```
∀-Application:
    Γ ⊢ e ⇒ ∀α. A
    ─────────────────────────────
    Γ, α̂ ⊢ e ⇒ [α ↦ α̂]A

Existential solving:
    During checking, α̂ may be solved to concrete type
    Solution must respect context ordering
```

**Strengths:**
- Higher-rank polymorphism
- Subtyping integration
- Complete for predicative fragment
- Elegant metatheory
- Good error properties

**Weaknesses:**
- Context threading complex
- Requires careful implementation
- Impredicativity limited

### 3.6 Local Type Inference

**Approach:** Minimal annotations, local type propagation

**Principles:**
```
1. Propagate types from annotations downward
2. Synthesize types from leaves upward
3. Meet in the middle at mode switches
4. Require annotations at polymorphic recursion
```

**Example (Scala):**
```scala
val f: Int => Int = x => x + 1  // x inferred as Int
val g = (x: Int) => x + 1       // Return type inferred
val xs = List(1, 2, 3)          // Element type inferred
```

**Strengths:**
- Minimal annotations
- Good for OO languages
- Practical for real codebases
- Familiar to developers

**Weaknesses:**
- Not complete
- May fail to infer
- Different from HM behavior
- Less predictable

### 3.7 Flow Type Inference

**Approach:** Union/intersection types, widening

**Key Ideas:**
```
1. Types can be unions: string | number
2. Narrowing via control flow: if (typeof x === "string") ...
3. Widening to prevent infinite types
4. Soundness sacrificed for practicality
```

**Strengths:**
- Handles JavaScript idioms
- Gradual typing
- Practical for dynamic code
- Good tooling integration

**Weaknesses:**
- Unsound
- Complex union reasoning
- Performance issues
- Unpredictable inference

---

## 4. Performance Comparison

### 4.1 Time Complexity

| Algorithm | Best Case | Worst Case | Typical |
|-----------|-----------|------------|---------|
| W | O(n) | O(n²) | O(n log n) |
| J | O(n α(n)) | O(n α(n)) | O(n α(n)) |
| Bidir | O(n) | O(n²) | O(n) |
| OutsideIn | O(n) | O(n²) | O(n log n) |
| C&E | O(n) | O(n²) | O(n) |
| Local | O(n) | O(n²) | O(n) |
| Flow | O(n) | O(n³) | O(n²) |

### 4.2 Space Complexity

| Algorithm | Space | Notes |
|-----------|-------|-------|
| W | O(n) | Substitution chains |
| J | O(n) | Union-find structure |
| Bidir | O(n) | Context stack |
| OutsideIn | O(n²) | Constraint store |
| C&E | O(n) | Context with markers |
| Local | O(n) | Propagation info |
| Flow | O(n²) | Type graph |

### 4.3 Practical Performance

| Algorithm | Small Programs | Large Programs | Incremental |
|-----------|----------------|----------------|-------------|
| W | Fast | Slow | Poor |
| J | Fast | Fast | Poor |
| Bidir | Fast | Fast | Good |
| OutsideIn | Medium | Medium | Good |
| C&E | Fast | Fast | Good |
| Local | Fast | Medium | Good |
| Flow | Slow | Slow | Medium |

---

## 5. Error Message Quality

### 5.1 Error Localization

| Algorithm | Localization | Why |
|-----------|--------------|-----|
| W | Poor | Constraint far from source |
| J | Poor | Same as W |
| Bidir | Excellent | Error at mode switch |
| OutsideIn | Medium | Constraint solving order |
| C&E | Excellent | Scoped existentials |
| Local | Good | Local propagation |
| Flow | Medium | Union widening hides source |

### 5.2 Example Error Messages

**Algorithm W/J:**
```
Error: Cannot unify Int with String
  In the application: f x
  
(May be far from actual error)
```

**Bidirectional:**
```
Error: Type mismatch in argument
  Expected: Int
  Got: String
  
  In: f "hello"
       ^^^^^^^
```

**OutsideIn:**
```
Error: Could not deduce (Show a) arising from use of 'show'
  Possible fix: add (Show a) to the context of the type signature
  
  In: show x
```

**Complete and Easy:**
```
Error: Cannot check λx. x against Int → String
  The function returns: x
  But expected: String
  
  In: (λx. x) : Int → String
          ^
```

---

## 6. Security Feature Support

### 6.1 Information Flow

| Algorithm | IFC Support | Approach |
|-----------|-------------|----------|
| W | ✗ | N/A |
| J | ✗ | N/A |
| Bidir | ✓ | Check labels in subtyping |
| OutsideIn | ◐ | Constraints on labels |
| C&E | ✓ | Label in subtyping lattice |
| Local | ◐ | Propagate labels |
| Flow | ◐ | Union of labels |

### 6.2 Capability Inference

| Algorithm | Capability Support | Approach |
|-----------|-------------------|----------|
| W | ext | Add effect variables |
| J | ext | Add effect variables |
| Bidir | ✓ | Track in context |
| OutsideIn | ✓ | Constraints on effects |
| C&E | ✓ | Effects in checking |
| Local | ◐ | Local propagation |
| Flow | ✗ | N/A |

### 6.3 Linear Type Support

| Algorithm | Linear Support | Approach |
|-----------|---------------|----------|
| W | ✗ | Context not split |
| J | ✗ | Context not split |
| Bidir | ✓ | Split context in rules |
| OutsideIn | ◐ | Multiplicity constraints |
| C&E | ✓ | Usage in context |
| Local | ◐ | Usage tracking |
| Flow | ✗ | N/A |

---

## 7. Comparative Code Examples

### 7.1 Simple Polymorphic Function

**All algorithms infer:** `id : ∀α. α → α`
```
let id = λx. x
```

### 7.2 Higher-Rank Type

**Need annotation for higher-rank:**
```
// Only bidir, OutsideIn, C&E handle this
let apply : (∀α. α → α) → Int → Int
let apply = λf. λx. f x
```

| Algorithm | Infers? | Notes |
|-----------|---------|-------|
| W | ✗ | No higher-rank |
| J | ✗ | No higher-rank |
| Bidir | ✓ | Checks against annotation |
| OutsideIn | ✓ | Instantiates at use |
| C&E | ✓ | Scoped existentials |

### 7.3 GADT Pattern Match

```haskell
data Expr a where
    LitInt :: Int → Expr Int
    Add :: Expr Int → Expr Int → Expr Int

eval :: Expr a → a
eval (LitInt n) = n      -- needs: a ~ Int
eval (Add x y) = eval x + eval y
```

| Algorithm | Handles? | Notes |
|-----------|----------|-------|
| W | ✗ | No refinement |
| J | ✗ | No refinement |
| Bidir | ✓ | Pattern refines type |
| OutsideIn | ✓ | Local assumptions |
| C&E | ✓ | Pattern matching |

### 7.4 Effect Inference

```
let f = λx. do
    print(x)
    return (x + 1)
// Should infer: Int -[IO]→ Int
```

| Algorithm | Infers? | Notes |
|-----------|---------|-------|
| W | ext | With effect extension |
| J | ext | With effect extension |
| Bidir | ✓ | Effects in judgment |
| OutsideIn | ✓ | Effect constraints |
| C&E | ✓ | Effect rows |

---

## 8. TERAS-LANG Suitability Analysis

### 8.1 Evaluation Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| Security support | 25% | IFC, caps, linear |
| Error quality | 20% | Localization, clarity |
| Feature coverage | 20% | HKT, GADTs, effects |
| Performance | 15% | Compile time |
| Predictability | 10% | Developer experience |
| Implementation | 10% | Complexity |

### 8.2 Weighted Scores

| Algorithm | Security | Errors | Features | Perf | Predict | Impl | **Total** |
|-----------|----------|--------|----------|------|---------|------|-----------|
| W | 3 | 4 | 3 | 7 | 5 | 9 | **4.35** |
| J | 3 | 4 | 3 | 9 | 5 | 8 | **4.55** |
| Bidir | 9 | 9 | 8 | 8 | 9 | 6 | **8.35** |
| OutsideIn | 7 | 6 | 9 | 7 | 6 | 4 | **6.85** |
| C&E | 9 | 9 | 8 | 8 | 9 | 5 | **8.20** |
| Local | 5 | 7 | 5 | 8 | 8 | 7 | **6.30** |
| Flow | 2 | 5 | 4 | 4 | 4 | 6 | **3.85** |

### 8.3 Recommendation

**Primary: Bidirectional type checking** with constraint solving for advanced features.

**Rationale:**
1. Best error localization for security failures
2. Natural fit for substructural types
3. Handles higher-rank and GADTs
4. Predictable for developers
5. Extensible to security features

---

## 9. Hybrid Approach for TERAS-LANG

### 9.1 Proposed Architecture

```
TERAS-LANG Inference = Bidirectional + Constraints
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Core:
├── Bidirectional checking for all terms
├── Mode switch at annotations and applications
└── Subtyping in subsumption rule

Extensions:
├── Constraint generation for type classes
├── Effect row inference with constraints
├── Capability set collection
├── Linear usage tracking
└── Security label inference

Solving:
├── Unification with union-find (from J)
├── Constraint simplification
├── Implication checking (from OutsideIn)
└── Defaulting for ambiguous types
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 9.2 Security-Specific Extensions

```
Security Inference Components:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Label Inference:
    - Generate label variables for unknown labels
    - Collect flow constraints from operations
    - Solve: minimal consistent labeling
    - Report: declassification requirements

Capability Inference:
    - Track required capabilities per function
    - Collect from primitive operations
    - Report: manifest of required capabilities
    - Verify: capability subset constraints

Linear Tracking:
    - Count usage of each variable
    - Split contexts in application
    - Report: unused or overused linear variables
    - Integrate: with capability consumption
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 10. Summary

### 10.1 Key Differentiators

| Approach | Best For | Avoid For |
|----------|----------|-----------|
| W/J | Simple HM languages | Advanced features |
| Bidir | Modern typed langs | Pure inference |
| OutsideIn | GHC-like languages | Simple languages |
| C&E | Research/new langs | Production (complexity) |
| Local | OO languages | Functional langs |
| Flow | Dynamic languages | Static guarantees |

### 10.2 TERAS-LANG Direction

TERAS-LANG should adopt **bidirectional type checking** as the foundation, extended with:
- Constraint solving for type classes and families
- Usage tracking for linear types
- Label inference for information flow
- Capability collection for permissions
- Excellent error messages with blame tracking

This combination provides the best balance of expressiveness, security support, error quality, and implementation tractability.

---

*Comparison document for TERAS-LANG research track. Analysis of type inference algorithms for security-focused language design.*
