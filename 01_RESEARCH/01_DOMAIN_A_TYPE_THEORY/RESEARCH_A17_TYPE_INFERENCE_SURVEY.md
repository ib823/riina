# RESEARCH_A17_TYPE_INFERENCE_SURVEY.md

## TERAS Research Track — Domain A: Type Theory
### Session A-17: Type Inference Algorithms

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research
**Predecessor:** A-16 (Sized Types)
**Successor:** A-18 (Subtyping Systems)

---

# PART I: FOUNDATIONS OF TYPE INFERENCE

## 1.1 Historical Development

```
Type Inference Timeline:

1969: Hindley - Principal type schemes
1978: Milner - Algorithm W for ML
1982: Damas-Milner - Formal soundness proof
1988: Cardelli - Type:Type and polymorphism
1998: Pierce & Turner - Local type inference
2000: Dunfield & Pfenning - Bidirectional typing
2013: Dunfield & Krishnaswami - Complete bidirectional
2020: Modern extensions - GADTs, dependent types, effects
```

## 1.2 Hindley-Milner Type System

### 1.2.1 Core System

```
Hindley-Milner (HM):

Types:
  τ ::= α | τ → τ | T τ₁...τₙ     (monotypes)
  σ ::= τ | ∀α.σ                   (polytypes)

Typing Rules:
  Γ(x) = σ
  ─────────────  (Var)
  Γ ⊢ x : σ

  Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
  ─────────────────────────────────  (App)
  Γ ⊢ e₁ e₂ : τ₂

  Γ, x : τ₁ ⊢ e : τ₂
  ─────────────────────  (Abs)
  Γ ⊢ λx.e : τ₁ → τ₂

  Γ ⊢ e₁ : σ    Γ, x : σ ⊢ e₂ : τ
  ─────────────────────────────────  (Let)
  Γ ⊢ let x = e₁ in e₂ : τ

Key Property: Principal types exist
```

### 1.2.2 Algorithm W

```
Algorithm W (Milner 1978):

W(Γ, e) → (S, τ)   -- substitution and type

W(Γ, x) = (id, inst(Γ(x)))

W(Γ, λx.e) =
  let α = fresh() in
  let (S, τ) = W(Γ[x↦α], e) in
  (S, S(α) → τ)

W(Γ, e₁ e₂) =
  let (S₁, τ₁) = W(Γ, e₁) in
  let (S₂, τ₂) = W(S₁(Γ), e₂) in
  let α = fresh() in
  let S₃ = unify(S₂(τ₁), τ₂ → α) in
  (S₃ ∘ S₂ ∘ S₁, S₃(α))

W(Γ, let x = e₁ in e₂) =
  let (S₁, τ₁) = W(Γ, e₁) in
  let σ = gen(S₁(Γ), τ₁) in
  let (S₂, τ₂) = W(S₁(Γ)[x↦σ], e₂) in
  (S₂ ∘ S₁, τ₂)

Complexity: O(n) typical, exponential worst case
```

### 1.2.3 Unification

```
Robinson's Unification:

unify(τ₁, τ₂) → S (most general unifier)

unify(α, τ) = 
  if α ∈ FV(τ) then fail (occurs check)
  else [α ↦ τ]

unify(τ₁ → τ₂, τ₃ → τ₄) =
  let S₁ = unify(τ₁, τ₃) in
  let S₂ = unify(S₁(τ₂), S₁(τ₄)) in
  S₂ ∘ S₁

unify(T τ₁...τₙ, T σ₁...σₙ) =
  unify(τ₁, σ₁) ∘ ... ∘ unify(τₙ, σₙ)

unify(τ, τ) = id

otherwise → fail
```

## 1.3 Bidirectional Type Checking

### 1.3.1 Core Approach

```
Bidirectional Typing:

Two Modes:
  Γ ⊢ e ⇐ A   -- check e against A
  Γ ⊢ e ⇒ A   -- synthesize type A for e

Mode Switching:
  Γ ⊢ e ⇒ A
  ───────────────  (Sub)
  Γ ⊢ e ⇐ A

Key Rules:
  Γ ⊢ e ⇐ A    Γ ⊢ f ⇐ B
  ────────────────────────  (check pair)
  Γ ⊢ (e, f) ⇐ A × B

  Γ(x) = A
  ───────────  (synth var)
  Γ ⊢ x ⇒ A

  Γ ⊢ f ⇒ A → B    Γ ⊢ e ⇐ A
  ─────────────────────────────  (synth app)
  Γ ⊢ f e ⇒ B
```

### 1.3.2 Benefits

```
Bidirectional Benefits:

1. Annotation Reduction
   - Types flow from context
   - Local type hints suffice
   
2. Better Error Messages
   - Know expected type
   - Mismatch is localized
   
3. Extensibility
   - Easy to add new constructs
   - Separate check/synth per form
   
4. Handles Advanced Features
   - Dependent types
   - GADTs
   - Subtyping
```

## 1.4 Local Type Inference

### 1.4.1 Pierce-Turner Approach

```
Local Type Inference (1998):

Key Insight:
  - Propagate types locally, not globally
  - Use bidirectional + local constraint solving
  - Avoid global unification when possible

Features:
  - Type arguments inferred at call sites
  - Annotations on lambda parameters
  - No global let-polymorphism inference
  
Example:
  map : ∀α β. (α → β) → List α → List β
  
  map (λx. x + 1) [1, 2, 3]
  -- α = Int, β = Int inferred locally
```

---

# PART II: ADVANCED INFERENCE SYSTEMS

## 2.1 OutsideIn (GHC)

### 2.1.1 Constraint-Based Inference

```
OutsideIn(X) (Vytiniotis et al.):

Approach:
  1. Generate constraints
  2. Solve constraints outside-in
  3. Propagate solutions
  
Constraint Language:
  Q ::= τ₁ ~ τ₂        -- equality
      | C τ₁...τₙ      -- type class
      | Q ∧ Q          -- conjunction
      | ∃α.Q           -- existential
      | Q ⊃ Q          -- implication

Algorithm:
  infer(e) = (τ, Q)     -- type and constraints
  solve(Q) = S          -- substitution
  final = S(τ)
```

### 2.1.2 GADTs and Type Families

```
GADT Inference:

data Expr a where
  Lit  : Int → Expr Int
  Plus : Expr Int → Expr Int → Expr Int
  Eq   : Expr Int → Expr Int → Expr Bool

eval : Expr a → a
eval (Lit n) = n        -- a ~ Int
eval (Plus e1 e2) = eval e1 + eval e2
eval (Eq e1 e2) = eval e1 == eval e2

Challenge:
  - Constructor carries type equality
  - Must solve with local assumptions
  
OutsideIn Solution:
  - Generate implications
  - Solve inside-out for GADTs
  - Maintain wanted/given separation
```

## 2.2 Liquid Type Inference

### 2.2.1 Refinement Inference

```
Liquid Types Inference:

Types:
  {ν : B | p}   -- refined base type

Inference Approach:
  1. Generate templates with unknown predicates
  2. Collect constraints from subtyping
  3. Solve via predicate abstraction
  
Qualifier Language:
  Q = {ν ≥ 0, ν ≤ len xs, ...}
  
Algorithm:
  - Infer qualifiers from program syntax
  - Template: {ν : B | κ} where κ is qualifier variable
  - Constraint: {ν : B | p₁} <: {ν : B | p₂} iff ∀ν. p₁ ⟹ p₂
  - Solve via abstract interpretation
```

## 2.3 Effect Inference

### 2.3.1 Row-Based Effect Inference

```
Effect Inference (Leijen 2014):

Types:
  τ ::= ... | τ → τ ! ε
  ε ::= ⟨ℓ₁ | ... | ℓₙ | ρ⟩   -- effect row

Inference:
  - Infer effect variables
  - Collect effect constraints
  - Solve via row unification
  
Example:
  f : A → B ! ⟨Read | ρ⟩
  g : B → C ! ⟨Write | σ⟩
  
  h x = g (f x)
  -- h : A → C ! ⟨Read | Write | ρ ∪ σ⟩
```

---

# PART III: INFERENCE FOR TERAS FEATURES

## 3.1 Linear Type Inference

```
Linear Type Inference:

Challenge:
  - Track usage of linear variables
  - Infer linearity annotations
  
Approaches:
  1. Explicit linearity (no inference)
     lin x : A, aff y : B
     
  2. Usage inference
     Infer lin/aff from how used
     
  3. Multiplicity polymorphism
     ∀m. A →^m B
     Infer m from context

TERAS Approach: Explicit linearity for clarity
```

## 3.2 Effect Type Inference

```
TERAS Effect Inference:

Effect Rows:
  fn f() -> A ! {E₁ | ρ}
  -- ρ is effect variable
  
Inference:
  - Collect effect constraints
  - Solve via row unification
  - Principal effects exist

Example:
  fn compose(f: A -> B ! E₁, g: B -> C ! E₂) -> (A -> C ! E₁ ∪ E₂)
  -- Effect union inferred
```

## 3.3 Capability Inference

```
Capability Inference:

Question:
  Can we infer capability requirements?
  
Approach:
  - Capabilities usually explicit (POLA)
  - But can infer from usage
  
Example:
  fn process(file: ???) -> String {
      file.read()  // requires cap<File, Read>
  }
  -- Infer: file : &cap<File, Read>
  
TERAS: Explicit for security, inference for convenience
```

## 3.4 Size Inference

```
Size Inference:

From A-16:
  - Partial size inference possible
  - Constraint-based approach
  
Example:
  length : List^? A → Nat
  length [] = 0
  length (x :: xs) = 1 + length xs
  
  Constraints:
    xs : List^i A where i < ?
    
  Solution:
    length : ∀i. List^i A → Nat
```

---

# PART IV: IMPLEMENTATION CONSIDERATIONS

## 4.1 Algorithm Choice

### 4.1.1 Comparison

| Algorithm | Completeness | Performance | Features |
|-----------|--------------|-------------|----------|
| Algorithm W | Complete (HM) | O(n) typical | Basic polymorphism |
| Algorithm M | Complete (HM) | O(n) typical | Better errors |
| Bidirectional | Local | O(n) | Dependent types, GADTs |
| OutsideIn | Modular | O(n) typical | Type families, GADTs |
| Liquid | Complete (LH) | SMT calls | Refinements |

### 4.1.2 For TERAS-LANG

```
TERAS Inference Strategy:

Core: Bidirectional type checking
  - Local inference
  - Good error messages
  - Handles dependent types

Enhancement: Constraint solving
  - For complex polymorphism
  - Effect row inference
  - Size constraint solving

Refinement: SMT integration
  - For refinement types
  - Verification conditions
```

## 4.2 Error Messages

```
Error Message Quality:

Key Factors:
  1. Location accuracy
  2. Expected vs actual types
  3. Suggestion of fixes
  4. Context preservation

Bidirectional Advantage:
  "Expected type A but got B"
  -- Clear mismatch at point of use

Techniques:
  - Blame tracking
  - Type error slicing
  - Counter-example generation
```

---

# PART V: SUMMARY

## 5.1 Key Systems Surveyed

| System | Core Approach | Key Innovation |
|--------|---------------|----------------|
| Algorithm W | Unification | Principal types |
| Bidirectional | Mode switching | Local inference |
| OutsideIn | Constraint | GADT support |
| Liquid | Abstraction | Refinement inference |

## 5.2 Design Considerations

```
TERAS-LANG Inference Questions:

1. Base Algorithm
   - Bidirectional (recommended)
   - Constraint-based enhancement
   
2. Polymorphism Inference
   - Let-polymorphism (yes)
   - Higher-rank (explicit annotation)
   
3. Feature Inference
   - Effects: Row inference
   - Sizes: Constraint-based
   - Capabilities: Mostly explicit
   
4. Error Quality
   - Priority: Clear, actionable messages
   - Technique: Bidirectional + blame tracking
```

---

**END OF SURVEY DOCUMENT**

**Next Document:** RESEARCH_A17_TYPE_INFERENCE_COMPARISON.md
