# TERAS-LANG Research Survey A-19: Type Inference Algorithms

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A19-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

## Executive Summary

Type inference algorithms automatically deduce types for expressions without requiring explicit annotations. This survey covers Hindley-Milner (Algorithm W), bidirectional type checking, constraint-based inference, unification algorithms, and inference for advanced type features. For TERAS-LANG, robust type inference reduces annotation burden while maintaining security guarantees through complete type information.

---

## 1. Foundations of Type Inference

### 1.1 What is Type Inference?

Type inference automatically determines the types of expressions:

```
Without inference (explicit):
    let x: Int = 5
    let f: (Int) -> Int = |y: Int| -> Int { y + 1 }
    let result: Int = f(x)

With inference:
    let x = 5              // inferred: Int
    let f = |y| y + 1      // inferred: (Int) -> Int
    let result = f(x)      // inferred: Int
```

### 1.2 Key Concepts

**Principal Types**: The most general type for an expression.
```
f = |x| x
// Principal type: ∀α. α → α (not Int → Int or Bool → Bool)
```

**Type Schemes**: Types with universal quantification.
```
σ ::= τ | ∀α. σ      (type schemes)
τ ::= α | τ → τ | ...  (monotypes)
```

**Substitution**: Mapping from type variables to types.
```
[α ↦ Int](α → α) = Int → Int
```

### 1.3 Historical Development

```
Timeline of Type Inference:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1958    │ Curry-Howard correspondence foundation
1969    │ Hindley: principal type theorem for combinatory logic
1978    │ Milner: Algorithm W for ML
1982    │ Damas-Milner: formal soundness and completeness
1985    │ Practical implementations in SML
1989    │ Rémy: rows and records
1993    │ Jones: qualified types (type classes)
1997    │ Odersky-Läufer: colored local type inference
2000    │ Pierce-Turner: local type inference
2004    │ Dunfield-Pfenning: bidirectional typing
2010    │ OutsideIn(X): modular constraint solving
2013    │ Complete and Easy bidirectional typing
2020+   │ Modern refinements and extensions
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. Hindley-Milner Type System

### 2.1 The HM Type System

The Hindley-Milner (HM) type system is the foundation of ML-family languages:

**Syntax:**
```
Types:       τ ::= α | τ₁ → τ₂ | T τ₁ ... τₙ
Schemes:     σ ::= τ | ∀α. σ
Expressions: e ::= x | λx. e | e₁ e₂ | let x = e₁ in e₂
```

**Key Properties:**
- Decidable type inference
- Principal types exist
- Let-polymorphism (generalize at let-bindings)

### 2.2 Typing Rules

```
Variable:
    x : σ ∈ Γ    τ = inst(σ)
    ─────────────────────────
           Γ ⊢ x : τ

Application:
    Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
    ─────────────────────────────────
           Γ ⊢ e₁ e₂ : τ₂

Abstraction:
    Γ, x : τ₁ ⊢ e : τ₂
    ──────────────────────
    Γ ⊢ λx. e : τ₁ → τ₂

Let:
    Γ ⊢ e₁ : τ₁    Γ, x : gen(Γ, τ₁) ⊢ e₂ : τ₂
    ────────────────────────────────────────────
              Γ ⊢ let x = e₁ in e₂ : τ₂
```

**Generalization:**
```
gen(Γ, τ) = ∀ᾱ. τ  where ᾱ = FV(τ) \ FV(Γ)
```

**Instantiation:**
```
inst(∀α₁...αₙ. τ) = [α₁ ↦ β₁, ..., αₙ ↦ βₙ]τ  (fresh βᵢ)
```

### 2.3 Algorithm W

Damas and Milner's Algorithm W computes principal types:

```
W(Γ, x) = 
    let σ = Γ(x) in
    let τ = inst(σ) in
    (∅, τ)

W(Γ, λx. e) =
    let α = fresh() in
    let (S, τ) = W(Γ ∪ {x : α}, e) in
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
    let (S₂, τ₂) = W(S₁(Γ) ∪ {x : σ}, e₂) in
    (S₂ ∘ S₁, τ₂)
```

### 2.4 Algorithm J (More Efficient)

Algorithm J uses explicit substitution application less:

```
J(Γ, e) performs inference using:
- Mutable unification variables
- Union-find for equivalence classes
- Levels for generalization
```

**Key optimization**: Instead of applying substitutions eagerly, use indirection through unification variables.

---

## 3. Unification Algorithms

### 3.1 First-Order Unification

Robinson's unification finds most general unifier (MGU):

```
unify(τ, τ) = ∅

unify(α, τ) = 
    if α ∈ FV(τ) then fail("occurs check")
    else [α ↦ τ]

unify(τ, α) = unify(α, τ)

unify(τ₁ → τ₂, τ₃ → τ₄) =
    let S₁ = unify(τ₁, τ₃) in
    let S₂ = unify(S₁(τ₂), S₁(τ₄)) in
    S₂ ∘ S₁

unify(T τ₁...τₙ, T τ'₁...τ'ₙ) =
    unify(τ₁, τ'₁) ∘ ... ∘ unify(τₙ, τ'ₙ)

unify(_, _) = fail("type mismatch")
```

### 3.2 Union-Find Unification

More efficient using union-find data structure:

```rust
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
    data: Vec<TypeNode>,
}

enum TypeNode {
    Var,
    Arrow(usize, usize),  // indices into union-find
    Con(String, Vec<usize>),
}

fn unify(uf: &mut UnionFind, a: usize, b: usize) -> Result<()> {
    let a = uf.find(a);
    let b = uf.find(b);
    if a == b { return Ok(()); }
    
    match (uf.data[a].clone(), uf.data[b].clone()) {
        (TypeNode::Var, _) => uf.union(a, b),
        (_, TypeNode::Var) => uf.union(b, a),
        (TypeNode::Arrow(a1, a2), TypeNode::Arrow(b1, b2)) => {
            uf.union(a, b);
            unify(uf, a1, b1)?;
            unify(uf, a2, b2)
        }
        (TypeNode::Con(n1, args1), TypeNode::Con(n2, args2)) 
            if n1 == n2 && args1.len() == args2.len() => {
            uf.union(a, b);
            for (x, y) in args1.iter().zip(args2.iter()) {
                unify(uf, *x, *y)?;
            }
            Ok(())
        }
        _ => Err("type mismatch")
    }
}
```

### 3.3 Higher-Order Unification

For dependent types and type families, need higher-order unification:

```
Flex-flex: ?F x₁...xₙ ≐ ?G y₁...yₘ
    - Multiple solutions possible
    - Generate constraint (delay)

Flex-rigid: ?F x₁...xₙ ≐ c t₁...tₘ
    - Imitation: F = λx₁...xₙ. c (H₁ x₁...xₙ) ... (Hₘ x₁...xₙ)
    - Projection: F = λx₁...xₙ. xᵢ (H₁ x₁...xₙ) ... (Hₖ x₁...xₙ)
```

**Decidability**: Higher-order unification is undecidable in general, but practical patterns are decidable.

---

## 4. Bidirectional Type Checking

### 4.1 Core Idea

Split type inference into two modes:
- **Checking** (⇐): Check expression against known type
- **Synthesis** (⇒): Infer type from expression

```
Γ ⊢ e ⇐ A   (check e against A)
Γ ⊢ e ⇒ A   (synthesize A from e)
```

### 4.2 Basic Bidirectional Rules

```
Synthesis (⇒):
─────────────
    Variable:     (x : A) ∈ Γ
                  ───────────────
                  Γ ⊢ x ⇒ A

    Annotated:    Γ ⊢ e ⇐ A
                  ─────────────────
                  Γ ⊢ (e : A) ⇒ A

    Application:  Γ ⊢ e₁ ⇒ A → B    Γ ⊢ e₂ ⇐ A
                  ──────────────────────────────
                  Γ ⊢ e₁ e₂ ⇒ B

Checking (⇐):
─────────────
    Lambda:       Γ, x : A ⊢ e ⇐ B
                  ──────────────────────
                  Γ ⊢ λx. e ⇐ A → B

    Subsumption:  Γ ⊢ e ⇒ A    A <: B
                  ────────────────────
                  Γ ⊢ e ⇐ B
```

### 4.3 Complete and Easy Bidirectional Typing

Dunfield and Krishnaswami's system handles polymorphism:

```
Types:    A, B ::= 1 | α | A → B | ∀α. A | ∃α. A
Context:  Γ    ::= · | Γ, x : A | Γ, α | Γ, α̂ | Γ, α̂ = τ

Key rules:

∀-Introduction (check):
    Γ, α ⊢ e ⇐ A
    ────────────────────
    Γ ⊢ e ⇐ ∀α. A

∀-Elimination (apply):
    Γ ⊢ e ⇒ ∀α. A    Γ ⊢ τ
    ─────────────────────────────
    Γ ⊢ e ⇒ [α ↦ τ]A

Existential variables (α̂):
    - Created when instantiating polymorphic types
    - Solved by unification during checking
    - Context grows from left to right
    - Solved vars can refer only to earlier vars
```

### 4.4 Benefits of Bidirectional Typing

| Property | Advantage |
|----------|-----------|
| Predictability | Type flows in predictable direction |
| Locality | Errors localized to expression |
| Modularity | Rules compose independently |
| Annotations | Minimal annotations at mode switches |
| Subtyping | Natural integration with subtyping |
| Polymorphism | Higher-rank types without complexity |

---

## 5. Constraint-Based Inference

### 5.1 Constraint Generation

Separate inference into constraint generation and solving:

```
Phase 1: Generate constraints
    infer(Γ, e) = (τ, C)
    
Phase 2: Solve constraints
    solve(C) = S (substitution)
    
Phase 3: Apply solution
    type(e) = S(τ)
```

### 5.2 Constraint Language

```
Constraints:
    C ::= τ₁ = τ₂           (equality)
        | τ₁ ≤ τ₂           (subtyping)
        | C₁ ∧ C₂           (conjunction)
        | ∃α. C             (existential)
        | ∀α. C             (universal)
        | τ ∈ K             (kind constraint)
        | instance(σ, τ)    (instantiation)
```

### 5.3 OutsideIn(X)

GHC's constraint-based type inference:

```
Key ideas:
1. Implication constraints: Q ⊃ C
   - Q is "given" constraints
   - C is "wanted" constraints
   
2. Touchable variables
   - Only certain variables can be unified
   - Prevents escape of local constraints

3. Modular solving
   - Solve constraints in separate scopes
   - Combine solutions carefully
```

**Example:**
```haskell
f :: a -> a -> Bool
f x y = x == y  -- Requires Eq a

-- Generates: ∀a. (Eq a) ⊃ (a ~ a, a ~ a, Bool ~ Bool)
```

### 5.4 Constraint Solving Strategies

| Strategy | Description | Use Case |
|----------|-------------|----------|
| Unification | Solve equalities | Basic types |
| Simplification | Reduce constraints | Before solving |
| Defaulting | Choose concrete types | Ambiguous cases |
| Improvement | Derive new equalities | Type families |
| Superclass | Add implied constraints | Type classes |

---

## 6. Inference for Advanced Features

### 6.1 Type Classes and Qualified Types

```
Qualified types: ρ ::= τ | π ⇒ ρ  (predicates before types)

Inference with type classes:
1. Collect predicates during inference
2. Context reduction: simplify predicates
3. Improvement: derive equalities from fundeps
4. Entailment: check if predicates are satisfiable

Example:
    show 42
    -- Infers: (Show a, Num a) ⇒ a → String
    -- After defaulting: String
```

### 6.2 GADTs

GADTs require special handling:

```haskell
data Expr a where
    LitInt  :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Add     :: Expr Int -> Expr Int -> Expr Int
    Eq      :: Expr a -> Expr a -> Expr Bool

-- Pattern matching refines types
eval :: Expr a -> a
eval (LitInt n)  = n        -- a ~ Int in this branch
eval (LitBool b) = b        -- a ~ Bool in this branch
eval (Add e1 e2) = eval e1 + eval e2  -- a ~ Int
eval (Eq e1 e2)  = eval e1 == eval e2 -- a ~ Bool
```

**GADT inference requires:**
- Local constraint assumptions from patterns
- Rigid type variables (don't unify with anything)
- Type annotations often required

### 6.3 Rank-N Types

Higher-rank polymorphism:

```
Rank-0: No quantifiers
Rank-1: Quantifiers at top level (∀α. τ)
Rank-2: Quantifiers in argument position (∀α. τ) → σ
Rank-N: Arbitrary nesting

Inference challenges:
- Rank-2: decidable but complex
- Rank-N: undecidable in general
- Practical: require annotations at rank-2+ positions
```

### 6.4 Type Families

```
Inference with type families:
1. Generate type family applications during inference
2. Reduce type families during constraint solving
3. Handle non-confluence carefully

Example:
    type family Element c
    type instance Element [a] = a
    
    head :: [a] -> Element [a]
    -- Reduces to: head :: [a] -> a
```

### 6.5 Dependent Types

```
Dependent type inference:
1. Elaborate terms and types simultaneously
2. Metavariables for unknown types AND values
3. Unification may require computation

Example (Idris):
    append : Vect n a -> Vect m a -> Vect (n + m) a
    -- Must infer n, m, a from context
    -- Must verify n + m matches expected length
```

---

## 7. Inference for Substructural Types

### 7.1 Linear Type Inference

```
Linear type inference must track:
- Usage counts per variable
- Splitting contexts for multiple arguments
- Ensuring exactly-once usage

Rules:
    Γ₁ ⊢ e₁ : A ⊸ B    Γ₂ ⊢ e₂ : A    Γ₁ ∩ Γ₂ = ∅
    ─────────────────────────────────────────────────
                  Γ₁ ∪ Γ₂ ⊢ e₁ e₂ : B

Inference strategy:
1. Generate usage constraints
2. Solve: exactly-once for linear, at-most-once for affine
3. Report errors for over/under use
```

### 7.2 Uniqueness Inference

```
Uniqueness type inference (Clean-style):
- Propagate uniqueness attributes
- Infer uniqueness from usage patterns
- Coerce unique → non-unique (but not reverse)

Example:
    f : *File -> *File  -- unique file
    read : *File -> (String, *File)
    -- Uniqueness inferred from single-use pattern
```

### 7.3 Effect Inference

```
Effect inference:
1. Generate effect variables for unknown effects
2. Collect effect constraints from operations
3. Solve: effect sets must include required effects

Example:
    f = |x| { print(x); x + 1 }
    -- Infer: f : Int -[IO]-> Int
    -- Effect row: <IO | ε> for polymorphism
```

---

## 8. Error Reporting

### 8.1 Error Localization

```
Challenge: Constraint collected far from error source

Strategies:
1. Blame tracking: Remember constraint origins
2. Minimal unsatisfiable subset: Find smallest conflict
3. Heuristics: Guess likely error location

Example:
    let f x = x + 1 in f "hello"
    --          ↑ actual error (String vs Int)
    -- vs reporting at '+' or at 'f' application
```

### 8.2 Error Messages

```
Good error message principles:
1. Show expected vs actual type
2. Show relevant context
3. Suggest fixes when possible
4. Don't overwhelm with details

Example:
    Error: Type mismatch
    Expected: Int
    Found:    String
    
    In the expression: f "hello"
    
    Note: f has type: Int -> Int
    Hint: Did you mean to pass an integer?
```

### 8.3 Type Holes

```
Type holes show inferred context:

    let f x = _     -- Type hole
    -- Inferred: f : α → β
    -- Context: x : α
    
    let g = _ + 1   -- Hole in expression
    -- Hole has type: Int
    -- Expected: Int
```

---

## 9. Implementation Techniques

### 9.1 Levels for Generalization

```
Use levels to track generalization scope:

Level 0: top-level (always generalized)
Level 1: first let
Level 2: nested let
...

Generalize variables with level > current binding level:

let id = λx. x in    -- Level 1
  let f = id in      -- Level 2, can generalize id's type
    f 42             -- Instantiate at Int
```

### 9.2 Incremental Inference

```
For IDE/LSP support:
1. Cache inference results per declaration
2. Invalidate affected declarations on edit
3. Re-infer only changed parts
4. Provide partial results during editing

Data structures:
- Dependency graph of declarations
- Cached constraint solutions
- Lazy constraint solving
```

### 9.3 Parallel Inference

```
Opportunities for parallelism:
1. Infer independent functions in parallel
2. Solve independent constraint sets in parallel
3. Parallelize occurs check for large types

Challenges:
- Mutual dependencies
- Shared unification state
- Deterministic error reporting
```

---

## 10. Security-Relevant Inference

### 10.1 Information Flow Inference

```
Infer security labels:
1. Start with unknown label variables
2. Generate flow constraints from operations
3. Solve: find minimal consistent labeling

Example:
    fn process(secret: String@Secret) -> String@? {
        secret.to_uppercase()
    }
    -- Infer: return type is String@Secret
    -- (data derived from secret inherits label)
```

### 10.2 Capability Inference

```
Infer required capabilities:
1. Track capability requirements per operation
2. Collect capabilities needed
3. Report missing capabilities

Example:
    fn fetch_data(url: Url) -> Data {
        http_get(url)  -- Requires NetConnect
    }
    -- Infer: function requires [NetConnect]
```

### 10.3 Permission Inference

```
For mobile/web contexts:
1. Analyze API calls
2. Collect required permissions
3. Generate permission manifest

Example:
    fn take_photo() {
        let cam = Camera::open();  // Requires Camera
        let loc = Gps::location(); // Requires Location
        Photo::with_location(cam.capture(), loc)
    }
    -- Infer: requires [Camera, Location]
```

---

## 11. Comparison of Approaches

### 11.1 Algorithm Comparison

| Algorithm | Complexity | Features | Modularity |
|-----------|------------|----------|------------|
| Algorithm W | O(n²) | Basic HM | Low |
| Algorithm J | O(n α(n)) | Basic HM | Low |
| Bidirectional | O(n) | Higher-rank | High |
| Constraint | O(n²) | Full features | High |
| OutsideIn(X) | O(n²) | Type families | High |

### 11.2 Feature Support

| Feature | W/J | Bidir | Constraint |
|---------|-----|-------|------------|
| Let-polymorphism | ✓ | ✓ | ✓ |
| Higher-rank | ✗ | ✓ | ◐ |
| GADTs | ✗ | ✓ | ✓ |
| Type families | ✗ | ◐ | ✓ |
| Type classes | ext | ext | ✓ |
| Subtyping | ✗ | ✓ | ✓ |
| Linear types | ext | ✓ | ✓ |

---

## 12. Integration with TERAS Architecture

### 12.1 Inference for TERAS-LANG

```
TERAS-LANG Inference Architecture:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Base: Bidirectional checking with constraints

Extensions:
├── Linear type tracking (usage counts)
├── Effect row inference (effect variables)
├── Capability inference (collect requirements)
├── Security label inference (flow constraints)
├── Region inference (lifetime parameters)
└── Row type inference (Rémy-style)

Error handling:
├── Blame tracking for security errors
├── Custom messages for capability failures
└── Suggestions for annotation points
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 12.2 Inference Pipeline

```
┌─────────────────────────────────────────────────────────────┐
│                 TERAS-LANG Inference Pipeline                │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Source → Parse → Desugar → Elaborate → Solve → Zonk → IR   │
│                      │          │          │                 │
│                      ▼          ▼          ▼                 │
│                 Insert      Generate    Unify                │
│                 Metas       Constraints  Solve               │
│                      │          │          │                 │
│                      ▼          ▼          ▼                 │
│                 Bidir       Linear     Security              │
│                 Check       Track      Label                 │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

### 12.3 Product-Specific Inference

| Product | Inference Focus |
|---------|-----------------|
| MENARA | Permission requirements, trust levels |
| GAPURA | Request/response types, effect rows |
| ZIRAH | Process capabilities, resource usage |
| BENTENG | Identity attributes, verification states |
| SANDI | Key types, algorithm parameters |

---

## 13. Summary and Recommendations

### 13.1 Key Findings

| Approach | Strengths | Weaknesses |
|----------|-----------|------------|
| Hindley-Milner | Complete, principal types | Limited features |
| Bidirectional | Predictable, modular | Needs annotations |
| Constraint | Flexible, extensible | Complex solving |
| OutsideIn(X) | Handles advanced features | Complex impl |

### 13.2 Recommendations for TERAS-LANG

1. **Use bidirectional typing as core** for predictable error messages
2. **Add constraint solving** for type classes and refinements
3. **Integrate linear tracking** into inference phases
4. **Infer security labels** with flow constraints
5. **Infer capabilities** from operation usage
6. **Provide excellent error messages** with blame tracking

### 13.3 Implementation Priority

```
Priority 1: Core inference
├── Bidirectional checking
├── Unification with union-find
└── Let-polymorphism

Priority 2: Advanced features
├── Effect inference
├── Row type inference
└── Type class resolution

Priority 3: Security inference
├── Label inference
├── Capability inference
└── Permission manifest generation
```

---

## 14. References

1. Damas, L., & Milner, R. (1982). "Principal type-schemes for functional programs"
2. Pierce, B., & Turner, D. (2000). "Local Type Inference"
3. Dunfield, J., & Krishnaswami, N. (2013). "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"
4. Vytiniotis, D., et al. (2011). "OutsideIn(X): Modular type inference with local assumptions"
5. Odersky, M., & Läufer, K. (1996). "Putting Type Annotations to Work"
6. Jones, M. P. (1994). "Qualified Types: Theory and Practice"
7. Pottier, F., & Rémy, D. (2005). "The Essence of ML Type Inference"
8. Serrano, A., et al. (2020). "A quick look at impredicativity"

---

*Survey document for TERAS-LANG research track. Comprehensive coverage of type inference algorithms with security applications.*
