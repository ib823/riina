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
// Principal type: âˆ€Î±. Î± â†’ Î± (not Int â†’ Int or Bool â†’ Bool)
```

**Type Schemes**: Types with universal quantification.
```
Ïƒ ::= Ï„ | âˆ€Î±. Ïƒ      (type schemes)
Ï„ ::= Î± | Ï„ â†’ Ï„ | ...  (monotypes)
```

**Substitution**: Mapping from type variables to types.
```
[Î± â†¦ Int](Î± â†’ Î±) = Int â†’ Int
```

### 1.3 Historical Development

```
Timeline of Type Inference:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
1958    â”‚ Curry-Howard correspondence foundation
1969    â”‚ Hindley: principal type theorem for combinatory logic
1978    â”‚ Milner: Algorithm W for ML
1982    â”‚ Damas-Milner: formal soundness and completeness
1985    â”‚ Practical implementations in SML
1989    â”‚ RÃ©my: rows and records
1993    â”‚ Jones: qualified types (type classes)
1997    â”‚ Odersky-LÃ¤ufer: colored local type inference
2000    â”‚ Pierce-Turner: local type inference
2004    â”‚ Dunfield-Pfenning: bidirectional typing
2010    â”‚ OutsideIn(X): modular constraint solving
2013    â”‚ Complete and Easy bidirectional typing
2020+   â”‚ Modern refinements and extensions
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

---

## 2. Hindley-Milner Type System

### 2.1 The HM Type System

The Hindley-Milner (HM) type system is the foundation of ML-family languages:

**Syntax:**
```
Types:       Ï„ ::= Î± | Ï„â‚ â†’ Ï„â‚‚ | T Ï„â‚ ... Ï„â‚™
Schemes:     Ïƒ ::= Ï„ | âˆ€Î±. Ïƒ
Expressions: e ::= x | Î»x. e | eâ‚ eâ‚‚ | let x = eâ‚ in eâ‚‚
```

**Key Properties:**
- Decidable type inference
- Principal types exist
- Let-polymorphism (generalize at let-bindings)

### 2.2 Typing Rules

```
Variable:
    x : Ïƒ âˆˆ Î“    Ï„ = inst(Ïƒ)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
           Î“ âŠ¢ x : Ï„

Application:
    Î“ âŠ¢ eâ‚ : Ï„â‚ â†’ Ï„â‚‚    Î“ âŠ¢ eâ‚‚ : Ï„â‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
           Î“ âŠ¢ eâ‚ eâ‚‚ : Ï„â‚‚

Abstraction:
    Î“, x : Ï„â‚ âŠ¢ e : Ï„â‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ Î»x. e : Ï„â‚ â†’ Ï„â‚‚

Let:
    Î“ âŠ¢ eâ‚ : Ï„â‚    Î“, x : gen(Î“, Ï„â‚) âŠ¢ eâ‚‚ : Ï„â‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
              Î“ âŠ¢ let x = eâ‚ in eâ‚‚ : Ï„â‚‚
```

**Generalization:**
```
gen(Î“, Ï„) = âˆ€á¾±. Ï„  where á¾± = FV(Ï„) \ FV(Î“)
```

**Instantiation:**
```
inst(âˆ€Î±â‚...Î±â‚™. Ï„) = [Î±â‚ â†¦ Î²â‚, ..., Î±â‚™ â†¦ Î²â‚™]Ï„  (fresh Î²áµ¢)
```

### 2.3 Algorithm W

Damas and Milner's Algorithm W computes principal types:

```
W(Î“, x) = 
    let Ïƒ = Î“(x) in
    let Ï„ = inst(Ïƒ) in
    (âˆ…, Ï„)

W(Î“, Î»x. e) =
    let Î± = fresh() in
    let (S, Ï„) = W(Î“ âˆª {x : Î±}, e) in
    (S, S(Î±) â†’ Ï„)

W(Î“, eâ‚ eâ‚‚) =
    let (Sâ‚, Ï„â‚) = W(Î“, eâ‚) in
    let (Sâ‚‚, Ï„â‚‚) = W(Sâ‚(Î“), eâ‚‚) in
    let Î± = fresh() in
    let Sâ‚ƒ = unify(Sâ‚‚(Ï„â‚), Ï„â‚‚ â†’ Î±) in
    (Sâ‚ƒ âˆ˜ Sâ‚‚ âˆ˜ Sâ‚, Sâ‚ƒ(Î±))

W(Î“, let x = eâ‚ in eâ‚‚) =
    let (Sâ‚, Ï„â‚) = W(Î“, eâ‚) in
    let Ïƒ = gen(Sâ‚(Î“), Ï„â‚) in
    let (Sâ‚‚, Ï„â‚‚) = W(Sâ‚(Î“) âˆª {x : Ïƒ}, eâ‚‚) in
    (Sâ‚‚ âˆ˜ Sâ‚, Ï„â‚‚)
```

### 2.4 Algorithm J (More Efficient)

Algorithm J uses explicit substitution application less:

```
J(Î“, e) performs inference using:
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
unify(Ï„, Ï„) = âˆ…

unify(Î±, Ï„) = 
    if Î± âˆˆ FV(Ï„) then fail("occurs check")
    else [Î± â†¦ Ï„]

unify(Ï„, Î±) = unify(Î±, Ï„)

unify(Ï„â‚ â†’ Ï„â‚‚, Ï„â‚ƒ â†’ Ï„â‚„) =
    let Sâ‚ = unify(Ï„â‚, Ï„â‚ƒ) in
    let Sâ‚‚ = unify(Sâ‚(Ï„â‚‚), Sâ‚(Ï„â‚„)) in
    Sâ‚‚ âˆ˜ Sâ‚

unify(T Ï„â‚...Ï„â‚™, T Ï„'â‚...Ï„'â‚™) =
    unify(Ï„â‚, Ï„'â‚) âˆ˜ ... âˆ˜ unify(Ï„â‚™, Ï„'â‚™)

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
Flex-flex: ?F xâ‚...xâ‚™ â‰ ?G yâ‚...yâ‚˜
    - Multiple solutions possible
    - Generate constraint (delay)

Flex-rigid: ?F xâ‚...xâ‚™ â‰ c tâ‚...tâ‚˜
    - Imitation: F = Î»xâ‚...xâ‚™. c (Hâ‚ xâ‚...xâ‚™) ... (Hâ‚˜ xâ‚...xâ‚™)
    - Projection: F = Î»xâ‚...xâ‚™. xáµ¢ (Hâ‚ xâ‚...xâ‚™) ... (Hâ‚– xâ‚...xâ‚™)
```

**Decidability**: Higher-order unification is undecidable in general, but practical patterns are decidable.

---

## 4. Bidirectional Type Checking

### 4.1 Core Idea

Split type inference into two modes:
- **Checking** (â‡): Check expression against known type
- **Synthesis** (â‡’): Infer type from expression

```
Î“ âŠ¢ e â‡ A   (check e against A)
Î“ âŠ¢ e â‡’ A   (synthesize A from e)
```

### 4.2 Basic Bidirectional Rules

```
Synthesis (â‡’):
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Variable:     (x : A) âˆˆ Î“
                  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                  Î“ âŠ¢ x â‡’ A

    Annotated:    Î“ âŠ¢ e â‡ A
                  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                  Î“ âŠ¢ (e : A) â‡’ A

    Application:  Î“ âŠ¢ eâ‚ â‡’ A â†’ B    Î“ âŠ¢ eâ‚‚ â‡ A
                  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                  Î“ âŠ¢ eâ‚ eâ‚‚ â‡’ B

Checking (â‡):
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Lambda:       Î“, x : A âŠ¢ e â‡ B
                  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                  Î“ âŠ¢ Î»x. e â‡ A â†’ B

    Subsumption:  Î“ âŠ¢ e â‡’ A    A <: B
                  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                  Î“ âŠ¢ e â‡ B
```

### 4.3 Complete and Easy Bidirectional Typing

Dunfield and Krishnaswami's system handles polymorphism:

```
Types:    A, B ::= 1 | Î± | A â†’ B | âˆ€Î±. A | âˆƒÎ±. A
Context:  Î“    ::= Â· | Î“, x : A | Î“, Î± | Î“, Î±Ì‚ | Î“, Î±Ì‚ = Ï„

Key rules:

âˆ€-Introduction (check):
    Î“, Î± âŠ¢ e â‡ A
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e â‡ âˆ€Î±. A

âˆ€-Elimination (apply):
    Î“ âŠ¢ e â‡’ âˆ€Î±. A    Î“ âŠ¢ Ï„
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e â‡’ [Î± â†¦ Ï„]A

Existential variables (Î±Ì‚):
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
    infer(Î“, e) = (Ï„, C)
    
Phase 2: Solve constraints
    solve(C) = S (substitution)
    
Phase 3: Apply solution
    type(e) = S(Ï„)
```

### 5.2 Constraint Language

```
Constraints:
    C ::= Ï„â‚ = Ï„â‚‚           (equality)
        | Ï„â‚ â‰¤ Ï„â‚‚           (subtyping)
        | Câ‚ âˆ§ Câ‚‚           (conjunction)
        | âˆƒÎ±. C             (existential)
        | âˆ€Î±. C             (universal)
        | Ï„ âˆˆ K             (kind constraint)
        | instance(Ïƒ, Ï„)    (instantiation)
```

### 5.3 OutsideIn(X)

GHC's constraint-based type inference:

```
Key ideas:
1. Implication constraints: Q âŠƒ C
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

-- Generates: âˆ€a. (Eq a) âŠƒ (a ~ a, a ~ a, Bool ~ Bool)
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
Qualified types: Ï ::= Ï„ | Ï€ â‡’ Ï  (predicates before types)

Inference with type classes:
1. Collect predicates during inference
2. Context reduction: simplify predicates
3. Improvement: derive equalities from fundeps
4. Entailment: check if predicates are satisfiable

Example:
    show 42
    -- Infers: (Show a, Num a) â‡’ a â†’ String
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
Rank-1: Quantifiers at top level (âˆ€Î±. Ï„)
Rank-2: Quantifiers in argument position (âˆ€Î±. Ï„) â†’ Ïƒ
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
    Î“â‚ âŠ¢ eâ‚ : A âŠ¸ B    Î“â‚‚ âŠ¢ eâ‚‚ : A    Î“â‚ âˆ© Î“â‚‚ = âˆ…
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                  Î“â‚ âˆª Î“â‚‚ âŠ¢ eâ‚ eâ‚‚ : B

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
- Coerce unique â†’ non-unique (but not reverse)

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
    -- Effect row: <IO | Îµ> for polymorphism
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
    --          â†‘ actual error (String vs Int)
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
    -- Inferred: f : Î± â†’ Î²
    -- Context: x : Î±
    
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

let id = Î»x. x in    -- Level 1
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
| Algorithm W | O(nÂ²) | Basic HM | Low |
| Algorithm J | O(n Î±(n)) | Basic HM | Low |
| Bidirectional | O(n) | Higher-rank | High |
| Constraint | O(nÂ²) | Full features | High |
| OutsideIn(X) | O(nÂ²) | Type families | High |

### 11.2 Feature Support

| Feature | W/J | Bidir | Constraint |
|---------|-----|-------|------------|
| Let-polymorphism | âœ“ | âœ“ | âœ“ |
| Higher-rank | âœ— | âœ“ | â— |
| GADTs | âœ— | âœ“ | âœ“ |
| Type families | âœ— | â— | âœ“ |
| Type classes | ext | ext | âœ“ |
| Subtyping | âœ— | âœ“ | âœ“ |
| Linear types | ext | âœ“ | âœ“ |

---

## 12. Integration with TERAS Architecture

### 12.1 Inference for TERAS-LANG

```
TERAS-LANG Inference Architecture:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
Base: Bidirectional checking with constraints

Extensions:
â”œâ”€â”€ Linear type tracking (usage counts)
â”œâ”€â”€ Effect row inference (effect variables)
â”œâ”€â”€ Capability inference (collect requirements)
â”œâ”€â”€ Security label inference (flow constraints)
â”œâ”€â”€ Region inference (lifetime parameters)
â””â”€â”€ Row type inference (RÃ©my-style)

Error handling:
â”œâ”€â”€ Blame tracking for security errors
â”œâ”€â”€ Custom messages for capability failures
â””â”€â”€ Suggestions for annotation points
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

### 12.2 Inference Pipeline

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                 TERAS-LANG Inference Pipeline                â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                              â”‚
â”‚  Source â†’ Parse â†’ Desugar â†’ Elaborate â†’ Solve â†’ Zonk â†’ IR   â”‚
â”‚                      â”‚          â”‚          â”‚                 â”‚
â”‚                      â–¼          â–¼          â–¼                 â”‚
â”‚                 Insert      Generate    Unify                â”‚
â”‚                 Metas       Constraints  Solve               â”‚
â”‚                      â”‚          â”‚          â”‚                 â”‚
â”‚                      â–¼          â–¼          â–¼                 â”‚
â”‚                 Bidir       Linear     Security              â”‚
â”‚                 Check       Track      Label                 â”‚
â”‚                                                              â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”œâ”€â”€ Bidirectional checking
â”œâ”€â”€ Unification with union-find
â””â”€â”€ Let-polymorphism

Priority 2: Advanced features
â”œâ”€â”€ Effect inference
â”œâ”€â”€ Row type inference
â””â”€â”€ Type class resolution

Priority 3: Security inference
â”œâ”€â”€ Label inference
â”œâ”€â”€ Capability inference
â””â”€â”€ Permission manifest generation
```

---

## 14. References

1. Damas, L., & Milner, R. (1982). "Principal type-schemes for functional programs"
2. Pierce, B., & Turner, D. (2000). "Local Type Inference"
3. Dunfield, J., & Krishnaswami, N. (2013). "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"
4. Vytiniotis, D., et al. (2011). "OutsideIn(X): Modular type inference with local assumptions"
5. Odersky, M., & LÃ¤ufer, K. (1996). "Putting Type Annotations to Work"
6. Jones, M. P. (1994). "Qualified Types: Theory and Practice"
7. Pottier, F., & RÃ©my, D. (2005). "The Essence of ML Type Inference"
8. Serrano, A., et al. (2020). "A quick look at impredicativity"

---

*Survey document for TERAS-LANG research track. Comprehensive coverage of type inference algorithms with security applications.*
