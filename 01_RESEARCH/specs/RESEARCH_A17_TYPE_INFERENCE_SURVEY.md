# RESEARCH_A17_TYPE_INFERENCE_SURVEY.md

## TERAS Research Track â€” Domain A: Type Theory
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
  Ï„ ::= Î± | Ï„ â†’ Ï„ | T Ï„â‚...Ï„â‚™     (monotypes)
  Ïƒ ::= Ï„ | âˆ€Î±.Ïƒ                   (polytypes)

Typing Rules:
  Î“(x) = Ïƒ
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (Var)
  Î“ âŠ¢ x : Ïƒ

  Î“ âŠ¢ eâ‚ : Ï„â‚ â†’ Ï„â‚‚    Î“ âŠ¢ eâ‚‚ : Ï„â‚
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (App)
  Î“ âŠ¢ eâ‚ eâ‚‚ : Ï„â‚‚

  Î“, x : Ï„â‚ âŠ¢ e : Ï„â‚‚
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (Abs)
  Î“ âŠ¢ Î»x.e : Ï„â‚ â†’ Ï„â‚‚

  Î“ âŠ¢ eâ‚ : Ïƒ    Î“, x : Ïƒ âŠ¢ eâ‚‚ : Ï„
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (Let)
  Î“ âŠ¢ let x = eâ‚ in eâ‚‚ : Ï„

Key Property: Principal types exist
```

### 1.2.2 Algorithm W

```
Algorithm W (Milner 1978):

W(Î“, e) â†’ (S, Ï„)   -- substitution and type

W(Î“, x) = (id, inst(Î“(x)))

W(Î“, Î»x.e) =
  let Î± = fresh() in
  let (S, Ï„) = W(Î“[xâ†¦Î±], e) in
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
  let (Sâ‚‚, Ï„â‚‚) = W(Sâ‚(Î“)[xâ†¦Ïƒ], eâ‚‚) in
  (Sâ‚‚ âˆ˜ Sâ‚, Ï„â‚‚)

Complexity: O(n) typical, exponential worst case
```

### 1.2.3 Unification

```
Robinson's Unification:

unify(Ï„â‚, Ï„â‚‚) â†’ S (most general unifier)

unify(Î±, Ï„) = 
  if Î± âˆˆ FV(Ï„) then fail (occurs check)
  else [Î± â†¦ Ï„]

unify(Ï„â‚ â†’ Ï„â‚‚, Ï„â‚ƒ â†’ Ï„â‚„) =
  let Sâ‚ = unify(Ï„â‚, Ï„â‚ƒ) in
  let Sâ‚‚ = unify(Sâ‚(Ï„â‚‚), Sâ‚(Ï„â‚„)) in
  Sâ‚‚ âˆ˜ Sâ‚

unify(T Ï„â‚...Ï„â‚™, T Ïƒâ‚...Ïƒâ‚™) =
  unify(Ï„â‚, Ïƒâ‚) âˆ˜ ... âˆ˜ unify(Ï„â‚™, Ïƒâ‚™)

unify(Ï„, Ï„) = id

otherwise â†’ fail
```

## 1.3 Bidirectional Type Checking

### 1.3.1 Core Approach

```
Bidirectional Typing:

Two Modes:
  Î“ âŠ¢ e â‡ A   -- check e against A
  Î“ âŠ¢ e â‡’ A   -- synthesize type A for e

Mode Switching:
  Î“ âŠ¢ e â‡’ A
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (Sub)
  Î“ âŠ¢ e â‡ A

Key Rules:
  Î“ âŠ¢ e â‡ A    Î“ âŠ¢ f â‡ B
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (check pair)
  Î“ âŠ¢ (e, f) â‡ A Ã— B

  Î“(x) = A
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (synth var)
  Î“ âŠ¢ x â‡’ A

  Î“ âŠ¢ f â‡’ A â†’ B    Î“ âŠ¢ e â‡ A
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (synth app)
  Î“ âŠ¢ f e â‡’ B
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
  map : âˆ€Î± Î². (Î± â†’ Î²) â†’ List Î± â†’ List Î²
  
  map (Î»x. x + 1) [1, 2, 3]
  -- Î± = Int, Î² = Int inferred locally
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
  Q ::= Ï„â‚ ~ Ï„â‚‚        -- equality
      | C Ï„â‚...Ï„â‚™      -- type class
      | Q âˆ§ Q          -- conjunction
      | âˆƒÎ±.Q           -- existential
      | Q âŠƒ Q          -- implication

Algorithm:
  infer(e) = (Ï„, Q)     -- type and constraints
  solve(Q) = S          -- substitution
  final = S(Ï„)
```

### 2.1.2 GADTs and Type Families

```
GADT Inference:

data Expr a where
  Lit  : Int â†’ Expr Int
  Plus : Expr Int â†’ Expr Int â†’ Expr Int
  Eq   : Expr Int â†’ Expr Int â†’ Expr Bool

eval : Expr a â†’ a
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
  {Î½ : B | p}   -- refined base type

Inference Approach:
  1. Generate templates with unknown predicates
  2. Collect constraints from subtyping
  3. Solve via predicate abstraction
  
Qualifier Language:
  Q = {Î½ â‰¥ 0, Î½ â‰¤ len xs, ...}
  
Algorithm:
  - Infer qualifiers from program syntax
  - Template: {Î½ : B | Îº} where Îº is qualifier variable
  - Constraint: {Î½ : B | pâ‚} <: {Î½ : B | pâ‚‚} iff âˆ€Î½. pâ‚ âŸ¹ pâ‚‚
  - Solve via abstract interpretation
```

## 2.3 Effect Inference

### 2.3.1 Row-Based Effect Inference

```
Effect Inference (Leijen 2014):

Types:
  Ï„ ::= ... | Ï„ â†’ Ï„ ! Îµ
  Îµ ::= âŸ¨â„“â‚ | ... | â„“â‚™ | ÏâŸ©   -- effect row

Inference:
  - Infer effect variables
  - Collect effect constraints
  - Solve via row unification
  
Example:
  f : A â†’ B ! âŸ¨Read | ÏâŸ©
  g : B â†’ C ! âŸ¨Write | ÏƒâŸ©
  
  h x = g (f x)
  -- h : A â†’ C ! âŸ¨Read | Write | Ï âˆª ÏƒâŸ©
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
     âˆ€m. A â†’^m B
     Infer m from context

TERAS Approach: Explicit linearity for clarity
```

## 3.2 Effect Type Inference

```
TERAS Effect Inference:

Effect Rows:
  fn f() -> A ! {Eâ‚ | Ï}
  -- Ï is effect variable
  
Inference:
  - Collect effect constraints
  - Solve via row unification
  - Principal effects exist

Example:
  fn compose(f: A -> B ! Eâ‚, g: B -> C ! Eâ‚‚) -> (A -> C ! Eâ‚ âˆª Eâ‚‚)
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
  length : List^? A â†’ Nat
  length [] = 0
  length (x :: xs) = 1 + length xs
  
  Constraints:
    xs : List^i A where i < ?
    
  Solution:
    length : âˆ€i. List^i A â†’ Nat
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
