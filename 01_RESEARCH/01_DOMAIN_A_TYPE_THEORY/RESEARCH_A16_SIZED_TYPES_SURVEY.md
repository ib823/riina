# RESEARCH_A16_SIZED_TYPES_SURVEY.md

## TERAS Research Track — Domain A: Type Theory
### Session A-16: Sized Types

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research
**Predecessor:** A-15 (Staged Types)
**Successor:** A-17 (Type Inference Algorithms)

---

# PART I: FOUNDATIONS OF SIZED TYPES

## 1.1 Historical Development

### 1.1.1 The Termination Problem

```
Motivation for Sized Types:

Total Functional Programming:
  - All functions must terminate
  - Recursion must be well-founded
  - Required for type-level computation
  - Essential for theorem provers
  
Traditional Approaches:
  1. Syntactic termination checking
     - Structural recursion on inductive types
     - Lexicographic orderings
     - Limitation: conservative, rejects valid programs
     
  2. Semantic termination
     - Measure functions
     - Well-founded recursion
     - Limitation: manual proofs required
```

### 1.1.2 Sized Types Origins

```
Historical Timeline:

1995: Hughes, Pareto, Sabry
      - "Proving the Correctness of Reactive Systems"
      - Size annotations for coinductive types
      - Guardedness via types

1996: Giménez
      - Codatatypes with sizes in Coq
      - Guarded definitions

2001: Blanqui
      - Size-based termination
      - Inductive/coinductive types

2006: Abel
      - Sized types in MiniAgda
      - Type-based termination checking
      - Compositional approach

2010: Abel & Pientka
      - Wellfounded recursion with sized types
      - Pattern matching with sizes
```

### 1.1.3 Core Motivation

```
Why Sized Types?

Problem: Termination checking is undecidable
Solution: Track data structure sizes in types

Benefits:
  1. Compositional termination
     - Function termination from type signature
     - No global analysis needed
     
  2. More programs accepted
     - Beyond structural recursion
     - Non-syntactic patterns
     
  3. Productivity guarantees
     - Codata must produce output
     - Infinite streams well-defined
```

## 1.2 Core Concepts

### 1.2.1 Size Annotations

```
Size Annotation Syntax:

Types with Size:
  List^i α        -- list of size at most i
  Nat^i           -- natural number < i
  Tree^i α        -- tree of depth at most i
  
Size Variables:
  i, j, k         -- ordinal-valued size variables
  ω              -- infinite size (no bound)
  
Size Ordering:
  i < j           -- i strictly less than j
  i ≤ j           -- i at most j
  i < ω           -- any finite size
  
Example:
  map : ∀α β. ∀i. (α → β) → List^i α → List^i β
  -- Output list same size as input
```

### 1.2.2 Sized Inductive Types

```
Inductive Types with Sizes:

data Nat^i where
  Zero : ∀j < i. Nat^i
  Succ : ∀j < i. Nat^j → Nat^i

-- Zero has any size
-- Succ increases size by 1

data List^i α where
  Nil  : ∀j < i. List^i α
  Cons : ∀j < i. α → List^j α → List^i α

-- Size bounds list length

data Tree^i α where
  Leaf : ∀j < i. α → Tree^i α
  Node : ∀j < i. Tree^j α → Tree^j α → Tree^i α

-- Size bounds tree depth
```

### 1.2.3 Sized Coinductive Types (Codata)

```
Coinductive Types with Sizes:

codata Stream^i α where
  head : Stream^i α → α
  tail : ∀j < i. Stream^i α → Stream^j α

-- Observations decrease size
-- Productivity: must produce infinite elements

codata CoNat^i where
  case : CoNat^i → Maybe (∃j < i. CoNat^j)

-- Potentially infinite naturals
-- case returns either nothing or smaller CoNat

Example:
  nats : ∀i. CoNat^i → Stream^i Nat
  nats n = Cons (value n) (nats (succ n))
  -- Productive: always produces next element
```

## 1.3 Type System Properties

### 1.3.1 Termination via Types

```
Type-Based Termination:

Key Insight:
  Recursive calls must be on smaller sizes
  Sizes track "distance to termination"

Recursive Function Typing:
  f : ∀i. A^i → B
  f x = ... f y ...  -- y : A^j where j < i

Example:
  length : ∀α. ∀i. List^i α → Nat
  length Nil = Zero
  length (Cons x xs) = Succ (length xs)
  -- xs has smaller size, so call terminates
```

### 1.3.2 Productivity via Types

```
Type-Based Productivity:

Corecursive functions must produce output:
  
  g : ∀i. A → B^i
  g a = ... (g a) ...  -- must occur under constructor

Example:
  zeros : ∀i. Stream^i Nat
  zeros = Cons 0 zeros
  -- zeros appears under Cons (guarded)
  -- Each observation (tail) decreases size

Counter-example (rejected):
  bad : ∀i. Stream^i Nat
  bad = tail bad  -- not guarded!
  -- Would produce no elements
```

### 1.3.3 Subtyping for Sizes

```
Size Subtyping:

Size Ordering Induces Subtyping:
  i ≤ j
  ───────────────
  A^i <: A^j

-- Smaller data fits in larger type

Variance:
  - Inductive types: covariant in size
    List^i α <: List^j α  when i ≤ j
    
  - Coinductive types: contravariant (observations)
    Stream^j α <: Stream^i α  when i ≤ j
    
Quantification:
  ∀i. A^i  ≈  A^ω  (infinite size, no bound)
```

---

# PART II: SYSTEM IMPLEMENTATIONS

## 2.1 Agda Sized Types

### 2.1.1 Overview

```
Agda Sized Types:

Built-in Support:
  - Size type: Size
  - Size successor: ↑ (increase size)
  - Size infinity: ∞
  - Size maximum: ⊔
  
Enabling:
  {-# OPTIONS --sized-types #-}
  
Syntax:
  data Nat : Size → Set where
    zero : {i : Size} → Nat (↑ i)
    suc  : {i : Size} → Nat i → Nat (↑ i)
```

### 2.1.2 Example: Sized Lists in Agda

```agda
{-# OPTIONS --sized-types #-}

open import Size

data List (A : Set) : Size → Set where
  []  : {i : Size} → List A (↑ i)
  _∷_ : {i : Size} → A → List A i → List A (↑ i)

-- Map preserves size
map : {A B : Set} {i : Size} → (A → B) → List A i → List B i
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- Append increases size
_++_ : {A : Set} {i j : Size} → List A i → List A j → List A (i ⊔ j)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
```

### 2.1.3 Sized Codata in Agda

```agda
{-# OPTIONS --sized-types --copatterns #-}

open import Size

record Stream (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream A j

open Stream

-- Productive infinite stream
repeat : {A : Set} {i : Size} → A → Stream A i
head (repeat x) = x
tail (repeat x) = repeat x

-- Map on streams
mapS : {A B : Set} {i : Size} → (A → B) → Stream A i → Stream B i
head (mapS f s) = f (head s)
tail (mapS f s) = mapS f (tail s)
```

## 2.2 F* Decreases Clauses

### 2.2.1 Overview

```
F* Termination Checking:

Approach:
  - Decreases clauses specify termination measure
  - Built-in lexicographic ordering
  - Can use sized types via measures

Syntax:
  let rec f (x : t) : Tot result (decreases x)
  
Built-in Measures:
  - Structural: size of inductive argument
  - Lexicographic: tuples with lex order
  - Custom: user-defined well-founded order
```

### 2.2.2 Example: F* with Measures

```fstar
// Simple structural recursion
let rec length #a (l : list a) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

// Lexicographic termination
let rec ackermann (m n : nat) : Tot nat (decreases %[m; n]) =
  if m = 0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

// Custom measure
let rec gcd (a b : pos) : Tot pos (decreases (a + b)) =
  if a = b then a
  else if a > b then gcd (a - b) b
  else gcd a (b - a)
```

## 2.3 MiniAgda

### 2.3.1 Original Sized Types

```
MiniAgda (Abel 2006):

Pure sized type system for research:

data Nat : Size -> Set where
  zero : [i : Size] -> Nat ($ i)
  succ : [i : Size] -> Nat i -> Nat ($ i)

-- $ is size successor

fun half : [i : Size] -> Nat i -> Nat i
{ half i (zero (j < i)) = zero j
; half i (succ (j < i) (zero (k < j))) = zero k
; half i (succ (j < i) (succ (k < j) n)) = succ k (half k n)
}

-- Complex size reasoning
-- Termination evident from types
```

## 2.4 CIC with Sized Types

### 2.4.1 Calculus of Inductive Constructions Extension

```
CIC^ω (Blanqui, Barthe):

Extension of CIC with ordinal sizes:

Syntax:
  s ::= i | 0 | s+1 | ω | sup{i}s

Types:
  I^s            -- inductive type with size s
  coI^s          -- coinductive type with size s

Reduction:
  Match over I^s reduces constructors with size < s

Termination:
  Recursive calls on arguments of smaller size
  
Productivity:
  Corecursive definitions must be guarded
  Observations decrease size
```

---

# PART III: ADVANCED TOPICS

## 3.1 Size Inference

### 3.1.1 Inference Problem

```
Size Inference Challenge:

Given:
  f x = ... f y ...
  
Infer:
  f : ∀i. A^i → B   with j < i where y : A^j

Approaches:
  1. Constraint-based inference
     - Generate size constraints
     - Solve via fixpoint
     
  2. Annotation propagation
     - Programmer provides key annotations
     - System propagates
     
  3. Bidirectional inference
     - Check vs infer modes
     - Local type annotation
```

### 3.1.2 Size Constraint Solving

```
Constraint Language:

Constraints:
  C ::= i < j | i ≤ j | i = j | C ∧ C | ∃i. C

Example Inference:
  length : List^? α → Nat
  length Nil = Zero
  length (Cons x xs) = Succ (length xs)
  
Constraints Generated:
  ∀i. List^i α → Nat
  xs : List^j α with j < i
  
Solution:
  length : ∀i. List^i α → Nat
```

## 3.2 Sized Types and Dependent Types

### 3.2.1 Interaction

```
Sized Dependent Types:

Combining sizes with dependent types:

Vec : Nat → Set → Set
Vec^i : Size → Nat → Set → Set

-- Size bounds structure, Nat is exact length
data Vec^i (n : Nat) (A : Set) : Size → Set where
  nil  : Vec^(↑i) zero A
  cons : {m : Nat} → A → Vec^i m A → Vec^(↑i) (suc m) A

-- Size ensures termination
-- Length ensures correctness
```

### 3.2.2 Universe Levels and Sizes

```
Universe Stratification:

Sizes interact with universe levels:

Size : Set_ω    -- Size has "large" universe level

Potential Issues:
  - Size polymorphism and universe polymorphism
  - Type-in-type with sizes
  
Restrictions:
  - Size cannot appear in indices (some systems)
  - Size erasure before runtime
```

## 3.3 Sized Types for Termination Metrics

### 3.3.1 Beyond Structural Recursion

```
Non-Structural Termination:

Example: Division
  div : Nat → Nat → Nat
  div n m = if n < m then 0 else 1 + div (n - m) m
  
Not structurally recursive!

With Sized Types:
  div : ∀i. Nat^i → Nat → Nat
  div Zero m = Zero
  div (Succ n) m = 
    if Succ n < m then Zero
    else Succ (div (minus (Succ n) m) m)
    
-- Need: minus decreases size appropriately
-- minus : Nat^i → Nat → Nat^i  (preserves bound)
```

### 3.3.2 Mutual Recursion

```
Mutually Recursive Functions:

even : Nat → Bool
odd  : Nat → Bool

even Zero = True
even (Succ n) = odd n

odd Zero = False
odd (Succ n) = even n

With Sizes:
  even : ∀i. Nat^i → Bool
  odd  : ∀i. Nat^i → Bool
  
-- Both decrease on same size
-- Mutual termination clear
```

---

# PART IV: SECURITY APPLICATIONS

## 4.1 Bounded Computation

### 4.1.1 Resource Bounds via Types

```
Security Application: Bounded Execution

Problem:
  - Denial of service via infinite loops
  - Resource exhaustion attacks
  
Solution with Sized Types:
  -- Function guaranteed to terminate
  process : ∀i. Request^i → Response
  
  -- Bounded recursion depth
  parse : ∀i. Input^i → Result
  
  -- Maximum iterations
  iterate : ∀i. Nat^i → State → State
```

### 4.1.2 TERAS Application

```
TERAS Bounded Computation:

GAPURA (WAF):
  -- Bounded request parsing
  parse_request : ∀i. Bytes^i → Request
  
  -- Bounded rule evaluation
  eval_rules : ∀i. RuleSet → Request → Decision

ZIRAH (EDR):
  -- Bounded signature matching
  match_signature : ∀i. Pattern → Memory^i → MatchResult
  
  -- Bounded behavior analysis
  analyze : ∀i. Events^i → ThreatLevel
```

## 4.2 Guaranteed Response Times

### 4.2.1 Worst-Case Execution Time

```
WCET via Sized Types:

Sized types enable WCET analysis:

process : ∀i. Input^i → Output
-- WCET = O(i) by size analysis

Derivation:
  - Size i bounds recursion depth
  - Each recursive call: constant work
  - Total work: O(i)
  
For Real-Time Security:
  - Predictable response times
  - No timing-based DoS
  - Bounded latency guarantees
```

## 4.3 Stream Processing Guarantees

### 4.3.1 Productive Security Services

```
Productive Stream Processing:

Security service as infinite stream processor:

service : ∀i. Stream^i Request → Stream^i Response
service reqs = map process reqs

Productivity guarantee:
  - Every request eventually gets response
  - No deadlocks
  - No infinite waiting
  
MENARA Application:
  session : ∀i. Stream^i Event → Stream^i Action
  -- Continuous session monitoring
  -- Guaranteed to process each event
```

---

# PART V: INTEGRATION WITH TYPE SYSTEM

## 5.1 Integration with Linear Types (A-04)

```
Linear Sized Types:

lin A^i    -- linear resource of bounded size

Example:
  process : ∀i. lin Buffer^i → Result
  -- Buffer consumed
  -- Processing terminates (bounded by i)

Combination Rules:
  Γ ⊢ e : lin A^i
  ─────────────────────
  Γ ⊢ e : lin A^j  where i ≤ j
```

## 5.2 Integration with Effects (A-11)

```
Sized Effects:

Effect indexing by size:

effect Iterate^i {
    Step : State → State
}
-- At most i iterations

Handler:
  handle (bounded_loop n) 
  with Iterator^n { ... }
  -- Guaranteed termination
```

## 5.3 Integration with Capabilities (A-14)

```
Sized Capabilities:

cap<R, P>^i   -- capability valid for i uses

Example:
  api_cap : cap<API, Call>^1000
  -- Can make at most 1000 API calls
  
Rate Limiting via Types:
  call_api : cap<API, Call>^(↑i) → Request → (Response, cap<API, Call>^i)
  -- Each call decreases remaining quota
```

## 5.4 Integration with Staged Types (A-15)

```
Sized Staging:

code[A^i]     -- code producing bounded data

Example:
  compile : Expr → code[∀i. Input^i → Output]
  -- Generated code terminates on any input
  
Staging with Termination:
  specialize : ∀i. Algorithm → code[Data^i → Result]
  -- Specialized code inherits termination
```

---

# PART VI: SUMMARY

## 6.1 Key Systems Surveyed

| System | Approach | Inference | Production |
|--------|----------|-----------|------------|
| Agda | Built-in sizes | Partial | Yes |
| F* | Decreases clauses | Manual | Yes |
| MiniAgda | Pure sized types | Research | Research |
| CIC^ω | Ordinal sizes | Partial | Research |

## 6.2 Core Properties

```
Essential Sized Type Properties:

1. Termination Guarantee
   Sized recursive functions terminate
   
2. Productivity Guarantee
   Sized corecursive functions are productive
   
3. Compositional Reasoning
   Size from type signature, not analysis
   
4. Subtyping
   Size ordering induces type ordering
   
5. Inference
   Partial automation possible
```

## 6.3 Design Considerations for TERAS-LANG

```
TERAS-LANG Sized Type Questions:

1. Size Representation
   - Ordinals (general)?
   - Naturals (simple)?
   - Symbolic (uninterpreted)?
   
2. Inference Level
   - Full inference?
   - Key annotations?
   - Explicit everywhere?
   
3. Integration Priorities
   - With linear types (A-04): bounded linear resources
   - With effects (A-11): bounded effect handling
   - With capabilities (A-14): usage-limited caps
   
4. Security Applications
   - DoS prevention via bounded computation
   - WCET for real-time guarantees
   - Resource quota enforcement
```

---

**END OF SURVEY DOCUMENT**

**Next Document:** RESEARCH_A16_SIZED_TYPES_COMPARISON.md
