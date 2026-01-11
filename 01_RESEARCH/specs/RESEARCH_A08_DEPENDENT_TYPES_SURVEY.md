# RESEARCH_A08_DEPENDENT_TYPES_SURVEY.md

## TERAS-LANG Research Track â€” Session A-08
## Dependent Types: Agda, Idris, Lean

**Version:** 1.0.0
**Date:** 2026-01-03
**Status:** COMPLETE
**Classification:** FOUNDATIONAL RESEARCH

---

# PART I: INTRODUCTION AND FOUNDATIONS

## 1.1 Purpose

This document provides a comprehensive survey of dependent type systems, their theoretical foundations, and practical implementations in languages such as Agda, Idris, and Lean. Dependent types are essential to TERAS-LANG because they enable:

1. **Compile-time verification** â€” Security properties proven at compile time
2. **Expressive specifications** â€” Types that precisely describe function behavior
3. **Proof-carrying code** â€” Programs that contain proofs of correctness
4. **Index-based invariants** â€” Length-indexed vectors, bounds-checked arrays
5. **Protocol verification** â€” Statically verified communication protocols

## 1.2 What Are Dependent Types?

A **dependent type** is a type whose definition depends on a value. This contrasts with simple types (where types depend only on other types) and parametric polymorphism (where types are parameterized by other types, not values).

### Core Insight

In standard type systems:
```
length : List a â†’ Int
```

With dependent types:
```
Vec : Type â†’ Nat â†’ Type
-- Vec a n is a vector of n elements of type a

head : Vec a (n + 1) â†’ a    -- Only callable on non-empty vectors!
append : Vec a n â†’ Vec a m â†’ Vec a (n + m)
```

The type itself carries information about the *value* â€” the length is part of the type.

## 1.3 Historical Development

### Timeline

| Year | Development | Significance |
|------|-------------|--------------|
| 1934 | Curry-Howard Correspondence (noticed by Curry) | Types as propositions, programs as proofs |
| 1972 | Martin-LÃ¶f Type Theory | First practical dependent type theory |
| 1984 | Per Martin-LÃ¶f's "Intuitionistic Type Theory" | Definitive formulation |
| 1985 | Calculus of Constructions (Coquand-Huet) | Foundation for Coq |
| 1989 | Calculus of Inductive Constructions | Added inductive types |
| 1999 | ALF (Alf proof editor) | Chalmers, precursor to Agda |
| 2002 | Epigram (McBride) | Practical dependent programming |
| 2005 | Agda 1 | First modern dependently-typed language |
| 2007 | Agda 2 (Norell) | Practical implementation |
| 2013 | Idris 1 (Brady) | General-purpose dependently-typed language |
| 2013 | Lean 1 (de Moura) | Microsoft Research theorem prover |
| 2017 | Lean 3 | First stable Lean version |
| 2021 | Lean 4 | Self-hosted, efficient code generation |
| 2021 | Idris 2 | Quantitative Type Theory foundation |

---

# PART II: THEORETICAL FOUNDATIONS

## 2.1 Dependent Function Types (Î -Types)

The **dependent function type** (Pi-type) generalizes ordinary function types by allowing the return type to depend on the input value.

### Formal Definition

```
Î (x : A). B(x)    -- or in notation: (x : A) â†’ B(x)
```

Where:
- `A` is a type (the domain)
- `B` is a type family indexed by elements of `A`
- For each `a : A`, we have `B(a)` is a type

### Rules

**Formation:**
```
Î“ âŠ¢ A : Type    Î“, x : A âŠ¢ B : Type
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
       Î“ âŠ¢ Î (x : A). B : Type
```

**Introduction:**
```
       Î“, x : A âŠ¢ b : B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ Î»(x : A). b : Î (x : A). B
```

**Elimination:**
```
Î“ âŠ¢ f : Î (x : A). B    Î“ âŠ¢ a : A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
         Î“ âŠ¢ f a : B[a/x]
```

**Computation (Î²-reduction):**
```
(Î»(x : A). b) a â‰¡ b[a/x]
```

### Ordinary Functions as Special Case

When `B` doesn't depend on `x`:
```
Î (x : A). B â‰¡ A â†’ B    -- ordinary function type
```

### Examples

```agda
-- Vector type indexed by length
data Vec (A : Set) : Nat â†’ Set where
  []  : Vec A zero
  _âˆ·_ : {n : Nat} â†’ A â†’ Vec A n â†’ Vec A (suc n)

-- Safe head: only works on non-empty vectors
head : {A : Set} {n : Nat} â†’ Vec A (suc n) â†’ A
head (x âˆ· xs) = x

-- Matrix multiplication with dimension checking
matMul : {m n p : Nat} â†’ Mat m n â†’ Mat n p â†’ Mat m p
```

## 2.2 Dependent Pair Types (Î£-Types)

The **dependent pair type** (Sigma-type) generalizes ordinary pair types by allowing the type of the second component to depend on the value of the first.

### Formal Definition

```
Î£(x : A). B(x)    -- or in notation: (x : A) Ã— B(x)
```

### Rules

**Formation:**
```
Î“ âŠ¢ A : Type    Î“, x : A âŠ¢ B : Type
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
       Î“ âŠ¢ Î£(x : A). B : Type
```

**Introduction:**
```
Î“ âŠ¢ a : A    Î“ âŠ¢ b : B[a/x]
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
   Î“ âŠ¢ (a, b) : Î£(x : A). B
```

**Elimination (projections):**
```
Î“ âŠ¢ p : Î£(x : A). B        Î“ âŠ¢ p : Î£(x : A). B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€      â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
   Î“ âŠ¢ fst p : A           Î“ âŠ¢ snd p : B[fst p/x]
```

### Existential Quantification

Î£-types encode existential quantification:
```
Î£(n : Nat). Vec A n    -- "there exists an n such that Vec A n"
```

This represents a vector of *some* length, paired with its length.

### Record Types

Records are desugared to Î£-types:
```agda
record Person : Set where
  field
    name : String
    age  : Nat

-- Equivalent to:
Person = Î£(name : String). Î£(age : Nat). âŠ¤
```

## 2.3 Universe Hierarchy

To avoid Russell's paradox (`Type : Type` leads to inconsistency), dependent type theories use a hierarchy of universes.

### Typical Hierarchy

```
Setâ‚€ : Setâ‚ : Setâ‚‚ : Setâ‚ƒ : ...
```

Or equivalently:
```
Typeâ‚€ : Typeâ‚ : Typeâ‚‚ : Typeâ‚ƒ : ...
```

### Rules

```
Nat : Setâ‚€         -- Nat is a small type
Setâ‚€ : Setâ‚        -- Setâ‚€ itself is in Setâ‚
List Setâ‚€ : Setâ‚   -- List of types is in Setâ‚
```

### Universe Polymorphism

Rather than duplicating definitions for each universe level:

```agda
-- Without universe polymorphism:
idâ‚€ : {A : Setâ‚€} â†’ A â†’ A
idâ‚ : {A : Setâ‚} â†’ A â†’ A
...

-- With universe polymorphism:
id : {â„“ : Level} {A : Set â„“} â†’ A â†’ A
id x = x
```

### Cumulativity

Some systems (Coq, Lean) have cumulative universes:
```
If A : Setáµ¢, then A : Setâ±¼ for all j â‰¥ i
```

Agda has non-cumulative universes by default.

## 2.4 Identity Types (Propositional Equality)

Identity types allow reasoning about equality within the type system.

### Formation

```
Î“ âŠ¢ A : Type    Î“ âŠ¢ a : A    Î“ âŠ¢ b : A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
           Î“ âŠ¢ a â‰¡ b : Type
```

### Introduction (Reflexivity)

```
    Î“ âŠ¢ a : A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ refl : a â‰¡ a
```

### Elimination (J Rule / Path Induction)

```
Î“ âŠ¢ C : (x y : A) â†’ (x â‰¡ y) â†’ Type
Î“ âŠ¢ c : (x : A) â†’ C x x refl
Î“ âŠ¢ p : a â‰¡ b
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
       Î“ âŠ¢ J C c p : C a b p
```

### Intensional vs Extensional

**Intensional (Agda, Lean, Idris):**
- `refl` is the only canonical proof of `a â‰¡ a`
- Function extensionality is not provable
- Type checking is decidable

**Extensional:**
- Equality reflection: if `p : a â‰¡ b`, then `a` and `b` are definitionally equal
- Function extensionality is provable
- Type checking is undecidable

## 2.5 Inductive Types and Families

### Ordinary Inductive Types

```agda
data Nat : Set where
  zero : Nat
  suc  : Nat â†’ Nat
```

### Indexed Inductive Families

```agda
data Vec (A : Set) : Nat â†’ Set where
  []  : Vec A zero
  _âˆ·_ : {n : Nat} â†’ A â†’ Vec A n â†’ Vec A (suc n)
```

The type `Vec A n` is **indexed** by the natural number `n`.

### Elimination Principles

Every inductive type generates an elimination principle (recursor/induction principle):

```agda
-- Induction principle for Nat
nat-ind : {P : Nat â†’ Set}
        â†’ P zero
        â†’ ((n : Nat) â†’ P n â†’ P (suc n))
        â†’ (n : Nat) â†’ P n
```

---

# PART III: DEPENDENT PATTERN MATCHING

## 3.1 Basic Dependent Pattern Matching

Dependent pattern matching extends ordinary pattern matching to handle indexed families.

### Example: Vector Head

```agda
head : {A : Set} {n : Nat} â†’ Vec A (suc n) â†’ A
head (x âˆ· xs) = x
-- No case for [] needed: the index (suc n) rules it out!
```

### Example: Vector Append

```agda
_++_ : {A : Set} {m n : Nat} â†’ Vec A m â†’ Vec A n â†’ Vec A (m + n)
[]       ++ ys = ys
(x âˆ· xs) ++ ys = x âˆ· (xs ++ ys)
```

The type checker verifies that:
- `[] ++ ys : Vec A (zero + n)` which equals `Vec A n` âœ“
- `(x âˆ· xs) ++ ys : Vec A (suc m + n)` which equals `Vec A (suc (m + n))` âœ“

## 3.2 Elimination with a Motive

Pattern matching on indexed types requires a **motive** â€” a type family that specifies what you're proving at each index.

### The J Eliminator

For identity types:
```
J : (C : (y : A) â†’ (x â‰¡ y) â†’ Type)
  â†’ (c : C x refl)
  â†’ (y : A) â†’ (p : x â‰¡ y) â†’ C y p
```

The motive `C` specifies how the result type varies with the equality proof.

### McBride's "Elimination with a Motive"

Pattern matching can be translated to eliminators by:
1. Computing a motive from the goal type and patterns
2. Providing methods for each constructor case
3. Handling recursive calls through induction hypotheses

## 3.3 Dot Patterns

When a pattern is **forced** by other patterns, it's written with a dot:

```agda
data Square : Nat â†’ Set where
  sq : (n : Nat) â†’ Square (n * n)

root : (n : Nat) â†’ Square (n * n) â†’ Nat
root n (sq .n) = n
-- The .n indicates this value is forced to be n
```

## 3.4 Absurd Patterns

When a case is impossible, we use absurd patterns:

```agda
empty-vec-no-head : {A : Set} â†’ Vec A zero â†’ âŠ¥
empty-vec-no-head ()  -- () marks impossible case
```

## 3.5 With-Abstraction (Agda)

Agda's `with` allows pattern matching on intermediate computations:

```agda
filter : {A : Set} â†’ (A â†’ Bool) â†’ List A â†’ List A
filter p []       = []
filter p (x âˆ· xs) with p x
... | true  = x âˆ· filter p xs
... | false = filter p xs
```

---

# PART IV: MAJOR IMPLEMENTATIONS

## 4.1 Agda

### Overview

Agda is a dependently-typed functional programming language and proof assistant developed at Chalmers University. It is the most direct descendant of Martin-LÃ¶f Type Theory.

### Key Features

| Feature | Description |
|---------|-------------|
| **Foundation** | Martin-LÃ¶f Type Theory with inductive families |
| **Totality** | Total language (termination/coverage checking) |
| **Unicode** | Full Unicode support in identifiers and mixfix operators |
| **Holes** | Interactive development with typed holes |
| **Proof mode** | Interactive proof construction via Emacs mode |
| **FFI** | Haskell FFI for practical programming |

### Type System Features

```agda
-- Universe polymorphism
id : âˆ€ {â„“} {A : Set â„“} â†’ A â†’ A
id x = x

-- Implicit arguments (inferred)
head : {A : Set} {n : Nat} â†’ Vec A (suc n) â†’ A

-- Instance arguments (type class-like)
show : {A : Set} {{_ : Show A}} â†’ A â†’ String

-- Sized types (termination)
data Colist (A : Set) (i : Size) : Set where
  []  : Colist A i
  _âˆ·_ : A â†’ Thunk (Colist A) i â†’ Colist A i
```

### Cubical Agda

Agda supports Cubical Type Theory for homotopy type theory:

```agda
{-# OPTIONS --cubical #-}

-- Function extensionality is provable
funExt : {A B : Type} {f g : A â†’ B}
       â†’ ((x : A) â†’ f x â‰¡ g x) â†’ f â‰¡ g
```

### Agda for TERAS Analysis

**Strengths:**
- Most faithful to type-theoretic foundations
- Excellent for formalization and proofs
- Mature ecosystem for verification
- Interactive development with holes

**Limitations:**
- No efficient runtime (targets Haskell)
- No built-in resource/linearity tracking
- Termination checker can be restrictive

## 4.2 Idris / Idris 2

### Overview

Idris is designed as a **general-purpose programming language** with dependent types, rather than primarily a proof assistant. Idris 2 is a complete rewrite based on Quantitative Type Theory (QTT).

### Idris 1 Features

```idris
-- First-class dependent types
data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a

-- Type providers (metaprogramming)
%provide (x : Integer) with fromFile "data.txt"

-- Implicit arguments
append : Vect n a -> Vect m a -> Vect (n + m) a
```

### Idris 2 and Quantitative Type Theory

Idris 2's key innovation is **Quantitative Type Theory (QTT)**, which tracks how many times each variable is used:

```idris
-- Multiplicities: 0 (erased), 1 (linear), Ï‰ (unrestricted)

-- Linear function: argument used exactly once
dup : (1 x : a) -> (a, a)  -- TYPE ERROR: x used twice!

-- Erased argument: not available at runtime
length : (0 xs : List a) -> Nat
length [] = 0
length (x :: xs) = 1 + length xs

-- Unrestricted: normal usage
map : (a -> b) -> List a -> List b
```

### Linear Types Integration

```idris
-- Linear channels for session types
data Chan : Protocol -> Type

-- Send on a linear channel (consumes channel, returns new state)
send : (1 chan : Chan (Send ty rest)) -> ty -> Chan rest

-- Resource-safe file handling
withFile : String -> (1 _ : File -> IO (Res a File)) -> IO a
```

### Idris for TERAS Analysis

**Strengths:**
- QTT unifies dependent and linear types
- Designed for practical programming
- Erasure inference reduces runtime overhead
- Session types and resource tracking

**Limitations:**
- Smaller ecosystem than Agda/Coq
- Idris 2 still maturing
- Less proof automation

## 4.3 Lean / Lean 4

### Overview

Lean is a theorem prover and programming language developed by Leonardo de Moura at Microsoft Research. Lean 4 is a complete reimplementation that can compile to efficient C code.

### Key Features

| Feature | Description |
|---------|-------------|
| **Foundation** | Calculus of Inductive Constructions |
| **Self-hosting** | Lean 4 is implemented in Lean |
| **Performance** | Compiles to efficient C code |
| **Metaprogramming** | Powerful macro system |
| **Mathlib** | Large mathematical library (210,000+ theorems) |

### Lean 4 Syntax

```lean
-- Type definitions
inductive Vec (Î± : Type) : Nat â†’ Type where
  | nil : Vec Î± 0
  | cons : Î± â†’ Vec Î± n â†’ Vec Î± (n + 1)

-- Dependent pattern matching
def head : Vec Î± (n + 1) â†’ Î±
  | Vec.cons x _ => x

-- Tactics for proofs
theorem vec_length_add (xs : Vec Î± m) (ys : Vec Î± n) :
    length (xs ++ ys) = m + n := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih]
```

### Functional but In-Place

Lean 4 uses reference counting with **reuse analysis** for efficient functional programming:

```lean
-- Pure code that performs destructive updates when safe
def mapTree (f : Î± â†’ Î²) : Tree Î± â†’ Tree Î²
  | .leaf x => .leaf (f x)
  | .node l r => .node (mapTree f l) (mapTree f r)
-- If the input tree is uniquely owned, updates happen in-place
```

### Type Classes

```lean
class Add (Î± : Type) where
  add : Î± â†’ Î± â†’ Î±

instance : Add Nat where
  add := Nat.add

#check (Add.add : {Î± : Type} â†’ [Add Î±] â†’ Î± â†’ Î± â†’ Î±)
```

### Lean for TERAS Analysis

**Strengths:**
- Efficient compiled code generation
- Powerful metaprogramming for automation
- Large mathematical library (mathlib)
- Active community and development
- Good for both programming and proofs

**Limitations:**
- No built-in linear/resource types
- Non-cumulative universes require management
- Mathlib conventions can be heavyweight

## 4.4 Comparison Summary

| Feature | Agda | Idris 2 | Lean 4 |
|---------|------|---------|--------|
| **Foundation** | MLTT | QTT | CIC |
| **Linear types** | No (external) | Yes (built-in) | No |
| **Universes** | Non-cumulative | Cumulative | Non-cumulative |
| **Tactics** | Reflection | Basic | Powerful |
| **Runtime** | Haskell backend | Chez Scheme | C codegen |
| **Primary use** | Proofs | Programming | Both |
| **Ecosystem** | Medium | Small | Large (mathlib) |
| **Totality** | Enforced | Enforced | Partial support |

---

# PART V: TYPE INFERENCE AND DECIDABILITY

## 5.1 The Decidability Challenge

Full type inference is **undecidable** for dependent types because:
1. Type equality may require arbitrary computation
2. Unification becomes higher-order
3. Implicit argument inference may not terminate

### Contrast with Hindley-Milner

| Property | Hindley-Milner | Dependent Types |
|----------|---------------|-----------------|
| Principal types | Always exist | May not exist |
| Type inference | Decidable | Undecidable |
| Type checking | Decidable | Decidable (intensional) |
| Annotations | Optional | Often required |

## 5.2 Bidirectional Type Checking

The standard approach for dependent types is **bidirectional type checking**, which splits typing into two modes:

### Synthesis (â†‘) vs Checking (â†“)

```
Î“ âŠ¢ e â‡’ A    -- term e synthesizes type A
Î“ âŠ¢ e â‡ A    -- term e checks against type A
```

### Key Rules

```
-- Variables synthesize
  (x : A) âˆˆ Î“
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  Î“ âŠ¢ x â‡’ A

-- Annotated terms synthesize
   Î“ âŠ¢ e â‡ A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ (e : A) â‡’ A

-- Lambda checks (given expected type)
   Î“, x : A âŠ¢ e â‡ B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ Î»x. e â‡ Î (x : A). B

-- Application synthesizes
Î“ âŠ¢ f â‡’ Î (x : A). B    Î“ âŠ¢ a â‡ A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
        Î“ âŠ¢ f a â‡’ B[a/x]

-- Mode switch
Î“ âŠ¢ e â‡’ A    A â‰¡ B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
     Î“ âŠ¢ e â‡ B
```

### Benefits of Bidirectional Typing

1. **Decidable** â€” Type checking terminates
2. **Predictable annotations** â€” Clear rules for when annotations are needed
3. **Good error messages** â€” Errors localized to specific subterms
4. **Composable** â€” Easily extended with new features

## 5.3 Implicit Arguments

Implicit arguments are inferred rather than explicitly provided:

```agda
-- Explicit argument
id-explicit : (A : Set) â†’ A â†’ A
id-explicit A x = x

-- Implicit argument (inferred from usage)
id : {A : Set} â†’ A â†’ A
id x = x

-- Usage: A is inferred
test : Nat
test = id 42  -- A = Nat inferred
```

### Inference Mechanisms

1. **Unification** â€” Match expected type with synthesized type
2. **Instance search** â€” Type class resolution
3. **Metavariables** â€” Defer resolution, solve constraints later

## 5.4 Higher-Order Unification

Dependent type inference often requires **higher-order unification**:

```
?F x â‰¡ x + x    -- Find F such that F x = x + x
-- Solution: F = Î»x. x + x
```

Higher-order unification is undecidable in general, so systems use:
- **Pattern fragment** â€” Decidable subset (Miller patterns)
- **Heuristics** â€” Best-effort guessing
- **User annotation** â€” Require hints when stuck

---

# PART VI: SECURITY APPLICATIONS

## 6.1 Type-Level Security Invariants

Dependent types enable encoding security properties directly in types:

### Length-Indexed Types for Buffer Safety

```agda
-- No buffer overflows possible
data Buffer : Nat â†’ Type where
  mkBuffer : (size : Nat) â†’ Vec Word8 size â†’ Buffer size

-- Reading requires bounds proof
readAt : (buf : Buffer n) â†’ (i : Fin n) â†’ Word8
```

### Authentication State Machines

```agda
data AuthState : Type where
  Unauthenticated : AuthState
  Authenticated : UserId â†’ AuthState

data Session : AuthState â†’ Type where
  Guest : Session Unauthenticated
  LoggedIn : (u : UserId) â†’ Token u â†’ Session (Authenticated u)

-- Only authenticated users can access protected resources
accessProtected : Session (Authenticated u) â†’ ProtectedData â†’ Response
```

## 6.2 Protocol Verification

Dependent types can verify protocol correctness:

```idris
-- TLS handshake state machine
data TLSState : Type where
  Initial : TLSState
  ClientHello : TLSState
  ServerHello : TLSState
  KeyExchange : TLSState
  Encrypted : SessionKey â†’ TLSState

-- State-indexed operations
sendClientHello : TLS Initial â†’ IO (TLS ClientHello)
receiveServerHello : TLS ClientHello â†’ IO (TLS ServerHello)
establishKey : TLS ServerHello â†’ IO (k ** TLS (Encrypted k))
```

## 6.3 Information Flow Control

Dependent types can track information flow:

```agda
data SecLevel : Type where
  Public : SecLevel
  Secret : SecLevel

_âŠ‘_ : SecLevel â†’ SecLevel â†’ Type
Public âŠ‘ _      = âŠ¤
Secret âŠ‘ Secret = âŠ¤
Secret âŠ‘ Public = âŠ¥

data Labeled : SecLevel â†’ Type â†’ Type where
  label : {l : SecLevel} â†’ a â†’ Labeled l a

-- Declassification requires proof
declassify : {lâ‚ lâ‚‚ : SecLevel} â†’ lâ‚ âŠ‘ lâ‚‚ â†’ Labeled lâ‚ a â†’ Labeled lâ‚‚ a
```

## 6.4 Cryptographic Protocol Types (F*)

F* (F-star) combines dependent types with effects for crypto:

```fstar
// Refinement types for cryptographic values
type key = b:bytes{length b = 32}
type nonce = b:bytes{length b = 24}

// Authenticated encryption with dependent result type
val encrypt : key â†’ nonce â†’ plaintext â†’ 
              (c:ciphertext{length c = length plaintext + 16})

// MAC verification returns proof
val verify : key â†’ tag â†’ msg â†’ option (p:unit{authentic key msg})
```

## 6.5 Dependent Session Types

Combining session types (A-07) with dependent types:

```idris
-- Value-dependent protocol
data AuthProtocol : Type where
  Auth : (n : Nat) â†’                  -- attempt number
         Send String â†’                -- username
         Send String â†’                -- password
         Recv (Either (AuthToken n) (LT n 3, AuthProtocol)) â†’
         AuthProtocol

-- After 3 failures, protocol terminates
```

---

# PART VII: ADVANCED TOPICS

## 7.1 Totality and Termination

Dependent type systems typically require **total** functions:

### Termination Checking

```agda
-- Structurally recursive (accepted)
factorial : Nat â†’ Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

-- Not structurally recursive (rejected without help)
ackermann : Nat â†’ Nat â†’ Nat
ackermann zero n = suc n
ackermann (suc m) zero = ackermann m (suc zero)
ackermann (suc m) (suc n) = ackermann m (ackermann (suc m) n)
-- Requires well-founded recursion or sized types
```

### Coverage Checking

Pattern matching must be exhaustive and handle all cases.

## 7.2 Sized Types (Agda)

Sized types help with termination of corecursive definitions:

```agda
data Stream (A : Set) (i : Size) : Set where
  _âˆ·_ : A â†’ Thunk (Stream A) i â†’ Stream A i

-- Guarded by productivity
map : {A B : Set} {i : Size} â†’ (A â†’ B) â†’ Stream A i â†’ Stream B i
map f (x âˆ· xs) = f x âˆ· Î» where .force â†’ map f (xs .force)
```

## 7.3 Elaboration and Metaprogramming

### Agda Reflection

```agda
-- Quote a term to its syntax tree
macro
  test : Term â†’ TC âŠ¤
  test hole = unify hole (lit (nat 42))
```

### Lean 4 Metaprogramming

```lean
-- Hygienic macros
macro "myMatch" x:term "with" alts:matchAlts : term => do
  `(match $x with $alts)

-- Tactics as metaprograms
elab "myTactic" : tactic => do
  let goal â† getMainGoal
  ...
```

## 7.4 Observational Type Theory

OTT (Altenkirch et al.) provides function extensionality without losing decidability:

```
-- Functions are equal if observationally equal
f â‰¡ g âŸº âˆ€ x. f x â‰¡ g x
```

## 7.5 Setoid-Based Approaches

When equality is too fine-grained:

```agda
record Setoid : Setâ‚ where
  field
    Carrier : Set
    _â‰ˆ_     : Carrier â†’ Carrier â†’ Set
    refl    : âˆ€ x â†’ x â‰ˆ x
    sym     : âˆ€ {x y} â†’ x â‰ˆ y â†’ y â‰ˆ x
    trans   : âˆ€ {x y z} â†’ x â‰ˆ y â†’ y â‰ˆ z â†’ x â‰ˆ z
```

---

# PART VIII: INTEGRATION WITH OTHER TYPE FEATURES

## 8.1 Dependent Types + Linear Types

Idris 2's QTT shows successful integration:

```idris
-- Multiplicity annotations on dependent types
data Vec : Nat â†’ Type â†’ Type where
  Nil  : Vec 0 a
  (::) : (1 x : a) â†’ (1 xs : Vec n a) â†’ Vec (S n) a

-- Linear function over dependent type
mapL : (1 f : a â†’ b) â†’ (1 xs : Vec n a) â†’ Vec n b
```

### Challenges

1. **Index erasure** â€” Indices often don't need runtime representation
2. **Multiplicity inference** â€” When can we infer multiplicities?
3. **Interaction rules** â€” How do multiplicities affect dependent elimination?

## 8.2 Dependent Types + Refinement Types

Refinement types (A-03) are a restricted form of dependent types:

```
{x : Int | x > 0}  â‰ˆ  Î£(x : Int). (x > 0)
```

Key differences:
- Refinements use SMT solvers (decidable fragments)
- Full dependent types allow arbitrary proofs

F* bridges these:
```fstar
type nat = x:int{x >= 0}  // Refinement
val length : list a â†’ nat  // Inferred refinements
```

## 8.3 Dependent Types + Effects

Combining dependent types with effect systems (A-05):

```idris
-- State effect indexed by pre/post state types
data State : (s : Type) â†’ Effect where
  Get : State s s s
  Put : s â†’ State s () s

-- Dependently-typed state transformer
withVec : (n : Nat) â†’ Eff [State (Vec n Int)] a â†’ a
```

## 8.4 Dependent Types + Session Types

Session types (A-07) with dependent protocols:

```
-- Protocol depends on received value
DepSession = (n : Nat) &â†’ repeat n (Int !â†’ End)
```

---

# PART IX: TERAS-LANG IMPLICATIONS

## 9.1 What TERAS-LANG Needs from Dependent Types

| Need | Dependent Types Solution |
|------|-------------------------|
| Array bounds safety | Length-indexed vectors |
| Protocol verification | State-indexed session types |
| Crypto constraints | Refinement-checked key sizes |
| Resource tracking | Linear + dependent (QTT) |
| Proof generation | Curry-Howard correspondence |

## 9.2 Design Considerations

### Universe Strategy

Options for TERAS-LANG:
1. **Cumulative** (like Coq) â€” Simpler for users
2. **Non-cumulative with lifting** (like Agda) â€” More control
3. **Universe polymorphism** â€” Generic over levels

**Recommendation:** Cumulative with explicit lifting for when needed.

### Implicit Arguments

Strategy:
1. **Bidirectional inference** â€” Core mechanism
2. **Instance arguments** â€” For type class-like patterns
3. **User annotations** â€” Required at definition boundaries

### Pattern Matching

Options:
1. **Eliminators only** â€” Simplest, verbose
2. **Dependent patterns** â€” With Axiom K (traditional)
3. **Without K** â€” HoTT-compatible

**Recommendation:** Dependent pattern matching without K for maximum generality.

## 9.3 Integration with Existing TERAS-LANG Features

### With Linear Types (A-04)

Follow Idris 2's QTT approach:
- Multiplicities on binders, not types
- Erasure annotation for indices
- Linearity preserved through dependent elimination

### With Refinement Types (A-03)

Layered approach:
- SMT-backed refinements for decidable properties
- Full dependent types for complex proofs
- Automatic lifting from refinements to proofs

### With Session Types (A-07)

Value-dependent protocols:
- Protocol progression depends on transmitted values
- Linear channel ownership
- Dependent session type verification

## 9.4 Complexity Budget

Dependent types add significant complexity:
- Type checking more expensive
- Error messages harder to understand
- Learning curve steeper

**Mitigation strategies:**
1. Good defaults and inference
2. Clear error messages with context
3. Gradual adoption (start simple, add dependencies as needed)
4. IDE support with interactive development

---

# PART X: REFERENCES

## Key Papers

1. Martin-LÃ¶f, P. (1984). "Intuitionistic Type Theory"
2. Coquand, T. & Huet, G. (1988). "The Calculus of Constructions"
3. Norell, U. (2007). "Towards a practical programming language based on dependent type theory" (Agda)
4. Brady, E. (2013). "Idris, a general-purpose dependently typed programming language"
5. Brady, E. (2021). "Idris 2: Quantitative Type Theory in Practice"
6. de Moura, L. & Ullrich, S. (2021). "The Lean 4 Theorem Prover and Programming Language"
7. McBride, C. (2002). "Elimination with a Motive"
8. Goguen, H., McBride, C., McKinna, J. (2006). "Eliminating Dependent Pattern Matching"
9. Dunfield, J. & Krishnaswami, N. (2013). "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism"
10. Atkey, R. (2018). "The Syntax and Semantics of Quantitative Type Theory"

## Language Documentation

- Agda: https://agda.readthedocs.io/
- Idris 2: https://idris2.readthedocs.io/
- Lean 4: https://lean-lang.org/theorem_proving_in_lean4/

## Textbooks

- "Certified Programming with Dependent Types" (Chlipala, 2013)
- "The Little Typer" (Friedman & Christiansen, 2018)
- "Type-Driven Development with Idris" (Brady, 2017)

---

**Document SHA-256:** To be computed on final version
**Word Count:** ~4,500 words
**Status:** COMPLETE â€” Ready for comparison and decision documents
