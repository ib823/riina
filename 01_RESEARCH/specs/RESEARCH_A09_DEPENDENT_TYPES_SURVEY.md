# TERAS RESEARCH SURVEY: DEPENDENT TYPES
## Session A-09: Agda, Idris, Lean, and Dependent Type Theory

**Document ID:** RESEARCH_A09_DEPENDENT_TYPES_SURVEY  
**Version:** 1.0.0  
**Date:** 2026-01-03  
**Status:** COMPLETE  
**Classification:** TERAS Research Track - Domain A (Type Theory)

---

## PART I: FOUNDATIONS OF DEPENDENT TYPES

### 1.1 What Are Dependent Types?

Dependent types are types that depend on values. Unlike simple types where `List Int` is a fixed type, dependent types allow `Vec n Int` where `n` is a value determining the vector's length. This enables types to express properties about values, blurring the line between types and propositions.

**The Curry-Howard Correspondence Extended:**
```
Simple Types          Propositional Logic
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
A â†’ B                 A implies B
A Ã— B                 A and B
A + B                 A or B

Dependent Types       Predicate Logic
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î (x:A).B(x)          âˆ€x:A. B(x)
Î£(x:A).B(x)          âˆƒx:A. B(x)
```

**Core Dependent Type Formers:**

1. **Dependent Function Types (Î -types):**
   ```
   Î (x:A).B(x)   or   (x : A) â†’ B x
   
   Formation:  Î“ âŠ¢ A : Type    Î“, x:A âŠ¢ B : Type
              â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                     Î“ âŠ¢ Î (x:A).B : Type
   
   Introduction:  Î“, x:A âŠ¢ t : B
                 â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                 Î“ âŠ¢ Î»x.t : Î (x:A).B
   
   Elimination:   Î“ âŠ¢ f : Î (x:A).B    Î“ âŠ¢ a : A
                 â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                        Î“ âŠ¢ f a : B[a/x]
   ```

2. **Dependent Pair Types (Î£-types):**
   ```
   Î£(x:A).B(x)   or   (x : A) Ã— B x
   
   Formation:  Î“ âŠ¢ A : Type    Î“, x:A âŠ¢ B : Type
              â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                     Î“ âŠ¢ Î£(x:A).B : Type
   
   Introduction:  Î“ âŠ¢ a : A    Î“ âŠ¢ b : B[a/x]
                 â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                    Î“ âŠ¢ (a, b) : Î£(x:A).B
   
   Elimination:  Î“ âŠ¢ p : Î£(x:A).B    Î“, x:A, y:B âŠ¢ C : Type
                 Î“, z:Î£(x:A).B âŠ¢ c : C[(Ï€â‚ z, Ï€â‚‚ z)/z]
                â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                 Î“ âŠ¢ match p with (x,y) â‡’ c : C[p/z]
   ```

### 1.2 Historical Development

**Timeline of Dependent Type Theory:**

| Year | Development | Contributor |
|------|-------------|-------------|
| 1971 | Intuitionistic Type Theory | Martin-LÃ¶f |
| 1972 | System F (polymorphism) | Girard |
| 1984 | Calculus of Constructions | Coquand & Huet |
| 1985 | NuPRL proof assistant | Constable et al. |
| 1989 | Coq proof assistant | INRIA |
| 1999 | Agda 1.0 | Catarina Coquand |
| 2007 | Agda 2.0 | Norell |
| 2011 | Idris 1.0 | Brady |
| 2013 | Lean | de Moura |
| 2017 | Idris 2 | Brady |
| 2021 | Lean 4 | de Moura et al. |

### 1.3 Universes and Type Hierarchies

**The Universe Hierarchy:**
```
Typeâ‚€ : Typeâ‚ : Typeâ‚‚ : Typeâ‚ƒ : ...

where:
  - Typeâ‚€ contains "small" types (Bool, Nat, List Nat, ...)
  - Typeâ‚ contains Typeâ‚€ and functions over Typeâ‚€
  - Type_n contains Type_{n-1} and functions over it
```

**Universe Polymorphism:**
```agda
-- Agda: universe levels explicit
id : {l : Level} â†’ {A : Set l} â†’ A â†’ A
id x = x

-- Can instantiate at any level
idNat : Nat â†’ Nat
idNat = id {lzero} {Nat}

idType : Set â†’ Set
idType = id {lsuc lzero} {Set}
```

**Predicative vs Impredicative:**
- **Predicative:** Î (x:Type_i).B is in Type_i only if B is in Type_i for all x
- **Impredicative:** Î (x:Type_i).B can be in Type_i even if quantifying over Type_i

Agda and Lean are predicative by default. Coq's Prop is impredicative.

---

## PART II: AGDA - THE DEPENDENTLY TYPED RESEARCH LANGUAGE

### 2.1 Overview and Philosophy

**Agda** is a dependently typed functional programming language developed at Chalmers University. It serves as both a programming language and a proof assistant, emphasizing:
- Clean, readable syntax inspired by Haskell
- Pattern matching with dependent types
- Universe polymorphism
- No tactics (proofs are programs)
- Focus on type-theoretic foundations

### 2.2 Core Language Features

**Inductive Data Types:**
```agda
-- Natural numbers
data â„• : Set where
  zero : â„•
  suc  : â„• â†’ â„•

-- Length-indexed vectors
data Vec (A : Set) : â„• â†’ Set where
  []  : Vec A zero
  _âˆ·_ : {n : â„•} â†’ A â†’ Vec A n â†’ Vec A (suc n)

-- Finite sets (bounded naturals)
data Fin : â„• â†’ Set where
  zero : {n : â„•} â†’ Fin (suc n)
  suc  : {n : â„•} â†’ Fin n â†’ Fin (suc n)
```

**Safe Vector Indexing:**
```agda
-- Type-safe indexing: impossible to index out of bounds
lookup : {A : Set} {n : â„•} â†’ Vec A n â†’ Fin n â†’ A
lookup (x âˆ· xs) zero    = x
lookup (x âˆ· xs) (suc i) = lookup xs i

-- Note: lookup [] i is impossible - no constructor for Fin zero
```

**Dependent Pattern Matching:**
```agda
-- Vector append with length proof
_++_ : {A : Set} {m n : â„•} â†’ Vec A m â†’ Vec A n â†’ Vec A (m + n)
[]       ++ ys = ys
(x âˆ· xs) ++ ys = x âˆ· (xs ++ ys)

-- The type checker verifies:
-- [] ++ ys : Vec A (zero + n) â‰¡ Vec A n  âœ“
-- (x âˆ· xs) ++ ys : Vec A (suc m + n) â‰¡ Vec A (suc (m + n))  âœ“
```

### 2.3 Propositional Equality in Agda

**The Identity Type:**
```agda
data _â‰¡_ {A : Set} (x : A) : A â†’ Set where
  refl : x â‰¡ x

-- Symmetry
sym : {A : Set} {x y : A} â†’ x â‰¡ y â†’ y â‰¡ x
sym refl = refl

-- Transitivity
trans : {A : Set} {x y z : A} â†’ x â‰¡ y â†’ y â‰¡ z â†’ x â‰¡ z
trans refl refl = refl

-- Congruence
cong : {A B : Set} {x y : A} â†’ (f : A â†’ B) â†’ x â‰¡ y â†’ f x â‰¡ f y
cong f refl = refl
```

**With-Abstraction for Dependent Matching:**
```agda
-- Need to match on equality proof to unify types
filter : {A : Set} {n : â„•} â†’ (A â†’ Bool) â†’ Vec A n â†’ Î£ â„• (Vec A)
filter p []       = (zero , [])
filter p (x âˆ· xs) with p x | filter p xs
... | true  | (m , ys) = (suc m , x âˆ· ys)
... | false | (m , ys) = (m , ys)
```

### 2.4 Agda's Module System

```agda
module Container where
  
  record Container : Setâ‚ where
    field
      Shape    : Set
      Position : Shape â†’ Set

  open Container

  -- Interpretation as a functor
  âŸ¦_âŸ§ : Container â†’ Set â†’ Set
  âŸ¦ C âŸ§ X = Î£ (Shape C) (Î» s â†’ Position C s â†’ X)

  -- Container morphisms
  record _â‡’_ (C D : Container) : Set where
    field
      shape    : Shape C â†’ Shape D
      position : {s : Shape C} â†’ Position D (shape s) â†’ Position C s
```

### 2.5 Instance Arguments (Type Classes)

```agda
record Eq (A : Set) : Set where
  field
    _==_ : A â†’ A â†’ Bool

open Eq {{...}}

-- Instance declaration
instance
  Eq-â„• : Eq â„•
  Eq-â„• = record { _==_ = natEq }

-- Instance argument resolved automatically
elem : {A : Set} {{_ : Eq A}} â†’ A â†’ List A â†’ Bool
elem x []       = false
elem x (y âˆ· ys) = if x == y then true else elem x ys
```

### 2.6 Agda's Termination Checker

Agda requires all functions to be terminating. It uses structural recursion analysis:

```agda
-- Terminates: recursive call on structurally smaller argument
length : {A : Set} â†’ List A â†’ â„•
length []       = zero
length (x âˆ· xs) = suc (length xs)

-- Does not terminate: Agda rejects
-- bad : â„• â†’ â„•
-- bad n = bad (suc n)

-- Termination pragmas for complex cases
{-# TERMINATING #-}
ack : â„• â†’ â„• â†’ â„•
ack zero    m       = suc m
ack (suc n) zero    = ack n (suc zero)
ack (suc n) (suc m) = ack n (ack (suc n) m)
```

### 2.7 Sized Types

Sized types provide more precise termination checking:

```agda
{-# BUILTIN SIZEUNIV SizeUniv #-}
{-# BUILTIN SIZE Size #-}
{-# BUILTIN SIZELT Size<_ #-}
{-# BUILTIN SIZESUC â†‘_ #-}
{-# BUILTIN SIZEINF âˆž #-}

data Nat : {i : Size} â†’ Set where
  zero : {i : Size} â†’ Nat {â†‘ i}
  suc  : {i : Size} â†’ Nat {i} â†’ Nat {â†‘ i}

-- Size-aware recursion
div2 : {i : Size} â†’ Nat {i} â†’ Nat {i}
div2 zero          = zero
div2 (suc zero)    = zero
div2 (suc (suc n)) = suc (div2 n)
```

---

## PART III: IDRIS - DEPENDENT TYPES FOR PRACTICAL PROGRAMMING

### 3.1 Overview and Philosophy

**Idris** (and Idris 2) was designed by Edwin Brady to bring dependent types to practical programming. Key differences from Agda:
- Focuses on being a general-purpose language
- Supports side effects through algebraic effects
- Linear types (Idris 2)
- Compiles to efficient code
- Totality is optional (not required)

### 3.2 Basic Dependent Types in Idris

```idris
-- Natural numbers
data Nat = Z | S Nat

-- Vectors with length
data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a

-- Safe head: impossible on empty vector
head : Vect (S n) a -> a
head (x :: xs) = x

-- Append with proof
(++) : Vect n a -> Vect m a -> Vect (n + m) a
(++) Nil       ys = ys
(++) (x :: xs) ys = x :: (xs ++ ys)
```

### 3.3 Proofs as Programs

```idris
-- Propositional equality
data (=) : a -> b -> Type where
  Refl : x = x

-- Plus is commutative (requires proofs)
plusCommutative : (n, m : Nat) -> n + m = m + n
plusCommutative Z     m = plusZeroRightNeutral m
plusCommutative (S k) m = rewrite plusCommutative k m in
                          rewrite plusSuccRightSucc m k in
                          Refl

-- Rewrite uses equality proofs to transform types
```

### 3.4 Implicit and Auto Arguments

```idris
-- Implicit arguments (inferred)
length : {n : Nat} -> Vect n a -> Nat
length {n} _ = n

-- Auto-implicit (instance resolved)
interface Eq a where
  (==) : a -> a -> Bool

elem : Eq a => a -> List a -> Bool
elem x []        = False
elem x (y :: ys) = if x == y then True else elem x ys

-- Default arguments
greet : {default "World" name : String} -> String
greet {name} = "Hello, " ++ name
```

### 3.5 Idris 2: Linear Types

Idris 2 integrates linear types (Quantitative Type Theory):

```idris
-- Linear function type (argument used exactly once)
data Lin : Type -> Type where
  MkLin : (1 _ : a) -> Lin a

-- File handle with linear usage
data File : Type where
  MkFile : FilePtr -> File

-- Linear file operations
openFile : (path : String) -> IO (Either Error (1 _ : File))
readFile : (1 _ : File) -> IO (Either Error (String, (1 _ : File)))
closeFile : (1 _ : File) -> IO ()

-- Usage: file must be used exactly once (closed)
withFile : String -> (File -> IO a) -> IO (Either Error a)
withFile path f = do
  Right (1 file) <- openFile path | Left err => pure (Left err)
  result <- f file
  closeFile file
  pure (Right result)
```

### 3.6 Algebraic Effects in Idris 2

```idris
-- Effect signature
data State : (s : Type) -> Type -> Type where
  Get : State s s
  Put : s -> State s ()

-- Effect handler
runState : s -> Eff [State s] a -> (a, s)
runState st (Pure x)     = (x, st)
runState st (Bind Get k) = runState st (k st)
runState st (Bind (Put s) k) = runState s (k ())

-- Effectful computation
increment : Eff [State Nat] ()
increment = do
  n <- Get
  Put (S n)

-- Run with initial state
test : ((), Nat)
test = runState 0 (do increment; increment; increment)
-- Result: ((), 3)
```

### 3.7 Elaboration Reflection

Idris allows compile-time metaprogramming:

```idris
%language ElabReflection

-- Generate equality decidability
deriveEq : Name -> Elab ()
deriveEq n = do
  [(_, ty)] <- getType n | _ => fail "Not a type"
  -- ... generate Eq implementation ...

-- Usage
data Color = Red | Green | Blue

%runElab deriveEq `{Color}
-- Generates: Eq Color instance
```

---

## PART IV: LEAN - MATHEMATICS AND METAPROGRAMMING

### 4.1 Overview and Philosophy

**Lean** (especially Lean 4) was designed by Leonardo de Moura at Microsoft Research with goals:
- Interactive theorem proving for mathematics
- Efficient verified programming
- Powerful metaprogramming (tactics are Lean programs)
- Performance-oriented compilation

### 4.2 Core Language Features

```lean
-- Inductive types
inductive Nat where
  | zero : Nat
  | succ : Nat â†’ Nat

-- Vectors
inductive Vec (Î± : Type u) : Nat â†’ Type u where
  | nil  : Vec Î± 0
  | cons : Î± â†’ Vec Î± n â†’ Vec Î± (n + 1)

-- Safe indexing
def Vec.get : Vec Î± n â†’ Fin n â†’ Î±
  | cons x xs, âŸ¨0, _âŸ©     => x
  | cons x xs, âŸ¨n + 1, hâŸ© => xs.get âŸ¨n, Nat.lt_of_succ_lt_succ hâŸ©
```

### 4.3 Propositions and Proofs

```lean
-- Proposition type (Prop)
-- Prop : Type (with proof irrelevance)

-- Equality
inductive Eq {Î± : Sort u} (a : Î±) : Î± â†’ Prop where
  | refl : Eq a a

-- Theorems as types, proofs as terms
theorem plus_comm (n m : Nat) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.add_succ, ih]

-- Or as a term:
theorem plus_comm' : âˆ€ n m : Nat, n + m = m + n :=
  fun n m => by induction n <;> simp [*]
```

### 4.4 Lean 4 Tactic Framework

```lean
-- Tactics are Lean 4 programs
syntax "my_tactic" : tactic

macro_rules
  | `(tactic| my_tactic) => `(tactic| (simp; ring))

-- Custom tactic
elab "repeat_assumption" : tactic => do
  for localDecl in â† getLCtx do
    if â† isDefEq (â† getMainTarget) localDecl.type then
      closeMainGoal `($(mkIdent localDecl.userName))
      return
  throwError "no matching assumption"

-- Use tactic
example (h : 1 + 1 = 2) : 1 + 1 = 2 := by repeat_assumption
```

### 4.5 Type Classes in Lean

```lean
-- Type class definition
class Add (Î± : Type u) where
  add : Î± â†’ Î± â†’ Î±

-- Instance
instance : Add Nat where
  add := Nat.add

-- Using type classes
def double [Add Î±] (x : Î±) : Î± := Add.add x x

-- Automatic instance search
#check double 5  -- Nat
```

### 4.6 Monadic Programming

```lean
-- IO monad
def main : IO Unit := do
  IO.println "Enter your name:"
  let name â† IO.getLine
  IO.println s!"Hello, {name}!"

-- State monad
def increment : StateM Nat Unit := do
  let n â† get
  set (n + 1)

-- Combining effects with transformers
def program : StateT Nat IO Unit := do
  increment
  let n â† get
  liftM (IO.println s!"Count: {n}")
```

### 4.7 Lean Mathlib

Mathlib is the mathematical library for Lean, containing formalized mathematics:

```lean
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.Basic

-- Using mathlib theorems
example (X : Type*) [MetricSpace X] (x y z : X) :
    dist x z â‰¤ dist x y + dist y z :=
  dist_triangle x y z

-- Group theory
example (G : Type*) [Group G] (a b : G) :
    (a * b)â»Â¹ = bâ»Â¹ * aâ»Â¹ :=
  mul_inv_rev a b
```

---

## PART V: COMPARISON OF AGDA, IDRIS, AND LEAN

### 5.1 Feature Comparison

| Feature | Agda | Idris 2 | Lean 4 |
|---------|------|---------|--------|
| **Universe Polymorphism** | Yes (explicit levels) | Yes (implicit) | Yes |
| **Proof Irrelevance** | No (by default) | Yes (with Prop) | Yes (Prop) |
| **Tactics** | No (terms only) | Yes (reflection) | Yes (powerful) |
| **Linear Types** | No | Yes (QTT) | No |
| **Effects** | No (monads) | Yes (algebraic) | Monads |
| **Totality** | Required | Optional | Optional |
| **Compilation** | Haskell/JS | Scheme/JS | Native/C |
| **Metaprogramming** | Reflection | Elab reflection | Macros/Elab |
| **Mathematics Focus** | Medium | Low | High |
| **Programming Focus** | Low | High | Medium |

### 5.2 Type Checking Algorithms

**Agda:** Bidirectional type checking with unification
```
infer(Î“, e) : (A, Ïƒ)      -- Infer type and substitution
check(Î“, e, A) : Ïƒ        -- Check term has type

-- Pattern matching:
1. Generate constraints from pattern
2. Unify constraints
3. Check coverage and termination
```

**Idris:** Elaboration to TT (Type Theory core)
```
elab : Raw â†’ Elab TT
-- Raw syntax â†’ Core term
-- Uses tactics internally for holes
```

**Lean 4:** Elaboration with metavariables
```
elaborate : Syntax â†’ ElabM Expr
-- Creates metavariables for unknowns
-- Solves via unification and type class resolution
```

### 5.3 Definitional vs Propositional Equality

```
Definitional (â‰¡):        Propositional (=):
- Checked by computation - Proven by terms
- 2 + 2 â‰¡ 4 (compute)   - âˆ€n. n + 0 = n (need proof)
- Free (no proof term)   - Requires evidence
- Limited               - Unlimited
```

**Approaches:**
- Agda: Relies heavily on definitional equality, sometimes needs rewrite
- Idris: Uses rewrite and proof search
- Lean: Powerful simp tactic for propositional equality

### 5.4 Termination and Totality

| Language | Termination Check | Totality |
|----------|------------------|----------|
| Agda | Structural + sized types | Required (warnings) |
| Idris | Structural + totality pragma | Optional (total/partial) |
| Lean | Structural + well-founded | Optional (partial allowed) |

---

## PART VI: DEPENDENT TYPES FOR SECURITY

### 6.1 Security Type Systems

**Secret Types (Information Flow):**
```agda
-- Security labels
data Label : Set where
  Low  : Label
  High : Label

-- Labeled values
data Labeled : Label â†’ Set â†’ Set where
  label : {l : Label} {A : Set} â†’ A â†’ Labeled l A

-- Can only read at same or higher level
unlabel : {lâ‚ lâ‚‚ : Label} {A : Set} 
        â†’ lâ‚ âŠ‘ lâ‚‚ â†’ Labeled lâ‚ A â†’ Labeled lâ‚‚ A
unlabel _ (label x) = label x
```

**Capability Types:**
```idris
-- Capability as type witness
data Cap : List Permission -> Type where
  MkCap : Cap perms

-- Require capability in type
readFile : Cap [Read] -> String -> IO String
writeFile : Cap [Write] -> String -> String -> IO ()

-- Capability composition
combine : Cap ps -> Cap qs -> Cap (ps ++ qs)
```

### 6.2 Protocol Verification

```agda
-- Protocol state machine as type
data ProtocolState : Set where
  Init     : ProtocolState
  SentKey  : ProtocolState
  RecvKey  : ProtocolState
  Secure   : ProtocolState
  
-- State-indexed channel
data Channel : ProtocolState â†’ Set where
  MkChannel : (s : ProtocolState) â†’ Channel s

-- Typed transitions
sendPublicKey : Channel Init â†’ IO (Channel SentKey)
receivePublicKey : Channel SentKey â†’ IO (Channel RecvKey)
deriveShared : Channel RecvKey â†’ IO (Channel Secure)
sendSecure : Channel Secure â†’ ByteString â†’ IO (Channel Secure)
```

### 6.3 Verified Cryptography

```lean
-- Length-indexed bytes
def Bytes (n : Nat) := Fin n â†’ UInt8

-- Type-safe AES key
def AES256Key := Bytes 32

-- Encryption preserves length relationship
def aes_encrypt (key : AES256Key) (plaintext : Bytes n) : Bytes (round16 n) :=
  sorry -- actual implementation

-- Type prevents mixing key sizes
-- aes_encrypt (key : Bytes 16) -- Type error!
```

### 6.4 Memory Safety with Dependent Types

```idris
-- Bounds-checked array access
data Array : Nat -> Type -> Type where
  MkArray : Vect n a -> Array n a

-- Index type ensures bounds
index : Array n a -> Fin n -> a
index (MkArray v) i = index v i  -- Can't overflow!

-- Safe buffer operations
data Buffer : Nat -> Type where
  MkBuffer : (cap : Nat) -> Ptr -> Buffer cap

write : {n : Nat} -> Buffer cap -> Fin cap -> Vect n UInt8 -> 
        {auto ok : n + finToNat i <= cap} -> IO ()
```

---

## PART VII: ADVANCED TOPICS

### 7.1 Induction-Recursion

Agda supports induction-recursion (simultaneous definition of type and function):

```agda
-- Universe of codes and their interpretation
mutual
  data U : Set where
    `â„•   : U
    `Î    : (a : U) â†’ (El a â†’ U) â†’ U
    `Î£   : (a : U) â†’ (El a â†’ U) â†’ U

  El : U â†’ Set
  El `â„•       = â„•
  El (`Î  a b) = (x : El a) â†’ El (b x)
  El (`Î£ a b) = Î£ (El a) (Î» x â†’ El (b x))
```

### 7.2 Observational Type Theory (OTT)

```
-- OTT distinguishes:
-- - Canonical forms (values)
-- - Neutral terms (blocked computation)
-- - Observations (what we can distinguish)

-- Functional extensionality becomes definitional:
f â‰¡ g  if  âˆ€x. f x â‰¡ g x
```

### 7.3 Setoid Type Theory

```agda
-- Setoid: type with custom equivalence
record Setoid : Setâ‚ where
  field
    Carrier : Set
    _â‰ˆ_     : Carrier â†’ Carrier â†’ Set
    refl    : âˆ€ x â†’ x â‰ˆ x
    sym     : âˆ€ x y â†’ x â‰ˆ y â†’ y â‰ˆ x
    trans   : âˆ€ x y z â†’ x â‰ˆ y â†’ y â‰ˆ z â†’ x â‰ˆ z
```

### 7.4 Quotient Types

```lean
-- Quotient type: type modulo equivalence
def Quotient {Î± : Sort u} (r : Î± â†’ Î± â†’ Prop) : Sort u :=
  Quot r

-- Example: integers as quotient of pairs
def Int' := Quotient (fun (a b : Nat Ã— Nat) => a.1 + b.2 = b.1 + a.2)
```

### 7.5 Higher Inductive Types (Brief)

```
-- HIT: inductive type with path constructors
data Circle : Type where
  base : Circle
  loop : base = base  -- Path constructor!

-- Enables quotients and other constructions
```

---

## PART VIII: PRACTICAL CONSIDERATIONS

### 8.1 Performance

| Language | Compilation | Runtime Performance |
|----------|-------------|-------------------|
| Agda | â†’ Haskell GHC | Good (via GHC) |
| Idris 2 | â†’ Scheme/C | Good |
| Lean 4 | â†’ Native/C | Excellent |

**Lean 4 Performance Features:**
- Reference counting (no GC pauses)
- Specialization
- Unboxing
- Compiler optimizations

### 8.2 Tooling

| Tool | Agda | Idris 2 | Lean 4 |
|------|------|---------|--------|
| **IDE** | Emacs (agda-mode) | VSCode, Vim | VSCode (excellent) |
| **REPL** | Limited | Yes | Yes |
| **Documentation** | Good | Growing | Excellent |
| **Package Manager** | None (use nix) | Pack | Lake |
| **Community Size** | Medium | Small | Large (growing) |

### 8.3 Learning Curve

**Difficulty Ranking (easiest to hardest for newcomers):**
1. **Lean 4** - Best tooling, good error messages, familiar syntax
2. **Idris 2** - Programming-focused, practical examples
3. **Agda** - Pure type theory, requires understanding foundations

### 8.4 Use Cases

| Use Case | Best Choice | Reason |
|----------|-------------|--------|
| Mathematics | Lean 4 | Mathlib, tactics |
| Verified Programs | Idris 2 | Linear types, effects |
| Type Theory Research | Agda | Clean, foundational |
| Industry Adoption | Lean 4 | Performance, tooling |
| Teaching | Idris 2 | Practical focus |

---

## PART IX: TERAS-LANG RELEVANCE

### 9.1 Dependent Types for Security Properties

**Type-Level Security Invariants:**
```
-- TERAS-LANG: Security level in type
type Secret<T, Level> where
  Level: SecurityLevel

-- Operations preserve or raise level
fn process<T, L1, L2>(x: Secret<T, L1>) -> Secret<U, max(L1, L2)>
  where L2 >= L1
```

**Protocol State Machines:**
```
-- TERAS-LANG: Protocol as dependent type
type AuthChannel<State: AuthState>

fn init() -> AuthChannel<Init>
fn challenge(c: AuthChannel<Init>) -> AuthChannel<Challenged>  
fn respond(c: AuthChannel<Challenged>, r: Response) -> AuthChannel<Verified>
fn secure_send(c: AuthChannel<Verified>, msg: Bytes) -> Result<()>
```

### 9.2 Refinement Integration

From A-08 (Refinement Types), integrate with dependent types:
```
-- Dependent + Refinement
type Vec<T, n: Nat> where n >= 0

fn safe_index<T, n: Nat>(v: Vec<T, n>, i: {k: Nat | k < n}) -> T

-- Refinement predicates as dependent types
type Bounded<lo: Int, hi: Int> = {x: Int | lo <= x && x <= hi}
```

### 9.3 Linear + Dependent Integration

From A-04 (Linear Types), combine with dependent types:
```
-- Linear dependent function
type LinVec<T, n: Nat> = lin Vec<T, n>

fn consume_all<T, n: Nat>(v: lin LinVec<T, n>) -> ()
  -- Must consume all n elements exactly once

-- Session types as dependent linear types
type Chan<S: SessionType> = lin uniq Channel<S>
```

### 9.4 Effect + Dependent Integration

From A-05 (Effect Systems):
```
-- Effects indexed by security level
effect SecureIO<Level: SecurityLevel> {
  fn read_secret() -> Secret<Bytes, Level>
  fn write_public(b: Bytes) -> ()  // Only if Level = Public
}

-- Dependent effect constraints
fn process<L: SecurityLevel>(x: Secret<T, L>) 
  -> eff[SecureIO<L>] Secret<U, L>
```

---

## PART X: KEY INSIGHTS AND RECOMMENDATIONS

### 10.1 Key Insights

1. **Types as Specifications:** Dependent types turn types into specifications that can express arbitrary properties about values.

2. **Proofs as Programs:** The Curry-Howard correspondence means writing correct code and proving theorems are the same activity.

3. **Universe Hierarchy:** Careful universe management prevents paradoxes while allowing powerful abstraction.

4. **Termination Matters:** For logical consistency, all functions must terminate (totality checking).

5. **Practical Trade-offs:** Lean 4 shows dependent types can be practical with good tooling and performance.

### 10.2 Recommendations for TERAS-LANG

| Aspect | Recommendation | Rationale |
|--------|----------------|-----------|
| **Foundation** | Lean 4-inspired | Performance, practical focus |
| **Dependent Types** | Full support | Express security invariants |
| **Universes** | Predicative + Type-in-Type option | Simple mental model |
| **Totality** | Optional with annotation | Practical default |
| **Tactics** | Limited, term-focused | Simplicity |
| **Integration** | With linear, refinement, effects | From A-04, A-08, A-05 |

### 10.3 TERAS-LANG Type Hierarchy Proposal

```
-- Universe hierarchy
Typeâ‚€ âŠ‚ Typeâ‚ âŠ‚ Typeâ‚‚ âŠ‚ ...

-- Security-specialized universes
Secretâ‚€ âŠ‚ Secretâ‚ âŠ‚ ...  (for classified data types)
Proof âŠ‚ Typeâ‚€             (proof-irrelevant propositions)

-- Kind system
Kind ::= Type_n | Secret_n | Proof | Effect | Region | Session
```

---

## PART XI: REFERENCES AND FURTHER READING

### Academic Papers
1. Martin-LÃ¶f, P. (1984). "Intuitionistic Type Theory"
2. Norell, U. (2007). "Towards a practical programming language based on dependent type theory"
3. Brady, E. (2013). "Idris, a general-purpose dependently typed programming language"
4. de Moura, L. et al. (2021). "The Lean 4 Theorem Prover and Programming Language"
5. Atkey, R. (2018). "Syntax and Semantics of Quantitative Type Theory"

### Books
1. "Programming in Martin-LÃ¶f's Type Theory" - NordstrÃ¶m et al.
2. "Type-Driven Development with Idris" - Brady
3. "Theorem Proving in Lean 4" - Avigad et al.

### Online Resources
- Agda Wiki: https://wiki.portal.chalmers.se/agda
- Idris 2 Documentation: https://idris2.readthedocs.io
- Lean 4 Documentation: https://lean-lang.org

---

**END OF SURVEY DOCUMENT**

*Document generated for TERAS Research Track - Session A-09*
*Next: RESEARCH_A09_DEPENDENT_TYPES_COMPARISON.md*
