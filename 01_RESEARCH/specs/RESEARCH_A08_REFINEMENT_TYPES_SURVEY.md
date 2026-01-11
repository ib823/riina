# RESEARCH_A08_REFINEMENT_TYPES_SURVEY.md
## TERAS-LANG Research Track A - Session 08
## Topic: Refinement Types (Liquid Haskell, F*)

**Document Version**: 1.0.0
**Created**: 2026-01-03
**Research Phase**: Track A - Type Systems and Formal Foundations
**Prerequisites**: A-01 (MLTT), A-02 (CoC), A-03 (HoTT), A-04 (Linear Types)

---

## 1. EXECUTIVE SUMMARY

Refinement types extend base types with logical predicates that characterize subsets of values, enabling compile-time verification of properties like array bounds, non-negativity, and functional correctness. This survey examines the historical development from Freeman and Pfenning (1991) through modern systems like Liquid Haskell and F*, focusing on the key innovation of combining Hindley-Milner inference with SMT-based predicate abstraction to achieve decidable, automatic verification.

**Key Finding**: Refinement types provide a sweet spot between expressive dependent types and simple ML-style types, offering automatic verification for a wide class of properties while maintaining decidability through restriction to SMT-decidable logics.

---

## 2. HISTORICAL FOUNDATIONS

### 2.1 Origins and Terminology

The concept of refinement types has evolved significantly since its introduction:

**Pre-History (1976-1990)**:
- Cartwright (1976): Refining Lisp datatypes with constraints
- Ada Range Types (1980): Contiguous subsets of integers
- Nordstrom & Petersson (1983): Logical refinements as subsets
- Constable (1986): Refinements as foundation of Nuprl proof assistant
- PVS (Rushby et al. 1998): Predicate subtyping

**Freeman and Pfenning (1991) - "Refinement Types for ML"**:
The seminal paper introduced the term "refinement types" for datasort refinements:
- Layer refinement system on top of ML's type system
- Refine datatypes by restricting available constructors
- Example: List refined to singleton, cons, nil lattice
- Decidable type inference via abstract interpretation

```ml
datatype Î± list = nil | cons of Î± * Î± list
rectype Î± singleton = cons Î± nil
```

This creates a lattice of type refinements where Î± list is at top, with refinements like Î± singleton âˆ¨ Î± nil below it.

**Key Distinction (Xi & Pfenning 1999)**:
- **Datasort refinements** (Freeman-Pfenning): Refine constructor sets
- **Index refinements** (DML): Refine types with index terms
- **Predicate subtypes** (modern usage): {x:T | P(x)} notation

The term "refinement types" has shifted to predominantly mean predicate subtypes, though this is a departure from the original meaning.

### 2.2 Dependent ML (Xi & Pfenning 1998-1999)

Dependent ML introduced index refinements:
- Types indexed by constraint domain terms
- Separation between indexes (compile-time) and runtime values
- Linear arithmetic constraints (decidable via integer linear programming)

```ml
datatype intlist = intNil | intCons of int * intlist
type List(n) (* List indexed by length n *)

append : {m,n:int} List(m) -> List(n) -> List(m+n)
```

**Key Properties**:
- Phase distinction: Indexes erased at runtime
- Constraint solving: NP-complete but practical
- Decidable type checking with tractable constraint domain
- Verified array bounds, red-black trees, binary search

---

## 3. LIQUID TYPES FRAMEWORK

### 3.1 Core Innovation (Rondon, Kawaguchi, Jhala - PLDI 2008)

Liquid Types ("Logically Qualified Data Types") combines:
- Hindley-Milner type inference for shape
- Predicate abstraction for refinements

**Key Insight**: Restrict refinements to conjunctions of user-provided logical qualifiers, enabling decidable inference via fixed-point computation.

**Refinement Type Syntax**:
```
{Î½ : B | P(Î½)}     -- Base type B with predicate P
x:Ï„â‚ â†’ Ï„â‚‚          -- Dependent function type
```

**Liquid Type Variable Îº**:
Instead of arbitrary predicates, use liquid type variables:
```
Îº â‰¡ qâ‚ âˆ§ qâ‚‚ âˆ§ ... âˆ§ qâ‚™ where qáµ¢ âˆˆ Q*
```
where Q* is a finite set of logical qualifiers.

### 3.2 Inference Algorithm

**Three-Step Process**:

1. **Template Generation**: 
   - Invoke HM to determine ML type shape
   - Replace refinements with fresh liquid type variables
   
2. **Constraint Generation**:
   - Generate subtyping constraints between templates
   - Path-sensitive through guard predicates
   
3. **Constraint Solving**:
   - Use predicate abstraction to find strongest conjunction
   - Fixed-point iteration over qualifier set

**Subtyping Rule (Sub-Base)**:
```
Î“ âŠ¢ {Î½:B | Pâ‚} <: {Î½:B | Pâ‚‚}
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
   Î“, Î½:B, Pâ‚ âŠ¢ Pâ‚‚   (SMT valid)
```

The subtyping check reduces to SMT validity.

### 3.3 Measures for Algebraic Types

Measures lift algebraic data constructors to logical functions:
```haskell
{-@ measure len @-}
len :: [a] -> Int
len []     = 0
len (x:xs) = 1 + len xs

-- Strengthens data constructors:
data [a] where
  []  :: {v:[a] | len v = 0}
  (:) :: x:a -> xs:[a] -> {v:[a] | len v = 1 + len xs}
```

This enables specifications over recursive data structures while keeping verification decidable.

---

## 4. LIQUID HASKELL

### 4.1 System Overview (Vazou et al. 2014+)

LiquidHaskell extends Liquid Types to full Haskell:
- Refinement type annotations in special comments
- SMT-based verification (Z3)
- Support for laziness and non-termination
- Refinement reflection for theorem proving

**Annotation Syntax**:
```haskell
{-@ div :: Int -> {v:Int | v /= 0} -> Int @-}
div :: Int -> Int -> Int
div x y = x `quot` y

{-@ type Nat = {v:Int | v >= 0} @-}
{-@ abs :: Int -> Nat @-}
abs x | x < 0     = -x
      | otherwise = x
```

### 4.2 Handling Laziness

Haskell's lazy evaluation challenges refinement soundness:
- Diverging expressions don't have values
- Can't assume refinements hold for diverging terms

**Solution: Stratified Types**:
- `Ï„â‡“` (Fin-type): Finite values, guaranteed to terminate
- `Ï„â†“` (Div-type): May diverge but reduces to value if terminates
- `Ï„` : Arbitrary expressions

**Termination Checking**:
- Associate well-founded metrics with recursive functions
- Verify metric decreases at recursive calls
- 96% of functions verified terminating with 1.7 LOC/100 LOC hints

### 4.3 Abstract Refinements (Vazou et al. 2013)

Abstract over refinements using type parameters:
```haskell
{-@ data Vec a <p :: Int -> a -> Bool> = ... @-}
{-@ type IncrVec a = Vec <{\i v -> i <= v}> a @-}
```

Enables:
- Parametric refinements for type classes
- Index-dependent refinements for key-value maps
- Recursive refinements for data structures
- Inductive refinements for higher-order traversals

### 4.4 Refinement Reflection (POPL 2018)

Reflect code into refinement logic for theorem proving:
```haskell
{-@ reflect fib @-}
fib :: Int -> Int
fib n | n <= 1 = n
      | otherwise = fib (n-1) + fib (n-2)

-- Now fib's definition available in refinements
{-@ fibPositive :: n:Nat -> {fib n >= 0} @-}
```

This transforms Haskell into a proof assistant while maintaining SMT automation through "Proof by Logical Evaluation" (PLE).

---

## 5. F* PROGRAMMING LANGUAGE

### 5.1 Language Design

F* (pronounced "F star") is a full-spectrum dependently typed language:
- Dependent types with refinement types
- Monadic effects system
- SMT-based automation + manual proofs
- Extraction to OCaml, F#, C, WebAssembly

**Design Philosophy**:
- Combine practical ML-style programming with verification
- Effect system tracks computational effects precisely
- Refinement types for automation, full dependent types when needed

### 5.2 Refinement Types in F*

```fstar
val incr : x:int -> y:int{y > x}
let incr x = x + 1

val incr_precise : x:int -> y:int{y = x + 1}
let incr_precise x = x + 1

val div : int -> (divisor:int{divisor <> 0}) -> int
let div x y = x / y
```

**Type Checking Process**:
1. Generate verification conditions from refinements
2. Dispatch to Z3 SMT solver
3. Report success or error

### 5.3 Effect System

F* tracks computational effects:
- `Tot`: Total functions (always terminate)
- `Pure`: Pure functions (may diverge)
- `ST`: Stateful computations with heap
- `ML`: Full ML-style effects

```fstar
val factorial : n:nat -> Tot (y:nat{y >= 1})
let rec factorial n = 
  if n = 0 then 1 
  else n * factorial (n - 1)
```

### 5.4 Low* and KaRaMeL

**Low***: A subset of F* for low-level verified C code:
- First-order, imperative, memory-safe
- Explicit memory management with proof
- Compiles to readable C via KaRaMeL

**Applications**:
- HACL*: Verified cryptographic library
- miTLS: Verified TLS implementation
- EverCrypt: Cross-platform verified crypto provider

---

## 6. HACL*: VERIFIED CRYPTOGRAPHIC LIBRARY

### 6.1 Overview

HACL* (High-Assurance Cryptographic Library):
- Written in F*/Low*
- Compiled to portable C
- Implements: ChaCha20, Poly1305, SHA-2/3, Curve25519, Ed25519, HMAC, HKDF

**Verification Guarantees**:
1. Memory safety: No buffer overflows, use-after-free
2. Functional correctness: Matches mathematical specification
3. Secret independence: Timing side-channel resistance

### 6.2 Verification Methodology

**Specification Layer**:
```fstar
(* High-level mathematical spec *)
type felem = x:int{x >= 0 && x < prime}
val fadd : felem -> felem -> felem
val fmul : felem -> felem -> felem
```

**Implementation Layer**:
- Optimized Low* code
- Verified against spec via refinement types
- Secret independence via secure integer interface

**Secret Independence**:
```fstar
(* Secure comparison - no branching on secrets *)
val eq_mask : s:uint32 -> t:uint32 -> 
  z:uint32{reveal z = (if reveal s = reveal t then 0xfffffffful else 0x0ul)}
```

### 6.3 Deployment and Performance

- Pure C implementations: As fast as OpenSSL/libsodium
- Reference implementations: Significantly faster than TweetNaCl  
- Assembly gap: 1.1x-5.7x slower than hand-optimized SUPERCOP

**Deployed In**:
- Mozilla Firefox NSS
- Linux kernel
- mbedTLS
- Tezos blockchain
- Microsoft Pluton
- Google Titan security chips

---

## 7. FLUX: LIQUID TYPES FOR RUST

### 7.1 Design Innovation (Lehmann et al. PLDI 2023)

Flux shows how refinements work with Rust's ownership:
- Index mutable locations with pure values
- Exploit ownership to abstract sub-structural reasoning
- Strong references for strong updates

**Key Insight**: Rust's ownership mechanisms handle aliasing, letting refinement types focus purely on functional properties.

### 7.2 Type System Features

**Indexed Mutable References**:
```rust
#[spec(fn(x: &mut i32[@n]) ensures x: &mut i32[@n+1])]
fn incr(x: &mut i32) {
    *x += 1
}
```

**Refined Vectors**:
```rust
type RVec<T> = Vec<T>;  // Refined vector with length tracking

#[spec(fn(v: &RVec<T>[@n]) -> usize[n])]
fn len<T>(v: &RVec<T>) -> usize {
    v.len()
}
```

### 7.3 Soundness via Stacked Borrows

Flux proves: "well-borrowed evaluations of well-typed programs do not get stuck"
- Formal dependency on Rust's aliasing model
- Stacked Borrows provides aliasing guarantees
- Refinements provide functional properties

### 7.4 Evaluation Results

Compared to Prusti (program logic verifier):
- Specification size: 2x reduction
- Verification time: 10x reduction  
- Loop invariant overhead: From 14% to 0%

**Case Study**: Verified process isolation in Tock OS
- Found multiple subtle bugs breaking isolation
- Used in Google Security Chip, Microsoft Pluton

---

## 8. SMT SOLVER INTEGRATION

### 8.1 Verification Condition Generation

Refinement type checking reduces to SMT validity:
```
Î“ âŠ¢ {x:B | P} <: {x:B | Q}
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
âˆ€x:B. (â‹€Î“ âˆ§ P) âŸ¹ Q  is valid
```

The key is ensuring generated VCs are SMT-decidable.

### 8.2 Decidable Theories

SMT solvers efficiently handle:
- Linear arithmetic (integers, reals)
- Uninterpreted functions
- Arrays with extensionality
- Bitvectors
- Sets (Z3)

**Liquid Types Restriction**: 
Refinements are conjunctions of qualifiers from Q*, ensuring decidability.

### 8.3 Encoding Strategies

**Measures as Uninterpreted Functions**:
```
len(nil) = 0
len(cons(x,xs)) = 1 + len(xs)
```

Encoded via axioms or constructor refinements (more efficient).

**Recursive Functions**: 
- Uninterpreted in base logic
- Refinement reflection unfolds definitions as needed
- PLE automates common proof patterns

---

## 9. COMPARATIVE ANALYSIS

### 9.1 Refinement Types vs Dependent Types

| Aspect | Refinement Types | Full Dependent Types |
|--------|------------------|---------------------|
| Expressiveness | Restricted predicates | Arbitrary propositions |
| Automation | SMT-based, automatic | Manual proofs common |
| Decidability | Decidable (restricted) | Undecidable |
| Phase separation | Indexes erased | Types may contain terms |
| Learning curve | Lower | Higher |

### 9.2 System Comparison

| System | Language | Logic | SMT | Effects | Extraction |
|--------|----------|-------|-----|---------|------------|
| Liquid Haskell | Haskell | First-order | Z3 | Partial | Native |
| F* | F*/OCaml | Dependent | Z3 | Monadic | C, OCaml, JS |
| DML | SML | Linear arith | â€” | Pure | Native |
| Flux | Rust | First-order | Z3 | Ownership | Native |

### 9.3 Strengths and Limitations

**Strengths**:
- Automatic verification of non-trivial properties
- Minimal annotation overhead
- Decidable type checking
- Integration with existing languages

**Limitations**:
- Cannot express all dependent type properties
- Quantified invariants challenging
- Performance overhead from SMT queries
- Learning curve for predicate design

---

## 10. SECURITY APPLICATIONS

### 10.1 Memory Safety

Refinement types naturally express bounds:
```haskell
{-@ get :: xs:[a] -> {i:Int | 0 <= i && i < len xs} -> a @-}
```

No runtime bounds checks needed when statically verified.

### 10.2 Information Flow

Type-level security labels:
```fstar
type labeled (l:label) (a:Type) = a
val declassify : labeled High a -> labeled Low a  (* Requires privilege *)
```

### 10.3 Cryptographic Verification

HACL* demonstrates refinement types can verify:
- Functional correctness against mathematical specs
- Memory safety without runtime checks
- Secret independence (timing side-channel resistance)

---

## 11. KEY TAKEAWAYS

1. **Evolution of terminology**: "Refinement types" has shifted from datasort refinements to predicate subtypes

2. **Liquid Types insight**: Combining HM inference with predicate abstraction enables decidable refinement inference

3. **SMT is key**: SMT solvers make refinement type checking practical and automatic

4. **Ownership + refinements**: Rust's Flux shows ownership types handle aliasing, refinements handle properties

5. **Real-world impact**: HACL* demonstrates production-quality verified cryptography using refinement types

---

## 12. REFERENCES

### Foundational Papers
- Freeman & Pfenning (1991). "Refinement Types for ML". PLDI.
- Xi & Pfenning (1998). "Eliminating Array Bound Checking Through Dependent Types". PLDI.
- Xi & Pfenning (1999). "Dependent Types in Practical Programming". POPL.

### Liquid Types
- Rondon, Kawaguchi, Jhala (2008). "Liquid Types". PLDI.
- Vazou et al. (2014). "LiquidHaskell: Experience with Refinement Types". Haskell Symposium.
- Vazou et al. (2018). "Refinement Reflection: Complete Verification with SMT". POPL.

### F* and Verified Cryptography
- Swamy et al. (2016). "Dependent Types and Multi-Monadic Effects in F*". POPL.
- ZinzindohouÃ© et al. (2017). "HACL*: A Verified Modern Cryptographic Library". CCS.

### Recent Advances
- Lehmann et al. (2023). "Flux: Liquid Types for Rust". PLDI.
- Jhala & Vazou (2021). "Refinement Types: A Tutorial". Foundations and Trends.

---

*Document generated as part of TERAS-LANG Research Track A*
*Session A-08: Refinement Types (Liquid Haskell, F*)*
