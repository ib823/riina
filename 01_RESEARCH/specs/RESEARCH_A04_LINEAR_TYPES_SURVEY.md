# RESEARCH_A04_LINEAR_TYPES_SURVEY.md

## TERAS Research Track â€” Session A-04
## Linear Types and Substructural Logic: Exhaustive Survey

**Document Version:** 1.0.0  
**Created:** 2026-01-03  
**Status:** COMPLETE  
**Classification:** TERAS Research Foundation

---

## Executive Summary

This document presents an exhaustive survey of linear types and substructural type systems, tracing their development from Girard's linear logic (1987) through modern implementations including Rust's ownership system. Linear types enforce that resources are used exactly once, providing compile-time guarantees for memory safety, resource management, and concurrency correctness without garbage collection overhead. For TERAS, linear types form a critical foundation for enforcing security invariants around cryptographic key handling, session management, capability tokens, and audit trail integrity.

---

## Table of Contents

1. [Historical Development](#1-historical-development)
2. [Theoretical Foundations](#2-theoretical-foundations)
3. [Substructural Type System Taxonomy](#3-substructural-type-system-taxonomy)
4. [Linear Logic Connectives and Modalities](#4-linear-logic-connectives-and-modalities)
5. [Categorical Semantics](#5-categorical-semantics)
6. [Rust Ownership and Borrowing Model](#6-rust-ownership-and-borrowing-model)
7. [Formal Semantics and Metatheory](#7-formal-semantics-and-metatheory)
8. [Language Implementations](#8-language-implementations)
9. [Integration with Dependent and Refinement Types](#9-integration-with-dependent-and-refinement-types)
10. [Security and Resource Applications](#10-security-and-resource-applications)
11. [TERAS Relevance Analysis](#11-teras-relevance-analysis)
12. [Research Gaps and Open Problems](#12-research-gaps-and-open-problems)
13. [Bibliography](#13-bibliography)

---

## 1. Historical Development

### 1.1 Origins: Girard's Linear Logic (1987)

Jean-Yves Girard introduced linear logic in his seminal 1987 paper "Linear Logic" published in Theoretical Computer Science. This work emerged from Girard's analysis of intuitionistic and classical logic, specifically from examining the decomposition of intuitionistic implication.

**Key Insight:** Girard observed that the intuitionistic implication A â†’ B conflates two distinct operations:
1. The pure computational aspect (linear implication A âŠ¸ B)
2. The structural manipulation of hypotheses (exponential modalities !, ?)

**Motivation:** Traditional logics treat hypotheses as unlimited resources that can be:
- Used multiple times (contraction)
- Ignored entirely (weakening)
- Reordered freely (exchange)

Linear logic makes resource usage explicit by restricting or controlling these structural rules.

### 1.2 Pre-Girard Precursors

**Relevant Logic (Anderson & Belnap, 1960s-1970s):**
- Rejected weakening to ensure premises are actually "relevant" to conclusions
- Allowed contraction (multiple uses)
- Introduced the "variable sharing property"

**Lambek Calculus (1958):**
- Non-commutative logic for syntactic categories
- No exchange, contraction, or weakening
- Foundation for ordered linear logic

**Intuitionistic Logic without Contraction:**
- Various investigations of restricted structural rules
- Connection to resource semantics observed independently

### 1.3 Development Timeline

| Year | Development | Significance |
|------|-------------|--------------|
| 1958 | Lambek Calculus | Non-commutative resource logic |
| 1987 | Girard's Linear Logic | Full decomposition of connectives |
| 1990 | Linear Type Systems | Curry-Howard for linear logic |
| 1992 | Clean Uniqueness Types | First practical implementation |
| 1993 | Linear Logic Programming | Lolli, Forum languages |
| 1994 | Wadler's Linear Types | Theoretical foundations |
| 1998 | Vault, Cyclone | Systems programming applications |
| 2002 | ATS (Xi) | Dependent linear types |
| 2010 | Rust Development Begins | Ownership/borrowing model |
| 2015 | Rust 1.0 | Mainstream adoption |
| 2018 | Linear Haskell | Integration with higher-order types |
| 2019 | Oxide Formalization | Formal Rust semantics |
| 2020+ | Session Types Integration | Linear types for protocols |

### 1.4 Curry-Howard Correspondence

Linear logic extends the Curry-Howard correspondence:

| Linear Logic | Type Theory | Computation |
|--------------|-------------|-------------|
| Linear implication (âŠ¸) | Linear function type | Functions consuming input |
| Tensor (âŠ—) | Pair type (both) | Parallel composition |
| With (&) | Pair type (choice) | Lazy pairs |
| Plus (âŠ•) | Sum type | Tagged unions |
| Of course (!) | Reusable type | Freely copyable |
| Why not (?) | Linear monad | Effect tracking |

---

## 2. Theoretical Foundations

### 2.1 Resource Interpretation

The fundamental insight of linear logic is treating logical propositions as **resources** rather than eternal truths:

**Classical/Intuitionistic Logic:**
- Propositions are facts that remain true indefinitely
- A proof of A remains valid for unlimited uses
- Hypotheses can be duplicated or ignored freely

**Linear Logic:**
- Propositions represent consumable resources
- A proof of A represents exactly one use of that resource
- Using a resource consumes it; it cannot be reused without explicit permission

### 2.2 Structural Rules

The structural rules govern how hypotheses behave in sequent calculus:

**Exchange (Commutativity):**
```
Î“, A, B, Î” âŠ¢ C
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (Exchange)
Î“, B, A, Î” âŠ¢ C
```
- Linear logic: ALLOWED (contexts are multisets)
- Ordered logic: FORBIDDEN (contexts are sequences)

**Contraction (Duplication):**
```
Î“, A, A âŠ¢ B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (Contraction)
Î“, A âŠ¢ B
```
- Linear/affine logic: FORBIDDEN without ! modality
- Classical/intuitionistic: ALLOWED freely

**Weakening (Discarding):**
```
Î“ âŠ¢ B
â”€â”€â”€â”€â”€â”€â”€â”€ (Weakening)
Î“, A âŠ¢ B
```
- Linear logic: FORBIDDEN without ! modality
- Affine logic: ALLOWED
- Classical/intuitionistic: ALLOWED

### 2.3 Sequent Calculus Formulation

Girard's original presentation uses one-sided sequents (classical linear logic):

```
âŠ¢ Î“, A, B      âŠ¢ Î”, AâŠ¥
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (âŠ—R)  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (âŠ¥L)
âŠ¢ Î“, Î”, A âŠ— B       âŠ¢ Î”, AâŠ¥ â…‹ BâŠ¥

âŠ¢ Î“, A    âŠ¢ Î“, B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (&R)
   âŠ¢ Î“, A & B

âŠ¢ Î“, A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (!R) [Î“ contains only !-formulas]
âŠ¢ Î“, !A
```

### 2.4 Cut Elimination

**Theorem (Girard 1987):** Linear logic enjoys cut elimination.

The cut rule:
```
âŠ¢ Î“, A    âŠ¢ AâŠ¥, Î”
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (Cut)
    âŠ¢ Î“, Î”
```

Can be eliminated, yielding a decision procedure for the logic. This is crucial for:
- Proof search algorithms
- Normalization of programs
- Type safety proofs

### 2.5 Proof Nets

Girard introduced **proof nets** as a canonical representation of linear logic proofs:

- Eliminate "bureaucratic" differences between proofs
- Graph-based representation
- Criterion for correct proofs (no "vicious circles")
- Foundation for geometry of interaction

**Structure:**
- Nodes: logical connectives
- Links: connections between formulas
- Correctness criterion: switching condition (any switch yields connected, acyclic graph)

---

## 3. Substructural Type System Taxonomy

### 3.1 Classification by Structural Rules

| Type System | Exchange | Contraction | Weakening | Use Pattern |
|-------------|----------|-------------|-----------|-------------|
| **Unrestricted** | âœ“ | âœ“ | âœ“ | Any number of times |
| **Linear** | âœ“ | âœ— | âœ— | Exactly once |
| **Affine** | âœ“ | âœ— | âœ“ | At most once |
| **Relevant** | âœ“ | âœ“ | âœ— | At least once |
| **Ordered** | âœ— | âœ— | âœ— | Exactly once, in order |

### 3.2 Linear Types

**Definition:** A linear type AâŠ¸ means values of type A must be used exactly once.

**Typing Rules:**
```
Î“ âŠ¢ M : A    Î”, x:A âŠ¢ N : B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (âŠ¸E)
        Î“, Î” âŠ¢ N[M/x] : B

Î“, x:A âŠ¢ M : B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (âŠ¸I) [x used exactly once in M]
Î“ âŠ¢ Î»x.M : A âŠ¸ B
```

**Context Splitting:** The context Î“, Î” is split between premises; no sharing.

**Applications:**
- Memory deallocation
- File handle management
- Cryptographic key consumption
- Protocol state transitions

### 3.3 Affine Types

**Definition:** Affine type values can be used at most once (zero or one times).

**Relaxation:** Adds weakening:
```
Î“ âŠ¢ M : B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (Weak)
Î“, x:A âŠ¢ M : B
```

**Practical Significance:**
- Allows resources to be safely discarded
- Exception handling: cleanup without using a resource
- Rust's actual model (not strictly linear)

### 3.4 Relevant Types

**Definition:** Relevant type values must be used at least once.

**Allows:** Contraction (multiple uses)
**Forbids:** Weakening (ignoring)

**Applications:**
- Ensuring audit trails are written
- Mandatory error handling
- Guaranteed notification delivery

### 3.5 Ordered Types

**Definition:** Values must be used exactly once, in the order introduced.

**Stack Semantics:**
- Variables form a stack
- Can only access top of stack
- Modeling stack-based allocation

**Typing Rules:**
```
Î“; x:A âŠ¢ M : B
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (âŠ¸I)
Î“ âŠ¢ Î»x.M : A âŠ¸ B

Î“ âŠ¢ M : A âŠ¸ B    Î” âŠ¢ N : A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (âŠ¸E)
      Î“; Î” âŠ¢ M N : B
```

Note: Context concatenation (;) preserves order.

---

## 4. Linear Logic Connectives and Modalities

### 4.1 Multiplicative Connectives

These connectives split resources between premises:

**Tensor (âŠ—) â€” "Times" or "Par":**
```
A âŠ— B â€” I have both A and B (simultaneously)
```
- Resources are parallel-composed
- Must use both components
- Type interpretation: pairs where both elements are consumed

**Linear Implication (âŠ¸) â€” "Lollipop":**
```
A âŠ¸ B â€” Given A (consuming it), I can produce B
```
- Function that consumes its argument exactly once
- No currying without explicit copying

**Par (â…‹):**
```
A â…‹ B â€” Dual of tensor in classical linear logic
```
- "Either A or B, but I don't control which"
- Related to non-determinism

**Multiplicative Units:**
- **1** (one): Unit for âŠ—, empty resource
- **âŠ¥** (bottom): Unit for â…‹

### 4.2 Additive Connectives

These connectives share contexts between premises:

**With (&) â€” "With":**
```
A & B â€” I have both A and B, but can only use one
```
- Internal choice: I choose which to use
- Lazy evaluation: other branch not computed
- Type interpretation: record with choosable fields

**Plus (âŠ•) â€” "Or":**
```
A âŠ• B â€” I have either A or B
```
- External choice: environment determined which
- Tagged union / sum type
- Pattern matching to determine

**Additive Units:**
- **âŠ¤** (top): Unit for &, any projection succeeds
- **0** (zero): Unit for âŠ•, impossible case

### 4.3 Exponential Modalities

**Of Course (!A) â€” "Bang":**
```
!A â€” Unlimited supply of A
```
- Can be contracted: !A âŠ¸ !A âŠ— !A
- Can be weakened: !A âŠ¸ 1
- Can be derelicted: !A âŠ¸ A

**Rules:**
```
âŠ¢ Î“, A
â”€â”€â”€â”€â”€â”€â”€â”€ (!R) where Î“ contains only !-formulas
âŠ¢ Î“, !A

âŠ¢ Î“, A
â”€â”€â”€â”€â”€â”€â”€â”€ (Dereliction)
âŠ¢ Î“, !A

âŠ¢ Î“, !A, !A
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (Contraction)
âŠ¢ Î“, !A

âŠ¢ Î“
â”€â”€â”€â”€â”€â”€ (Weakening)
âŠ¢ Î“, !A
```

**Why Not (?A) â€” "Question":**
```
?A â€” Dual of !A in classical linear logic
```
- Allows demand for A at any time
- Related to effect tracking

### 4.4 Connective Relationships

| Classical | Linear Decomposition |
|-----------|---------------------|
| A âˆ§ B | !A âŠ— !B (shared) or A & B (choice) |
| A âˆ¨ B | ?A â…‹ ?B (shared) or A âŠ• B (choice) |
| A â†’ B | !A âŠ¸ B (unlimited) or A âŠ¸ B (linear) |
| Â¬A | A âŠ¸ âŠ¥ (linear) or AâŠ¥ (involution) |

### 4.5 Polarization and Focusing

**Andreoli's Focusing (1992):** 
- Formulas classified as positive or negative
- Proof search becomes deterministic in focused phases
- Eliminates "don't care" non-determinism

| Polarity | Connectives | Behavior |
|----------|-------------|----------|
| Positive | âŠ—, âŠ•, 1, 0, ! | Invertible on left |
| Negative | â…‹, &, âŠ¥, âŠ¤, ? | Invertible on right |

---

## 5. Categorical Semantics

### 5.1 Symmetric Monoidal Categories

Linear logic is the internal language of **symmetric monoidal closed categories** (SMCC):

**Structure:**
- Category C with objects (types) and morphisms (programs)
- Tensor product âŠ— : C Ã— C â†’ C
- Unit object I
- Natural isomorphisms:
  - Î± : (A âŠ— B) âŠ— C â‰… A âŠ— (B âŠ— C) (associator)
  - Î» : I âŠ— A â‰… A (left unitor)
  - Ï : A âŠ— I â‰… A (right unitor)
  - Ïƒ : A âŠ— B â‰… B âŠ— A (symmetry)

**Closure:** Internal hom A âŠ¸ B with adjunction:
```
Hom(A âŠ— B, C) â‰… Hom(A, B âŠ¸ C)
```

### 5.2 Contrast with Cartesian Closed Categories

| Property | CCC (Î»-calculus) | SMCC (Linear) |
|----------|-----------------|---------------|
| Product | A Ã— B (diagonal Î” exists) | A âŠ— B (no diagonal) |
| Diagonal | Î” : A â†’ A Ã— A | None |
| Terminal | 1 with ! : A â†’ 1 | I (no general map) |
| Copy | Free | Requires ! |
| Discard | Free | Requires affine |

**Key Insight:** The diagonal morphism Î” : A â†’ A Ã— A enables copying in CCCs. SMCCs lack this, enforcing linearity.

### 5.3 *-Autonomous Categories

Classical linear logic corresponds to **-autonomous categories*:

- SMCC structure
- Dualizing object âŠ¥
- Isomorphism A â‰… (A âŠ¸ âŠ¥) âŠ¸ âŠ¥ (double negation)
- De Morgan duality: (A âŠ— B)âŠ¥ â‰… AâŠ¥ â…‹ BâŠ¥

### 5.4 Coalgebras and Exponentials

The ! modality is modeled by a comonad:

**Comonad Structure:**
- ! : C â†’ C (functor)
- Îµ : !A â†’ A (counit, dereliction)
- Î´ : !A â†’ !!A (comultiplication, digging)

**Coalgebra Laws:**
```
Îµ âˆ˜ Î´ = id
!Îµ âˆ˜ Î´ = id
Î´ âˆ˜ Î´ = !Î´ âˆ˜ Î´
```

**Seely's Conditions (1989):**
For modeling full linear logic:
- ! is a monoidal comonad
- !A carries a cocommutative comonoid structure
- Natural transformations for contraction and weakening

### 5.5 Chu Construction

**Chu(C, âŠ¥)** provides a canonical way to build *-autonomous categories:

- Objects: pairs (Aâº, Aâ») with pairing Aâº Ã— Aâ» â†’ âŠ¥
- Morphisms: pairs (f, g) with compatibility
- Constructs linear logic model from any monoidal category

---

## 6. Rust Ownership and Borrowing Model

### 6.1 Ownership Principles

Rust implements an **affine type system** through ownership rules:

**Three Ownership Rules:**
1. Each value has exactly one owner (variable)
2. When the owner goes out of scope, the value is dropped
3. Ownership can be transferred (moved), ending the previous binding

**Move Semantics:**
```rust
let s1 = String::from("hello");
let s2 = s1;  // s1 moved to s2
// s1 is no longer valid here
```

### 6.2 Borrowing System

Rust relaxes strict linearity through **borrowing**:

**Immutable Borrows (&T):**
```rust
let s = String::from("hello");
let r1 = &s;  // immutable borrow
let r2 = &s;  // multiple immutable borrows allowed
println!("{} {}", r1, r2);
```
- Multiple simultaneous immutable borrows allowed
- Cannot modify through immutable reference
- Original cannot be modified while borrowed

**Mutable Borrows (&mut T):**
```rust
let mut s = String::from("hello");
let r = &mut s;  // mutable borrow
r.push_str(" world");
// Only one mutable borrow at a time
```
- Exactly one mutable borrow at a time
- No immutable borrows while mutable borrow active
- Prevents data races statically

### 6.3 Borrow Checker Algorithm

**Alias XOR Mutability Principle:**
At any point, either:
- Multiple readers (&T), OR
- Single writer (&mut T)
Never both.

**Lifetime Annotations:**
```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```
- 'a is a lifetime parameter
- Ensures returned reference valid as long as inputs
- Compiler infers lifetimes where unambiguous

### 6.4 Non-Lexical Lifetimes (NLL)

**Pre-NLL (Rust < 2018):**
- Lifetimes tied to lexical scope
- Over-conservative rejections

**Post-NLL:**
- Dataflow analysis determines actual live ranges
- References "die" after last use
- More programs accepted without loss of safety

**Example:**
```rust
let mut x = 5;
let y = &x;      // borrow starts
println!("{}", y);  // last use of y
let z = &mut x;  // OK with NLL: y's borrow ended
```

### 6.5 Interior Mutability Patterns

Rust provides escape hatches from borrow checking via **interior mutability**:

**Cell<T>:**
- Single-threaded mutable memory cell
- get/set operations
- No references to contents

**RefCell<T>:**
- Runtime-checked borrowing
- borrow() returns Ref<T>
- borrow_mut() returns RefMut<T>
- Panics on violation (moved from compile to runtime)

**Mutex<T>, RwLock<T>:**
- Thread-safe interior mutability
- Blocking synchronization
- Prevents data races in concurrent code

### 6.6 Affine vs Linear in Rust

**Rust is Affine, Not Linear:**
- Values can be dropped without use (weakening allowed)
- Drop trait for destructor logic
- Leak amplification: mem::forget doesn't call Drop

**Linear Rust Proposals:**
- RFC for linear/droppable distinction
- Pin<T> for self-referential structures
- Partial linearity for specific types

---

## 7. Formal Semantics and Metatheory

### 7.1 Oxide: Formalized Rust Core

**Weiss et al. (2019):** Oxide formalizes Rust's ownership model.

**Key Features:**
- Regions as sets of locations (places)
- Place expressions with projection paths
- Ownership and borrowing as type-level constraints

**Type System:**
```
Ï„ ::= bool | unit | &Ï mut? Ï„ | Box<Ï„> | ...
```

**Place Typing:**
```
Î“ âŠ¢ Ï€ : Ï„ @ Ï    (place Ï€ has type Ï„ in region Ï)
```

**Safety Theorem:** Well-typed Oxide programs do not exhibit:
- Use after free
- Double free
- Data races

### 7.2 Patina: Affine Types for Rust

**Reed (2015):** Patina models Rust's core features.

**Components:**
- Affine types for ownership
- Borrowed references (shared vs unique)
- Lifetime tracking
- Drop semantics

**Typing Judgment:**
```
Î”; Î“ âŠ¢ e : Ï„ âŠ£ Î”'
```
- Î”: loan set (active borrows)
- Î“: variable environment
- Î”': updated loans after evaluation

### 7.3 FR Calculus

**Lightweight Formalism:**
- Focused on reference lifetimes
- Borrowing as explicit operations
- Compatible with linear lambda calculus

### 7.4 Metatheoretic Properties

**Type Safety:**
- Progress: Well-typed terms either are values or can step
- Preservation: Reduction preserves types

**Memory Safety:**
- No dangling pointers
- No double frees
- No data races

**Proofs:** Typically by:
- Syntactic methods (Wright-Felleisen)
- Logical relations
- Step-indexed models

---

## 8. Language Implementations

### 8.1 Clean (1990s)

**Uniqueness Types:**
- Unique values: exactly one reference
- Non-unique values: freely copyable
- Subtyping: unique â‰¤ non-unique

**Applications:**
- Efficient array updates (in-place)
- Safe I/O without monads
- Concurrent programming

**Syntax:**
```clean
:: *World  // unique world
:: File    // linear file handle

fopen :: String *World -> (*File, *World)
fclose :: *File *World -> *World
```

### 8.2 ATS (Applied Type System)

**Xi (2002-present):** Combines dependent types with linear types.

**Features:**
- Linear and persistent types
- Theorem proving in types
- Safe manual memory management
- C-level performance

**Resource Types:**
```ats
viewtype FILE (l:addr) = @{ pf: FILE_v l, ptr: ptr l }

fun fread {l:addr} (pf: !FILE_v l >> FILE_v l | ptr l): int
```

**Linear Views:**
- `FILE_v l`: permission to access file at address l
- `!T >> T'`: consumes T, produces T'

### 8.3 Linear Haskell (2018)

**Bernardy et al.:** GHC extension for linear types.

**Approach:**
- Multiplicity annotations on arrows
- `a ->. b` (linear function)
- `a -> b` (unrestricted function)
- Multiplicity polymorphism

**Syntax:**
```haskell
dup :: a %1 -> (a, a)  -- INVALID: linear constraint violated

linear :: a %1 -> b    -- consumes a exactly once
unrestricted :: a -> b -- consumes a any number of times
```

**Key Innovation:**
- Retrofitting linearity to existing Haskell
- Backwards compatibility
- Multiplicity polymorphism: `forall (m :: Multiplicity). a %m -> b`

### 8.4 Cyclone (2002-2006)

**Safe C Dialect:**
- Region-based memory management
- Fat pointers with bounds
- Existential types for data abstraction

**Linear Regions:**
```cyclone
region r {
    int *@region(r) x = rmalloc(r, sizeof(int));
    *x = 42;
} // region r and all its allocations freed here
```

### 8.5 Vault (2001)

**Microsoft Research:**
- Keys and locks for resource tracking
- Linear capabilities
- Inspired Rust's design

**Adoption Discipline:**
- Resources have keys
- Keys can be tracked linearly
- Compiler verifies key usage

### 8.6 Mezzo (2012)

**Protzenko & Pottier:**
- Algebraic types with permissions
- Adoption/abandon discipline
- Frame inference

**Permissions:**
```mezzo
val x: (ref int, x @ ref int)  // value and permission
```

---

## 9. Integration with Dependent and Refinement Types

### 9.1 ATS Model: Linear + Dependent

ATS demonstrates successful integration:

**Dependent Types:**
```ats
fun vector_get {n:nat} {i:nat | i < n} 
    (v: vector(a, n), i: int i): a
```

**Linear Types:**
```ats
fun free {a:viewtype} {l:addr} 
    (pf: a @ l | p: ptr l): void
```

**Combined:**
```ats
fun array_free {a:viewtype} {n:nat} {l:addr}
    (pf: @[a][n] @ l | p: ptr l, n: int n): void
```

### 9.2 F* Approach

**Linear Effects:**
- Effect system with linear resources
- ST monad for stateful computations
- Separation logic integration

```fstar
let read_file (f: file_handle) 
  : ST (string * file_handle)
    (requires (fun h -> h `contains` f))
    (ensures (fun h (s, f') h' -> f' == f))
= ...
```

### 9.3 Liquid Linear Types

**Combining Refinement + Linear:**
- Predicate refinements on linear types
- SMT-based verification
- Resource-aware reasoning

**Example:**
```
{x: File | isOpen(x)} âŠ¸ {y: File | isClosed(y)}
```

### 9.4 TERAS Integration Strategy

**Proposed Combination:**
1. **Linear types** for resource safety (keys, handles, capabilities)
2. **Refinement types** for security predicates (labels, permissions)
3. **Dependent types** for protocol verification (session types)

**Layered Approach:**
```
Layer 3: Session types (protocol state)
Layer 2: Refinement types (security labels)  
Layer 1: Linear types (resource ownership)
Layer 0: Base types
```

---

## 10. Security and Resource Applications

### 10.1 Memory Safety

**Vulnerabilities Prevented:**
- Use-after-free
- Double-free
- Dangling pointers
- Buffer overflows (with bounds checking)
- Memory leaks (with affine + destructors)

**Mechanism:**
- Linear types ensure single ownership
- Borrowing provides temporary aliasing
- Lifetimes bound alias duration
- Drop ensures cleanup

### 10.2 Concurrency Safety

**Data Race Prevention:**
```rust
// Rust's Send + Sync traits
trait Send {}  // safe to transfer between threads
trait Sync {}  // safe to share between threads (via &)
```

**Linear Types Ensure:**
- No concurrent mutation of shared data
- Message-passing with ownership transfer
- Lock-free correctness through linearity

### 10.3 Cryptographic Key Management

**Linear Types for Keys:**
```
type SessionKey      // linear: must be used and destroyed
type PublicKey = !PK // unrestricted: freely copyable

derive_key : MasterKey âŠ¸ (SessionKey âŠ— MasterKey')
encrypt : SessionKey âŠ— Plaintext âŠ¸ Ciphertext
decrypt : SessionKey âŠ— Ciphertext âŠ¸ Plaintext âŠ— SessionKey
destroy : SessionKey âŠ¸ unit
```

**Guarantees:**
- Keys cannot be duplicated
- Keys must be explicitly destroyed
- Key material cleanup enforced

### 10.4 Capability Systems

**Linear Capabilities:**
```
type Cap[R]  // linear capability to access resource R

access : Cap[R] âŠ¸ (R âŠ— Cap[R])  // use and return
revoke : Cap[R] âŠ¸ unit           // capability consumed
```

**Applications:**
- File system permissions
- Network access control
- Hardware device access
- Privilege escalation prevention

### 10.5 Protocol State Machines

**Session Types (Honda, 1993):**
```
type AuthProtocol = 
    !Username.?Password.?AuthResult.end

type ServerSide =
    ?Username.!Challenge.?Response.!Result.end
```

**Linear Channels:**
```
send : Chan[!A.S] âŠ— A âŠ¸ Chan[S]
recv : Chan[?A.S] âŠ¸ (A âŠ— Chan[S])
close : Chan[end] âŠ¸ unit
```

**TERAS Protocol Applications:**
- TLS handshake verification
- Authentication flow enforcement
- API call sequencing

### 10.6 Audit Trail Integrity

**Relevant Types for Audit:**
```
type AuditEntry    // relevant: must be used at least once
type AuditLog = List[AuditEntry]

log_action : Action â†’ AuditEntry
commit : AuditEntry â†’ IO unit  // ensures entry is recorded
```

**Guarantee:** Every security-relevant action produces an audit entry that must be committed.

---

## 11. TERAS Relevance Analysis

### 11.1 Alignment with TERAS Principles

| TERAS Principle | Linear Types Support |
|-----------------|---------------------|
| Zero-dependency | Ownership replaces GC |
| Formal verification | Type-based resource proofs |
| Compile-time security | Static resource checking |
| Performance | No runtime overhead |
| Memory safety | Use-after-free prevention |

### 11.2 TERAS Product Applications

**MENARA (Mobile Security):**
- Session token linearity
- Secure enclave key handling
- Certificate chain management

**GAPURA (WAF):**
- Connection handle safety
- Request/response lifecycle
- Capability-based access

**ZIRAH (EDR):**
- Sensor data ownership
- Alert channel protocols
- Memory isolation enforcement

**BENTENG (eKYC):**
- Biometric data lifetime
- Document handle safety
- Verification flow protocols

**SANDI (Signatures):**
- Private key linearity
- Signing ceremony protocols
- Key escrow safety

### 11.3 Required Extensions

**Beyond Standard Linear Types:**
1. **Security lattice integration:** Labels on linear types
2. **Information flow:** No-cloning for secrets
3. **Protocol verification:** Session types
4. **Capability tokens:** Dynamic permissions
5. **Audit enforcement:** Relevant types for logging

### 11.4 Integration with Other TERAS Type Features

**With Refinement Types (A-03):**
```
type SecureKey{l:Label} = {k: Key | level(k) = l} âŠ¸
```

**With Dependent Types (A-01):**
```
type Vec[A, n:Nat] = A^n âŠ¸
```

**With Effect System:**
```
read_key : () â†’ IO[KeyStore] Key âŠ¸
```

---

## 12. Research Gaps and Open Problems

### 12.1 Theoretical Gaps

1. **Semantic models for borrowing:** Current models (Oxide, Patina) are syntactic; denotational semantics needed

2. **Higher-order borrowing:** Closures capturing references, lifetime polymorphism

3. **Dependent linear types:** Full integration of MLTT with linear types (beyond ATS)

4. **Graded modal types:** Quantitative types (use at most n times)

5. **Concurrent linear types:** Session types for shared-memory concurrency

### 12.2 Practical Gaps

1. **Ergonomics:** Linear types add annotation burden

2. **Inference:** Lifetime inference is NP-hard in general

3. **Interoperability:** FFI with non-linear languages (C, Python)

4. **Debugging:** Error messages for linearity violations

5. **IDE support:** Visualization of ownership flow

### 12.3 Security-Specific Gaps

1. **Information flow + linearity:** Integrated IFC with resource tracking

2. **Capability revocation:** Dynamic capability invalidation with static safety

3. **Declassification:** Controlled release of linear secrets

4. **Side-channel resistance:** Preventing leaks through resource usage patterns

5. **Attestation:** Linear types for remote attestation protocols

### 12.4 TERAS-Specific Research Questions

1. How to represent security labels on linear types efficiently?
2. Can we encode capability hierarchies with linear types?
3. How to integrate session types with TERAS protocol verification?
4. What is the overhead of linear type checking for large codebases?
5. Can we extract efficient Rust code from linear TERAS-LANG programs?

---

## 13. Bibliography

### 13.1 Foundational Papers

1. Girard, J.-Y. (1987). "Linear Logic." Theoretical Computer Science, 50(1):1-102.

2. Wadler, P. (1990). "Linear Types Can Change the World!" IFIP TC 2 Working Conference on Programming Concepts and Methods.

3. Abramsky, S. (1993). "Computational Interpretations of Linear Logic." Theoretical Computer Science, 111(1-2):3-57.

4. Barber, A. (1996). "Dual Intuitionistic Linear Logic." Technical Report ECS-LFCS-96-347, University of Edinburgh.

5. Benton, N. (1994). "A Mixed Linear and Non-Linear Logic: Proofs, Terms and Models." CSL 1994.

### 13.2 Type Systems

6. Walker, D. (2005). "Substructural Type Systems." Advanced Topics in Types and Programming Languages, MIT Press.

7. Xi, H. (2002). "Dependent ML: An Approach to Practical Programming with Dependent Types." Journal of Functional Programming.

8. Bernardy, J.-P. et al. (2018). "Linear Haskell: Practical Linearity in a Higher-Order Polymorphic Language." POPL 2018.

9. Tov, J. & Pucella, R. (2011). "Practical Affine Types." POPL 2011.

10. Mazurak, K. et al. (2010). "Lightweight Linear Types in System FÂ°." TLDI 2010.

### 13.3 Rust and Implementations

11. Jung, R. et al. (2018). "RustBelt: Securing the Foundations of the Rust Programming Language." POPL 2018.

12. Weiss, A. et al. (2019). "Oxide: The Essence of Rust." arXiv:1903.00982.

13. Reed, E. (2015). "Patina: A Formalization of the Rust Programming Language." Technical Report, University of Washington.

14. Anderson, B. & Klock, F. (2014). "Non-Lexical Lifetimes." Rust RFC.

### 13.4 Session Types

15. Honda, K. (1993). "Types for Dyadic Interaction." CONCUR 1993.

16. Honda, K., Yoshida, N., & Carbone, M. (2008). "Multiparty Asynchronous Session Types." POPL 2008.

17. Gay, S. & Hole, M. (2005). "Subtyping for Session Types in the Pi Calculus." Acta Informatica.

### 13.5 Security Applications

18. Walker, D. & Morrisett, G. (2000). "Alias Types for Recursive Data Structures." Workshop on Types in Compilation.

19. DeLine, R. & FÃ¤hndrich, M. (2001). "Enforcing High-Level Protocols in Low-Level Software." PLDI 2001.

20. Swamy, N. et al. (2011). "Secure Distributed Programming with Value-Dependent Types." ICFP 2011.

### 13.6 Categorical Semantics

21. Seely, R.A.G. (1989). "Linear Logic, *-Autonomous Categories and Cofree Coalgebras." Categories in Computer Science and Logic, AMS.

22. Mellies, P.-A. (2009). "Categorical Semantics of Linear Logic." Panoramas et SynthÃ¨ses.

23. Benton, N., Bierman, G., & de Paiva, V. (1998). "Computational Types from a Logical Perspective." Journal of Functional Programming.

---

## Document Metadata

**Research Track:** A (Theoretical Foundations)  
**Session:** A-04  
**Topic:** Linear Types and Substructural Logic  
**Preceding Sessions:** A-01 (MLTT), A-02 (CoC/CIC), A-03 (Refinement Types)  
**Following Sessions:** A-05 (Effect Systems), A-06 (Session Types)

**SHA-256 Lineage:**
- Parent: RESEARCH_A03_REFINEMENT_TYPES_DECISION.md
- This document: [To be computed on finalization]

---

*This survey provides the theoretical foundation for TERAS-LANG's resource management layer, complementing the refinement types (A-03) for security predicates and dependent types (A-01) for protocol verification.*
