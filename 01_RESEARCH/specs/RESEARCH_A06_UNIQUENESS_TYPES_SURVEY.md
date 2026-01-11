# RESEARCH_A06_UNIQUENESS_TYPES_SURVEY

## Session A-06: Uniqueness Types (Clean Language)

**Research Track**: Domain A - Type Theory Foundations
**Session**: A-06 of 20
**Date**: 2026-01-03
**Status**: COMPREHENSIVE SURVEY

---

## Executive Summary

Uniqueness types provide a mechanism for tracking whether values have exactly one reference at runtime, enabling safe in-place updates within purely functional languages while maintaining referential transparency. Originating in the Clean programming language (1987), uniqueness types offer an alternative to monads for handling effects and side effects, and have influenced modern systems languages including Rust. This survey examines the theoretical foundations, formal semantics, practical implementations, and relationship to linear and affine types.

---

## 1. Historical Development and Motivation

### 1.1 Origins in Clean (1987)

The Clean programming language was formally introduced at FPCA '87 (Third International Conference on Functional Programming Languages and Computer Architecture) in Portland, Oregon. The primary motivations for creating Clean were:

1. **Overcoming limitations in contemporary functional languages** (e.g., Miranda)
2. **Integrating efficient state management** via uniqueness typing while preserving purity
3. **Avoiding impure features** like side effects
4. **Graph reduction as computational model** for explicit sharing, cyclic definitions, and optimized reductions

Key insight: Unlike term-based evaluation (which could lead to inefficiencies), Clean emphasized **graph reduction** to enable better control over resource usage and performance in concurrent settings.

### 1.2 The Problem Uniqueness Types Solve

In purely functional languages, values are immutable. This creates challenges for:

1. **Efficient I/O operations**: Reading/writing files, network communication
2. **Mutable data structures**: Arrays, hash tables with O(1) updates
3. **Interfacing with imperative world**: C libraries, operating system calls
4. **Resource management**: Files, connections, memory

Traditional solutions:
- **Monads** (Haskell): Sequence effects through monadic composition
- **State threads** (ST monad): Encapsulate mutable state
- **Linear types**: Ensure values used exactly once

Uniqueness types offer an alternative: track when a value has **exactly one reference**, allowing safe destructive updates.

### 1.3 Key Researchers and Contributions

| Researcher | Institution | Contribution |
|------------|-------------|--------------|
| Erik Barendsen | Radboud University Nijmegen | Formal semantics of uniqueness typing |
| Sjaak Smetsers | Radboud University Nijmegen | Graph rewriting semantics, type inference |
| Rinus Plasmeijer | Radboud University Nijmegen | Clean language design, I/O system |
| Marko van Eekelen | Radboud University Nijmegen | Graph rewriting, type system |
| Dana Harrington | University of Calgary | Uniqueness logic |

---

## 2. Theoretical Foundations

### 2.1 Core Concept: Reference Count Invariant

A value has a **unique** type if and only if:
- At runtime, there exists exactly one reference to that value
- No other part of the program can observe changes to the value

Notation in Clean:
```clean
*Type    -- Unique type (exactly one reference)
Type     -- Non-unique type (possibly shared)
```

### 2.2 Uniqueness Attributes

Clean's type system extends conventional types with **uniqueness attributes**:

| Attribute | Symbol | Meaning |
|-----------|--------|---------|
| Unique | `*` | Exactly one reference exists |
| Non-unique | (none) | Possibly multiple references |
| Polymorphic | `u:` | Attribute is a type variable |

Example type signatures:
```clean
// Unique array update (in-place)
update :: *{#a} Int a -> *{#a}

// Non-unique array read
select :: {#a} Int -> a

// Polymorphic uniqueness
map :: (a -> b) u:[a] -> u:[b]
```

### 2.3 Graph Rewriting Semantics

Clean's uniqueness types are formalized using **term graph rewriting systems (TGRS)**, not lambda calculus. Key aspects:

**Graph Representation**:
- Values are nodes in a graph
- References are edges to nodes
- Sharing is explicit (multiple edges to same node)
- Unique values have exactly one incoming edge

**Rewrite Rules**:
```
Graph node with unique type:
    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
    â”‚  Node (value)   â”‚  â† exactly one reference
    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Graph node with shared type:
    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
    â”‚  Node (value)   â”‚  â† multiple references
    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â†‘     â†‘
       ref1   ref2
```

**Confluence**: Barendsen and Smetsers proved confluence for term graph rewrite systems with copying, essential for deterministic evaluation.

### 2.4 Type Preservation During Evaluation

Key theorem (Barendsen & Smetsers 1996):
> In both conventional and uniqueness type systems, typing is preserved during evaluation, and types can be determined effectively. Moreover, with respect to a graph rewriting semantics, both type systems are sound.

This means:
1. **Subject reduction**: Well-typed terms reduce to well-typed terms
2. **Decidability**: Type inference is decidable
3. **Soundness**: If a term has unique type, it truly has one reference

### 2.5 Uniqueness Logic (Harrington 2006)

Dana Harrington established a **Curry-Howard-Lambek correspondence** between uniqueness types and a resource-sensitive logic:

**Key insight**: Uniqueness logic is similar to intuitionistic linear logic, but the modality (which moderates structural rules) is introduced via **dual rules** compared to linear logic's `!` (of course) modality.

**Structural rules**:
| Rule | Linear Logic | Uniqueness Logic |
|------|--------------|------------------|
| Contraction | Forbidden without `!` | Forbidden for unique |
| Weakening | Forbidden without `!` | Allowed (affine-like) |
| Exchange | Allowed | Allowed |

**Categorical semantics**: Uniqueness types correspond to certain closed categories with specific properties regarding copying and discarding.

---

## 3. Uniqueness Types in Clean

### 3.1 The Uniqueness Type System

Clean's type system combines:
1. **Milner/Hindley/Mycroft polymorphism**
2. **Uniqueness attributes** on types
3. **Coercion rules** between unique and non-unique

**Type grammar** (simplified):
```
Type := BasicType
      | *Type                    -- Unique type
      | [Type]                   -- List
      | {Type}                   -- Lazy array
      | {#Type}                  -- Strict array
      | (Type, Type, ...)        -- Tuple
      | Type -> Type             -- Function
      | TypeVar                  -- Polymorphic
      | u:Type                   -- Uniqueness polymorphic
```

### 3.2 Uniqueness Propagation Rules

**Coercion**: Unique values can be used where non-unique is expected (but not vice versa):
```
*T â‰¤ T    (unique can become non-unique)
T â‰° *T    (non-unique cannot become unique)
```

**Consumption**: Using a unique value makes it unavailable:
```clean
// VALID: x is consumed exactly once
f :: *Int -> Int
f x = x + 1

// INVALID: x used twice
g :: *Int -> Int
g x = x + x  // ERROR: x already consumed
```

**Propagation through data structures**:
```clean
// If list is unique, elements may be unique
*[*Int]    -- Unique list of unique integers

// Tuple uniqueness
*(Int, *File)  -- Unique tuple containing unique file
```

### 3.3 Uniqueness and I/O

Clean handles I/O through **world passing**:
```clean
// World type is unique - ensures sequential I/O
Start :: *World -> *World
Start world = snd (fclose file world2)
  where
    (file, world1) = fopen "test.txt" FReadText world
    (ok, world2)   = freadline file

// I/O primitive types
fopen  :: String Int *World -> (*File, *World)
fclose :: *File *World -> (Bool, *World)
fread  :: *File -> (String, *File)
```

**Key properties**:
1. `*World` is unique - cannot duplicate the world
2. Each I/O operation consumes the old world, produces new world
3. Sequencing is enforced by uniqueness
4. Compiler can safely perform destructive updates

### 3.4 Destructive Array Updates

One of the main practical benefits - O(1) array update:
```clean
// In-place array update (O(1) time)
update :: *{#Int} Int Int -> *{#Int}

// Usage
modifyArray :: *{#Int} -> *{#Int}
modifyArray arr = update arr 0 42

// Without uniqueness, would require O(n) copy:
updateCopy :: {#Int} Int Int -> {#Int}  // Must copy entire array
```

### 3.5 Uniqueness Polymorphism

Functions can be polymorphic in uniqueness:
```clean
// Works for both unique and non-unique lists
map :: (a -> b) u:[a] -> u:[b]

// Preserves uniqueness attribute of input
id :: u:a -> u:a

// Conditional uniqueness
swap :: u:(a, b) -> u:(b, a)
```

---

## 4. Comparison with Related Type Systems

### 4.1 Uniqueness vs Linear Types

| Aspect | Linear Types | Uniqueness Types |
|--------|--------------|------------------|
| **Guarantee** | Value used exactly once | At most one reference exists |
| **Perspective** | How value is *used* | How value is *aliased* |
| **Discarding** | Must be used (no weakening) | Can be discarded (weakening OK) |
| **Semantic basis** | Linear logic | Graph rewriting, ref counting |
| **Focus** | Consumption pattern | Reference structure |

**Critical difference**: Linear types track **usage** (each value used exactly once). Uniqueness types track **aliasing** (at most one reference exists). A unique value can be discarded without use; a linear value cannot.

### 4.2 Uniqueness vs Affine Types

| Aspect | Affine Types | Uniqueness Types |
|--------|--------------|------------------|
| **Constraint** | At most one use | At most one reference |
| **Rust analogy** | Ownership without `Drop` | Ownership with unique access |
| **Weakening** | Allowed | Allowed |
| **Contraction** | Forbidden | Forbidden for unique |

Uniqueness and affine types are closely related, both allowing values to be discarded. The difference is perspective: affine focuses on use count, uniqueness on reference count.

### 4.3 Uniqueness vs Rust Ownership

| Aspect | Rust Ownership | Clean Uniqueness |
|--------|----------------|------------------|
| **Single owner** | Yes (move semantics) | Yes (unique attribute) |
| **Borrowing** | Yes (&T, &mut T) | Limited (spread attribute) |
| **Lifetimes** | Explicit/inferred | Implicit |
| **Drop** | Automatic destructor | Garbage collected |
| **Interior mutability** | Cell, RefCell | Not applicable |

Rust's ownership system can be seen as an **operationalized uniqueness type system** with:
- Explicit lifetime annotations
- Borrowing for temporary shared access
- Affine types for owned values
- Destructor integration

### 4.4 Relationship to Fractional Permissions

Recent work by Marshall and Orchard (2024) shows that uniqueness and linearity can be unified through **fractional permissions** (Boyland 2003):

**Fractional permissions model**:
- Permission value in (0, 1]
- 1 = unique/mutable access
- < 1 = shared/immutable access
- Permissions must sum to â‰¤ 1

**Graded uniqueness**:
```
Permission p âˆˆ (0, 1]

Unique:   p = 1    (full permission, can mutate)
Borrowed: p < 1    (partial permission, read-only)
Sum rule: Î£ permissions â‰¤ 1
```

This generalizes Clean's binary unique/non-unique to a continuous spectrum.

---

## 5. Languages Implementing Uniqueness Types

### 5.1 Clean (Primary)

**Status**: Production language, active development
**Key features**:
- Full uniqueness type system with polymorphism
- Uniqueness-based I/O
- Efficient array operations
- IDE for Windows

**Example program**:
```clean
module Main

import StdEnv

Start :: *World -> *World
Start world
  # (console, world) = stdio world
  # console = fwrites "Hello, World!\n" console
  # (ok, world) = fclose console world
  = world
```

### 5.2 Mercury

**Status**: Production logic programming language
**Uniqueness approach**: Mode system with unique modes

**Unique modes**:
```mercury
:- mode uo == free >> unique.     % unique output
:- mode ui == unique >> unique.   % unique input (inspection)
:- mode di == unique >> dead.     % destructive input
```

**I/O handling**:
```mercury
main(!IO) :-
    io.write_string("Hello, World!\n", !IO).

% !IO is a state variable pair: IO0, IO
% Threaded uniquely through the program
```

**Features**:
- Declarative logic programming
- Mode system includes uniqueness
- Compile-time garbage collection possible
- Destructive updates with unique modes

### 5.3 Cogent

**Status**: Research language for verified systems code (CSIRO/Data61)
**Purpose**: Low-level OS components with formal verification

**Key innovation**: Two semantics with refinement proof
1. **Imperative semantics**: For efficient C code generation
2. **Functional semantics**: For equational reasoning and verification

**Type system features**:
- Uniqueness types (linear objects have one reference)
- No trusted runtime or garbage collector
- Certifying compiler (generates proof with code)

**Example**:
```cogent
-- File system read operation
read : (SysState, Inode!, Buffer) -> RR (SysState, Buffer) () ErrCode
```

**Verified properties**:
- Memory safety (no null pointer dereference)
- No signed integer overflow
- No memory leaks
- No double-free

### 5.4 Futhark

**Status**: GPU programming language
**Uniqueness approach**: Module system with uniqueness constraints

**Example** (preventing RNG bugs):
```futhark
module type rand = {
  type rng
  val mk_rng : i32 -> rng
  val rand : i32 -> *rng -> (rng, i32)  -- *rng is consumed
}
```

The `*` marks a consuming parameter - the RNG state cannot be reused after passing to `rand`, preventing accidental correlation in random numbers.

---

## 6. Formal Semantics Deep Dive

### 6.1 Natural Deduction Formulation

Barendsen and Smetsers presented uniqueness typing in **natural deduction style** (1995):

**Typing judgment**: Î“ âŠ¢ e : Ï„ @ u
- Î“: context
- e: expression
- Ï„: type
- u: uniqueness attribute (unique or non-unique)

**Key rules** (simplified):

**Variable**:
```
x : Ï„ @ u âˆˆ Î“
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ x : Ï„ @ u
```

**Abstraction**:
```
Î“, x : Ï„â‚ @ uâ‚ âŠ¢ e : Ï„â‚‚ @ uâ‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ Î»x.e : (Ï„â‚ @ uâ‚ â†’ Ï„â‚‚ @ uâ‚‚)
```

**Application with uniqueness**:
```
Î“â‚ âŠ¢ eâ‚ : (Ï„â‚ @ unique â†’ Ï„â‚‚) @ u
Î“â‚‚ âŠ¢ eâ‚‚ : Ï„â‚ @ unique
Î“â‚ âˆ© Î“â‚‚ contains no unique types
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“â‚ âˆª Î“â‚‚ âŠ¢ eâ‚ eâ‚‚ : Ï„â‚‚ @ u
```

**Uniqueness coercion**:
```
Î“ âŠ¢ e : Ï„ @ unique
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : Ï„ @ non-unique
```

### 6.2 Type Inference Algorithm

Clean uses **constraint-based type inference** extended for uniqueness:

1. **Generate constraints**: 
   - Type constraints (Ï„â‚ = Ï„â‚‚)
   - Uniqueness constraints (uâ‚ â‰¤ uâ‚‚)

2. **Solve type constraints**:
   - Standard Hindley-Milner unification

3. **Solve uniqueness constraints**:
   - Partial order: unique â‰¤ non-unique
   - Find consistent assignment of uniqueness attributes

4. **Generalize**:
   - Quantify over type variables
   - Quantify over uniqueness variables (u:)

### 6.3 Principal Types

Barendsen and Smetsers proved existence of **principal uniqueness variants**:

> Given a conventional type, there exists a most general uniqueness variant of that type.

This ensures type inference produces the most general type, allowing maximum reuse.

---

## 7. Applications and Use Cases

### 7.1 I/O Without Monads

Clean's uniqueness approach to I/O:

**Advantages over monads**:
1. No do-notation overhead
2. Direct functional style
3. Natural composition
4. Easier to understand for non-FP programmers

**Example comparison**:
```haskell
-- Haskell with IO monad
main :: IO ()
main = do
    handle <- openFile "test.txt" ReadMode
    contents <- hGetContents handle
    putStrLn contents
    hClose handle
```

```clean
-- Clean with uniqueness
Start :: *World -> *World
Start world
  # (ok, file, world) = fopen "test.txt" FReadText world
  # (contents, file) = fread file
  # world = snd (fclose file world)
  = world
```

### 7.2 Efficient Data Structures

**In-place array operations**:
```clean
// O(1) update for unique array
updateInPlace :: *{#Int} -> *{#Int}
updateInPlace arr = {arr & [0] = 42, [1] = 100}

// Would be O(n) for non-unique array
```

**Mutable state without monads**:
```clean
// Stateful computation with unique state
runStateful :: *State -> (*Result, *State)
runStateful state = 
    let (x, state1) = read state
        state2 = write x state1
    in (x, state2)
```

### 7.3 Safe Concurrent Programming

Uniqueness ensures thread safety for unique values:

```clean
// Unique channel - no races possible
send :: *Channel a a -> *Channel a
recv :: *Channel a -> (a, *Channel a)

// Fork with unique resources
fork :: (*World -> *World) *World -> *World
```

### 7.4 File System Verification (Cogent)

Cogent's uniqueness types enable verification of file system implementations:

**Verified file systems**:
1. **BilbyFS**: Custom flash file system
2. **ext2fs**: Standard Linux file system

**Properties verified**:
- Crash consistency
- No memory leaks
- No double-free
- Type safety
- Memory safety

---

## 8. Advanced Topics

### 8.1 Spread and Sharing

Clean provides **spread** for limited sharing of unique values:

```clean
// Spread: temporarily share a unique value
spread :: *a -> (a, a -> *a)
```

This allows inspection of unique values without consuming them, similar to borrowing in Rust.

### 8.2 Uniqueness and Laziness

Interaction between uniqueness and lazy evaluation:

**Challenge**: Lazy evaluation can delay reference creation, affecting uniqueness

**Solution**: Clean's graph rewriting semantics handles this:
- Uniqueness determined by graph structure
- Lazy thunks maintain reference information
- Forcing evaluation preserves uniqueness invariants

### 8.3 External Uniqueness

Clarke and Wrigstad (2003) proposed **external uniqueness**:
> A reference is externally unique if it is the only reference into an aggregate from outside that aggregate.

This relaxes pure uniqueness to allow internal aliasing within a data structure while maintaining unique external access.

### 8.4 Uniqueness Typing Simplified (de Vries 2008)

Simplifications to uniqueness type system:
1. **Removing coercion subtyping**: Direct attribute handling
2. **Simpler inference**: Reduced constraint solving
3. **Better integration**: With modern type system features

---

## 9. Uniqueness and Security Applications

### 9.1 Capability-Based Security

Unique capabilities cannot be duplicated:
```
capability :: *Capability
use :: *Capability -> Result  -- consumes the capability
```

### 9.2 One-Time Tokens

```clean
// Token can only be used once
validateToken :: *Token -> Bool
validateToken token = ... // token is consumed

// Cannot replay - token is gone after validation
```

### 9.3 Secure State Transitions

```clean
// State machine with unique states
data State = Initial | Authenticated | Authorized

transition :: *Initial -> *Authenticated
transition state = ...  // original state consumed

// Cannot return to previous state
```

### 9.4 Memory Safety Without GC

Uniqueness enables:
- Compile-time deallocation points
- No use-after-free (consumed values unavailable)
- No double-free (can only free once)
- No data races (unique values have single owner)

---

## 10. Comparison with Rust's Approach

### 10.1 Ownership as Operationalized Uniqueness

Rust's ownership model implements uniqueness concepts:

| Clean Concept | Rust Implementation |
|---------------|---------------------|
| `*T` (unique) | Owned value `T` |
| Non-unique | Shared reference `&T` |
| Spread | Borrowing |
| Consume | Move semantics |
| World threading | Lifetime system |

### 10.2 Key Differences

**Type-level vs Value-level**:
- Clean: Uniqueness in types (`*Int`)
- Rust: Ownership in values/lifetimes

**Borrowing model**:
- Clean: Limited spread mechanism
- Rust: Rich borrowing with lifetimes, multiple borrows

**Destruction**:
- Clean: Garbage collected
- Rust: Deterministic Drop

**Mutability**:
- Clean: Uniqueness enables mutation
- Rust: Separate `mut` qualifier

### 10.3 What Rust Adds

1. **Lifetime annotations**: Explicit region reasoning
2. **Non-lexical lifetimes**: Dataflow-based analysis
3. **Interior mutability**: Cell, RefCell, atomic types
4. **Destructor ordering**: Guaranteed cleanup
5. **Unsafe escape hatch**: When needed

### 10.4 What Clean Provides That Rust Doesn't

1. **Type-level uniqueness**: Uniqueness is first-class in types
2. **Uniqueness polymorphism**: Functions polymorphic in uniqueness
3. **Simpler model**: No lifetime annotations
4. **Pure functional semantics**: Easier equational reasoning

---

## 11. TERAS-LANG Relevance

### 11.1 Uniqueness for Security Properties

**One-time credentials**:
```teras
// TERAS example: unique cryptographic key
type SigningKey = lin Key  // linear/unique

fn sign(key: lin SigningKey, message: Bytes) -> Signature {
    // key is consumed - cannot sign twice with same key instance
}
```

**Capability tokens**:
```teras
// Unique capability cannot be duplicated
type NetworkCap = lin Cap<Network>

fn send(cap: lin NetworkCap, data: Bytes) -> (lin NetworkCap, Result) {
    // Must thread capability through operations
}
```

### 11.2 Integration with TERAS Type System

Uniqueness complements existing TERAS type features:

| TERAS Feature | Uniqueness Benefit |
|---------------|-------------------|
| IFC labels | Unique secrets prevent leakage |
| Capabilities | Unique caps prevent ambient authority |
| Session types | Unique endpoints ensure protocol |
| Refinement types | Unique + refined for strong guarantees |

### 11.3 Recommended Approach for TERAS-LANG

Based on A-04 (Linear Types) decision and this research:

1. **Primary mechanism**: Graded linear/affine types (from A-04)
2. **Uniqueness attribute**: As special case of linear (multiplicity = 1)
3. **Syntax**: `lin T` for linear, `uniq T` for unique emphasis
4. **Semantics**: Reference-counting semantics for unique values
5. **Coercion**: unique â†’ affine â†’ unrestricted

### 11.4 Key Insights for Implementation

1. **Graph rewriting semantics** provides clear reference model
2. **Uniqueness polymorphism** enables generic programming
3. **Spread/borrowing** necessary for practical use
4. **Integration with effects** through unique world/state threading
5. **Security tokens** as unique capabilities

---

## 12. Key Research Papers

### Foundational Papers

1. **Barendsen & Smetsers (1996)**: "Uniqueness Typing for Functional Languages with Graph Rewriting Semantics"
   - Formal semantics of uniqueness types
   - Soundness proofs
   - Principal types theorem

2. **Barendsen & Smetsers (1993)**: "Conventional and Uniqueness Typing in Graph Rewrite Systems"
   - Initial formalization
   - FSTTCS conference

3. **Harrington (2006)**: "Uniqueness Logic"
   - Curry-Howard correspondence
   - Categorical semantics
   - Theoretical Computer Science journal

### Language Implementations

4. **Plasmeijer & van Eekelen (1999)**: "Keep It Clean: A Unique Approach to Functional Programming"
   - Clean language design
   - I/O system
   - Practical applications

5. **Somogyi et al. (1996)**: "The Execution Algorithm of Mercury"
   - Mercury's unique modes
   - Logic programming integration

6. **O'Connor et al. (2021)**: "Cogent: Uniqueness Types and Certifying Compilation"
   - Verified systems programming
   - Two-semantics approach
   - Journal of Functional Programming

### Recent Developments

7. **Marshall & Orchard (2024)**: "Functional Ownership through Fractional Uniqueness"
   - Graded uniqueness
   - Integration with linear types
   - Fractional permissions

8. **de Vries et al. (2007)**: "Uniqueness Typing Redefined"
   - Simplified formulation
   - Better inference

---

## 13. Summary and Conclusions

### Key Takeaways

1. **Uniqueness types** track reference counts, not usage counts
2. **Clean** pioneered uniqueness for I/O and efficient updates
3. **Graph rewriting semantics** provides formal foundation
4. **Uniqueness â‰ˆ affine** but with reference-counting perspective
5. **Rust** operationalizes uniqueness as ownership
6. **Cogent** demonstrates verification potential
7. **Fractional permissions** generalize uniqueness/linearity

### For TERAS-LANG

Uniqueness types provide:
- **Alternative perspective** on resource management
- **Security tokens** as unique capabilities
- **Efficient updates** for cryptographic state
- **I/O handling** without monadic overhead
- **Verification benefits** for formal proofs

Recommend integrating uniqueness as a **semantic interpretation** of linear types in TERAS-LANG, with Rust-style syntax and Clean-style theoretical foundation.

---

## Document Metadata

```yaml
document_id: RESEARCH_A06_UNIQUENESS_TYPES_SURVEY
version: 1.0.0
date: 2026-01-03
session: A-06
domain: Type Theory Foundations
sources_analyzed: 52
pages: ~28
status: COMPLETE
```
