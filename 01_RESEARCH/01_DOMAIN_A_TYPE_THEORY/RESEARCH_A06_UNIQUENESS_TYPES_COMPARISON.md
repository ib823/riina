# RESEARCH_A06_UNIQUENESS_TYPES_COMPARISON

## Session A-06: Uniqueness Types Comparative Analysis

**Research Track**: Domain A - Type Theory Foundations
**Session**: A-06 of 20
**Date**: 2026-01-03
**Status**: COMPARATIVE ANALYSIS

---

## 1. Substructural Type Systems Taxonomy

### 1.1 Structural Rules Overview

| Rule | What it Allows | Substructural Restriction |
|------|----------------|--------------------------|
| **Weakening** | Ignore/discard values | Removing prevents unused values |
| **Contraction** | Use values multiple times | Removing prevents aliasing |
| **Exchange** | Reorder values | Removing enforces ordering |

### 1.2 Type System Classification

| Type System | Weakening | Contraction | Exchange | Uses |
|-------------|-----------|-------------|----------|------|
| **Normal** | ✓ | ✓ | ✓ | Any number |
| **Affine** | ✓ | ✗ | ✓ | At most once |
| **Relevant** | ✗ | ✓ | ✓ | At least once |
| **Linear** | ✗ | ✗ | ✓ | Exactly once |
| **Ordered** | ✗ | ✗ | ✗ | Exactly once, in order |
| **Uniqueness** | ✓ | ✗ | ✓ | At most one reference |

### 1.3 Critical Distinction: Use vs Reference

| Perspective | Focus | Question Asked |
|-------------|-------|----------------|
| **Linear/Affine** | Usage count | "How many times is this value used?" |
| **Uniqueness** | Reference count | "How many references point to this value?" |

This distinction matters:
- **Linear**: Must use value exactly once (no drop)
- **Affine**: May use value at most once (can drop)
- **Uniqueness**: At most one reference exists (implies affine usage)

---

## 2. Uniqueness vs Linear Types

### 2.1 Fundamental Semantic Difference

| Aspect | Linear Types | Uniqueness Types |
|--------|--------------|------------------|
| **Core invariant** | Each binding used exactly once | At most one reference exists |
| **Can discard?** | No (must consume) | Yes (can be garbage collected) |
| **Formal basis** | Linear logic | Graph rewriting semantics |
| **Destruction** | Explicit consumption | Implicit GC |
| **Resource view** | Value is resource | Reference is resource |

### 2.2 Code Comparison

**Linear (must use)**:
```
fn consume_linear(x: lin T) {
    // MUST use x somehow
    drop(x);  // explicit drop required
}

fn unused_linear(x: lin T) {
    // ERROR: x not used
}
```

**Uniqueness (at most one reference)**:
```clean
consume_unique :: *T -> ()
consume_unique x = ()  // OK: x implicitly discarded

unused_unique :: *T -> ()
unused_unique x = ()   // Also OK in Clean
```

### 2.3 When They Coincide

Linear and uniqueness types provide **equivalent guarantees** when:
1. Value is used exactly once
2. No aliasing occurs during use
3. Resource is consumed at end

Divergence occurs when:
1. Value needs to be discarded → Uniqueness allows, linear forbids
2. Value passed to multiple call sites → Both forbid, but different reasons

### 2.4 Practical Implications

| Use Case | Linear Better | Uniqueness Better |
|----------|---------------|-------------------|
| Must-use resources | ✓ | |
| File handles | ✓ | |
| Optional cleanup | | ✓ |
| Efficient updates | | ✓ |
| Pure functional I/O | | ✓ |
| Protocol completion | ✓ | |

---

## 3. Uniqueness vs Affine Types

### 3.1 Closer Relationship

Uniqueness types are semantically closer to affine types:

| Property | Affine Types | Uniqueness Types |
|----------|--------------|------------------|
| Weakening | ✓ (can discard) | ✓ (can discard) |
| Contraction | ✗ (no duplication) | ✗ (no aliasing) |
| Perspective | Use-based | Reference-based |

### 3.2 Subtle Differences

**Affine (use at most once)**:
```rust
fn take_affine(x: Affine<T>) {
    // Can use x once
    let _ = x;  // moved
    // Cannot use x again
}

fn discard_affine(x: Affine<T>) {
    // OK to just let x drop
}
```

**Uniqueness (at most one reference)**:
```clean
// Uniqueness tracked at type level
take_unique :: *T -> R
take_unique x = use x

// Can "spread" unique for inspection
inspect_unique :: *T -> (*T, Info)
inspect_unique x = spread x (\y -> (y, getInfo y))
```

### 3.3 Key Insight

> **Uniqueness implies affine behavior, but affine doesn't imply uniqueness.**

Uniqueness is a **stronger property** - it guarantees the reference structure, not just usage pattern. This enables:
- Safe in-place updates (know there's only one reference)
- Efficient memory reuse
- Simpler reasoning about sharing

---

## 4. Uniqueness vs Rust Ownership

### 4.1 Conceptual Mapping

| Clean/Uniqueness | Rust/Ownership |
|------------------|----------------|
| `*T` (unique) | `T` (owned) |
| Non-unique `T` | `&T` (shared ref) |
| Consume unique | Move semantics |
| Spread | Borrowing |
| Uniqueness polymorphism | Generic over ownership |

### 4.2 Feature Comparison

| Feature | Clean Uniqueness | Rust Ownership |
|---------|------------------|----------------|
| **Type annotation** | `*T` prefix | Ownership implicit |
| **Borrowing** | Spread (limited) | Rich (`&T`, `&mut T`) |
| **Lifetimes** | Implicit | Explicit/inferred |
| **Destruction** | GC | Deterministic Drop |
| **Mutability** | Via uniqueness | Via `mut` |
| **Interior mutability** | No | Cell, RefCell |
| **Polymorphism** | Uniqueness vars | Lifetime parameters |

### 4.3 Borrowing Models

**Clean spread**:
```clean
// Limited: get value and continuation
spread :: *a -> (a, a -> *a)

usage :: *Array -> (*Array, Int)
usage arr = 
    let (a, restore) = spread arr
        val = a.[0]
        arr' = restore a
    in (arr', val)
```

**Rust borrowing**:
```rust
fn usage(arr: &mut Vec<i32>) -> i32 {
    arr[0]  // Borrow, don't consume
}

fn main() {
    let mut arr = vec![1, 2, 3];
    let x = usage(&mut arr);  // Borrow
    arr.push(4);  // Still usable
}
```

Rust's borrowing is more flexible and ergonomic.

### 4.4 Advantages of Each

**Clean Uniqueness Advantages**:
1. Type-level uniqueness attribute
2. No lifetime annotations
3. Cleaner functional semantics
4. Easier equational reasoning
5. Uniqueness polymorphism built-in

**Rust Ownership Advantages**:
1. Rich borrowing model
2. Deterministic destruction
3. No GC overhead
4. Interior mutability patterns
5. Zero-cost abstractions
6. Industry adoption

---

## 5. Language Implementation Comparison

### 5.1 Clean

**Type System**:
```clean
// Unique array with polymorphic element
*{#a}

// Unique function type
*Int -> *Int

// Uniqueness polymorphism
u:a -> u:a
```

**Strengths**:
- Pioneer of uniqueness types
- Mature implementation
- Good for teaching

**Weaknesses**:
- Limited adoption
- Spread mechanism clunky
- GC required

### 5.2 Mercury

**Mode System**:
```mercury
:- mode uo == free >> unique.
:- mode ui == unique >> unique.
:- mode di == unique >> dead.

:- pred process(array::di, array::uo) is det.
```

**Strengths**:
- Integrates with logic programming
- Compile-time GC possible
- Strong determinism system

**Weaknesses**:
- Complex mode system
- Niche language
- Steep learning curve

### 5.3 Cogent

**Type System**:
```cogent
-- Unique buffer
type Buffer

read : (SysState, Buffer!) -> RR SysState (Buffer, Data) ErrCode
write : (SysState, Buffer, Data) -> RR SysState Buffer ErrCode
```

**Strengths**:
- Verification integration
- C code generation
- Proof generation
- seL4 ecosystem

**Weaknesses**:
- Research language
- Limited features
- Specific to systems code

### 5.4 Comparison Matrix

| Language | Uniqueness | Borrowing | Verification | Production |
|----------|------------|-----------|--------------|------------|
| Clean | Full | Limited | No | Yes |
| Mercury | Via modes | No | No | Yes |
| Cogent | Full | No | Yes | Research |
| Rust | Via ownership | Full | Limited | Yes |
| Futhark | Limited | No | No | Yes |

---

## 6. Theoretical Comparison

### 6.1 Formal Foundations

| System | Foundation | Key Property |
|--------|------------|--------------|
| Linear types | Linear logic | Girard's resource semantics |
| Affine types | Affine logic | Weakening allowed |
| Uniqueness | Graph rewriting | Reference count invariant |
| Rust | Affine + regions | Operational semantics |

### 6.2 Categorical Semantics

**Linear types**: Symmetric monoidal closed categories
**Uniqueness types**: Categories with copying constraints (Harrington's uniqueness logic)

**Key difference**: 
- Linear: ⊗ (tensor) doesn't admit diagonal
- Uniqueness: Diagonal exists but is constrained by reference structure

### 6.3 Proof-Theoretic Comparison

| Logic | Structural Rules | Modality |
|-------|------------------|----------|
| Linear | No W, no C | ! for unlimited |
| Affine | W, no C | Similar to linear |
| Uniqueness | W, no C (unique) | Dual to ! |

Harrington showed uniqueness logic uses modality rules **dual** to linear logic's `!`.

---

## 7. Security Applications Comparison

### 7.1 Capability-Based Security

| Approach | How Capabilities Work |
|----------|----------------------|
| Linear | Capability consumed on use |
| Affine | Capability can be dropped |
| Uniqueness | Capability has one reference |
| Rust | Capability moved on use |

**Best for security**: Linear (ensures use) or Uniqueness (prevents sharing)

### 7.2 Information Flow Control

| Type System | IFC Support |
|-------------|-------------|
| Linear | Secrets must be consumed |
| Affine | Secrets can be dropped |
| Uniqueness | Secrets have unique reference |
| Rust | Secrets moved, not copied |

**For TERAS**: Uniqueness + IFC labels provide strong secret handling.

### 7.3 Cryptographic Key Management

**Linear approach**:
```
fn sign(key: lin Key, msg: &[u8]) -> Signature {
    // key MUST be consumed
    internal_sign(key, msg)
}
// key gone - good for one-time keys
```

**Uniqueness approach**:
```clean
sign :: *Key [Byte] -> (*Key, Signature)
sign key msg = 
    let sig = internalSign key msg
    in (key, sig)  // Can keep using if needed
```

**Rust approach**:
```rust
fn sign(key: SecretKey, msg: &[u8]) -> Signature {
    // key moved, will be dropped after
    key.sign(msg)
}
```

---

## 8. Integration Strategies

### 8.1 Linear + Uniqueness

Marshall & Orchard (2024) show these can coexist:

```
-- Linearity (usage count)
lin(1) T  -- use exactly once

-- Uniqueness (reference count)  
uniq T    -- at most one reference

-- Combined
lin(1) uniq T  -- use exactly once AND unique reference
```

### 8.2 Graded Approach

**Quantitative type theory** framework:
```
Type annotations: T @ (usage, uniqueness)

Examples:
T @ (ω, shared)   -- unlimited use, shared
T @ (1, unique)   -- linear, unique
T @ (0-1, unique) -- affine, unique
T @ (1+, shared)  -- relevant, shared
```

### 8.3 Fractional Permissions

Generalize uniqueness to fractional permissions:

| Permission | Meaning | Alias for |
|------------|---------|-----------|
| 1 | Full/unique | Mutable access |
| ½ | Half | Shared immutable |
| ¼ | Quarter | More sharing |
| 0 | None | No access |

**Rust analogy**:
- `&mut T` ≈ permission = 1
- `&T` ≈ permission < 1 (shared with others)

---

## 9. TERAS-LANG Recommendations

### 9.1 Type System Design

Based on comparative analysis, recommend:

1. **Primary framework**: Graded linear types (from A-04)
2. **Uniqueness**: As semantic property of linear(1) types
3. **Borrowing**: Rust-style with lifetimes
4. **Syntax**: Clean-inspired annotations

### 9.2 Proposed Syntax

```teras
// Linear type (must use exactly once)
lin T

// Affine type (use at most once)  
affine T

// Unique reference (at most one reference)
uniq T

// Combined
lin uniq Key  // Linear unique key

// Borrowing
&T       // Shared reference
&mut T   // Unique mutable reference

// Lifetime annotations
&'a T    // Reference with lifetime 'a
```

### 9.3 Semantic Model

**Reference to Clean**: Graph rewriting semantics for uniqueness
**Reference to Rust**: Operational semantics for borrowing
**Reference to Linear Haskell**: Graded multiplicities

### 9.4 Security Features

```teras
// One-time token (linear)
type OTP = lin Token

// Unique capability (cannot be shared)
type SecureCap = uniq Cap<Privilege>

// Secret key (linear unique)
type SigningKey = lin uniq Key<Ed25519>
```

---

## 10. Conclusion

### 10.1 Key Findings

| Finding | Implication |
|---------|-------------|
| Uniqueness ≠ Linear | Different constraints, complementary |
| Uniqueness ≈ Affine | Similar behavior, different perspective |
| Clean pioneered | Strong theoretical foundation |
| Rust operationalized | Practical, adopted approach |
| Grading unifies | Single framework for all |

### 10.2 For TERAS-LANG

**Adopt**: Graded linear types with Rust-style borrowing
**Integrate**: Uniqueness as reference-count interpretation
**Extend**: For security-specific use cases (capabilities, tokens)

### 10.3 Decision Preview

Based on this comparison, A-06 decision will recommend:
- Clean's uniqueness semantics for theoretical foundation
- Rust's ownership model for practical implementation
- Graded types for unified framework
- Security-focused extensions for TERAS requirements

---

## Document Metadata

```yaml
document_id: RESEARCH_A06_UNIQUENESS_TYPES_COMPARISON
version: 1.0.0
date: 2026-01-03
session: A-06
domain: Type Theory Foundations
comparison_dimensions: 10
status: COMPLETE
```
