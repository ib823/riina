# RESEARCH_A04_LINEAR_TYPES_COMPARISON.md

## TERAS Research Track — Session A-04
## Linear Types and Substructural Logic: Comparative Analysis

**Document Version:** 1.0.0  
**Created:** 2026-01-03  
**Status:** COMPLETE  
**Classification:** TERAS Research Foundation

---

## Executive Summary

This document provides a systematic comparative analysis of linear type systems and their variants for TERAS-LANG integration. We evaluate strict linear types, affine types (Rust model), uniqueness types (Clean model), and graded/quantitative approaches across multiple dimensions: expressiveness, ergonomics, verification power, performance, and security guarantees. The analysis informs architectural decisions for how TERAS-LANG will handle resource ownership, borrowing, and security-critical data flows.

---

## Table of Contents

1. [Comparison Framework](#1-comparison-framework)
2. [Substructural Variants Comparison](#2-substructural-variants-comparison)
3. [Implementation Approaches Comparison](#3-implementation-approaches-comparison)
4. [Borrowing Mechanisms Analysis](#4-borrowing-mechanisms-analysis)
5. [Integration with Other Type Features](#5-integration-with-other-type-features)
6. [Security Applications Comparison](#6-security-applications-comparison)
7. [Ergonomics and Usability](#7-ergonomics-and-usability)
8. [Performance Characteristics](#8-performance-characteristics)
9. [TERAS Requirements Alignment](#9-teras-requirements-alignment)
10. [Comparative Decision Matrix](#10-comparative-decision-matrix)
11. [Recommendations](#11-recommendations)

---

## 1. Comparison Framework

### 1.1 Evaluation Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| **Security Guarantees** | 25% | Ability to enforce security invariants |
| **Resource Safety** | 20% | Prevention of resource leaks/misuse |
| **Expressiveness** | 15% | Ability to express complex patterns |
| **Decidability** | 15% | Type checking termination guarantees |
| **Ergonomics** | 10% | Developer experience and learning curve |
| **Performance** | 10% | Runtime and compile-time overhead |
| **Tooling** | 5% | Ecosystem maturity |

### 1.2 Comparison Categories

1. **Substructural Variants:** Linear vs Affine vs Relevant vs Ordered
2. **Implementation Models:** Rust-style vs Clean-style vs ATS-style
3. **Borrowing Mechanisms:** Region-based vs Permission-based vs Capability-based
4. **Integration Approaches:** Standalone vs Combined with dependent/refinement types
5. **Security Features:** Key management, capability systems, protocol verification

### 1.3 Baseline Requirements for TERAS

| Requirement | Priority | Description |
|-------------|----------|-------------|
| Cryptographic key safety | Critical | Keys cannot leak or duplicate |
| Capability enforcement | Critical | Access rights properly tracked |
| Session protocol safety | High | Protocol states enforced |
| Memory safety | High | No use-after-free, double-free |
| Zero runtime overhead | High | Type erasure, no GC |
| Decidable type checking | High | Compilation must terminate |
| Integration with refinements | Medium | Combine with A-03 results |
| Ergonomic borrowing | Medium | Practical for large codebases |

---

## 2. Substructural Variants Comparison

### 2.1 Linear Types (Exact Once)

**Definition:** Values must be used exactly once.

**Structural Rules:**
- Exchange: ✓
- Contraction: ✗
- Weakening: ✗

**Strengths:**
```
+ Perfect resource tracking
+ No accidental leaks possible
+ Ideal for cryptographic keys
+ Clean categorical semantics (SMCC)
+ Protocol state precisely tracked
```

**Weaknesses:**
```
- Error handling awkward (must handle unused values)
- Cannot easily discard unneeded resources
- Every branch must consume linear values
- Verbose without syntactic sugar
```

**Example Issue:**
```
// Linear types: problem with conditional
fn process(key: Key ⊸) -> Result {
    if condition {
        use_key(key)?  // key consumed
    } else {
        // PROBLEM: key must be consumed here too!
        destroy_key(key)  // must explicitly destroy
    }
}
```

**TERAS Fit:** Excellent for critical resources (keys, capabilities), but too strict for general programming.

### 2.2 Affine Types (At Most Once)

**Definition:** Values may be used at most once (zero or one times).

**Structural Rules:**
- Exchange: ✓
- Contraction: ✗
- Weakening: ✓

**Strengths:**
```
+ Allows discarding unused values
+ Error handling via early return
+ Simpler mental model
+ Rust demonstrates practicality
+ Drop semantics for cleanup
```

**Weaknesses:**
```
- Cannot guarantee use (audit trail issue)
- Implicit discarding may hide bugs
- Less precise than linear for protocols
```

**Example Advantage:**
```rust
// Affine types: natural error handling
fn process(key: Key) -> Result<(), Error> {
    if !condition {
        return Err(Error::Skip);  // key implicitly dropped
    }
    use_key(key)?;
    Ok(())
}
```

**TERAS Fit:** Good default for most resources; need additional mechanism for must-use resources.

### 2.3 Relevant Types (At Least Once)

**Definition:** Values must be used at least once (possibly multiple times).

**Structural Rules:**
- Exchange: ✓
- Contraction: ✓
- Weakening: ✗

**Strengths:**
```
+ Ensures resources are always used
+ Perfect for audit logging
+ Error messages must be handled
+ Notification delivery guaranteed
```

**Weaknesses:**
```
- Allows aliasing (contraction)
- Cannot track unique ownership
- Less common, fewer implementations
```

**Example Use:**
```
// Relevant types: guaranteed audit
fn security_action(entry: AuditEntry) {
    // entry MUST be used at least once
    log(entry);
    // Can use again if needed
    backup_log(entry);
}
// ERROR if entry never used
```

**TERAS Fit:** Essential for audit trail enforcement, error handling requirements.

### 2.4 Ordered Types (Exact Once, In Order)

**Definition:** Values used exactly once, in introduction order (stack discipline).

**Structural Rules:**
- Exchange: ✗
- Contraction: ✗
- Weakening: ✗

**Strengths:**
```
+ Models stack allocation perfectly
+ Very efficient implementation
+ Clear memory layout
```

**Weaknesses:**
```
- Too restrictive for most programs
- Cannot pass arguments out of order
- Limited practical applicability
```

**TERAS Fit:** Too restrictive; not recommended for general use.

### 2.5 Substructural Comparison Matrix

| Property | Linear | Affine | Relevant | Ordered |
|----------|--------|--------|----------|---------|
| **Use count** | =1 | ≤1 | ≥1 | =1 |
| **Can duplicate** | ✗ | ✗ | ✓ | ✗ |
| **Can discard** | ✗ | ✓ | ✗ | ✗ |
| **Can reorder** | ✓ | ✓ | ✓ | ✗ |
| **Key safety** | ★★★ | ★★☆ | ★☆☆ | ★★★ |
| **Audit safety** | ★★☆ | ★☆☆ | ★★★ | ★★☆ |
| **Ergonomics** | ★☆☆ | ★★★ | ★★☆ | ☆☆☆ |
| **Error handling** | ★☆☆ | ★★★ | ★★☆ | ☆☆☆ |
| **Implementations** | Few | Rust | Rare | Very rare |

---

## 3. Implementation Approaches Comparison

### 3.1 Rust Ownership Model

**Key Features:**
- Affine by default
- Borrowing system
- Lifetimes
- Drop trait
- Interior mutability

**Ownership Rules:**
```rust
// 1. Each value has one owner
let s = String::from("hello");

// 2. Value dropped when owner goes out of scope
{
    let s = String::from("hello");
} // s dropped here

// 3. Ownership can be transferred
let s2 = s; // s moved to s2
```

**Borrowing:**
```rust
// Immutable borrow: multiple allowed
let r1 = &s;
let r2 = &s;

// Mutable borrow: exclusive
let r3 = &mut s;
// Cannot have r1, r2 while r3 exists
```

**Strengths:**
- Proven in production (Linux kernel, Firefox)
- Zero runtime overhead
- Excellent tooling
- Large ecosystem

**Weaknesses:**
- Complex lifetime annotations
- Learning curve ("fighting the borrow checker")
- Cannot express some patterns (self-referential structs)

### 3.2 Clean Uniqueness Types

**Key Features:**
- Unique vs non-unique type distinction
- Subtyping: unique ≤ non-unique
- No explicit lifetimes
- Coercion from unique to non-unique

**Syntax:**
```clean
:: *World           // unique type
:: [a]              // non-unique list

// Uniqueness propagation
fopen :: String *World -> (*File, *World)
fclose :: *File *World -> *World
```

**Strengths:**
- Simpler than Rust (no lifetimes)
- Efficient I/O without monads
- Clean integration with functional style

**Weaknesses:**
- Less flexible than borrowing
- No temporary aliasing
- Limited practical adoption

### 3.3 ATS Linear Views

**Key Features:**
- Separation of views (proofs) and values
- Linear views for resource tracking
- Theorem proving in types
- Manual memory management

**Syntax:**
```ats
// View type: permission to access memory
viewtype ptr_v (a:viewtype, l:addr) = a @ l

// Linear function
fn free {a:viewtype} {l:addr} 
    (pf: a @ l | p: ptr l): void

// Usage
implement main () = let
    val (pf | p) = malloc<int>()
    val () = !p := 42
    val () = free(pf | p)
in end
```

**Strengths:**
- Most expressive system
- Full dependent types integration
- C-level performance
- Formal verification

**Weaknesses:**
- Very steep learning curve
- Verbose annotations
- Small community

### 3.4 Linear Haskell

**Key Features:**
- Multiplicity annotations
- Backwards compatible
- Higher-order linear functions
- Multiplicity polymorphism

**Syntax:**
```haskell
-- Linear function (arrow with multiplicity 1)
consume :: a %1 -> ()

-- Unrestricted function (normal arrow, multiplicity Many)
use :: a -> b

-- Multiplicity polymorphic
map :: (a %p -> b) -> [a] %p -> [b]
```

**Strengths:**
- Retrofits to existing language
- Higher-order friendly
- Multiplicity polymorphism elegant

**Weaknesses:**
- GHC-specific
- Ecosystem not yet adapted
- Limited adoption

### 3.5 Implementation Comparison Matrix

| Feature | Rust | Clean | ATS | Linear Haskell |
|---------|------|-------|-----|----------------|
| **Linearity model** | Affine | Unique | Linear views | Multiplicity |
| **Borrowing** | ✓ | ✗ | ✓ | ✗ |
| **Lifetimes** | Explicit | Implicit | Explicit | Implicit |
| **Dependent types** | ✗ | ✗ | ✓ | Limited |
| **Learning curve** | Medium | Low | Very High | Medium |
| **Production ready** | ✓✓✓ | ✓ | ✓ | ✓ |
| **Zero GC** | ✓ | ✓ | ✓ | ✗ |
| **TERAS alignment** | High | Medium | High | Medium |

---

## 4. Borrowing Mechanisms Analysis

### 4.1 Region-Based Borrowing (Rust)

**Mechanism:**
- References have lifetimes
- Lifetimes are regions of code
- Borrow checker validates no dangling references

**Notation:**
```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str
```

**Advantages:**
- Precise control over alias scope
- Compiler can optimize based on lifetime
- Interoperable with ownership

**Disadvantages:**
- Annotation burden
- Lifetime elision rules complex
- Higher-ranked lifetimes difficult

### 4.2 Permission-Based (Mezzo, Alms)

**Mechanism:**
- Permissions are linear capabilities
- Access requires holding permission
- Permissions can be split/combined

**Notation:**
```mezzo
val ref : a -> (r: ref a, r @ ref a)
val get : (r: ref a | r @ ref a) -> a
```

**Advantages:**
- Fine-grained access control
- Explicit about what's borrowed
- Compositional

**Disadvantages:**
- Verbose
- Permission management overhead
- Less intuitive

### 4.3 Capability-Based (Pony)

**Mechanism:**
- Reference capabilities: iso, val, ref, box, tag, trn
- Deny and allow guarantees
- Actor model integration

**Notation:**
```pony
class iso MyClass  // isolated: unique mutable
class val MyClass  // value: immutable, shareable
class ref MyClass  // reference: unique identity
```

**Advantages:**
- Actor-safe by design
- Fine-grained capability lattice
- No data races possible

**Disadvantages:**
- Complex capability system
- Steep learning curve
- Limited ecosystem

### 4.4 Borrowing Comparison

| Aspect | Rust Lifetimes | Permissions | Capabilities |
|--------|---------------|-------------|--------------|
| **Granularity** | Lexical/NLL | Fine | Coarse |
| **Annotation** | Heavy | Very Heavy | Medium |
| **Learning** | Medium | Hard | Hard |
| **Concurrency** | Manual | Manual | Built-in |
| **Flexibility** | High | Very High | Medium |

---

## 5. Integration with Other Type Features

### 5.1 Linear + Dependent Types

**ATS Approach:**
- Separate domains: statics (types) and dynamics (values)
- Linear views in static domain
- Full dependent types available

**Advantages:**
- Maximum expressiveness
- Can prove complex properties
- Protocol state in types

**Challenges:**
- Significant complexity
- Type inference limited
- Large annotation burden

**Example:**
```ats
// Dependent linear type: array with proof of valid index
fn array_get {a:viewtype} {n:nat} {i:nat | i < n} {l:addr}
    (pf: @[a][n] @ l | p: ptr l, i: int i): (a @ l[i] -<lin,prf> @[a][n] @ l | a)
```

### 5.2 Linear + Refinement Types

**F* Approach:**
- Effect system with linear resources
- Refinement predicates on state
- Pre/post conditions

**Example:**
```fstar
val read_file: f:file{isOpen f} -> ST (string & file{isClosed f})
    (requires (fun h -> h `contains` f))
    (ensures (fun h0 r h1 -> ...))
```

**Advantages:**
- SMT automation
- Familiar effect syntax
- Practical for verification

**Challenges:**
- Effect system complexity
- SMT solver dependence

### 5.3 Linear + Session Types

**Approach:** Channel types encode protocol state

**Example:**
```
type AuthChannel = !Username.?Challenge.!Response.?Result.end
```

**Advantages:**
- Protocol compliance enforced
- Deadlock freedom possible
- Natural linear semantics

**Challenges:**
- Channel mobility
- Delegation complexity

### 5.4 Integration Comparison

| Integration | Complexity | Power | TERAS Need |
|-------------|------------|-------|------------|
| Linear alone | Low | Medium | Partial |
| Linear + Dependent | Very High | Very High | Overkill |
| Linear + Refinement | Medium | High | Good |
| Linear + Session | Medium | High | Essential |
| Linear + Effects | High | High | Useful |

---

## 6. Security Applications Comparison

### 6.1 Cryptographic Key Management

**Linear Types:**
```
// Keys must be explicitly destroyed
type PrivateKey ⊸
derive : Seed ⊸ PrivateKey
sign : PrivateKey ⊗ Message → PrivateKey ⊗ Signature
destroy : PrivateKey ⊸ ()
```
- ✓ No key duplication
- ✓ Explicit destruction required
- ✗ Cannot temporarily share for operations

**Affine Types (Rust):**
```rust
fn sign(key: &PrivateKey, msg: &[u8]) -> Signature
// Key borrowed, not consumed
```
- ✓ Practical borrowing for operations
- ✗ Keys could be leaked (mem::forget)
- ✗ No guarantee of use

**TERAS Need:** Linear for key lifecycle, borrowing for operations.

### 6.2 Capability Systems

| Approach | Revocation | Attenuation | Ambient | Delegation |
|----------|------------|-------------|---------|------------|
| Linear caps | ✓ | ✓ | ✗ | ✓ |
| Affine caps | ✗ | ✓ | ✗ | ✓ |
| Object caps | ✓ | ✓ | ✗ | ✓ |

**Linear Capabilities:**
- Transfer is permanent
- Cannot revoke once given
- Clean semantics

**Token-Based:**
- Revocation via invalidation
- More flexible
- Requires runtime check

**TERAS Need:** Hybrid approach—linear for structure, runtime for revocation.

### 6.3 Protocol State Enforcement

**Session Types (Linear Channels):**
```
type TLSHandshake =
    !ClientHello.?ServerHello.?Certificate.
    !KeyExchange.!Finished.?Finished.!encrypted
```

**State Machines (Refinement):**
```
type Connection{s:State} where
    s ∈ {Idle, Handshaking, Established, Closed}
```

**Comparison:**
| Aspect | Session Types | State Machines |
|--------|--------------|----------------|
| Guarantee | Linear use | State validity |
| Flexibility | Protocol fixed | Dynamic transitions |
| Verification | Static | Static + runtime |

**TERAS Need:** Session types for protocol structure, refinements for state predicates.

### 6.4 Audit Trail Enforcement

**Relevant Types:**
```
type AuditEntry  // must use at least once
action : () → AuditEntry
log : AuditEntry → IO ()
// MUST call log on every AuditEntry
```

**Effect-Based:**
```
action : () → Audit AuditEntry
// Audit effect requires eventual logging
```

**TERAS Need:** Relevant types or effects for guaranteed audit.

---

## 7. Ergonomics and Usability

### 7.1 Learning Curve Comparison

| System | Initial Learning | Mastery | Typical Pain Points |
|--------|-----------------|---------|---------------------|
| Rust | 2-4 weeks | 6-12 months | Lifetimes, borrow checker |
| Clean | 1-2 weeks | 2-4 months | Uniqueness propagation |
| ATS | 2-3 months | 1-2 years | Views, theorem proving |
| Linear Haskell | 1-2 weeks | 2-4 months | Multiplicity reasoning |

### 7.2 Error Message Quality

**Rust:**
- Excellent error messages
- Suggestions for fixes
- NLL improved clarity

**ATS:**
- Cryptic error messages
- Requires deep understanding
- Limited tooling

**Linear Haskell:**
- Improving rapidly
- GHC quality baseline
- Multiplicity errors can confuse

### 7.3 Annotation Burden

| Operation | Rust | ATS | Linear Haskell |
|-----------|------|-----|----------------|
| Simple function | Low | High | Low |
| Borrowing | Medium | High | N/A |
| Generic code | Medium | Very High | Low |
| Complex protocols | High | Very High | Medium |

### 7.4 TERAS Ergonomics Requirements

**Must Have:**
- Clear error messages
- Minimal annotation for common cases
- IDE support for tracking ownership

**Nice to Have:**
- Inference for linearity where possible
- Visualizations of ownership flow
- Migration tooling from Rust

---

## 8. Performance Characteristics

### 8.1 Compile-Time Overhead

| System | Checking Complexity | Typical Impact |
|--------|-------------------|----------------|
| Rust (NLL) | O(n³) worst case | 10-30% of compile time |
| Linear types | O(n) context check | Minimal |
| Dependent linear | Undecidable (restricted) | Can be slow |
| Refinement linear | SMT calls | Variable |

### 8.2 Runtime Overhead

**Zero-Cost Systems:**
- Rust: All checks at compile time
- ATS: Type erasure, no runtime
- Clean: Uniqueness is compile-time

**Non-Zero-Cost:**
- RefCell: Runtime borrow checking
- Rc/Arc: Reference counting
- Session types: Sometimes runtime checks

### 8.3 Code Size Impact

| Approach | Code Bloat | Why |
|----------|-----------|-----|
| Monomorphization | High | Generic instantiation |
| Type erasure | None | Types removed |
| Proof terms | None | Erased at compile |

### 8.4 TERAS Performance Requirements

**Mandated:**
- Zero runtime overhead for type checking
- Performance ≥ equivalent hand-written C
- No garbage collection

**Implications:**
- Type erasure required
- Compile-time linearity checking only
- No runtime borrow checks in hot paths

---

## 9. TERAS Requirements Alignment

### 9.1 Security Requirements Mapping

| TERAS Requirement | Best Approach | Runner-Up |
|-------------------|--------------|-----------|
| Key lifecycle | Linear | Affine + relevant |
| Capability tokens | Linear | Affine |
| Session protocols | Session types | Linear channels |
| Audit enforcement | Relevant | Linear |
| Memory safety | Affine + borrowing | Linear |
| Data race prevention | Affine + borrowing | Linear |

### 9.2 Architectural Requirements Mapping

| TERAS Requirement | Best Approach | Runner-Up |
|-------------------|--------------|-----------|
| Zero dependencies | All approaches | - |
| Formal verification | ATS model | Linear + refinement |
| Compile-time security | All approaches | - |
| Decidable checking | Affine/Linear | Dependent (restricted) |
| Rust extraction | Affine model | - |

### 9.3 Product-Specific Requirements

**MENARA (Mobile):**
- Session tokens: Affine
- Secure enclave: Linear
- Network: Session types

**GAPURA (WAF):**
- Connections: Affine + Drop
- Requests: Linear (must respond)
- Rules: Immutable (!)

**ZIRAH (EDR):**
- Sensors: Capability
- Alerts: Relevant
- Memory: Affine + borrowing

**BENTENG (eKYC):**
- Documents: Linear
- Biometrics: Linear
- Verification: Session types

**SANDI (Signatures):**
- Private keys: Linear
- Certificates: Affine
- Signing: Session types

---

## 10. Comparative Decision Matrix

### 10.1 Weighted Scoring

| Criterion (Weight) | Linear | Affine | Relevant | Rust Model | ATS Model |
|--------------------|--------|--------|----------|------------|-----------|
| Security (25%) | 9 | 7 | 6 | 8 | 9 |
| Resource Safety (20%) | 10 | 8 | 6 | 9 | 10 |
| Expressiveness (15%) | 7 | 8 | 7 | 8 | 10 |
| Decidability (15%) | 10 | 10 | 10 | 9 | 7 |
| Ergonomics (10%) | 4 | 8 | 6 | 8 | 3 |
| Performance (10%) | 10 | 10 | 10 | 10 | 10 |
| Tooling (5%) | 3 | 8 | 2 | 9 | 2 |
| **Weighted Total** | **8.0** | **8.1** | **6.7** | **8.5** | **7.9** |

### 10.2 Security-Specific Scoring

| Security Feature | Linear | Affine | Relevant | Rust | ATS |
|-----------------|--------|--------|----------|------|-----|
| Key non-duplication | 10 | 8 | 3 | 8 | 10 |
| Key destruction | 10 | 5 | 8 | 6 | 10 |
| Capability tracking | 10 | 7 | 5 | 8 | 10 |
| Protocol enforcement | 9 | 6 | 6 | 7 | 9 |
| Audit guarantee | 5 | 3 | 10 | 4 | 8 |
| **Security Total** | **8.8** | **5.8** | **6.4** | **6.6** | **9.4** |

### 10.3 Practicality Scoring

| Practicality Factor | Linear | Affine | Relevant | Rust | ATS |
|--------------------|--------|--------|----------|------|-----|
| Error messages | 5 | 8 | 5 | 9 | 3 |
| IDE support | 3 | 8 | 2 | 9 | 2 |
| Community | 3 | 9 | 2 | 10 | 2 |
| Libraries | 2 | 8 | 1 | 10 | 2 |
| Documentation | 4 | 8 | 3 | 9 | 4 |
| **Practicality Total** | **3.4** | **8.2** | **2.6** | **9.4** | **2.6** |

---

## 11. Recommendations

### 11.1 Primary Recommendation: Hybrid System

**ADOPT:** Graded linear type system with Rust-style borrowing

**Rationale:**
- Combines linear precision for security-critical resources
- Affine default for practical programming
- Relevant for audit enforcement
- Borrowing for ergonomic temporary access

### 11.2 Type Modality Structure

```
Modalities:
- Linear (1): Exact once use (keys, capabilities)
- Affine (≤1): At most once (default for resources)
- Relevant (≥1): At least once (audit entries)
- Unrestricted (ω): Freely copyable (immutable data)

Type Grammar:
τ ::= T                     -- base type
    | τ ⊸ τ                 -- linear function
    | τ → τ                 -- unrestricted function  
    | τ ⊗ τ                 -- linear pair
    | τ & τ                 -- with (choice)
    | !τ                    -- unrestricted
    | &τ                    -- shared borrow
    | &mut τ                -- mutable borrow
    | Linear τ              -- explicitly linear
    | Relevant τ            -- must-use
```

### 11.3 Security-Critical Defaults

| Resource Type | Default Modality | Rationale |
|--------------|------------------|-----------|
| Private keys | Linear | Must destroy explicitly |
| Session tokens | Affine | Can discard on logout |
| Capabilities | Linear | Cannot duplicate |
| Audit entries | Relevant | Must log |
| Connections | Affine | Drop cleans up |
| Immutable config | Unrestricted | Freely share |

### 11.4 Borrowing Approach

**ADOPT:** Rust-style region-based borrowing with modifications:

1. **Shared borrows (&T):** Read-only, multiple allowed
2. **Unique borrows (&mut T):** Write, exclusive
3. **Linear borrows:** For security-critical temporary access

**Modifications from Rust:**
- Explicit linearity annotations where needed
- Integration with refinement types for permissions
- Session-typed channels for protocols

### 11.5 Implementation Priority

| Phase | Feature | Priority |
|-------|---------|----------|
| 1 | Affine types + Drop | Critical |
| 2 | Borrowing (shared/unique) | Critical |
| 3 | Linear annotation | High |
| 4 | Relevant annotation | High |
| 5 | Lifetime inference | Medium |
| 6 | Session types | Medium |

### 11.6 Integration with A-03 (Refinement Types)

```
// Combined linear + refinement
type SecureKey = Linear {k: Key | level(k) ≥ Secret}

// Borrowing with refinement
fn encrypt(key: &SecureKey, data: &[u8]{len(data) < MAX}) -> Ciphertext
```

### 11.7 Risk Mitigation

| Risk | Mitigation |
|------|------------|
| Annotation burden | Good defaults, inference |
| Learning curve | Excellent error messages |
| Lifetime complexity | Conservative inference, explicit when needed |
| Integration complexity | Phased implementation |

---

## Document Metadata

**Research Track:** A (Theoretical Foundations)  
**Session:** A-04  
**Document Type:** Comparative Analysis  
**Preceding Document:** RESEARCH_A04_LINEAR_TYPES_SURVEY.md  
**Following Document:** RESEARCH_A04_LINEAR_TYPES_DECISION.md

**Decision:** HYBRID graded linear system with Rust-style borrowing recommended.

---

*This comparison establishes the foundation for TERAS-LANG's resource management layer, recommending a pragmatic hybrid approach that balances security guarantees with developer ergonomics.*
