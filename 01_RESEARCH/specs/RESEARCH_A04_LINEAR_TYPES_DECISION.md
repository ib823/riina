# RESEARCH_A04_LINEAR_TYPES_DECISION.md

## TERAS Research Track: Session A-04
## Linear Types Integration Decision for TERAS-LANG

**Document Version:** 1.0.0
**Created:** 2026-01-03
**Session:** A-04 of 47
**Track:** Foundational Type Theory
**Status:** APPROVED

---

## 1. Decision Summary

### 1.1 Primary Decision

**ADOPT** a hybrid graded linear/affine type system with Rust-style ownership and borrowing semantics as the foundational resource management layer for TERAS-LANG.

### 1.2 Decision Statement

TERAS-LANG shall implement:

1. **Affine-by-default** semantics where all values may be used at most once unless explicitly marked otherwise
2. **Rust-style ownership and borrowing** with shared (&) and unique (&mut) references
3. **Graded multiplicity annotations** (0, 1, Ï‰) for fine-grained resource control
4. **Explicit linearity markers** for strict exactly-once semantics when required
5. **Integration hooks** for session types (A-05/A-06) and refinement types (A-03)

### 1.3 Rationale

This decision balances theoretical rigor with practical usability:

| Criterion | Weight | Score | Justification |
|-----------|--------|-------|---------------|
| Security guarantees | 30% | 9.5/10 | Compile-time memory safety, capability consumption |
| Zero runtime overhead | 25% | 10/10 | All checks at compile time |
| Developer ergonomics | 20% | 8/10 | Proven in Rust, good error messages possible |
| Integration with A-01/A-02/A-03 | 15% | 8.5/10 | Established patterns (ATS, QTT, F*) |
| Formal verification potential | 10% | 9/10 | RustBelt demonstrates semantic soundness |

**Weighted Score: 9.1/10** - Exceeds threshold for adoption.

---

## 2. Architecture Decision Record

### ADR-A04-001: Graded Linear Type System

**Context:** TERAS-LANG requires compile-time resource management guarantees for security-critical code including cryptographic keys, capabilities, session state, and memory.

**Decision:** Implement a graded linear type system with multiplicities:

```
Multiplicities: m ::= 0        -- erased (type-level only)
                    | 1        -- linear (exactly once)
                    | Ï‰        -- unrestricted (any usage)
                    | â‰¤1       -- affine (at most once) [default]
                    | â‰¥1       -- relevant (at least once)
```

**Consequences:**
- Positive: Fine-grained control over resource usage
- Positive: Subsumes linear, affine, relevant as special cases
- Negative: Slightly more complex mental model than pure affine
- Mitigated: Default to affine for ergonomics

### ADR-A04-002: Ownership and Borrowing

**Context:** Resource management must be practical for systems programming without garbage collection.

**Decision:** Adopt Rust's ownership model with modifications:

```
Ownership Rules:
1. Each value has exactly one owner
2. Ownership transfers via move semantics
3. Values dropped when owner goes out of scope
4. Borrowing temporarily suspends ownership
```

**Borrowing:**
```
References:
  &T     -- shared (immutable) reference, multiple allowed
  &mut T -- unique (mutable) reference, exclusive access
  
Lifetimes:
  'a     -- named lifetime parameter
  'static -- 'static lifetime (global)
```

**Consequences:**
- Positive: Proven effective in Rust ecosystem
- Positive: Zero runtime overhead
- Positive: Prevents data races statically
- Negative: Lifetime annotations can be verbose
- Mitigated: Aggressive lifetime elision rules

### ADR-A04-003: Linear Type Annotations

**Context:** Some resources require strict exactly-once semantics beyond affine.

**Decision:** Provide explicit linearity markers:

```teras
// Affine (default) - at most once
type AffineKey = Key

// Linear - exactly once (must be consumed)
type LinearKey = lin Key

// Unrestricted - any number of uses
type SharedConfig = unr Config
```

**Consequences:**
- Positive: Expressive power for different resource semantics
- Positive: Explicit intent documentation
- Negative: Additional syntax complexity
- Mitigated: Affine default covers most cases

### ADR-A04-004: Integration with Refinement Types

**Context:** Session A-03 established refinement types for security predicates.

**Decision:** Enable combined refinement and linearity annotations:

```teras
// Refined linear type
type SecretKey = lin {k: Key | security_level(k) â‰¥ Secret}

// Refined affine capability
type FileHandle = {h: Handle | valid(h) âˆ§ mode(h) = ReadOnly}

// Borrowing with refinements
fn read(file: &{h: Handle | valid(h)}) -> Result<Data, Error>
```

**Integration Points:**
- Refinement predicates preserved through borrows
- Linearity annotations orthogonal to refinements
- SMT solver handles refinement subtyping (A-03)
- Type checker handles linearity (A-04)

**Consequences:**
- Positive: Unified type language with orthogonal features
- Positive: Maximum expressiveness
- Negative: Implementation complexity
- Mitigated: Clear separation of concerns

---

## 3. Type System Specification

### 3.1 Multiplicity System

**Syntax:**
```
Multiplicities:
  m, n ::= 0           -- zero (erased)
         | 1           -- one (linear)
         | Ï‰           -- many (unrestricted)
         | m + n       -- addition
         | m Ã— n       -- multiplication
         | â‰¤1          -- affine sugar
         | â‰¥1          -- relevant sugar

Types with Multiplicity:
  Ï„ ::= ...
      | m Ï„            -- type with multiplicity m
```

**Multiplicity Arithmetic:**
```
0 + m = m
1 + 1 = Ï‰       (two uses = unlimited)
Ï‰ + m = Ï‰
0 Ã— m = 0
1 Ã— m = m
Ï‰ Ã— m = Ï‰ (if m â‰  0), 0 (if m = 0)
```

**Subtyping:**
```
0 â‰¤ 1 â‰¤ Ï‰      (0 most restrictive, Ï‰ least)
```

### 3.2 Typing Judgement

**Form:** Î“ âŠ¢ e : Ï„ â«¤ Î“'

- Î“: Input typing context with multiplicities
- e: Expression
- Ï„: Type (may include multiplicity)
- Î“': Output context (tracking consumed resources)

**Context Operations:**
```
Context Split: Î“ = Î“â‚ + Î“â‚‚
  (x : mâ‚Ï„) + (x : mâ‚‚Ï„) = (x : (mâ‚+mâ‚‚)Ï„)

Context Scale: m Ã— Î“
  m Ã— (x : nÏ„) = (x : (mÃ—n)Ï„)
```

### 3.3 Core Typing Rules

**Variables:**
```
              x : mÏ„ âˆˆ Î“
Var:          â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
              Î“ âŠ¢ x : Ï„ â«¤ Î“[x â†¦ 0Ï„]
```

**Abstraction:**
```
              Î“, x : mÏ„â‚ âŠ¢ e : Ï„â‚‚ â«¤ Î“', x : 0Ï„â‚
Abs:          â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
              Î“ âŠ¢ Î»x.e : (m Ï„â‚) â†’ Ï„â‚‚ â«¤ Î“'
```

**Application:**
```
              Î“â‚ âŠ¢ eâ‚ : (m Ï„â‚) â†’ Ï„â‚‚ â«¤ Î“â‚'
              Î“â‚‚ âŠ¢ eâ‚‚ : Ï„â‚ â«¤ Î“â‚‚'
App:          â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
              Î“â‚ + Î“â‚‚ âŠ¢ eâ‚ eâ‚‚ : Ï„â‚‚ â«¤ m Ã— Î“â‚‚' + Î“â‚'
```

**Borrow (Shared):**
```
              Î“ âŠ¢ e : Ï„ â«¤ Î“'
              x fresh
Borrow:       â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
              Î“ âŠ¢ &e : &'a Ï„ â«¤ Î“', x : borrowed(Ï„, 'a)
```

**Borrow (Unique):**
```
              Î“ âŠ¢ e : Ï„ â«¤ Î“'
              x fresh, unique(e)
BorrowMut:    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
              Î“ âŠ¢ &mut e : &'a mut Ï„ â«¤ Î“', x : borrowed_mut(Ï„, 'a)
```

### 3.4 Ownership Transfer

**Move Semantics:**
```teras
fn transfer_ownership() {
    let key: LinearKey = create_key();  // key owned here
    let key2 = key;                      // ownership moved to key2
    // key is now invalid (moved)
    consume(key2);                       // key2 consumed
}
```

**Copy Types:**
```teras
// Types implementing Copy can be duplicated
impl Copy for u32 {}
impl Copy for bool {}
// Copy requires: Ï‰ Ã— Ï„ is valid
```

### 3.5 Lifetime Inference

**Elision Rules:**

1. Each input reference gets fresh lifetime
2. If exactly one input lifetime, output lifetime = input
3. If &self or &mut self present, output lifetime = self

**Examples:**
```teras
// Fully elided
fn first(x: &str) -> &str { ... }
// Elaborates to:
fn first<'a>(x: &'a str) -> &'a str { ... }

// Multiple inputs, explicit needed
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str { ... }
```

---

## 4. Security-Specific Linear Types

### 4.1 Cryptographic Keys

**Design:**
```teras
/// Private signing key - must be consumed or destroyed
pub type SigningKey = lin {
    key: [u8; 32] |
    valid_key(key) âˆ§ not_leaked(key)
}

/// Create a signing key (produces linear value)
pub fn generate_signing_key() -> SigningKey

/// Sign data (consumes key momentarily via borrow)
pub fn sign(key: &SigningKey, data: &[u8]) -> Signature

/// Secure destruction (consumes key)
pub fn destroy_key(key: SigningKey) -> ()
```

**Guarantee:** SigningKey cannot be:
- Duplicated (no Copy)
- Leaked (must be consumed)
- Used after destruction (moved)

### 4.2 Capabilities

**Design:**
```teras
/// Capability for resource access - consumed on use
pub type Capability<R> = lin {
    cap: CapToken<R> |
    valid(cap) âˆ§ authorized(cap)
}

/// Use capability (consumes it, may return new capability)
pub fn use_capability<R, T>(
    cap: Capability<R>,
    action: fn(&R) -> T
) -> (T, Option<Capability<R>>)

/// Revoke capability (consumes without returning)
pub fn revoke(cap: Capability<R>) -> ()
```

### 4.3 Session State

**Design:**
```teras
/// TLS session in handshake state
pub type TlsHandshake = lin Session<HandshakeState>

/// TLS session in established state
pub type TlsEstablished = lin Session<EstablishedState>

/// Complete handshake (state transition)
pub fn complete_handshake(
    session: TlsHandshake,
    params: HandshakeParams
) -> Result<TlsEstablished, TlsError>
```

**Guarantee:** Session state machine enforced at compile time.

### 4.4 One-Time Tokens

**Design:**
```teras
/// Authentication token - single use
pub type AuthToken = lin {
    token: TokenData |
    not_used(token) âˆ§ not_expired(token)
}

/// Validate token (consumes it)
pub fn validate_token(token: AuthToken) -> Result<UserId, AuthError>
```

**Guarantee:** Token cannot be replayed (linearity prevents reuse).

---

## 5. Implementation Architecture

### 5.1 Type Checker Extensions

**Module Structure:**
```
teras-lang/
â”œâ”€â”€ src/
â”‚   â””â”€â”€ typecheck/
â”‚       â”œâ”€â”€ context.rs       -- Typing context with multiplicities
â”‚       â”œâ”€â”€ linearity.rs     -- Linearity checking
â”‚       â”œâ”€â”€ ownership.rs     -- Ownership tracking
â”‚       â”œâ”€â”€ borrowck.rs      -- Borrow checker
â”‚       â”œâ”€â”€ lifetime.rs      -- Lifetime inference and checking
â”‚       â””â”€â”€ integration.rs   -- Integration with refinement types
```

### 5.2 Borrow Checker Algorithm

**Phase 1: Ownership Analysis**
```
1. Build ownership graph for each function
2. Identify move points
3. Verify single ownership invariant
```

**Phase 2: Borrow Analysis**
```
1. Identify borrow regions
2. Check exclusivity (no &mut with &)
3. Verify lifetime containment
```

**Phase 3: Liveness Analysis**
```
1. Compute live ranges for borrows
2. Non-lexical lifetime extension
3. Report violations
```

### 5.3 Error Messages

**Design Priority:** Excellent error messages are critical for adoption.

**Example Error:**
```
error[E0382]: use of moved value: `key`
  --> src/crypto.rs:15:13
   |
12 |     let key = generate_key();
   |         --- move occurs because `key` has type `SigningKey`, which is linear
13 |     let key2 = key;
   |                --- value moved here
14 |     
15 |     sign(&key, data);
   |          ^^^^ value used here after move
   |
help: consider borrowing instead of moving
   |
13 |     let key2 = &key;
   |                +
```

### 5.4 Integration Points

**With Refinement Types (A-03):**
```
                    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
                    â”‚ TERAS-LANG Type  â”‚
                    â”‚    Checker       â”‚
                    â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
                             â”‚
              â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
              â”‚              â”‚              â”‚
              â–¼              â–¼              â–¼
    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
    â”‚ Linearity    â”‚ â”‚ Refinement   â”‚ â”‚ Dependent    â”‚
    â”‚ Checker      â”‚ â”‚ Checker      â”‚ â”‚ Type Checker â”‚
    â”‚ (A-04)       â”‚ â”‚ (A-03)       â”‚ â”‚ (A-01/A-02)  â”‚
    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
                            â”‚
                            â–¼
                    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
                    â”‚ SMT Solver   â”‚
                    â”‚ (embedded)   â”‚
                    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

**With Session Types (planned A-05/A-06):**
- Session endpoints are linear
- Protocol state tracked via type
- Channel operations consume/produce endpoints

---

## 6. Migration and Compatibility

### 6.1 Default Behavior

**Conservative Defaults:**
- All user-defined types are affine by default
- Copy trait must be explicitly implemented
- Borrows require explicit lifetime when ambiguous

**Inference Maximized:**
- Lifetime elision for common patterns
- Multiplicity inference where unambiguous
- Automatic dereferencing for ergonomics

### 6.2 Escape Hatches

**Unsafe Blocks:**
```teras
unsafe {
    // Can violate linearity constraints
    // Must be audited
    let ptr = &key as *const Key;
    // ... low-level operations ...
}
```

**Safety Contract:**
- Unsafe code must maintain safety invariants at boundaries
- Linear values must not escape unsafe blocks inappropriately
- Auditing requirements for unsafe code

### 6.3 Interoperability

**FFI Considerations:**
```teras
extern "C" {
    // C function that takes ownership
    fn c_consume_key(key: *mut Key);
}

// Safe wrapper
pub fn consume_key(key: LinearKey) {
    unsafe {
        c_consume_key(&key as *const _ as *mut _);
        std::mem::forget(key);  // Prevent double-free
    }
}
```

---

## 7. Validation Strategy

### 7.1 Formal Verification

**Goals:**
- Prove type soundness (progress + preservation)
- Verify safety of unsafe abstractions
- Establish semantic foundations (RustBelt-style)

**Approach:**
- Coq/Agda mechanization of core calculus
- Iris-based semantic model for unsafe code
- Property-based testing for implementation

### 7.2 Testing Strategy

**Unit Tests:**
- Positive: Well-typed linear programs
- Negative: Ill-typed programs with clear violations
- Edge cases: Complex lifetime scenarios

**Integration Tests:**
- Combined refinement + linearity
- Session type protocols
- Cryptographic workflows

### 7.3 Benchmarks

**Performance Targets:**
- Zero runtime overhead from linearity checks
- Compile-time within 2x of equivalent Rust
- Memory usage comparable to Rust

---

## 8. Risk Assessment

### 8.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Lifetime inference too weak | Medium | High | Conservative fallback to explicit |
| Integration complexity with A-03 | Medium | Medium | Clear interface boundaries |
| Error messages unclear | Low | High | Dedicated UX effort |
| Performance regression | Low | Medium | Continuous benchmarking |

### 8.2 Adoption Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Learning curve too steep | Medium | Medium | Documentation, tutorials |
| Annotation burden | Low | Medium | Good defaults, inference |
| Ecosystem incompatibility | Medium | Low | Clear FFI story |

---

## 9. Implementation Roadmap

### Phase 1: Core Ownership (Weeks 1-4)
- [ ] Ownership tracking in type checker
- [ ] Move semantics implementation
- [ ] Drop trait and deterministic destruction
- [ ] Basic error messages

### Phase 2: Borrowing (Weeks 5-8)
- [ ] Shared reference (&T) support
- [ ] Unique reference (&mut T) support
- [ ] Exclusivity checking
- [ ] Lifetime parameter syntax

### Phase 3: Lifetime Inference (Weeks 9-12)
- [ ] Elision rules implementation
- [ ] Non-lexical lifetimes
- [ ] Lifetime bound inference
- [ ] Advanced error messages

### Phase 4: Graded Linearity (Weeks 13-16)
- [ ] Multiplicity annotations (0, 1, Ï‰)
- [ ] Linear (lin) marker
- [ ] Relevant (â‰¥1) support
- [ ] Integration with refinement types

### Phase 5: Hardening (Weeks 17-20)
- [ ] Comprehensive test suite
- [ ] Performance optimization
- [ ] Documentation
- [ ] Security audit of implementation

---

## 10. Decision Approval

### 10.1 Alignment with TERAS Principles

| TERAS Law | Alignment | Notes |
|-----------|-----------|-------|
| Law 1: Self-Sufficiency | âœ“ | No GC or runtime dependencies |
| Law 2: Formal Verification | âœ“ | Type system provides proofs |
| Law 3: Zero Third-Party | âœ“ | Custom implementation |
| Law 4: Malaysian Identity | â—‹ | Neutral (type system) |
| Law 5: Post-Quantum Ready | â—‹ | Orthogonal concern |
| Law 6: Memory Safety | âœ“ | Core guarantee |
| Law 7: Auditability | âœ“ | Clear ownership semantics |
| Law 8: Performance | âœ“ | Zero runtime overhead |

**Overall Alignment: 9.2/10**

### 10.2 Sign-Off

**Decision:** APPROVED for implementation in TERAS-LANG

**Rationale:**
- Proven approach (Rust) with excellent safety record
- Zero runtime overhead meets performance requirements
- Strong formal foundations (RustBelt) enable verification
- Natural integration with refinements and session types

**Next Steps:**
1. Proceed to A-05 (Effect Systems) for complementary analysis
2. Begin Phase 1 implementation per roadmap
3. Develop formal specification for mechanization

---

## 11. References

1. Girard, J.-Y. (1987). "Linear Logic." TCS.
2. Jung, R. et al. (2017). "RustBelt: Securing the Foundations of Rust." POPL.
3. Weiss, A. et al. (2019). "Oxide: The Essence of Rust."
4. Atkey, R. (2018). "Syntax and Semantics of Quantitative Type Theory." LICS.
5. Bernardy, J.-P. et al. (2017). "Linear Haskell." POPL.

---

## Document Metadata

**Research Track:** A (Theoretical Foundations)
**Session:** A-04
**Document Type:** Architecture Decision
**Status:** APPROVED
**Preceding Documents:**
- RESEARCH_A04_LINEAR_TYPES_SURVEY.md
- RESEARCH_A04_LINEAR_TYPES_COMPARISON.md
**Following Session:** A-05 (Effect Systems and Monads)

**SHA-256 Lineage:**
- Parent: RESEARCH_A03_REFINEMENT_TYPES_DECISION.md
- This Document: [Computed on finalization]

---

*This decision establishes the resource management foundation for TERAS-LANG, enabling compile-time guarantees for memory safety, capability management, and secure resource handling.*
