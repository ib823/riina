# RESEARCH_A06_UNIQUENESS_TYPES_DECISION

## Session A-06: Uniqueness Types Architecture Decision

**Research Track**: Domain A - Type Theory Foundations
**Session**: A-06 of 20
**Date**: 2026-01-03
**Status**: ARCHITECTURE DECISION

---

## Decision Summary

**DECISION A-06**: ADOPT Clean's uniqueness semantics as theoretical foundation for TERAS-LANG's unique reference type, integrated with the graded linear type system decided in A-04.

**Rationale**: Uniqueness types provide reference-count invariants that complement the usage-count invariants of linear types, enabling both efficient in-place updates and strong security guarantees for exclusive resource access.

---

## 1. Context and Problem

### 1.1 Current State (from A-04)

Session A-04 decided to adopt a **graded linear/affine type system** with Rust-style ownership and borrowing. This provides:
- Usage tracking (how many times a value is used)
- Ownership semantics (single owner, move semantics)
- Borrowing (shared and mutable references)
- Lifetime tracking

### 1.2 Gap Identified

A-04's linear types track **usage** but don't directly express **aliasing guarantees**. TERAS-LANG needs:
- **Unique reference guarantee**: Know definitively that only one reference exists
- **Security token semantics**: One-time capabilities that cannot be shared
- **Efficient updates**: Safe in-place mutation for cryptographic state
- **Formal foundation**: Theory connecting uniqueness to verification

### 1.3 Decision Needed

How should TERAS-LANG express and enforce **uniqueness** (single reference) semantics, and how does this integrate with the A-04 linear type system?

---

## 2. Options Considered

### Option 1: No Explicit Uniqueness

**Description**: Rely solely on A-04's linear/affine types without uniqueness concept.

**Pros**:
- Simpler type system
- Fewer concepts for users
- Linear already provides single-use

**Cons**:
- Cannot express "exactly one reference" guarantee
- Less precise for security reasoning
- Missing optimization opportunities
- No foundation for verification proofs

**Evaluation**: Insufficient for TERAS security requirements.

### Option 2: Clean-Style Uniqueness Attribute

**Description**: Add `*T` uniqueness prefix to types, following Clean's approach.

**Pros**:
- Well-understood formal semantics
- Graph rewriting foundation
- Proven in production (Clean, Mercury)
- Uniqueness polymorphism

**Cons**:
- Additional type system complexity
- May conflict with linear type annotations
- Different notation from Rust ecosystem
- Separate from ownership/borrowing model

**Evaluation**: Strong foundation but integration concerns.

### Option 3: Unified via Graded Types

**Description**: Express uniqueness as a grading dimension alongside linearity.

```
T @ (usage, uniqueness)

Where:
  usage âˆˆ {0, 1, Ï‰}     -- from A-04
  uniqueness âˆˆ {shared, unique}
```

**Pros**:
- Single unified framework
- Natural extension of A-04 decision
- Follows current research (Marshall & Orchard 2024)
- Composable with other gradings

**Cons**:
- More complex grading algebra
- Novel approach (less proven)
- May over-engineer simple cases

**Evaluation**: Theoretically elegant, complexity concerns.

### Option 4: Rust-Style Implicit Uniqueness

**Description**: Unique ownership implied by type, borrowing controls sharing.

**Pros**:
- Familiar to Rust developers
- Proven at scale
- Integrates with A-04 ownership decision
- Ergonomic borrowing

**Cons**:
- Uniqueness not explicit in types
- Harder to express uniqueness polymorphism
- Less amenable to formal verification
- No type-level uniqueness reasoning

**Evaluation**: Practical but less expressive for TERAS needs.

### Option 5: Hybrid Clean+Rust (RECOMMENDED)

**Description**: Clean's uniqueness semantics as theoretical foundation, Rust's operational model for implementation, unified through graded types.

**Components**:
1. **Semantic foundation**: Clean's graph rewriting semantics
2. **Syntax**: `uniq T` for unique types
3. **Integration**: Uniqueness as grading dimension
4. **Borrowing**: Rust-style with uniqueness preservation
5. **Verification**: Cogent-inspired proof generation

**Pros**:
- Best of both worlds
- Strong formal foundation
- Practical implementation model
- Unified with A-04 decision
- Security-focused extensions

**Cons**:
- Complex integration work
- Novel combination (less precedent)
- Requires careful specification

**Evaluation**: Best fit for TERAS requirements.

---

## 3. Decision

### 3.1 Selected Option

**Option 5: Hybrid Clean+Rust Approach**

### 3.2 Architectural Decisions

**A-06-D1**: Uniqueness as Semantic Property
- Uniqueness represents the reference-count invariant: at most one reference exists
- Complementary to linearity (usage-count invariant)
- Foundation: Clean's graph rewriting semantics (Barendsen & Smetsers 1996)

**A-06-D2**: Type-Level Uniqueness Annotation
- Syntax: `uniq T` for unique types
- Interaction with linearity: `lin uniq T` for linear unique values
- Default: Non-unique (shared possible)

**A-06-D3**: Graded Integration
```
Grading dimensions:
  Multiplicity m âˆˆ {0, 1, Ï‰, affine, relevant}  -- from A-04
  Uniqueness u âˆˆ {shared, unique}               -- from A-06

Type form: T @ (m, u)
Shorthand:
  lin T     â‰¡ T @ (1, shared)
  uniq T    â‰¡ T @ (Ï‰, unique)  
  lin uniq T â‰¡ T @ (1, unique)
```

**A-06-D4**: Uniqueness and Borrowing
- Unique values can be borrowed: `&uniq T` (immutable), `&mut uniq T` (mutable)
- Borrowing preserves uniqueness: no aliasing during borrow
- After borrow ends, uniqueness restored
- Clean's spread operation implemented via borrowing

**A-06-D5**: Uniqueness Polymorphism
```teras
// Polymorphic in uniqueness
fn identity<u: Uniqueness>(x: T @ u) -> T @ u {
    x
}

// Constrained
fn mutate<T>(x: uniq T) -> uniq T
where T: Mutable
{
    // Can mutate in-place
}
```

**A-06-D6**: Coercion Rules
```
Coercion ordering: unique < shared

unique â†’ shared  (OK: can forget uniqueness)
shared â†’ unique  (ERROR: cannot prove uniqueness)
```

**A-06-D7**: Security Applications
- One-time tokens: `lin uniq Token`
- Exclusive capabilities: `uniq Cap<P>`
- Secret keys: `lin uniq SecretKey`
- Session endpoints: `uniq Chan<Protocol>`

---

## 4. Type System Specification

### 4.1 Uniqueness Kinds

```
UniqueKind ::= shared | unique | U  (uniqueness variable)

Type ::= 
    | BaseType
    | Type @ (Multiplicity, UniqueKind)
    | uniq Type          -- sugar for T @ (Ï‰, unique)
    | lin Type           -- sugar for T @ (1, shared) 
    | lin uniq Type      -- sugar for T @ (1, unique)
    | &Type              -- shared borrow
    | &mut Type          -- unique borrow
    | forall U. Type     -- uniqueness polymorphism
```

### 4.2 Typing Rules

**Uniqueness Introduction**:
```
Î“ âŠ¢ e : T
T has no aliases in Î“
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : uniq T
```

**Uniqueness Elimination** (Coercion):
```
Î“ âŠ¢ e : uniq T
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : T
```

**Unique Borrow**:
```
Î“ âŠ¢ e : uniq T
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ &mut e : &mut uniq T
```

**Shared Borrow of Unique**:
```
Î“ âŠ¢ e : uniq T
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ &e : &uniq T
```

**Uniqueness Polymorphism**:
```
Î“ âŠ¢ e : T @ (m, U)
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : forall U. T @ (m, U)
```

### 4.3 Subtyping

```
uniq T <: T            -- unique is subtype of shared
&uniq T <: &T          -- unique ref is subtype of shared ref
&mut uniq T <: &mut T  -- unique mut ref is subtype of mut ref
```

### 4.4 Interaction with Multiplicity

| Multiplicity | Uniqueness | Meaning |
|--------------|------------|---------|
| 0 | any | Erased, not used |
| 1 | shared | Linear, possibly shared |
| 1 | unique | Linear, definitely unique |
| Ï‰ | shared | Unrestricted, possibly shared |
| Ï‰ | unique | Unrestricted, definitely unique |
| affine | unique | At most once, unique |

---

## 5. Implementation Strategy

### 5.1 Compiler Phases

**Phase 1: Parsing**
- Recognize `uniq` keyword
- Parse uniqueness annotations

**Phase 2: Uniqueness Inference**
- Infer uniqueness attributes where not specified
- Similar to Clean's uniqueness inference algorithm

**Phase 3: Uniqueness Checking**
- Verify uniqueness constraints
- Check no aliasing of unique values
- Integrate with borrow checker

**Phase 4: Optimization**
- Enable in-place updates for unique values
- Eliminate copies when uniqueness proven

### 5.2 Borrow Checker Integration

From A-04, borrow checker handles ownership and lifetimes. Extend for uniqueness:

```
Extended borrow state:
  Location â†’ (Type, Ownership, Uniqueness, Borrows)

Uniqueness preservation:
  When unique value borrowed:
    - Shared borrow: uniqueness preserved (read-only)
    - Mutable borrow: uniqueness preserved (exclusive)
    - Move: uniqueness transferred
```

### 5.3 Error Messages

```
error[E0501]: cannot alias unique value
  --> src/main.teras:15:9
   |
14 |     let key: uniq Key = generate_key();
   |         --- unique value created here
15 |     let copy = key;  // moves
16 |     use(key);        // ERROR: already moved
   |         ^^^ value used after move
   |
   = note: unique values can only have one reference
```

---

## 6. Security Integration

### 6.1 Unique Capabilities

```teras
// Capability that cannot be shared
type SecureCap<P: Permission> = lin uniq Cap<P>

// Create capability (requires proof of authority)
fn create_cap<P>(auth: AuthToken) -> SecureCap<P>
where Auth: Authorizes<P>
{
    // Only one reference to this capability exists
    SecureCap::new(auth)
}

// Use capability (consumes it)
fn exercise<P>(cap: SecureCap<P>) -> P::Result {
    // cap is consumed - cannot be reused or shared
    cap.exercise()
}
```

### 6.2 One-Time Tokens

```teras
// Token for single use
type OTP = lin uniq Token

fn validate(otp: OTP) -> Result<(), Error> {
    // OTP is linear and unique:
    // - Must be used (linear)
    // - Cannot be copied (unique)
    otp.check()
}

// Replay attack impossible - token consumed
```

### 6.3 Cryptographic Keys

```teras
// Signing key with strong protection
type SigningKey = lin uniq Key<Ed25519>

fn sign(key: &uniq SigningKey, msg: &[u8]) -> Signature {
    // Borrow key uniquely - no other reference exists
    // Cannot leak key through aliasing
    key.inner_sign(msg)
}

// Key destruction is guaranteed (linear)
fn destroy(key: SigningKey) {
    key.zeroize();  // Must be called
}
```

### 6.4 Session Channels

```teras
// Unique channel endpoint
type Chan<P: Protocol> = uniq Channel<P>

fn send<P, T>(chan: Chan<P::Send<T>>, msg: T) -> Chan<P::Next>
where P: Protocol
{
    // Uniqueness ensures no races
    // Linear ensures protocol followed
    chan.send_internal(msg)
}
```

---

## 7. Verification Benefits

### 7.1 Proof Obligations

Uniqueness enables simpler verification:

| Property | Without Uniqueness | With Uniqueness |
|----------|-------------------|-----------------|
| No aliasing | Prove for all refs | Guaranteed by type |
| Safe update | Prove exclusive access | Guaranteed by type |
| No races | Complex analysis | Type-level guarantee |

### 7.2 Cogent-Style Refinement

Following Cogent's approach, TERAS-LANG can generate:

1. **Functional semantics**: Pure, equational reasoning
2. **Imperative semantics**: Efficient execution
3. **Refinement proof**: Functional â‰¤ Imperative

Uniqueness types make this refinement simpler to prove.

### 7.3 Security Properties

Uniqueness enables proving:
- **Confidentiality**: Unique secrets cannot leak through aliasing
- **Integrity**: Unique state cannot be modified by aliases
- **Availability**: Unique resources properly managed

---

## 8. Migration from A-04

### 8.1 Extending Graded Types

A-04 established multiplicities. A-06 adds uniqueness dimension:

```
Before (A-04):
  lin T     -- linear
  affine T  -- affine
  T         -- unrestricted

After (A-06):
  lin T         -- linear, shared (default)
  lin uniq T    -- linear, unique
  affine uniq T -- affine, unique
  uniq T        -- unrestricted, unique
  T             -- unrestricted, shared
```

### 8.2 Backward Compatibility

Existing A-04 types have implicit `shared` uniqueness:
```
lin T â‰¡ lin shared T
T â‰¡ shared T
```

### 8.3 Inference Rules

When uniqueness not annotated:
1. If type is newly constructed, infer `unique`
2. If type comes from shared context, infer `shared`
3. If type is parameter, infer `shared` (conservative)
4. Allow explicit `uniq` to override

---

## 9. TERAS Alignment

### 9.1 Eight Laws Compliance

| Law | Uniqueness Support |
|-----|-------------------|
| Self-sufficiency | Clean semantics (no external theory) |
| Formal verification | Stronger proofs via uniqueness |
| Cryptographic focus | Unique keys, secure state |
| Performance | In-place updates |
| Memory safety | No alias-based bugs |
| Zero third-party | First-class feature |
| Malaysian identity | `uniq` keyword (unique in Malay similar) |
| Compile-time | All uniqueness checks static |

### 9.2 Product Integration

| Product | Uniqueness Use |
|---------|---------------|
| MENARA | Unique device tokens |
| GAPURA | Unique session handles |
| ZIRAH | Unique threat indicators |
| BENTENG | Unique identity credentials |
| SANDI | Unique signing keys |

---

## 10. Implementation Roadmap

### Phase 1: Core Uniqueness (Weeks 1-4)
- [ ] Uniqueness kind in type system
- [ ] Parser for `uniq` keyword
- [ ] Basic uniqueness checking
- [ ] Integration with A-04 multiplicity

### Phase 2: Uniqueness Inference (Weeks 5-8)
- [ ] Inference algorithm (Clean-based)
- [ ] Principal uniqueness types
- [ ] Error messages

### Phase 3: Borrow Checker Integration (Weeks 9-12)
- [ ] Extend borrow state for uniqueness
- [ ] Uniqueness-preserving borrows
- [ ] Lifetime interaction

### Phase 4: Security Features (Weeks 13-16)
- [ ] Unique capability types
- [ ] One-time token patterns
- [ ] Cryptographic key types

### Phase 5: Optimization (Weeks 17-20)
- [ ] In-place update optimization
- [ ] Copy elimination
- [ ] Performance validation

---

## 11. Decision Record

### 11.1 Decision Statement

**ADOPT** Clean's uniqueness type semantics as theoretical foundation for TERAS-LANG's `uniq` type annotation, integrated with the graded linear type system from A-04 decision.

### 11.2 Key Decisions

| ID | Decision | Rationale |
|----|----------|-----------|
| A-06-D1 | Uniqueness as reference-count invariant | Complements linear usage-count |
| A-06-D2 | `uniq T` syntax | Clear, composable |
| A-06-D3 | Graded integration | Unified framework |
| A-06-D4 | Rust-style borrowing | Ergonomic, proven |
| A-06-D5 | Uniqueness polymorphism | Generic programming |
| A-06-D6 | unique â†’ shared coercion | Safe subsumption |
| A-06-D7 | Security-focused types | TERAS requirements |

### 11.3 Alignment Score

| Criterion | Score | Notes |
|-----------|-------|-------|
| TERAS principles | 9/10 | Strong verification, security |
| Implementation feasibility | 8/10 | Complex but understood |
| Theoretical foundation | 9/10 | Clean semantics well-proven |
| Security applications | 10/10 | Ideal for capabilities, keys |
| Developer ergonomics | 7/10 | Additional concept to learn |

**Overall Score**: 8.6/10

### 11.4 Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Complexity overload | Medium | High | Good defaults, inference |
| Integration issues | Medium | Medium | Careful specification |
| Performance overhead | Low | Medium | Static checking only |
| User confusion | Medium | Medium | Clear documentation |

---

## 12. References

1. Barendsen & Smetsers (1996). "Uniqueness Typing for Functional Languages with Graph Rewriting Semantics"
2. Harrington (2006). "Uniqueness Logic"
3. O'Connor et al. (2021). "Cogent: Uniqueness Types and Certifying Compilation"
4. Marshall & Orchard (2024). "Functional Ownership through Fractional Uniqueness"
5. Session A-04 Decision: Graded Linear Types

---

## Document Metadata

```yaml
document_id: RESEARCH_A06_UNIQUENESS_TYPES_DECISION
version: 1.0.0
date: 2026-01-03
session: A-06
domain: Type Theory Foundations
decision: ADOPT hybrid Clean+Rust uniqueness
alignment_score: 8.6/10
status: COMPLETE
```
