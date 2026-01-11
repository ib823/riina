# RESEARCH_A07_SESSION_TYPES_DECISION

## Session A-07: Session Types Architecture Decision

**Research Track**: Domain A - Type Theory Foundations
**Session**: A-07 of 20
**Date**: 2026-01-03
**Status**: ARCHITECTURE DECISION

---

## Decision Summary

**DECISION A-07**: ADOPT binary session types with refinement predicates as core protocol specification mechanism, with multiparty session types as phased extension, integrated with TERAS-LANG's linear type system for safe channel endpoint ownership.

**Rationale**: Session types provide the ideal foundation for verified security protocol implementations, ensuring protocol compliance at compile time. The linear logic connection aligns with A-04/A-06 decisions on linear and unique types.

---

## 1. Context and Problem

### 1.1 TERAS Requirements

TERAS security products require verified communication protocols:
- **MENARA**: Device-server authentication
- **GAPURA**: HTTP request/response handling
- **ZIRAH**: Threat intelligence feeds
- **BENTENG**: Identity verification flows
- **SANDI**: Signature request protocols

### 1.2 Current State

From A-04 and A-06 decisions:
- Linear types for resource tracking
- Unique types for single-reference guarantees
- Borrowing for temporary access

**Gap**: No mechanism for specifying and verifying communication protocols.

### 1.3 Decision Needed

How should TERAS-LANG specify, check, and enforce communication protocols?

---

## 2. Options Considered

### Option 1: No Native Session Types

**Description**: Use regular types for messages, no protocol enforcement.

**Evaluation**: Insufficient for security requirements. Protocol violations undetected. **Rejected**.

### Option 2: Binary Session Types Only

**Description**: Two-party session types with duality.

**Pros**:
- Simpler implementation
- Well-understood theory
- Good for client-server

**Cons**:
- Limited to two parties
- Complex protocols need composition

**Evaluation**: Good starting point but limiting. **Partial**.

### Option 3: Full Multiparty Session Types

**Description**: Global types with projection to local types.

**Pros**:
- Full protocol expressiveness
- Native multi-party
- Industry standard (Scribble)

**Cons**:
- Complex implementation
- Projection algorithm needed
- Harder to learn

**Evaluation**: Powerful but complex. **Consider for extension**.

### Option 4: Dependent Session Types

**Description**: Value-dependent protocols Ã  la Toninho-Caires-Pfenning.

**Pros**:
- Maximum expressiveness
- Proof-carrying communication
- Value-dependent branching

**Cons**:
- Undecidable type checking
- Complex implementation
- Requires dependent types base

**Evaluation**: Too complex for initial implementation. **Future consideration**.

### Option 5: Refinement Session Types (RECOMMENDED)

**Description**: Binary/multiparty sessions with refinement predicates, SMT-checked.

**Pros**:
- Practical expressiveness
- Decidable (SMT) checking
- Aligns with A-03 (refinement types)
- Incremental adoption

**Cons**:
- SMT solver dependency
- Not as expressive as full dependent

**Evaluation**: Best balance for TERAS. **Recommended**.

---

## 3. Decision

### 3.1 Selected Approach

**Option 5: Refinement Session Types** with phased implementation:
- Phase 1: Binary session types with linear endpoints
- Phase 2: Refinement predicates on messages
- Phase 3: Multiparty session types extension
- Phase 4: Dependent features (long-term)

### 3.2 Architectural Decisions

**A-07-D1**: Session Types as First-Class Types
- Session types are types describing channel behavior
- Syntax: `session S` for session type declarations
- Integration with type system

**A-07-D2**: Linear Channel Endpoints
- Each session endpoint is linear (from A-04)
- Ensures exactly-once usage of protocol steps
- Prevents endpoint aliasing

```teras
// Channel type with session
type Chan<S> = lin Channel<S>

// Endpoint ownership
fn use_channel(c: lin Chan<S>) -> (Result, lin Chan<S'>)
```

**A-07-D3**: Binary Session Type Syntax
```teras
session S ::=
    | !T.S           // Send T, continue as S
    | ?T.S           // Receive T, continue as S
    | +{lâ‚:Sâ‚, ...}  // Internal choice (select)
    | &{lâ‚:Sâ‚, ...}  // External choice (offer)
    | rec X.S        // Recursive session
    | X              // Session variable
    | end            // Termination
```

**A-07-D4**: Duality Relationship
```teras
// Dual types are related
dual(!T.S) = ?T.dual(S)
dual(?T.S) = !T.dual(S)
dual(+{l:S}) = &{l:dual(S)}
dual(&{l:S}) = +{l:dual(S)}
dual(end) = end
dual(rec X.S) = rec X.dual(S)
```

**A-07-D5**: Refinement Predicates
```teras
// Message with refinement
session AuthSession = 
    ?{pin: u32 | pin.len == 4}.        // 4-digit PIN
    !{response: Response}.
    &{ valid: !{token: Token | valid(token)}.end,
       invalid: end }
```

**A-07-D6**: Protocol Operations
```teras
// Primitives
fn send<T, S>(c: lin Chan<!T.S>, v: T) -> lin Chan<S>
fn recv<T, S>(c: lin Chan<?T.S>) -> (T, lin Chan<S>)
fn select<S>(c: lin Chan<+{l:S, ...}>, label: l) -> lin Chan<S>
fn offer<...>(c: lin Chan<&{...}>) -> Branches<...>
fn close(c: lin Chan<end>) -> ()
```

**A-07-D7**: Integration with Uniqueness
```teras
// Session endpoint is unique
type Endpoint<S> = lin uniq Chan<S>

// Borrowing for inspection
fn peek<S>(c: &uniq Chan<S>) -> SessionInfo
```

---

## 4. Session Type System Specification

### 4.1 Typing Judgment

```
Î“; Î” âŠ¢ e : T; Î”'

Where:
  Î“ = Standard context (unrestricted)
  Î” = Session context (linear)
  T = Result type
  Î”' = Remaining session context
```

### 4.2 Key Typing Rules

**Send**:
```
Î“ âŠ¢ v : T    Î“; Î”, c:S âŠ¢ e : U; Î”'
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“; Î”, c:!T.S âŠ¢ send(c, v); e : U; Î”'
```

**Receive**:
```
Î“, x:T; Î”, c:S âŠ¢ e : U; Î”'
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“; Î”, c:?T.S âŠ¢ x â† recv(c); e : U; Î”'
```

**Close**:
```
Î“; Î” âŠ¢ e : T; Î”'
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“; Î”, c:end âŠ¢ close(c); e : T; Î”'
```

**Select**:
```
Î“; Î”, c:Sâ±¼ âŠ¢ e : T; Î”'
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“; Î”, c:+{láµ¢:Sáµ¢} âŠ¢ select(c, lâ±¼); e : T; Î”'
```

**Offer**:
```
âˆ€i. Î“; Î”, c:Sáµ¢ âŠ¢ eáµ¢ : T; Î”'
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“; Î”, c:&{láµ¢:Sáµ¢} âŠ¢ offer(c){láµ¢ â†’ eáµ¢} : T; Î”'
```

### 4.3 Refinement Integration

```
Î“ âŠ¢ v : T    {Ï†}    Î“; Î”, c:S âŠ¢ e : U; Î”'
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“; Î”, c:!{x:T|Ï†}.S âŠ¢ send(c, v); e : U; Î”'
                    when SMT(Ï†[v/x])
```

---

## 5. Security Protocol Examples

### 5.1 Authentication Protocol

```teras
session AuthProtocol =
    // Client sends credentials
    !{username: String | len(username) > 0}.
    !{password: Bytes | len(password) >= 8}.
    // Server responds
    ?{nonce: u64}.
    !{response: Bytes | len(response) == 32}.
    // Server decision
    &{ authenticated: 
         ?{token: SessionToken | valid(token)}.
         AuthenticatedSession,
       rejected:
         ?{reason: Error}.
         end }

type AuthClient = Chan<AuthProtocol>
type AuthServer = Chan<dual(AuthProtocol)>
```

### 5.2 Key Exchange

```teras
session KeyExchange =
    // Send public key
    !{pub_key: PublicKey | curve25519(pub_key)}.
    // Receive server public key
    ?{server_key: PublicKey | curve25519(server_key)}.
    // Compute shared secret (implicit)
    // Continue with encrypted session
    EncryptedSession

fn establish_key(c: lin Chan<KeyExchange>, 
                 keypair: KeyPair) 
    -> (lin Chan<EncryptedSession>, SharedSecret)
{
    let c = send(c, keypair.public);
    let (server_key, c) = recv(c);
    let secret = dh(keypair.private, server_key);
    (c, secret)
}
```

### 5.3 Capability Delegation

```teras
session CapabilityTransfer<C: Capability> =
    // Send capability (linear)
    !lin C.
    // Receive acknowledgment
    ?{ack: bool | ack == true}.
    end

fn delegate<C: Capability>(
    c: lin Chan<CapabilityTransfer<C>>,
    cap: lin C
) -> () {
    let c = send(c, cap);  // cap is now gone
    let (ack, c) = recv(c);
    close(c)
}
```

---

## 6. Multiparty Extension (Phase 3)

### 6.1 Global Type Syntax

```teras
global G ::=
    | p -> q: T.G        // p sends T to q
    | p -> q: {l:G, ...} // Labeled interaction
    | rec X.G            // Recursion
    | X                  // Variable
    | end                // End

// Example: Two-buyer protocol
global TwoBuyer =
    Buyer1 -> Seller: Title.
    Seller -> Buyer1: Price.
    Seller -> Buyer2: Price.
    Buyer1 -> Buyer2: Contribution.
    Buyer2 -> Seller: {
        accept: Buyer2 -> Seller: Address.
                Seller -> Buyer2: Date.end,
        reject: end
    }
```

### 6.2 Projection

```teras
// Project global to local for role
project(G, role) -> S

// Buyer1's local type
project(TwoBuyer, Buyer1) =
    !Title.?Price.!Contribution.end
```

### 6.3 Scribble-like DSL

```teras
protocol TwoBuyer(
    role Buyer1,
    role Buyer2, 
    role Seller
) {
    Title from Buyer1 to Seller;
    Price from Seller to Buyer1, Buyer2;
    Contribution from Buyer1 to Buyer2;
    choice at Buyer2 {
        accept() from Buyer2 to Seller;
        Address from Buyer2 to Seller;
        Date from Seller to Buyer2;
    } or {
        reject() from Buyer2 to Seller;
    }
}
```

---

## 7. Implementation Strategy

### 7.1 Phase 1: Binary Sessions (Weeks 1-8)

- [ ] Session type syntax and parsing
- [ ] Duality computation
- [ ] Linear endpoint tracking
- [ ] Basic typing rules
- [ ] send/recv/select/offer primitives
- [ ] close and recursion

### 7.2 Phase 2: Refinement Integration (Weeks 9-16)

- [ ] Refinement predicates on messages
- [ ] SMT integration for checking
- [ ] Error messages for violations
- [ ] Value-dependent examples

### 7.3 Phase 3: Multiparty Extension (Weeks 17-24)

- [ ] Global type syntax
- [ ] Projection algorithm
- [ ] Coherence checking
- [ ] Scribble-like frontend
- [ ] Multi-role code generation

### 7.4 Phase 4: Advanced Features (Future)

- [ ] Dependent session types
- [ ] Timed sessions
- [ ] Exception handling
- [ ] Shared sessions

---

## 8. Integration with Prior Decisions

### 8.1 A-04 (Linear Types)

Session endpoints are linear:
```teras
// c: lin Chan<S>
let c = send(c, v);  // c is consumed, new c returned
// Old c not usable
```

### 8.2 A-06 (Uniqueness Types)

Session endpoints are unique:
```teras
// c: uniq Chan<S>
// Only one reference to this endpoint
let info = peek(&c);  // Borrow for inspection
let c = send(c, v);   // Consume and continue
```

### 8.3 A-03 (Refinement Types)

Refinements on message types:
```teras
session S = !{n: i32 | n > 0 && n < 100}.end
```

### 8.4 A-05 (Effect Systems)

Session operations as effects:
```teras
// Effect for session I/O
effect Session<S> {
    send<T>(v: T) -> ()
    recv<T>() -> T
    select(label: Label) -> ()
    offer() -> Label
}
```

---

## 9. TERAS Product Integration

### 9.1 MENARA (Mobile Security)

```teras
session MobileAuth =
    // Device registration
    !DeviceId.
    ?Challenge.
    !SignedResponse.
    &{ registered: !Certificate.SecureSession,
       failed: !Error.end }
```

### 9.2 GAPURA (WAF)

```teras
session HTTPSession =
    rec Loop.
    ?Request.
    +{ forward: !Response.Loop,
       block: !BlockedResponse.Loop,
       close: end }
```

### 9.3 BENTENG (Identity)

```teras
session KYCVerification =
    ?IdentityDocument.
    !VerificationRequest.
    ?BiometricChallenge.
    !BiometricResponse.
    &{ verified: !VerificationCertificate.end,
       rejected: !RejectionReason.end }
```

---

## 10. Decision Record

### 10.1 Decision Statement

**ADOPT** binary session types with refinement predicates as TERAS-LANG's protocol specification mechanism, with linear endpoint ownership and phased multiparty extension.

### 10.2 Key Decisions

| ID | Decision | Rationale |
|----|----------|-----------|
| A-07-D1 | First-class session types | Protocol-centric design |
| A-07-D2 | Linear endpoints | Prevent misuse, ensure completion |
| A-07-D3 | Standard binary syntax | Proven, well-understood |
| A-07-D4 | Duality relationship | Two-party protocol safety |
| A-07-D5 | Refinement predicates | Value-dependent protocols |
| A-07-D6 | Typed operations | Safe protocol implementation |
| A-07-D7 | Uniqueness integration | Single-owner endpoints |

### 10.3 Alignment Score

| Criterion | Score | Notes |
|-----------|-------|-------|
| TERAS principles | 9/10 | Verified protocols |
| Security focus | 10/10 | Ideal for auth protocols |
| Implementation | 8/10 | Phased approach manageable |
| Theory foundation | 9/10 | Linear logic connection |
| Integration | 9/10 | Aligns with A-04, A-06 |

**Overall Score**: 9.0/10

### 10.4 Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Multiparty complexity | Medium | Medium | Phased approach |
| SMT performance | Low | Medium | Caching, incremental |
| User learning curve | Medium | Low | Good documentation |

---

## 11. References

1. Honda (1993). "Types for Dyadic Interaction"
2. Caires & Pfenning (2010). "Session Types as Intuitionistic Linear Propositions"
3. Honda, Yoshida, Carbone (2008). "Multiparty Asynchronous Session Types"
4. Toninho, Caires, Pfenning (2011). "Dependent Session Types"
5. Sessions A-04, A-06 decisions

---

## Document Metadata

```yaml
document_id: RESEARCH_A07_SESSION_TYPES_DECISION
version: 1.0.0
date: 2026-01-03
session: A-07
domain: Type Theory Foundations
decision: ADOPT refinement session types
alignment_score: 9.0/10
status: COMPLETE
```
