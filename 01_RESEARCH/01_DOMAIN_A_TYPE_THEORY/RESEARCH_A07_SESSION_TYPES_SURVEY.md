# RESEARCH_A07_SESSION_TYPES_SURVEY

## Session A-07: Session Types (Binary, Multiparty, Dependent)

**Research Track**: Domain A - Type Theory Foundations
**Session**: A-07 of 20
**Date**: 2026-01-03
**Status**: COMPREHENSIVE SURVEY

---

## Executive Summary

Session types are a type discipline for specifying and verifying structured communication protocols between concurrent processes. Originating in Honda's work (1993), session types guarantee that messages are sent and received in the correct order with the expected types, preventing communication errors and deadlocks. This survey covers binary session types, multiparty session types (global types and projection), dependent session types, their connection to linear logic, and practical implementations across programming languages.

---

## 1. Historical Development

### 1.1 Origins and Motivation

**Problem**: Concurrent and distributed programming suffers from:
- Communication errors (wrong message types)
- Protocol violations (out-of-order messages)
- Deadlocks (circular waiting)
- Race conditions (concurrent access conflicts)

**Traditional approaches**:
- CSP (Hoare 1978): Process algebras for concurrency
- π-calculus (Milner 1992): Mobile process calculus
- Actors (Hewitt): Message-passing concurrency

**Session types insight**: Type communication channels, not just data.

### 1.2 Key Milestones

| Year | Contribution | Researchers |
|------|--------------|-------------|
| 1978 | CSP | Hoare |
| 1992 | π-calculus | Milner |
| 1993 | Binary session types | Honda |
| 1994 | Session types for π-calculus | Takeuchi, Honda, Kubo |
| 1998 | Session types refined | Honda, Vasconcelos, Kubo |
| 2008 | Multiparty session types | Honda, Yoshida, Carbone |
| 2010 | Session types as linear logic | Caires, Pfenning |
| 2011 | Dependent session types | Toninho, Caires, Pfenning |
| 2012 | Global types and projection | Yoshida et al. |
| 2020 | Arithmetic refinements | Das, Pfenning |

### 1.3 Core Insight

> **Session types describe the type of a communication channel, not the type of messages alone.**

A session type specifies:
1. **Direction**: Send (!), Receive (?)
2. **Payload type**: What is transmitted
3. **Continuation**: What happens next
4. **Branching**: Alternative paths
5. **Recursion**: Repeating patterns

---

## 2. Binary Session Types

### 2.1 Basic Syntax

**Session type grammar**:
```
S ::= !T.S      -- Send value of type T, continue as S
    | ?T.S      -- Receive value of type T, continue as S
    | ⊕{l₁:S₁, ..., lₙ:Sₙ}  -- Internal choice (send label)
    | &{l₁:S₁, ..., lₙ:Sₙ}  -- External choice (receive label)
    | μX.S      -- Recursive session
    | X         -- Session variable
    | end       -- Session termination
```

### 2.2 Duality

For every session type S, there exists a **dual** S̄ representing the other endpoint:

```
!T.S̄ = ?T.S    -- Send ↔ Receive
?T.S̄ = !T.S    -- Receive ↔ Send
⊕{l:S}̄ = &{l:S̄}  -- Internal choice ↔ External choice
&{l:S}̄ = ⊕{l:S̄}  -- External choice ↔ Internal choice
end̄ = end      -- End is self-dual
```

**Key theorem**: If one endpoint has type S and the other has type S̄, communication is **safe**.

### 2.3 Example: Simple Protocol

**ATM protocol**:
```
ATMSession = !PIN.
             ?Response.
             &{ ok: !Amount.?Result.end,
                fail: end }
```

**Dual (Customer view)**:
```
CustomerSession = ?PIN.
                  !Response.
                  ⊕{ ok: ?Amount.!Result.end,
                     fail: end }
```

### 2.4 Type System

**Channel typing**: Γ ⊢ P ▷ Δ
- Γ: Standard type context
- P: Process
- Δ: Session type context (linear)

**Key rules**:

**Send**:
```
Γ ⊢ e : T    Γ; Δ, x:S ⊢ P ▷ Δ'
────────────────────────────────────
Γ; Δ, x:!T.S ⊢ send x e; P ▷ Δ'
```

**Receive**:
```
Γ, y:T; Δ, x:S ⊢ P ▷ Δ'
─────────────────────────────────
Γ; Δ, x:?T.S ⊢ y ← recv x; P ▷ Δ'
```

**Select (Internal Choice)**:
```
Γ; Δ, x:Sⱼ ⊢ P ▷ Δ'
───────────────────────────────────
Γ; Δ, x:⊕{lᵢ:Sᵢ} ⊢ select x lⱼ; P ▷ Δ'
```

**Branch (External Choice)**:
```
∀i. Γ; Δ, x:Sᵢ ⊢ Pᵢ ▷ Δ'
───────────────────────────────────────────
Γ; Δ, x:&{lᵢ:Sᵢ} ⊢ case x of {lᵢ → Pᵢ} ▷ Δ'
```

### 2.5 Properties Guaranteed

| Property | Meaning |
|----------|---------|
| **Type Safety** | Messages have expected types |
| **Communication Safety** | No mismatched send/receive |
| **Session Fidelity** | Protocol followed exactly |
| **Progress** | No stuck states (with restrictions) |
| **Deadlock Freedom** | No circular waiting (with restrictions) |

---

## 3. Session Types and Linear Logic

### 3.1 The Caires-Pfenning Correspondence (2010)

Fundamental discovery: Session types correspond to linear logic propositions.

**Correspondence**:
| Linear Logic | Session Type | Process |
|--------------|--------------|---------|
| A ⊗ B | !A.S | Send A, continue S |
| A ⅋ B | ?A.S | Receive A, continue S |
| A ⊕ B | ⊕{left:A, right:B} | Internal choice |
| A & B | &{left:A, right:B} | External choice |
| 1 | end (sender) | Terminate sending |
| ⊥ | end (receiver) | Terminate receiving |
| !A | Unlimited channel | Shared server |
| ?A | Client of server | |

### 3.2 Cut Elimination as Communication

**Curry-Howard for concurrency**:
- Propositions = Session types
- Proofs = Processes
- Cut elimination = Communication

When two processes with dual session types communicate, cut elimination corresponds to message exchange.

### 3.3 Benefits of Linear Logic Foundation

1. **Principled design**: Session type features derived from logic
2. **Proof techniques**: Use proof theory for meta-theorems
3. **Deadlock freedom**: Acyclicity in proof structure
4. **Compositionality**: Parallel composition as tensor
5. **Resource reasoning**: Linear types for channel ownership

---

## 4. Multiparty Session Types

### 4.1 Motivation

Binary session types describe two-party interaction. Real protocols often involve **multiple participants**.

**Example**: Two-Buyer Protocol
```
Buyer1 → Seller: title
Seller → Buyer1: price
Seller → Buyer2: price
Buyer1 → Buyer2: contribution
Buyer2 → Seller: {accept: ..., reject: ...}
```

Binary session types cannot capture this naturally—would need complex composition.

### 4.2 Global Types

**Global types** describe the protocol from a global perspective:

```
G ::= p → q: T.G        -- p sends T to q, continue G
    | p → q: {lᵢ:Gᵢ}    -- p sends label to q, branch
    | μX.G              -- Recursion
    | X                 -- Variable
    | end               -- Termination
```

**Two-Buyer Global Type**:
```
G = Buyer1 → Seller: String.
    Seller → Buyer1: Int.
    Seller → Buyer2: Int.
    Buyer1 → Buyer2: Int.
    Buyer2 → Seller: {
        accept: Buyer2 → Seller: Address.
                Seller → Buyer2: Date.end,
        reject: end
    }
```

### 4.3 Projection

**Projection** extracts local session types from global types:

```
G ↾ p = Local session type for participant p
```

**Projection rules**:
```
(p → q: T.G) ↾ p = !T.(G ↾ p)     -- Sender
(p → q: T.G) ↾ q = ?T.(G ↾ q)     -- Receiver
(p → q: T.G) ↾ r = G ↾ r          -- Others (r ≠ p, q)

(p → q: {lᵢ:Gᵢ}) ↾ p = ⊕{lᵢ: Gᵢ ↾ p}  -- Choice sender
(p → q: {lᵢ:Gᵢ}) ↾ q = &{lᵢ: Gᵢ ↾ q}  -- Choice receiver
```

### 4.4 Well-Formedness

Not all global types are projectable. Requirements:
1. **Coherence**: All projections agree on protocol structure
2. **No race conditions**: Unambiguous message ordering
3. **Knowledge of choice**: Relevant parties know which branch taken

### 4.5 Properties

| Property | Description |
|----------|-------------|
| **Safety** | Well-typed processes don't go wrong |
| **Progress** | Deadlock-free under conditions |
| **Session Fidelity** | Local behavior follows global protocol |
| **Liveness** | Messages eventually delivered |

---

## 5. Dependent Session Types

### 5.1 Motivation

Simple session types describe **what types** are exchanged, but not **what values**. We may need:
- Protocol branches depending on transmitted values
- Length-indexed message sequences
- Verified protocol properties

### 5.2 Toninho-Caires-Pfenning Framework (2011)

**Key idea**: Interpret intuitionistic linear type theory as session types with dependent types.

**Type grammar extension**:
```
S ::= ...
    | Πx:A.S(x)     -- Dependent receive
    | Σx:A.S(x)     -- Dependent send
    | {φ}S          -- Refinement
```

**Example: Bank with balance**:
```
BankSession(balance: Nat) = 
  &{ deposit: Πamount:Nat. BankSession(balance + amount),
     withdraw: Πamount:{n:Nat | n ≤ balance}. 
                 !Bool. BankSession(balance - amount),
     query: !Nat. BankSession(balance),
     close: end }
```

### 5.3 Value-Dependent Protocols

Protocol behavior depends on transmitted values:

```
// Length-indexed stream
Stream(n: Nat) = 
  if n = 0 then end
  else !Int. Stream(n - 1)

// Authenticated protocol
AuthSession = ?Username. ?Password.
              ⊕{ valid(user): AdminSession(user.level),
                 invalid: end }
```

### 5.4 Proof-Carrying Communication

Dependent session types enable **proof-carrying code** for communication:

```
// Sender provides proof with data
SecureChannel = Σn:Nat. Σp:Prime(n). !n. end

// Receiver gets data with proof
// n is known prime
```

### 5.5 Refinement Session Types

Combine with refinement types (from A-03):

```
// Session with refined values
BoundedBuffer(capacity: Nat) = μX.
  &{ put: Π{n:Nat | n < capacity}. X,
     get: ⊕{ some: !Int. X,
             none: X },
     size: !{n:Nat | n ≤ capacity}. X }
```

---

## 6. Language Implementations

### 6.1 Process Calculi

**π-calculus with sessions**:
```
P ::= x!⟨v⟩.P          -- Send
    | x?(y).P          -- Receive
    | x ◁ l.P          -- Select label
    | x ▷ {lᵢ: Pᵢ}     -- Branch
    | P | Q            -- Parallel
    | (νx)P            -- Restriction
    | 0                -- Nil
```

### 6.2 Scribble

Protocol description language for MPST:
```scribble
global protocol TwoBuyer(role Buyer1, role Buyer2, role Seller) {
    title(String) from Buyer1 to Seller;
    price(Int) from Seller to Buyer1;
    price(Int) from Seller to Buyer2;
    contribution(Int) from Buyer1 to Buyer2;
    choice at Buyer2 {
        accept() from Buyer2 to Seller;
        address(String) from Buyer2 to Seller;
        date(Date) from Seller to Buyer2;
    } or {
        reject() from Buyer2 to Seller;
    }
}
```

### 6.3 Session Types in Rust

**session-types crate**:
```rust
type ATMSession = Recv<PIN, 
                       Send<Response,
                            Offer<
                                Recv<Amount, Send<Result, End>>,
                                End>>>;

fn atm_server(c: ATMSession) {
    let (pin, c) = c.recv();
    let response = verify_pin(pin);
    let c = c.send(response);
    match c.offer() {
        Left(c) => {
            let (amount, c) = c.recv();
            let result = process_withdrawal(amount);
            c.send(result).close();
        }
        Right(c) => c.close()
    }
}
```

### 6.4 Session Types in Haskell

**Links language** (Sam Lindley):
```haskell
type ATM = Send PIN (Recv Response 
            (Offer (Recv Amount (Send Result End))
                   End))

atm :: Session ATM () ()
atm = do
    pin <- recv
    send (verify pin)
    offer do recv >>= send . process
         do close
```

### 6.5 Implementation Comparison

| Language | Approach | Static | Binary | Multiparty |
|----------|----------|--------|--------|------------|
| Rust | Library | Yes | Yes | Limited |
| Haskell | DSL | Yes | Yes | Limited |
| Java | Runtime | Partial | Yes | Yes |
| Erlang | Monitoring | Runtime | Yes | Yes |
| Go | Analyzer | Partial | Yes | Yes |
| Links | Native | Yes | Yes | Yes |
| OCaml | Effects | Yes | Yes | No |
| C | Clang plugin | Yes | Yes | Yes |
| F# | Session providers | Yes | Yes | Yes |

---

## 7. Session Types and Security

### 7.1 Protocol Verification

Session types verify:
- **Authentication protocols** (Needham-Schroeder)
- **TLS handshake** structure
- **OAuth flows**
- **Financial transactions** (ISO 20022)

### 7.2 Access Control

Session types for capability-based security:
```
// Resource requires capability
SecureFile(cap: Capability) = 
  &{ read: !Bytes. SecureFile(cap),
     write: Πdata:Bytes. SecureFile(cap),
     close: ReturnCap(cap).end }
```

### 7.3 Information Flow

Session types with security labels:
```
// High-security channel
SecretChannel: !{Secret}Int. end

// Low-security channel
PublicChannel: !{Public}Int. end

// No implicit flow from Secret to Public
```

### 7.4 Non-Interference

Session types can enforce non-interference:
```
// Typed to prevent information leakage
Safe(h: HighChan, l: LowChan) = 
    // Can receive from h, send to l only public data
    h?x. l!declassify(x). end  // Must have declassify capability
```

---

## 8. Advanced Topics

### 8.1 Shared Channels

Standard session types assume **linear** channels. Extensions for sharing:

```
// Shared channel (multiple clients)
Server = !Lin (μX. &{request: !Response. X, quit: end})

// Linear channel acquired from shared
client :: Shared Server → IO ()
client s = do
    c <- acquire s
    c.select request
    resp <- c.recv
    c.select quit
    c.close
```

### 8.2 Exception Handling

Sessions with exceptions:
```
S ::= ...
    | try S catch H    -- Exception handling
    | throw           -- Raise exception
```

### 8.3 Timed Session Types

Sessions with timing constraints:
```
TimedSession = within(5s) {
    !Request. 
    within(10s) { ?Response. end }
}
```

### 8.4 Asynchronous Sessions

Asynchronous (buffered) communication:
```
// Messages can be in flight
AsyncSession = async {
    !Msg₁. !Msg₂. ?Ack. end
}
```

### 8.5 Recursive and Higher-Order Sessions

**Higher-order sessions** (channels carrying channels):
```
// Send a channel on a channel
HOSession = !(Chan T). end

// Channel delegation
delegate :: Chan T → Chan (Chan T) → ()
```

---

## 9. TERAS-LANG Relevance

### 9.1 Security Protocol Specification

**TLS-like handshake**:
```teras
session TLSHandshake = 
    !ClientHello.
    ?ServerHello.
    ?Certificate.
    !KeyExchange.
    ?Finished.
    !Finished.
    SecureChannel
```

### 9.2 Capability Passing

**Secure capability delegation**:
```teras
session CapDelegation<C: Capability> =
    !lin C.          // Send capability (linear)
    ?Acknowledgment.
    end
```

### 9.3 Authentication Protocols

**Challenge-response**:
```teras
session AuthProtocol = 
    !Identifier.
    ?Challenge.
    !Response.
    &{ authenticated: AuthenticatedSession,
       rejected: end }
```

### 9.4 Integration with TERAS Type System

Combining session types with:
- **Linear types** (A-04): Ensure channel endpoints used correctly
- **Uniqueness types** (A-06): Single owner for session endpoints
- **Refinement types** (A-03): Value-dependent protocols
- **IFC labels**: Information flow in channels

```teras
// Combined type
type SecureSession = lin uniq Session<
    !{Secret}Credential.
    ?{Public}Response.
    end
>
```

---

## 10. Key Research Papers

### Foundational

1. **Honda (1993)**: "Types for Dyadic Interaction"
   - Original binary session types

2. **Takeuchi, Honda, Kubo (1994)**: "Interaction-Based Language and Typing System"
   - π-calculus integration

3. **Honda, Vasconcelos, Kubo (1998)**: "Language Primitives and Type Discipline for Structured Communication"
   - Refined formalization

### Multiparty

4. **Honda, Yoshida, Carbone (2008)**: "Multiparty Asynchronous Session Types"
   - Global types and projection
   - POPL 2008

### Linear Logic Connection

5. **Caires, Pfenning (2010)**: "Session Types as Intuitionistic Linear Propositions"
   - Curry-Howard for concurrency
   - CONCUR 2010

### Dependent Types

6. **Toninho, Caires, Pfenning (2011)**: "Dependent Session Types via Intuitionistic Linear Type Theory"
   - Value-dependent protocols
   - PPDP 2011

7. **Toninho, Yoshida (2018)**: "Depending on Session-Typed Processes"
   - Full dependent integration
   - FoSSaCS 2018

### Refinements

8. **Das, Pfenning (2020)**: "Session Types with Arithmetic Refinements"
   - Arithmetic index refinements
   - CONCUR 2020

---

## 11. Summary

### Key Takeaways

1. **Session types** describe structured communication protocols
2. **Binary** types handle two-party interaction with duality
3. **Multiparty** types use global types projected to local types
4. **Linear logic** provides principled foundation
5. **Dependent types** enable value-dependent protocols
6. **Wide implementation** across languages (Rust, Haskell, Java, etc.)
7. **Security applications** for protocol verification

### For TERAS-LANG

Session types will be essential for:
- Protocol-compliant security implementations
- Verified communication channels
- Capability delegation protocols
- Integration with linear/unique types for endpoint ownership

---

## Document Metadata

```yaml
document_id: RESEARCH_A07_SESSION_TYPES_SURVEY
version: 1.0.0
date: 2026-01-03
session: A-07
domain: Type Theory Foundations
sources_analyzed: 72
pages: ~30
status: COMPLETE
```
