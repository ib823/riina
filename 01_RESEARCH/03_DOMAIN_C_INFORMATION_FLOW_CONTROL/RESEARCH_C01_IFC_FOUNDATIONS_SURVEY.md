# TERAS-LANG Research Survey C-01: Information Flow Control Foundations

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C01-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-01 |
| Domain | C: Information Flow Control |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Information Flow Control (IFC) is the foundation of security type systems, tracking how sensitive data propagates through programs. This survey covers the theoretical foundations, lattice-based security models, noninterference properties, and their application to programming language design critical for TERAS's security guarantees.

---

## Part 1: Information Flow Fundamentals

### 1.1 What is Information Flow?

```
Information Flow: The transfer of data between security domains

Flow occurs when:
├── Direct assignment: x = y
├── Indirect via control: if secret then public = 1
├── Via covert channels: timing, storage, power
└── Via side effects: exceptions, termination

IFC Goal: Prevent unauthorized information flow
```

### 1.2 Historical Development

```
Timeline:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1973    │ Bell-LaPadula: Military security model
1976    │ Denning: Lattice model for secure flow
1977    │ Denning & Denning: Certification of programs
1996    │ Volpano, Smith, Irvine: Type system for IFC
1999    │ Myers & Liskov: JFlow/Jif language
2000    │ Sabelfeld & Myers: Language-based IFC survey
2006    │ Li & Zdancewic: Downgrading policies
2010    │ Stefan et al: LIO monad
2014    │ Rajani & Garg: Types for IFC
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.3 Security Properties

```
Confidentiality: Secret data doesn't flow to public outputs
    Secret → Public  ✗ (prohibited)
    Public → Secret  ✓ (allowed, upgrades)

Integrity: Untrusted data doesn't influence trusted computations
    Untrusted → Trusted  ✗ (prohibited)
    Trusted → Untrusted  ✓ (allowed)

Availability: (Not typically addressed by IFC)
```

---

## Part 2: Security Lattices

### 2.1 Lattice Theory Basics

```
A security lattice (L, ⊑) is a partially ordered set where:
├── ⊥ (bottom): Least restrictive (public)
├── ⊤ (top): Most restrictive (top secret)
├── ⊔ (join): Least upper bound
└── ⊓ (meet): Greatest lower bound

Properties:
    ∀a,b ∈ L: a ⊔ b ∈ L    (closed under join)
    ∀a,b ∈ L: a ⊓ b ∈ L    (closed under meet)
```

### 2.2 Common Security Lattices

```
Two-Point Lattice (Simplest):
    High (Secret)
        │
    Low (Public)

Four-Level Military:
       TopSecret
          │
       Secret
          │
     Confidential
          │
     Unclassified

Diamond Lattice (Compartments):
           ⊤
          / \
         A   B
          \ /
           ⊥

Powerset Lattice (Categories):
    Labels = P({HR, Finance, Engineering})
    Order = subset relation
```

### 2.3 Flow Relation

```
Information can flow from L₁ to L₂ iff L₁ ⊑ L₂

"Can flow to" relation (⊑):
    Public ⊑ Secret     ✓ (upgrade allowed)
    Secret ⊑ Public     ✗ (leak!)
    Secret ⊑ Secret     ✓ (same level)

Label join for combined data:
    Secret ⊔ Public = Secret
    HR ⊔ Finance = {HR, Finance}
```

---

## Part 3: Noninterference

### 3.1 Definition

```
Noninterference (Goguen & Meseguer, 1982):

A program P satisfies noninterference if:
    For all inputs i₁, i₂ where i₁ =_L i₂:
        P(i₁) =_L P(i₂)

Where =_L means "equal at security level L"

Intuition: Low-security outputs depend only on
           low-security inputs
```

### 3.2 Formal Statement

```
Let:
    H = high-security inputs
    L = low-security inputs
    out_L = low-security outputs

Noninterference:
    ∀h₁, h₂ ∈ H, l ∈ L:
        out_L(P(h₁, l)) = out_L(P(h₂, l))

The high inputs h₁, h₂ don't affect low outputs.
```

### 3.3 Types of Noninterference

```
Termination-Insensitive Noninterference (TINI):
├── Ignores termination behavior
├── Allows: while(secret) {}  (infinite loop leak)
├── Practical for most systems
└── Used by most IFC systems

Termination-Sensitive Noninterference (TSNI):
├── Considers termination as observable
├── Forbids: while(secret) {}
├── Stronger guarantee
└── Harder to achieve

Progress-Sensitive Noninterference (PSNI):
├── Progress must not depend on secrets
├── Intermediate between TINI and TSNI
└── Practical and meaningful
```

### 3.4 Implicit Flows

```
Implicit Flow: Information leak via control flow

Example:
    if secret then public := 1 else public := 0

The value of 'public' reveals 'secret'!

Detection: Track program counter label
    pc : Label  -- current security context
    
Rule: In branch on secret, pc ⊒ secret_level
      All assignments must be at least pc level
```

---

## Part 4: Type Systems for IFC

### 4.1 Security Types

```
Security Type: τ^L where τ is base type, L is label

int^High      -- high-security integer
string^Low    -- low-security string
(int^H → int^L)  -- function: high to low (leak!)

Type well-formedness:
    τ^L well-formed if τ well-formed
```

### 4.2 Typing Rules

```
Subtyping (covariant in label):
    L₁ ⊑ L₂
    ─────────────
    τ^L₁ <: τ^L₂

Variable:
    x : τ^L ∈ Γ
    ──────────────
    Γ ⊢ x : τ^L

Assignment:
    Γ ⊢ e : τ^L₁    x : τ^L₂ ∈ Γ    L₁ ⊔ pc ⊑ L₂
    ────────────────────────────────────────────────
    Γ, pc ⊢ x := e

Conditional:
    Γ ⊢ e : bool^L
    Γ, pc ⊔ L ⊢ c₁    Γ, pc ⊔ L ⊢ c₂
    ─────────────────────────────────────
    Γ, pc ⊢ if e then c₁ else c₂
```

### 4.3 Soundness

```
Type Soundness for IFC:

Theorem: If ∅, ⊥ ⊢ P : cmd then P satisfies noninterference.

Proof approach:
1. Define logical relation for security types
2. Show typing rules preserve relation
3. Fundamental lemma implies noninterference
```

---

## Part 5: Explicit vs Implicit Labels

### 5.1 Explicit Labels

```
Explicit: Labels written in source code

let secret : int^High = get_password()
let public : int^Low = 0

// Error: High → Low flow
let leak : int^Low = secret  // TYPE ERROR

Pros:
+ Clear security policy
+ Precise control
+ Self-documenting

Cons:
- Verbose
- Annotation burden
- Refactoring pain
```

### 5.2 Implicit Labels (Label Inference)

```
Implicit: Labels inferred by type system

let secret = get_password()  // Inferred: High
let public = 0               // Inferred: Low

// Error detected via inference
let leak = secret           // Inferred: High (not Low!)

Pros:
+ Less annotation
+ Easier refactoring
+ Type inference technology

Cons:
- Harder error messages
- May need annotations at boundaries
- Inference complexity
```

### 5.3 Hybrid Approach

```
Best of both worlds:

// Explicit at API boundaries
pub fn get_secret() -> int^Secret { ... }

// Inferred internally  
fn process() {
    let x = get_secret()  // x : int^Secret (inferred)
    let y = x + 1         // y : int^Secret (inferred)
}
```

---

## Part 6: Decentralized Labels

### 6.1 Decentralized Label Model (DLM)

```
Myers & Liskov (1997): Decentralized IFC

Labels include PRINCIPALS (owners):
    {Alice: Bob, Charlie}
    
Meaning: Alice owns data; Bob and Charlie can read

Reader sets:
    {o: r₁, r₂, ...}
    Owner o allows readers r₁, r₂, ...
```

### 6.2 Label Operations in DLM

```
Join (most restrictive):
    {Alice: Bob} ⊔ {Alice: Charlie} = {Alice: Bob ∩ Charlie}
    
    If Bob can read A and Charlie can read B,
    only intersection can read A ⊔ B.

Meet (least restrictive):
    {Alice: Bob} ⊓ {Alice: Charlie} = {Alice: Bob ∪ Charlie}

Acts-for:
    Alice acts-for Bob means Alice can read Bob's data
```

### 6.3 Declassification in DLM

```
Owner-controlled declassification:

{Alice: Alice} → {Alice: Bob}

Alice can declassify her own data to Bob.
Non-owners cannot declassify.

Code:
    declassify(secret, {Alice: Bob})
    // Only valid if current principal acts-for Alice
```

---

## Part 7: Covert Channels

### 7.1 Channel Taxonomy

```
Covert Channels:

Storage Channels:
├── Shared memory/files
├── Database state
└── Configuration

Timing Channels:
├── Execution time variations
├── Cache timing
└── Network latency

Termination Channels:
├── Program termination
├── Exception raising
└── Progress observation

Power/EM Channels:
├── Power consumption
├── EM emanations
└── (Hardware-level)
```

### 7.2 Timing Channels

```
Example timing leak:

fn check_password(input: str^Low, actual: str^High) -> bool^Low {
    for i in 0..input.len() {
        if input[i] != actual[i] {
            return false  // Returns early!
        }
    }
    true
}

Attack: Measure response time to guess password character by character

Mitigation: Constant-time comparison
```

### 7.3 Mitigation Strategies

```
Covert Channel Mitigations:

1. Padding/Noise
   - Add random delays
   - Reduce bandwidth

2. Constant-Time Execution
   - No secret-dependent branches
   - Compiler support needed

3. Isolation
   - Separate processes
   - Air gaps

4. Formal Verification
   - Prove absence of channels
   - Expensive but thorough
```

---

## Part 8: IFC Languages

### 8.1 Jif (Java + Information Flow)

```java
// Jif: Java with security labels

class Example {
    // Labeled field
    int{Alice:Bob} secret;
    
    // Labeled method
    int{Alice:} process{Alice:}(int{Alice:} x) {
        return x + secret;  // Both labeled
    }
    
    // Declassification
    void release() where caller(Alice) {
        int{Alice:*} public = declassify(secret, {Alice:*});
    }
}
```

### 8.2 FlowCaml

```ocaml
(* FlowCaml: OCaml with IFC *)

(* Security levels *)
level Low < High

(* Labeled types *)
val secret : (int, High) t
val public : (int, Low) t

(* Function with flow constraint *)
val process : (int, 'a) t -> (int, 'a) t

(* Error: flow violation *)
let leak = (secret : (int, Low) t)  (* Type error! *)
```

### 8.3 LIO (Labeled IO)

```haskell
-- LIO: Haskell library for IFC

-- Labels
data Label = Low | High deriving (Eq, Ord)

-- Labeled computation
type LIO l a = LIORef Label -> IO a

-- Labeled value
data Labeled l a = Labeled Label a

-- Operations
label :: a -> LIO l (Labeled l a)
unlabel :: Labeled l a -> LIO l a  -- Raises current label

-- Example
example :: LIO High Int
example = do
    secret <- unlabel secretData  -- Current label becomes High
    return (secret + 1)
```

---

## Part 9: Security Applications

### 9.1 Web Application Security

```
IFC for Web Apps:

Client-Server Flow:
    User Input (Untrusted) → Validation → Database (Trusted)
    
Label Mapping:
    UserInput : Tainted
    Session : Confidential
    PublicContent : Public
    AdminData : Secret

Policies:
    - Tainted data must be sanitized before storage
    - Secret data cannot flow to client response
    - Session data scoped to user
```

### 9.2 Database Security

```
Row-Level Security via IFC:

Table: Employees
    name    : string^Public
    salary  : int^{HR}
    ssn     : string^{HR, Employee}

Query Rewriting:
    SELECT salary FROM employees
    → Error: Current principal doesn't have HR

    SELECT name FROM employees
    → OK: name is Public
```

### 9.3 Mobile Security

```
Android/iOS IFC:

Sensitive Sources:
    Location    : PrivacySensitive
    Contacts    : PrivacySensitive  
    Camera      : PrivacySensitive

Sinks:
    Network     : External
    SMS         : External
    Storage     : Persistent

Policy: PrivacySensitive ⋢ External without user consent
```

---

## Part 10: TERAS IFC Design

### 10.1 Security Levels

```rust
// TERAS security lattice

#[derive(PartialOrd, Ord)]
enum SecurityLevel {
    Public,        // ⊥ - Anyone can read
    Internal,      // Company internal
    Confidential,  // Need-to-know
    Secret,        // Cleared personnel only
    TopSecret,     // ⊤ - Highest classification
}

// Lattice operations
impl SecurityLevel {
    fn join(self, other: Self) -> Self {
        max(self, other)
    }
    
    fn meet(self, other: Self) -> Self {
        min(self, other)
    }
    
    fn flows_to(self, other: Self) -> bool {
        self <= other
    }
}
```

### 10.2 Security Labels

```rust
// TERAS label with principals

struct Label {
    owner: Principal,
    readers: Set<Principal>,
    level: SecurityLevel,
}

impl Label {
    fn can_flow_to(&self, target: &Label) -> bool {
        // Level check
        self.level.flows_to(target.level) &&
        // Reader restriction (DLM-style)
        target.readers.is_subset(&self.readers)
    }
}

// Labeled type
type Labeled<L: Label, T> = (T, PhantomData<L>);
```

### 10.3 Integration with Effects

```rust
// IFC as effect + coeffect

// Effect for security operations
effect Security<L: Label> {
    label<T>(value: T) -> Labeled<L, T>,
    unlabel<T>(labeled: Labeled<L, T>) -> T,
    declassify<L1, L2, T>(value: Labeled<L1, T>) -> Labeled<L2, T>
        where CurrentPrincipal: ActsFor<L1.owner>
}

// Coeffect for security context
fn process_secret() -[IO]-> Result @ {Clearance::Secret} {
    // Can only call if context has Secret clearance
}
```

---

## Part 11: Bibliography

1. Bell, D.E., LaPadula, L.J. (1973). "Secure Computer Systems: Mathematical Foundations"
2. Denning, D.E. (1976). "A Lattice Model of Secure Information Flow"
3. Goguen, J.A., Meseguer, J. (1982). "Security Policies and Security Models"
4. Volpano, D., Smith, G., Irvine, C. (1996). "A Sound Type System for Secure Flow Analysis"
5. Myers, A.C., Liskov, B. (1997). "A Decentralized Model for Information Flow Control"
6. Sabelfeld, A., Myers, A.C. (2003). "Language-Based Information-Flow Security"
7. Stefan, D., et al. (2011). "Flexible Dynamic Information Flow Control in Haskell"

---

*Research Track Output — Domain C: Information Flow Control*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
