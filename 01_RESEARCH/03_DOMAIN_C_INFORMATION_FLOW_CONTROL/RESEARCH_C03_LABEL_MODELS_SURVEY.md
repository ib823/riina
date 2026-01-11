# TERAS-LANG Research Survey C-03: Label Models

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C03-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-03 |
| Domain | C: Information Flow Control |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Security labels define the granularity and expressiveness of IFC policies. This survey covers simple lattices, decentralized label models (DLM), dependent labels, and hybrid models, with focus on practical security policies for TERAS products.

---

## Part 1: Simple Lattice Models

### 1.1 Linear Lattices

```
Military Classification (Bell-LaPadula):

    Top Secret
        │
      Secret
        │
    Confidential
        │
    Unclassified

Properties:
    - Total ordering
    - Simple to understand
    - Limited expressiveness
    - No compartmentalization
```

### 1.2 Powerset Lattices

```
Category-Based Labels:

Labels = P({HR, Finance, Engineering, Legal})

Examples:
    {HR}                    -- HR only
    {HR, Finance}           -- HR and Finance
    {HR, Finance, Legal}    -- Multiple departments
    {}                      -- Public (bottom)
    {HR, Finance, Eng, Legal} -- All (top)

Join: Union of sets
Meet: Intersection of sets
```

### 1.3 Product Lattices

```
Combining dimensions:

Label = Level × Compartments × Integrity

Example:
    (Secret, {Project_X}, Trusted)
    
Properties:
    - Multiple independent dimensions
    - Fine-grained policies
    - Exponential label space
```

---

## Part 2: Decentralized Label Model (DLM)

### 2.1 Core Concepts

```
DLM (Myers & Liskov, 1997):

Label = { owner₁: readers₁; owner₂: readers₂; ... }

Components:
    - Owner: Principal who controls the data
    - Readers: Principals allowed to read
    
Example:
    {Alice: Bob, Charlie; David: Eve}
    
    Alice allows Bob and Charlie to read
    David allows Eve to read
    Effective readers = {Bob, Charlie} ∩ {Eve} = {}
```

### 2.2 Label Operations

```
Join (most restrictive):
    {o: R₁} ⊔ {o: R₂} = {o: R₁ ∩ R₂}
    
    "Only principals in BOTH sets can read"

Meet (least restrictive):
    {o: R₁} ⊓ {o: R₂} = {o: R₁ ∪ R₂}
    
    "Principals in EITHER set can read"

Flow relation:
    L₁ ⊑ L₂ iff effective_readers(L₂) ⊆ effective_readers(L₁)
    
    "L₂ is more restrictive than L₁"
```

### 2.3 Acts-For Relation

```
Delegation hierarchy:

    CEO
   /   \
  CFO   CTO
  |      |
 Finance Engineering

acts_for(CEO, CFO) = true
acts_for(CFO, CEO) = false
acts_for(CEO, Finance) = true (transitive)

Usage:
    - Declassification authority
    - Role-based access
    - Delegation of trust
```

### 2.4 Declassification

```
Owner-controlled declassification:

// Original label
let secret = {Alice: Alice}  // Only Alice can read

// Alice declassifies to Bob
let shared = declassify(secret, {Alice: Alice, Bob})
              ^^^^^^^^^^^^^^^^^^
              Only valid if current_principal acts_for Alice

// Integrity check prevents unauthorized declassification
fn bad() {
    // Eve cannot declassify Alice's data
    declassify(alice_secret, {Alice: *})  // ERROR!
}
```

---

## Part 3: Dependent Labels

### 3.1 Labels Dependent on Values

```
Label depends on runtime data:

fn read_at_level(user: User) -> Data @ user.clearance {
    // Return type depends on user's clearance level
    database.read_at(user.clearance)
}

Type: (u: User) → Data @ u.clearance
```

### 3.2 Policy Parameters

```
Parameterized policies:

policy UserCanRead(user: User, data: Data) {
    user.clearance ⊒ data.classification
}

fn access(user: User, data: Data @ L) -> Data @ L
    where UserCanRead(user, data)
{
    data
}
```

### 3.3 First-Class Labels

```
Labels as runtime values:

fn label_of<T>(x: T @ L) -> Label {
    L  // Return the label
}

fn check_flow(from: Label, to: Label) -> bool {
    from.flows_to(to)
}

fn upgrade<L1, L2>(x: T @ L1, target: L2) -> T @ (L1 ⊔ L2)
    where L1 ⊑ L2
{
    x as T @ (L1 ⊔ L2)
}
```

---

## Part 4: Integrity Labels

### 4.1 Dual of Confidentiality

```
Integrity concerns TRUST, not secrecy:

High Integrity: Trusted source
Low Integrity:  Untrusted source (e.g., user input)

Flow direction (OPPOSITE to confidentiality):
    Trusted → Untrusted   ✓ (allowed)
    Untrusted → Trusted   ✗ (blocked)
```

### 4.2 Integrity in DLM

```
DLM Integrity Component:

Label = { owners : readers ; ← writers }
        ^^^^^^^^^^^^^^^^^^^   ^^^^^^^^^^
        Confidentiality       Integrity

Integrity meaning:
    { ← Alice, Bob }  means Alice and Bob have "endorsed" this
    
Writers are SOURCES of trust, not destinations
```

### 4.3 Robust Declassification

```
Integrity protects declassification:

// Only trusted code can declassify
fn declassify(x: T @ (Secret, Trusted)) -> T @ (Public, Trusted)
    where CurrentPrincipal: Trusted
{
    // Attacker cannot inject declassify call
}

// Untrusted code cannot declassify
fn attack(x: T @ (Secret, Untrusted)) -> T @ (Public, _) {
    declassify(x)  // ERROR: no authority
}
```

---

## Part 5: Specialized Label Models

### 5.1 Taint Labels

```
Taint Tracking:

enum TaintSource {
    UserInput,
    NetworkData,
    FileSystem,
    DatabaseQuery,
    Environment,
}

type Taint = Set<TaintSource>

Flow rules:
    - Operations propagate taint (union)
    - Sanitization removes taint
    - Sinks check for taint
```

### 5.2 Capability Labels

```
Capability-Based Labels:

enum Capability {
    FileRead, FileWrite,
    NetworkAccess,
    ProcessControl,
    CryptoOperations,
}

type CapLabel = Set<Capability>

Usage:
    fn read_file(path) -> Data @ {FileRead} {
        // Can only call with FileRead capability
    }
```

### 5.3 Temporal Labels

```
Time-Based Labels:

struct TemporalLabel {
    base: Label,
    valid_from: Timestamp,
    valid_until: Timestamp,
}

Usage:
    - Time-limited access
    - Embargo periods
    - Automatic reclassification
```

---

## Part 6: Label Inference

### 6.1 Constraint-Based Inference

```
Generate and solve label constraints:

// Source (no labels)
fn process(x, y) {
    let z = x + y
    return z
}

// Constraints generated
L_x ⊔ L_y ⊑ L_z
L_z = L_return

// Inferred type
fn process<L>(x: int@L, y: int@L) -> int@L
```

### 6.2 Bidirectional Label Checking

```
Combine inference with checking:

// Explicit labels propagate inward
fn explicit(x: int@Secret) -> int@Secret {
    let y = x + 1  // y inferred as @Secret
    y
}

// Internal inference, explicit boundaries
fn internal() {
    let a = get_secret()  // @Secret inferred
    let b = a * 2         // @Secret inferred
    publish(b)            // ERROR: Secret → Public
}
```

---

## Part 7: TERAS Label Design

### 7.1 TERAS Security Lattice

```rust
// Core security levels
#[derive(PartialOrd, Ord, Clone, Copy)]
pub enum SecurityLevel {
    Public = 0,
    Internal = 1,
    Confidential = 2,
    Secret = 3,
    TopSecret = 4,
}

// Compartments
#[derive(Clone)]
pub struct Compartment(Set<String>);

// Full label
#[derive(Clone)]
pub struct Label {
    pub level: SecurityLevel,
    pub compartments: Compartment,
    pub integrity: IntegrityLevel,
    pub owner: Option<Principal>,
    pub readers: Option<Set<Principal>>,
}
```

### 7.2 Label Operations

```rust
impl Label {
    pub fn join(&self, other: &Label) -> Label {
        Label {
            level: max(self.level, other.level),
            compartments: self.compartments.union(&other.compartments),
            integrity: min(self.integrity, other.integrity),
            owner: self.owner.or(other.owner),
            readers: match (&self.readers, &other.readers) {
                (Some(r1), Some(r2)) => Some(r1.intersection(r2)),
                (Some(r), None) | (None, Some(r)) => Some(r.clone()),
                (None, None) => None,
            },
        }
    }
    
    pub fn can_flow_to(&self, target: &Label) -> bool {
        // Confidentiality: self must be ≤ target
        self.level <= target.level &&
        self.compartments.is_subset(&target.compartments) &&
        // Integrity: self must be ≥ target (opposite direction)
        self.integrity >= target.integrity &&
        // DLM: target readers subset of self readers
        match (&self.readers, &target.readers) {
            (Some(sr), Some(tr)) => tr.is_subset(sr),
            (None, _) => true,
            (Some(_), None) => false,
        }
    }
}
```

### 7.3 Product-Specific Labels

```rust
// MENARA (Mobile Security)
mod menara {
    pub const DEVICE_ID: Label = Label::new(Confidential, {DeviceInfo});
    pub const LOCATION: Label = Label::new(Secret, {LocationData});
    pub const BIOMETRIC: Label = Label::new(TopSecret, {BiometricData});
}

// GAPURA (WAF)
mod gapura {
    pub const USER_INPUT: Label = Label::untrusted();
    pub const VALIDATED: Label = Label::trusted(Internal);
    pub const BLOCKED_IP: Label = Label::new(Internal, {ThreatIntel});
}

// ZIRAH (EDR)
mod zirah {
    pub const PROCESS_DATA: Label = Label::new(Confidential, {EndpointData});
    pub const THREAT_SIG: Label = Label::new(Secret, {ThreatIntel});
    pub const QUARANTINE: Label = Label::new(Secret, {MalwareData});
}

// BENTENG (eKYC)
mod benteng {
    pub const PERSONAL_ID: Label = Label::new(Secret, {PII});
    pub const FACE_TEMPLATE: Label = Label::new(TopSecret, {BiometricData});
    pub const VERIFICATION: Label = Label::new(Confidential, {KYCResult});
}

// SANDI (Digital Signatures)
mod sandi {
    pub const PRIVATE_KEY: Label = Label::new(TopSecret, {CryptoKey});
    pub const PUBLIC_KEY: Label = Label::new(Public, {});
    pub const SIGNATURE: Label = Label::new(Internal, {CryptoOutput});
}
```

---

## Part 8: Bibliography

1. Myers, A.C., Liskov, B. (1997). "A Decentralized Model for Information Flow Control"
2. Myers, A.C., Liskov, B. (2000). "Protecting Privacy using the Decentralized Label Model"
3. Zdancewic, S., Myers, A.C. (2001). "Robust Declassification"
4. Chong, S., Myers, A.C. (2006). "Decentralized Robustness"
5. Bell, D.E., LaPadula, L.J. (1973). "Secure Computer Systems"

---

*Research Track Output — Domain C: Information Flow Control*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
