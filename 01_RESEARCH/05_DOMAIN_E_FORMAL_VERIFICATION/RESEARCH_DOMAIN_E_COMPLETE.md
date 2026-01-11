# TERAS-LANG Research Domain E: Formal Verification

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-E-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | E-01 through E-10 |
| Domain | E: Formal Verification |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# E-01: Verification Foundations

## What is Formal Verification?

```
Formal Verification: Mathematical proof that a program satisfies its specification

Levels:
├── Type checking: Lightweight verification
├── Static analysis: Approximation-based
├── Model checking: Exhaustive state exploration
├── Theorem proving: Full mathematical proof
└── Certified compilation: Proof-preserving translation
```

## Verification Properties

```
Safety: "Nothing bad happens"
    - No null pointer dereference
    - No buffer overflow
    - No data races

Liveness: "Something good eventually happens"
    - Termination
    - Progress
    - Eventual consistency

Security:
    - Noninterference
    - Confidentiality
    - Integrity
```

## TERAS Decision E-01

**ADOPT** multi-level verification:
1. Type system as primary verification
2. Refinement types for specifications
3. Optional theorem proving for critical code
4. Automated verification where possible

### Architecture Decision ID: `TERAS-ARCH-E01-VER-001`

---

# E-02: Refinement Types

## Definition

```rust
// Refinement type: Base type + Predicate
type Nat = { x: i32 | x >= 0 }
type NonZero = { x: i32 | x != 0 }
type Range = { x: i32 | 0 <= x && x < len }

// Function with refinements
fn divide(n: i32, d: NonZero) -> i32 {
    n / d  // Safe: d cannot be zero
}

fn array_access<T>(arr: &[T; N], idx: { i: usize | i < N }) -> &T {
    &arr[idx]  // Safe: idx in bounds
}
```

## Liquid Types (SMT-Based)

```
Liquid Types = Refinement Types + SMT Solving

1. Express predicates in decidable logic (QF_LIA, QF_LRA)
2. Generate verification conditions
3. Discharge to SMT solver (Z3, CVC5)
4. Report errors if unsatisfiable
```

## TERAS Refinement Design

```rust
// Refinement syntax
fn process(
    input: { s: String | s.len() <= 1024 },
    count: { n: u32 | n > 0 && n <= 100 }
) -> { r: Vec<u8> | r.len() == count as usize } {
    // Implementation
}

// Security refinements
fn encrypt(
    key: { k: Key | k.is_valid() && k.algorithm == AES256 },
    plaintext: { p: Bytes | p.len() <= MAX_PLAINTEXT }
) -> { c: Ciphertext | c.algorithm == AES256 } {
    // Verified encryption
}
```

## TERAS Decision E-02

**ADOPT** refinement types:
1. Liquid-type style with SMT solving
2. Security-relevant predicates
3. Decidable fragment for automation
4. Escape hatch for complex properties

### Architecture Decision ID: `TERAS-ARCH-E02-REF-001`

---

# E-03: Dependent Types

## Full Dependency

```rust
// Types that depend on values

// Length-indexed vectors
type Vec<T, N: Nat> where N is value

fn concat<T, N: Nat, M: Nat>(
    a: Vec<T, N>, 
    b: Vec<T, M>
) -> Vec<T, N + M> {
    // Type guarantees result length
}

// Sized matrices
fn multiply<T: Num, N, M, P>(
    a: Matrix<T, N, M>,
    b: Matrix<T, M, P>
) -> Matrix<T, N, P> {
    // Dimensions statically checked
}
```

## Dependent Types for Security

```rust
// Security-indexed types
type Encrypted<L: SecurityLevel, T> = ...

fn encrypt<L, T>(key: Key @ L, data: T) -> Encrypted<L, T> {
    // Encrypted at level L
}

fn decrypt<L, T>(key: Key @ L, cipher: Encrypted<L, T>) -> T @ L {
    // Result has label L
}
```

## TERAS Decision E-03

**ADOPT** limited dependent types:
1. Value-indexed types for sizes/lengths
2. Type families for computed types
3. Security-indexed types
4. Avoid full dependent types (complexity)

### Architecture Decision ID: `TERAS-ARCH-E03-DEP-001`

---

# E-04: Contract-Based Verification

## Design by Contract

```rust
// Pre/post conditions and invariants

#[requires(n > 0)]
#[ensures(result >= 1)]
fn factorial(n: u32) -> u32 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

// Class invariants
#[invariant(self.balance >= 0)]
struct BankAccount {
    balance: i64,
}

impl BankAccount {
    #[requires(amount > 0)]
    #[ensures(self.balance == old(self.balance) + amount)]
    fn deposit(&mut self, amount: i64) {
        self.balance += amount;
    }
    
    #[requires(amount > 0 && amount <= self.balance)]
    #[ensures(self.balance == old(self.balance) - amount)]
    fn withdraw(&mut self, amount: i64) {
        self.balance -= amount;
    }
}
```

## Security Contracts

```rust
// Information flow contracts
#[ensures(result.label() <= input.label())]
fn downgrade(input: Labeled<T>) -> Labeled<T> { ... }

// Capability contracts
#[requires(caller.has_capability(Capability::FileWrite))]
#[ensures(file.modified())]
fn write_file(file: &mut File, data: &[u8]) { ... }

// Audit contracts
#[ensures(audit_log.contains(AuditEvent::AccessAttempt))]
fn access_sensitive_data(user: &User) -> Data { ... }
```

## TERAS Decision E-04

**ADOPT** contracts:
1. Pre/post conditions
2. Class invariants
3. Security-specific contracts
4. Static verification where possible

### Architecture Decision ID: `TERAS-ARCH-E04-CTR-001`

---

# E-05: Separation Logic

## Core Concepts

```
Separation Logic: Reasoning about heap-manipulating programs

Key connectives:
    emp         -- Empty heap
    e ↦ v       -- e points to v (exactly)
    P * Q       -- P and Q on separate heap portions
    P -* Q      -- If P, then Q (magic wand)

Frame rule:
    {P} c {Q}
    ─────────────────
    {P * R} c {Q * R}
    
    R is preserved if c doesn't touch it
```

## Separation Logic for Security

```rust
// Ownership as separation
// x ↦ v * y ↦ w means x and y are separate

// Exclusive access
#[requires(file ↦ contents)]
#[ensures(file ↦ new_contents)]
fn write_exclusive(file: &mut File, new_contents: Bytes) { ... }

// Shared reading
#[requires(file ↦ contents)]
#[ensures(file ↦ contents)]  // Unchanged
fn read_shared(file: &File) -> Bytes { ... }
```

## TERAS Decision E-05

**INTEGRATE** separation logic concepts:
1. Ownership as separation
2. Borrow checking as separation
3. Permission accounting
4. Frame reasoning for modularity

### Architecture Decision ID: `TERAS-ARCH-E05-SEP-001`

---

# E-06: Model Checking

## Bounded Model Checking

```rust
// Model checking verifies all states up to bound

#[model_check(bound = 10)]
fn verify_protocol() {
    let mut state = initial_state();
    loop {
        let action = choose_action();
        state = transition(state, action);
        assert!(invariant_holds(&state));
    }
}
```

## Security Property Checking

```rust
// Verify security properties via model checking

#[security_property]
fn noninterference_check() {
    let high1 = symbolic_high();
    let high2 = symbolic_high();
    let low = symbolic_low();
    
    let out1 = program(high1, low);
    let out2 = program(high2, low);
    
    assert!(low_equivalent(out1, out2));
}
```

## TERAS Decision E-06

**SUPPORT** model checking:
1. Bounded verification for protocols
2. Security property checking
3. Integration with test framework
4. Counterexample generation

### Architecture Decision ID: `TERAS-ARCH-E06-MC-001`

---

# E-07: Theorem Proving

## Interactive Provers

```
Interactive Theorem Provers:
├── Coq: Dependent types, extraction
├── Isabelle/HOL: Higher-order logic
├── Lean: Modern, good automation
├── Agda: Dependently typed language
└── F*: Effect-oriented verification
```

## Verified Cryptography

```fstar
// F* verified crypto example

val aes_encrypt: 
    key:bytes{length key = 32} -> 
    plaintext:bytes{length plaintext <= max_size} ->
    Tot (cipher:bytes{length cipher = length plaintext + 16})

// Proof that encryption is injective
val encryption_injective:
    k:key -> p1:plaintext -> p2:plaintext ->
    Lemma (aes_encrypt k p1 = aes_encrypt k p2 ==> p1 = p2)
```

## TERAS Decision E-07

**SUPPORT** theorem proving:
1. Optional extraction from Coq/Lean
2. Verified crypto library support
3. Critical component verification
4. Proof witnesses for security

### Architecture Decision ID: `TERAS-ARCH-E07-TP-001`

---

# E-08: Verified Compilation

## Certified Compilation

```
Compiler Correctness:

For all programs P:
    If P compiles to M, then
    behavior(M) = behavior(P)

Or more precisely:
    observational_equivalence(P, M)
```

## CompCert Model

```
CompCert: Verified C compiler

Passes:
    C → Clight → C#minor → Cminor → CminorSel →
    RTL → LTL → Linear → Mach → Assembly

Each pass proven:
    ∀P. compile(P) = M → P ≃ M
```

## TERAS Compilation Verification

```rust
// TERAS compilation guarantees

// Type preservation
#[ensures(∀e. type_of(e) = type_of(compile(e)))]

// Effect preservation  
#[ensures(∀e. effects(e) = effects(compile(e)))]

// Security preservation
#[ensures(∀e. secure(e) => secure(compile(e)))]

// Noninterference preservation
#[ensures(∀P. noninterferent(P) => noninterferent(compile(P)))]
```

## TERAS Decision E-08

**TARGET** verified compilation:
1. Type preservation proof
2. Effect preservation proof
3. Security preservation proof
4. Consider CompCert backend for C output

### Architecture Decision ID: `TERAS-ARCH-E08-VC-001`

---

# E-09: Automated Verification

## SMT-Based Verification

```rust
// Generate SMT formulas for verification

// Function to verify
fn abs(x: i32) -> { r: i32 | r >= 0 } {
    if x < 0 { -x } else { x }
}

// Generated SMT (simplified)
// (declare-fun x () Int)
// (declare-fun r () Int)
// (assert (= r (ite (< x 0) (- x) x)))
// (assert (not (>= r 0)))
// (check-sat)  ; unsat means verified!
```

## Verification Condition Generation

```
VCGen for Hoare triples:

wp(skip, Q) = Q
wp(x := e, Q) = Q[x ↦ e]
wp(c1; c2, Q) = wp(c1, wp(c2, Q))
wp(if b then c1 else c2, Q) = (b ⇒ wp(c1, Q)) ∧ (¬b ⇒ wp(c2, Q))
wp(while b do c, Q) = I ∧ ∀.(I ∧ b ⇒ wp(c, I)) ∧ (I ∧ ¬b ⇒ Q)
```

## TERAS Decision E-09

**IMPLEMENT** automated verification:
1. SMT-based refinement checking
2. Automatic VC generation
3. Liquid-type inference
4. Push-button for decidable cases

### Architecture Decision ID: `TERAS-ARCH-E09-AUTO-001`

---

# E-10: Verification in Practice

## Practical Considerations

```
Verification in practice:

1. Incremental verification
   - Verify changed code only
   - Cache verification results

2. Modular verification
   - Verify components separately
   - Use contracts at boundaries

3. Prioritization
   - Critical code fully verified
   - Less critical: lighter checks

4. Developer experience
   - Clear error messages
   - IDE integration
   - Suggested fixes
```

## TERAS Verification Strategy

```
TERAS Verification Levels:

Level 0: Type Checking
    - Standard type safety
    - Effect tracking
    - Borrow checking
    
Level 1: Refinement Types
    - Bounds checking
    - Precondition validation
    - SMT-automated

Level 2: Contracts
    - Pre/post conditions
    - Invariants
    - May require hints

Level 3: Full Verification
    - Theorem proving
    - Complete specifications
    - For critical components

Default: Level 1 for all code
Required: Level 2 for security-critical
Optional: Level 3 for crypto/core
```

## TERAS Decision E-10

**ESTABLISH** verification strategy:
1. Tiered verification levels
2. Mandatory Level 1 for all code
3. Level 2 for security boundaries
4. Level 3 for cryptographic code

### Architecture Decision ID: `TERAS-ARCH-E10-STR-001`

---

# Domain E Summary

## Completed Sessions

| Session | Topic | Decision ID |
|---------|-------|-------------|
| E-01 | Verification Foundations | TERAS-ARCH-E01-VER-001 |
| E-02 | Refinement Types | TERAS-ARCH-E02-REF-001 |
| E-03 | Dependent Types | TERAS-ARCH-E03-DEP-001 |
| E-04 | Contracts | TERAS-ARCH-E04-CTR-001 |
| E-05 | Separation Logic | TERAS-ARCH-E05-SEP-001 |
| E-06 | Model Checking | TERAS-ARCH-E06-MC-001 |
| E-07 | Theorem Proving | TERAS-ARCH-E07-TP-001 |
| E-08 | Verified Compilation | TERAS-ARCH-E08-VC-001 |
| E-09 | Automated Verification | TERAS-ARCH-E09-AUTO-001 |
| E-10 | Practice | TERAS-ARCH-E10-STR-001 |

## Key Decisions

1. **Refinement types** as primary verification
2. **SMT-based automation** for decidable properties
3. **Tiered verification** levels
4. **Optional theorem proving** for critical code
5. **Verified compilation** as long-term goal

---

## Domain E: COMPLETE

**Total Documents: 10** (combined in this file)

Ready for Domain F: Memory Safety

---

*Research Track Output — Domain E: Formal Verification*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
