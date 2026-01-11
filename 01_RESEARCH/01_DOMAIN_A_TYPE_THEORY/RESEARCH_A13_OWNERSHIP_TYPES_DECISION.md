# RESEARCH_A13_OWNERSHIP_TYPES_DECISION.md

## TERAS Research Track — Domain A: Type Theory
### Session A-13: Ownership Types — Architecture Decision

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Architecture Decision Record
**Status:** ADOPTED
**Predecessor:** A-12 (Region Types - Linear Regions)
**Successor:** A-14 (Capability Types)

---

# DECISION SUMMARY

**ADOPT: Rust-style ownership with Mezzo-style explicit permissions, integrated with linear types (A-04), uniqueness types (A-06), and region types (A-12) for TERAS-LANG memory safety and resource management.**

---

# PART I: CONTEXT AND REQUIREMENTS

## 1.1 Decision Drivers

### 1.1.1 TERAS Core Requirements

| Requirement | Source | Ownership Implication |
|-------------|--------|----------------------|
| Memory safety | D01 | Complete static verification |
| Zero overhead | D38 | No runtime checks |
| Formal verification | D02 | Sound type system |
| Concurrency safety | D14 | Data race freedom |
| Resource management | D07 | Deterministic cleanup |

### 1.1.2 Integration Requirements

```
Must integrate with:
  A-04: Linear Types     - Ownership ≈ affine types
  A-06: Uniqueness Types - Exclusive access
  A-07: Session Types    - Protocol resources
  A-08: Refinement Types - Ownership predicates
  A-12: Region Types     - Lifetime scoping
```

### 1.1.3 TERAS Product Requirements

| Product | Ownership Need |
|---------|----------------|
| MENARA | Session credentials, crypto keys |
| GAPURA | Request buffers, connection handles |
| ZIRAH | Process handles, memory snapshots |
| BENTENG | Biometric data, document images |
| SANDI | Signing keys, certificate chains |

## 1.2 Constraints

```
Hard Constraints:
  C1: Zero runtime overhead for ownership checks
  C2: Static verification at compile time only
  C3: Deterministic resource deallocation
  C4: Data race freedom for concurrent code
  C5: Integration with existing type system decisions

Soft Constraints:
  S1: Familiar syntax for Rust developers
  S2: Explicit annotation when needed
  S3: Good error messages for ownership violations
  S4: Composable with other type features
```

---

# PART II: DECISION DETAILS

## 2.1 Adopted Ownership Model

### 2.1.1 Core Principles

```
TERAS-LANG Ownership Principles:

P1: Single Ownership
    Every value has exactly one owner at any time
    
P2: Move Semantics
    Assignment transfers ownership (move by default)
    
P3: Scope-Based Cleanup
    Values dropped when owner scope ends
    
P4: Borrowing for Sharing
    Temporary access via immutable/mutable borrows
    
P5: Static Verification
    All ownership verified at compile time
```

### 2.1.2 Ownership Kinds

```
TERAS-LANG Ownership Taxonomy:

owned T       -- Affine ownership (can drop)
  - Auto-cleanup when scope ends
  - Move on assignment
  - Can be explicitly dropped
  
lin owned T   -- Linear ownership (must consume)
  - Must be explicitly consumed
  - Cannot drop implicitly
  - For critical resources
  
uniq owned T  -- Unique ownership (no aliases ever)
  - Combines uniqueness (A-06) with ownership
  - Strongest guarantee
  - Required for secure key material
  
shared<T>     -- Reference-counted ownership
  - Multiple owners via counting
  - Last owner triggers cleanup
  - Thread-safe via Arc semantics
```

### 2.1.3 Borrowing Rules

```
TERAS-LANG Borrowing:

Rule 1: Shared XOR Mutable
  At any time, either:
    - Any number of immutable borrows (&T)
    - Exactly one mutable borrow (&mut T)
  Never both simultaneously

Rule 2: Lifetime Constraint
  Borrows cannot outlive the borrowed value
  Enforced via region integration (A-12)

Rule 3: Borrow Linearity
  &T     is duplicable (can be copied)
  &mut T is linear (exactly one reference)

Syntax:
  &x        -- immutable borrow
  &mut x    -- mutable borrow
  &'ρ x     -- borrow with explicit lifetime
  &'ρ mut x -- mutable borrow with lifetime
```

## 2.2 Type Syntax

### 2.2.1 Ownership Type Forms

```
Ownership Types:

Primary Forms:
  owned T                 -- owned value
  &T                      -- immutable borrow
  &mut T                  -- mutable borrow
  shared<T>               -- reference counted

With Qualifiers:
  lin owned T             -- linear owned
  uniq owned T            -- unique owned
  lin &T                  -- linear borrow (unusual)
  
With Lifetimes:
  &'a T                   -- borrow with lifetime 'a
  &'a mut T               -- mutable with lifetime 'a
  owned T at ρ            -- owned in region ρ

Full Form:
  [lin|aff] [uniq] owned T [at ρ] [! E]
```

### 2.2.2 Function Signatures

```
Function Ownership Patterns:

// Takes ownership, returns ownership
fn consume(x: owned Buffer) -> owned Result

// Borrows immutably
fn read(x: &Data) -> Value

// Borrows mutably  
fn modify(x: &mut Data) -> ()

// Takes ownership of linear resource
fn use_key(k: lin owned Key) -> Signature

// Returns borrow tied to input lifetime
fn first<'a>(x: &'a [T]) -> &'a T

// Explicit permission (Mezzo-style)
fn process<P: Permission>(x: P::Ref<Buffer>) -> Result
```

## 2.3 Permission System (Mezzo-inspired Enhancement)

### 2.3.1 Explicit Permissions

```
TERAS-LANG Permissions:

Permission Kinds:
  Read<T>      -- can read T
  Write<T>     -- can write T  
  Own<T>       -- owns T
  Consume<T>   -- will consume T

Permission Syntax:
  fn f(x: T @ Read)     -- read permission
  fn g(x: T @ Write)    -- write permission
  fn h(x: T @ Own)      -- ownership
  fn i(x: T @ Consume)  -- consuming

Default Inference:
  &T        ⟹  T @ Read
  &mut T    ⟹  T @ Write
  owned T   ⟹  T @ Own
```

### 2.3.2 Permission Composition

```
Permission Algebra:

Read ⊆ Write ⊆ Own
Consume ⟂ Read  (cannot read consumed)

Splitting:
  Own<T> → Read<T> ⊗ Write<T>
  
Merging:
  Read<T> ⊗ Write<T> → Own<T>
  (only if same value)

Transfer:
  Own<T> ⊸ Consume<T>  (consuming transfer)
```

## 2.4 Integration Specifications

### 2.4.1 Integration with Linear Types (A-04)

```
Ownership-Linearity Mapping:

owned T      ≡  aff T + Drop
lin owned T  ≡  lin T + explicit_consume
&T           ≡  duplicable ref
&mut T       ≡  lin ref (exclusive)

Combined Typing Rules:

Γ ⊢ e : owned T    Δ, x : owned T ⊢ e' : τ
───────────────────────────────────────────  (let-owned)
        Γ, Δ ⊢ let x = e in e' : τ

Γ ⊢ e : lin owned T    Δ, x : lin owned T ⊢ e' : τ
───────────────────────────────────────────────────  (let-lin-owned)
        Γ ⊗ Δ ⊢ let x = e in e' : τ
```

### 2.4.2 Integration with Uniqueness (A-06)

```
Ownership-Uniqueness Interaction:

uniq owned T:
  - Unique (no aliases) + Owned (auto-cleanup)
  - Strongest guarantee
  - Required for secure resources

shared owned T:
  - Multiple ownership via ref-counting
  - Cannot be unique
  - Thread-safe (Arc semantics)

Rules:
  uniq owned T <: owned T      (subsumption)
  owned T ⊥ shared<T>          (incompatible)
  uniq owned T → shared<T>     (forbidden)
```

### 2.4.3 Integration with Regions (A-12)

```
Ownership-Region Integration:

owned T at ρ:
  - Value owned AND in region ρ
  - Cleanup: min(owner scope, region end)
  
&'ρ T:
  - Borrow from region ρ
  - Lifetime bounded by region

Deallocation Priority:
  1. Explicit drop
  2. Owner scope end
  3. Region deallocation
  (whichever comes first)

Type Rules:
  Γ ⊢ e : owned T at ρ    ρ ∈ Γ
  ────────────────────────────────
  Γ ⊢ &e : &'ρ T

  cap : lin Cap<ρ>    Γ ⊢ e : owned T at ρ
  ─────────────────────────────────────────
  Γ ⊢ drop(e, cap) : () ! {Free<ρ>}
```

### 2.4.4 Integration with Effects (A-11)

```
Ownership Effects:

Move<T>     -- ownership transfer effect
Drop<T>     -- destruction effect
Clone<T>    -- duplication effect
Borrow<T>   -- borrow creation effect

Effect Tracking:
  fn consume(x: owned T) -> R ! {Drop<T>}
  fn clone(x: &T) -> owned T ! {Clone<T>}  // T: Clone
  fn transfer(x: owned T) -> owned T ! {Move<T>}

Effect Composition:
  Γ ⊢ e : owned T ! E₁    Δ ⊢ e' : τ ! E₂
  ────────────────────────────────────────
  Γ, Δ ⊢ let _ = e in e' : τ ! E₁ ∪ E₂ ∪ {Drop<T>}
```

---

# PART III: DETAILED DESIGN

## 3.1 Borrow Checker Specification

### 3.1.1 Dataflow Analysis

```
Borrow Checker Algorithm:

Phase 1: Collect Borrows
  For each borrow expression &x or &mut x:
    - Record borrow point
    - Determine lifetime (region)
    - Track mutability

Phase 2: Compute Liveness
  For each variable:
    - Compute live ranges (NLL-style)
    - Identify last use point
    - Allow lifetime to end at last use

Phase 3: Check Conflicts
  For each point in program:
    - If mutable borrow active:
        no other borrows allowed
    - If shared borrows active:
        no mutable borrows allowed
    - If moving:
        no active borrows allowed

Phase 4: Verify Lifetimes
  For each borrow:
    - Verify borrow ⊆ borrowed value's lifetime
    - Verify region constraints satisfied
```

### 3.1.2 Error Messages

```
Ownership Error Categories:

E001: Use After Move
  "value `x` used after move"
  Help: consider cloning or borrowing
  
E002: Borrow of Moved Value
  "cannot borrow `x` because it was moved"
  Help: move happened at line N
  
E003: Mutable Borrow Conflict
  "cannot borrow `x` as mutable, already borrowed as immutable"
  Help: immutable borrow used at line N
  
E004: Double Mutable Borrow
  "cannot borrow `x` as mutable more than once"
  Help: first mutable borrow at line N
  
E005: Borrow Outlives Value
  "borrowed value does not live long enough"
  Help: value dropped at line N, borrow used at line M
  
E006: Linear Value Not Consumed
  "linear value `x` must be explicitly consumed"
  Help: use `consume(x)` or pass to consuming function
```

## 3.2 Drop Semantics

### 3.2.1 Drop Trait

```
Drop Protocol:

trait Drop {
    fn drop(&mut self);
}

Drop Invocation Order:
  1. Explicit drop() call
  2. Scope exit (reverse declaration order)
  3. Region deallocation
  
Custom Drop:
  impl Drop for SecretKey {
      fn drop(&mut self) {
          secure_wipe(self.data);  // Zero memory
      }
  }
  
  impl Drop for FileHandle {
      fn drop(&mut self) {
          close_file(self.fd);     // Release resource
      }
  }
```

### 3.2.2 Drop Ordering

```
Drop Order Guarantees:

struct Container {
    first: A,
    second: B,
    third: C,
}

// Drop order: third, second, first
// (reverse of field declaration)

{
    let x = A::new();
    let y = B::new();
    let z = C::new();
}
// Drop order: z, y, x
// (reverse of variable declaration)
```

## 3.3 Interior Mutability

### 3.3.1 Controlled Escape Hatches

```
Interior Mutability Types:

Cell<T>: T where T: Copy
  - get/set without &mut
  - Only for Copy types
  - No runtime cost
  
RefCell<T>:
  - Runtime borrow checking
  - borrow() -> Ref<T>
  - borrow_mut() -> RefMut<T>
  - Panics on violation
  
Mutex<T>:
  - Thread-safe mutation
  - lock() -> MutexGuard<T>
  - Blocks on contention
  
RwLock<T>:
  - Multiple readers OR one writer
  - read() -> RwLockReadGuard<T>
  - write() -> RwLockWriteGuard<T>
```

### 3.3.2 Security Constraints

```
Interior Mutability Restrictions for TERAS:

Secret<T>: NO interior mutability
  - Prevent timing side-channels
  - Must use move semantics only
  
Key<T>: NO Cell/RefCell
  - Only Mutex for concurrent access
  - Secure zeroization on unlock failure
  
Tainted<T>: NO interior mutability
  - Prevent bypassing sanitization
  - Must explicitly transform
```

---

# PART IV: TERAS PRODUCT APPLICATIONS

## 4.1 MENARA (Mobile Security)

```
Ownership Patterns:

// Session credential with linear ownership
fn authenticate(
    cred: lin owned Credential
) -> Result<owned Session, Error> {
    // cred must be consumed by verify
    let result = verify(cred)?;
    Ok(Session::new(result))
}

// Crypto key with unique ownership
fn encrypt(
    key: &uniq owned EncryptionKey,
    data: &[u8]
) -> owned Ciphertext {
    // key borrowed immutably, not consumed
    key.encrypt(data)
}

// Session with owned lifetime
struct Session {
    token: owned Token,
    key: uniq owned SessionKey,
    expires: Timestamp,
}

impl Drop for Session {
    fn drop(&mut self) {
        secure_wipe(&mut self.key);
        invalidate_token(&self.token);
    }
}
```

## 4.2 GAPURA (Web Application Firewall)

```
Ownership Patterns:

// Request processing with ownership transfer
fn process_request(
    req: owned Request
) -> owned Response ! {IO, Log} {
    // Ownership ensures request processed once
    let validated = validate(req)?;
    let sanitized = sanitize(validated)?;
    route(sanitized)
}

// Connection handle with exclusive ownership
struct Connection {
    socket: uniq owned Socket,
    buffer: owned Buffer,
}

// Borrow for reading (shared)
fn read_request(conn: &Connection) -> &[u8] {
    &conn.buffer
}

// Borrow for writing (exclusive)
fn write_response(
    conn: &mut Connection, 
    resp: &Response
) -> Result<(), IoError> {
    conn.socket.write(resp.as_bytes())
}
```

## 4.3 ZIRAH (Endpoint Detection & Response)

```
Ownership Patterns:

// Process analysis with snapshot ownership
fn analyze_process(
    snapshot: owned ProcessSnapshot
) -> owned AnalysisResult {
    // snapshot consumed during analysis
    let memory = extract_memory(&snapshot);
    let threads = extract_threads(&snapshot);
    analyze(memory, threads)
}

// Evidence chain with linear ownership
fn collect_evidence(
    process: &Process
) -> lin owned Evidence {
    // Linear: must be explicitly handled
    let evidence = Evidence::capture(process);
    evidence  // Caller must consume
}

// Handle evidence (consuming)
fn store_evidence(
    evidence: lin owned Evidence,
    storage: &mut EvidenceStore
) -> StorageReceipt {
    // Consumes evidence, returns receipt
    storage.store(evidence)
}
```

## 4.4 BENTENG (eKYC/Identity)

```
Ownership Patterns:

// Biometric data with secure ownership
struct BiometricCapture {
    image: uniq owned SecureBuffer,
    template: uniq owned BiometricTemplate,
}

impl Drop for BiometricCapture {
    fn drop(&mut self) {
        secure_wipe(&mut self.image);
        secure_wipe(&mut self.template);
    }
}

// Document verification consuming document
fn verify_document(
    doc: lin owned DocumentImage
) -> Result<owned VerificationResult, Error> {
    // doc must be consumed
    let extracted = extract_data(doc)?;
    let verified = verify_authenticity(&extracted)?;
    Ok(VerificationResult::new(verified))
}

// Face match with borrowed references
fn match_faces(
    captured: &BiometricTemplate,
    stored: &BiometricTemplate
) -> MatchScore {
    // Both borrowed, not consumed
    compare_templates(captured, stored)
}
```

## 4.5 SANDI (Digital Signatures)

```
Ownership Patterns:

// Signing key with unique linear ownership
fn generate_key() -> lin uniq owned SigningKey {
    // Must be consumed, no aliases possible
    let key = SigningKey::generate();
    key
}

// Signing consumes key temporarily via exclusive borrow
fn sign(
    key: &uniq owned SigningKey,
    message: &[u8]
) -> owned Signature {
    // Exclusive borrow prevents concurrent signing
    key.sign(message)
}

// Key destruction (consuming)
fn destroy_key(key: lin uniq owned SigningKey) {
    // Explicit consumption with secure wipe
    // drop impl handles secure zeroization
    drop(key)
}

// Certificate chain with owned references
struct CertificateChain {
    leaf: owned Certificate,
    intermediates: owned Vec<Certificate>,
    root: &'static Certificate,  // Static lifetime
}
```

---

# PART V: IMPLEMENTATION ROADMAP

## 5.1 Phase 1: Core Ownership (Weeks 1-8)

```
Week 1-2: Basic Ownership
  - owned T type implementation
  - Move semantics
  - Basic drop support
  
Week 3-4: Borrowing
  - &T immutable borrows
  - &mut T mutable borrows
  - Basic lifetime inference
  
Week 5-6: Borrow Checker
  - Conflict detection
  - NLL dataflow analysis
  - Error reporting
  
Week 7-8: Integration Testing
  - Ownership-linearity interaction
  - Region integration
  - Comprehensive test suite
```

## 5.2 Phase 2: Advanced Features (Weeks 9-14)

```
Week 9-10: Lifetime Annotations
  - Explicit lifetimes <'a>
  - Lifetime elision rules
  - Lifetime bounds
  
Week 11-12: Interior Mutability
  - Cell<T> implementation
  - RefCell<T> with checks
  - Mutex<T>/RwLock<T>
  
Week 13-14: Permissions (Optional)
  - Explicit permission syntax
  - Permission inference
  - Permission composition
```

## 5.3 Phase 3: Security Extensions (Weeks 15-18)

```
Week 15-16: Secure Drop
  - Secure zeroization
  - Drop ordering guarantees
  - Panic safety
  
Week 17-18: Product Integration
  - MENARA patterns
  - GAPURA patterns
  - ZIRAH/BENTENG/SANDI patterns
```

---

# PART VI: RATIONALE

## 6.1 Why Rust-Style Ownership?

```
Arguments For:

1. Proven at Scale
   - Mozilla Firefox components
   - AWS infrastructure
   - Linux kernel modules
   - Thousands of production applications

2. Zero Runtime Overhead
   - All checks at compile time
   - No reference counting
   - No garbage collection
   
3. Complete Memory Safety
   - No use-after-free
   - No double-free
   - No data races
   - No null pointer dereference

4. Developer Familiarity
   - Largest modern safe systems language
   - Extensive documentation
   - Active community

Arguments Against (Mitigated):

1. Learning Curve
   - Mitigated: Good error messages
   - Mitigated: Familiar to Rust devs
   
2. Borrow Checker Frustration
   - Mitigated: NLL improvements
   - Mitigated: Interior mutability escapes
   
3. Limited Flexibility
   - Mitigated: Mezzo-style explicit permissions
   - Mitigated: RefCell for dynamic borrowing
```

## 6.2 Why Add Explicit Permissions?

```
Benefits of Mezzo-Style Permissions:

1. Documentation Value
   fn f(x: T @ Read)  -- clearly read-only
   fn g(x: T @ Write) -- clearly mutating
   
2. Fine-Grained Control
   Split ownership into read/write
   Useful for capability patterns
   
3. Theoretical Clarity
   Permission algebra well-defined
   Easier formal verification
   
4. Future Extension Point
   Capability systems (A-14)
   Information flow (security labels)
```

## 6.3 Alternative Approaches Rejected

| Alternative | Reason for Rejection |
|-------------|---------------------|
| Vale generational refs | Runtime overhead (D38 violation) |
| Mezzo-only | Not production-proven |
| Cyclone regions only | No ownership semantics |
| GC-based | Runtime overhead, non-deterministic |
| Manual memory | Unsafe, verification burden |

---

# PART VII: VERIFICATION

## 7.1 Decision Alignment Matrix

| Requirement | How Satisfied | Confidence |
|-------------|---------------|------------|
| D01 Memory Safety | Ownership + borrowing | High |
| D02 Formal Foundation | Affine types + proofs | High |
| D38 Zero Overhead | Compile-time only | High |
| D14 Concurrency | Send/Sync + &mut exclusivity | High |
| A-04 Linear Types | owned ≡ affine | High |
| A-06 Uniqueness | uniq owned T | High |
| A-12 Regions | Lifetime integration | High |

## 7.2 Risk Analysis

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Borrow checker too restrictive | Medium | Medium | Interior mutability, NLL |
| Permission overhead | Low | Low | Optional annotations |
| Integration complexity | Medium | High | Phased implementation |
| Learning curve | Medium | Medium | Good error messages |

## 7.3 Success Metrics

```
Quantitative Metrics:
  - 100% memory safety (no UAF, double-free, races)
  - 0% runtime overhead for ownership checks
  - <5% compile time increase vs no ownership
  - <10% annotation overhead vs Rust

Qualitative Metrics:
  - Developers find ownership intuitive
  - Error messages actionable
  - Security properties verifiable
```

---

# PART VIII: CONCLUSION

## 8.1 Decision Statement

**TERAS-LANG SHALL ADOPT Rust-style ownership with move semantics, borrowing rules, and lifetime tracking, enhanced with optional Mezzo-style explicit permissions, integrated with linear types (A-04), uniqueness types (A-06), and region types (A-12) for complete memory safety with zero runtime overhead.**

## 8.2 Key Commitments

1. **Move Semantics**: Default ownership transfer on assignment
2. **Borrowing Rules**: Shared XOR mutable at all times
3. **Static Verification**: All ownership checked at compile time
4. **Zero Overhead**: No runtime ownership tracking
5. **Deterministic Cleanup**: Drop at scope exit
6. **Linear Integration**: owned ≡ aff T + Drop
7. **Region Integration**: Lifetimes as region references

## 8.3 Integration Summary

```
Ownership Integration Map:

        A-04 Linear Types
              │
              ▼
         ┌────────────┐
A-06 ───▶│ OWNERSHIP  │◀─── A-12 Regions
Unique   │   TYPES    │     Lifetimes
         │  (A-13)    │
         └────────────┘
              │
              ▼
        A-14 Capability Types
```

---

## APPENDIX A: DECISION RECORD

| Field | Value |
|-------|-------|
| Decision ID | TERAS-A13-001 |
| Title | Ownership Types Adoption |
| Status | ADOPTED |
| Date | 2026-01-03 |
| Deciders | TERAS Architecture Team |
| Supersedes | None |
| Related | A-04, A-06, A-11, A-12 |

---

**END OF DECISION DOCUMENT**

**Session A-13: COMPLETE**

**Next Session:** A-14 — Capability Types
