# RESEARCH_A14_CAPABILITY_TYPES_DECISION.md

## TERAS Research Track â€” Domain A: Type Theory
### Session A-14: Capability Types â€” Architecture Decision

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Architecture Decision Record
**Status:** ADOPTED
**Predecessor:** A-13 (Ownership Types)
**Successor:** A-15 (Staged Types)

---

# DECISION SUMMARY

**ADOPT: Austral-style linear capabilities as first-class types, integrated with Wyvern-style effect capabilities, ownership semantics (A-13), and region-bounded lifetimes (A-12) for TERAS-LANG authority control with zero runtime overhead.**

---

# PART I: CONTEXT AND REQUIREMENTS

## 1.1 Decision Drivers

### 1.1.1 TERAS Core Requirements

| Requirement | Source | Capability Implication |
|-------------|--------|----------------------|
| No ambient authority | D03 | All authority via capabilities |
| Confused deputy prevention | D08 | Capability passing enforces authority |
| Principle of least authority | D09 | Attenuation and minimal grants |
| Zero overhead | D38 | Static verification only |
| Formal verification | D02 | Sound capability system |

### 1.1.2 Integration Requirements

```
Must integrate with:
  A-04: Linear Types     - Linear capabilities
  A-11: Effect Types     - Capability effects
  A-12: Region Types     - Capability lifetimes
  A-13: Ownership Types  - Capability ownership
```

### 1.1.3 TERAS Product Security Requirements

| Product | Capability Need |
|---------|----------------|
| MENARA | Session caps, crypto key caps |
| GAPURA | Request processing caps, backend caps |
| ZIRAH | Process inspection caps, response caps |
| BENTENG | Camera caps, biometric caps |
| SANDI | Signing key caps, HSM access caps |

## 1.2 Constraints

```
Hard Constraints:
  C1: Zero runtime overhead (no dynamic capability checks)
  C2: No ambient authority (all authority from parameters)
  C3: Unforgeable capabilities (cannot create from nothing)
  C4: Attenuation support (can reduce, not amplify)
  C5: Integration with existing type decisions

Soft Constraints:
  S1: Explicit capability flow visible in types
  S2: Support for revocation patterns
  S3: Composable with effects and regions
  S4: Intuitive for security-conscious developers
```

---

# PART II: DECISION DETAILS

## 2.1 Adopted Capability Model

### 2.1.1 Core Principles

```
TERAS-LANG Capability Principles:

P1: Capabilities as Types
    cap<R, P> is a first-class type
    R = resource type, P = permission set
    
P2: No Ambient Authority
    All authority flows from function parameters
    No global capability access
    
P3: Unforgeability
    Capabilities only from:
    - Function parameters
    - Creation (with appropriate authority)
    - Attenuation (subset of existing)
    
P4: Attenuation
    Can restrict permissions: P â†’ P' where P' âŠ† P
    Cannot amplify: never P â†’ P' where P' âŠƒ P
    
P5: Static Verification
    All capability checks at compile time
    Zero runtime capability overhead
```

### 2.1.2 Capability Type Syntax

```
Capability Type Forms:

Basic Capability:
  cap<Resource, Permission>
  
Examples:
  cap<File, Read>           -- read-only file access
  cap<File, Read + Write>   -- read-write file access
  cap<Network, Connect>     -- network connection permission
  cap<Memory, Alloc>        -- memory allocation permission
  
With Linearity (A-04):
  lin cap<R, P>             -- linear (must use)
  aff cap<R, P>             -- affine (can drop)
  
With Ownership (A-13):
  owned cap<R, P>           -- owned capability
  &cap<R, P>                -- borrowed (shared)
  &mut cap<R, P>            -- borrowed (exclusive)
  
With Region (A-12):
  cap<R, P> at Ï            -- capability in region
```

### 2.1.3 Permission System

```
Permission Type Definition:

Permission Hierarchy:
  Full > {Read, Write, Execute, Grant, Revoke} > None

Permission Lattice:
           Full
         / | | \
     Read Write Exec Grant
         \ | | /
           None

Permission Operations:
  Pâ‚ + Pâ‚‚     -- union (Pâ‚ âˆª Pâ‚‚)
  Pâ‚ * Pâ‚‚     -- intersection (Pâ‚ âˆ© Pâ‚‚)
  Pâ‚ - Pâ‚‚     -- subtraction (Pâ‚ \ Pâ‚‚)
  Pâ‚ âŠ† Pâ‚‚     -- subset check
```

## 2.2 Capability Operations

### 2.2.1 Creation

```
Capability Creation:

// Creation requires higher authority
fn create_file_cap(
    fs: &cap<Filesystem, CreateFile>
) -> cap<File, Full> {
    fs.create_file()
}

// Type rule for creation
Î“ âŠ¢ c : cap<Sys, Create<R>>
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ create(c) : cap<R, Full>
```

### 2.2.2 Attenuation

```
Capability Attenuation:

// Explicit attenuation
fn attenuate<R, P, P'>(
    c: cap<R, P>
) -> cap<R, P'> 
where P' âŠ† P {
    // Zero cost, just type change
}

// Example usage
let full: cap<File, Full> = get_file();
let read_only: cap<File, Read> = attenuate(full);

// Type rule
Î“ âŠ¢ c : cap<R, P>    P' âŠ† P
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ attenuate(c) : cap<R, P'>
```

### 2.2.3 Usage

```
Capability Usage:

// Using a capability
fn read_file(c: &cap<File, Read>) -> String {
    c.read()  // Authorized by capability
}

// Effect annotation (Wyvern-style)
fn read_file(c: &cap<File, Read>) -> String 
  ! {File.Read} 
{
    c.read()
}

// Type rule
Î“ âŠ¢ c : cap<R, P>    use_op âˆˆ P
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ c.use_op() : Ï„ ! {R.use_op}
```

### 2.2.4 Transfer

```
Capability Transfer:

// Move semantics (default for owned)
fn transfer(c: owned cap<R, P>) -> owned cap<R, P> {
    c  // Ownership transferred
}

// Borrowing (temporary access)
fn borrow<'a>(c: &'a cap<R, P>) -> &'a cap<R, P> {
    c  // Reference, original retained
}
```

## 2.3 Entry Point Capabilities

### 2.3.1 Main Function Signature

```
Entry Point Design:

// All initial authority as parameters
fn main(
    console: cap<Console, All>,
    filesystem: cap<Filesystem, All>,
    network: cap<Network, All>,
    clock: cap<Clock, Read>,
    entropy: cap<Entropy, Read>
) -> ExitCode {
    // All authority comes from parameters
    // No global access possible
}

// TERAS product entry point
fn teras_main(
    console: cap<Console, Log>,
    config: cap<Config, Read>,
    crypto: cap<Crypto, All>,
    storage: cap<Storage, All>,
    audit: cap<Audit, Write>
) -> TerasResult {
    // Security-focused capability set
}
```

### 2.3.2 Capability Derivation

```
Deriving Sub-Capabilities:

fn main(fs: cap<Filesystem, All>) {
    // Derive read-only file cap
    let reader: cap<File, Read> = fs.open_read("data.txt");
    
    // Derive write-only file cap
    let writer: cap<File, Write> = fs.open_write("out.txt");
    
    // Cannot derive what we don't have
    // let exec: cap<File, Execute> = ...  // ERROR: no Execute
}
```

## 2.4 Integration Specifications

### 2.4.1 Linear Capability Integration (A-04)

```
Linear Capabilities:

// Must-use capabilities (critical resources)
lin cap<Transaction, Full>   -- must commit/abort
lin cap<Connection, Full>    -- must close
lin cap<Lock, Full>          -- must release

// Affine capabilities (can drop)
aff cap<File, Read>          -- can close implicitly
aff cap<Cache, Read>         -- can forget

// Type rules with linearity
Î“ âŠ¢ c : lin cap<R, P>    Î”, x : lin cap<R, P> âŠ¢ e : Ï„
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ— Î” âŠ¢ letcap x = c in e : Ï„

// Linear capability must be consumed
fn use_transaction(txn: lin cap<Transaction, Full>) {
    // Must call commit or abort
    txn.commit()  // Consumes txn
}
```

### 2.4.2 Effect Integration (A-11)

```
Capability Effects:

// Effect declaration from capability
effect FileEffect {
    Read : () â†’ String,
    Write : String â†’ (),
}

// Capability requires effect
fn process(f: cap<File, Read>) -> String 
  ! {FileEffect.Read} 
{
    f.read()
}

// Effect masking at capability boundary
fn confined() -> String ! {} {
    letcap f = open_file() in
        let result = f.read();  // ! {FileEffect.Read}
        close(f);
        result  // Only result escapes, effect masked
    end
}
```

### 2.4.3 Ownership Integration (A-13)

```
Capability Ownership:

// Owned capability (move semantics)
fn consume(c: owned cap<File, Full>) {
    let content = c.read();
    c.close();  // c consumed
}

// Borrowed capability (temporary access)
fn read_only(c: &cap<File, Read>) -> String {
    c.read()  // c not consumed
}

// Exclusive borrow for mutation
fn modify(c: &mut cap<File, Write>) {
    c.write("data");
}

// Ownership + Attenuation
fn safe_read(c: owned cap<File, Full>) -> String {
    let reader: &cap<File, Read> = &attenuate(c);
    reader.read()
    // c dropped at end
}
```

### 2.4.4 Region Integration (A-12)

```
Region-Scoped Capabilities:

// Capability lifetime bounded by region
letregion Ï in
    letcap f: cap<File, Full> at Ï = open("data.txt") in
        let content = f.read();
        content  // Escapes region
    end  // f revoked at region end
end

// Type with region
cap<File, Read> at Ï    -- file cap in region Ï
&'Ï cap<File, Read>     -- borrow scoped to region

// Bulk revocation via region
fn scoped_work(fs: &cap<Filesystem, All>) -> Result {
    letregion work_region in
        letcap c1 = open_at(fs, work_region, "a.txt") in
        letcap c2 = open_at(fs, work_region, "b.txt") in
            process(c1, c2)
        end end
    end  // Both c1 and c2 revoked
}
```

---

# PART III: DETAILED DESIGN

## 3.1 Capability Type System

### 3.1.1 Type Formation Rules

```
Capability Type Formation:

Resource Types:
  R ::= File | Network | Memory | Console | ...
        | Custom<name>

Permission Types:
  P ::= None | Read | Write | Execute | Grant
        | P + P | P * P | Full

Capability Types:
  Ï„_cap ::= cap<R, P>
          | lin cap<R, P>
          | aff cap<R, P>
          | cap<R, P> at Ï

Formation Rules:
  R resource    P permission
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (cap-form)
  cap<R, P> type
  
  R resource    P permission    Ï region
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (cap-region-form)
  cap<R, P> at Ï type
```

### 3.1.2 Subtyping Rules

```
Capability Subtyping:

Permission Subtyping:
  Pâ‚ âŠ† Pâ‚‚
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (cap-perm-sub)
  cap<R, Pâ‚‚> <: cap<R, Pâ‚>
  
  (contravariant in permission)

Linearity Subtyping:
  lin cap<R, P> <: aff cap<R, P>
  (linear can be used as affine)

Region Subtyping:
  Ïâ‚ âŠ‡ Ïâ‚‚    (Ïâ‚ outlives Ïâ‚‚)
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  cap<R, P> at Ïâ‚ <: cap<R, P> at Ïâ‚‚
```

### 3.1.3 Typing Rules

```
Core Capability Typing:

Variable:
  x : cap<R, P> âˆˆ Î“
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (cap-var)
  Î“ âŠ¢ x : cap<R, P>

Attenuation:
  Î“ âŠ¢ e : cap<R, P>    P' âŠ† P
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (cap-attenuate)
  Î“ âŠ¢ attenuate(e) : cap<R, P'>

Usage:
  Î“ âŠ¢ e : cap<R, P>    op âˆˆ P
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (cap-use)
  Î“ âŠ¢ e.op(args) : Ï„ ! {R.op}

Linear Usage:
  Î“ âŠ¢ c : lin cap<R, P>    Î”, x:lin cap<R,P> âŠ¢ e : Ï„
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ (cap-lin-let)
  Î“ âŠ— Î” âŠ¢ letcap x = c in e : Ï„
```

## 3.2 Permission System Details

### 3.2.1 Standard Permission Sets

```
TERAS Standard Permissions:

File Permissions:
  File.Read     -- read content
  File.Write    -- write content
  File.Execute  -- execute (if applicable)
  File.Delete   -- delete file
  File.Full     -- all of above

Network Permissions:
  Network.Connect  -- establish connection
  Network.Listen   -- accept connections
  Network.Send     -- send data
  Network.Receive  -- receive data
  Network.Full     -- all of above

Crypto Permissions:
  Crypto.Sign      -- create signatures
  Crypto.Verify    -- verify signatures
  Crypto.Encrypt   -- encrypt data
  Crypto.Decrypt   -- decrypt data
  Crypto.Full      -- all of above

Memory Permissions:
  Memory.Alloc     -- allocate
  Memory.Free      -- deallocate
  Memory.Read      -- read
  Memory.Write     -- write
  Memory.Full      -- all of above
```

### 3.2.2 Custom Permission Definition

```
Defining Custom Permissions:

// Domain-specific permissions
permission TERAS {
    ScanProcess,    -- scan a process
    Terminate,      -- terminate a process
    CollectEvidence -- forensic collection
}

// Capability with custom permission
cap<Process, TERAS.ScanProcess>

// Permission composition
cap<Process, TERAS.ScanProcess + TERAS.CollectEvidence>
```

## 3.3 Revocation Mechanisms

### 3.3.1 Region-Based Revocation

```
Bulk Revocation via Regions:

// All capabilities in region revoked at once
fn with_revocable<R, T>(
    factory: &cap<Factory, Create<R>>,
    f: fn(cap<R, Full>) -> T
) -> T {
    letregion revoke_region in
        letcap c: cap<R, Full> at revoke_region = 
            factory.create() in
            f(c)
        end
    end  // c revoked here
}
```

### 3.3.2 Proxy-Based Revocation

```
Revocable Capability Pattern:

struct Revocable<R, P> {
    inner: Option<cap<R, P>>,
    revoked: bool,
}

impl<R, P> Revocable<R, P> {
    fn use<T>(&self, f: fn(&cap<R, P>) -> T) -> Option<T> {
        if self.revoked {
            None
        } else {
            self.inner.as_ref().map(f)
        }
    }
    
    fn revoke(&mut self) {
        self.revoked = true;
        self.inner = None;
    }
}
```

---

# PART IV: TERAS PRODUCT APPLICATIONS

## 4.1 MENARA (Mobile Security)

```
MENARA Capability Architecture:

// Entry capabilities
fn menara_main(
    ui: cap<UI, All>,
    crypto: cap<Crypto, All>,
    secure_storage: cap<SecureStorage, All>,
    biometric: cap<Biometric, Capture + Match>,
    network: cap<Network, Connect + Send + Receive>
) -> Result {
    // Derive session capabilities
    let session_cap = create_session(
        &crypto, 
        &secure_storage
    );
    
    // Auth flow with minimal capabilities
    let auth_result = authenticate(
        &attenuate(biometric, Biometric.Match),
        &session_cap
    );
    
    ...
}

// Session capability (linear)
lin cap<Session, Active>

// Must explicitly end session
fn end_session(session: lin cap<Session, Active>) -> () {
    session.invalidate()  // Consumes session
}
```

## 4.2 GAPURA (Web Application Firewall)

```
GAPURA Capability Architecture:

// Request processing pipeline
fn process_request(
    req: cap<Request, Read>,
    backend: cap<Backend, Forward>,
    log: cap<Log, Write>
) -> cap<Response, Full> {
    // Validation with read-only
    let validated = validate(&req)?;
    
    // Forward requires Forward permission
    let response = backend.forward(validated)?;
    
    // Log with write-only
    log.write(&format!("Processed: {:?}", req));
    
    response
}

// Connection capability (linear, must close)
fn handle_connection(
    conn: lin cap<Connection, Full>
) -> Result {
    let request = conn.read_request()?;
    let response = process(request)?;
    conn.write_response(response)?;
    conn.close()  // Consumes conn
}
```

## 4.3 ZIRAH (Endpoint Detection & Response)

```
ZIRAH Capability Architecture:

// Privilege-separated scanning
fn scan_process(
    proc: cap<Process, Inspect>,  // Read-only
    mem: cap<Memory, Read>        // Read-only
) -> ScanResult {
    let state = proc.get_state();
    let regions = mem.read_regions(&proc);
    analyze(state, regions)
}

// Response requires elevated capability
fn respond_to_threat(
    proc: cap<Process, Terminate>,  // Elevated
    evidence: lin cap<Evidence, Collect>
) -> ResponseResult {
    let ev = evidence.capture();  // Consumes evidence cap
    proc.terminate()?;
    Ok(ResponseResult::new(ev))
}

// Capability grant for response
fn escalate_if_threat(
    scanner: cap<Process, Inspect>,
    responder: cap<Escalation, Grant>,
    result: &ScanResult
) -> Option<cap<Process, Terminate>> {
    if result.is_threat() {
        Some(responder.grant_terminate(&scanner))
    } else {
        None
    }
}
```

## 4.4 BENTENG (eKYC/Identity)

```
BENTENG Capability Architecture:

// Biometric isolation
fn verify_identity(
    camera: cap<Camera, Capture>,
    biometric: cap<Biometric, Process + Match>,
    document: cap<Document, Verify>,
    store: cap<TemplateStore, Read>
) -> VerificationResult {
    // Each stage gets minimal capability
    let image = camera.capture()?;
    
    let template = biometric.process(image)?;
    
    let match_result = biometric.match(
        &template, 
        &store.get_template()?
    )?;
    
    let doc_result = document.verify()?;
    
    combine_results(match_result, doc_result)
}

// Linear biometric data (must be cleared)
fn with_biometric<T>(
    bio: lin cap<BiometricData, Full>,
    f: fn(&cap<BiometricData, Read>) -> T
) -> T {
    let result = f(&attenuate(bio, Read));
    bio.secure_clear();  // Consumes bio
    result
}
```

## 4.5 SANDI (Digital Signatures)

```
SANDI Capability Architecture:

// Signing key capability (linear, unique)
lin uniq cap<SigningKey, Sign>

// Signing operation
fn sign_document(
    key: &uniq cap<SigningKey, Sign>,  // Borrowed unique
    doc: &[u8]
) -> Signature {
    key.sign(doc)
}

// Key destruction (consumes linear capability)
fn destroy_key(
    key: lin uniq cap<SigningKey, Full>
) -> () {
    key.secure_wipe();  // Consumes key
}

// HSM integration
fn hsm_sign(
    hsm: &cap<HSM, Access>,
    key_id: KeyId,
    message: &[u8]
) -> Signature {
    // HSM capability controls all key access
    hsm.sign(key_id, message)
}

// Certificate chain with borrowed capabilities
fn verify_chain(
    chain: &[cap<Certificate, Verify>],
    root: &cap<TrustAnchor, Verify>
) -> ChainResult {
    // All verify caps borrowed, not consumed
    verify_certificate_chain(chain, root)
}
```

---

# PART V: IMPLEMENTATION ROADMAP

## 5.1 Phase 1: Core Capabilities (Weeks 1-6)

```
Week 1-2: Capability Type System
  - cap<R, P> type implementation
  - Permission lattice
  - Basic typing rules
  
Week 3-4: Capability Operations
  - Attenuation
  - Usage checking
  - Effect annotation
  
Week 5-6: Entry Points
  - Main function capabilities
  - No ambient authority verification
  - Initial capability derivation
```

## 5.2 Phase 2: Integration (Weeks 7-12)

```
Week 7-8: Linear Integration (A-04)
  - lin cap<R, P>
  - Linear capability consumption
  - Must-use verification
  
Week 9-10: Ownership Integration (A-13)
  - owned cap<R, P>
  - Capability borrowing
  - Move semantics for capabilities
  
Week 11-12: Region Integration (A-12)
  - cap<R, P> at Ï
  - Region-bounded capabilities
  - Bulk revocation
```

## 5.3 Phase 3: Advanced Features (Weeks 13-18)

```
Week 13-14: Effect Integration (A-11)
  - Capability effects
  - Effect masking
  - Effect polymorphism
  
Week 15-16: Revocation Patterns
  - Region-based revocation
  - Proxy patterns
  - Membrane pattern
  
Week 17-18: Product Integration
  - TERAS product capability designs
  - Security validation
  - Performance testing
```

---

# PART VI: RATIONALE

## 6.1 Why Austral-Style Linear Capabilities?

```
Arguments For:

1. Zero Runtime Overhead
   - All checks at compile time
   - No dynamic capability verification
   - D38 compliance guaranteed

2. Strong Resource Guarantees
   - Linear capabilities ensure cleanup
   - Must-use prevents resource leaks
   - Matches TERAS security model

3. Clean Integration
   - Natural fit with A-04 linear types
   - Composable with A-13 ownership
   - Region-compatible (A-12)

4. No Ambient Authority
   - Security by design
   - All authority explicit
   - Confused deputy prevention

Arguments Against (Mitigated):

1. Learning Curve
   - Mitigated: Familiar to Rust developers
   - Mitigated: Good error messages

2. Verbosity
   - Mitigated: Inference where possible
   - Mitigated: Elision rules for common cases
```

## 6.2 Why Effect Integration?

```
Benefits of Wyvern-Style Effects:

1. Modular Reasoning
   - Effect signatures show capability use
   - Composition rules for effects
   
2. Effect Masking
   - Confine effects to capability scope
   - Clean module boundaries
   
3. Verification Support
   - Effects enable formal reasoning
   - Tractable verification
```

## 6.3 Alternatives Rejected

| Alternative | Reason for Rejection |
|-------------|---------------------|
| E-style dynamic | Runtime overhead (D38 violation) |
| Pony ref-caps only | Limited integration with effects |
| seL4 kernel caps | Wrong abstraction level |
| No capabilities | Cannot achieve POLA |

---

# PART VII: VERIFICATION

## 7.1 Decision Alignment Matrix

| Requirement | How Satisfied | Confidence |
|-------------|---------------|------------|
| D03 No Ambient Authority | Entry capabilities only | High |
| D08 Confused Deputy | Capability passing | High |
| D09 POLA | Attenuation | High |
| D38 Zero Overhead | Static verification | High |
| A-04 Linear Types | lin cap<R, P> | High |
| A-11 Effects | Capability effects | High |
| A-12 Regions | cap<R, P> at Ï | High |
| A-13 Ownership | owned cap<R, P> | High |

## 7.2 Risk Analysis

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Capability verbosity | Medium | Medium | Inference, elision |
| Integration complexity | Medium | High | Phased implementation |
| Permission explosion | Low | Medium | Standard permission sets |
| Revocation complexity | Medium | Medium | Region-based pattern |

## 7.3 Success Metrics

```
Quantitative:
  - 100% authority traceable to entry capabilities
  - 0% runtime capability overhead
  - <5% annotation overhead vs uncapability code
  
Qualitative:
  - Capability flow visible in type signatures
  - Revocation patterns implementable
  - Product security requirements met
```

---

# PART VIII: CONCLUSION

## 8.1 Decision Statement

**TERAS-LANG SHALL ADOPT Austral-style linear capabilities as first-class types (`cap<R, P>`), with Wyvern-style effect integration, ownership semantics, and region-bounded lifetimes, ensuring zero runtime overhead, no ambient authority, and complete integration with the TERAS type system.**

## 8.2 Key Commitments

1. **First-Class Capabilities**: `cap<R, P>` as type constructor
2. **Permission Lattice**: Hierarchical permission system
3. **No Ambient Authority**: All authority from parameters
4. **Attenuation**: Can reduce, never amplify permissions
5. **Linear Option**: `lin cap<R, P>` for must-use resources
6. **Effect Integration**: Capability effects for modular reasoning
7. **Region Integration**: `cap<R, P> at Ï` for lifetime bounding

## 8.3 Integration Summary

```
Capability Integration Map:

     A-04 Linear      A-11 Effects
         â”‚                 â”‚
         â–¼                 â–¼
    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
    â”‚   CAPABILITY TYPES      â”‚
    â”‚       (A-14)            â”‚
    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â–²                 â–²
         â”‚                 â”‚
    A-13 Ownership    A-12 Regions
```

---

## APPENDIX A: DECISION RECORD

| Field | Value |
|-------|-------|
| Decision ID | TERAS-A14-001 |
| Title | Capability Types Adoption |
| Status | ADOPTED |
| Date | 2026-01-03 |
| Deciders | TERAS Architecture Team |
| Supersedes | None |
| Related | A-04, A-11, A-12, A-13 |

---

**END OF DECISION DOCUMENT**

**Session A-14: COMPLETE**

**Next Session:** A-15 â€” Staged Types (Multi-Stage Programming)
