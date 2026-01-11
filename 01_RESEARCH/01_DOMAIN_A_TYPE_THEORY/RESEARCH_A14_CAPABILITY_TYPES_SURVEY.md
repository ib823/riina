# RESEARCH_A14_CAPABILITY_TYPES_SURVEY.md

## TERAS Research Track — Domain A: Type Theory
### Session A-14: Capability Types

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research
**Predecessor:** A-13 (Ownership Types)
**Successor:** A-15 (Staged Types)

---

# PART I: FOUNDATIONS OF CAPABILITY-BASED SECURITY

## 1.1 Historical Development

### 1.1.1 Origins: Dennis & Van Horn (1966)

The capability concept originated in early operating systems research:

```
Original Capability Concept:

Dennis & Van Horn "Programming Semantics for 
Multiprogrammed Computations" (1966)

Capability = Token granting access rights to resource
Key Properties:
  - Unforgeable (cannot create from nothing)
  - Transferable (can be passed between domains)
  - Attenuable (can restrict but not amplify)
  - Revocable (access can be withdrawn)

Early Systems:
  - CAL-TSS (1968)
  - CAP Computer (Cambridge, 1970)
  - Hydra (CMU, 1974)
  - KeyKOS (1983)
```

### 1.1.2 Object-Capability Model

The object-capability (ocap) model unified OOP with capabilities:

```
Object-Capability Principles (Mark Miller, 2003):

1. Reference as Capability
   Object reference = authority to invoke methods
   No global mutable state
   
2. Capability Rules:
   - Can only use capabilities you hold
   - Can only get capabilities by:
     a) Creation (creating new object)
     b) Introduction (someone passes you one)
     c) Initial endowment (startup capabilities)
   
3. Principle of Least Authority (POLA)
   Grant only capabilities needed for task
   
4. Encapsulation
   Private state protected by capability boundary
```

### 1.1.3 Language-Based Capabilities

Moving capabilities into the type system:

```
Timeline:

1966: Dennis & Van Horn - OS capabilities
1974: Hydra - Capability OS
1988: Emerald - Mobile objects with capabilities
1998: E Language - Pure object-capabilities
2001: Joe-E - Capability-safe Java subset
2006: Caja - JavaScript confinement
2015: Pony - Reference capabilities
2017: Wyvern - Capability-safe effects
2021: Austral - Linear capabilities
2024: Various - Capability-enhanced Rust
```

## 1.2 Core Concepts

### 1.2.1 What is a Capability Type?

```
Capability Type Definition:

A capability type is a type that:
1. Represents authority to perform some operation
2. Cannot be forged (created from nothing)
3. Can be passed between program components
4. Can be restricted (attenuated)

Capability ≈ Unforgeable + Transferable + Authority

Type System Encoding:
  cap<R, P>   -- capability for resource R with permission P
  
  Examples:
    cap<File, Read>     -- can read file
    cap<Socket, Write>  -- can write socket
    cap<Memory, Alloc>  -- can allocate memory
```

### 1.2.2 Capability vs Access Control

| Property | Capabilities | ACLs (Access Control Lists) |
|----------|--------------|----------------------------|
| Check point | Reference site | Resource site |
| Ambient authority | No | Yes |
| Delegation | Direct transfer | Requires permission |
| Revocation | Indirect (proxy) | Direct (modify list) |
| Confused deputy | Prevented | Vulnerable |

### 1.2.3 Confused Deputy Problem

```
Confused Deputy (Hardy, 1988):

Scenario:
  Compiler needs to write output file
  User asks to compile program
  User specifies output path as billing file
  Compiler writes to billing file (has authority)
  User's attack succeeds
  
With ACLs:
  Compiler has write access to billing file
  User doesn't, but compiler acts on user's behalf
  Compiler is "confused" about whose authority to use
  
With Capabilities:
  Compiler only uses capabilities passed by user
  User cannot pass billing file capability
  Attack prevented by design
```

## 1.3 Taxonomy of Capability Systems

### 1.3.1 OS-Level Capabilities

```
Operating System Capabilities:

seL4:
  - Formally verified microkernel
  - Capabilities for all kernel resources
  - CNode (capability space)
  - Derivation tree for revocation
  
EROS/CapROS/seL4:
  - Persistent capabilities
  - Keyed capabilities
  - Checkpoint/restart
  
Capsicum (FreeBSD/Linux):
  - Capability mode for sandboxing
  - cap_rights_t for file descriptors
  - Practical Unix integration
  
Fuchsia (Zircon):
  - Handle = capability
  - Rights bits on handles
  - No ambient authority
```

### 1.3.2 Language-Level Capabilities

```
Language Capability Systems:

E Language:
  - Pure object-capability
  - Promise pipelining
  - Eventual send (!)
  - Capability patterns (sealer/unsealer)
  
Pony:
  - Reference capabilities (iso, val, ref, box, tag, trn)
  - Deny capabilities for concurrency
  - Type system prevents data races
  
Wyvern:
  - Effect system with capabilities
  - Resource types
  - Capability-safe effects
  
Austral:
  - Linear types for capabilities
  - No ambient authority
  - Systems programming focus
```

---

# PART II: DETAILED SYSTEM ANALYSIS

## 2.1 E Language

### 2.1.1 Overview

E is a pure object-capability language designed by Mark Miller:

```
E Language Key Features:

Pure Object-Capability:
  - No global mutable state
  - All authority via object references
  - No reflection to bypass encapsulation
  
Distributed Objects:
  - Transparent distribution
  - Promise pipelining
  - Eventual send operator (!)
  
Security Patterns:
  - Sealer/unsealer (encryption as capability)
  - Caretaker (revocable proxy)
  - Membrane (complete boundary)
```

### 2.1.2 Capability Patterns in E

```e
# Sealer/Unsealer Pattern
def makeBrandPair() {
    def [sealer, unsealer] := makeBrand()
    
    # Seal a value (returns opaque sealed box)
    def sealed := sealer.seal(sensitiveData)
    
    # Only matching unsealer can extract
    def data := unsealer.unseal(sealed)
}

# Caretaker Pattern (Revocable Forwarder)
def makeCaretaker(target) {
    var revoked := false
    
    def caretaker {
        match [verb, args] {
            if (revoked) { throw("Revoked") }
            E.call(target, verb, args)
        }
    }
    
    def revoker {
        to revoke() { revoked := true }
    }
    
    [caretaker, revoker]
}

# Membrane Pattern (Complete Boundary)
def makeMembrane() {
    def wrapped := [].asMap()
    
    def wrap(obj) {
        if (obj == null) { return null }
        if (wrapped.contains(obj)) { return wrapped[obj] }
        
        def proxy {
            match [verb, args] {
                def wrappedArgs := args.map(wrap)
                def result := E.call(obj, verb, wrappedArgs)
                wrap(result)
            }
        }
        wrapped[obj] := proxy
        proxy
    }
    
    wrap
}
```

### 2.1.3 Promise Pipelining

```e
# Without pipelining: 3 round trips
def a := remoteObj.method1()
when (a) -> {
    def b := a.method2()
    when (b) -> {
        def c := b.method3()
        # use c
    }
}

# With pipelining: 1 round trip
def a := remoteObj <- method1()
def b := a <- method2()
def c := b <- method3()
when (c) -> {
    # use c
}
# All messages sent together, results pipelined
```

## 2.2 Pony Reference Capabilities

### 2.2.1 Reference Capability System

Pony uses reference capabilities for safe concurrency:

```
Pony Reference Capabilities:

iso (isolated):
  - No other references exist
  - Can be sent to other actors
  - Mutable
  
val (value):
  - Immutable
  - Can be shared freely
  - Safe to read concurrently
  
ref (reference):
  - Mutable
  - Only one actor can hold refs
  - Cannot be sent between actors
  
box (box):
  - Read-only view
  - May be mutable elsewhere
  - Locally immutable
  
tag (tag):
  - Identity only
  - Cannot read or write
  - Can compare identity
  
trn (transition):
  - Write-unique, multiple readers
  - Can become val
```

### 2.2.2 Capability Subtyping

```
Pony Capability Subtyping Lattice:

          iso
         /   \
       trn   val
         \   /
          ref
           |
          box
           |
          tag

Subtyping Rules:
  iso <: trn
  iso <: val  
  trn <: ref
  val <: ref (contravariant)
  ref <: box
  box <: tag
```

### 2.2.3 Viewpoint Adaptation

```pony
// Viewpoint adaptation: what capability do we see 
// when accessing field through reference?

class Data
  var field: String iso

actor Main
  var data: Data iso
  
  // Accessing data.field through iso reference:
  // iso->iso = iso (field is isolated)
  
  var data2: Data ref
  // ref->iso = tag (cannot alias isolated through shared ref)
  
// Adaptation table:
//       | iso | trn | ref | val | box | tag
// ------+-----+-----+-----+-----+-----+----
// iso   | iso | trn | ref | val | box | tag
// trn   | iso | trn | box | val | box | tag
// ref   | iso | trn | ref | val | box | tag
// val   | val | val | val | val | val | tag
// box   | tag | tag | tag | val | box | tag
// tag   | ⊥   | ⊥   | ⊥   | ⊥   | ⊥   | ⊥
```

### 2.2.4 Deny Capabilities

```
Pony Deny Properties:

Each capability denies certain operations to aliases:

Capability | Local R | Local W | Global R | Global W
-----------|---------|---------|----------|----------
iso        | ✓       | ✓       | ✗        | ✗
trn        | ✓       | ✓       | ✓        | ✗
ref        | ✓       | ✓       | ✓        | ✓
val        | ✓       | ✗       | ✓        | ✗
box        | ✓       | ✗       | ✓        | ?
tag        | ✗       | ✗       | ✗        | ✗

Legend:
  Local = this reference
  Global = other references (aliases)
  R = read, W = write
  ✓ = allowed, ✗ = denied, ? = unknown
```

## 2.3 Wyvern Capability Effects

### 2.3.1 Effect System Design

Wyvern combines capabilities with effects:

```
Wyvern Capability Effects:

Resource Types:
  resource type File
    def read(): String
    def write(s: String): Unit
    
  // File is a capability type
  // Operations are effects

Effect Annotations:
  def process(f: File): String with {File.read}
  
  // Function requires File.read capability
  
Capability Passing:
  def main(fs: {File}): Unit
    val f = fs.open("data.txt")
    val contents = process(f)
```

### 2.3.2 Effect Hierarchy

```
Wyvern Effect Organization:

effect IO
  effect File extends IO
    def read: String
    def write: Unit
  effect Network extends IO
    def connect: Socket
    def send: Unit
    
// Hierarchical effects
// Capability for File includes File.read and File.write
// Capability for IO includes all File and Network effects
```

## 2.4 Austral Linear Capabilities

### 2.4.1 Linear Capability Design

Austral combines linear types with capabilities:

```austral
-- Linear type for file handle
linear type File: Linear;

-- Capability type for filesystem
capability type Filesystem;

-- Opening file requires capability, returns linear
function openFile(
  fs: &Filesystem,
  path: String
): File;

-- Reading consumes capability to read
function readFile(
  file: &File
): String;

-- Closing consumes the linear file
function closeFile(
  file: File
): Unit;

-- Usage:
function process(fs: &Filesystem): Unit is
  let f: File := openFile(fs, "data.txt");
  let contents: String := readFile(&f);
  -- Must close (linear must be consumed)
  closeFile(f);
end;
```

### 2.4.2 No Ambient Authority

```austral
-- Austral prohibits ambient authority

-- WRONG: Global file access
-- function bad(): String is
--   let f := openFile("data.txt"); -- No fs capability!
--   ...
-- end;

-- CORRECT: Capability parameter
function good(fs: &Filesystem): String is
  let f := openFile(fs, "data.txt");
  let contents := readFile(&f);
  closeFile(f);
  contents
end;

-- Entry point receives initial capabilities
entry function main(
  console: &Console,
  filesystem: &Filesystem,
  network: &Network
): ExitCode is
  -- All authority comes from parameters
  good(filesystem)
end;
```

## 2.5 seL4 Formal Capability Model

### 2.5.1 Capability Derivation

```
seL4 Capability Model:

CNode (Capability Node):
  - Array of capability slots
  - Tree structure (CSpace)
  - Each slot holds one capability
  
Capability Derivation:
  parent_cap → child_cap (with subset of rights)
  
  Rights attenuation:
    FullControl > Write > Read
    
  Revocation:
    Revoking parent revokes all children
    Derivation tree enables bulk revocation

Formal Properties:
  - Authority confined to derivation
  - No capability amplification
  - Revocation always terminates
```

### 2.5.2 seL4 Capability Types

```
seL4 Kernel Capabilities:

Memory:
  Untyped    -- raw memory (can retype)
  Frame      -- mapped memory
  PageTable  -- address space structure
  
Objects:
  TCB        -- thread control
  Endpoint   -- synchronous IPC
  Notification -- async signal
  CNode      -- capability storage
  
Rights:
  AllRights  -- full access
  Read       -- read-only
  Write      -- write-only
  Grant      -- can give to others
  GrantReply -- reply-specific grant
```

---

# PART III: TYPE SYSTEM ENCODINGS

## 3.1 Capability Type Syntax

### 3.1.1 Common Patterns

```
Capability Type Notations:

Simple Form:
  Cap<R>         -- capability for resource R
  
With Permissions:
  Cap<R, P>      -- capability for R with permission P
  Cap<File, RW>  -- read-write file capability
  
Linear Capabilities:
  lin Cap<R>     -- must use exactly once
  aff Cap<R>     -- use at most once
  
Bounded Capabilities:
  Cap<R> at ρ    -- capability valid in region ρ
  
Parameterized:
  ∀α. Cap<α>     -- polymorphic capability
```

### 3.1.2 Typing Rules

```
Capability Typing Rules:

Introduction (creation):
  Γ ⊢ create[R] : Cap<R> ! {Create<R>}
  -- Creating capability requires Create effect
  
Elimination (use):
  Γ ⊢ c : Cap<R>    Γ ⊢ op : R → τ
  ─────────────────────────────────
  Γ ⊢ use(c, op) : τ ! {Use<R>}
  
Attenuation:
  Γ ⊢ c : Cap<R, P>    P' ⊆ P
  ────────────────────────────
  Γ ⊢ attenuate(c) : Cap<R, P'>
  
Linearity:
  Γ ⊢ c : lin Cap<R>    Δ, x : lin Cap<R> ⊢ e : τ
  ─────────────────────────────────────────────────
  Γ ⊗ Δ ⊢ let x = c in e : τ
```

## 3.2 Permission Lattices

### 3.2.1 Common Permission Structures

```
Permission Lattice Examples:

File Permissions:
         Full
        /    \
     Read    Write
        \    /
         None

Memory Permissions:
           Full
         /  |  \
      Read Write Exec
        \   |   /
          None

Capability Operations:
         All
       /  |  \
   Use Grant Revoke
     \   |   /
       None
```

### 3.2.2 Permission Composition

```
Permission Algebra:

Meet (intersection):
  Read ∧ Write = None
  Full ∧ Read = Read
  
Join (union):
  Read ∨ Write = (Read + Write)
  Full ∨ Read = Full
  
Subtraction:
  Full - Read = Write
  (Read + Write) - Write = Read
  
Complement:
  ¬Read = Write + Exec + ...
```

## 3.3 Effect Integration

### 3.3.1 Capability Effects

```
Capability-Based Effect System:

Resource Effects:
  effect File = {Read, Write, Create, Delete}
  effect Network = {Connect, Send, Receive, Listen}
  effect Memory = {Alloc, Free, Read, Write}
  
Capability Requirement:
  fn read(f: Cap<File, Read>) -> String ! {File.Read}
  
Effect Polymorphism:
  fn withFile[E](
    cap: Cap<File, E>, 
    op: Cap<File, E> -> τ ! E
  ) -> τ ! E
```

### 3.3.2 Effect Masking

```
Capability Scope and Effect Masking:

Region-Bounded Capability:
  letcap c = create<File> at ρ in
    let result = use(c, read) in
    result
  end
  // File effect masked at region boundary
  // Result escapes, capability doesn't

Effect Signature:
  fn outer() -> String ! {}
    letcap c = create<File> at local in
      let s = read_file(c) in
      s  // String escapes
    end     // File capability dropped
  end
  // No File effect visible externally
```

---

# PART IV: SECURITY PROPERTIES

## 4.1 Capability Safety Properties

### 4.1.1 Formal Properties

```
Capability Safety Theorem:

Unforgeability:
  If Γ ⊬ cap : Cap<R> at time t
  Then Γ cannot use R at time t
  (Cannot create capabilities from nothing)
  
Monotonicity:
  If Γ ⊢ cap : Cap<R, P>
  Then attenuate(cap) : Cap<R, P'> where P' ⊆ P
  (Can only reduce, never increase authority)
  
Encapsulation:
  If R is created with capability c
  And c is not shared
  Then R is isolated
  (Private capabilities protect private state)
  
Confinement:
  If capability c is not passed to component X
  Then X cannot use resource R(c)
  (Authority limited to capability possession)
```

### 4.1.2 Confused Deputy Prevention

```
Capability Type Safety vs Confused Deputy:

Scenario: Compiler writing output file

ACL Version (Vulnerable):
  fn compile(input: Path, output: Path)
    // Compiler has file write access
    // User specifies output = "/etc/passwd"
    // Attack succeeds!

Capability Version (Safe):
  fn compile(input: Cap<File, Read>, output: Cap<File, Write>)
    // User must provide output capability
    // User cannot provide capability for /etc/passwd
    // Attack prevented!
```

## 4.2 Revocation Strategies

### 4.2.1 Proxy-Based Revocation

```
Revocable Capability via Proxy:

struct Revocable<C> {
    inner: Option<C>,
    revoked: AtomicBool,
}

impl<C: Capability> Revocable<C> {
    fn use<F, R>(&self, f: F) -> Result<R, Revoked>
    where F: FnOnce(&C) -> R
    {
        if self.revoked.load(Ordering::Acquire) {
            Err(Revoked)
        } else {
            match &self.inner {
                Some(cap) => Ok(f(cap)),
                None => Err(Revoked),
            }
        }
    }
    
    fn revoke(&self) {
        self.revoked.store(true, Ordering::Release);
    }
}
```

### 4.2.2 Generational Revocation

```
Generation-Based Revocation:

struct GenerationalCap<C> {
    cap: C,
    generation: u64,
}

struct CapRegistry {
    current_gen: AtomicU64,
}

impl CapRegistry {
    fn issue<C>(&self, cap: C) -> GenerationalCap<C> {
        GenerationalCap {
            cap,
            generation: self.current_gen.load(Ordering::Acquire),
        }
    }
    
    fn revoke_all(&self) {
        self.current_gen.fetch_add(1, Ordering::Release);
    }
    
    fn is_valid<C>(&self, gcap: &GenerationalCap<C>) -> bool {
        gcap.generation == self.current_gen.load(Ordering::Acquire)
    }
}
```

## 4.3 Capability Patterns for Security

### 4.3.1 Sealer/Unsealer (Encryption Pattern)

```
Type-Safe Encryption via Capabilities:

trait Sealer<T> {
    type Sealed;
    fn seal(&self, value: T) -> Self::Sealed;
}

trait Unsealer<T> {
    type Sealed;
    fn unseal(&self, sealed: Self::Sealed) -> Option<T>;
}

fn make_brand<T>() -> (impl Sealer<T>, impl Unsealer<T>) {
    let key = generate_key();
    (SealerImpl(key.clone()), UnsealerImpl(key))
}

// Only matching sealer/unsealer pair can access data
// Type system enforces: cannot unseal wrong brand
```

### 4.3.2 Membrane (Boundary Enforcement)

```
Membrane for Complete Isolation:

struct Membrane {
    // All capabilities wrapped at boundary
    // All results wrapped on return
}

impl Membrane {
    fn wrap<T: Capability>(&self, cap: T) -> MembraneWrapped<T> {
        // Capability now monitored
        // Can be revoked by revoking membrane
    }
    
    fn revoke(&self) {
        // Revokes ALL capabilities in membrane
    }
}

// Use case: Sandboxing untrusted code
fn sandbox(code: UntrustedCode, membrane: &Membrane) {
    let wrapped_fs = membrane.wrap(fs_cap);
    let wrapped_net = membrane.wrap(net_cap);
    
    code.run(wrapped_fs, wrapped_net);
    
    // After: revoke entire sandbox
    membrane.revoke();
}
```

---

# PART V: SECURITY APPLICATIONS

## 5.1 MENARA (Mobile Security)

```
Capability Design for Mobile Security:

Session Capabilities:
  cap<Session, Active>   -- active session authority
  cap<Crypto, Sign>      -- signing capability
  cap<Crypto, Verify>    -- verification capability
  cap<KeyStore, Access>  -- keystore access
  
Usage Pattern:
  fn authenticate(
    session: cap<Session, Active>,
    keystore: cap<KeyStore, Access>
  ) -> Result<AuthToken, Error> {
    let key = keystore.get_signing_key()?;
    let signature = key.sign(challenge)?;
    session.submit_auth(signature)
  }
  
Revocation:
  // On logout, revoke session capability
  // All derived operations immediately invalid
```

## 5.2 GAPURA (Web Application Firewall)

```
Capability Design for WAF:

Request Processing Capabilities:
  cap<Request, Read>      -- read request data
  cap<Request, Modify>    -- modify request (rewrite)
  cap<Response, Write>    -- write response
  cap<Backend, Forward>   -- forward to backend
  
Pipeline with Attenuated Caps:
  fn process_request(
    req: cap<Request, Read + Modify>,
    backend: cap<Backend, Forward>
  ) -> cap<Response, Write> {
    // Validation stage: Read only
    let validated = validate(attenuate(req, Read))?;
    
    // Sanitization stage: Read + Modify
    let sanitized = sanitize(req)?;
    
    // Forwarding: requires Forward cap
    backend.forward(sanitized)
  }
```

## 5.3 ZIRAH (Endpoint Detection & Response)

```
Capability Design for EDR:

Process Inspection Capabilities:
  cap<Process, Inspect>   -- read process state
  cap<Process, Suspend>   -- suspend process
  cap<Process, Terminate> -- terminate process
  cap<Memory, Read>       -- read process memory
  cap<Evidence, Collect>  -- collect forensic data
  
Privilege Separation:
  // Scanner has limited capabilities
  fn scan_process(
    proc: cap<Process, Inspect>,
    mem: cap<Memory, Read>
  ) -> ScanResult {
    let state = proc.get_state()?;
    let mem_regions = mem.read_regions()?;
    analyze(state, mem_regions)
  }
  
  // Only responder can terminate
  fn respond_to_threat(
    proc: cap<Process, Terminate>,
    evidence: cap<Evidence, Collect>
  ) -> ResponseResult {
    evidence.capture_before_action()?;
    proc.terminate()
  }
```

## 5.4 BENTENG (eKYC/Identity)

```
Capability Design for Identity Verification:

Biometric Capabilities:
  cap<Camera, Capture>    -- capture image
  cap<Biometric, Process> -- process biometric
  cap<Template, Match>    -- perform matching
  cap<Document, Verify>   -- verify document
  
Isolation Pattern:
  fn verify_identity(
    camera: cap<Camera, Capture>,
    biometric: cap<Biometric, Process>,
    template_store: cap<Template, Match>
  ) -> VerificationResult {
    // Each capability is minimal
    // Camera cannot access template store
    // Template store cannot access camera
    
    let image = camera.capture()?;
    let template = biometric.extract_template(image)?;
    template_store.match_template(template)
  }
```

## 5.5 SANDI (Digital Signatures)

```
Capability Design for Signing:

Key Capabilities:
  cap<Key, Sign>          -- can sign with key
  cap<Key, Verify>        -- can verify with key
  cap<Key, Export>        -- can export key (dangerous!)
  cap<HSM, Access>        -- HSM access
  
Principle of Least Authority:
  // Signing service only gets Sign capability
  fn signing_service(
    key: cap<Key, Sign>  // NOT Export!
  ) -> SigningService {
    SigningService { key }
  }
  
  // Key cannot be extracted
  // Only signing operations possible
  
HSM Integration:
  fn hsm_sign(
    hsm: cap<HSM, Access>,
    key_id: KeyId,
    message: &[u8]
  ) -> Signature {
    // HSM enforces capability at hardware level
    hsm.sign(key_id, message)
  }
```

---

# PART VI: INTEGRATION WITH TYPE SYSTEM

## 6.1 Integration with Linear Types (A-04)

```
Linear Capabilities:

lin cap<R>   -- capability must be used exactly once
aff cap<R>   -- capability can be dropped (not used)

Use Cases:
  lin cap<Connection> -- must close connection
  lin cap<Transaction> -- must commit or abort
  aff cap<File>        -- file handle can be dropped
  
Typing Rule:
  Γ ⊢ c : lin cap<R>    Δ, x : lin cap<R> ⊢ e : τ
  ─────────────────────────────────────────────────
  Γ ⊗ Δ ⊢ letcap x = c in e : τ
```

## 6.2 Integration with Ownership (A-13)

```
Owned Capabilities:

owned cap<R>     -- capability with ownership semantics
&cap<R>          -- borrowed capability (read)
&mut cap<R>      -- exclusive borrowed capability

Ownership Rules:
  - owned cap<R> can be moved
  - &cap<R> can be shared (multiple borrows)
  - &mut cap<R> is exclusive
  
Typing:
  fn use_cap(c: &cap<File, Read>) -> String
    // Borrows capability, doesn't consume
    
  fn consume_cap(c: owned cap<Connection>) -> ()
    // Takes ownership, closes connection
```

## 6.3 Integration with Regions (A-12)

```
Region-Scoped Capabilities:

cap<R> at ρ    -- capability valid in region ρ

Region Scoping:
  letregion ρ in
    letcap c : cap<File> at ρ = open_file(path) in
      use(c, read)
    end
  end  // capability deallocated with region

Effect Masking:
  letregion ρ in
    // File effects confined to region
    let result = file_operations() in
    result  // escapes, but cap doesn't
  end  // File effects masked
```

## 6.4 Integration with Effects (A-11)

```
Capability Effects:

Effect Declaration:
  effect Capability<R> {
    Create : () → cap<R>,
    Use : cap<R> → τ,
    Drop : cap<R> → (),
  }
  
Handler Pattern:
  handle {
    let c = perform Create();
    let r = perform Use(c);
    perform Drop(c);
    r
  } with {
    Create() → resume(create_real_resource()),
    Use(c) → resume(use_real_resource(c)),
    Drop(c) → resume(drop_real_resource(c)),
  }
```

---

# PART VII: SUMMARY

## 7.1 Key Systems Surveyed

| System | Approach | Key Feature | Production |
|--------|----------|-------------|------------|
| E | Object-capability | Promise pipelining | Yes |
| Pony | Ref capabilities | Deny capabilities | Yes |
| Wyvern | Effect caps | Hierarchical effects | Research |
| Austral | Linear caps | No ambient authority | Yes |
| seL4 | Kernel caps | Formal verification | Yes |

## 7.2 Core Capability Properties

```
Essential Capability Properties:

1. Unforgeability
   Cannot create capability from nothing
   
2. Transferability
   Can pass capabilities between components
   
3. Attenuation
   Can only reduce, never increase authority
   
4. Encapsulation
   Capability bounds protect private state
   
5. POLA Enablement
   Supports principle of least authority
```

## 7.3 Design Considerations for TERAS-LANG

```
TERAS-LANG Capability Design Questions:

1. Capability Representation
   - First-class types (like Pony)?
   - Effect annotations (like Wyvern)?
   - Linear resources (like Austral)?
   
2. Permission Model
   - Lattice-based (File: Read ⊆ Full)?
   - Set-based (explicit permission sets)?
   - Hierarchical (IO > File > Read)?
   
3. Revocation Strategy
   - Proxy-based (indirect)?
   - Generational (version numbers)?
   - Region-based (lifetime-bounded)?
   
4. Integration Priority
   - With linear types (A-04): High
   - With ownership (A-13): High
   - With regions (A-12): Medium
   - With effects (A-11): High
```

---

**END OF SURVEY DOCUMENT**

**Next Document:** RESEARCH_A14_CAPABILITY_TYPES_COMPARISON.md
