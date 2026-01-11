# TERAS-LANG Research Domain D: Capability-Based Security

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-D-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | D-01 through D-10 |
| Domain | D: Capability-Based Security |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# D-01: Capability Security Foundations

## Executive Summary

Capability-based security provides fine-grained access control through unforgeable tokens. This session covers the theoretical foundations and practical applications for TERAS.

## Core Concepts

### What is a Capability?

```
Capability = Unforgeable reference + Access rights

Properties:
â”œâ”€â”€ Unforgeable: Cannot be created out of thin air
â”œâ”€â”€ Transferable: Can be passed to others
â”œâ”€â”€ Attenuable: Can create weaker capabilities
â”œâ”€â”€ First-class: Can be stored, passed, returned
â””â”€â”€ Specific: Grants access to specific resource
```

### Capability vs ACL

```
Access Control Lists (ACL):
    Resource â†’ Set<Principal>
    "Who can access this resource?"

Capabilities:
    Principal â†’ Set<Capability>
    "What can this principal access?"

Key difference: Authority is held, not checked against
```

### Historical Development

```
Timeline:
1966    â”‚ Dennis & Van Horn: Capability concept
1974    â”‚ Hydra: Capability-based OS
1979    â”‚ Capability-Based Computer Systems (Levy)
1988    â”‚ KeyKOS: Persistent capabilities
1997    â”‚ E Language: Object capabilities
2003    â”‚ Caja: Capability-safe JavaScript
2010    â”‚ Capsicum: FreeBSD capabilities
2015    â”‚ CHERI: Hardware capabilities
```

## TERAS Decision D-01

**ADOPT** capability-based security:
1. First-class capability values
2. Object-capability discipline
3. Capability attenuation
4. Integration with type system

### Architecture Decision ID: `TERAS-ARCH-D01-CAP-001`

---

# D-02: Object Capabilities (OCaps)

## Object-Capability Model

```rust
// Object = Capability
// Having reference = Having authority

struct FileCapability {
    path: PathBuf,           // Resource identifier
    permissions: Permission, // Access rights
    // Cannot be forged - constructed only by system
}

impl FileCapability {
    // Attenuation: Create weaker capability
    pub fn read_only(&self) -> ReadOnlyFileCapability {
        ReadOnlyFileCapability {
            path: self.path.clone(),
            // Removed write permission
        }
    }
}
```

## OCap Principles

```
1. Memory safety
   - No pointer forging
   - No buffer overflows
   
2. Encapsulation
   - Private fields inaccessible
   - Authority through interfaces only
   
3. No ambient authority
   - No global mutable state
   - No implicit capabilities
   
4. Least authority
   - Grant minimum needed
   - Attenuate when passing
```

## TERAS OCap Design

```rust
// Capability trait
pub trait Capability: Sized + 'static {
    type Resource;
    type Rights: Rights;
    
    fn resource(&self) -> &Self::Resource;
    fn rights(&self) -> Self::Rights;
    fn attenuate(self, new_rights: Self::Rights) -> Option<Self>;
}

// Example: File capability
pub struct FileCap {
    handle: FileHandle,  // Unforgeable
    rights: FileRights,
}

impl Capability for FileCap {
    type Resource = FileHandle;
    type Rights = FileRights;
    
    fn attenuate(self, new_rights: FileRights) -> Option<Self> {
        if new_rights.is_subset(&self.rights) {
            Some(FileCap { handle: self.handle, rights: new_rights })
        } else {
            None  // Cannot escalate
        }
    }
}
```

## TERAS Decision D-02

**ADOPT** object-capability model:
1. Capabilities as objects
2. Authority through references
3. Mandatory attenuation support
4. No ambient authority

### Architecture Decision ID: `TERAS-ARCH-D02-OCP-001`

---

# D-03: Capability Types

## Type-Based Capability Enforcement

```rust
// Capability in type system

// Capability type parameter
struct SecureFile<R: Rights> {
    handle: FileHandle,
    _rights: PhantomData<R>,
}

// Type-level rights
struct Read;
struct Write;
struct ReadWrite;

// Type-level attenuation
impl<R: Rights> SecureFile<R> {
    fn read(&self) -> Bytes where R: HasRead { ... }
    fn write(&self, data: Bytes) where R: HasWrite { ... }
}

// Attenuation at type level
impl SecureFile<ReadWrite> {
    fn as_read_only(self) -> SecureFile<Read> { ... }
}
```

## Capability Effects

```rust
// Capability as effect/coeffect

effect FileSystem {
    fn open(path: Path) -> File;
    fn read(f: &File) -> Bytes;
    fn write(f: &File, data: Bytes);
}

// Capability coeffect
fn read_config() -[IO]-> Config 
    @ {Capability::FileRead}  // Requires capability
{
    let file = FileSystem::open("config.toml");
    FileSystem::read(&file)
}
```

## TERAS Decision D-03

**IMPLEMENT** capability types:
1. Type-level capability tracking
2. Compile-time rights checking
3. Integration with coeffects (B-03)
4. Phantom type markers for rights

### Architecture Decision ID: `TERAS-ARCH-D03-CTY-001`

---

# D-04: Capability Revocation

## Revocation Mechanisms

```rust
// 1. Caretaker pattern
struct Caretaker<C: Capability> {
    capability: Option<C>,
}

impl<C: Capability> Caretaker<C> {
    fn use_capability(&self) -> Option<&C> {
        self.capability.as_ref()
    }
    
    fn revoke(&mut self) {
        self.capability = None;
    }
}

// 2. Revocation capability
struct RevocableCap<C: Capability> {
    cap: C,
    revoked: Arc<AtomicBool>,
}

impl<C: Capability> RevocableCap<C> {
    fn use_if_valid(&self) -> Option<&C> {
        if !self.revoked.load(Ordering::Acquire) {
            Some(&self.cap)
        } else {
            None
        }
    }
}

// 3. Membrane pattern
struct Membrane<Inner, Outer> {
    inner: Inner,
    revoked: bool,
    // Wraps all capabilities crossing boundary
}
```

## TERAS Decision D-04

**IMPLEMENT** revocation:
1. Caretaker pattern for simple cases
2. Revocation capabilities for distributed
3. Membrane pattern for boundaries
4. Audit logging for revocations

### Architecture Decision ID: `TERAS-ARCH-D04-REV-001`

---

# D-05: Capability Patterns

## Common Patterns

### 1. Powerbox

```rust
// User-mediated capability granting
struct Powerbox {
    available: HashMap<ResourceType, Capability>,
}

impl Powerbox {
    fn request(&self, resource_type: ResourceType) -> Option<Capability> {
        // Show dialog to user
        // User grants or denies
        if user_approved() {
            self.available.get(&resource_type).cloned()
        } else {
            None
        }
    }
}
```

### 2. Sealers/Unsealers

```rust
// Brand/Trademark pattern
struct Sealer<T> {
    key: SealKey,  // Private
}

struct Unsealer<T> {
    key: SealKey,  // Same key
}

struct Sealed<T> {
    data: T,
    seal: SealMark,
}

impl<T> Sealer<T> {
    fn seal(&self, data: T) -> Sealed<T> { ... }
}

impl<T> Unsealer<T> {
    fn unseal(&self, sealed: Sealed<T>) -> Option<T> {
        if sealed.seal.matches(&self.key) {
            Some(sealed.data)
        } else {
            None
        }
    }
}
```

### 3. Facets

```rust
// Different views of same resource
trait Resource {
    fn admin_facet(&self) -> AdminFacet;
    fn user_facet(&self) -> UserFacet;
    fn guest_facet(&self) -> GuestFacet;
}

struct AdminFacet { /* full access */ }
struct UserFacet { /* limited access */ }
struct GuestFacet { /* read-only */ }
```

### 4. Endowment

```rust
// Initial capabilities from trusted source
fn main() {
    // Receive capabilities from runtime
    let fs_cap = runtime.get_capability::<FileSystem>();
    let net_cap = runtime.get_capability::<Network>();
    
    // Pass to application
    run_app(fs_cap, net_cap);
}
```

## TERAS Decision D-05

**IMPLEMENT** patterns:
1. Powerbox for user-granted capabilities
2. Sealer/Unsealer for brands
3. Facets for role-based views
4. Explicit endowment at startup

### Architecture Decision ID: `TERAS-ARCH-D05-PAT-001`

---

# D-06: Hardware Capabilities (CHERI)

## CHERI Overview

```
CHERI: Capability Hardware Enhanced RISC Instructions

Features:
â”œâ”€â”€ Fat pointers (128/256 bits)
â”œâ”€â”€ Hardware-enforced bounds
â”œâ”€â”€ Permission bits in pointers
â”œâ”€â”€ Unforgeable by construction
â””â”€â”€ Backward compatible
```

## CHERI Capability Format

```
128-bit CHERI capability:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Permissions â”‚ Object Type â”‚ Bounds â”‚ Base Address â”‚ Cursor â”‚
â”‚   (16 bits) â”‚   (24 bits) â”‚(varies)â”‚   (varies)   â”‚(varies)â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Permissions:
- Load/Store
- Execute
- Seal/Unseal
- Load capability
- Store capability
- System access
```

## TERAS CHERI Integration

```rust
// When targeting CHERI

#[cfg(target_arch = "cheri")]
mod cheri {
    // Native capability pointers
    type CapPtr<T> = *mut T;  // Is actually a capability
    
    // Bounds-checked references
    impl<T> CapPtr<T> {
        fn with_bounds(self, base: usize, length: usize) -> Self {
            // Hardware sets bounds
        }
        
        fn narrow_permissions(self, perms: Permissions) -> Self {
            // Hardware removes permissions
        }
    }
}
```

## TERAS Decision D-06

**SUPPORT** CHERI when available:
1. Target CHERI platforms
2. Map capabilities to CHERI pointers
3. Use hardware bounds checking
4. Fallback to software on non-CHERI

### Architecture Decision ID: `TERAS-ARCH-D06-HW-001`

---

# D-07: Capability and IFC Integration

## Unified Model

```rust
// Capabilities carry security labels

struct LabeledCapability<C: Capability, L: Label> {
    cap: C,
    label: L,
}

// Using capability requires:
// 1. Having the capability
// 2. Having appropriate clearance for label
fn use_capability<C, L>(cap: LabeledCapability<C, L>) 
    @ {Clearance: L}  // Coeffect requirement
{
    cap.use();
}
```

## Capability as Authority for Declassification

```rust
// Declassify capability
struct DeclassifyCap<From: Label, To: Label> {
    _from: PhantomData<From>,
    _to: PhantomData<To>,
}

fn declassify<T, From, To>(
    value: T @ From,
    cap: DeclassifyCap<From, To>  // Must have capability
) -> T @ To {
    // Capability authorizes declassification
    unsafe { transmute_label(value) }
}
```

## TERAS Decision D-07

**INTEGRATE** capabilities with IFC:
1. Labeled capabilities
2. Declassification via capability
3. Capability effects require clearance
4. Unified authority model

### Architecture Decision ID: `TERAS-ARCH-D07-INT-001`

---

# D-08: Sandboxing

## Capability-Based Sandboxing

```rust
// Sandbox: Capability-limited environment

struct Sandbox {
    capabilities: CapabilitySet,
    memory_limit: usize,
    time_limit: Duration,
}

impl Sandbox {
    fn run<T>(&self, f: impl FnOnce() -> T) -> Result<T, SandboxError> {
        // Create isolated environment
        // Inject only specified capabilities
        // Run with resource limits
        
        with_capabilities(&self.capabilities, || {
            with_limits(self.memory_limit, self.time_limit, f)
        })
    }
}
```

## Sandbox Patterns

```rust
// 1. Plugin execution
fn run_plugin(plugin: Plugin, input: PluginInput) -> PluginOutput {
    let sandbox = Sandbox::new()
        .with_capability(ReadConfig)
        .with_memory_limit(10_MB)
        .with_time_limit(100_MS);
    
    sandbox.run(|| plugin.process(input))
}

// 2. Tenant isolation
fn run_tenant_code(tenant: TenantId, code: Code) -> Result {
    let caps = tenant_capabilities(tenant);
    let sandbox = Sandbox::from_capabilities(caps);
    sandbox.run(|| execute(code))
}

// 3. Untrusted input processing
fn process_untrusted(input: Bytes @ Untrusted) -> Result @ Trusted {
    let sandbox = Sandbox::minimal();  // Almost no capabilities
    let result = sandbox.run(|| parse(input))?;
    validate_and_endorse(result)
}
```

## TERAS Decision D-08

**IMPLEMENT** sandboxing:
1. Capability-based isolation
2. Resource limits
3. Plugin execution support
4. Tenant isolation for TERAS products

### Architecture Decision ID: `TERAS-ARCH-D08-SBX-001`

---

# D-09: Capability in TERAS Products

## Product-Specific Capabilities

### MENARA (Mobile Security)

```rust
mod menara_caps {
    capability DeviceInfo {
        read_device_id,
        read_os_version,
        read_hardware_info,
    }
    
    capability SensitiveData {
        access_contacts,
        access_location,
        access_camera,
    }
    
    capability Security {
        verify_integrity,
        report_threat,
        quarantine_app,
    }
}
```

### GAPURA (WAF)

```rust
mod gapura_caps {
    capability RequestProcessing {
        read_request,
        modify_request,
        block_request,
        allow_request,
    }
    
    capability ThreatIntel {
        query_blocklist,
        update_blocklist,
        report_attack,
    }
}
```

### ZIRAH (EDR)

```rust
mod zirah_caps {
    capability SystemAccess {
        read_processes,
        read_network,
        read_filesystem,
    }
    
    capability Response {
        kill_process,
        quarantine_file,
        block_network,
        alert_admin,
    }
}
```

### BENTENG (eKYC)

```rust
mod benteng_caps {
    capability Verification {
        access_camera,
        capture_document,
        verify_identity,
    }
    
    capability BiometricData {
        store_template,
        match_template,
        delete_template,
    }
}
```

### SANDI (Digital Signatures)

```rust
mod sandi_caps {
    capability CryptoKey {
        generate_key,
        use_private_key,
        export_public_key,
    }
    
    capability Signing {
        sign_document,
        verify_signature,
        timestamp_signature,
    }
}
```

## TERAS Decision D-09

**DEFINE** product capabilities:
1. Per-product capability hierarchies
2. Least-privilege defaults
3. Audit for capability use
4. Attenuation for delegation

### Architecture Decision ID: `TERAS-ARCH-D09-PRD-001`

---

# D-10: Capability Best Practices

## Design Guidelines

```
Capability Design Principles:

1. POLA (Principle of Least Authority)
   - Grant minimum required
   - Attenuate before passing

2. Explicit Dependencies
   - Pass capabilities explicitly
   - No ambient authority

3. Separation of Concerns
   - Different capabilities for different functions
   - Facets for different views

4. Defense in Depth
   - Multiple capability checks
   - Combine with IFC

5. Audit Everything
   - Log capability grants
   - Log capability uses
   - Log attenuations
```

## Common Mistakes

```
Anti-patterns to avoid:

1. God capability
   âœ— struct AllAccess { /* everything */ }
   âœ“ Separate capabilities per resource

2. Implicit capability from context
   âœ— fn delete() { ambient_fs().delete(current_file()) }
   âœ“ fn delete(fs: FsCap, file: FileCap) { fs.delete(file) }

3. Capability leak
   âœ— static CACHED_CAP: Cap = ...
   âœ“ Pass capabilities through call stack

4. Missing attenuation
   âœ— pass(my_full_cap)
   âœ“ pass(my_cap.read_only())
```

## TERAS Decision D-10

**FINALIZE** capability guidelines:
1. Mandatory POLA enforcement
2. Static analysis for capability leaks
3. Automatic attenuation suggestions
4. Comprehensive audit integration

### Architecture Decision ID: `TERAS-ARCH-D10-BPR-001`

---

# Domain D Summary

## Completed Sessions

| Session | Topic | Decision ID |
|---------|-------|-------------|
| D-01 | Capability Foundations | TERAS-ARCH-D01-CAP-001 |
| D-02 | Object Capabilities | TERAS-ARCH-D02-OCP-001 |
| D-03 | Capability Types | TERAS-ARCH-D03-CTY-001 |
| D-04 | Revocation | TERAS-ARCH-D04-REV-001 |
| D-05 | Patterns | TERAS-ARCH-D05-PAT-001 |
| D-06 | Hardware (CHERI) | TERAS-ARCH-D06-HW-001 |
| D-07 | IFC Integration | TERAS-ARCH-D07-INT-001 |
| D-08 | Sandboxing | TERAS-ARCH-D08-SBX-001 |
| D-09 | Product Capabilities | TERAS-ARCH-D09-PRD-001 |
| D-10 | Best Practices | TERAS-ARCH-D10-BPR-001 |

## Key Decisions

1. **Object-capability model** as foundation
2. **Type-level capability tracking**
3. **Integration with effects and IFC**
4. **Hardware support** (CHERI)
5. **Product-specific** capability definitions

---

## Domain D: COMPLETE

**Total Documents: 10** (combined in this file)

Ready for Domain E: Formal Verification

---

*Research Track Output â€” Domain D: Capability-Based Security*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
