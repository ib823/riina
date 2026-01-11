# TERAS-LANG Research Domain J: Module Systems and Namespaces

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-J-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | J-01 through J-10 |
| Domain | J: Module Systems and Namespaces |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# J-01: Module System Foundations

## Executive Summary

Module systems provide abstraction, encapsulation, and code organization. For security-critical systems, modules must also enforce capability boundaries, control information flow, and enable separate compilation with verified interfaces.

## Module System Goals

```
1. Namespace Management
   - Avoid name collisions
   - Hierarchical organization
   - Qualified access

2. Encapsulation
   - Hide implementation details
   - Control access to internals
   - Maintain invariants

3. Abstraction
   - Abstract types
   - Interface contracts
   - Polymorphism

4. Separate Compilation
   - Independent compilation units
   - Stable interfaces
   - Incremental builds

5. Security (TERAS-specific)
   - Capability boundaries
   - Information flow control
   - Audit points at module boundaries
```

## Module vs Package vs Crate

```
Module: Single namespace unit
    - Defined in one or more files
    - Contains types, functions, constants
    - Has visibility controls

Package: Collection of modules
    - Distributable unit
    - Version controlled
    - Dependency specification

Crate (Rust): Compilation unit
    - Library or binary
    - Root of module tree
    - Defines extern interfaces
```

## TERAS Module Hierarchy

```
teras                       # Root crate
â”œâ”€â”€ core                    # Core utilities
â”‚   â”œâ”€â”€ types              # Basic types
â”‚   â”œâ”€â”€ collections        # Collections
â”‚   â””â”€â”€ io                 # I/O primitives
â”œâ”€â”€ crypto                  # Cryptography
â”‚   â”œâ”€â”€ symmetric          # AES, ChaCha20
â”‚   â”œâ”€â”€ asymmetric         # RSA, EC, PQC
â”‚   â”œâ”€â”€ hash               # SHA, BLAKE
â”‚   â””â”€â”€ kdf                # Key derivation
â”œâ”€â”€ security               # Security primitives
â”‚   â”œâ”€â”€ auth               # Authentication
â”‚   â”œâ”€â”€ authz              # Authorization
â”‚   â”œâ”€â”€ audit              # Audit logging
â”‚   â””â”€â”€ ifc                # Information flow
â””â”€â”€ products               # TERAS products
    â”œâ”€â”€ menara             # Mobile security
    â”œâ”€â”€ gapura             # WAF
    â”œâ”€â”€ zirah              # EDR
    â”œâ”€â”€ benteng            # eKYC
    â””â”€â”€ sandi              # Digital signatures
```

## TERAS Decision J-01

**IMPLEMENT** module system:
1. Hierarchical modules
2. Strong encapsulation
3. Capability-aware boundaries
4. Separate compilation

### Architecture Decision ID: `TERAS-ARCH-J01-MOD-001`

---

# J-02: Visibility and Access Control

## Visibility Levels

```rust
// Public: Accessible from anywhere
pub struct PublicType;
pub fn public_function() {}

// Private: Accessible only in current module (default)
struct PrivateType;
fn private_function() {}

// Crate-visible: Accessible within crate
pub(crate) struct CrateType;
pub(crate) fn crate_function() {}

// Super-visible: Accessible in parent module
pub(super) struct SuperType;

// Path-visible: Accessible in specific module
pub(in crate::security) struct SecurityType;
```

## Struct Field Visibility

```rust
pub struct Config {
    // Public field
    pub name: String,
    
    // Private field (only this module)
    api_key: SecureString,
    
    // Crate-visible field
    pub(crate) internal_flag: bool,
}

impl Config {
    // Public constructor controls access
    pub fn new(name: String, api_key: SecureString) -> Self {
        Config {
            name,
            api_key,
            internal_flag: false,
        }
    }
    
    // Public getter
    pub fn name(&self) -> &str {
        &self.name
    }
    
    // No getter for api_key - truly private
}
```

## TERAS Security Visibility

```rust
// Security level visibility
#[security_level(Secret)]
pub(security: Secret) struct ClassifiedData {
    content: Vec<u8>,
}

// Only code with Secret clearance can access
impl ClassifiedData {
    #[requires_clearance(Secret)]
    pub fn read(&self) -> &[u8] {
        &self.content
    }
}

// Capability-based visibility
#[requires_capability(CryptoSign)]
pub fn sign_document(doc: &Document) -> Signature {
    // Only accessible with CryptoSign capability
}

// Module-level security policy
#[module_policy(
    clearance = TopSecret,
    capabilities = [CryptoAll, AuditRead]
)]
mod classified_operations {
    // All items inherit module security policy
}
```

## TERAS Decision J-02

**IMPLEMENT** visibility:
1. Rust-style visibility levels
2. Security-level visibility
3. Capability-based access
4. Module-level policies

### Architecture Decision ID: `TERAS-ARCH-J02-VIS-001`

---

# J-03: Imports and Exports

## Import Syntax

```rust
// Import specific items
use std::collections::HashMap;
use std::io::{Read, Write};

// Import with alias
use std::collections::HashMap as Map;

// Import all public items (discouraged)
use std::collections::*;

// Nested imports
use std::{
    collections::{HashMap, HashSet},
    io::{self, Read, Write},
    sync::Arc,
};

// Re-export
pub use crate::internal::PublicApi;

// Re-export with rename
pub use crate::internal::InternalName as PublicName;
```

## Export Control

```rust
// Module declaration
mod private_module;        // Private module
pub mod public_module;     // Public module

// Selective re-export
mod internal {
    pub struct Foo;
    pub struct Bar;
    struct Baz;  // Private
}

pub use internal::Foo;  // Only Foo is public API

// Prelude pattern
pub mod prelude {
    pub use crate::core::*;
    pub use crate::common_traits::*;
}

// User imports prelude
use teras::prelude::*;
```

## TERAS Security Imports

```rust
// Import with capability requirement
#[requires_capability(CryptoAll)]
use teras::crypto::*;

// Import triggers audit
#[audit_import]
use teras::security::classified::*;

// Labeled imports
use teras::data::*;  // All imports carry their labels

// Capability scoped imports
with_capability!(FileRead) {
    use std::fs::*;  // Only available in this scope
}
```

## TERAS Decision J-03

**IMPLEMENT** imports:
1. Rust-style use syntax
2. Selective re-exports
3. Security-aware imports
4. Capability scoping

### Architecture Decision ID: `TERAS-ARCH-J03-IMP-001`

---

# J-04: Abstract Types and Signatures

## Abstract Types

```rust
// Type is public but representation is hidden
mod counter {
    pub struct Counter {
        value: u64,  // Private field
    }
    
    impl Counter {
        pub fn new() -> Self {
            Counter { value: 0 }
        }
        
        pub fn increment(&mut self) {
            self.value += 1;
        }
        
        pub fn get(&self) -> u64 {
            self.value
        }
    }
}

// Users cannot construct or inspect directly
use counter::Counter;
let c = Counter::new();  // OK
// let c = Counter { value: 0 };  // ERROR: private field
```

## Module Signatures (Traits as Interfaces)

```rust
// Define interface
trait KeyStore {
    type Key;
    type Error;
    
    fn generate(&mut self) -> Result<Self::Key, Self::Error>;
    fn get(&self, id: &KeyId) -> Result<&Self::Key, Self::Error>;
    fn delete(&mut self, id: &KeyId) -> Result<(), Self::Error>;
}

// Implementation
struct FileKeyStore { ... }

impl KeyStore for FileKeyStore {
    type Key = FileKey;
    type Error = IoError;
    
    fn generate(&mut self) -> Result<FileKey, IoError> { ... }
    fn get(&self, id: &KeyId) -> Result<&FileKey, IoError> { ... }
    fn delete(&mut self, id: &KeyId) -> Result<(), IoError> { ... }
}

struct HsmKeyStore { ... }

impl KeyStore for HsmKeyStore {
    type Key = HsmKey;
    type Error = HsmError;
    
    fn generate(&mut self) -> Result<HsmKey, HsmError> { ... }
    fn get(&self, id: &KeyId) -> Result<&HsmKey, HsmError> { ... }
    fn delete(&mut self, id: &KeyId) -> Result<(), HsmError> { ... }
}
```

## Sealed Traits

```rust
// Prevent external implementations
mod sealed {
    pub trait Sealed {}
}

pub trait CryptoAlgorithm: sealed::Sealed {
    fn name(&self) -> &str;
    fn key_size(&self) -> usize;
}

// Only TERAS can implement
impl sealed::Sealed for Aes256 {}
impl CryptoAlgorithm for Aes256 {
    fn name(&self) -> &str { "AES-256" }
    fn key_size(&self) -> usize { 32 }
}

// External crates cannot implement CryptoAlgorithm
```

## TERAS Decision J-04

**IMPLEMENT** abstractions:
1. Abstract type pattern
2. Trait-based interfaces
3. Sealed traits for security
4. Associated types

### Architecture Decision ID: `TERAS-ARCH-J04-ABS-001`

---

# J-05: Separate Compilation

## Compilation Units

```
Compilation Model:

Source Files â†’ Parsing â†’ AST â†’ Type Checking â†’ IR â†’ Optimization â†’ Object Code
                                    â†“
                            Interface Files (.terai)
                                    â†“
                        Other compilation units import

Interface File Contains:
- Public type signatures
- Public function signatures
- Effect signatures
- Security labels
- Capability requirements
```

## Interface Files

```rust
// Generated interface file: crypto.terai
module crypto;

pub struct AesKey<const BITS: usize>;

pub fn encrypt(
    key: &AesKey<256>,
    nonce: &Nonce,
    data: &[u8]
) -> Vec<u8>
! CryptoEffect
@ {Capability::CryptoEncrypt};

pub fn decrypt(
    key: &AesKey<256>,
    nonce: &Nonce,
    ciphertext: &[u8]
) -> Result<Vec<u8>, DecryptError>
! CryptoEffect
@ {Capability::CryptoDecrypt};
```

## Incremental Compilation

```
Dependency Graph:
    core.teras
        â†“
    crypto.teras â† security.teras
        â†“              â†“
    products/sandi.teras

Change in crypto.teras:
1. Recompile crypto.teras
2. Check interface unchanged?
   - Yes: Done
   - No: Recompile dependents (sandi.teras)
```

## TERAS Security in Interfaces

```rust
// Interface includes security contracts
pub fn process_pii(data: PiiData @ Secret) -> ProcessedData @ Public
! IFCEffect
@ {Capability::PiiAccess}
requires { data.validated }
ensures { result.sanitized };

// Capability requirements in interface
#[interface_capability(CryptoSign)]
pub trait Signer {
    fn sign(&self, data: &[u8]) -> Signature;
}
```

## TERAS Decision J-05

**IMPLEMENT** separate compilation:
1. Interface file generation
2. Incremental compilation
3. Security in interfaces
4. Stable ABI for security modules

### Architecture Decision ID: `TERAS-ARCH-J05-SEP-001`

---

# J-06: Package Management

## Package Manifest

```toml
# teras.toml
[package]
name = "teras-crypto"
version = "1.0.0"
edition = "2026"
authors = ["TERAS Team"]
license = "Proprietary"

[dependencies]
teras-core = "1.0"
teras-audit = "1.0"

[dev-dependencies]
teras-test = "1.0"

[features]
default = ["pqc"]
pqc = []        # Post-quantum crypto
hsm = []        # HSM support
fips = []       # FIPS compliance mode

[security]
min-clearance = "Confidential"
required-capabilities = ["CryptoAll"]
audit-level = "Full"
```

## Dependency Resolution

```
Resolution Algorithm:

1. Parse all package manifests
2. Build dependency graph
3. Resolve version constraints
   - Semver compatibility
   - Security version requirements
4. Check security constraints
   - Capability requirements satisfied
   - Clearance levels compatible
5. Lock resolved versions
```

## Security in Dependencies

```toml
# Security-aware dependencies
[dependencies]
# Standard dependency
serde = "1.0"

# Dependency with security constraints
teras-crypto = { 
    version = "1.0", 
    features = ["fips"],
    security = { 
        audit = true,
        min-version = "1.0.5",  # Security patch
        verified = true          # Only use verified builds
    }
}

# Pinned for security
openssl-sys = { 
    version = "=0.9.80",  # Exact version
    checksum = "sha256:abc123..."
}
```

## TERAS Decision J-06

**IMPLEMENT** packages:
1. TOML manifest format
2. Semver versioning
3. Security constraints
4. Verified builds

### Architecture Decision ID: `TERAS-ARCH-J06-PKG-001`

---

# J-07: Workspace and Multi-Crate Projects

## Workspace Structure

```
teras-workspace/
â”œâ”€â”€ Cargo.toml           # Workspace manifest
â”œâ”€â”€ teras-core/
â”‚   â”œâ”€â”€ Cargo.toml
â”‚   â””â”€â”€ src/
â”œâ”€â”€ teras-crypto/
â”‚   â”œâ”€â”€ Cargo.toml
â”‚   â””â”€â”€ src/
â”œâ”€â”€ teras-security/
â”‚   â”œâ”€â”€ Cargo.toml
â”‚   â””â”€â”€ src/
â”œâ”€â”€ products/
â”‚   â”œâ”€â”€ menara/
â”‚   â”œâ”€â”€ gapura/
â”‚   â”œâ”€â”€ zirah/
â”‚   â”œâ”€â”€ benteng/
â”‚   â””â”€â”€ sandi/
â””â”€â”€ tools/
    â”œâ”€â”€ teras-cli/
    â””â”€â”€ teras-test/
```

## Workspace Manifest

```toml
# Root Cargo.toml
[workspace]
members = [
    "teras-core",
    "teras-crypto",
    "teras-security",
    "products/*",
    "tools/*",
]

[workspace.package]
version = "1.0.0"
edition = "2026"
license = "Proprietary"

[workspace.dependencies]
# Shared dependency versions
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }

[workspace.security]
# Workspace-wide security policy
audit-all-deps = true
require-signatures = true
```

## Inter-Crate Dependencies

```toml
# teras-crypto/Cargo.toml
[package]
name = "teras-crypto"
version.workspace = true

[dependencies]
teras-core = { path = "../teras-core" }

# products/sandi/Cargo.toml
[package]
name = "teras-sandi"
version.workspace = true

[dependencies]
teras-core = { path = "../../teras-core" }
teras-crypto = { path = "../../teras-crypto" }
teras-security = { path = "../../teras-security" }
```

## TERAS Decision J-07

**IMPLEMENT** workspaces:
1. Multi-crate workspaces
2. Shared configurations
3. Path dependencies
4. Unified security policy

### Architecture Decision ID: `TERAS-ARCH-J07-WRK-001`

---

# J-08: Module Initialization and Lifecycle

## Static Initialization

```rust
// Compile-time constants
const MAX_BUFFER_SIZE: usize = 4096;
const DEFAULT_TIMEOUT: Duration = Duration::from_secs(30);

// Static items (runtime initialized)
static GLOBAL_CONFIG: Lazy<Config> = Lazy::new(|| {
    Config::load().expect("Failed to load config")
});

// Thread-local
thread_local! {
    static SECURITY_CONTEXT: RefCell<SecurityContext> = 
        RefCell::new(SecurityContext::default());
}
```

## Module Initialization Order

```rust
// Explicit initialization
mod crypto {
    static INITIALIZED: AtomicBool = AtomicBool::new(false);
    
    pub fn init() -> Result<(), InitError> {
        if INITIALIZED.swap(true, Ordering::SeqCst) {
            return Ok(());  // Already initialized
        }
        
        // Initialize crypto subsystem
        init_rng()?;
        init_algorithms()?;
        
        Audit::log(ModuleInitialized { module: "crypto" });
        Ok(())
    }
    
    pub fn shutdown() {
        // Cleanup
        zeroize_keys();
        INITIALIZED.store(false, Ordering::SeqCst);
        Audit::log(ModuleShutdown { module: "crypto" });
    }
}

// Dependency-ordered initialization
fn init_teras() -> Result<(), InitError> {
    // Order matters
    core::init()?;
    crypto::init()?;  // Depends on core
    security::init()?;  // Depends on crypto
    audit::init()?;
    
    Ok(())
}
```

## TERAS Secure Initialization

```rust
// Security-critical initialization
#[secure_init(
    requires = [core, crypto],
    clearance = TopSecret,
    audit = true
)]
mod hsm {
    pub fn init(config: &HsmConfig) -> Result<(), HsmError> {
        // Authenticate to HSM
        let session = hsm_authenticate(config)?;
        
        // Verify HSM integrity
        verify_hsm_state(&session)?;
        
        // Load keys
        load_master_keys(&session)?;
        
        Audit::log(HsmInitialized { 
            serial: session.device_serial(),
        });
        
        Ok(())
    }
}

// Initialization verification
#[test]
fn test_init_order() {
    // Verify correct initialization order
    assert!(core::is_initialized());
    assert!(crypto::is_initialized());
    assert!(security::is_initialized());
}
```

## TERAS Decision J-08

**IMPLEMENT** initialization:
1. Explicit init functions
2. Dependency ordering
3. Secure init attributes
4. Shutdown cleanup

### Architecture Decision ID: `TERAS-ARCH-J08-INI-001`

---

# J-09: Conditional Compilation

## Feature Flags

```rust
// Feature-gated code
#[cfg(feature = "pqc")]
mod post_quantum {
    pub fn ml_kem_encapsulate(...) { ... }
    pub fn ml_dsa_sign(...) { ... }
}

#[cfg(not(feature = "pqc"))]
mod post_quantum {
    pub fn ml_kem_encapsulate(...) {
        panic!("PQC not enabled");
    }
}

// Conditional compilation
#[cfg(feature = "fips")]
fn random_bytes(buf: &mut [u8]) {
    fips_approved_rng(buf);
}

#[cfg(not(feature = "fips"))]
fn random_bytes(buf: &mut [u8]) {
    getrandom(buf);
}
```

## Platform-Specific Code

```rust
// OS-specific implementations
#[cfg(target_os = "linux")]
mod platform {
    pub fn secure_memory(ptr: *mut u8, len: usize) {
        mlock(ptr, len);
    }
}

#[cfg(target_os = "windows")]
mod platform {
    pub fn secure_memory(ptr: *mut u8, len: usize) {
        VirtualLock(ptr, len);
    }
}

#[cfg(target_os = "macos")]
mod platform {
    pub fn secure_memory(ptr: *mut u8, len: usize) {
        mlock(ptr, len);
    }
}

// Architecture-specific
#[cfg(target_arch = "x86_64")]
fn aes_encrypt_block(key: &[u8], block: &mut [u8]) {
    // Use AES-NI instructions
    unsafe { aes_ni_encrypt(key, block); }
}

#[cfg(target_arch = "aarch64")]
fn aes_encrypt_block(key: &[u8], block: &mut [u8]) {
    // Use ARM Crypto extensions
    unsafe { arm_aes_encrypt(key, block); }
}
```

## TERAS Security Configurations

```rust
// Security level configurations
#[cfg(security_level = "high")]
const KEY_SIZE: usize = 256;
const ITERATIONS: u32 = 1_000_000;

#[cfg(security_level = "standard")]
const KEY_SIZE: usize = 128;
const ITERATIONS: u32 = 100_000;

// Audit configurations
#[cfg(audit = "full")]
macro_rules! audit {
    ($event:expr) => { Audit::log($event); }
}

#[cfg(audit = "minimal")]
macro_rules! audit {
    ($event:expr) => { 
        if $event.severity() >= Severity::High {
            Audit::log($event);
        }
    }
}

#[cfg(audit = "none")]
macro_rules! audit {
    ($event:expr) => {}
}
```

## TERAS Decision J-09

**IMPLEMENT** conditional compilation:
1. Feature flags
2. Platform targets
3. Security configurations
4. Audit levels

### Architecture Decision ID: `TERAS-ARCH-J09-CFG-001`

---

# J-10: Module Patterns in TERAS Products

## MENARA Module Structure

```rust
// products/menara/src/lib.rs
pub mod scanner {
    pub mod app;
    pub mod network;
    pub mod permission;
}

pub mod protection {
    pub mod realtime;
    pub mod scheduled;
}

pub mod reporting {
    pub mod threats;
    pub mod compliance;
}

// Prelude for common imports
pub mod prelude {
    pub use crate::scanner::*;
    pub use crate::protection::*;
    pub use crate::ThreatLevel;
}
```

## GAPURA Module Structure

```rust
// products/gapura/src/lib.rs
pub mod core {
    pub mod request;
    pub mod response;
    pub mod context;
}

pub mod rules {
    pub mod parser;
    pub mod engine;
    pub mod actions;
}

pub mod detection {
    pub mod sql_injection;
    pub mod xss;
    pub mod rce;
    pub mod custom;
}

pub mod ratelimit {
    pub mod bucket;
    pub mod sliding_window;
}
```

## ZIRAH Module Structure

```rust
// products/zirah/src/lib.rs
pub mod agent {
    pub mod collector;
    pub mod sender;
}

pub mod scanner {
    pub mod file;
    pub mod memory;
    pub mod registry;
}

pub mod detection {
    pub mod signatures;
    pub mod heuristics;
    pub mod behavioral;
}

pub mod response {
    pub mod quarantine;
    pub mod remediate;
    pub mod isolate;
}
```

## BENTENG Module Structure

```rust
// products/benteng/src/lib.rs
pub mod verification {
    pub mod face;
    pub mod document;
    pub mod liveness;
}

pub mod ocr {
    pub mod mykad;
    pub mod passport;
    pub mod drivers_license;
}

pub mod matching {
    pub mod biometric;
    pub mod data;
}

pub mod session {
    pub mod workflow;
    pub mod state;
}
```

## SANDI Module Structure

```rust
// products/sandi/src/lib.rs
pub mod keys {
    pub mod generation;
    pub mod storage;
    pub mod hsm;
}

pub mod signing {
    pub mod document;
    pub mod timestamp;
    pub mod certificate;
}

pub mod verification {
    pub mod signature;
    pub mod chain;
    pub mod revocation;
}

pub mod formats {
    pub mod pkcs7;
    pub mod xades;
    pub mod pades;
}
```

## TERAS Decision J-10

**IMPLEMENT** product modules:
1. Domain-driven structure
2. Clear boundaries
3. Public API via prelude
4. Internal implementation hiding

### Architecture Decision ID: `TERAS-ARCH-J10-PROD-001`

---

# Domain J Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| J-01 | Foundations | TERAS-ARCH-J01-MOD-001 |
| J-02 | Visibility | TERAS-ARCH-J02-VIS-001 |
| J-03 | Imports | TERAS-ARCH-J03-IMP-001 |
| J-04 | Abstractions | TERAS-ARCH-J04-ABS-001 |
| J-05 | Separate Compilation | TERAS-ARCH-J05-SEP-001 |
| J-06 | Packages | TERAS-ARCH-J06-PKG-001 |
| J-07 | Workspaces | TERAS-ARCH-J07-WRK-001 |
| J-08 | Initialization | TERAS-ARCH-J08-INI-001 |
| J-09 | Conditional | TERAS-ARCH-J09-CFG-001 |
| J-10 | Products | TERAS-ARCH-J10-PROD-001 |

## Domain J: COMPLETE

---

*Research Track Output â€” Domain J: Module Systems and Namespaces*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
