# TERAS-LANG Research Domain D: Hardware Security

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-D-HARDWARE-SECURITY |
| Version | 1.0.0 |
| Date | 2026-01-04 |
| Sessions | D-01 through D-15 |
| Domain | D: Hardware Security |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# D-01: Trusted Execution Environments (TEEs) - Foundations

## Executive Summary

Trusted Execution Environments provide hardware-isolated execution contexts that protect code and data even from privileged software. This session covers all major TEE architectures, their security guarantees, and known vulnerabilities.

## 1. Intel SGX (Software Guard Extensions)

### 1.1 Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                        SGX Architecture                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Untrusted Application                     │   │
│  │  ┌─────────────────────────────────────────────────────┐    │   │
│  │  │                    Enclave                           │    │   │
│  │  │  ┌─────────────┐  ┌─────────────┐  ┌────────────┐   │    │   │
│  │  │  │ Trusted Code│  │ Sealed Data │  │ Attestation│   │    │   │
│  │  │  └─────────────┘  └─────────────┘  └────────────┘   │    │   │
│  │  │                                                      │    │   │
│  │  │  Protected by: EPC (Enclave Page Cache)             │    │   │
│  │  │  Encrypted with: MEE (Memory Encryption Engine)     │    │   │
│  │  └─────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Ring 0: OS/Hypervisor (UNTRUSTED from enclave perspective)        │
│  Hardware: CPU Package (Trust Anchor)                               │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 SGX Instructions

```
ENCLAVE LIFECYCLE:
├── ECREATE    - Create enclave control structure
├── EADD       - Add pages to enclave
├── EEXTEND    - Measure page contents
├── EINIT      - Initialize enclave (verify SIGSTRUCT)
├── EENTER     - Enter enclave (ring 3 → enclave)
├── EEXIT      - Exit enclave (enclave → ring 3)
├── ERESUME    - Resume after AEX (Asynchronous Enclave Exit)
├── EGETKEY    - Derive sealing/report keys
├── EREPORT    - Generate attestation report
└── EREMOVE    - Remove enclave page

PRIVILEGED INSTRUCTIONS (Ring 0):
├── EBLOCK     - Block EPC page for eviction
├── ETRACK     - Activate EBLOCK changes
├── EWB        - Evict EPC page (encrypted to main memory)
├── ELDB/ELDU  - Load blocked/unblocked page back
└── EPA        - Add version array page
```

### 1.3 SGX Security Properties

**Confidentiality**: 
- Memory Encryption Engine (MEE) encrypts EPC with AES-128-CTR
- Per-enclave keys derived from CPU master key
- Version Array prevents rollback of evicted pages

**Integrity**:
- MRENCLAVE: Hash of enclave identity (code + data layout)
- MRSIGNER: Hash of signing key
- MAC on every cache line (prevents tampering)

**Attestation**:
- Local attestation: EREPORT creates MAC-protected report
- Remote attestation: EPID/DCAP quotes signed by Intel

### 1.4 SGX Vulnerabilities (Comprehensive)

```
VULNERABILITY CLASS: Side-Channel Attacks
├── Cache-Based
│   ├── Prime+Probe: Detect enclave cache access patterns
│   ├── Flush+Reload: Requires shared memory (limited in SGX)
│   └── Cache-Line Granularity: 64-byte resolution
│
├── Page-Table Based
│   ├── Controlled-Channel: OS controls page faults
│   ├── Page-fault sequences leak access patterns
│   └── Demonstrated: Extracting full documents, keys
│
├── Branch Prediction
│   ├── Branch Target Injection (BTI/Spectre v2)
│   ├── Speculative execution leaks enclave data
│   └── SgxPectre: Specific SGX variant
│
├── Speculative Execution
│   ├── Foreshadow/L1TF: L1 cache bypass
│   ├── Reads arbitrary enclave memory
│   └── Complete SGX break (patched, performance cost)
│
└── Microarchitectural
    ├── CacheOut/TAA: Transactional memory leaks
    ├── LVI: Load Value Injection
    └── ÆPIC Leak: Uninitialized APIC register read

VULNERABILITY CLASS: Software Attacks
├── Iago Attacks: Malicious OS returns corrupted syscall results
├── AsyncShock: Interrupt handling vulnerabilities
├── Dark-ROP: Enclave gadget chains
└── Guard's Dilemma: Cannot verify OS behavior

VULNERABILITY CLASS: Physical Attacks
├── Cold Boot: Memory remanence (MEE mitigates)
├── Bus Snooping: Encrypted, but patterns visible
└── Fault Injection: Voltage/clock glitching
```

### 1.5 SGX Programming Model

```c
// Enclave Definition (EDL file)
enclave {
    trusted {
        // Functions callable from untrusted code (ECALLs)
        public int ecall_process_secret([in, size=len] uint8_t* data, size_t len);
        public int ecall_get_sealed([out, size=sealed_size] uint8_t* sealed, 
                                     size_t sealed_size);
    };
    
    untrusted {
        // Functions enclave can call out to (OCALLs)
        void ocall_print_string([in, string] const char* str);
        int ocall_read_file([in, string] const char* path,
                           [out, size=buf_size] uint8_t* buf,
                           size_t buf_size);
    };
};

// Trusted code (inside enclave)
#include "enclave_t.h"
#include <sgx_tseal.h>
#include <sgx_trts.h>

int ecall_process_secret(uint8_t* data, size_t len) {
    // Validate input (CRITICAL - prevents Iago attacks)
    if (!sgx_is_outside_enclave(data, len)) {
        return SGX_ERROR_INVALID_PARAMETER;
    }
    
    // Copy to enclave memory (prevents TOCTOU)
    uint8_t* local_copy = (uint8_t*)malloc(len);
    memcpy(local_copy, data, len);
    
    // Process secretly...
    
    // Zero sensitive data before free
    memset_s(local_copy, len, 0, len);
    free(local_copy);
    
    return SGX_SUCCESS;
}
```

## 2. ARM TrustZone

### 2.1 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                     ARM TrustZone Architecture                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌──────────────────────────┐  ┌──────────────────────────┐        │
│  │      Normal World        │  │      Secure World         │        │
│  │                          │  │                           │        │
│  │  ┌────────────────────┐  │  │  ┌─────────────────────┐ │        │
│  │  │   Rich OS (Linux)  │  │  │  │  Trusted OS (OP-TEE)│ │        │
│  │  │   ┌──────────────┐ │  │  │  │  ┌───────────────┐  │ │        │
│  │  │   │ Normal Apps  │ │  │  │  │  │ Trusted Apps  │  │ │        │
│  │  │   └──────────────┘ │  │  │  │  │ (TA: DRM, Pay)│  │ │        │
│  │  └────────────────────┘  │  │  │  └───────────────┘  │ │        │
│  │                          │  │  └─────────────────────┘ │        │
│  │  EL0: User              │  │  S-EL0: Secure User      │        │
│  │  EL1: Kernel            │  │  S-EL1: Secure Kernel    │        │
│  │  EL2: Hypervisor        │  │                           │        │
│  └──────────────────────────┘  └──────────────────────────┘        │
│                                                                     │
│                    EL3: Secure Monitor (ATF)                        │
│                    ═══════════════════════════                      │
│                    Handles world switching via SMC                  │
└─────────────────────────────────────────────────────────────────────┘

NS BIT: Single bit in processor determines world
- NS=0: Secure World (can access everything)
- NS=1: Normal World (blocked from secure resources)
```

### 2.2 TrustZone Components

**Hardware:**
- TZASC (TrustZone Address Space Controller): Memory partitioning
- TZPC (TrustZone Protection Controller): Peripheral access control
- TZMA (TrustZone Memory Adapter): On-chip memory protection
- GIC (Generic Interrupt Controller): Secure interrupt routing

**Software Stack:**
- Secure Monitor (EL3): World switching, SMC handler
- Trusted OS: OP-TEE, Trusty, QSEE, iTrustee
- Trusted Applications: Isolated secure services

### 2.3 GlobalPlatform TEE API

```c
// Trusted Application Entry Points
TEE_Result TA_CreateEntryPoint(void);
void TA_DestroyEntryPoint(void);
TEE_Result TA_OpenSessionEntryPoint(uint32_t paramTypes,
                                     TEE_Param params[4],
                                     void **sessionContext);
void TA_CloseSessionEntryPoint(void *sessionContext);
TEE_Result TA_InvokeCommandEntryPoint(void *sessionContext,
                                       uint32_t commandID,
                                       uint32_t paramTypes,
                                       TEE_Param params[4]);

// Cryptographic Operations
TEE_Result TEE_AllocateOperation(TEE_OperationHandle *operation,
                                  uint32_t algorithm,
                                  uint32_t mode,
                                  uint32_t maxKeySize);

// Secure Storage
TEE_Result TEE_CreatePersistentObject(uint32_t storageID,
                                       const void *objectID,
                                       size_t objectIDLen,
                                       uint32_t flags,
                                       TEE_ObjectHandle attributes,
                                       const void *initialData,
                                       size_t initialDataLen,
                                       TEE_ObjectHandle *object);
```

### 2.4 TrustZone Vulnerabilities

```
VULNERABILITY CLASS: Software
├── QSEE Exploits: Multiple privilege escalation (2014-2020)
├── Boomerang Attack: Return-oriented programming in TEE
├── CLKSCREW: Software-controlled voltage/frequency attacks
└── Trust Issues: Compromised TA can attack other TAs

VULNERABILITY CLASS: Design Limitations
├── Single Secure World: No isolation between TAs (in basic TZ)
├── No Remote Attestation: Standard TZ lacks attestation
├── Vendor Dependent: Security varies by implementation
└── Debug Interfaces: JTAG/SWD can compromise security

VULNERABILITY CLASS: Side-Channels
├── Cache Attacks: Prime+Probe works across worlds
├── TruSpy: Cross-world cache-based covert channel
└── ARMageddon: Comprehensive ARM cache attack study
```

## 3. AMD SEV (Secure Encrypted Virtualization)

### 3.1 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                        AMD SEV Architecture                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                      Hypervisor (Untrusted)                    │ │
│  │  ┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐  │ │
│  │  │   VM 1 (SEV)    │ │   VM 2 (SEV)    │ │  VM 3 (Plain)   │  │ │
│  │  │   Key: K1       │ │   Key: K2       │ │   No encryption │  │ │
│  │  │   ┌───────────┐ │ │   ┌───────────┐ │ │                 │  │ │
│  │  │   │Guest OS   │ │ │   │Guest OS   │ │ │                 │  │ │
│  │  │   │+ Apps     │ │ │   │+ Apps     │ │ │                 │  │ │
│  │  │   └───────────┘ │ │   └───────────┘ │ │                 │  │ │
│  │  └─────────────────┘ └─────────────────┘ └─────────────────┘  │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
│  AMD Secure Processor (PSP): Key management, attestation           │
│  Memory Encryption: AES-128 with per-VM keys                       │
└─────────────────────────────────────────────────────────────────────┘

SEV Variants:
├── SEV: Basic memory encryption
├── SEV-ES: Encrypted State (register protection)
└── SEV-SNP: Secure Nested Paging (integrity + attestation)
```

### 3.2 SEV-SNP Security Features

**Memory Integrity:**
- Reverse Map Table (RMP): Tracks page ownership
- Prevents hypervisor from mapping guest pages maliciously
- Memory replay protection

**Attestation:**
- VCEK (Versioned Chip Endorsement Key): Per-chip attestation key
- Attestation reports signed by PSP
- Platform measurement chain

### 3.3 SEV Vulnerabilities

```
SEV (Original):
├── SEVered: Hypervisor can remap encrypted pages
├── No integrity protection → Ciphertext manipulation
└── Unencrypted VMCB → Register state visible

SEV-ES:
├── Encrypted VMSA (VM Save Area)
├── Still vulnerable to page remapping
└── Performance impact from encrypted registers

SEV-SNP:
├── Addresses integrity with RMP
├── Side-channel attacks still apply
├── CacheWarp: Software-based fault attack (2023)
└── ÆPIC-like attacks on AMD
```

## 4. Intel TDX (Trust Domain Extensions)

### 4.1 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                        Intel TDX Architecture                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    TDX Module (TCB)                            │ │
│  │  - Manages TD lifecycle                                        │ │
│  │  - Memory encryption/integrity                                 │ │
│  │  - Attestation                                                 │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│  ┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐       │
│  │  Trust Domain 1 │ │  Trust Domain 2 │ │  VMX Guest      │       │
│  │  (TD Guest)     │ │  (TD Guest)     │ │  (Untrusted)    │       │
│  │  - Encrypted    │ │  - Encrypted    │ │                 │       │
│  │  - Integrity    │ │  - Integrity    │ │                 │       │
│  │  - Attested     │ │  - Attested     │ │                 │       │
│  └─────────────────┘ └─────────────────┘ └─────────────────┘       │
│                                                                     │
│  Untrusted VMM: Manages resources but cannot access TD memory      │
└─────────────────────────────────────────────────────────────────────┘

Key Features:
├── Multi-key TME (Total Memory Encryption)
├── Integrity via MAC per cache line
├── Secure EPT (Extended Page Tables)
└── Remote attestation via Intel SGX infrastructure
```

## TERAS Decision D-01

**CRITICAL FINDINGS:**

1. **No TEE is Perfect**: All TEEs have demonstrated vulnerabilities
2. **Side-Channels Universal**: Cache/speculative attacks affect all platforms
3. **Defense in Depth Required**: Cannot rely solely on TEE for security

**FOR TERAS:**
- Use TEE as ONE layer of defense, not sole protection
- Implement side-channel resistant algorithms in software
- Design for TEE-agnostic operation (support multiple TEEs)
- Attestation verification must be rigorous
- Assume TEE compromise is possible; limit blast radius

### Architecture Decision ID: `TERAS-ARCH-D01-TEE-001`

---

# D-02: Trusted Platform Module (TPM)

## 1. TPM 2.0 Architecture

### 1.1 Component Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                      TPM 2.0 Architecture                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    TPM Subsystems                            │   │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐    │   │
│  │  │  Cryptographic│  │   Platform    │  │   Credential  │    │   │
│  │  │   Subsystem   │  │ Configuration │  │   Management  │    │   │
│  │  │  - RSA/ECC    │  │   Registers   │  │  - Keys       │    │   │
│  │  │  - AES        │  │   (PCRs)      │  │  - Certs      │    │   │
│  │  │  - SHA-256    │  │   - 24 banks  │  │  - Hierarchy  │    │   │
│  │  │  - HMAC       │  │   - Extend    │  │               │    │   │
│  │  └───────────────┘  └───────────────┘  └───────────────┘    │   │
│  │                                                              │   │
│  │  ┌───────────────┐  ┌───────────────┐  ┌───────────────┐    │   │
│  │  │   Random      │  │    Non-       │  │   Command     │    │   │
│  │  │   Number      │  │   Volatile    │  │   Execution   │    │   │
│  │  │   Generator   │  │   Storage     │  │   Engine      │    │   │
│  │  │   (RNG)       │  │   (NVRAM)     │  │               │    │   │
│  │  └───────────────┘  └───────────────┘  └───────────────┘    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Interface: FIFO/CRB over LPC/SPI/I2C                              │
└─────────────────────────────────────────────────────────────────────┘

Key Hierarchies:
├── Platform Hierarchy (PH): OEM/firmware controlled
├── Storage Hierarchy (SH): OS/user key storage
├── Endorsement Hierarchy (EH): TPM identity, attestation
└── Null Hierarchy: Session keys, ephemeral operations
```

### 1.2 Platform Configuration Registers (PCRs)

```
PCR Index | Typical Usage
──────────┼────────────────────────────────────────────
PCR 0     | CRTM, BIOS, Platform firmware
PCR 1     | Platform configuration (BIOS settings)
PCR 2     | Option ROM code
PCR 3     | Option ROM configuration
PCR 4     | MBR, IPL code (bootloader stage 1)
PCR 5     | MBR configuration, GPT/partition table
PCR 6     | State transitions, wake events
PCR 7     | Secure Boot policy
PCR 8-15  | OS-specific measurements
PCR 16    | Debug PCR
PCR 17-22 | TXT (Trusted Execution Technology)
PCR 23    | Application-specific

PCR Extension:
PCR_new = Hash(PCR_old || measurement)
- One-way: Cannot undo extension
- Order-dependent: Same measurements in different order → different PCR
```

### 1.3 TPM Commands

```c
// Key Creation
TPM2_CreatePrimary   // Create primary key under hierarchy
TPM2_Create          // Create child key
TPM2_Load            // Load key from external blob
TPM2_ContextSave     // Save key context
TPM2_ContextLoad     // Restore key context

// Sealing/Unsealing
TPM2_Create(... policyDigest ...)  // Create sealed blob
TPM2_Unseal                         // Unseal with policy

// PCR Operations
TPM2_PCR_Extend      // Extend PCR with measurement
TPM2_PCR_Read        // Read PCR values
TPM2_PCR_Reset       // Reset PCR (limited PCRs only)

// Attestation
TPM2_Quote           // Sign PCR values
TPM2_Certify         // Certify key properties
TPM2_GetCapability   // Query TPM properties

// Policy Commands
TPM2_PolicyPCR       // Policy requires specific PCR values
TPM2_PolicyPassword  // Policy requires password
TPM2_PolicyAuthValue // Policy requires auth value
TPM2_PolicyOR        // Disjunction of policies
TPM2_PolicyNV        // Policy based on NV index
```

### 1.4 Measured Boot / Trusted Boot

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Measured Boot Chain                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  CPU Reset ────────────────────────────────────────────────────►    │
│       │                                                             │
│       ▼                                                             │
│  ┌─────────┐    Measure    ┌─────────┐    Measure    ┌─────────┐   │
│  │  CRTM   │──────────────►│  BIOS   │──────────────►│  Boot   │   │
│  │ (ACM)   │    PCR[0]     │         │    PCR[4]     │ Loader  │   │
│  └─────────┘               └─────────┘               └─────────┘   │
│       │                         │                         │         │
│       │                         │                         │         │
│       ▼                         ▼                         ▼         │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                         TPM PCRs                             │   │
│  │  PCR[0]: CRTM hash                                          │   │
│  │  PCR[1]: BIOS config                                        │   │
│  │  PCR[4]: Bootloader                                         │   │
│  │  PCR[8-9]: OS kernel + initrd                               │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Attestation: TPM2_Quote signs PCR values                          │
│  Verification: Compare against known-good values                    │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.5 TPM Vulnerabilities

```
VULNERABILITY CLASS: Physical Attacks
├── TPM Genie: MITM on LPC bus, intercept commands
├── Cold Boot: Memory contains TPM session state
├── Fault Injection: Glitch during unsealing
└── ROCA (CVE-2017-15361): Weak RSA key generation in Infineon TPMs

VULNERABILITY CLASS: Software/Firmware
├── TPM-FAIL (CVE-2019-11090): Timing attack on ECDSA
├── fTPM vulnerabilities: AMD PSP bugs affect fTPM
└── Reference implementation bugs: Various CVEs

VULNERABILITY CLASS: Design Issues
├── Time-of-Check-Time-of-Use: Boot measurements vs. runtime
├── Evil Maid: Physical access can modify measured components
├── Reset attacks: Discrete TPM can be reset independently
└── Key hierarchy: Owner password often not set
```

## 2. Remote Attestation

### 2.1 Attestation Protocols

```
Direct Anonymous Attestation (DAA):
┌──────────┐         ┌──────────┐         ┌──────────┐
│  Issuer  │         │   Host   │         │ Verifier │
│ (Vendor) │         │  (TPM)   │         │          │
└────┬─────┘         └────┬─────┘         └────┬─────┘
     │                    │                    │
     │  Issue Credential  │                    │
     │<───────────────────│                    │
     │  (EK attestation)  │                    │
     │───────────────────>│                    │
     │                    │                    │
     │                    │  Attestation Req   │
     │                    │<───────────────────│
     │                    │                    │
     │                    │  DAA Signature     │
     │                    │───────────────────>│
     │                    │  (Anonymous proof) │
     │                    │                    │
     │                    │                    │
     
Privacy Properties:
- Issuer cannot link attestations to TPM
- Verifier cannot link attestations (unless same basename)
- Revocation possible without breaking anonymity
```

## TERAS Decision D-02

**FOR TERAS:**
1. Use TPM for secure key storage (never export raw keys)
2. Implement measured boot for TERAS runtime
3. Seal sensitive data to PCR values
4. Design for discrete TPM vulnerabilities
5. Support fTPM but prefer hardware TPM
6. Implement remote attestation for deployment verification

### Architecture Decision ID: `TERAS-ARCH-D02-TPM-001`

---

# D-03: Hardware Security Modules (HSMs)

## 1. HSM Architecture

### 1.1 Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                       HSM Architecture                               │
├─────────────────────────────────────────────────────────────────────┤
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Tamper-Resistant Boundary                   │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │   Secure    │  │    Key      │  │   Cryptographic     │   │ │
│  │  │  Processor  │  │   Storage   │  │     Engines         │   │ │
│  │  │  (ARM/RISC) │  │  (Battery-  │  │  - RSA/ECC accel    │   │ │
│  │  │             │  │   backed)   │  │  - AES/3DES accel   │   │ │
│  │  │  Runs HSM   │  │             │  │  - Hash accel       │   │ │
│  │  │  firmware   │  │  Zeroizes   │  │  - RNG (TRNG)       │   │ │
│  │  │             │  │  on tamper  │  │                     │   │ │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │ │
│  │                                                               │ │
│  │  ┌─────────────────────────────────────────────────────────┐ │ │
│  │  │                  Tamper Detection                        │ │ │
│  │  │  - Temperature sensors                                   │ │ │
│  │  │  - Voltage monitors                                      │ │ │
│  │  │  - Light sensors (epoxy removal)                         │ │ │
│  │  │  - Mesh sensors (drilling/probing)                       │ │ │
│  │  │  - Clock frequency monitors                              │ │ │
│  │  └─────────────────────────────────────────────────────────┘ │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
│  Interface: PCIe / Network (TLS) / USB                             │
│  Management: Console / Web UI / PKCS#11                            │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 FIPS 140-2/140-3 Security Levels

```
Level 1: Basic Security
├── Production-grade equipment
├── One approved algorithm
├── No physical security required
└── Example: OpenSSL FIPS module

Level 2: Tamper-Evidence
├── Tamper-evident coatings/seals
├── Role-based authentication
├── Operator/User roles
└── Example: Some USB tokens

Level 3: Tamper-Resistance
├── Active tamper response (zeroization)
├── Identity-based authentication
├── Physical separation of interfaces
├── EFP/EFT environmental protection
└── Example: Thales Luna, Entrust nShield

Level 4: Complete Envelope
├── Complete environmental failure protection
├── Multi-factor authentication required
├── Immediate zeroization on any anomaly
├── Penetration testing required
└── Example: Very specialized devices
```

### 1.3 HSM Operations

```c
// PKCS#11 API (Standard HSM Interface)

// Session Management
CK_RV C_OpenSession(CK_SLOT_ID slotID, CK_FLAGS flags,
                    CK_VOID_PTR pApplication,
                    CK_NOTIFY Notify,
                    CK_SESSION_HANDLE_PTR phSession);

// Key Generation
CK_RV C_GenerateKeyPair(CK_SESSION_HANDLE hSession,
                        CK_MECHANISM_PTR pMechanism,
                        CK_ATTRIBUTE_PTR pPublicKeyTemplate,
                        CK_ULONG ulPublicKeyAttributeCount,
                        CK_ATTRIBUTE_PTR pPrivateKeyTemplate,
                        CK_ULONG ulPrivateKeyAttributeCount,
                        CK_OBJECT_HANDLE_PTR phPublicKey,
                        CK_OBJECT_HANDLE_PTR phPrivateKey);

// Key attributes
CK_ATTRIBUTE privateKeyTemplate[] = {
    {CKA_TOKEN, &true, sizeof(true)},           // Persistent
    {CKA_PRIVATE, &true, sizeof(true)},         // Requires login
    {CKA_SENSITIVE, &true, sizeof(true)},       // Never extractable plaintext
    {CKA_EXTRACTABLE, &false, sizeof(false)},   // Cannot wrap/export
    {CKA_SIGN, &true, sizeof(true)},            // Can sign
};

// Signing
CK_RV C_Sign(CK_SESSION_HANDLE hSession,
             CK_BYTE_PTR pData, CK_ULONG ulDataLen,
             CK_BYTE_PTR pSignature, CK_ULONG_PTR pulSignatureLen);

// Key Wrapping (for backup)
CK_RV C_WrapKey(CK_SESSION_HANDLE hSession,
                CK_MECHANISM_PTR pMechanism,
                CK_OBJECT_HANDLE hWrappingKey,
                CK_OBJECT_HANDLE hKey,
                CK_BYTE_PTR pWrappedKey,
                CK_ULONG_PTR pulWrappedKeyLen);
```

### 1.4 Cloud HSM Services

```
AWS CloudHSM:
├── FIPS 140-2 Level 3
├── Dedicated HSM instances
├── PKCS#11, JCE, CNG interfaces
├── Backup to S3 (encrypted)
└── Customer-controlled keys (AWS has no access)

Azure Dedicated HSM:
├── Thales Luna Network HSM
├── FIPS 140-2 Level 3
├── Direct customer access
├── HA configuration support
└── Customer-managed firmware

Google Cloud HSM:
├── FIPS 140-2 Level 3
├── Cloud KMS integration
├── Asymmetric key support
└── EKM (External Key Manager) support

AWS KMS (vs CloudHSM):
├── Multi-tenant (shared HSM backend)
├── Managed service (less control)
├── FIPS 140-2 Level 2 (software)
├── FIPS 140-2 Level 3 (HSM-backed keys)
└── Simpler API, lower cost
```

## TERAS Decision D-03

**FOR TERAS:**
1. HSM integration for root key storage
2. Support PKCS#11 interface standard
3. Never store master keys in software
4. Implement key ceremony procedures
5. Support both on-premise and cloud HSM
6. Design for HSM unavailability (cached operations)

### Architecture Decision ID: `TERAS-ARCH-D03-HSM-001`

---

# D-04: Secure Boot and Chain of Trust

## 1. UEFI Secure Boot

### 1.1 Key Hierarchy

```
┌─────────────────────────────────────────────────────────────────────┐
│                    UEFI Secure Boot Key Hierarchy                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│                     Platform Key (PK)                               │
│                     ────────────────                                │
│                     OEM-controlled                                  │
│                     Single key                                      │
│                     Controls KEK enrollment                         │
│                            │                                        │
│                            ▼                                        │
│                  Key Exchange Keys (KEK)                            │
│                  ───────────────────────                            │
│                  Can modify db/dbx                                  │
│                  Multiple keys allowed                              │
│                  Microsoft KEK typically included                   │
│                            │                                        │
│                            ▼                                        │
│         ┌─────────────────┴─────────────────┐                      │
│         ▼                                   ▼                       │
│    Signature DB (db)                   Forbidden DB (dbx)           │
│    ──────────────────                  ────────────────             │
│    Allowed signatures                  Revoked signatures           │
│    - Microsoft UEFI CA                 - Known-bad hashes           │
│    - Microsoft 3rd Party CA            - Revoked certificates       │
│    - Vendor keys                       - Compromised keys           │
│    - User keys                                                      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Boot Flow

```
UEFI Secure Boot Verification:

1. Power On
   └──► CPU initializes, loads UEFI firmware

2. UEFI Firmware (PEI/DXE)
   └──► Self-verification (optional, vendor-specific)

3. Boot Manager
   └──► Loads bootloader (e.g., GRUB, Windows Boot Manager)
   └──► Verifies signature against db, checks not in dbx
   └──► Failure: Boot halted or fallback

4. Bootloader
   └──► Loads kernel
   └──► Shim (Linux): Re-verifies with MOK (Machine Owner Key)
   └──► Failure: Kernel not loaded

5. Kernel
   └──► Loads modules/drivers
   └──► Kernel lockdown mode (Linux): Restricts runtime modifications
```

### 1.3 Secure Boot Vulnerabilities

```
VULNERABILITY CLASS: Bootkit/Rootkit
├── BootHole (CVE-2020-10713): GRUB2 buffer overflow, bypass Secure Boot
├── BlackLotus (2023): First in-wild UEFI bootkit bypassing Secure Boot
├── FinSpy UEFI: Commercial spyware with UEFI persistence
└── Hacking Team UEFI: Leaked rootkit with Secure Boot bypass

VULNERABILITY CLASS: Key Management
├── Leaked signing keys: Some OEM keys compromised
├── Test keys in production: MOK enrolled with test keys
├── Weak key storage: PK/KEK stored insecurely
└── No revocation: dbx updates slow/incomplete

VULNERABILITY CLASS: Implementation
├── Parser bugs: Complex formats (PE/COFF) lead to vulnerabilities
├── Variable tampering: Authenticated variables improperly verified
├── Time-of-check issues: Variables modified between check and use
└── Integer overflows: Size calculations in signature verification

VULNERABILITY CLASS: Design
├── Microsoft monopoly: Requires Microsoft signature for most hardware
├── No measured boot: Secure Boot alone doesn't provide attestation
├── User hostile: Adding custom keys is difficult
└── Partial coverage: Only covers early boot, not runtime
```

## 2. Intel TXT (Trusted Execution Technology)

### 2.1 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Intel TXT Architecture                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Normal Boot                    TXT Launch                          │
│  ───────────                    ──────────                          │
│  BIOS → OS                      BIOS → SINIT ACM → MLE              │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Dynamic Root of Trust                     │   │
│  │                                                              │   │
│  │  1. GETSEC[SENTER] - Enter measured environment             │   │
│  │  2. Load SINIT ACM (Intel-signed Authenticated Code Module) │   │
│  │  3. SINIT measures MLE (Measured Launch Environment)        │   │
│  │  4. MLE executes (tboot → Linux kernel)                     │   │
│  │  5. Measurements extend PCR 17-22                           │   │
│  │                                                              │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  DRTM vs SRTM:                                                      │
│  - SRTM: Static Root of Trust (full boot measured)                 │
│  - DRTM: Dynamic Root of Trust (late launch, smaller TCB)          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 TXT Vulnerabilities

```
├── SINIT Bypass: Vulnerability in SINIT ACM verification
├── SMM Attacks: SMM not measured, can attack TXT environment
├── DMA Attacks: IOMMU configuration errors
├── Reset Attacks: TXT state not properly cleared on reset
└── TOCTOU: Memory contents change between measurement and use
```

## TERAS Decision D-04

**FOR TERAS:**
1. Require Secure Boot for deployment
2. Provide signed bootloader/shim
3. Use TXT/DRTM where available
4. Implement runtime integrity verification
5. Support measured boot with TPM
6. Design for boot compromise recovery

### Architecture Decision ID: `TERAS-ARCH-D04-BOOT-001`

---

# D-05: Memory Protection Hardware

## 1. Memory Management Unit (MMU)

### 1.1 Page Table Security

```
┌─────────────────────────────────────────────────────────────────────┐
│                    x86-64 Page Table Entry                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  63    62    52 51          12 11   9 8 7 6 5 4 3 2 1 0            │
│  ├─────┼───────┼──────────────┼─────┼─┼─┼─┼─┼─┼─┼─┼─┼─┤            │
│  │ XD  │ Avail │ Physical Addr│Avail│G│0│D│A│C│W│U│W│P│            │
│  │     │       │  (Bits 51:12)│     │ │ │ │ │D│T│S│ │ │            │
│  └─────┴───────┴──────────────┴─────┴─┴─┴─┴─┴─┴─┴─┴─┴─┘            │
│                                                                     │
│  Security-Relevant Bits:                                            │
│  ├── P (Present): Page is valid                                    │
│  ├── R/W: 0=Read-only, 1=Read-Write                                │
│  ├── U/S: 0=Supervisor only, 1=User accessible                     │
│  ├── XD/NX (bit 63): Execute Disable (No Execute)                  │
│  └── SMEP/SMAP: Supervisor Mode Execution/Access Prevention        │
│                                                                     │
│  Protection Keys (bits 62:59 in PTE):                              │
│  ├── PKU: User-space protection keys (PKRU register)               │
│  └── PKS: Supervisor protection keys (MSR)                         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Modern Memory Protections

```
Protection         | Description                    | Bypass Technique
───────────────────┼────────────────────────────────┼──────────────────────
W^X (DEP/NX)       | Pages cannot be W and X        | ROP/JOP, JIT spray
ASLR               | Randomize memory layout        | Info leak, brute force
Stack Canaries     | Detect stack buffer overflow   | Format string, info leak
SMEP               | Prevent kernel exec of user    | Kernel ROP, ret2dir
SMAP               | Prevent kernel access of user  | Gadgets, physmap
KASLR              | Randomize kernel addresses     | Side-channel, info leak
CET (Shadow Stack) | Hardware return address check  | Non-ret control flow
BTI                | Branch target hardening        | Still vulnerable
CFI                | Control Flow Integrity         | Implementation gaps
```

## 2. IOMMU (Input/Output Memory Management Unit)

### 2.1 Intel VT-d Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                      Intel VT-d Architecture                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────┐        ┌─────────────┐        ┌─────────────────┐ │
│  │   Device    │───────►│   IOMMU     │───────►│  System Memory  │ │
│  │  (PCIe/USB) │  DMA   │  (VT-d)     │        │                 │ │
│  └─────────────┘        └─────────────┘        └─────────────────┘ │
│                                │                                    │
│                   ┌────────────┴────────────┐                      │
│                   ▼                         ▼                       │
│            ┌──────────────┐         ┌──────────────┐               │
│            │ Context Table│         │  Page Tables │               │
│            │ (per device) │         │ (per domain) │               │
│            └──────────────┘         └──────────────┘               │
│                                                                     │
│  Protections:                                                       │
│  ├── DMA Remapping: Restrict device memory access                  │
│  ├── Interrupt Remapping: Prevent interrupt injection              │
│  └── Posted Interrupts: Secure interrupt delivery                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 DMA Attack Mitigations

```
Attack Vector:
1. Malicious device connected (Thunderbolt, PCIe)
2. Device performs DMA to kernel memory
3. Overwrites security-sensitive structures
4. Kernel compromised

Mitigations:
├── IOMMU enabled by default (Linux 5.x+)
├── Thunderbolt security levels (user authorization)
├── Kernel DMA protection (pre-boot setting)
├── Secure Boot required for full protection
└── Windows: Kernel DMA Protection policy

Remaining Issues:
├── IOMMU bypass via ATS (Address Translation Services)
├── Passthrough mode for VMs disables protection
├── Complex configuration leads to errors
└── Legacy devices may not be isolated
```

## 3. ARM Memory Protection

### 3.1 Memory Tagging Extension (MTE)

```
┌─────────────────────────────────────────────────────────────────────┐
│                    ARM Memory Tagging Extension                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Pointer:  [63:60 TAG] [59:0 ADDRESS]                              │
│                  │                                                  │
│                  ▼                                                  │
│  Memory:  Each 16-byte granule has 4-bit tag                       │
│                                                                     │
│  ┌────────────────────────────────────────────────────────────┐    │
│  │  0x1000  │  0x1010  │  0x1020  │  0x1030  │  ...          │    │
│  │  Tag: 5  │  Tag: 3  │  Tag: 7  │  Tag: 5  │               │    │
│  └────────────────────────────────────────────────────────────┘    │
│                                                                     │
│  Access:                                                            │
│  ├── Load/Store checks pointer tag against memory tag              │
│  ├── Match: Access proceeds                                        │
│  ├── Mismatch: Fault (sync) or async report                        │
│  └── IRG instruction: Generate random tag                          │
│                                                                     │
│  Use Cases:                                                         │
│  ├── Heap buffer overflow detection                                │
│  ├── Use-after-free detection                                      │
│  ├── Double-free detection                                         │
│  └── Stack buffer overflow (with compiler support)                 │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 3.2 Pointer Authentication (PAC)

```
ARMv8.3 Pointer Authentication:

Pointer Format:
┌─────────────────────────────────────────────────────────────────────┐
│  [63:48 PAC] [47:0 Virtual Address]                                 │
│                                                                     │
│  PAC = QARMA(key, pointer || context)                              │
│                                                                     │
│  Keys (per EL):                                                     │
│  ├── APIAKey: Instruction pointers (A key)                         │
│  ├── APIBKey: Instruction pointers (B key)                         │
│  ├── APDAKey: Data pointers (A key)                                │
│  ├── APDBKey: Data pointers (B key)                                │
│  └── APGAKey: Generic authentication                               │
│                                                                     │
│  Instructions:                                                      │
│  ├── PACIA: Sign instruction pointer with A key                    │
│  ├── AUTIA: Authenticate instruction pointer with A key            │
│  ├── PACDA: Sign data pointer with A key                           │
│  └── RETAA: Return with authentication                             │
│                                                                     │
│  Security:                                                          │
│  ├── Protects return addresses (vs ROP)                            │
│  ├── Protects function pointers                                    │
│  ├── Probabilistic: 16-bit PAC has 1/65536 collision               │
│  └── PACMAN attack: Speculative execution can leak PAC             │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## TERAS Decision D-05

**FOR TERAS:**
1. Mandate W^X enforcement
2. Use hardware memory tagging (MTE) where available
3. Enable pointer authentication on ARM
4. Require IOMMU for device isolation
5. Implement software guards for missing hardware features
6. Design for various hardware protection levels

### Architecture Decision ID: `TERAS-ARCH-D05-MEMPROT-001`

---

# D-06: CPU Security Features

## 1. Control Flow Integrity (CFI) Hardware

### 1.1 Intel CET (Control-flow Enforcement Technology)

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Intel CET Architecture                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Shadow Stack:                                                      │
│  ─────────────                                                      │
│  ┌────────────┐     ┌────────────┐                                 │
│  │ User Stack │     │Shadow Stack│                                 │
│  │            │     │            │                                 │
│  │ Local Vars │     │ Ret Addr 1 │ ◄─── CALL pushes to both       │
│  │ Ret Addr 1 │────►│ Ret Addr 2 │ ◄─── RET compares both         │
│  │ Local Vars │     │    ...     │                                 │
│  │ Ret Addr 2 │     │            │                                 │
│  │    ...     │     │            │                                 │
│  └────────────┘     └────────────┘                                 │
│                                                                     │
│  Shadow Stack Properties:                                           │
│  ├── Separate memory region, not writable via normal stores        │
│  ├── CALL: Push return address to shadow stack                     │
│  ├── RET: Compare shadow stack vs regular stack                    │
│  ├── Mismatch: #CP (Control Protection) exception                  │
│  └── INCSSP/RDSSP: Manipulate shadow stack pointer                 │
│                                                                     │
│  Indirect Branch Tracking (IBT):                                    │
│  ───────────────────────────────                                    │
│  ├── ENDBR32/ENDBR64: Valid indirect branch targets                │
│  ├── JMP/CALL indirect sets TRACKER state                          │
│  ├── Next instruction must be ENDBR or #CP exception               │
│  └── Prevents arbitrary code execution via JOP                     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 ARM BTI (Branch Target Identification)

```
ARMv8.5 Branch Target Identification:

Landing Pads:
├── BTI c: Valid target for BLR (call indirect)
├── BTI j: Valid target for BR (jump indirect)
├── BTI jc: Valid target for both
└── PSTATE.BTYPE: Tracks previous branch type

Code:
    BLR x0          // Sets BTYPE = 01 (call)
    ...
target:
    BTI c           // Valid landing pad for calls
    // Function code
    RET

Protection:
├── Must land on BTI instruction after indirect branch
├── Fault if landing on non-BTI instruction
├── Coarse-grained: Any BTI of matching type is valid
└── Combine with PAC for better protection
```

## 2. Speculative Execution Defenses

### 2.1 Spectre Mitigations

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Spectre Mitigation Overview                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Spectre v1 (Bounds Check Bypass):                                  │
│  ─────────────────────────────────                                  │
│  Mitigation:                                                        │
│  ├── LFENCE: Serialize speculative execution                       │
│  ├── Array index masking: index &= (index < limit) - 1             │
│  ├── Speculation barriers: Compiler intrinsics                     │
│  └── Static analysis: Identify vulnerable patterns                 │
│                                                                     │
│  Spectre v2 (Branch Target Injection):                              │
│  ─────────────────────────────────────                              │
│  Mitigation:                                                        │
│  ├── Retpoline: Replace indirect branches with return trampolines  │
│  ├── IBRS: Indirect Branch Restricted Speculation                  │
│  ├── STIBP: Single Thread Indirect Branch Predictors               │
│  ├── IBPB: Indirect Branch Predictor Barrier                       │
│  └── eIBRS: Enhanced IBRS (always-on mode)                         │
│                                                                     │
│  Spectre-BHB (Branch History Buffer):                               │
│  ────────────────────────────────────                               │
│  Mitigation:                                                        │
│  ├── Clear BHB on kernel entry                                     │
│  └── Additional barrier instructions                               │
│                                                                     │
│  SSBD (Speculative Store Bypass Disable):                           │
│  ─────────────────────────────────────────                          │
│  ├── Prevents speculative bypass of store forwarding               │
│  └── Significant performance impact                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 Meltdown Mitigations

```
Meltdown (Rogue Data Cache Load):
├── Speculative read of kernel memory from user space
├── Data transmitted via cache side channel
└── Complete kernel memory exposure

KPTI (Kernel Page Table Isolation):
├── Separate page tables for user and kernel mode
├── Kernel pages not mapped in user page tables
├── Context switch flushes TLB (performance cost)
└── PCID: Process Context ID to reduce TLB flush cost

Kernel:
┌─────────────────┐     User:
│ Kernel code     │     ┌─────────────────┐
│ Kernel data     │     │ User code       │
│ User code       │     │ User data       │
│ User data       │     │ (Kernel: tiny   │
│                 │     │  trampoline     │
│                 │     │  only)          │
└─────────────────┘     └─────────────────┘
```

## 3. Memory Encryption

### 3.1 Intel TME/MKTME

```
Total Memory Encryption (TME):
├── AES-XTS encryption of all DRAM
├── Single key for entire system
├── Key generated at boot, stored in CPU
└── Transparent to software

Multi-Key TME (MKTME):
├── Multiple encryption keys
├── Per-page key selection via page tables
├── Key ID in physical address bits
├── Enables SEV-like VM isolation
└── Up to 64+ keys depending on CPU
```

## TERAS Decision D-06

**FOR TERAS:**
1. Enable CET shadow stack when available
2. Compile with CFI enabled (LLVM CFI)
3. Use retpoline for Spectre v2 mitigation
4. Enable KPTI and speculative execution mitigations
5. Design algorithms for speculative execution safety
6. Monitor for new CPU vulnerabilities

### Architecture Decision ID: `TERAS-ARCH-D06-CPUSEC-001`

---

# D-07: Physical Security and Tamper Resistance

## 1. Physical Attack Classes

### 1.1 Attack Taxonomy

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Physical Attack Taxonomy                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  INVASIVE ATTACKS (require chip decapsulation)                      │
│  ─────────────────────────────────────────────                      │
│  ├── Microprobing: Direct probe of internal signals                │
│  ├── FIB (Focused Ion Beam): Circuit modification                  │
│  ├── Laser fault injection: Targeted bit flips                     │
│  └── Reverse engineering: Full chip layout extraction              │
│                                                                     │
│  SEMI-INVASIVE ATTACKS (access to chip surface)                     │
│  ───────────────────────────────────────────────                    │
│  ├── Optical fault induction: UV/visible light attacks             │
│  ├── Electromagnetic fault induction: EM pulses                    │
│  ├── Laser scanning microscopy: Read memory contents               │
│  └── Photon emission analysis: Observe transistor switching        │
│                                                                     │
│  NON-INVASIVE ATTACKS (external observation only)                   │
│  ─────────────────────────────────────────────────                  │
│  ├── Power analysis: SPA, DPA, CPA                                 │
│  ├── Electromagnetic analysis: SEMA, DEMA                          │
│  ├── Timing analysis: Operation timing variations                  │
│  ├── Acoustic analysis: Sound of operations                        │
│  ├── Thermal analysis: Heat patterns                               │
│  └── Cold boot: Memory remanence after power loss                  │
│                                                                     │
│  FAULT INJECTION ATTACKS                                            │
│  ───────────────────────                                            │
│  ├── Voltage glitching: Vcc manipulation                           │
│  ├── Clock glitching: Frequency manipulation                       │
│  ├── Temperature extremes: Induce bit flips                        │
│  └── Radiation: X-ray, gamma, particle beams                       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Tamper Resistance Techniques

```
Passive Defenses:
├── Security meshes: Detect drilling/cutting
├── Light sensors: Detect decapsulation
├── Temperature sensors: Detect extreme conditions
├── Voltage sensors: Detect glitching attempts
├── Clock monitors: Detect frequency manipulation
├── Epoxy/conformal coating: Physical barrier
└── Shielding: EM protection

Active Defenses:
├── Automatic zeroization: Destroy keys on tamper
├── Alarm circuits: Alert on intrusion
├── Self-destruct: Physical destruction of chip
├── Frequency hopping: Vary operation timing
├── Power filtering: Reduce side-channel leakage
└── Dummy operations: Mask real operations
```

## 2. Cold Boot Attacks

### 2.1 Memory Remanence

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Cold Boot Attack                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Standard DRAM Decay:                                               │
│  ├── Room temperature: ~1-2 seconds before significant decay       │
│  ├── 0°C: ~10 seconds retention                                    │
│  ├── -50°C: ~10 minutes retention                                  │
│  └── Liquid nitrogen: Hours of retention                           │
│                                                                     │
│  Attack Procedure:                                                  │
│  1. Target machine running with keys in memory                     │
│  2. Cool DRAM modules (canned air upside down = -50°C)            │
│  3. Power off briefly                                              │
│  4. Boot from attack USB with memory imaging tool                  │
│  5. Dump memory contents                                           │
│  6. Extract encryption keys                                        │
│                                                                     │
│  Mitigations:                                                       │
│  ├── Memory encryption (TME/MKTME, SEV)                           │
│  ├── Key scrubbing on shutdown                                     │
│  ├── TRESOR: Store keys in CPU registers only                      │
│  ├── Memory locking: Prevent swap, wipe on hibernate              │
│  └── Physical memory protection: Tamper-evident cases              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. Bus Sniffing and Probing

### 3.1 External Bus Attacks

```
Target Buses:
├── PCIe: DMA attacks, malicious peripherals
├── USB: BadUSB, malicious devices
├── Thunderbolt: Direct memory access
├── SPI: Flash chip reading/writing
├── I2C: EEPROM access, TPM communication
├── JTAG: Debug access, full system control
└── SWD: ARM debug interface

Mitigations:
├── IOMMU: DMA protection
├── Bus encryption: TPM 2.0 encrypted sessions
├── Debug fuses: Disable JTAG/SWD in production
├── Port disable: Block unused interfaces
├── Authentication: Device attestation before trust
└── Physical protection: Block port access
```

## TERAS Decision D-07

**FOR TERAS:**
1. Assume physical access is possible
2. Never store keys in plain DRAM
3. Use memory encryption where available
4. Implement secure key zeroization
5. Design for HSM/secure element key storage
6. Document physical security requirements for deployment

### Architecture Decision ID: `TERAS-ARCH-D07-PHYSICAL-001`

---

# D-08: Hardware Random Number Generators

## 1. TRNG Architectures

### 1.1 Entropy Sources

```
┌─────────────────────────────────────────────────────────────────────┐
│                    TRNG Entropy Sources                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  PHYSICAL SOURCES:                                                  │
│  ─────────────────                                                  │
│  ├── Thermal noise: Johnson-Nyquist noise in resistors             │
│  ├── Shot noise: Random electron flow in semiconductors            │
│  ├── Metastability: Flip-flop settling time variation              │
│  ├── Ring oscillator jitter: Phase noise in oscillators            │
│  ├── Radioactive decay: Truly random quantum events                │
│  └── Quantum effects: Photon polarization, vacuum fluctuations     │
│                                                                     │
│  COMMON IMPLEMENTATIONS:                                            │
│  ───────────────────────                                            │
│  ├── Intel RDRAND: CSPRNG seeded by entropy source                 │
│  │   └── NOT raw entropy: Output is conditioned                    │
│  ├── Intel RDSEED: Closer to raw entropy                           │
│  │   └── May fail (CF=0) if entropy depleted                       │
│  ├── ARM TRNG: Implementation-defined source                       │
│  └── TPM RNG: Hardware RNG in TPM chip                             │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 RDRAND/RDSEED Architecture

```
Intel DRNG (Digital Random Number Generator):

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  ┌─────────────────┐     ┌─────────────────┐     ┌──────────────┐  │
│  │ Entropy Source  │────►│  Conditioner    │────►│    CSPRNG    │  │
│  │ (Thermal noise) │     │ (AES-CBC-MAC)   │     │ (AES-CTR)    │  │
│  └─────────────────┘     └─────────────────┘     └──────┬───────┘  │
│                                     │                    │          │
│                                     │                    ▼          │
│                               RDSEED output         RDRAND output   │
│                                                                     │
│  RDRAND:                                                            │
│  ├── Always succeeds (waits if necessary)                          │
│  ├── Output is CSPRNG output                                       │
│  ├── Reseeded from conditioner periodically                        │
│  └── Suitable for key generation                                   │
│                                                                     │
│  RDSEED:                                                            │
│  ├── May fail if entropy depleted                                  │
│  ├── Output is conditioned entropy                                 │
│  ├── Suitable for seeding other CSPRNGs                            │
│  └── Use retry loop with back-off                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.3 RNG Vulnerabilities

```
VULNERABILITY CLASS: Hardware Issues
├── Insufficient entropy: Weak noise source
├── Biased output: Statistical non-uniformity
├── Predictable patterns: Correlations in output
├── Hardware failure: Silent RNG failure
└── Backdoor concerns: Potential for weakened implementations

VULNERABILITY CLASS: Implementation Issues
├── RDRAND underflow: AMD Ryzen bug returned 0xFFFFFFFF
├── VM entropy starvation: Multiple VMs deplete pool
├── Boot-time weakness: Insufficient entropy early in boot
└── Fork issues: Child processes share RNG state

Mitigation:
├── Multiple entropy sources: Don't rely on single source
├── Health testing: Continuous RNG output validation
├── Entropy estimation: Track available randomness
├── NIST SP 800-90B: Entropy source validation standard
└── Conditioning: Always post-process raw entropy
```

## 2. Entropy Collection

### 2.1 Linux Random Subsystem

```
Linux /dev/random Architecture:

┌─────────────────────────────────────────────────────────────────────┐
│                    Entropy Sources                                   │
│  ├── RDRAND/RDSEED (if available)                                  │
│  ├── Interrupt timing                                              │
│  ├── Disk timing                                                   │
│  ├── Human input (keyboard, mouse)                                 │
│  └── virtio-rng (VMs)                                              │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    CRNG (Cryptographic RNG)                          │
│  ├── ChaCha20 stream cipher                                        │
│  ├── Reseeded when entropy available                               │
│  └── Fast extraction from pool                                     │
└─────────────────────────────────────────────────────────────────────┘
                              │
                              ▼
         ┌────────────────────┴────────────────────┐
         │                                         │
    /dev/random                              /dev/urandom
    (blocks if no entropy,                   (never blocks,
     but same CRNG since 5.6)                always available)
```

## TERAS Decision D-08

**FOR TERAS:**
1. Use hardware RNG (RDRAND/RDSEED) when available
2. Always combine multiple entropy sources
3. Implement continuous health testing
4. Use CSPRNG with hardware seed
5. Handle RNG failures gracefully
6. Document entropy requirements for each operation

### Architecture Decision ID: `TERAS-ARCH-D08-RNG-001`

---

# D-09: Secure Coprocessors and Enclaves

## 1. Apple Secure Enclave

### 1.1 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Apple Secure Enclave                              │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    Application Processor                       │ │
│  │  ┌─────────────────────────────────────────────────────────┐  │ │
│  │  │                      iOS/macOS                           │  │ │
│  │  │  ┌────────────┐  ┌────────────┐  ┌────────────┐         │  │ │
│  │  │  │ Keychain   │  │ Face ID    │  │ Apple Pay  │         │  │ │
│  │  │  │ Services   │  │            │  │            │         │  │ │
│  │  │  └─────┬──────┘  └─────┬──────┘  └─────┬──────┘         │  │ │
│  │  │        └───────────────┼───────────────┘                │  │ │
│  │  │                        │                                 │  │ │
│  │  │                  SEP Requests                            │  │ │
│  │  └────────────────────────┼─────────────────────────────────┘  │ │
│  └───────────────────────────┼───────────────────────────────────┘ │
│                              │                                      │
│  ════════════════════════════│══════════════════════════════════   │
│                              ▼                                      │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │              Secure Enclave Processor (SEP)                    │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │ │
│  │  │ SEP OS      │  │ Secure Key  │  │ Hardware Crypto     │   │ │
│  │  │ (SEPOS)     │  │ Store       │  │ Engine              │   │ │
│  │  │             │  │             │  │ - AES               │   │ │
│  │  │ Dedicated   │  │ UID: Never  │  │ - PKA (Public Key)  │   │ │
│  │  │ L4 kernel   │  │ leaves SEP  │  │ - TRNG              │   │ │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │ │
│  │                                                               │ │
│  │  Anti-Replay: Secure counter, tamper-evident storage         │ │
│  │  Secure Boot: Separate from AP boot chain                    │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘

Key Features:
├── UID (Unique ID): Device-specific key, fused at manufacture
├── GID (Group ID): Device class key
├── Hardware memory protection from AP
├── Dedicated boot ROM and secure boot
└── Anti-rollback counters for updates
```

### 1.2 SEP Security Services

```
Services Provided:
├── Touch ID / Face ID: Biometric template storage and matching
├── Apple Pay: Payment credential protection
├── Keychain: Key hierarchy rooted in SEP
├── Disk Encryption: File encryption key protection
├── Passcode Verification: Rate limiting and wipe on excessive failures
└── Secure Neural Engine: ML model protection (A14+)
```

## 2. Google Titan / Android StrongBox

### 2.1 Architecture

```
Google Titan M2:
├── Purpose-built security chip
├── ARM Cortex-M3 core
├── Separate from main SoC
├── Hardware crypto: RSA, ECC, AES, SHA
├── TRNG
└── Tamper detection

Android StrongBox:
├── Hardware-backed keystore
├── Isolated from main processor
├── Key generation in hardware
├── No key export
└── User authentication binding

KeyMint (Android 12+):
├── Modern Keymaster replacement
├── Remote key provisioning
├── Attestation improvements
└── Better key use authorization
```

## 3. Microsoft Pluton

### 3.1 Architecture

```
Microsoft Pluton:
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  Traditional: ─────┬───── Firmware ─────┬───── TPM (Discrete)      │
│               Bus attack surface                                    │
│                                                                     │
│  Pluton:     ┌─────────────────────────────────────────────┐       │
│              │                   CPU                        │       │
│              │  ┌──────────────────────────────────────┐   │       │
│              │  │            Pluton                     │   │       │
│              │  │  - Security processor core           │   │       │
│              │  │  - Crypto accelerators               │   │       │
│              │  │  - Secure storage                    │   │       │
│              │  │  - Direct CPU integration            │   │       │
│              │  │  - No external bus exposure          │   │       │
│              │  └──────────────────────────────────────┘   │       │
│              └─────────────────────────────────────────────┘       │
│                                                                     │
│  Benefits:                                                          │
│  ├── No physical bus to attack                                     │
│  ├── Firmware updates via Windows Update                           │
│  ├── TPM 2.0 compatible                                            │
│  └── Additional features beyond TPM                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## TERAS Decision D-09

**FOR TERAS:**
1. Support secure coprocessors where available
2. Abstract secure element interface
3. Use platform security features appropriately
4. Implement fallback for systems without SE
5. Document security level requirements
6. Leverage mobile secure enclaves for MENARA

### Architecture Decision ID: `TERAS-ARCH-D09-SECCOPRO-001`

---

# D-10: Hardware Vulnerability Classes

## 1. Microarchitectural Attacks (Comprehensive)

### 1.1 Spectre Family

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Spectre Vulnerability Family                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Spectre v1 (Bounds Check Bypass) - CVE-2017-5753                   │
│  ──────────────────────────────────────────────────                 │
│  if (x < array1_size)                                               │
│      y = array2[array1[x] * 256];  // Speculative access            │
│                                                                     │
│  Spectre v2 (Branch Target Injection) - CVE-2017-5715               │
│  ─────────────────────────────────────────────────────              │
│  Attacker trains branch predictor to mispredict indirect branches   │
│  Victim speculatively executes attacker-chosen gadget               │
│                                                                     │
│  Spectre v3 (Meltdown) - CVE-2017-5754                              │
│  ─────────────────────────────────────                              │
│  User-mode speculative read of kernel memory                        │
│  Exception deferred until retirement                                │
│                                                                     │
│  Spectre v3a (Rogue System Register Read)                           │
│  ─────────────────────────────────────────                          │
│  Speculative read of system registers                               │
│                                                                     │
│  Spectre v4 (Speculative Store Bypass) - CVE-2018-3639              │
│  ────────────────────────────────────────────────────               │
│  Store-to-load forwarding speculates around store                   │
│                                                                     │
│  Spectre-BHB (Branch History Buffer) - 2022                         │
│  ──────────────────────────────────────────                         │
│  BHB poisoning bypasses some v2 mitigations                         │
│                                                                     │
│  Spectre-RSB (Return Stack Buffer)                                  │
│  ─────────────────────────────────                                  │
│  RSB pollution leads to mispredicted returns                        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 MDS (Microarchitectural Data Sampling)

```
RIDL (Rogue In-Flight Data Load):
├── Leak data from line fill buffers
└── CVE-2018-12126 (MFBDS), CVE-2018-12127 (MLPDS)

Fallout:
├── Leak data from store buffers
└── CVE-2018-12130 (MSBDS)

ZombieLoad:
├── Leak data from load ports
├── Cross-hyperthread attack
└── CVE-2019-11091 (MDSUM)

TAA (TSX Asynchronous Abort):
├── Leak data during TSX abort
└── CVE-2019-11135

Mitigations:
├── MDS_NO: Hardware indication of immunity
├── VERW: Clear CPU buffers
├── Hyperthreading disable: Eliminate cross-thread attacks
└── Microcode updates: Partial mitigations
```

### 1.3 Other Microarchitectural Vulnerabilities

```
Foreshadow (L1 Terminal Fault):
├── L1TF: CVE-2018-3615 (SGX), CVE-2018-3620 (OS), CVE-2018-3646 (VMM)
├── Bypass L1 cache checks
├── Complete SGX break
└── Mitigation: PTE inversion, flush L1 on VM entry

CacheOut / L1DES:
├── CVE-2020-0549
├── Leak data from evicted cache lines
└── Mitigation: Microcode updates

VRS (Vector Register Sampling):
├── CVE-2020-0548
├── Leak SIMD register contents
└── Mitigation: Clear vector registers

SRBDS (Special Register Buffer Data Sampling):
├── CVE-2020-0543 (CrossTalk)
├── Leak data across cores via staging buffer
└── Affects: RDRAND, RDSEED, EGETKEY

LVI (Load Value Injection):
├── CVE-2020-0551
├── Inject values into victim's loads
├── Reverse of Meltdown-style attacks
└── Complex exploitation

ÆPIC Leak:
├── Read uninitialized data from APIC registers
├── Affects SGX: leak enclave data
└── CVE-2022-21233

Downfall (GDS - Gather Data Sampling):
├── CVE-2022-40982
├── AVX2/AVX-512 gather instructions leak data
└── Significant performance impact from mitigation

Inception (TTE - Transient Execution Training):
├── CVE-2023-20569 (AMD)
├── Train branch predictor for RAS manipulation
└── Phantom speculation attacks

Zenbleed:
├── CVE-2023-20593 (AMD Zen 2)
├── Leak data from XMM/YMM registers
├── Fast cross-process attack
└── Microcode fix available
```

## 2. Rowhammer

### 2.1 Attack Mechanism

```
┌─────────────────────────────────────────────────────────────────────┐
│                    DRAM Rowhammer Attack                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  DRAM Structure:                                                    │
│  ├── Rows of capacitor cells                                       │
│  ├── Cells lose charge over time (refresh needed)                  │
│  └── Adjacent rows share physical proximity                        │
│                                                                     │
│  Attack:                                                            │
│  ┌─────────┐     ┌─────────┐     ┌─────────┐                       │
│  │ Row N-1 │     │ Row N-1 │     │ Row N-1 │ ← Victim row          │
│  ├─────────┤     ├─────────┤     ├─────────┤                       │
│  │  Row N  │ ──► │  Row N  │ ──► │  Row N  │ ← Hammer (activate)   │
│  ├─────────┤     ├─────────┤     ├─────────┤                       │
│  │ Row N+1 │     │ Row N+1 │     │ Row N+1 │ ← Victim row          │
│  └─────────┘     └─────────┘     └─────────┘                       │
│                                                                     │
│  Repeated activation of Row N causes bit flips in N-1 and N+1      │
│                                                                     │
│  Exploitation:                                                      │
│  ├── Privilege escalation: Flip bits in page tables                │
│  ├── Sandbox escape: Flip bits in security metadata                │
│  ├── VM escape: Flip bits in hypervisor structures                 │
│  └── RSA key recovery: Flip bits in key data                       │
│                                                                     │
│  Variants:                                                          │
│  ├── Single-sided: Hammer one row                                  │
│  ├── Double-sided: Hammer rows on both sides                       │
│  ├── One-location: Single cache line hammer                        │
│  ├── TRRespass: Bypass Target Row Refresh                          │
│  └── Half-Double: Three-row pattern                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘

Mitigations:
├── ECC memory: Detect single-bit flips (but not multi-bit)
├── Target Row Refresh (TRR): Hardware mitigation (often bypassable)
├── PARA: Probabilistic Adjacent Row Activation
├── Memory isolation: Prevent attacker control over physical addresses
└── Refresh rate increase: Performance cost
```

## 3. PLATYPUS and Power Side Channels

```
PLATYPUS (Power Leakage Attacks):
├── Read Intel RAPL (Running Average Power Limit) counters
├── Infer execution patterns from power consumption
├── Extract AES keys from SGX enclaves
└── Mitigation: Restrict RAPL access

Hertzbleed:
├── Frequency scaling reveals data-dependent operations
├── Remote timing attack via frequency changes
├── P-state variations leak information
└── Mitigation: Constant-time implementation
```

## TERAS Decision D-10

**FOR TERAS:**
1. Implement constant-time cryptography
2. Avoid secret-dependent branches/memory access
3. Monitor for new microarchitectural vulnerabilities
4. Enable available hardware mitigations
5. Design for defense-in-depth against speculation
6. Document hardware requirements for secure operation

### Architecture Decision ID: `TERAS-ARCH-D10-HWVULN-001`

---

# D-11: Hardware Root of Trust

## 1. Root of Trust Concepts

### 1.1 Trust Anchor Hierarchy

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Hardware Root of Trust Hierarchy                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│                    ┌─────────────────────┐                          │
│                    │   Hardware RoT      │                          │
│                    │   (CPU/TPM/HSM)     │                          │
│                    │   ┌─────────────┐   │                          │
│                    │   │ Root Keys   │   │                          │
│                    │   │ (Fused/OTP) │   │                          │
│                    │   └─────────────┘   │                          │
│                    └─────────┬───────────┘                          │
│                              │                                      │
│                              ▼                                      │
│                    ┌─────────────────────┐                          │
│                    │   Firmware RoT      │                          │
│                    │   (Boot ROM/ACM)    │                          │
│                    │   Signed by HW Key  │                          │
│                    └─────────┬───────────┘                          │
│                              │                                      │
│                              ▼                                      │
│                    ┌─────────────────────┐                          │
│                    │   Software RoT      │                          │
│                    │   (Bootloader/BIOS) │                          │
│                    │   Verified by FW    │                          │
│                    └─────────┬───────────┘                          │
│                              │                                      │
│                              ▼                                      │
│                    ┌─────────────────────┐                          │
│                    │   Application RoT   │                          │
│                    │   (OS/Apps)         │                          │
│                    │   Verified by SW    │                          │
│                    └─────────────────────┘                          │
│                                                                     │
│  Chain of Trust: Each layer measures/verifies the next             │
│  Compromise: Any break in chain compromises all downstream         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Root of Trust Types

```
Root of Trust for Storage (RTS):
├── Secure storage of secrets
├── Key hierarchy anchored in hardware
├── Sealing/unsealing to platform state
└── Examples: TPM NVRAM, Secure Enclave keystore

Root of Trust for Measurement (RTM):
├── Measure code/data before execution
├── Extend measurements to PCRs
├── Enable attestation of platform state
└── Examples: TPM PCRs, SGX MRENCLAVE

Root of Trust for Reporting (RTR):
├── Sign attestation reports
├── Prove platform identity
├── Remote verification of platform state
└── Examples: TPM EK, SGX EPID/DCAP

Root of Trust for Update (RTU):
├── Authenticate firmware updates
├── Prevent rollback attacks
├── Secure version management
└── Examples: Secure Boot, TPM counter
```

## 2. Device Identity

### 2.1 Hardware Attestation

```
Device Identity Composition Engine (DICE):
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  UDS (Unique Device Secret)                                        │
│       │                                                             │
│       ▼                                                             │
│  CDI (Compound Device Identifier)                                  │
│  = KDF(UDS, Hash(First Mutable Code))                              │
│       │                                                             │
│       ▼                                                             │
│  Cert Chain: CDI → Layer 1 → Layer 2 → ... → Application           │
│                                                                     │
│  Each layer:                                                        │
│  1. Derives keys from parent CDI + measurement                     │
│  2. Creates certificate for next layer                             │
│  3. Erases parent CDI from memory                                  │
│                                                                     │
│  Benefits:                                                          │
│  ├── Unique identity per device                                    │
│  ├── Identity includes all firmware                                │
│  ├── Key rotation on firmware update                               │
│  └── Standardized (TCG DICE spec)                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. Secure Key Provisioning

### 3.1 Key Injection

```
Manufacturing Key Injection:
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  Option 1: Factory Injection                                        │
│  ──────────────────────────                                         │
│  ├── Key generated in secure facility                              │
│  ├── Injected via programming interface                            │
│  ├── Key escrow for recovery                                       │
│  └── Risk: Supply chain compromise                                 │
│                                                                     │
│  Option 2: On-Device Generation                                     │
│  ─────────────────────────────                                      │
│  ├── Device generates own key                                      │
│  ├── Public key extracted for registration                         │
│  ├── Private key never leaves device                               │
│  └── Preferred for high-security applications                      │
│                                                                     │
│  Option 3: Key Agreement                                            │
│  ───────────────────────                                            │
│  ├── Device and server perform key agreement                       │
│  ├── Shared secret derived                                         │
│  └── Forward secrecy possible                                      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## TERAS Decision D-11

**FOR TERAS:**
1. Leverage hardware root of trust where available
2. Implement DICE-style layered identity
3. Support multiple attestation schemes
4. Design for devices without hardware RoT (software fallback)
5. Document trust assumptions clearly
6. Implement secure key provisioning

### Architecture Decision ID: `TERAS-ARCH-D11-ROT-001`

---

# D-12: Peripheral and Bus Security

## 1. PCIe Security

### 1.1 PCIe DMA Attacks

```
┌─────────────────────────────────────────────────────────────────────┐
│                    PCIe DMA Attack Surface                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Attack Vectors:                                                    │
│  ├── Malicious PCIe device (hardware implant)                      │
│  ├── Compromised firmware on legitimate device                     │
│  ├── Thunderbolt/USB4 (PCIe tunneling)                             │
│  ├── FireWire (legacy, still exploitable)                          │
│  └── ExpressCard/CardBus                                           │
│                                                                     │
│  Attack Capabilities:                                               │
│  ├── Read arbitrary physical memory                                │
│  ├── Write arbitrary physical memory                               │
│  ├── Bypass CPU memory protections                                 │
│  ├── Inject code into kernel                                       │
│  └── Extract encryption keys                                       │
│                                                                     │
│  Tools:                                                             │
│  ├── PCILeech: Open-source DMA attack framework                    │
│  ├── Inception: Firewire/Thunderbolt attack tool                   │
│  └── LAN Turtle: Network-based physical access                     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘

Mitigations:
├── IOMMU (VT-d/AMD-Vi): Restrict device memory access
├── Kernel DMA Protection: Pre-boot IOMMU configuration
├── Thunderbolt security levels: User authorization
├── Device authentication: Cryptographic device identity
└── Physical port blocking: Disable unused interfaces
```

## 2. USB Security

### 2.1 USB Attack Classes

```
BadUSB:
├── Reprogram USB device firmware
├── Present as different device class (HID, storage)
├── Keyboard emulation for command injection
└── No signature verification on USB firmware

USB Rubber Ducky / Malicious HID:
├── Appears as keyboard
├── Injects keystrokes rapidly
├── Payload execution via typing
└── Bypasses most security software

USB Killer:
├── Physical damage via voltage spike
├── Capacitor charge/discharge
└── Hardware destruction

USB Armory / LAN Turtle:
├── Full computer in USB form factor
├── Network attacks via USB Ethernet
└── Man-in-the-middle capabilities

Mitigations:
├── USBGuard (Linux): Device whitelisting
├── USB Restricted Mode (iOS): Limit USB after lock
├── USB device authentication (USB 3.x)
├── Physical port sealing
└── USB filtering policies
```

## 3. Network Interface Security

### 3.1 BMC/IPMI Attacks

```
Baseboard Management Controller Risks:
├── Separate processor with network access
├── Operates independently of main OS
├── Often poor security practices
│   ├── Default credentials
│   ├── Unpatched firmware
│   └── Cleartext protocols
├── Full system access
│   ├── Remote console (KVM)
│   ├── Power control
│   ├── Firmware updates
│   └── Memory access (via PCIe)
└── Difficult to monitor from host OS

Mitigation:
├── Dedicated management network (physically isolated)
├── Strong BMC credentials
├── Firmware updates
├── Disable if not needed
└── Monitor BMC audit logs
```

## TERAS Decision D-12

**FOR TERAS:**
1. Require IOMMU for DMA protection
2. Implement USB device policy enforcement
3. Document peripheral security requirements
4. Design for untrusted peripheral assumption
5. Support BMC security monitoring
6. Audit peripheral access in TERAS logs

### Architecture Decision ID: `TERAS-ARCH-D12-PERIPH-001`

---

# D-13: Embedded and IoT Hardware Security

## 1. Embedded Security Challenges

### 1.1 Constraints

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Embedded Security Constraints                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Resource Constraints:                                              │
│  ├── Limited CPU: MHz vs GHz                                       │
│  ├── Limited RAM: KB vs GB                                         │
│  ├── Limited storage: KB-MB vs GB-TB                               │
│  ├── Limited power: mW vs W                                        │
│  └── No hardware crypto acceleration                               │
│                                                                     │
│  Physical Exposure:                                                 │
│  ├── Devices deployed in hostile environments                      │
│  ├── Physical access assumed                                       │
│  ├── No tamper-resistant enclosure                                 │
│  └── Debug interfaces often accessible                             │
│                                                                     │
│  Update Challenges:                                                 │
│  ├── No network connectivity (some devices)                        │
│  ├── Limited update mechanisms                                     │
│  ├── Bricking risk                                                 │
│  └── Long deployment lifetime (10+ years)                          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Secure Boot for Embedded

```
Embedded Secure Boot Options:

MCU with Built-in Security:
├── ARM Cortex-M33/M35P with TrustZone-M
├── Secure boot ROM
├── Secure key storage (OTP)
├── Hardware crypto
└── Examples: STM32L5, LPC55, nRF5340

External Secure Element:
├── ATECC608: Crypto authentication
├── STSAFE: Secure element
├── SE050: EdgeLock
└── Provides: Key storage, crypto, attestation

Software-Only:
├── Verified boot chain
├── Signature verification
├── Limited without hardware support
└── Vulnerable to physical attacks
```

## 2. Lightweight Cryptography

### 2.1 NIST Lightweight Crypto

```
NIST Lightweight Cryptography Competition Winner:

ASCON (Selected 2023):
├── Permutation-based design
├── AEAD: Ascon-128, Ascon-128a
├── Hashing: Ascon-Hash, Ascon-Hasha
├── Small code/state size
├── Good performance on constrained devices
└── Resistance to side-channel attacks

Other Lightweight Primitives:
├── PRESENT: Block cipher (64-bit block)
├── SIMON/SPECK: NSA lightweight ciphers
├── PHOTON: Lightweight hash function
├── GRAIN-128: Stream cipher
└── CHASKEY: MAC for microcontrollers
```

## TERAS Decision D-13

**FOR TERAS:**
1. Support constrained device deployments (MENARA)
2. Implement lightweight crypto options
3. Design for limited hardware security
4. Support secure boot where available
5. Plan for long device lifetimes
6. Document minimum hardware requirements

### Architecture Decision ID: `TERAS-ARCH-D13-EMBEDDED-001`

---

# D-14: Supply Chain Security

## 1. Hardware Supply Chain Threats

### 1.1 Threat Model

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Hardware Supply Chain Threats                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Design Phase:                                                      │
│  ├── Malicious IP cores                                            │
│  ├── Hardware trojans in HDL                                       │
│  ├── Backdoored EDA tools                                          │
│  └── Compromised design specifications                             │
│                                                                     │
│  Fabrication Phase:                                                 │
│  ├── Unauthorized modifications at foundry                         │
│  ├── Overproduction and grey market                                │
│  ├── Hardware trojans inserted during fab                          │
│  └── Quality control bypass                                        │
│                                                                     │
│  Assembly/Test Phase:                                               │
│  ├── Component substitution (counterfeit)                          │
│  ├── Firmware tampering                                            │
│  ├── Additional components added                                   │
│  └── Test interface left enabled                                   │
│                                                                     │
│  Distribution Phase:                                                │
│  ├── Interception and modification                                 │
│  ├── Repackaging with malware                                      │
│  ├── Firmware updates during transit                               │
│  └── Supply chain interdiction (nation-state)                      │
│                                                                     │
│  Operational Phase:                                                 │
│  ├── Malicious firmware updates                                    │
│  ├── Compromised support tools                                     │
│  └── Social engineering of operators                               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Counterfeit Detection

```
Detection Methods:
├── Visual inspection: Package markings, quality
├── X-ray imaging: Internal structure verification
├── Electrical testing: Parameter verification
├── Decapsulation: Die inspection
├── DNA marking: Unique identifiers
└── Cryptographic authentication: Device certificates

Authentication:
├── Platform Certificate: TPM-based device identity
├── Secure device identity: DICE, SPDM
├── Supply chain tracking: Blockchain-based provenance
└── Component authentication: Chip-level crypto
```

## 2. Trusted Computing Infrastructure

### 2.1 TCG Standards

```
Trusted Computing Group Standards:

TPM (Trusted Platform Module):
├── TPM 2.0 Library Specification
├── PC Client Platform TPM Profile
├── Mobile TPM Profile
└── Server TPM Profile

Device Identity:
├── DICE: Device Identifier Composition Engine
├── Platform Certificates
└── Endorsement Key hierarchies

Firmware Integrity:
├── TCG PC Client Firmware Integrity Measurement
├── Reference Integrity Manifest (RIM)
└── TCG Firmware Update Specification

Network Security:
├── TNC (Trusted Network Connect)
├── IF-MAP: Security Metadata Access Protocol
└── Platform Trust Services
```

## TERAS Decision D-14

**FOR TERAS:**
1. Document hardware provenance requirements
2. Support supply chain attestation
3. Implement device authentication
4. Design for untrusted hardware assumption
5. Support hardware allow-listing
6. Integrate with supply chain security tools

### Architecture Decision ID: `TERAS-ARCH-D14-SUPPLY-001`

---

# D-15: Hardware Security Integration for TERAS

## 1. TERAS Hardware Security Architecture

### 1.1 Integrated Design

```
┌─────────────────────────────────────────────────────────────────────┐
│                    TERAS Hardware Security Integration               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                    TERAS Application                           │ │
│  │  ┌─────────────────────────────────────────────────────────┐  │ │
│  │  │              Hardware Abstraction Layer                  │  │ │
│  │  │  ┌───────────┐ ┌───────────┐ ┌───────────┐ ┌─────────┐ │  │ │
│  │  │  │  TEE      │ │    TPM    │ │   HSM     │ │  CPU    │ │  │ │
│  │  │  │  Adapter  │ │  Adapter  │ │  Adapter  │ │ Adapter │ │  │ │
│  │  │  │ ─────────│ │ ─────────│ │ ─────────│ │─────────│ │  │ │
│  │  │  │ SGX      │ │ TPM2-TSS  │ │ PKCS#11  │ │ RDRAND  │ │  │ │
│  │  │  │ TrustZone│ │ fTPM     │ │ CloudHSM │ │ CET     │ │  │ │
│  │  │  │ SEV      │ │           │ │          │ │ PAC/MTE │ │  │ │
│  │  │  └───────────┘ └───────────┘ └───────────┘ └─────────┘ │  │ │
│  │  └─────────────────────────────────────────────────────────┘  │ │
│  │                              │                                 │ │
│  │  ┌───────────────────────────▼───────────────────────────────┐│ │
│  │  │              Security Policy Engine                        ││ │
│  │  │  - Feature detection                                       ││ │
│  │  │  - Fallback selection                                      ││ │
│  │  │  - Security level enforcement                              ││ │
│  │  │  - Attestation verification                                ││ │
│  │  └───────────────────────────────────────────────────────────┘│ │
│  └───────────────────────────────────────────────────────────────┘ │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Security Level Mapping

```
TERAS Security Levels Based on Hardware:

LEVEL 5 (Highest - Nation State Resistant):
├── Hardware Requirements:
│   ├── HSM (FIPS 140-2 Level 3+)
│   ├── Discrete TPM 2.0
│   ├── TEE (SGX/TrustZone)
│   ├── Hardware memory encryption
│   └── CET/PAC enabled
├── Use Case: Critical infrastructure, defense
└── Products: SANDI (highest tier), BENTENG (government)

LEVEL 4 (High - Enterprise):
├── Hardware Requirements:
│   ├── TPM 2.0 (discrete or firmware)
│   ├── Hardware crypto acceleration
│   ├── IOMMU enabled
│   └── Secure Boot
├── Use Case: Enterprise security
└── Products: GAPURA, ZIRAH enterprise tier

LEVEL 3 (Medium - Commercial):
├── Hardware Requirements:
│   ├── Secure Boot
│   ├── ASLR/DEP/NX
│   ├── Hardware RNG
│   └── Basic TEE (TrustZone)
├── Use Case: Commercial applications
└── Products: MENARA, standard deployments

LEVEL 2 (Basic - Consumer):
├── Hardware Requirements:
│   ├── DEP/NX
│   ├── Software RNG with OS entropy
│   └── Basic memory protection
├── Use Case: Consumer applications
└── Products: MENARA consumer tier

LEVEL 1 (Minimal - Legacy):
├── Hardware: Any (best effort)
├── Warning: Security significantly reduced
└── Not recommended for production
```

### 1.3 Feature Detection and Fallback

```rust
// TERAS hardware security feature detection
pub struct HardwareSecurityProfile {
    tee: TeeSupport,
    tpm: TpmSupport,
    hsm: Option<HsmConfig>,
    cpu_features: CpuSecurityFeatures,
    memory_protection: MemoryProtection,
    rng: RngSource,
}

impl HardwareSecurityProfile {
    pub fn detect() -> Self {
        HardwareSecurityProfile {
            tee: TeeSupport::detect(),
            tpm: TpmSupport::detect(),
            hsm: HsmConfig::detect(),
            cpu_features: CpuSecurityFeatures::detect(),
            memory_protection: MemoryProtection::detect(),
            rng: RngSource::detect(),
        }
    }
    
    pub fn security_level(&self) -> SecurityLevel {
        // Determine highest achievable security level
        if self.hsm.is_some() && self.tee.has_sgx() && self.tpm.is_discrete() {
            SecurityLevel::Level5
        } else if self.tpm.is_available() && self.cpu_features.has_crypto_accel() {
            SecurityLevel::Level4
        } else if self.tee.has_basic() && self.rng.is_hardware() {
            SecurityLevel::Level3
        } else if self.cpu_features.has_dep_nx() {
            SecurityLevel::Level2
        } else {
            SecurityLevel::Level1
        }
    }
    
    pub fn select_key_storage(&self) -> KeyStorageBackend {
        if let Some(hsm) = &self.hsm {
            KeyStorageBackend::Hsm(hsm.clone())
        } else if self.tee.has_sgx() {
            KeyStorageBackend::SgxSealing
        } else if self.tee.has_trustzone() {
            KeyStorageBackend::TrustZone
        } else if self.tpm.is_available() {
            KeyStorageBackend::TpmSealing
        } else {
            KeyStorageBackend::Software
        }
    }
}
```

## 2. Product-Specific Hardware Integration

### 2.1 Product Requirements

```
MENARA (Mobile Security):
├── ARM TrustZone required
├── Secure Element preferred
├── Hardware-backed keystore (Android/iOS)
├── Biometric integration (TEE)
└── Attestation: SafetyNet/App Attest

GAPURA (WAF):
├── Server-grade hardware
├── Hardware AES-NI for TLS
├── RDRAND for session tokens
├── Optional HSM for key management
└── High-throughput crypto

ZIRAH (EDR):
├── TPM for measured boot
├── CET/PAC for exploit mitigation
├── Hardware perf counters for anomaly detection
├── IOMMU for device isolation
└── Memory encryption for forensic protection

BENTENG (eKYC):
├── HSM for identity key protection
├── TEE for biometric processing
├── Secure Element for credential storage
├── Hardware attestation for device binding
└── Tamper detection integration

SANDI (Digital Signatures):
├── HSM required for signing keys
├── TPM for audit logging integrity
├── Timestamping hardware
├── FIPS 140-2 Level 3 minimum
└── Air-gapped HSM option
```

## TERAS Decision D-15

**FOR TERAS:**
1. Implement hardware abstraction layer
2. Support graceful degradation
3. Document hardware requirements per security level
4. Provide detection and configuration tools
5. Integrate attestation across all products
6. Maintain hardware compatibility matrix

### Architecture Decision ID: `TERAS-ARCH-D15-INTEGRATE-001`

---

# Domain D Summary: Hardware Security

| Session | Topic | Decision ID |
|---------|-------|-------------|
| D-01 | TEE Foundations | TERAS-ARCH-D01-TEE-001 |
| D-02 | TPM | TERAS-ARCH-D02-TPM-001 |
| D-03 | HSM | TERAS-ARCH-D03-HSM-001 |
| D-04 | Secure Boot | TERAS-ARCH-D04-BOOT-001 |
| D-05 | Memory Protection | TERAS-ARCH-D05-MEMPROT-001 |
| D-06 | CPU Security | TERAS-ARCH-D06-CPUSEC-001 |
| D-07 | Physical Security | TERAS-ARCH-D07-PHYSICAL-001 |
| D-08 | Hardware RNG | TERAS-ARCH-D08-RNG-001 |
| D-09 | Secure Coprocessors | TERAS-ARCH-D09-SECCOPRO-001 |
| D-10 | Hardware Vulnerabilities | TERAS-ARCH-D10-HWVULN-001 |
| D-11 | Hardware Root of Trust | TERAS-ARCH-D11-ROT-001 |
| D-12 | Peripheral Security | TERAS-ARCH-D12-PERIPH-001 |
| D-13 | Embedded Security | TERAS-ARCH-D13-EMBEDDED-001 |
| D-14 | Supply Chain | TERAS-ARCH-D14-SUPPLY-001 |
| D-15 | Integration | TERAS-ARCH-D15-INTEGRATE-001 |

## Key Findings

1. **No hardware security feature is perfect** - all have vulnerabilities
2. **Defense in depth is essential** - combine multiple hardware features
3. **Side-channels are universal** - affect all TEE/secure processor designs
4. **Physical access changes everything** - design for hostile environments
5. **Hardware abstraction is critical** - support varying security levels

## DOMAIN D: COMPLETE

---

*Research Track Output — Domain D: Hardware Security*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
