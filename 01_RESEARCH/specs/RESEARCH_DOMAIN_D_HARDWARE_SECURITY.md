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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                        SGX Architecture                              â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                    Untrusted Application                     â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚                    Enclave                           â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â”‚ Trusted Codeâ”‚  â”‚ Sealed Data â”‚  â”‚ Attestationâ”‚   â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚    â”‚   â”‚
â”‚  â”‚  â”‚                                                      â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  Protected by: EPC (Enclave Page Cache)             â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  Encrypted with: MEE (Memory Encryption Engine)     â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  Ring 0: OS/Hypervisor (UNTRUSTED from enclave perspective)        â”‚
â”‚  Hardware: CPU Package (Trust Anchor)                               â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 SGX Instructions

```
ENCLAVE LIFECYCLE:
â”œâ”€â”€ ECREATE    - Create enclave control structure
â”œâ”€â”€ EADD       - Add pages to enclave
â”œâ”€â”€ EEXTEND    - Measure page contents
â”œâ”€â”€ EINIT      - Initialize enclave (verify SIGSTRUCT)
â”œâ”€â”€ EENTER     - Enter enclave (ring 3 â†’ enclave)
â”œâ”€â”€ EEXIT      - Exit enclave (enclave â†’ ring 3)
â”œâ”€â”€ ERESUME    - Resume after AEX (Asynchronous Enclave Exit)
â”œâ”€â”€ EGETKEY    - Derive sealing/report keys
â”œâ”€â”€ EREPORT    - Generate attestation report
â””â”€â”€ EREMOVE    - Remove enclave page

PRIVILEGED INSTRUCTIONS (Ring 0):
â”œâ”€â”€ EBLOCK     - Block EPC page for eviction
â”œâ”€â”€ ETRACK     - Activate EBLOCK changes
â”œâ”€â”€ EWB        - Evict EPC page (encrypted to main memory)
â”œâ”€â”€ ELDB/ELDU  - Load blocked/unblocked page back
â””â”€â”€ EPA        - Add version array page
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
â”œâ”€â”€ Cache-Based
â”‚   â”œâ”€â”€ Prime+Probe: Detect enclave cache access patterns
â”‚   â”œâ”€â”€ Flush+Reload: Requires shared memory (limited in SGX)
â”‚   â””â”€â”€ Cache-Line Granularity: 64-byte resolution
â”‚
â”œâ”€â”€ Page-Table Based
â”‚   â”œâ”€â”€ Controlled-Channel: OS controls page faults
â”‚   â”œâ”€â”€ Page-fault sequences leak access patterns
â”‚   â””â”€â”€ Demonstrated: Extracting full documents, keys
â”‚
â”œâ”€â”€ Branch Prediction
â”‚   â”œâ”€â”€ Branch Target Injection (BTI/Spectre v2)
â”‚   â”œâ”€â”€ Speculative execution leaks enclave data
â”‚   â””â”€â”€ SgxPectre: Specific SGX variant
â”‚
â”œâ”€â”€ Speculative Execution
â”‚   â”œâ”€â”€ Foreshadow/L1TF: L1 cache bypass
â”‚   â”œâ”€â”€ Reads arbitrary enclave memory
â”‚   â””â”€â”€ Complete SGX break (patched, performance cost)
â”‚
â””â”€â”€ Microarchitectural
    â”œâ”€â”€ CacheOut/TAA: Transactional memory leaks
    â”œâ”€â”€ LVI: Load Value Injection
    â””â”€â”€ Ã†PIC Leak: Uninitialized APIC register read

VULNERABILITY CLASS: Software Attacks
â”œâ”€â”€ Iago Attacks: Malicious OS returns corrupted syscall results
â”œâ”€â”€ AsyncShock: Interrupt handling vulnerabilities
â”œâ”€â”€ Dark-ROP: Enclave gadget chains
â””â”€â”€ Guard's Dilemma: Cannot verify OS behavior

VULNERABILITY CLASS: Physical Attacks
â”œâ”€â”€ Cold Boot: Memory remanence (MEE mitigates)
â”œâ”€â”€ Bus Snooping: Encrypted, but patterns visible
â””â”€â”€ Fault Injection: Voltage/clock glitching
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                     ARM TrustZone Architecture                       â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”        â”‚
â”‚  â”‚      Normal World        â”‚  â”‚      Secure World         â”‚        â”‚
â”‚  â”‚                          â”‚  â”‚                           â”‚        â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚        â”‚
â”‚  â”‚  â”‚   Rich OS (Linux)  â”‚  â”‚  â”‚  â”‚  Trusted OS (OP-TEE)â”‚ â”‚        â”‚
â”‚  â”‚  â”‚   â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚  â”‚  â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚ â”‚        â”‚
â”‚  â”‚  â”‚   â”‚ Normal Apps  â”‚ â”‚  â”‚  â”‚  â”‚  â”‚ Trusted Apps  â”‚  â”‚ â”‚        â”‚
â”‚  â”‚  â”‚   â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚  â”‚  â”‚  â”‚  â”‚ (TA: DRM, Pay)â”‚  â”‚ â”‚        â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚  â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚ â”‚        â”‚
â”‚  â”‚                          â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚        â”‚
â”‚  â”‚  EL0: User              â”‚  â”‚  S-EL0: Secure User      â”‚        â”‚
â”‚  â”‚  EL1: Kernel            â”‚  â”‚  S-EL1: Secure Kernel    â”‚        â”‚
â”‚  â”‚  EL2: Hypervisor        â”‚  â”‚                           â”‚        â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜        â”‚
â”‚                                                                     â”‚
â”‚                    EL3: Secure Monitor (ATF)                        â”‚
â”‚                    â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                      â”‚
â”‚                    Handles world switching via SMC                  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

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
â”œâ”€â”€ QSEE Exploits: Multiple privilege escalation (2014-2020)
â”œâ”€â”€ Boomerang Attack: Return-oriented programming in TEE
â”œâ”€â”€ CLKSCREW: Software-controlled voltage/frequency attacks
â””â”€â”€ Trust Issues: Compromised TA can attack other TAs

VULNERABILITY CLASS: Design Limitations
â”œâ”€â”€ Single Secure World: No isolation between TAs (in basic TZ)
â”œâ”€â”€ No Remote Attestation: Standard TZ lacks attestation
â”œâ”€â”€ Vendor Dependent: Security varies by implementation
â””â”€â”€ Debug Interfaces: JTAG/SWD can compromise security

VULNERABILITY CLASS: Side-Channels
â”œâ”€â”€ Cache Attacks: Prime+Probe works across worlds
â”œâ”€â”€ TruSpy: Cross-world cache-based covert channel
â””â”€â”€ ARMageddon: Comprehensive ARM cache attack study
```

## 3. AMD SEV (Secure Encrypted Virtualization)

### 3.1 Architecture

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                        AMD SEV Architecture                          â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚                      Hypervisor (Untrusted)                    â”‚ â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚ â”‚
â”‚  â”‚  â”‚   VM 1 (SEV)    â”‚ â”‚   VM 2 (SEV)    â”‚ â”‚  VM 3 (Plain)   â”‚  â”‚ â”‚
â”‚  â”‚  â”‚   Key: K1       â”‚ â”‚   Key: K2       â”‚ â”‚   No encryption â”‚  â”‚ â”‚
â”‚  â”‚  â”‚   â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚ â”‚   â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚ â”‚                 â”‚  â”‚ â”‚
â”‚  â”‚  â”‚   â”‚Guest OS   â”‚ â”‚ â”‚   â”‚Guest OS   â”‚ â”‚ â”‚                 â”‚  â”‚ â”‚
â”‚  â”‚  â”‚   â”‚+ Apps     â”‚ â”‚ â”‚   â”‚+ Apps     â”‚ â”‚ â”‚                 â”‚  â”‚ â”‚
â”‚  â”‚  â”‚   â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚ â”‚   â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚ â”‚                 â”‚  â”‚ â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                                                                     â”‚
â”‚  AMD Secure Processor (PSP): Key management, attestation           â”‚
â”‚  Memory Encryption: AES-128 with per-VM keys                       â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

SEV Variants:
â”œâ”€â”€ SEV: Basic memory encryption
â”œâ”€â”€ SEV-ES: Encrypted State (register protection)
â””â”€â”€ SEV-SNP: Secure Nested Paging (integrity + attestation)
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
â”œâ”€â”€ SEVered: Hypervisor can remap encrypted pages
â”œâ”€â”€ No integrity protection â†’ Ciphertext manipulation
â””â”€â”€ Unencrypted VMCB â†’ Register state visible

SEV-ES:
â”œâ”€â”€ Encrypted VMSA (VM Save Area)
â”œâ”€â”€ Still vulnerable to page remapping
â””â”€â”€ Performance impact from encrypted registers

SEV-SNP:
â”œâ”€â”€ Addresses integrity with RMP
â”œâ”€â”€ Side-channel attacks still apply
â”œâ”€â”€ CacheWarp: Software-based fault attack (2023)
â””â”€â”€ Ã†PIC-like attacks on AMD
```

## 4. Intel TDX (Trust Domain Extensions)

### 4.1 Architecture

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                        Intel TDX Architecture                        â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚                    TDX Module (TCB)                            â”‚ â”‚
â”‚  â”‚  - Manages TD lifecycle                                        â”‚ â”‚
â”‚  â”‚  - Memory encryption/integrity                                 â”‚ â”‚
â”‚  â”‚  - Attestation                                                 â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                              â”‚                                      â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”       â”‚
â”‚  â”‚  Trust Domain 1 â”‚ â”‚  Trust Domain 2 â”‚ â”‚  VMX Guest      â”‚       â”‚
â”‚  â”‚  (TD Guest)     â”‚ â”‚  (TD Guest)     â”‚ â”‚  (Untrusted)    â”‚       â”‚
â”‚  â”‚  - Encrypted    â”‚ â”‚  - Encrypted    â”‚ â”‚                 â”‚       â”‚
â”‚  â”‚  - Integrity    â”‚ â”‚  - Integrity    â”‚ â”‚                 â”‚       â”‚
â”‚  â”‚  - Attested     â”‚ â”‚  - Attested     â”‚ â”‚                 â”‚       â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜       â”‚
â”‚                                                                     â”‚
â”‚  Untrusted VMM: Manages resources but cannot access TD memory      â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Key Features:
â”œâ”€â”€ Multi-key TME (Total Memory Encryption)
â”œâ”€â”€ Integrity via MAC per cache line
â”œâ”€â”€ Secure EPT (Extended Page Tables)
â””â”€â”€ Remote attestation via Intel SGX infrastructure
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                      TPM 2.0 Architecture                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                    TPM Subsystems                            â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚  Cryptographicâ”‚  â”‚   Platform    â”‚  â”‚   Credential  â”‚    â”‚   â”‚
â”‚  â”‚  â”‚   Subsystem   â”‚  â”‚ Configuration â”‚  â”‚   Management  â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  - RSA/ECC    â”‚  â”‚   Registers   â”‚  â”‚  - Keys       â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  - AES        â”‚  â”‚   (PCRs)      â”‚  â”‚  - Certs      â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  - SHA-256    â”‚  â”‚   - 24 banks  â”‚  â”‚  - Hierarchy  â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  - HMAC       â”‚  â”‚   - Extend    â”‚  â”‚               â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â”‚                                                              â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚   Random      â”‚  â”‚    Non-       â”‚  â”‚   Command     â”‚    â”‚   â”‚
â”‚  â”‚  â”‚   Number      â”‚  â”‚   Volatile    â”‚  â”‚   Execution   â”‚    â”‚   â”‚
â”‚  â”‚  â”‚   Generator   â”‚  â”‚   Storage     â”‚  â”‚   Engine      â”‚    â”‚   â”‚
â”‚  â”‚  â”‚   (RNG)       â”‚  â”‚   (NVRAM)     â”‚  â”‚               â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  Interface: FIFO/CRB over LPC/SPI/I2C                              â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Key Hierarchies:
â”œâ”€â”€ Platform Hierarchy (PH): OEM/firmware controlled
â”œâ”€â”€ Storage Hierarchy (SH): OS/user key storage
â”œâ”€â”€ Endorsement Hierarchy (EH): TPM identity, attestation
â””â”€â”€ Null Hierarchy: Session keys, ephemeral operations
```

### 1.2 Platform Configuration Registers (PCRs)

```
PCR Index | Typical Usage
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
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
- Order-dependent: Same measurements in different order â†’ different PCR
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Measured Boot Chain                               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  CPU Reset â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â–º    â”‚
â”‚       â”‚                                                             â”‚
â”‚       â–¼                                                             â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”    Measure    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”    Measure    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  CRTM   â”‚â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â–ºâ”‚  BIOS   â”‚â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â–ºâ”‚  Boot   â”‚   â”‚
â”‚  â”‚ (ACM)   â”‚    PCR[0]     â”‚         â”‚    PCR[4]     â”‚ Loader  â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜               â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜               â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚       â”‚                         â”‚                         â”‚         â”‚
â”‚       â”‚                         â”‚                         â”‚         â”‚
â”‚       â–¼                         â–¼                         â–¼         â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                         TPM PCRs                             â”‚   â”‚
â”‚  â”‚  PCR[0]: CRTM hash                                          â”‚   â”‚
â”‚  â”‚  PCR[1]: BIOS config                                        â”‚   â”‚
â”‚  â”‚  PCR[4]: Bootloader                                         â”‚   â”‚
â”‚  â”‚  PCR[8-9]: OS kernel + initrd                               â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  Attestation: TPM2_Quote signs PCR values                          â”‚
â”‚  Verification: Compare against known-good values                    â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.5 TPM Vulnerabilities

```
VULNERABILITY CLASS: Physical Attacks
â”œâ”€â”€ TPM Genie: MITM on LPC bus, intercept commands
â”œâ”€â”€ Cold Boot: Memory contains TPM session state
â”œâ”€â”€ Fault Injection: Glitch during unsealing
â””â”€â”€ ROCA (CVE-2017-15361): Weak RSA key generation in Infineon TPMs

VULNERABILITY CLASS: Software/Firmware
â”œâ”€â”€ TPM-FAIL (CVE-2019-11090): Timing attack on ECDSA
â”œâ”€â”€ fTPM vulnerabilities: AMD PSP bugs affect fTPM
â””â”€â”€ Reference implementation bugs: Various CVEs

VULNERABILITY CLASS: Design Issues
â”œâ”€â”€ Time-of-Check-Time-of-Use: Boot measurements vs. runtime
â”œâ”€â”€ Evil Maid: Physical access can modify measured components
â”œâ”€â”€ Reset attacks: Discrete TPM can be reset independently
â””â”€â”€ Key hierarchy: Owner password often not set
```

## 2. Remote Attestation

### 2.1 Attestation Protocols

```
Direct Anonymous Attestation (DAA):
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”         â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”         â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚  Issuer  â”‚         â”‚   Host   â”‚         â”‚ Verifier â”‚
â”‚ (Vendor) â”‚         â”‚  (TPM)   â”‚         â”‚          â”‚
â””â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”˜         â””â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”˜         â””â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”˜
     â”‚                    â”‚                    â”‚
     â”‚  Issue Credential  â”‚                    â”‚
     â”‚<â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”‚                    â”‚
     â”‚  (EK attestation)  â”‚                    â”‚
     â”‚â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€>â”‚                    â”‚
     â”‚                    â”‚                    â”‚
     â”‚                    â”‚  Attestation Req   â”‚
     â”‚                    â”‚<â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”‚
     â”‚                    â”‚                    â”‚
     â”‚                    â”‚  DAA Signature     â”‚
     â”‚                    â”‚â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€>â”‚
     â”‚                    â”‚  (Anonymous proof) â”‚
     â”‚                    â”‚                    â”‚
     â”‚                    â”‚                    â”‚
     
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                       HSM Architecture                               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚                    Tamper-Resistant Boundary                   â”‚ â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚ â”‚
â”‚  â”‚  â”‚   Secure    â”‚  â”‚    Key      â”‚  â”‚   Cryptographic     â”‚   â”‚ â”‚
â”‚  â”‚  â”‚  Processor  â”‚  â”‚   Storage   â”‚  â”‚     Engines         â”‚   â”‚ â”‚
â”‚  â”‚  â”‚  (ARM/RISC) â”‚  â”‚  (Battery-  â”‚  â”‚  - RSA/ECC accel    â”‚   â”‚ â”‚
â”‚  â”‚  â”‚             â”‚  â”‚   backed)   â”‚  â”‚  - AES/3DES accel   â”‚   â”‚ â”‚
â”‚  â”‚  â”‚  Runs HSM   â”‚  â”‚             â”‚  â”‚  - Hash accel       â”‚   â”‚ â”‚
â”‚  â”‚  â”‚  firmware   â”‚  â”‚  Zeroizes   â”‚  â”‚  - RNG (TRNG)       â”‚   â”‚ â”‚
â”‚  â”‚  â”‚             â”‚  â”‚  on tamper  â”‚  â”‚                     â”‚   â”‚ â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚ â”‚
â”‚  â”‚                                                               â”‚ â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚ â”‚
â”‚  â”‚  â”‚                  Tamper Detection                        â”‚ â”‚ â”‚
â”‚  â”‚  â”‚  - Temperature sensors                                   â”‚ â”‚ â”‚
â”‚  â”‚  â”‚  - Voltage monitors                                      â”‚ â”‚ â”‚
â”‚  â”‚  â”‚  - Light sensors (epoxy removal)                         â”‚ â”‚ â”‚
â”‚  â”‚  â”‚  - Mesh sensors (drilling/probing)                       â”‚ â”‚ â”‚
â”‚  â”‚  â”‚  - Clock frequency monitors                              â”‚ â”‚ â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                                                                     â”‚
â”‚  Interface: PCIe / Network (TLS) / USB                             â”‚
â”‚  Management: Console / Web UI / PKCS#11                            â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 FIPS 140-2/140-3 Security Levels

```
Level 1: Basic Security
â”œâ”€â”€ Production-grade equipment
â”œâ”€â”€ One approved algorithm
â”œâ”€â”€ No physical security required
â””â”€â”€ Example: OpenSSL FIPS module

Level 2: Tamper-Evidence
â”œâ”€â”€ Tamper-evident coatings/seals
â”œâ”€â”€ Role-based authentication
â”œâ”€â”€ Operator/User roles
â””â”€â”€ Example: Some USB tokens

Level 3: Tamper-Resistance
â”œâ”€â”€ Active tamper response (zeroization)
â”œâ”€â”€ Identity-based authentication
â”œâ”€â”€ Physical separation of interfaces
â”œâ”€â”€ EFP/EFT environmental protection
â””â”€â”€ Example: Thales Luna, Entrust nShield

Level 4: Complete Envelope
â”œâ”€â”€ Complete environmental failure protection
â”œâ”€â”€ Multi-factor authentication required
â”œâ”€â”€ Immediate zeroization on any anomaly
â”œâ”€â”€ Penetration testing required
â””â”€â”€ Example: Very specialized devices
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
â”œâ”€â”€ FIPS 140-2 Level 3
â”œâ”€â”€ Dedicated HSM instances
â”œâ”€â”€ PKCS#11, JCE, CNG interfaces
â”œâ”€â”€ Backup to S3 (encrypted)
â””â”€â”€ Customer-controlled keys (AWS has no access)

Azure Dedicated HSM:
â”œâ”€â”€ Thales Luna Network HSM
â”œâ”€â”€ FIPS 140-2 Level 3
â”œâ”€â”€ Direct customer access
â”œâ”€â”€ HA configuration support
â””â”€â”€ Customer-managed firmware

Google Cloud HSM:
â”œâ”€â”€ FIPS 140-2 Level 3
â”œâ”€â”€ Cloud KMS integration
â”œâ”€â”€ Asymmetric key support
â””â”€â”€ EKM (External Key Manager) support

AWS KMS (vs CloudHSM):
â”œâ”€â”€ Multi-tenant (shared HSM backend)
â”œâ”€â”€ Managed service (less control)
â”œâ”€â”€ FIPS 140-2 Level 2 (software)
â”œâ”€â”€ FIPS 140-2 Level 3 (HSM-backed keys)
â””â”€â”€ Simpler API, lower cost
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    UEFI Secure Boot Key Hierarchy                    â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚                     Platform Key (PK)                               â”‚
â”‚                     â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                â”‚
â”‚                     OEM-controlled                                  â”‚
â”‚                     Single key                                      â”‚
â”‚                     Controls KEK enrollment                         â”‚
â”‚                            â”‚                                        â”‚
â”‚                            â–¼                                        â”‚
â”‚                  Key Exchange Keys (KEK)                            â”‚
â”‚                  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                            â”‚
â”‚                  Can modify db/dbx                                  â”‚
â”‚                  Multiple keys allowed                              â”‚
â”‚                  Microsoft KEK typically included                   â”‚
â”‚                            â”‚                                        â”‚
â”‚                            â–¼                                        â”‚
â”‚         â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                      â”‚
â”‚         â–¼                                   â–¼                       â”‚
â”‚    Signature DB (db)                   Forbidden DB (dbx)           â”‚
â”‚    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€             â”‚
â”‚    Allowed signatures                  Revoked signatures           â”‚
â”‚    - Microsoft UEFI CA                 - Known-bad hashes           â”‚
â”‚    - Microsoft 3rd Party CA            - Revoked certificates       â”‚
â”‚    - Vendor keys                       - Compromised keys           â”‚
â”‚    - User keys                                                      â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Boot Flow

```
UEFI Secure Boot Verification:

1. Power On
   â””â”€â”€â–º CPU initializes, loads UEFI firmware

2. UEFI Firmware (PEI/DXE)
   â””â”€â”€â–º Self-verification (optional, vendor-specific)

3. Boot Manager
   â””â”€â”€â–º Loads bootloader (e.g., GRUB, Windows Boot Manager)
   â””â”€â”€â–º Verifies signature against db, checks not in dbx
   â””â”€â”€â–º Failure: Boot halted or fallback

4. Bootloader
   â””â”€â”€â–º Loads kernel
   â””â”€â”€â–º Shim (Linux): Re-verifies with MOK (Machine Owner Key)
   â””â”€â”€â–º Failure: Kernel not loaded

5. Kernel
   â””â”€â”€â–º Loads modules/drivers
   â””â”€â”€â–º Kernel lockdown mode (Linux): Restricts runtime modifications
```

### 1.3 Secure Boot Vulnerabilities

```
VULNERABILITY CLASS: Bootkit/Rootkit
â”œâ”€â”€ BootHole (CVE-2020-10713): GRUB2 buffer overflow, bypass Secure Boot
â”œâ”€â”€ BlackLotus (2023): First in-wild UEFI bootkit bypassing Secure Boot
â”œâ”€â”€ FinSpy UEFI: Commercial spyware with UEFI persistence
â””â”€â”€ Hacking Team UEFI: Leaked rootkit with Secure Boot bypass

VULNERABILITY CLASS: Key Management
â”œâ”€â”€ Leaked signing keys: Some OEM keys compromised
â”œâ”€â”€ Test keys in production: MOK enrolled with test keys
â”œâ”€â”€ Weak key storage: PK/KEK stored insecurely
â””â”€â”€ No revocation: dbx updates slow/incomplete

VULNERABILITY CLASS: Implementation
â”œâ”€â”€ Parser bugs: Complex formats (PE/COFF) lead to vulnerabilities
â”œâ”€â”€ Variable tampering: Authenticated variables improperly verified
â”œâ”€â”€ Time-of-check issues: Variables modified between check and use
â””â”€â”€ Integer overflows: Size calculations in signature verification

VULNERABILITY CLASS: Design
â”œâ”€â”€ Microsoft monopoly: Requires Microsoft signature for most hardware
â”œâ”€â”€ No measured boot: Secure Boot alone doesn't provide attestation
â”œâ”€â”€ User hostile: Adding custom keys is difficult
â””â”€â”€ Partial coverage: Only covers early boot, not runtime
```

## 2. Intel TXT (Trusted Execution Technology)

### 2.1 Architecture

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Intel TXT Architecture                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Normal Boot                    TXT Launch                          â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                          â”‚
â”‚  BIOS â†’ OS                      BIOS â†’ SINIT ACM â†’ MLE              â”‚
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                    Dynamic Root of Trust                     â”‚   â”‚
â”‚  â”‚                                                              â”‚   â”‚
â”‚  â”‚  1. GETSEC[SENTER] - Enter measured environment             â”‚   â”‚
â”‚  â”‚  2. Load SINIT ACM (Intel-signed Authenticated Code Module) â”‚   â”‚
â”‚  â”‚  3. SINIT measures MLE (Measured Launch Environment)        â”‚   â”‚
â”‚  â”‚  4. MLE executes (tboot â†’ Linux kernel)                     â”‚   â”‚
â”‚  â”‚  5. Measurements extend PCR 17-22                           â”‚   â”‚
â”‚  â”‚                                                              â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  DRTM vs SRTM:                                                      â”‚
â”‚  - SRTM: Static Root of Trust (full boot measured)                 â”‚
â”‚  - DRTM: Dynamic Root of Trust (late launch, smaller TCB)          â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 TXT Vulnerabilities

```
â”œâ”€â”€ SINIT Bypass: Vulnerability in SINIT ACM verification
â”œâ”€â”€ SMM Attacks: SMM not measured, can attack TXT environment
â”œâ”€â”€ DMA Attacks: IOMMU configuration errors
â”œâ”€â”€ Reset Attacks: TXT state not properly cleared on reset
â””â”€â”€ TOCTOU: Memory contents change between measurement and use
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    x86-64 Page Table Entry                           â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  63    62    52 51          12 11   9 8 7 6 5 4 3 2 1 0            â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”¼â”€â”¼â”€â”¼â”€â”¼â”€â”¼â”€â”¼â”€â”¼â”€â”¼â”€â”¼â”€â”¤            â”‚
â”‚  â”‚ XD  â”‚ Avail â”‚ Physical Addrâ”‚Availâ”‚Gâ”‚0â”‚Dâ”‚Aâ”‚Câ”‚Wâ”‚Uâ”‚Wâ”‚Pâ”‚            â”‚
â”‚  â”‚     â”‚       â”‚  (Bits 51:12)â”‚     â”‚ â”‚ â”‚ â”‚ â”‚Dâ”‚Tâ”‚Sâ”‚ â”‚ â”‚            â”‚
â”‚  â””â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”´â”€â”´â”€â”´â”€â”´â”€â”´â”€â”´â”€â”´â”€â”´â”€â”´â”€â”˜            â”‚
â”‚                                                                     â”‚
â”‚  Security-Relevant Bits:                                            â”‚
â”‚  â”œâ”€â”€ P (Present): Page is valid                                    â”‚
â”‚  â”œâ”€â”€ R/W: 0=Read-only, 1=Read-Write                                â”‚
â”‚  â”œâ”€â”€ U/S: 0=Supervisor only, 1=User accessible                     â”‚
â”‚  â”œâ”€â”€ XD/NX (bit 63): Execute Disable (No Execute)                  â”‚
â”‚  â””â”€â”€ SMEP/SMAP: Supervisor Mode Execution/Access Prevention        â”‚
â”‚                                                                     â”‚
â”‚  Protection Keys (bits 62:59 in PTE):                              â”‚
â”‚  â”œâ”€â”€ PKU: User-space protection keys (PKRU register)               â”‚
â”‚  â””â”€â”€ PKS: Supervisor protection keys (MSR)                         â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Modern Memory Protections

```
Protection         | Description                    | Bypass Technique
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                      Intel VT-d Architecture                         â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”        â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”        â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚   Device    â”‚â”€â”€â”€â”€â”€â”€â”€â–ºâ”‚   IOMMU     â”‚â”€â”€â”€â”€â”€â”€â”€â–ºâ”‚  System Memory  â”‚ â”‚
â”‚  â”‚  (PCIe/USB) â”‚  DMA   â”‚  (VT-d)     â”‚        â”‚                 â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜        â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜        â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                                â”‚                                    â”‚
â”‚                   â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                      â”‚
â”‚                   â–¼                         â–¼                       â”‚
â”‚            â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”         â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”               â”‚
â”‚            â”‚ Context Tableâ”‚         â”‚  Page Tables â”‚               â”‚
â”‚            â”‚ (per device) â”‚         â”‚ (per domain) â”‚               â”‚
â”‚            â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜         â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜               â”‚
â”‚                                                                     â”‚
â”‚  Protections:                                                       â”‚
â”‚  â”œâ”€â”€ DMA Remapping: Restrict device memory access                  â”‚
â”‚  â”œâ”€â”€ Interrupt Remapping: Prevent interrupt injection              â”‚
â”‚  â””â”€â”€ Posted Interrupts: Secure interrupt delivery                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 DMA Attack Mitigations

```
Attack Vector:
1. Malicious device connected (Thunderbolt, PCIe)
2. Device performs DMA to kernel memory
3. Overwrites security-sensitive structures
4. Kernel compromised

Mitigations:
â”œâ”€â”€ IOMMU enabled by default (Linux 5.x+)
â”œâ”€â”€ Thunderbolt security levels (user authorization)
â”œâ”€â”€ Kernel DMA protection (pre-boot setting)
â”œâ”€â”€ Secure Boot required for full protection
â””â”€â”€ Windows: Kernel DMA Protection policy

Remaining Issues:
â”œâ”€â”€ IOMMU bypass via ATS (Address Translation Services)
â”œâ”€â”€ Passthrough mode for VMs disables protection
â”œâ”€â”€ Complex configuration leads to errors
â””â”€â”€ Legacy devices may not be isolated
```

## 3. ARM Memory Protection

### 3.1 Memory Tagging Extension (MTE)

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    ARM Memory Tagging Extension                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Pointer:  [63:60 TAG] [59:0 ADDRESS]                              â”‚
â”‚                  â”‚                                                  â”‚
â”‚                  â–¼                                                  â”‚
â”‚  Memory:  Each 16-byte granule has 4-bit tag                       â”‚
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚
â”‚  â”‚  0x1000  â”‚  0x1010  â”‚  0x1020  â”‚  0x1030  â”‚  ...          â”‚    â”‚
â”‚  â”‚  Tag: 5  â”‚  Tag: 3  â”‚  Tag: 7  â”‚  Tag: 5  â”‚               â”‚    â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚
â”‚                                                                     â”‚
â”‚  Access:                                                            â”‚
â”‚  â”œâ”€â”€ Load/Store checks pointer tag against memory tag              â”‚
â”‚  â”œâ”€â”€ Match: Access proceeds                                        â”‚
â”‚  â”œâ”€â”€ Mismatch: Fault (sync) or async report                        â”‚
â”‚  â””â”€â”€ IRG instruction: Generate random tag                          â”‚
â”‚                                                                     â”‚
â”‚  Use Cases:                                                         â”‚
â”‚  â”œâ”€â”€ Heap buffer overflow detection                                â”‚
â”‚  â”œâ”€â”€ Use-after-free detection                                      â”‚
â”‚  â”œâ”€â”€ Double-free detection                                         â”‚
â”‚  â””â”€â”€ Stack buffer overflow (with compiler support)                 â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 3.2 Pointer Authentication (PAC)

```
ARMv8.3 Pointer Authentication:

Pointer Format:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚  [63:48 PAC] [47:0 Virtual Address]                                 â”‚
â”‚                                                                     â”‚
â”‚  PAC = QARMA(key, pointer || context)                              â”‚
â”‚                                                                     â”‚
â”‚  Keys (per EL):                                                     â”‚
â”‚  â”œâ”€â”€ APIAKey: Instruction pointers (A key)                         â”‚
â”‚  â”œâ”€â”€ APIBKey: Instruction pointers (B key)                         â”‚
â”‚  â”œâ”€â”€ APDAKey: Data pointers (A key)                                â”‚
â”‚  â”œâ”€â”€ APDBKey: Data pointers (B key)                                â”‚
â”‚  â””â”€â”€ APGAKey: Generic authentication                               â”‚
â”‚                                                                     â”‚
â”‚  Instructions:                                                      â”‚
â”‚  â”œâ”€â”€ PACIA: Sign instruction pointer with A key                    â”‚
â”‚  â”œâ”€â”€ AUTIA: Authenticate instruction pointer with A key            â”‚
â”‚  â”œâ”€â”€ PACDA: Sign data pointer with A key                           â”‚
â”‚  â””â”€â”€ RETAA: Return with authentication                             â”‚
â”‚                                                                     â”‚
â”‚  Security:                                                          â”‚
â”‚  â”œâ”€â”€ Protects return addresses (vs ROP)                            â”‚
â”‚  â”œâ”€â”€ Protects function pointers                                    â”‚
â”‚  â”œâ”€â”€ Probabilistic: 16-bit PAC has 1/65536 collision               â”‚
â”‚  â””â”€â”€ PACMAN attack: Speculative execution can leak PAC             â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Intel CET Architecture                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Shadow Stack:                                                      â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                                      â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”     â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                                 â”‚
â”‚  â”‚ User Stack â”‚     â”‚Shadow Stackâ”‚                                 â”‚
â”‚  â”‚            â”‚     â”‚            â”‚                                 â”‚
â”‚  â”‚ Local Vars â”‚     â”‚ Ret Addr 1 â”‚ â—„â”€â”€â”€ CALL pushes to both       â”‚
â”‚  â”‚ Ret Addr 1 â”‚â”€â”€â”€â”€â–ºâ”‚ Ret Addr 2 â”‚ â—„â”€â”€â”€ RET compares both         â”‚
â”‚  â”‚ Local Vars â”‚     â”‚    ...     â”‚                                 â”‚
â”‚  â”‚ Ret Addr 2 â”‚     â”‚            â”‚                                 â”‚
â”‚  â”‚    ...     â”‚     â”‚            â”‚                                 â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜     â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                                 â”‚
â”‚                                                                     â”‚
â”‚  Shadow Stack Properties:                                           â”‚
â”‚  â”œâ”€â”€ Separate memory region, not writable via normal stores        â”‚
â”‚  â”œâ”€â”€ CALL: Push return address to shadow stack                     â”‚
â”‚  â”œâ”€â”€ RET: Compare shadow stack vs regular stack                    â”‚
â”‚  â”œâ”€â”€ Mismatch: #CP (Control Protection) exception                  â”‚
â”‚  â””â”€â”€ INCSSP/RDSSP: Manipulate shadow stack pointer                 â”‚
â”‚                                                                     â”‚
â”‚  Indirect Branch Tracking (IBT):                                    â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                    â”‚
â”‚  â”œâ”€â”€ ENDBR32/ENDBR64: Valid indirect branch targets                â”‚
â”‚  â”œâ”€â”€ JMP/CALL indirect sets TRACKER state                          â”‚
â”‚  â”œâ”€â”€ Next instruction must be ENDBR or #CP exception               â”‚
â”‚  â””â”€â”€ Prevents arbitrary code execution via JOP                     â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 ARM BTI (Branch Target Identification)

```
ARMv8.5 Branch Target Identification:

Landing Pads:
â”œâ”€â”€ BTI c: Valid target for BLR (call indirect)
â”œâ”€â”€ BTI j: Valid target for BR (jump indirect)
â”œâ”€â”€ BTI jc: Valid target for both
â””â”€â”€ PSTATE.BTYPE: Tracks previous branch type

Code:
    BLR x0          // Sets BTYPE = 01 (call)
    ...
target:
    BTI c           // Valid landing pad for calls
    // Function code
    RET

Protection:
â”œâ”€â”€ Must land on BTI instruction after indirect branch
â”œâ”€â”€ Fault if landing on non-BTI instruction
â”œâ”€â”€ Coarse-grained: Any BTI of matching type is valid
â””â”€â”€ Combine with PAC for better protection
```

## 2. Speculative Execution Defenses

### 2.1 Spectre Mitigations

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Spectre Mitigation Overview                       â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Spectre v1 (Bounds Check Bypass):                                  â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                  â”‚
â”‚  Mitigation:                                                        â”‚
â”‚  â”œâ”€â”€ LFENCE: Serialize speculative execution                       â”‚
â”‚  â”œâ”€â”€ Array index masking: index &= (index < limit) - 1             â”‚
â”‚  â”œâ”€â”€ Speculation barriers: Compiler intrinsics                     â”‚
â”‚  â””â”€â”€ Static analysis: Identify vulnerable patterns                 â”‚
â”‚                                                                     â”‚
â”‚  Spectre v2 (Branch Target Injection):                              â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                              â”‚
â”‚  Mitigation:                                                        â”‚
â”‚  â”œâ”€â”€ Retpoline: Replace indirect branches with return trampolines  â”‚
â”‚  â”œâ”€â”€ IBRS: Indirect Branch Restricted Speculation                  â”‚
â”‚  â”œâ”€â”€ STIBP: Single Thread Indirect Branch Predictors               â”‚
â”‚  â”œâ”€â”€ IBPB: Indirect Branch Predictor Barrier                       â”‚
â”‚  â””â”€â”€ eIBRS: Enhanced IBRS (always-on mode)                         â”‚
â”‚                                                                     â”‚
â”‚  Spectre-BHB (Branch History Buffer):                               â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                               â”‚
â”‚  Mitigation:                                                        â”‚
â”‚  â”œâ”€â”€ Clear BHB on kernel entry                                     â”‚
â”‚  â””â”€â”€ Additional barrier instructions                               â”‚
â”‚                                                                     â”‚
â”‚  SSBD (Speculative Store Bypass Disable):                           â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                          â”‚
â”‚  â”œâ”€â”€ Prevents speculative bypass of store forwarding               â”‚
â”‚  â””â”€â”€ Significant performance impact                                â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 Meltdown Mitigations

```
Meltdown (Rogue Data Cache Load):
â”œâ”€â”€ Speculative read of kernel memory from user space
â”œâ”€â”€ Data transmitted via cache side channel
â””â”€â”€ Complete kernel memory exposure

KPTI (Kernel Page Table Isolation):
â”œâ”€â”€ Separate page tables for user and kernel mode
â”œâ”€â”€ Kernel pages not mapped in user page tables
â”œâ”€â”€ Context switch flushes TLB (performance cost)
â””â”€â”€ PCID: Process Context ID to reduce TLB flush cost

Kernel:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”     User:
â”‚ Kernel code     â”‚     â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Kernel data     â”‚     â”‚ User code       â”‚
â”‚ User code       â”‚     â”‚ User data       â”‚
â”‚ User data       â”‚     â”‚ (Kernel: tiny   â”‚
â”‚                 â”‚     â”‚  trampoline     â”‚
â”‚                 â”‚     â”‚  only)          â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜     â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 3. Memory Encryption

### 3.1 Intel TME/MKTME

```
Total Memory Encryption (TME):
â”œâ”€â”€ AES-XTS encryption of all DRAM
â”œâ”€â”€ Single key for entire system
â”œâ”€â”€ Key generated at boot, stored in CPU
â””â”€â”€ Transparent to software

Multi-Key TME (MKTME):
â”œâ”€â”€ Multiple encryption keys
â”œâ”€â”€ Per-page key selection via page tables
â”œâ”€â”€ Key ID in physical address bits
â”œâ”€â”€ Enables SEV-like VM isolation
â””â”€â”€ Up to 64+ keys depending on CPU
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Physical Attack Taxonomy                          â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  INVASIVE ATTACKS (require chip decapsulation)                      â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                      â”‚
â”‚  â”œâ”€â”€ Microprobing: Direct probe of internal signals                â”‚
â”‚  â”œâ”€â”€ FIB (Focused Ion Beam): Circuit modification                  â”‚
â”‚  â”œâ”€â”€ Laser fault injection: Targeted bit flips                     â”‚
â”‚  â””â”€â”€ Reverse engineering: Full chip layout extraction              â”‚
â”‚                                                                     â”‚
â”‚  SEMI-INVASIVE ATTACKS (access to chip surface)                     â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                    â”‚
â”‚  â”œâ”€â”€ Optical fault induction: UV/visible light attacks             â”‚
â”‚  â”œâ”€â”€ Electromagnetic fault induction: EM pulses                    â”‚
â”‚  â”œâ”€â”€ Laser scanning microscopy: Read memory contents               â”‚
â”‚  â””â”€â”€ Photon emission analysis: Observe transistor switching        â”‚
â”‚                                                                     â”‚
â”‚  NON-INVASIVE ATTACKS (external observation only)                   â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                  â”‚
â”‚  â”œâ”€â”€ Power analysis: SPA, DPA, CPA                                 â”‚
â”‚  â”œâ”€â”€ Electromagnetic analysis: SEMA, DEMA                          â”‚
â”‚  â”œâ”€â”€ Timing analysis: Operation timing variations                  â”‚
â”‚  â”œâ”€â”€ Acoustic analysis: Sound of operations                        â”‚
â”‚  â”œâ”€â”€ Thermal analysis: Heat patterns                               â”‚
â”‚  â””â”€â”€ Cold boot: Memory remanence after power loss                  â”‚
â”‚                                                                     â”‚
â”‚  FAULT INJECTION ATTACKS                                            â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                            â”‚
â”‚  â”œâ”€â”€ Voltage glitching: Vcc manipulation                           â”‚
â”‚  â”œâ”€â”€ Clock glitching: Frequency manipulation                       â”‚
â”‚  â”œâ”€â”€ Temperature extremes: Induce bit flips                        â”‚
â”‚  â””â”€â”€ Radiation: X-ray, gamma, particle beams                       â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Tamper Resistance Techniques

```
Passive Defenses:
â”œâ”€â”€ Security meshes: Detect drilling/cutting
â”œâ”€â”€ Light sensors: Detect decapsulation
â”œâ”€â”€ Temperature sensors: Detect extreme conditions
â”œâ”€â”€ Voltage sensors: Detect glitching attempts
â”œâ”€â”€ Clock monitors: Detect frequency manipulation
â”œâ”€â”€ Epoxy/conformal coating: Physical barrier
â””â”€â”€ Shielding: EM protection

Active Defenses:
â”œâ”€â”€ Automatic zeroization: Destroy keys on tamper
â”œâ”€â”€ Alarm circuits: Alert on intrusion
â”œâ”€â”€ Self-destruct: Physical destruction of chip
â”œâ”€â”€ Frequency hopping: Vary operation timing
â”œâ”€â”€ Power filtering: Reduce side-channel leakage
â””â”€â”€ Dummy operations: Mask real operations
```

## 2. Cold Boot Attacks

### 2.1 Memory Remanence

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Cold Boot Attack                                  â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Standard DRAM Decay:                                               â”‚
â”‚  â”œâ”€â”€ Room temperature: ~1-2 seconds before significant decay       â”‚
â”‚  â”œâ”€â”€ 0Â°C: ~10 seconds retention                                    â”‚
â”‚  â”œâ”€â”€ -50Â°C: ~10 minutes retention                                  â”‚
â”‚  â””â”€â”€ Liquid nitrogen: Hours of retention                           â”‚
â”‚                                                                     â”‚
â”‚  Attack Procedure:                                                  â”‚
â”‚  1. Target machine running with keys in memory                     â”‚
â”‚  2. Cool DRAM modules (canned air upside down = -50Â°C)            â”‚
â”‚  3. Power off briefly                                              â”‚
â”‚  4. Boot from attack USB with memory imaging tool                  â”‚
â”‚  5. Dump memory contents                                           â”‚
â”‚  6. Extract encryption keys                                        â”‚
â”‚                                                                     â”‚
â”‚  Mitigations:                                                       â”‚
â”‚  â”œâ”€â”€ Memory encryption (TME/MKTME, SEV)                           â”‚
â”‚  â”œâ”€â”€ Key scrubbing on shutdown                                     â”‚
â”‚  â”œâ”€â”€ TRESOR: Store keys in CPU registers only                      â”‚
â”‚  â”œâ”€â”€ Memory locking: Prevent swap, wipe on hibernate              â”‚
â”‚  â””â”€â”€ Physical memory protection: Tamper-evident cases              â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 3. Bus Sniffing and Probing

### 3.1 External Bus Attacks

```
Target Buses:
â”œâ”€â”€ PCIe: DMA attacks, malicious peripherals
â”œâ”€â”€ USB: BadUSB, malicious devices
â”œâ”€â”€ Thunderbolt: Direct memory access
â”œâ”€â”€ SPI: Flash chip reading/writing
â”œâ”€â”€ I2C: EEPROM access, TPM communication
â”œâ”€â”€ JTAG: Debug access, full system control
â””â”€â”€ SWD: ARM debug interface

Mitigations:
â”œâ”€â”€ IOMMU: DMA protection
â”œâ”€â”€ Bus encryption: TPM 2.0 encrypted sessions
â”œâ”€â”€ Debug fuses: Disable JTAG/SWD in production
â”œâ”€â”€ Port disable: Block unused interfaces
â”œâ”€â”€ Authentication: Device attestation before trust
â””â”€â”€ Physical protection: Block port access
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    TRNG Entropy Sources                              â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  PHYSICAL SOURCES:                                                  â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                                  â”‚
â”‚  â”œâ”€â”€ Thermal noise: Johnson-Nyquist noise in resistors             â”‚
â”‚  â”œâ”€â”€ Shot noise: Random electron flow in semiconductors            â”‚
â”‚  â”œâ”€â”€ Metastability: Flip-flop settling time variation              â”‚
â”‚  â”œâ”€â”€ Ring oscillator jitter: Phase noise in oscillators            â”‚
â”‚  â”œâ”€â”€ Radioactive decay: Truly random quantum events                â”‚
â”‚  â””â”€â”€ Quantum effects: Photon polarization, vacuum fluctuations     â”‚
â”‚                                                                     â”‚
â”‚  COMMON IMPLEMENTATIONS:                                            â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                            â”‚
â”‚  â”œâ”€â”€ Intel RDRAND: CSPRNG seeded by entropy source                 â”‚
â”‚  â”‚   â””â”€â”€ NOT raw entropy: Output is conditioned                    â”‚
â”‚  â”œâ”€â”€ Intel RDSEED: Closer to raw entropy                           â”‚
â”‚  â”‚   â””â”€â”€ May fail (CF=0) if entropy depleted                       â”‚
â”‚  â”œâ”€â”€ ARM TRNG: Implementation-defined source                       â”‚
â”‚  â””â”€â”€ TPM RNG: Hardware RNG in TPM chip                             â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 RDRAND/RDSEED Architecture

```
Intel DRNG (Digital Random Number Generator):

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”     â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”     â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚
â”‚  â”‚ Entropy Source  â”‚â”€â”€â”€â”€â–ºâ”‚  Conditioner    â”‚â”€â”€â”€â”€â–ºâ”‚    CSPRNG    â”‚  â”‚
â”‚  â”‚ (Thermal noise) â”‚     â”‚ (AES-CBC-MAC)   â”‚     â”‚ (AES-CTR)    â”‚  â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜     â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜     â””â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚
â”‚                                     â”‚                    â”‚          â”‚
â”‚                                     â”‚                    â–¼          â”‚
â”‚                               RDSEED output         RDRAND output   â”‚
â”‚                                                                     â”‚
â”‚  RDRAND:                                                            â”‚
â”‚  â”œâ”€â”€ Always succeeds (waits if necessary)                          â”‚
â”‚  â”œâ”€â”€ Output is CSPRNG output                                       â”‚
â”‚  â”œâ”€â”€ Reseeded from conditioner periodically                        â”‚
â”‚  â””â”€â”€ Suitable for key generation                                   â”‚
â”‚                                                                     â”‚
â”‚  RDSEED:                                                            â”‚
â”‚  â”œâ”€â”€ May fail if entropy depleted                                  â”‚
â”‚  â”œâ”€â”€ Output is conditioned entropy                                 â”‚
â”‚  â”œâ”€â”€ Suitable for seeding other CSPRNGs                            â”‚
â”‚  â””â”€â”€ Use retry loop with back-off                                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.3 RNG Vulnerabilities

```
VULNERABILITY CLASS: Hardware Issues
â”œâ”€â”€ Insufficient entropy: Weak noise source
â”œâ”€â”€ Biased output: Statistical non-uniformity
â”œâ”€â”€ Predictable patterns: Correlations in output
â”œâ”€â”€ Hardware failure: Silent RNG failure
â””â”€â”€ Backdoor concerns: Potential for weakened implementations

VULNERABILITY CLASS: Implementation Issues
â”œâ”€â”€ RDRAND underflow: AMD Ryzen bug returned 0xFFFFFFFF
â”œâ”€â”€ VM entropy starvation: Multiple VMs deplete pool
â”œâ”€â”€ Boot-time weakness: Insufficient entropy early in boot
â””â”€â”€ Fork issues: Child processes share RNG state

Mitigation:
â”œâ”€â”€ Multiple entropy sources: Don't rely on single source
â”œâ”€â”€ Health testing: Continuous RNG output validation
â”œâ”€â”€ Entropy estimation: Track available randomness
â”œâ”€â”€ NIST SP 800-90B: Entropy source validation standard
â””â”€â”€ Conditioning: Always post-process raw entropy
```

## 2. Entropy Collection

### 2.1 Linux Random Subsystem

```
Linux /dev/random Architecture:

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Entropy Sources                                   â”‚
â”‚  â”œâ”€â”€ RDRAND/RDSEED (if available)                                  â”‚
â”‚  â”œâ”€â”€ Interrupt timing                                              â”‚
â”‚  â”œâ”€â”€ Disk timing                                                   â”‚
â”‚  â”œâ”€â”€ Human input (keyboard, mouse)                                 â”‚
â”‚  â””â”€â”€ virtio-rng (VMs)                                              â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
                              â”‚
                              â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    CRNG (Cryptographic RNG)                          â”‚
â”‚  â”œâ”€â”€ ChaCha20 stream cipher                                        â”‚
â”‚  â”œâ”€â”€ Reseeded when entropy available                               â”‚
â”‚  â””â”€â”€ Fast extraction from pool                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
                              â”‚
                              â–¼
         â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
         â”‚                                         â”‚
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Apple Secure Enclave                              â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚                    Application Processor                       â”‚ â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚ â”‚
â”‚  â”‚  â”‚                      iOS/macOS                           â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”         â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚ Keychain   â”‚  â”‚ Face ID    â”‚  â”‚ Apple Pay  â”‚         â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚ Services   â”‚  â”‚            â”‚  â”‚            â”‚         â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â””â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”˜         â”‚  â”‚ â”‚
â”‚  â”‚  â”‚        â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                â”‚  â”‚ â”‚
â”‚  â”‚  â”‚                        â”‚                                 â”‚  â”‚ â”‚
â”‚  â”‚  â”‚                  SEP Requests                            â”‚  â”‚ â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                              â”‚                                      â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â”‚â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•   â”‚
â”‚                              â–¼                                      â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚              Secure Enclave Processor (SEP)                    â”‚ â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚ â”‚
â”‚  â”‚  â”‚ SEP OS      â”‚  â”‚ Secure Key  â”‚  â”‚ Hardware Crypto     â”‚   â”‚ â”‚
â”‚  â”‚  â”‚ (SEPOS)     â”‚  â”‚ Store       â”‚  â”‚ Engine              â”‚   â”‚ â”‚
â”‚  â”‚  â”‚             â”‚  â”‚             â”‚  â”‚ - AES               â”‚   â”‚ â”‚
â”‚  â”‚  â”‚ Dedicated   â”‚  â”‚ UID: Never  â”‚  â”‚ - PKA (Public Key)  â”‚   â”‚ â”‚
â”‚  â”‚  â”‚ L4 kernel   â”‚  â”‚ leaves SEP  â”‚  â”‚ - TRNG              â”‚   â”‚ â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚ â”‚
â”‚  â”‚                                                               â”‚ â”‚
â”‚  â”‚  Anti-Replay: Secure counter, tamper-evident storage         â”‚ â”‚
â”‚  â”‚  Secure Boot: Separate from AP boot chain                    â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Key Features:
â”œâ”€â”€ UID (Unique ID): Device-specific key, fused at manufacture
â”œâ”€â”€ GID (Group ID): Device class key
â”œâ”€â”€ Hardware memory protection from AP
â”œâ”€â”€ Dedicated boot ROM and secure boot
â””â”€â”€ Anti-rollback counters for updates
```

### 1.2 SEP Security Services

```
Services Provided:
â”œâ”€â”€ Touch ID / Face ID: Biometric template storage and matching
â”œâ”€â”€ Apple Pay: Payment credential protection
â”œâ”€â”€ Keychain: Key hierarchy rooted in SEP
â”œâ”€â”€ Disk Encryption: File encryption key protection
â”œâ”€â”€ Passcode Verification: Rate limiting and wipe on excessive failures
â””â”€â”€ Secure Neural Engine: ML model protection (A14+)
```

## 2. Google Titan / Android StrongBox

### 2.1 Architecture

```
Google Titan M2:
â”œâ”€â”€ Purpose-built security chip
â”œâ”€â”€ ARM Cortex-M3 core
â”œâ”€â”€ Separate from main SoC
â”œâ”€â”€ Hardware crypto: RSA, ECC, AES, SHA
â”œâ”€â”€ TRNG
â””â”€â”€ Tamper detection

Android StrongBox:
â”œâ”€â”€ Hardware-backed keystore
â”œâ”€â”€ Isolated from main processor
â”œâ”€â”€ Key generation in hardware
â”œâ”€â”€ No key export
â””â”€â”€ User authentication binding

KeyMint (Android 12+):
â”œâ”€â”€ Modern Keymaster replacement
â”œâ”€â”€ Remote key provisioning
â”œâ”€â”€ Attestation improvements
â””â”€â”€ Better key use authorization
```

## 3. Microsoft Pluton

### 3.1 Architecture

```
Microsoft Pluton:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  Traditional: â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€ Firmware â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€ TPM (Discrete)      â”‚
â”‚               Bus attack surface                                    â”‚
â”‚                                                                     â”‚
â”‚  Pluton:     â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”       â”‚
â”‚              â”‚                   CPU                        â”‚       â”‚
â”‚              â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚       â”‚
â”‚              â”‚  â”‚            Pluton                     â”‚   â”‚       â”‚
â”‚              â”‚  â”‚  - Security processor core           â”‚   â”‚       â”‚
â”‚              â”‚  â”‚  - Crypto accelerators               â”‚   â”‚       â”‚
â”‚              â”‚  â”‚  - Secure storage                    â”‚   â”‚       â”‚
â”‚              â”‚  â”‚  - Direct CPU integration            â”‚   â”‚       â”‚
â”‚              â”‚  â”‚  - No external bus exposure          â”‚   â”‚       â”‚
â”‚              â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚       â”‚
â”‚              â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜       â”‚
â”‚                                                                     â”‚
â”‚  Benefits:                                                          â”‚
â”‚  â”œâ”€â”€ No physical bus to attack                                     â”‚
â”‚  â”œâ”€â”€ Firmware updates via Windows Update                           â”‚
â”‚  â”œâ”€â”€ TPM 2.0 compatible                                            â”‚
â”‚  â””â”€â”€ Additional features beyond TPM                                â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Spectre Vulnerability Family                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Spectre v1 (Bounds Check Bypass) - CVE-2017-5753                   â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                 â”‚
â”‚  if (x < array1_size)                                               â”‚
â”‚      y = array2[array1[x] * 256];  // Speculative access            â”‚
â”‚                                                                     â”‚
â”‚  Spectre v2 (Branch Target Injection) - CVE-2017-5715               â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€              â”‚
â”‚  Attacker trains branch predictor to mispredict indirect branches   â”‚
â”‚  Victim speculatively executes attacker-chosen gadget               â”‚
â”‚                                                                     â”‚
â”‚  Spectre v3 (Meltdown) - CVE-2017-5754                              â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                              â”‚
â”‚  User-mode speculative read of kernel memory                        â”‚
â”‚  Exception deferred until retirement                                â”‚
â”‚                                                                     â”‚
â”‚  Spectre v3a (Rogue System Register Read)                           â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                          â”‚
â”‚  Speculative read of system registers                               â”‚
â”‚                                                                     â”‚
â”‚  Spectre v4 (Speculative Store Bypass) - CVE-2018-3639              â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€               â”‚
â”‚  Store-to-load forwarding speculates around store                   â”‚
â”‚                                                                     â”‚
â”‚  Spectre-BHB (Branch History Buffer) - 2022                         â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                         â”‚
â”‚  BHB poisoning bypasses some v2 mitigations                         â”‚
â”‚                                                                     â”‚
â”‚  Spectre-RSB (Return Stack Buffer)                                  â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                  â”‚
â”‚  RSB pollution leads to mispredicted returns                        â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 MDS (Microarchitectural Data Sampling)

```
RIDL (Rogue In-Flight Data Load):
â”œâ”€â”€ Leak data from line fill buffers
â””â”€â”€ CVE-2018-12126 (MFBDS), CVE-2018-12127 (MLPDS)

Fallout:
â”œâ”€â”€ Leak data from store buffers
â””â”€â”€ CVE-2018-12130 (MSBDS)

ZombieLoad:
â”œâ”€â”€ Leak data from load ports
â”œâ”€â”€ Cross-hyperthread attack
â””â”€â”€ CVE-2019-11091 (MDSUM)

TAA (TSX Asynchronous Abort):
â”œâ”€â”€ Leak data during TSX abort
â””â”€â”€ CVE-2019-11135

Mitigations:
â”œâ”€â”€ MDS_NO: Hardware indication of immunity
â”œâ”€â”€ VERW: Clear CPU buffers
â”œâ”€â”€ Hyperthreading disable: Eliminate cross-thread attacks
â””â”€â”€ Microcode updates: Partial mitigations
```

### 1.3 Other Microarchitectural Vulnerabilities

```
Foreshadow (L1 Terminal Fault):
â”œâ”€â”€ L1TF: CVE-2018-3615 (SGX), CVE-2018-3620 (OS), CVE-2018-3646 (VMM)
â”œâ”€â”€ Bypass L1 cache checks
â”œâ”€â”€ Complete SGX break
â””â”€â”€ Mitigation: PTE inversion, flush L1 on VM entry

CacheOut / L1DES:
â”œâ”€â”€ CVE-2020-0549
â”œâ”€â”€ Leak data from evicted cache lines
â””â”€â”€ Mitigation: Microcode updates

VRS (Vector Register Sampling):
â”œâ”€â”€ CVE-2020-0548
â”œâ”€â”€ Leak SIMD register contents
â””â”€â”€ Mitigation: Clear vector registers

SRBDS (Special Register Buffer Data Sampling):
â”œâ”€â”€ CVE-2020-0543 (CrossTalk)
â”œâ”€â”€ Leak data across cores via staging buffer
â””â”€â”€ Affects: RDRAND, RDSEED, EGETKEY

LVI (Load Value Injection):
â”œâ”€â”€ CVE-2020-0551
â”œâ”€â”€ Inject values into victim's loads
â”œâ”€â”€ Reverse of Meltdown-style attacks
â””â”€â”€ Complex exploitation

Ã†PIC Leak:
â”œâ”€â”€ Read uninitialized data from APIC registers
â”œâ”€â”€ Affects SGX: leak enclave data
â””â”€â”€ CVE-2022-21233

Downfall (GDS - Gather Data Sampling):
â”œâ”€â”€ CVE-2022-40982
â”œâ”€â”€ AVX2/AVX-512 gather instructions leak data
â””â”€â”€ Significant performance impact from mitigation

Inception (TTE - Transient Execution Training):
â”œâ”€â”€ CVE-2023-20569 (AMD)
â”œâ”€â”€ Train branch predictor for RAS manipulation
â””â”€â”€ Phantom speculation attacks

Zenbleed:
â”œâ”€â”€ CVE-2023-20593 (AMD Zen 2)
â”œâ”€â”€ Leak data from XMM/YMM registers
â”œâ”€â”€ Fast cross-process attack
â””â”€â”€ Microcode fix available
```

## 2. Rowhammer

### 2.1 Attack Mechanism

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    DRAM Rowhammer Attack                             â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  DRAM Structure:                                                    â”‚
â”‚  â”œâ”€â”€ Rows of capacitor cells                                       â”‚
â”‚  â”œâ”€â”€ Cells lose charge over time (refresh needed)                  â”‚
â”‚  â””â”€â”€ Adjacent rows share physical proximity                        â”‚
â”‚                                                                     â”‚
â”‚  Attack:                                                            â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”     â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”     â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”                       â”‚
â”‚  â”‚ Row N-1 â”‚     â”‚ Row N-1 â”‚     â”‚ Row N-1 â”‚ â† Victim row          â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤     â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤     â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤                       â”‚
â”‚  â”‚  Row N  â”‚ â”€â”€â–º â”‚  Row N  â”‚ â”€â”€â–º â”‚  Row N  â”‚ â† Hammer (activate)   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤     â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤     â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤                       â”‚
â”‚  â”‚ Row N+1 â”‚     â”‚ Row N+1 â”‚     â”‚ Row N+1 â”‚ â† Victim row          â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜     â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜     â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                       â”‚
â”‚                                                                     â”‚
â”‚  Repeated activation of Row N causes bit flips in N-1 and N+1      â”‚
â”‚                                                                     â”‚
â”‚  Exploitation:                                                      â”‚
â”‚  â”œâ”€â”€ Privilege escalation: Flip bits in page tables                â”‚
â”‚  â”œâ”€â”€ Sandbox escape: Flip bits in security metadata                â”‚
â”‚  â”œâ”€â”€ VM escape: Flip bits in hypervisor structures                 â”‚
â”‚  â””â”€â”€ RSA key recovery: Flip bits in key data                       â”‚
â”‚                                                                     â”‚
â”‚  Variants:                                                          â”‚
â”‚  â”œâ”€â”€ Single-sided: Hammer one row                                  â”‚
â”‚  â”œâ”€â”€ Double-sided: Hammer rows on both sides                       â”‚
â”‚  â”œâ”€â”€ One-location: Single cache line hammer                        â”‚
â”‚  â”œâ”€â”€ TRRespass: Bypass Target Row Refresh                          â”‚
â”‚  â””â”€â”€ Half-Double: Three-row pattern                                â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Mitigations:
â”œâ”€â”€ ECC memory: Detect single-bit flips (but not multi-bit)
â”œâ”€â”€ Target Row Refresh (TRR): Hardware mitigation (often bypassable)
â”œâ”€â”€ PARA: Probabilistic Adjacent Row Activation
â”œâ”€â”€ Memory isolation: Prevent attacker control over physical addresses
â””â”€â”€ Refresh rate increase: Performance cost
```

## 3. PLATYPUS and Power Side Channels

```
PLATYPUS (Power Leakage Attacks):
â”œâ”€â”€ Read Intel RAPL (Running Average Power Limit) counters
â”œâ”€â”€ Infer execution patterns from power consumption
â”œâ”€â”€ Extract AES keys from SGX enclaves
â””â”€â”€ Mitigation: Restrict RAPL access

Hertzbleed:
â”œâ”€â”€ Frequency scaling reveals data-dependent operations
â”œâ”€â”€ Remote timing attack via frequency changes
â”œâ”€â”€ P-state variations leak information
â””â”€â”€ Mitigation: Constant-time implementation
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Hardware Root of Trust Hierarchy                  â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚                    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                          â”‚
â”‚                    â”‚   Hardware RoT      â”‚                          â”‚
â”‚                    â”‚   (CPU/TPM/HSM)     â”‚                          â”‚
â”‚                    â”‚   â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚                          â”‚
â”‚                    â”‚   â”‚ Root Keys   â”‚   â”‚                          â”‚
â”‚                    â”‚   â”‚ (Fused/OTP) â”‚   â”‚                          â”‚
â”‚                    â”‚   â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚                          â”‚
â”‚                    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                          â”‚
â”‚                              â”‚                                      â”‚
â”‚                              â–¼                                      â”‚
â”‚                    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                          â”‚
â”‚                    â”‚   Firmware RoT      â”‚                          â”‚
â”‚                    â”‚   (Boot ROM/ACM)    â”‚                          â”‚
â”‚                    â”‚   Signed by HW Key  â”‚                          â”‚
â”‚                    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                          â”‚
â”‚                              â”‚                                      â”‚
â”‚                              â–¼                                      â”‚
â”‚                    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                          â”‚
â”‚                    â”‚   Software RoT      â”‚                          â”‚
â”‚                    â”‚   (Bootloader/BIOS) â”‚                          â”‚
â”‚                    â”‚   Verified by FW    â”‚                          â”‚
â”‚                    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                          â”‚
â”‚                              â”‚                                      â”‚
â”‚                              â–¼                                      â”‚
â”‚                    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                          â”‚
â”‚                    â”‚   Application RoT   â”‚                          â”‚
â”‚                    â”‚   (OS/Apps)         â”‚                          â”‚
â”‚                    â”‚   Verified by SW    â”‚                          â”‚
â”‚                    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                          â”‚
â”‚                                                                     â”‚
â”‚  Chain of Trust: Each layer measures/verifies the next             â”‚
â”‚  Compromise: Any break in chain compromises all downstream         â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Root of Trust Types

```
Root of Trust for Storage (RTS):
â”œâ”€â”€ Secure storage of secrets
â”œâ”€â”€ Key hierarchy anchored in hardware
â”œâ”€â”€ Sealing/unsealing to platform state
â””â”€â”€ Examples: TPM NVRAM, Secure Enclave keystore

Root of Trust for Measurement (RTM):
â”œâ”€â”€ Measure code/data before execution
â”œâ”€â”€ Extend measurements to PCRs
â”œâ”€â”€ Enable attestation of platform state
â””â”€â”€ Examples: TPM PCRs, SGX MRENCLAVE

Root of Trust for Reporting (RTR):
â”œâ”€â”€ Sign attestation reports
â”œâ”€â”€ Prove platform identity
â”œâ”€â”€ Remote verification of platform state
â””â”€â”€ Examples: TPM EK, SGX EPID/DCAP

Root of Trust for Update (RTU):
â”œâ”€â”€ Authenticate firmware updates
â”œâ”€â”€ Prevent rollback attacks
â”œâ”€â”€ Secure version management
â””â”€â”€ Examples: Secure Boot, TPM counter
```

## 2. Device Identity

### 2.1 Hardware Attestation

```
Device Identity Composition Engine (DICE):
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  UDS (Unique Device Secret)                                        â”‚
â”‚       â”‚                                                             â”‚
â”‚       â–¼                                                             â”‚
â”‚  CDI (Compound Device Identifier)                                  â”‚
â”‚  = KDF(UDS, Hash(First Mutable Code))                              â”‚
â”‚       â”‚                                                             â”‚
â”‚       â–¼                                                             â”‚
â”‚  Cert Chain: CDI â†’ Layer 1 â†’ Layer 2 â†’ ... â†’ Application           â”‚
â”‚                                                                     â”‚
â”‚  Each layer:                                                        â”‚
â”‚  1. Derives keys from parent CDI + measurement                     â”‚
â”‚  2. Creates certificate for next layer                             â”‚
â”‚  3. Erases parent CDI from memory                                  â”‚
â”‚                                                                     â”‚
â”‚  Benefits:                                                          â”‚
â”‚  â”œâ”€â”€ Unique identity per device                                    â”‚
â”‚  â”œâ”€â”€ Identity includes all firmware                                â”‚
â”‚  â”œâ”€â”€ Key rotation on firmware update                               â”‚
â”‚  â””â”€â”€ Standardized (TCG DICE spec)                                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 3. Secure Key Provisioning

### 3.1 Key Injection

```
Manufacturing Key Injection:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  Option 1: Factory Injection                                        â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                         â”‚
â”‚  â”œâ”€â”€ Key generated in secure facility                              â”‚
â”‚  â”œâ”€â”€ Injected via programming interface                            â”‚
â”‚  â”œâ”€â”€ Key escrow for recovery                                       â”‚
â”‚  â””â”€â”€ Risk: Supply chain compromise                                 â”‚
â”‚                                                                     â”‚
â”‚  Option 2: On-Device Generation                                     â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                      â”‚
â”‚  â”œâ”€â”€ Device generates own key                                      â”‚
â”‚  â”œâ”€â”€ Public key extracted for registration                         â”‚
â”‚  â”œâ”€â”€ Private key never leaves device                               â”‚
â”‚  â””â”€â”€ Preferred for high-security applications                      â”‚
â”‚                                                                     â”‚
â”‚  Option 3: Key Agreement                                            â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                                            â”‚
â”‚  â”œâ”€â”€ Device and server perform key agreement                       â”‚
â”‚  â”œâ”€â”€ Shared secret derived                                         â”‚
â”‚  â””â”€â”€ Forward secrecy possible                                      â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    PCIe DMA Attack Surface                           â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Attack Vectors:                                                    â”‚
â”‚  â”œâ”€â”€ Malicious PCIe device (hardware implant)                      â”‚
â”‚  â”œâ”€â”€ Compromised firmware on legitimate device                     â”‚
â”‚  â”œâ”€â”€ Thunderbolt/USB4 (PCIe tunneling)                             â”‚
â”‚  â”œâ”€â”€ FireWire (legacy, still exploitable)                          â”‚
â”‚  â””â”€â”€ ExpressCard/CardBus                                           â”‚
â”‚                                                                     â”‚
â”‚  Attack Capabilities:                                               â”‚
â”‚  â”œâ”€â”€ Read arbitrary physical memory                                â”‚
â”‚  â”œâ”€â”€ Write arbitrary physical memory                               â”‚
â”‚  â”œâ”€â”€ Bypass CPU memory protections                                 â”‚
â”‚  â”œâ”€â”€ Inject code into kernel                                       â”‚
â”‚  â””â”€â”€ Extract encryption keys                                       â”‚
â”‚                                                                     â”‚
â”‚  Tools:                                                             â”‚
â”‚  â”œâ”€â”€ PCILeech: Open-source DMA attack framework                    â”‚
â”‚  â”œâ”€â”€ Inception: Firewire/Thunderbolt attack tool                   â”‚
â”‚  â””â”€â”€ LAN Turtle: Network-based physical access                     â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Mitigations:
â”œâ”€â”€ IOMMU (VT-d/AMD-Vi): Restrict device memory access
â”œâ”€â”€ Kernel DMA Protection: Pre-boot IOMMU configuration
â”œâ”€â”€ Thunderbolt security levels: User authorization
â”œâ”€â”€ Device authentication: Cryptographic device identity
â””â”€â”€ Physical port blocking: Disable unused interfaces
```

## 2. USB Security

### 2.1 USB Attack Classes

```
BadUSB:
â”œâ”€â”€ Reprogram USB device firmware
â”œâ”€â”€ Present as different device class (HID, storage)
â”œâ”€â”€ Keyboard emulation for command injection
â””â”€â”€ No signature verification on USB firmware

USB Rubber Ducky / Malicious HID:
â”œâ”€â”€ Appears as keyboard
â”œâ”€â”€ Injects keystrokes rapidly
â”œâ”€â”€ Payload execution via typing
â””â”€â”€ Bypasses most security software

USB Killer:
â”œâ”€â”€ Physical damage via voltage spike
â”œâ”€â”€ Capacitor charge/discharge
â””â”€â”€ Hardware destruction

USB Armory / LAN Turtle:
â”œâ”€â”€ Full computer in USB form factor
â”œâ”€â”€ Network attacks via USB Ethernet
â””â”€â”€ Man-in-the-middle capabilities

Mitigations:
â”œâ”€â”€ USBGuard (Linux): Device whitelisting
â”œâ”€â”€ USB Restricted Mode (iOS): Limit USB after lock
â”œâ”€â”€ USB device authentication (USB 3.x)
â”œâ”€â”€ Physical port sealing
â””â”€â”€ USB filtering policies
```

## 3. Network Interface Security

### 3.1 BMC/IPMI Attacks

```
Baseboard Management Controller Risks:
â”œâ”€â”€ Separate processor with network access
â”œâ”€â”€ Operates independently of main OS
â”œâ”€â”€ Often poor security practices
â”‚   â”œâ”€â”€ Default credentials
â”‚   â”œâ”€â”€ Unpatched firmware
â”‚   â””â”€â”€ Cleartext protocols
â”œâ”€â”€ Full system access
â”‚   â”œâ”€â”€ Remote console (KVM)
â”‚   â”œâ”€â”€ Power control
â”‚   â”œâ”€â”€ Firmware updates
â”‚   â””â”€â”€ Memory access (via PCIe)
â””â”€â”€ Difficult to monitor from host OS

Mitigation:
â”œâ”€â”€ Dedicated management network (physically isolated)
â”œâ”€â”€ Strong BMC credentials
â”œâ”€â”€ Firmware updates
â”œâ”€â”€ Disable if not needed
â””â”€â”€ Monitor BMC audit logs
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Embedded Security Constraints                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Resource Constraints:                                              â”‚
â”‚  â”œâ”€â”€ Limited CPU: MHz vs GHz                                       â”‚
â”‚  â”œâ”€â”€ Limited RAM: KB vs GB                                         â”‚
â”‚  â”œâ”€â”€ Limited storage: KB-MB vs GB-TB                               â”‚
â”‚  â”œâ”€â”€ Limited power: mW vs W                                        â”‚
â”‚  â””â”€â”€ No hardware crypto acceleration                               â”‚
â”‚                                                                     â”‚
â”‚  Physical Exposure:                                                 â”‚
â”‚  â”œâ”€â”€ Devices deployed in hostile environments                      â”‚
â”‚  â”œâ”€â”€ Physical access assumed                                       â”‚
â”‚  â”œâ”€â”€ No tamper-resistant enclosure                                 â”‚
â”‚  â””â”€â”€ Debug interfaces often accessible                             â”‚
â”‚                                                                     â”‚
â”‚  Update Challenges:                                                 â”‚
â”‚  â”œâ”€â”€ No network connectivity (some devices)                        â”‚
â”‚  â”œâ”€â”€ Limited update mechanisms                                     â”‚
â”‚  â”œâ”€â”€ Bricking risk                                                 â”‚
â”‚  â””â”€â”€ Long deployment lifetime (10+ years)                          â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Secure Boot for Embedded

```
Embedded Secure Boot Options:

MCU with Built-in Security:
â”œâ”€â”€ ARM Cortex-M33/M35P with TrustZone-M
â”œâ”€â”€ Secure boot ROM
â”œâ”€â”€ Secure key storage (OTP)
â”œâ”€â”€ Hardware crypto
â””â”€â”€ Examples: STM32L5, LPC55, nRF5340

External Secure Element:
â”œâ”€â”€ ATECC608: Crypto authentication
â”œâ”€â”€ STSAFE: Secure element
â”œâ”€â”€ SE050: EdgeLock
â””â”€â”€ Provides: Key storage, crypto, attestation

Software-Only:
â”œâ”€â”€ Verified boot chain
â”œâ”€â”€ Signature verification
â”œâ”€â”€ Limited without hardware support
â””â”€â”€ Vulnerable to physical attacks
```

## 2. Lightweight Cryptography

### 2.1 NIST Lightweight Crypto

```
NIST Lightweight Cryptography Competition Winner:

ASCON (Selected 2023):
â”œâ”€â”€ Permutation-based design
â”œâ”€â”€ AEAD: Ascon-128, Ascon-128a
â”œâ”€â”€ Hashing: Ascon-Hash, Ascon-Hasha
â”œâ”€â”€ Small code/state size
â”œâ”€â”€ Good performance on constrained devices
â””â”€â”€ Resistance to side-channel attacks

Other Lightweight Primitives:
â”œâ”€â”€ PRESENT: Block cipher (64-bit block)
â”œâ”€â”€ SIMON/SPECK: NSA lightweight ciphers
â”œâ”€â”€ PHOTON: Lightweight hash function
â”œâ”€â”€ GRAIN-128: Stream cipher
â””â”€â”€ CHASKEY: MAC for microcontrollers
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Hardware Supply Chain Threats                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Design Phase:                                                      â”‚
â”‚  â”œâ”€â”€ Malicious IP cores                                            â”‚
â”‚  â”œâ”€â”€ Hardware trojans in HDL                                       â”‚
â”‚  â”œâ”€â”€ Backdoored EDA tools                                          â”‚
â”‚  â””â”€â”€ Compromised design specifications                             â”‚
â”‚                                                                     â”‚
â”‚  Fabrication Phase:                                                 â”‚
â”‚  â”œâ”€â”€ Unauthorized modifications at foundry                         â”‚
â”‚  â”œâ”€â”€ Overproduction and grey market                                â”‚
â”‚  â”œâ”€â”€ Hardware trojans inserted during fab                          â”‚
â”‚  â””â”€â”€ Quality control bypass                                        â”‚
â”‚                                                                     â”‚
â”‚  Assembly/Test Phase:                                               â”‚
â”‚  â”œâ”€â”€ Component substitution (counterfeit)                          â”‚
â”‚  â”œâ”€â”€ Firmware tampering                                            â”‚
â”‚  â”œâ”€â”€ Additional components added                                   â”‚
â”‚  â””â”€â”€ Test interface left enabled                                   â”‚
â”‚                                                                     â”‚
â”‚  Distribution Phase:                                                â”‚
â”‚  â”œâ”€â”€ Interception and modification                                 â”‚
â”‚  â”œâ”€â”€ Repackaging with malware                                      â”‚
â”‚  â”œâ”€â”€ Firmware updates during transit                               â”‚
â”‚  â””â”€â”€ Supply chain interdiction (nation-state)                      â”‚
â”‚                                                                     â”‚
â”‚  Operational Phase:                                                 â”‚
â”‚  â”œâ”€â”€ Malicious firmware updates                                    â”‚
â”‚  â”œâ”€â”€ Compromised support tools                                     â”‚
â”‚  â””â”€â”€ Social engineering of operators                               â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Counterfeit Detection

```
Detection Methods:
â”œâ”€â”€ Visual inspection: Package markings, quality
â”œâ”€â”€ X-ray imaging: Internal structure verification
â”œâ”€â”€ Electrical testing: Parameter verification
â”œâ”€â”€ Decapsulation: Die inspection
â”œâ”€â”€ DNA marking: Unique identifiers
â””â”€â”€ Cryptographic authentication: Device certificates

Authentication:
â”œâ”€â”€ Platform Certificate: TPM-based device identity
â”œâ”€â”€ Secure device identity: DICE, SPDM
â”œâ”€â”€ Supply chain tracking: Blockchain-based provenance
â””â”€â”€ Component authentication: Chip-level crypto
```

## 2. Trusted Computing Infrastructure

### 2.1 TCG Standards

```
Trusted Computing Group Standards:

TPM (Trusted Platform Module):
â”œâ”€â”€ TPM 2.0 Library Specification
â”œâ”€â”€ PC Client Platform TPM Profile
â”œâ”€â”€ Mobile TPM Profile
â””â”€â”€ Server TPM Profile

Device Identity:
â”œâ”€â”€ DICE: Device Identifier Composition Engine
â”œâ”€â”€ Platform Certificates
â””â”€â”€ Endorsement Key hierarchies

Firmware Integrity:
â”œâ”€â”€ TCG PC Client Firmware Integrity Measurement
â”œâ”€â”€ Reference Integrity Manifest (RIM)
â””â”€â”€ TCG Firmware Update Specification

Network Security:
â”œâ”€â”€ TNC (Trusted Network Connect)
â”œâ”€â”€ IF-MAP: Security Metadata Access Protocol
â””â”€â”€ Platform Trust Services
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    TERAS Hardware Security Integration               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚                    TERAS Application                           â”‚ â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚ â”‚
â”‚  â”‚  â”‚              Hardware Abstraction Layer                  â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚  TEE      â”‚ â”‚    TPM    â”‚ â”‚   HSM     â”‚ â”‚  CPU    â”‚ â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚  Adapter  â”‚ â”‚  Adapter  â”‚ â”‚  Adapter  â”‚ â”‚ Adapter â”‚ â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚ â”€â”€â”€â”€â”€â”€â”€â”€â”€â”‚ â”‚ â”€â”€â”€â”€â”€â”€â”€â”€â”€â”‚ â”‚ â”€â”€â”€â”€â”€â”€â”€â”€â”€â”‚ â”‚â”€â”€â”€â”€â”€â”€â”€â”€â”€â”‚ â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚ SGX      â”‚ â”‚ TPM2-TSS  â”‚ â”‚ PKCS#11  â”‚ â”‚ RDRAND  â”‚ â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚ TrustZoneâ”‚ â”‚ fTPM     â”‚ â”‚ CloudHSM â”‚ â”‚ CET     â”‚ â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â”‚ SEV      â”‚ â”‚           â”‚ â”‚          â”‚ â”‚ PAC/MTE â”‚ â”‚  â”‚ â”‚
â”‚  â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚  â”‚ â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚ â”‚
â”‚  â”‚                              â”‚                                 â”‚ â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â–¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”â”‚ â”‚
â”‚  â”‚  â”‚              Security Policy Engine                        â”‚â”‚ â”‚
â”‚  â”‚  â”‚  - Feature detection                                       â”‚â”‚ â”‚
â”‚  â”‚  â”‚  - Fallback selection                                      â”‚â”‚ â”‚
â”‚  â”‚  â”‚  - Security level enforcement                              â”‚â”‚ â”‚
â”‚  â”‚  â”‚  - Attestation verification                                â”‚â”‚ â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Security Level Mapping

```
TERAS Security Levels Based on Hardware:

LEVEL 5 (Highest - Nation State Resistant):
â”œâ”€â”€ Hardware Requirements:
â”‚   â”œâ”€â”€ HSM (FIPS 140-2 Level 3+)
â”‚   â”œâ”€â”€ Discrete TPM 2.0
â”‚   â”œâ”€â”€ TEE (SGX/TrustZone)
â”‚   â”œâ”€â”€ Hardware memory encryption
â”‚   â””â”€â”€ CET/PAC enabled
â”œâ”€â”€ Use Case: Critical infrastructure, defense
â””â”€â”€ Products: SANDI (highest tier), BENTENG (government)

LEVEL 4 (High - Enterprise):
â”œâ”€â”€ Hardware Requirements:
â”‚   â”œâ”€â”€ TPM 2.0 (discrete or firmware)
â”‚   â”œâ”€â”€ Hardware crypto acceleration
â”‚   â”œâ”€â”€ IOMMU enabled
â”‚   â””â”€â”€ Secure Boot
â”œâ”€â”€ Use Case: Enterprise security
â””â”€â”€ Products: GAPURA, ZIRAH enterprise tier

LEVEL 3 (Medium - Commercial):
â”œâ”€â”€ Hardware Requirements:
â”‚   â”œâ”€â”€ Secure Boot
â”‚   â”œâ”€â”€ ASLR/DEP/NX
â”‚   â”œâ”€â”€ Hardware RNG
â”‚   â””â”€â”€ Basic TEE (TrustZone)
â”œâ”€â”€ Use Case: Commercial applications
â””â”€â”€ Products: MENARA, standard deployments

LEVEL 2 (Basic - Consumer):
â”œâ”€â”€ Hardware Requirements:
â”‚   â”œâ”€â”€ DEP/NX
â”‚   â”œâ”€â”€ Software RNG with OS entropy
â”‚   â””â”€â”€ Basic memory protection
â”œâ”€â”€ Use Case: Consumer applications
â””â”€â”€ Products: MENARA consumer tier

LEVEL 1 (Minimal - Legacy):
â”œâ”€â”€ Hardware: Any (best effort)
â”œâ”€â”€ Warning: Security significantly reduced
â””â”€â”€ Not recommended for production
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
â”œâ”€â”€ ARM TrustZone required
â”œâ”€â”€ Secure Element preferred
â”œâ”€â”€ Hardware-backed keystore (Android/iOS)
â”œâ”€â”€ Biometric integration (TEE)
â””â”€â”€ Attestation: SafetyNet/App Attest

GAPURA (WAF):
â”œâ”€â”€ Server-grade hardware
â”œâ”€â”€ Hardware AES-NI for TLS
â”œâ”€â”€ RDRAND for session tokens
â”œâ”€â”€ Optional HSM for key management
â””â”€â”€ High-throughput crypto

ZIRAH (EDR):
â”œâ”€â”€ TPM for measured boot
â”œâ”€â”€ CET/PAC for exploit mitigation
â”œâ”€â”€ Hardware perf counters for anomaly detection
â”œâ”€â”€ IOMMU for device isolation
â””â”€â”€ Memory encryption for forensic protection

BENTENG (eKYC):
â”œâ”€â”€ HSM for identity key protection
â”œâ”€â”€ TEE for biometric processing
â”œâ”€â”€ Secure Element for credential storage
â”œâ”€â”€ Hardware attestation for device binding
â””â”€â”€ Tamper detection integration

SANDI (Digital Signatures):
â”œâ”€â”€ HSM required for signing keys
â”œâ”€â”€ TPM for audit logging integrity
â”œâ”€â”€ Timestamping hardware
â”œâ”€â”€ FIPS 140-2 Level 3 minimum
â””â”€â”€ Air-gapped HSM option
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

*Research Track Output â€” Domain D: Hardware Security*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
