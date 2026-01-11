# TERAS-LANG Research Domain I: Operating Systems Security

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-I-OS-SECURITY |
| Version | 1.0.0 |
| Date | 2026-01-04 |
| Sessions | I-01 through I-10 |
| Domain | I: Operating Systems Security |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# I-01: Security Kernel and TCB Fundamentals

## Executive Summary

Operating system security forms the foundation upon which all application security is built. This domain covers secure OS design, verified kernels, capability-based systems, and their relevance to TERAS platform deployment.

## 1. Trusted Computing Base (TCB)

### 1.1 TCB Concepts

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Trusted Computing Base                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Definition:                                                        â”‚
â”‚  The TCB is the totality of protection mechanisms within a          â”‚
â”‚  computer system responsible for enforcing security policy.         â”‚
â”‚                                                                     â”‚
â”‚  TCB Components:                                                    â”‚
â”‚  â”œâ”€â”€ Hardware: CPU, MMU, security coprocessors                     â”‚
â”‚  â”œâ”€â”€ Firmware: BIOS/UEFI, microcode                                â”‚
â”‚  â”œâ”€â”€ OS Kernel: Process isolation, access control                  â”‚
â”‚  â”œâ”€â”€ Security services: Authentication, audit                      â”‚
â”‚  â””â”€â”€ Trusted applications: Security-critical code                  â”‚
â”‚                                                                     â”‚
â”‚  TCB Principles:                                                    â”‚
â”‚  â”œâ”€â”€ Minimization: Smaller TCB = smaller attack surface            â”‚
â”‚  â”œâ”€â”€ Verification: TCB should be formally verified                 â”‚
â”‚  â”œâ”€â”€ Isolation: TCB protected from non-TCB components              â”‚
â”‚  â””â”€â”€ Completeness: All security-relevant ops go through TCB        â”‚
â”‚                                                                     â”‚
â”‚  Reference Monitor:                                                 â”‚
â”‚  â”œâ”€â”€ Mediates all access to objects                                â”‚
â”‚  â”œâ”€â”€ Properties:                                                   â”‚
â”‚  â”‚   â”œâ”€â”€ Complete mediation: All accesses checked                  â”‚
â”‚  â”‚   â”œâ”€â”€ Tamperproof: Cannot be modified by untrusted code        â”‚
â”‚  â”‚   â””â”€â”€ Verifiable: Small enough to analyze                       â”‚
â”‚  â””â”€â”€ Implementation: Security kernel                               â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 TCB Size Comparison

```
System                      â”‚ TCB Size (LOC)  â”‚ Verified
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
seL4 microkernel            â”‚ ~10,000         â”‚ Yes (full)
MINIX 3                     â”‚ ~6,000 (kernel) â”‚ Partial
L4 family                   â”‚ ~10-15,000      â”‚ Some variants
Windows kernel              â”‚ ~50,000,000+    â”‚ No
Linux kernel                â”‚ ~30,000,000+    â”‚ No
macOS kernel (XNU)          â”‚ ~5,000,000+     â”‚ No

TCB Size Impact:
â”œâ”€â”€ Every 1000 LOC: ~15 bugs on average
â”œâ”€â”€ Larger TCB: More potential vulnerabilities
â”œâ”€â”€ Verification cost: Grows with size
â””â”€â”€ Practical limit for full verification: ~50,000 LOC
```

## 2. Security Kernel Designs

### 2.1 Monolithic vs Microkernel

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Kernel Architecture Comparison                    â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  MONOLITHIC KERNEL (Linux, Windows):                                â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                      User Space                              â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”        â”‚   â”‚
â”‚  â”‚  â”‚  App 1  â”‚  â”‚  App 2  â”‚  â”‚  App 3  â”‚  â”‚  App N  â”‚        â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜        â”‚   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤   â”‚
â”‚  â”‚                      Kernel Space (TCB)                      â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚ Process  â”‚ Memory â”‚ Filesystem â”‚ Network â”‚ Drivers  â”‚    â”‚   â”‚
â”‚  â”‚  â”‚ Mgmt     â”‚ Mgmt   â”‚            â”‚ Stack   â”‚          â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚  TCB: Everything in kernel space                                   â”‚
â”‚                                                                     â”‚
â”‚  MICROKERNEL (seL4, MINIX 3):                                       â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                      User Space                              â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”        â”‚   â”‚
â”‚  â”‚  â”‚  App 1  â”‚  â”‚  App 2  â”‚  â”‚ Network â”‚  â”‚Filesystemâ”‚        â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚ Server  â”‚  â”‚ Server  â”‚        â”‚   â”‚
â”‚  â”‚                            â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜        â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”                                   â”‚   â”‚
â”‚  â”‚  â”‚ Device  â”‚  â”‚ Memory  â”‚                                   â”‚   â”‚
â”‚  â”‚  â”‚ Drivers â”‚  â”‚ Server  â”‚                                   â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                                   â”‚   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤   â”‚
â”‚  â”‚           Kernel Space (TCB - Minimal)                       â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚   â”‚
â”‚  â”‚  â”‚  IPC  â”‚  Scheduling  â”‚  Memory (basic)  â”‚  Capability â”‚  â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚  TCB: Only microkernel (much smaller)                              â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## TERAS Decision I-01

**FOR TERAS:**
1. Prefer microkernel-based platforms where possible
2. Document TCB for each deployment model
3. Minimize TERAS components in TCB
4. Formal verification for security-critical paths

### Architecture Decision ID: `TERAS-ARCH-I01-TCB-001`

---

# I-02: seL4 - Verified Microkernel

## 1. seL4 Architecture

### 1.1 Overview

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    seL4 Microkernel Architecture                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Verification Status:                                               â”‚
â”‚  â”œâ”€â”€ Functional correctness: Proved                                â”‚
â”‚  â”œâ”€â”€ Implementation matches spec: Proved                           â”‚
â”‚  â”œâ”€â”€ Binary matches C code: Proved (some platforms)                â”‚
â”‚  â”œâ”€â”€ Security properties: Proved                                   â”‚
â”‚  â”‚   â”œâ”€â”€ Confidentiality (no information leakage)                 â”‚
â”‚  â”‚   â”œâ”€â”€ Integrity (no unauthorized modification)                 â”‚
â”‚  â”‚   â””â”€â”€ Availability (no denial of service by user code)         â”‚
â”‚  â””â”€â”€ Timing channels: NOT addressed (ongoing work)                 â”‚
â”‚                                                                     â”‚
â”‚  Kernel Services (minimal):                                         â”‚
â”‚  â”œâ”€â”€ Threads: Execution contexts                                   â”‚
â”‚  â”œâ”€â”€ Address spaces: Virtual memory                                â”‚
â”‚  â”œâ”€â”€ IPC: Synchronous message passing                              â”‚
â”‚  â”œâ”€â”€ Notifications: Asynchronous signals                           â”‚
â”‚  â”œâ”€â”€ Capabilities: Access control                                  â”‚
â”‚  â””â”€â”€ Interrupts: Delivered as notifications                        â”‚
â”‚                                                                     â”‚
â”‚  Everything Else: User-level servers                                â”‚
â”‚  â”œâ”€â”€ Device drivers                                                â”‚
â”‚  â”œâ”€â”€ File systems                                                  â”‚
â”‚  â”œâ”€â”€ Network stack                                                 â”‚
â”‚  â”œâ”€â”€ Memory management (beyond basic)                              â”‚
â”‚  â””â”€â”€ OS personality (Linux, POSIX, etc.)                           â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Capability System

```
seL4 Capability Model:

Capability Structure:
â”œâ”€â”€ Object reference: Pointer to kernel object
â”œâ”€â”€ Access rights: Permissions bitmap
â””â”€â”€ Badge: Unforgeable identifier

Capability Operations:
â”œâ”€â”€ Invoke: Use capability to perform operation
â”œâ”€â”€ Copy: Duplicate capability (possibly with reduced rights)
â”œâ”€â”€ Grant: Transfer capability to another thread
â”œâ”€â”€ Mint: Create derived capability with badge
â””â”€â”€ Revoke: Recursively revoke all derived capabilities

Example Objects and Capabilities:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Object Type        â”‚ Capability Operations                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ TCB (Thread)       â”‚ Suspend, Resume, Configure, ReadRegisters  â”‚
â”‚ CNode (Cap table)  â”‚ Copy, Mint, Delete, Revoke, Rotate         â”‚
â”‚ Untyped            â”‚ Retype (create new objects)                â”‚
â”‚ Endpoint           â”‚ Send, Receive, Grant                       â”‚
â”‚ Notification       â”‚ Signal, Wait                               â”‚
â”‚ Page               â”‚ Map, Unmap, GetAddress                     â”‚
â”‚ PageTable          â”‚ Map, Unmap                                 â”‚
â”‚ IRQHandler         â”‚ Acknowledge, SetNotification               â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.3 seL4 Proof Structure

```
Verification Layers:

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  Abstract Specification (Isabelle/HOL)                              â”‚
â”‚  â”œâ”€â”€ High-level description of kernel behavior                     â”‚
â”‚  â”œâ”€â”€ Defines what the kernel should do                             â”‚
â”‚  â””â”€â”€ ~5,700 lines of Isabelle                                      â”‚
â”‚                              â†“ Refinement proof                     â”‚
â”‚  Executable Specification (Haskell)                                 â”‚
â”‚  â”œâ”€â”€ Algorithmic description                                       â”‚
â”‚  â”œâ”€â”€ Testable prototype                                            â”‚
â”‚  â””â”€â”€ ~10,000 lines of Haskell                                      â”‚
â”‚                              â†“ Refinement proof                     â”‚
â”‚  C Implementation                                                   â”‚
â”‚  â”œâ”€â”€ Actual implementation                                         â”‚
â”‚  â”œâ”€â”€ Manually written, guided by spec                              â”‚
â”‚  â””â”€â”€ ~10,000 lines of C                                            â”‚
â”‚                              â†“ Translation validation               â”‚
â”‚  Binary (ARM, x86, RISC-V)                                          â”‚
â”‚  â”œâ”€â”€ Compiled from C                                               â”‚
â”‚  â””â”€â”€ Binary verification (some platforms)                          â”‚
â”‚                                                                     â”‚
â”‚  Proof Effort: ~200,000 lines of Isabelle proof                    â”‚
â”‚  Person-years: ~20 for initial proof                               â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 2. seL4-Based Systems

### 2.1 CAmkES Component Framework

```
CAmkES Component Example:

/* Component definition */
component SecureStorage {
    control;  /* Has main thread */
    
    /* Provided interface */
    provides StorageInterface storage;
    
    /* Required interface */
    uses EncryptionInterface crypto;
    
    /* Dataport (shared memory) */
    dataport Buf(4096) data_buffer;
    
    /* Configuration */
    has mutex lock;
}

/* Assembly connecting components */
assembly {
    composition {
        component SecureStorage storage;
        component CryptoServer crypto;
        component Application app;
    }
    
    connection {
        /* RPC connection */
        seL4RPCCall storage_conn(from app.storage, to storage.storage);
        
        /* Crypto connection */
        seL4RPCCall crypto_conn(from storage.crypto, to crypto.encrypt);
        
        /* Shared memory */
        seL4SharedData data_conn(from app.buffer, to storage.data_buffer);
    }
    
    configuration {
        /* Security policy */
        storage.storage_access = "app";
        crypto.integrity = "high";
    }
}
```

### 2.2 seL4 Deployments

```
Production Uses:
â”œâ”€â”€ DARPA HACMS: Unhackable military helicopter
â”œâ”€â”€ Genode OS Framework: General-purpose seL4 port
â”œâ”€â”€ Trustworthy Systems: Defense applications
â”œâ”€â”€ HENSOLDT Cyber: Secure gateway products
â””â”€â”€ Ghost Locomotion: Autonomous vehicle systems

TERAS Relevance:
â”œâ”€â”€ Highest assurance deployments
â”œâ”€â”€ Defense/government customers
â”œâ”€â”€ Critical infrastructure
â””â”€â”€ Air-gapped secure systems
```

## TERAS Decision I-02

**FOR TERAS:**
1. Support seL4 for highest-assurance deployments
2. Develop CAmkES components for TERAS
3. Leverage capability model for TERAS isolation
4. Target seL4 for SANDI secure signing

### Architecture Decision ID: `TERAS-ARCH-I02-SEL4-001`

---

# I-03: Capability-Based Operating Systems

## 1. Capability System Theory

### 1.1 Capability Concepts

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Capability-Based Security                         â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Capability Definition:                                             â”‚
â”‚  An unforgeable token that grants specific access rights to a       â”‚
â”‚  specific object.                                                   â”‚
â”‚                                                                     â”‚
â”‚  Capability = (Object Reference, Access Rights)                     â”‚
â”‚                                                                     â”‚
â”‚  Key Properties:                                                    â”‚
â”‚  â”œâ”€â”€ Unforgeable: Cannot create without proper authority           â”‚
â”‚  â”œâ”€â”€ Transferable: Can be passed to other processes                â”‚
â”‚  â”œâ”€â”€ Specific: Identifies exact object and permissions             â”‚
â”‚  â””â”€â”€ Principle of Least Privilege: Natural fit                     â”‚
â”‚                                                                     â”‚
â”‚  Capability vs ACL:                                                 â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  ACL (Access Control List):                                  â”‚   â”‚
â”‚  â”‚  Object â†’ [(Subject, Rights), ...]                          â”‚   â”‚
â”‚  â”‚  "Who can access this object?"                              â”‚   â”‚
â”‚  â”‚  Check: Is subject in object's ACL?                         â”‚   â”‚
â”‚  â”‚                                                              â”‚   â”‚
â”‚  â”‚  Capability List:                                            â”‚   â”‚
â”‚  â”‚  Subject â†’ [(Object, Rights), ...]                          â”‚   â”‚
â”‚  â”‚  "What can this subject access?"                            â”‚   â”‚
â”‚  â”‚  Check: Does subject have capability for object?            â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  Capability Advantages:                                             â”‚
â”‚  â”œâ”€â”€ Delegation: Easy to grant subset of access                    â”‚
â”‚  â”œâ”€â”€ Revocation: More complex but possible                         â”‚
â”‚  â”œâ”€â”€ Confused deputy prevention: Natural defense                   â”‚
â”‚  â””â”€â”€ Least privilege: Fine-grained permissions                     â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Confused Deputy Problem

```
Confused Deputy Attack:

Scenario:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  User â”€â”€requestâ”€â”€â–º Compiler â”€â”€writeâ”€â”€â–º /billing/user_file          â”‚
â”‚                      â”‚                                              â”‚
â”‚                      â”‚ Compiler has write access to billing dir     â”‚
â”‚                      â”‚ for legitimate logging purposes              â”‚
â”‚                      â”‚                                              â”‚
â”‚  Attacker â”€â”€â”€â”€â”€â”€â”€â”€â”€â–º Compiler â”€â”€writeâ”€â”€â–º /billing/important_file   â”‚
â”‚           (malicious output path)                                   â”‚
â”‚                                                                     â”‚
â”‚  Problem: Compiler uses its own authority, not user's              â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Capability Solution:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  User â”€â”€(capability to user_file)â”€â”€â–º Compiler                      â”‚
â”‚                                         â”‚                           â”‚
â”‚                                         â”‚ Can only write where     â”‚
â”‚                                         â”‚ user has capability      â”‚
â”‚                                         â–¼                           â”‚
â”‚                                      /user/output.o                 â”‚
â”‚                                                                     â”‚
â”‚  Attacker cannot forge capability to /billing/important_file       â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 2. Capability Operating Systems

### 2.1 CHERI (Capability Hardware Enhanced RISC Instructions)

```
CHERI Architecture:

Hardware Capabilities:
â”œâ”€â”€ 128-bit or 256-bit capability registers
â”œâ”€â”€ Bounds: Base address and length
â”œâ”€â”€ Permissions: Read, write, execute, etc.
â”œâ”€â”€ Sealed: Cannot be modified
â””â”€â”€ Compartment ID: For cross-domain calls

Capability Format (128-bit):
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Tag â”‚ Permissions â”‚ Object Type â”‚ Bounds â”‚ Offset â”‚ Address        â”‚
â”‚ 1b  â”‚    15b      â”‚     4b      â”‚  ~40b  â”‚  ~20b  â”‚    ~48b        â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Memory Safety:
â”œâ”€â”€ All pointers are capabilities
â”œâ”€â”€ Bounds checked on every access
â”œâ”€â”€ Cannot forge pointers
â”œâ”€â”€ Spatial safety: No out-of-bounds access
â””â”€â”€ Temporal safety: With revocation

CHERI Implementations:
â”œâ”€â”€ CHERI-MIPS: Research processor
â”œâ”€â”€ CHERI-RISC-V: Morello prototype
â”œâ”€â”€ Arm Morello: Production board (2022)
â””â”€â”€ CHERIoT: For embedded/IoT
```

### 2.2 Capsicum (FreeBSD)

```
Capsicum Capability Mode:

Enter Capability Mode:
cap_enter()  /* Process can no longer access global namespace */

After cap_enter():
â”œâ”€â”€ Cannot open files by path
â”œâ”€â”€ Cannot create sockets by address
â”œâ”€â”€ Must use pre-opened descriptors
â””â”€â”€ Capabilities = file descriptors + rights

Capability Rights:
CAP_READ        /* Read from descriptor */
CAP_WRITE       /* Write to descriptor */
CAP_SEEK        /* Seek on descriptor */
CAP_MMAP        /* Memory map descriptor */
CAP_FSTAT       /* Get descriptor status */
CAP_FSYNC       /* Sync descriptor */
CAP_FTRUNCATE   /* Truncate descriptor */
CAP_LOOKUP      /* Look up in directory (limited) */
CAP_CREATE      /* Create in directory */
CAP_DELETE      /* Delete in directory */
...

Example: Sandboxed Image Converter
int main(int argc, char *argv[]) {
    int input_fd = open(argv[1], O_RDONLY);
    int output_fd = open(argv[2], O_WRONLY | O_CREAT);
    
    /* Restrict rights */
    cap_rights_t rights;
    cap_rights_init(&rights, CAP_READ, CAP_MMAP);
    cap_rights_limit(input_fd, &rights);
    
    cap_rights_init(&rights, CAP_WRITE);
    cap_rights_limit(output_fd, &rights);
    
    /* Enter capability mode */
    cap_enter();
    
    /* Now sandboxed - can only use input_fd and output_fd */
    convert_image(input_fd, output_fd);
    
    return 0;
}
```

## TERAS Decision I-03

**FOR TERAS:**
1. Use capability model for TERAS internal architecture
2. Support Capsicum sandboxing on FreeBSD
3. Design for CHERI when hardware available
4. Capability-based API for TERAS libraries

### Architecture Decision ID: `TERAS-ARCH-I03-CAPABILITY-001`

---

# I-04: Linux Security Mechanisms

## 1. Linux Security Modules (LSM)

### 1.1 LSM Framework

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Linux Security Modules                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  LSM Hook Points:                                                   â”‚
â”‚  â”œâ”€â”€ Task hooks: fork, exec, setuid                                â”‚
â”‚  â”œâ”€â”€ File hooks: open, read, write, mmap                           â”‚
â”‚  â”œâ”€â”€ Inode hooks: create, link, unlink, permission                 â”‚
â”‚  â”œâ”€â”€ Socket hooks: create, bind, connect, accept                   â”‚
â”‚  â”œâ”€â”€ Network hooks: packet filtering, labeling                     â”‚
â”‚  â””â”€â”€ IPC hooks: shm, msg, sem operations                           â”‚
â”‚                                                                     â”‚
â”‚  LSM Implementations:                                               â”‚
â”‚  â”œâ”€â”€ SELinux: Mandatory access control                             â”‚
â”‚  â”œâ”€â”€ AppArmor: Path-based MAC                                      â”‚
â”‚  â”œâ”€â”€ Smack: Simplified MAC                                         â”‚
â”‚  â”œâ”€â”€ TOMOYO: Learning-based MAC                                    â”‚
â”‚  â”œâ”€â”€ Yama: ptrace restrictions                                     â”‚
â”‚  â””â”€â”€ LoadPin: Module loading restrictions                          â”‚
â”‚                                                                     â”‚
â”‚  LSM Stacking (since 5.1):                                          â”‚
â”‚  â”œâ”€â”€ Multiple minor LSMs can coexist                               â”‚
â”‚  â”œâ”€â”€ One major LSM (SELinux/AppArmor/Smack)                        â”‚
â”‚  â””â”€â”€ Chain of hooks evaluated                                      â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Seccomp-BPF

```c
// Seccomp-BPF Filter Example

#include <linux/seccomp.h>
#include <linux/filter.h>
#include <sys/prctl.h>

// BPF filter to allow only specific syscalls
struct sock_filter filter[] = {
    /* Load syscall number */
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, 
             offsetof(struct seccomp_data, nr)),
    
    /* Allow read */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_read, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    
    /* Allow write */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_write, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    
    /* Allow exit_group */
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_exit_group, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    
    /* Kill on any other syscall */
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL),
};

struct sock_fprog prog = {
    .len = sizeof(filter) / sizeof(filter[0]),
    .filter = filter,
};

void apply_seccomp() {
    prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
    prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog);
}

// Using libseccomp (higher-level)
#include <seccomp.h>

void apply_seccomp_easy() {
    scmp_filter_ctx ctx = seccomp_init(SCMP_ACT_KILL);
    
    seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(read), 0);
    seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(write), 0);
    seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(exit_group), 0);
    
    /* Allow write only to stdout/stderr */
    seccomp_rule_add(ctx, SCMP_ACT_ALLOW, SCMP_SYS(write), 1,
                     SCMP_A0(SCMP_CMP_LE, 2));
    
    seccomp_load(ctx);
    seccomp_release(ctx);
}
```

## 2. Namespaces and Cgroups

### 2.1 Linux Namespaces

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Linux Namespaces                                  â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Namespace Types:                                                   â”‚
â”‚  â”œâ”€â”€ Mount (mnt): File system mount points                         â”‚
â”‚  â”œâ”€â”€ UTS: Hostname and domain name                                 â”‚
â”‚  â”œâ”€â”€ IPC: System V IPC, POSIX message queues                       â”‚
â”‚  â”œâ”€â”€ Network (net): Network devices, ports, routing                â”‚
â”‚  â”œâ”€â”€ PID: Process IDs                                              â”‚
â”‚  â”œâ”€â”€ User: User and group IDs                                      â”‚
â”‚  â”œâ”€â”€ Cgroup: Cgroup root directory                                 â”‚
â”‚  â””â”€â”€ Time: System time (since 5.6)                                 â”‚
â”‚                                                                     â”‚
â”‚  Operations:                                                        â”‚
â”‚  â”œâ”€â”€ clone(CLONE_NEWNS | CLONE_NEWPID | ...)                       â”‚
â”‚  â”œâ”€â”€ unshare(CLONE_NEWNET)                                         â”‚
â”‚  â””â”€â”€ setns(fd, CLONE_NEWUSER)                                      â”‚
â”‚                                                                     â”‚
â”‚  Container Isolation:                                               â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  Container = Namespaces + Cgroups + Seccomp + Capabilities  â”‚   â”‚
â”‚  â”‚                                                              â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚                    Container                         â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â”œâ”€â”€ Own filesystem (mnt ns)                        â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â”œâ”€â”€ Own network (net ns)                           â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â”œâ”€â”€ Own PIDs (pid ns)                              â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â”œâ”€â”€ Resource limits (cgroups)                      â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â”œâ”€â”€ Syscall filter (seccomp)                       â”‚    â”‚   â”‚
â”‚  â”‚  â”‚  â””â”€â”€ Limited capabilities                           â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 User Namespaces Security

```
User Namespace Isolation:

Mapping:
â”œâ”€â”€ Container UID 0 â†’ Host UID 100000
â”œâ”€â”€ Container UID 1 â†’ Host UID 100001
â”œâ”€â”€ ...
â””â”€â”€ Unprivileged in host, privileged in container

Security Implications:
â”œâ”€â”€ Root in container â‰  root on host
â”œâ”€â”€ CAP_SYS_ADMIN in container = limited
â”œâ”€â”€ Can create other namespaces
â””â”€â”€ Enables rootless containers

Risks:
â”œâ”€â”€ Kernel attack surface expanded
â”œâ”€â”€ New code paths for unprivileged users
â”œâ”€â”€ CVEs in user namespace handling
â””â”€â”€ Often disabled in production

Configuration:
# Enable user namespaces
echo 1 > /proc/sys/kernel/unprivileged_userns_clone

# Or disable for security
echo 0 > /proc/sys/kernel/unprivileged_userns_clone
```

## TERAS Decision I-04

**FOR TERAS:**
1. Use seccomp-bpf for all TERAS processes
2. Provide seccomp profiles for each component
3. Support namespace isolation where appropriate
4. Document SELinux/AppArmor requirements

### Architecture Decision ID: `TERAS-ARCH-I04-LINUX-001`

---

# I-05: Process and Memory Isolation

## 1. Address Space Isolation

### 1.1 Memory Protection Mechanisms

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Memory Isolation Mechanisms                       â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  VIRTUAL MEMORY:                                                    â”‚
â”‚  â”œâ”€â”€ Each process has own address space                            â”‚
â”‚  â”œâ”€â”€ Page tables translate virtual â†’ physical                      â”‚
â”‚  â”œâ”€â”€ Hardware enforced (MMU)                                       â”‚
â”‚  â””â”€â”€ Kernel manages mappings                                       â”‚
â”‚                                                                     â”‚
â”‚  PAGE PERMISSIONS:                                                  â”‚
â”‚  â”œâ”€â”€ Read (R): Can read memory                                     â”‚
â”‚  â”œâ”€â”€ Write (W): Can write memory                                   â”‚
â”‚  â”œâ”€â”€ Execute (X): Can execute code                                 â”‚
â”‚  â”œâ”€â”€ User/Supervisor: Ring 3 vs Ring 0                             â”‚
â”‚  â””â”€â”€ NX bit: No-execute for data pages                             â”‚
â”‚                                                                     â”‚
â”‚  W^X (Write XOR Execute):                                           â”‚
â”‚  â”œâ”€â”€ Page cannot be both writable and executable                   â”‚
â”‚  â”œâ”€â”€ Prevents code injection                                       â”‚
â”‚  â”œâ”€â”€ Enforced by modern OSes                                       â”‚
â”‚  â””â”€â”€ JIT must use mprotect() carefully                             â”‚
â”‚                                                                     â”‚
â”‚  ASLR (Address Space Layout Randomization):                         â”‚
â”‚  â”œâ”€â”€ Stack: Random offset                                          â”‚
â”‚  â”œâ”€â”€ Heap: Random base                                             â”‚
â”‚  â”œâ”€â”€ Libraries: Random load addresses                              â”‚
â”‚  â”œâ”€â”€ Executable: PIE (Position Independent Executable)             â”‚
â”‚  â””â”€â”€ Entropy: ~28-30 bits on 64-bit                                â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Kernel Address Space Isolation

```
KPTI (Kernel Page Table Isolation):

Purpose: Mitigate Meltdown attack

Before KPTI:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚         User Page Tables                â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚
â”‚  â”‚  User Space (accessible)          â”‚  â”‚
â”‚  â”‚  Kernel Space (mapped, but        â”‚  â”‚
â”‚  â”‚               supervisor-only)    â”‚  â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
Meltdown: Speculative execution could read kernel

After KPTI:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚         User Page Tables                â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚
â”‚  â”‚  User Space (accessible)          â”‚  â”‚
â”‚  â”‚  Minimal kernel (syscall entry)   â”‚  â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚         Kernel Page Tables              â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚
â”‚  â”‚  Full kernel (only during syscall)â”‚  â”‚
â”‚  â”‚  User space                       â”‚  â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
Kernel not mapped in user mode â†’ no Meltdown
```

## 2. Sandboxing Technologies

### 2.1 Chrome Sandbox Architecture

```
Chrome Multi-Process Architecture:

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚  â”‚                     Browser Process                            â”‚ â”‚
â”‚  â”‚  - UI, network I/O, file system                               â”‚ â”‚
â”‚  â”‚  - Full privileges                                            â”‚ â”‚
â”‚  â”‚  - Broker for sandboxed processes                             â”‚ â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â”‚                              â”‚                                      â”‚
â”‚           â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                  â”‚
â”‚           â”‚                  â”‚                  â”‚                   â”‚
â”‚           â–¼                  â–¼                  â–¼                   â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”       â”‚
â”‚  â”‚  Renderer 1     â”‚ â”‚  Renderer 2     â”‚ â”‚  GPU Process    â”‚       â”‚
â”‚  â”‚  (sandboxed)    â”‚ â”‚  (sandboxed)    â”‚ â”‚  (sandboxed)    â”‚       â”‚
â”‚  â”‚  - Seccomp-BPF  â”‚ â”‚  - Seccomp-BPF  â”‚ â”‚  - Seccomp-BPF  â”‚       â”‚
â”‚  â”‚  - Namespaces   â”‚ â”‚  - Namespaces   â”‚ â”‚  - Limited caps â”‚       â”‚
â”‚  â”‚  - No network   â”‚ â”‚  - No network   â”‚ â”‚                 â”‚       â”‚
â”‚  â”‚  - No filesystemâ”‚ â”‚  - No filesystemâ”‚ â”‚                 â”‚       â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜       â”‚
â”‚                                                                     â”‚
â”‚  Sandbox Layers:                                                    â”‚
â”‚  â”œâ”€â”€ Layer 1: seccomp-BPF (syscall filtering)                      â”‚
â”‚  â”œâ”€â”€ Layer 2: Namespaces (PID, network, user)                      â”‚
â”‚  â”œâ”€â”€ Layer 3: Capabilities (dropped)                               â”‚
â”‚  â””â”€â”€ Layer 4: chroot/pivot_root (filesystem)                       â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 gVisor and Firecracker

```
gVisor (Google):
â”œâ”€â”€ User-space kernel
â”œâ”€â”€ Intercepts syscalls via ptrace or KVM
â”œâ”€â”€ Implements Linux syscalls in Go
â”œâ”€â”€ Reduced kernel attack surface
â”œâ”€â”€ Container runtime: runsc
â””â”€â”€ Performance overhead: Significant for syscall-heavy workloads

Firecracker (AWS):
â”œâ”€â”€ MicroVM monitor
â”œâ”€â”€ Minimal virtual machine
â”œâ”€â”€ KVM-based
â”œâ”€â”€ ~125ms boot time
â”œâ”€â”€ <5 MB memory overhead
â”œâ”€â”€ Used by AWS Lambda, Fargate
â””â”€â”€ Security: VM isolation > container isolation
```

## TERAS Decision I-05

**FOR TERAS:**
1. Multi-process architecture with isolation
2. Use seccomp + namespaces for TERAS components
3. Consider gVisor for additional isolation
4. Document isolation boundaries

### Architecture Decision ID: `TERAS-ARCH-I05-ISOLATION-001`

---

# I-06: File System Security

## 1. File System Access Control

### 1.1 Permission Models

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    File System Permission Models                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  UNIX PERMISSIONS (Traditional):                                    â”‚
â”‚  -rwxr-xr-x  1  owner  group  size  date  filename                 â”‚
â”‚   â”‚â”‚â”‚ â”‚â”‚â”‚ â”‚â”‚â”‚                                                       â”‚
â”‚   â”‚â”‚â”‚ â”‚â”‚â”‚ â””â”´â”´â”€â”€ Others: r-x (read, execute)                        â”‚
â”‚   â”‚â”‚â”‚ â””â”´â”´â”€â”€â”€â”€â”€â”€ Group: r-x (read, execute)                         â”‚
â”‚   â””â”´â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ Owner: rwx (read, write, execute)                  â”‚
â”‚                                                                     â”‚
â”‚  Special Bits:                                                      â”‚
â”‚  â”œâ”€â”€ setuid (4xxx): Run as file owner                              â”‚
â”‚  â”œâ”€â”€ setgid (2xxx): Run as file group                              â”‚
â”‚  â””â”€â”€ sticky (1xxx): Delete only by owner (directories)             â”‚
â”‚                                                                     â”‚
â”‚  POSIX ACLs (Extended):                                             â”‚
â”‚  # getfacl file                                                     â”‚
â”‚  user::rwx                                                          â”‚
â”‚  user:alice:r-x                                                     â”‚
â”‚  group::r-x                                                         â”‚
â”‚  group:developers:rwx                                               â”‚
â”‚  mask::rwx                                                          â”‚
â”‚  other::---                                                         â”‚
â”‚                                                                     â”‚
â”‚  Extended Attributes:                                               â”‚
â”‚  â”œâ”€â”€ security.*: SELinux labels                                    â”‚
â”‚  â”œâ”€â”€ system.*: ACLs, capabilities                                  â”‚
â”‚  â”œâ”€â”€ trusted.*: Requires CAP_SYS_ADMIN                             â”‚
â”‚  â””â”€â”€ user.*: User-defined                                          â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 File System Capabilities

```
Linux Capabilities on Files:

# Set capability on executable
setcap cap_net_bind_service=+ep /usr/bin/myserver

Capability Sets:
â”œâ”€â”€ Permitted (p): Can be acquired
â”œâ”€â”€ Inheritable (i): Preserved across exec
â”œâ”€â”€ Effective (e): Currently active
â””â”€â”€ Ambient: Inherited by non-setuid programs

Common File Capabilities:
â”œâ”€â”€ cap_net_bind_service: Bind ports <1024
â”œâ”€â”€ cap_net_raw: Raw sockets
â”œâ”€â”€ cap_sys_admin: Various admin functions
â”œâ”€â”€ cap_dac_override: Bypass file permissions
â””â”€â”€ cap_setuid/cap_setgid: Change UID/GID

Security Considerations:
â”œâ”€â”€ Capabilities are NOT namespaced (mostly)
â”œâ”€â”€ Can grant partial root-like abilities
â”œâ”€â”€ More granular than setuid
â””â”€â”€ Still requires careful management
```

## 2. Integrity Protection

### 2.1 dm-verity and fs-verity

```
dm-verity (Block-level):

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                     Merkle Tree                              â”‚   â”‚
â”‚  â”‚                        Root Hash                             â”‚   â”‚
â”‚  â”‚                       /        \                             â”‚   â”‚
â”‚  â”‚                    Hash         Hash                         â”‚   â”‚
â”‚  â”‚                   /    \       /    \                        â”‚   â”‚
â”‚  â”‚                 H0     H1    H2     H3                       â”‚   â”‚
â”‚  â”‚                 â”‚      â”‚      â”‚      â”‚                       â”‚   â”‚
â”‚  â”‚  Data Blocks: [B0]   [B1]   [B2]   [B3]                     â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  Read Operation:                                                    â”‚
â”‚  1. Read data block                                                â”‚
â”‚  2. Read hash tree path to root                                    â”‚
â”‚  3. Verify hash chain                                              â”‚
â”‚  4. If mismatch â†’ return I/O error                                 â”‚
â”‚                                                                     â”‚
â”‚  Use Cases:                                                         â”‚
â”‚  â”œâ”€â”€ Android Verified Boot                                         â”‚
â”‚  â”œâ”€â”€ Chrome OS rootfs                                              â”‚
â”‚  â””â”€â”€ Read-only system partitions                                   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

fs-verity (File-level):
â”œâ”€â”€ Per-file Merkle tree
â”œâ”€â”€ Enabled on individual files
â”œâ”€â”€ Works with any filesystem supporting it (ext4, f2fs, btrfs)
â”œâ”€â”€ File becomes read-only after enabling
â””â”€â”€ Used by APK v4 signature
```

### 2.2 IMA/EVM (Integrity Measurement Architecture)

```
IMA (Integrity Measurement Architecture):

Measurement:
â”œâ”€â”€ Record hash of files before use
â”œâ”€â”€ Store in TPM PCR (extend)
â”œâ”€â”€ Create IMA measurement list
â””â”€â”€ Enable remote attestation

Appraisal:
â”œâ”€â”€ Compare hash against known-good
â”œâ”€â”€ Block execution if mismatch
â”œâ”€â”€ Signed policy for expected hashes
â””â”€â”€ Boot-time enforcement

EVM (Extended Verification Module):
â”œâ”€â”€ Protect extended attributes
â”œâ”€â”€ HMAC or digital signature
â”œâ”€â”€ Prevents offline tampering
â””â”€â”€ Requires IMA

IMA Policy Example:
# Measure all executables
measure func=BPRM_CHECK mask=MAY_EXEC

# Appraise signed kernel modules
appraise func=MODULE_CHECK appraise_type=imasig

# Don't measure /tmp
dont_measure fsmagic=0x01021994
```

## TERAS Decision I-06

**FOR TERAS:**
1. Use fs-verity for TERAS binaries
2. Implement IMA appraisal for installations
3. Document file permission requirements
4. No setuid in TERAS components

### Architecture Decision ID: `TERAS-ARCH-I06-FILESYSTEM-001`

---

# I-07: Network Security in OS

## 1. Network Stack Security

### 1.1 Packet Filtering Architecture

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Linux Network Stack Security                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  NETFILTER/IPTABLES (Legacy):                                       â”‚
â”‚                                                                     â”‚
â”‚  Packet Flow:                                                       â”‚
â”‚  Network â”€â”€â–º PREROUTING â”€â”€â–º Routing â”€â”€â–º FORWARD â”€â”€â–º POSTROUTING    â”‚
â”‚       In         â”‚           â”‚            â”‚            â”‚            â”‚
â”‚                  â”‚           â–¼            â”‚            â–¼            â”‚
â”‚                  â”‚         INPUT          â”‚        Out Network      â”‚
â”‚                  â”‚           â”‚            â”‚                         â”‚
â”‚                  â”‚           â–¼            â”‚                         â”‚
â”‚                  â”‚      Local Process     â”‚                         â”‚
â”‚                  â”‚           â”‚            â”‚                         â”‚
â”‚                  â”‚           â–¼            â”‚                         â”‚
â”‚                  â””â”€â”€â”€â”€â”€â”€â”€ OUTPUT â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                         â”‚
â”‚                                                                     â”‚
â”‚  Tables:                                                            â”‚
â”‚  â”œâ”€â”€ filter: Packet filtering (default)                            â”‚
â”‚  â”œâ”€â”€ nat: Network address translation                              â”‚
â”‚  â”œâ”€â”€ mangle: Packet modification                                   â”‚
â”‚  â”œâ”€â”€ raw: Connection tracking exemptions                           â”‚
â”‚  â””â”€â”€ security: SELinux marking                                     â”‚
â”‚                                                                     â”‚
â”‚  NFTABLES (Modern):                                                 â”‚
â”‚  â”œâ”€â”€ Replaces iptables, ip6tables, arptables, ebtables            â”‚
â”‚  â”œâ”€â”€ Single unified framework                                      â”‚
â”‚  â”œâ”€â”€ Better performance (bytecode)                                 â”‚
â”‚  â””â”€â”€ More flexible syntax                                          â”‚
â”‚                                                                     â”‚
â”‚  BPF/XDP (Programmable):                                            â”‚
â”‚  â”œâ”€â”€ eBPF: In-kernel virtual machine                               â”‚
â”‚  â”œâ”€â”€ XDP: Process at driver level (fastest)                        â”‚
â”‚  â”œâ”€â”€ TC: Traffic control integration                               â”‚
â”‚  â””â”€â”€ Socket: Per-socket filtering                                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 eBPF for Network Security

```c
// XDP Program Example (packet filtering)

#include <linux/bpf.h>
#include <linux/if_ether.h>
#include <linux/ip.h>
#include <linux/tcp.h>

SEC("xdp")
int xdp_firewall(struct xdp_md *ctx) {
    void *data = (void *)(long)ctx->data;
    void *data_end = (void *)(long)ctx->data_end;
    
    struct ethhdr *eth = data;
    if ((void *)(eth + 1) > data_end)
        return XDP_PASS;
    
    if (eth->h_proto != htons(ETH_P_IP))
        return XDP_PASS;
    
    struct iphdr *ip = (void *)(eth + 1);
    if ((void *)(ip + 1) > data_end)
        return XDP_PASS;
    
    // Block specific IP
    if (ip->saddr == htonl(0x0a000001)) // 10.0.0.1
        return XDP_DROP;
    
    // Block port 22 (SSH) from outside
    if (ip->protocol == IPPROTO_TCP) {
        struct tcphdr *tcp = (void *)ip + (ip->ihl * 4);
        if ((void *)(tcp + 1) > data_end)
            return XDP_PASS;
        
        if (tcp->dest == htons(22))
            return XDP_DROP;
    }
    
    return XDP_PASS;
}

char _license[] SEC("license") = "GPL";
```

## 2. Socket Security

### 2.1 Socket Options

```c
// Secure Socket Configuration

int sockfd = socket(AF_INET, SOCK_STREAM, 0);

// Bind to specific interface
setsockopt(sockfd, SOL_SOCKET, SO_BINDTODEVICE, "eth0", 4);

// Set receive timeout (DoS protection)
struct timeval tv = {.tv_sec = 30, .tv_usec = 0};
setsockopt(sockfd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

// Disable Nagle (for some protocols)
int flag = 1;
setsockopt(sockfd, IPPROTO_TCP, TCP_NODELAY, &flag, sizeof(flag));

// Mark socket for SELinux/iptables
int mark = 0x1234;
setsockopt(sockfd, SOL_SOCKET, SO_MARK, &mark, sizeof(mark));

// Peer credentials (Unix sockets)
struct ucred cred;
socklen_t len = sizeof(cred);
getsockopt(sockfd, SOL_SOCKET, SO_PEERCRED, &cred, &len);
// cred.pid, cred.uid, cred.gid
```

## TERAS Decision I-07

**FOR TERAS:**
1. Use nftables/eBPF for network filtering
2. Provide eBPF programs for GAPURA integration
3. Document network security requirements
4. SO_PEERCRED for local IPC authentication

### Architecture Decision ID: `TERAS-ARCH-I07-NETWORK-001`

---

# I-08: Cryptographic Services in OS

## 1. Kernel Crypto API

### 1.1 Linux Crypto Framework

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Linux Kernel Crypto API                           â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Algorithm Types:                                                   â”‚
â”‚  â”œâ”€â”€ Cipher (skcipher): AES, ChaCha20                              â”‚
â”‚  â”œâ”€â”€ AEAD: AES-GCM, ChaCha20-Poly1305                              â”‚
â”‚  â”œâ”€â”€ Hash (shash): SHA-256, SHA-3, BLAKE2                          â”‚
â”‚  â”œâ”€â”€ HMAC: HMAC-SHA256                                             â”‚
â”‚  â”œâ”€â”€ Asymmetric: RSA, ECDSA (limited)                              â”‚
â”‚  â””â”€â”€ RNG: DRBG, jitterentropy                                      â”‚
â”‚                                                                     â”‚
â”‚  Hardware Acceleration:                                             â”‚
â”‚  â”œâ”€â”€ AES-NI: Intel AES instructions                                â”‚
â”‚  â”œâ”€â”€ SHA-NI: Intel SHA instructions                                â”‚
â”‚  â”œâ”€â”€ ARMv8 Crypto: ARM crypto extensions                           â”‚
â”‚  â””â”€â”€ TPM: Hardware RNG, key operations                             â”‚
â”‚                                                                     â”‚
â”‚  User-Space Access:                                                 â”‚
â”‚  â”œâ”€â”€ AF_ALG socket interface                                       â”‚
â”‚  â””â”€â”€ /dev/crypto (older)                                           â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 AF_ALG Interface

```c
// Using kernel crypto via AF_ALG

#include <linux/if_alg.h>
#include <sys/socket.h>

// AES-GCM encryption using kernel crypto
void kernel_aes_gcm_encrypt(void) {
    int tfmfd, opfd;
    struct sockaddr_alg sa = {
        .salg_family = AF_ALG,
        .salg_type = "aead",
        .salg_name = "gcm(aes)"
    };
    
    // Create algorithm socket
    tfmfd = socket(AF_ALG, SOCK_SEQPACKET, 0);
    bind(tfmfd, (struct sockaddr *)&sa, sizeof(sa));
    
    // Set key
    unsigned char key[16] = {...};
    setsockopt(tfmfd, SOL_ALG, ALG_SET_KEY, key, sizeof(key));
    
    // Set authentication tag length
    setsockopt(tfmfd, SOL_ALG, ALG_SET_AEAD_AUTHSIZE, NULL, 16);
    
    // Get operation socket
    opfd = accept(tfmfd, NULL, 0);
    
    // Prepare message
    struct msghdr msg = {0};
    struct cmsghdr *cmsg;
    struct af_alg_iv *iv;
    unsigned char cbuf[CMSG_SPACE(4) + CMSG_SPACE(20)];
    
    msg.msg_control = cbuf;
    msg.msg_controllen = sizeof(cbuf);
    
    // Set operation (encrypt)
    cmsg = CMSG_FIRSTHDR(&msg);
    cmsg->cmsg_level = SOL_ALG;
    cmsg->cmsg_type = ALG_SET_OP;
    cmsg->cmsg_len = CMSG_LEN(4);
    *(__u32 *)CMSG_DATA(cmsg) = ALG_OP_ENCRYPT;
    
    // Set IV
    cmsg = CMSG_NXTHDR(&msg, cmsg);
    cmsg->cmsg_level = SOL_ALG;
    cmsg->cmsg_type = ALG_SET_IV;
    cmsg->cmsg_len = CMSG_LEN(20);
    iv = (void *)CMSG_DATA(cmsg);
    iv->ivlen = 12;
    memcpy(iv->iv, nonce, 12);
    
    // Send plaintext, receive ciphertext
    struct iovec iov = {.iov_base = plaintext, .iov_len = len};
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    
    sendmsg(opfd, &msg, 0);
    read(opfd, ciphertext, len + 16);  // +16 for tag
    
    close(opfd);
    close(tfmfd);
}
```

## 2. Key Management

### 2.1 Linux Keyring

```
Linux Kernel Keyring:

Key Types:
â”œâ”€â”€ user: Generic user data
â”œâ”€â”€ logon: Non-readable credentials
â”œâ”€â”€ keyring: Container for other keys
â”œâ”€â”€ asymmetric: RSA/ECC keys
â”œâ”€â”€ encrypted: Keys encrypted by master key
â””â”€â”€ trusted: TPM-sealed keys

Keyrings:
â”œâ”€â”€ @u: User keyring
â”œâ”€â”€ @us: User session keyring
â”œâ”€â”€ @s: Session keyring
â”œâ”€â”€ @p: Process keyring
â”œâ”€â”€ @t: Thread keyring
â””â”€â”€ @g: Group keyring

Operations:
# Add key
keyctl add user mykey "secret" @u

# Read key
keyctl read [key_id]

# Set permissions
keyctl setperm [key_id] 0x3f3f0000

# Link to keyring
keyctl link [key_id] @s

# Request key from userspace
keyctl request2 user mykey "info" @s

Kernel Integration:
â”œâ”€â”€ fs-crypt: File encryption keys
â”œâ”€â”€ dm-crypt: Disk encryption keys
â”œâ”€â”€ TLS sockets: TLS keys
â””â”€â”€ IMA: Appraisal keys
```

## TERAS Decision I-08

**FOR TERAS:**
1. Use kernel crypto where possible (hardware accel)
2. Leverage keyring for ephemeral keys
3. TPM-sealed keys for long-term storage
4. Document kernel module requirements

### Architecture Decision ID: `TERAS-ARCH-I08-CRYPTO-001`

---

# I-09: Virtualization Security

## 1. Hypervisor Security Models

### 1.1 Type 1 vs Type 2 Hypervisors

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Hypervisor Types                                  â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  TYPE 1 (Bare Metal):                                               â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  VM 1        VM 2        VM 3                               â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”    â”Œâ”€â”€â”€â”€â”€â”    â”Œâ”€â”€â”€â”€â”€â”                             â”‚   â”‚
â”‚  â”‚  â”‚Guestâ”‚    â”‚Guestâ”‚    â”‚Guestâ”‚                             â”‚   â”‚
â”‚  â”‚  â”‚ OS  â”‚    â”‚ OS  â”‚    â”‚ OS  â”‚                             â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”˜    â””â”€â”€â”€â”€â”€â”˜    â””â”€â”€â”€â”€â”€â”˜                             â”‚   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤   â”‚
â”‚  â”‚              Hypervisor (Xen, VMware ESXi, KVM)             â”‚   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤   â”‚
â”‚  â”‚                       Hardware                               â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚  TCB: Hypervisor only (smaller)                                    â”‚
â”‚                                                                     â”‚
â”‚  TYPE 2 (Hosted):                                                   â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  VM 1        VM 2        Host Apps                          â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”    â”Œâ”€â”€â”€â”€â”€â”    â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”                         â”‚   â”‚
â”‚  â”‚  â”‚Guestâ”‚    â”‚Guestâ”‚    â”‚         â”‚                         â”‚   â”‚
â”‚  â”‚  â”‚ OS  â”‚    â”‚ OS  â”‚    â”‚         â”‚                         â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”˜    â””â”€â”€â”€â”€â”€â”˜    â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                         â”‚   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤   â”‚
â”‚  â”‚         Hypervisor (VirtualBox, VMware Workstation)         â”‚   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤   â”‚
â”‚  â”‚                       Host OS                                â”‚   â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤   â”‚
â”‚  â”‚                       Hardware                               â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚  TCB: Hypervisor + Host OS (larger)                                â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 VM Escape Vulnerabilities

```
VM Escape Attack Vectors:

Hypervisor Vulnerabilities:
â”œâ”€â”€ CVE-2017-5715 (Spectre): Cross-VM speculation attacks
â”œâ”€â”€ CVE-2020-3992 (VMware): OpenSLP heap overflow
â”œâ”€â”€ VENOM (CVE-2015-3456): QEMU floppy driver escape
â””â”€â”€ Cloudburst (2009): VMware display driver escape

Attack Surface:
â”œâ”€â”€ Virtual device emulation (largest)
â”œâ”€â”€ Hypercall interface
â”œâ”€â”€ Shared memory (ballooning)
â”œâ”€â”€ Pass-through devices (IOMMU bypass)
â””â”€â”€ Nested virtualization

Mitigations:
â”œâ”€â”€ Minimize virtual devices
â”œâ”€â”€ Use virtio (paravirtualized)
â”œâ”€â”€ Enable IOMMU/VT-d
â”œâ”€â”€ Memory encryption (SEV, TDX)
â”œâ”€â”€ VM introspection
â””â”€â”€ Hypervisor hardening
```

## 2. Container vs VM Security

### 2.1 Isolation Comparison

```
Isolation Levels:

                    Container          VM               seL4 Partition
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Kernel              Shared             Separate         Verified
Isolation boundary  Process/Namespace  Hardware-assisted Proved secure
Attack surface      Large (host kernel) Medium (hypervisor) Minimal
Escape difficulty   Medium             Hard             Very hard (formal)
Performance         Near-native        5-20% overhead   Minimal
Boot time           <1 second          Seconds-minutes  Milliseconds
Memory overhead     Megabytes          100+ MB          Kilobytes

Recommendation for TERAS:
â”œâ”€â”€ Containers: Development, testing, less sensitive
â”œâ”€â”€ VMs: Production, multi-tenant, sensitive data
â””â”€â”€ seL4: Highest assurance, air-gapped, critical
```

## TERAS Decision I-09

**FOR TERAS:**
1. VM isolation for multi-tenant deployments
2. Confidential computing (SEV/TDX) where available
3. Minimal device exposure to VMs
4. Consider seL4 partitions for highest assurance

### Architecture Decision ID: `TERAS-ARCH-I09-VIRTUALIZATION-001`

---

# I-10: TERAS OS Integration Architecture

## 1. TERAS Deployment Models

### 1.1 Multi-Layer Security

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    TERAS OS Integration Architecture                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  DEPLOYMENT MODEL 1: Containerized (Standard)                       â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”        â”‚   â”‚
â”‚  â”‚  â”‚ MENARA  â”‚  â”‚ GAPURA  â”‚  â”‚  ZIRAH  â”‚  â”‚ BENTENG â”‚        â”‚   â”‚
â”‚  â”‚  â”‚Containerâ”‚  â”‚Containerâ”‚  â”‚Containerâ”‚  â”‚Containerâ”‚        â”‚   â”‚
â”‚  â”‚  â”‚ Seccomp â”‚  â”‚ Seccomp â”‚  â”‚ Seccomp â”‚  â”‚ Seccomp â”‚        â”‚   â”‚
â”‚  â”‚  â”‚ AppArmorâ”‚  â”‚ AppArmorâ”‚  â”‚ AppArmorâ”‚  â”‚ AppArmorâ”‚        â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜        â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚         Container Runtime (containerd/runc)         â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚         Host OS (Linux with SELinux)                â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  DEPLOYMENT MODEL 2: VM-Isolated (High Security)                    â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”          â”‚   â”‚
â”‚  â”‚  â”‚   VM 1      â”‚  â”‚   VM 2      â”‚  â”‚   VM 3      â”‚          â”‚   â”‚
â”‚  â”‚  â”‚ TERAS Core  â”‚  â”‚   GAPURA    â”‚  â”‚   SANDI     â”‚          â”‚   â”‚
â”‚  â”‚  â”‚ SEV-enabled â”‚  â”‚ SEV-enabled â”‚  â”‚ SEV-enabled â”‚          â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜          â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚         Hypervisor (KVM + SEV/TDX)                  â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  DEPLOYMENT MODEL 3: seL4 Partitioned (Critical)                    â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”          â”‚   â”‚
â”‚  â”‚  â”‚   SANDI     â”‚  â”‚   TERAS     â”‚  â”‚   Linux     â”‚          â”‚   â”‚
â”‚  â”‚  â”‚   Signing   â”‚  â”‚   Core      â”‚  â”‚   (limited) â”‚          â”‚   â”‚
â”‚  â”‚  â”‚             â”‚  â”‚             â”‚  â”‚             â”‚          â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜          â”‚   â”‚
â”‚  â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”    â”‚   â”‚
â”‚  â”‚  â”‚              seL4 Microkernel (Verified)            â”‚    â”‚   â”‚
â”‚  â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜    â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Security Requirements Matrix

```
TERAS Product OS Security Requirements:

Product    â”‚ Isolation    â”‚ MAC        â”‚ Crypto      â”‚ Attestation
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
MENARA     â”‚ App sandbox  â”‚ SELinux    â”‚ TEE         â”‚ SafetyNet
GAPURA     â”‚ Container    â”‚ AppArmor   â”‚ Kernel      â”‚ IMA/TPM
ZIRAH      â”‚ Container    â”‚ SELinux    â”‚ Kernel      â”‚ IMA/TPM
BENTENG    â”‚ VM/Container â”‚ SELinux    â”‚ HSM/TEE     â”‚ TPM/TEE
SANDI      â”‚ VM/seL4      â”‚ Mandatory  â”‚ HSM         â”‚ TPM+HSM
```

## 2. OS Hardening Guidelines

### 2.1 TERAS Host OS Configuration

```bash
#!/bin/bash
# TERAS Host OS Hardening

# 1. Kernel Security Parameters
cat >> /etc/sysctl.d/99-teras.conf << EOF
# Network hardening
net.ipv4.conf.all.rp_filter = 1
net.ipv4.conf.all.accept_redirects = 0
net.ipv4.conf.all.send_redirects = 0
net.ipv4.icmp_echo_ignore_broadcasts = 1
net.ipv4.tcp_syncookies = 1

# Memory protection
kernel.randomize_va_space = 2
kernel.kptr_restrict = 2
kernel.dmesg_restrict = 1
kernel.perf_event_paranoid = 3

# User namespace (disable if not needed)
kernel.unprivileged_userns_clone = 0

# BPF hardening
kernel.unprivileged_bpf_disabled = 1
net.core.bpf_jit_harden = 2
EOF

# 2. Enable SELinux
setenforce 1
sed -i 's/SELINUX=permissive/SELINUX=enforcing/' /etc/selinux/config

# 3. File system hardening
mount -o remount,nosuid,nodev,noexec /tmp
mount -o remount,nosuid,nodev,noexec /var/tmp

# 4. Disable unnecessary services
systemctl disable --now avahi-daemon
systemctl disable --now cups
systemctl disable --now rpcbind

# 5. Install TERAS seccomp profiles
cp /opt/teras/seccomp/* /etc/seccomp/

# 6. Configure audit
cat >> /etc/audit/rules.d/teras.rules << EOF
-w /opt/teras -p wa -k teras_files
-w /etc/teras -p wa -k teras_config
-a always,exit -F arch=b64 -S execve -k process_execution
EOF
```

## TERAS Decision I-10

**FOR TERAS:**
1. Multiple deployment models based on security level
2. Standardized hardening for all deployments
3. OS-agnostic design where possible
4. Document specific OS requirements per product

### Architecture Decision ID: `TERAS-ARCH-I10-INTEGRATE-001`

---

# Domain I Summary: Operating Systems Security

| Session | Topic | Decision ID |
|---------|-------|-------------|
| I-01 | TCB Fundamentals | TERAS-ARCH-I01-TCB-001 |
| I-02 | seL4 | TERAS-ARCH-I02-SEL4-001 |
| I-03 | Capabilities | TERAS-ARCH-I03-CAPABILITY-001 |
| I-04 | Linux Security | TERAS-ARCH-I04-LINUX-001 |
| I-05 | Process Isolation | TERAS-ARCH-I05-ISOLATION-001 |
| I-06 | File System | TERAS-ARCH-I06-FILESYSTEM-001 |
| I-07 | Network | TERAS-ARCH-I07-NETWORK-001 |
| I-08 | Crypto Services | TERAS-ARCH-I08-CRYPTO-001 |
| I-09 | Virtualization | TERAS-ARCH-I09-VIRTUALIZATION-001 |
| I-10 | Integration | TERAS-ARCH-I10-INTEGRATE-001 |

## Key Principles

1. **Minimal TCB**: Smaller trusted base = smaller attack surface
2. **Defense in Depth**: Multiple isolation layers
3. **Formal Verification**: seL4 for highest assurance
4. **Leverage Hardware**: Use TEE, TPM, memory encryption
5. **OS Hardening**: Mandatory for all deployments

## DOMAIN I: COMPLETE

---

*Research Track Output â€” Domain I: Operating Systems Security*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
