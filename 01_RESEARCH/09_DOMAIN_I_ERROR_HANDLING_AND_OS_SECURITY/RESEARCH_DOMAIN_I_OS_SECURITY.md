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
┌─────────────────────────────────────────────────────────────────────┐
│                    Trusted Computing Base                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Definition:                                                        │
│  The TCB is the totality of protection mechanisms within a          │
│  computer system responsible for enforcing security policy.         │
│                                                                     │
│  TCB Components:                                                    │
│  ├── Hardware: CPU, MMU, security coprocessors                     │
│  ├── Firmware: BIOS/UEFI, microcode                                │
│  ├── OS Kernel: Process isolation, access control                  │
│  ├── Security services: Authentication, audit                      │
│  └── Trusted applications: Security-critical code                  │
│                                                                     │
│  TCB Principles:                                                    │
│  ├── Minimization: Smaller TCB = smaller attack surface            │
│  ├── Verification: TCB should be formally verified                 │
│  ├── Isolation: TCB protected from non-TCB components              │
│  └── Completeness: All security-relevant ops go through TCB        │
│                                                                     │
│  Reference Monitor:                                                 │
│  ├── Mediates all access to objects                                │
│  ├── Properties:                                                   │
│  │   ├── Complete mediation: All accesses checked                  │
│  │   ├── Tamperproof: Cannot be modified by untrusted code        │
│  │   └── Verifiable: Small enough to analyze                       │
│  └── Implementation: Security kernel                               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 TCB Size Comparison

```
System                      │ TCB Size (LOC)  │ Verified
────────────────────────────┼─────────────────┼──────────
seL4 microkernel            │ ~10,000         │ Yes (full)
MINIX 3                     │ ~6,000 (kernel) │ Partial
L4 family                   │ ~10-15,000      │ Some variants
Windows kernel              │ ~50,000,000+    │ No
Linux kernel                │ ~30,000,000+    │ No
macOS kernel (XNU)          │ ~5,000,000+     │ No

TCB Size Impact:
├── Every 1000 LOC: ~15 bugs on average
├── Larger TCB: More potential vulnerabilities
├── Verification cost: Grows with size
└── Practical limit for full verification: ~50,000 LOC
```

## 2. Security Kernel Designs

### 2.1 Monolithic vs Microkernel

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Kernel Architecture Comparison                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  MONOLITHIC KERNEL (Linux, Windows):                                │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      User Space                              │   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │   │
│  │  │  App 1  │  │  App 2  │  │  App 3  │  │  App N  │        │   │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘        │   │
│  ├─────────────────────────────────────────────────────────────┤   │
│  │                      Kernel Space (TCB)                      │   │
│  │  ┌─────────────────────────────────────────────────────┐    │   │
│  │  │ Process  │ Memory │ Filesystem │ Network │ Drivers  │    │   │
│  │  │ Mgmt     │ Mgmt   │            │ Stack   │          │    │   │
│  │  └─────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│  TCB: Everything in kernel space                                   │
│                                                                     │
│  MICROKERNEL (seL4, MINIX 3):                                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      User Space                              │   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │   │
│  │  │  App 1  │  │  App 2  │  │ Network │  │Filesystem│        │   │
│  │  └─────────┘  └─────────┘  │ Server  │  │ Server  │        │   │
│  │                            └─────────┘  └─────────┘        │   │
│  │  ┌─────────┐  ┌─────────┐                                   │   │
│  │  │ Device  │  │ Memory  │                                   │   │
│  │  │ Drivers │  │ Server  │                                   │   │
│  │  └─────────┘  └─────────┘                                   │   │
│  ├─────────────────────────────────────────────────────────────┤   │
│  │           Kernel Space (TCB - Minimal)                       │   │
│  │  ┌───────────────────────────────────────────────────────┐  │   │
│  │  │  IPC  │  Scheduling  │  Memory (basic)  │  Capability │  │   │
│  │  └───────────────────────────────────────────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────┘   │
│  TCB: Only microkernel (much smaller)                              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
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
┌─────────────────────────────────────────────────────────────────────┐
│                    seL4 Microkernel Architecture                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Verification Status:                                               │
│  ├── Functional correctness: Proved                                │
│  ├── Implementation matches spec: Proved                           │
│  ├── Binary matches C code: Proved (some platforms)                │
│  ├── Security properties: Proved                                   │
│  │   ├── Confidentiality (no information leakage)                 │
│  │   ├── Integrity (no unauthorized modification)                 │
│  │   └── Availability (no denial of service by user code)         │
│  └── Timing channels: NOT addressed (ongoing work)                 │
│                                                                     │
│  Kernel Services (minimal):                                         │
│  ├── Threads: Execution contexts                                   │
│  ├── Address spaces: Virtual memory                                │
│  ├── IPC: Synchronous message passing                              │
│  ├── Notifications: Asynchronous signals                           │
│  ├── Capabilities: Access control                                  │
│  └── Interrupts: Delivered as notifications                        │
│                                                                     │
│  Everything Else: User-level servers                                │
│  ├── Device drivers                                                │
│  ├── File systems                                                  │
│  ├── Network stack                                                 │
│  ├── Memory management (beyond basic)                              │
│  └── OS personality (Linux, POSIX, etc.)                           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Capability System

```
seL4 Capability Model:

Capability Structure:
├── Object reference: Pointer to kernel object
├── Access rights: Permissions bitmap
└── Badge: Unforgeable identifier

Capability Operations:
├── Invoke: Use capability to perform operation
├── Copy: Duplicate capability (possibly with reduced rights)
├── Grant: Transfer capability to another thread
├── Mint: Create derived capability with badge
└── Revoke: Recursively revoke all derived capabilities

Example Objects and Capabilities:
┌────────────────────┬────────────────────────────────────────────┐
│ Object Type        │ Capability Operations                      │
├────────────────────┼────────────────────────────────────────────┤
│ TCB (Thread)       │ Suspend, Resume, Configure, ReadRegisters  │
│ CNode (Cap table)  │ Copy, Mint, Delete, Revoke, Rotate         │
│ Untyped            │ Retype (create new objects)                │
│ Endpoint           │ Send, Receive, Grant                       │
│ Notification       │ Signal, Wait                               │
│ Page               │ Map, Unmap, GetAddress                     │
│ PageTable          │ Map, Unmap                                 │
│ IRQHandler         │ Acknowledge, SetNotification               │
└────────────────────┴────────────────────────────────────────────┘
```

### 1.3 seL4 Proof Structure

```
Verification Layers:

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  Abstract Specification (Isabelle/HOL)                              │
│  ├── High-level description of kernel behavior                     │
│  ├── Defines what the kernel should do                             │
│  └── ~5,700 lines of Isabelle                                      │
│                              ↓ Refinement proof                     │
│  Executable Specification (Haskell)                                 │
│  ├── Algorithmic description                                       │
│  ├── Testable prototype                                            │
│  └── ~10,000 lines of Haskell                                      │
│                              ↓ Refinement proof                     │
│  C Implementation                                                   │
│  ├── Actual implementation                                         │
│  ├── Manually written, guided by spec                              │
│  └── ~10,000 lines of C                                            │
│                              ↓ Translation validation               │
│  Binary (ARM, x86, RISC-V)                                          │
│  ├── Compiled from C                                               │
│  └── Binary verification (some platforms)                          │
│                                                                     │
│  Proof Effort: ~200,000 lines of Isabelle proof                    │
│  Person-years: ~20 for initial proof                               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
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
├── DARPA HACMS: Unhackable military helicopter
├── Genode OS Framework: General-purpose seL4 port
├── Trustworthy Systems: Defense applications
├── HENSOLDT Cyber: Secure gateway products
└── Ghost Locomotion: Autonomous vehicle systems

TERAS Relevance:
├── Highest assurance deployments
├── Defense/government customers
├── Critical infrastructure
└── Air-gapped secure systems
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
┌─────────────────────────────────────────────────────────────────────┐
│                    Capability-Based Security                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Capability Definition:                                             │
│  An unforgeable token that grants specific access rights to a       │
│  specific object.                                                   │
│                                                                     │
│  Capability = (Object Reference, Access Rights)                     │
│                                                                     │
│  Key Properties:                                                    │
│  ├── Unforgeable: Cannot create without proper authority           │
│  ├── Transferable: Can be passed to other processes                │
│  ├── Specific: Identifies exact object and permissions             │
│  └── Principle of Least Privilege: Natural fit                     │
│                                                                     │
│  Capability vs ACL:                                                 │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  ACL (Access Control List):                                  │   │
│  │  Object → [(Subject, Rights), ...]                          │   │
│  │  "Who can access this object?"                              │   │
│  │  Check: Is subject in object's ACL?                         │   │
│  │                                                              │   │
│  │  Capability List:                                            │   │
│  │  Subject → [(Object, Rights), ...]                          │   │
│  │  "What can this subject access?"                            │   │
│  │  Check: Does subject have capability for object?            │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Capability Advantages:                                             │
│  ├── Delegation: Easy to grant subset of access                    │
│  ├── Revocation: More complex but possible                         │
│  ├── Confused deputy prevention: Natural defense                   │
│  └── Least privilege: Fine-grained permissions                     │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Confused Deputy Problem

```
Confused Deputy Attack:

Scenario:
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  User ──request──► Compiler ──write──► /billing/user_file          │
│                      │                                              │
│                      │ Compiler has write access to billing dir     │
│                      │ for legitimate logging purposes              │
│                      │                                              │
│  Attacker ─────────► Compiler ──write──► /billing/important_file   │
│           (malicious output path)                                   │
│                                                                     │
│  Problem: Compiler uses its own authority, not user's              │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘

Capability Solution:
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  User ──(capability to user_file)──► Compiler                      │
│                                         │                           │
│                                         │ Can only write where     │
│                                         │ user has capability      │
│                                         ▼                           │
│                                      /user/output.o                 │
│                                                                     │
│  Attacker cannot forge capability to /billing/important_file       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. Capability Operating Systems

### 2.1 CHERI (Capability Hardware Enhanced RISC Instructions)

```
CHERI Architecture:

Hardware Capabilities:
├── 128-bit or 256-bit capability registers
├── Bounds: Base address and length
├── Permissions: Read, write, execute, etc.
├── Sealed: Cannot be modified
└── Compartment ID: For cross-domain calls

Capability Format (128-bit):
┌────────────────────────────────────────────────────────────────────┐
│ Tag │ Permissions │ Object Type │ Bounds │ Offset │ Address        │
│ 1b  │    15b      │     4b      │  ~40b  │  ~20b  │    ~48b        │
└────────────────────────────────────────────────────────────────────┘

Memory Safety:
├── All pointers are capabilities
├── Bounds checked on every access
├── Cannot forge pointers
├── Spatial safety: No out-of-bounds access
└── Temporal safety: With revocation

CHERI Implementations:
├── CHERI-MIPS: Research processor
├── CHERI-RISC-V: Morello prototype
├── Arm Morello: Production board (2022)
└── CHERIoT: For embedded/IoT
```

### 2.2 Capsicum (FreeBSD)

```
Capsicum Capability Mode:

Enter Capability Mode:
cap_enter()  /* Process can no longer access global namespace */

After cap_enter():
├── Cannot open files by path
├── Cannot create sockets by address
├── Must use pre-opened descriptors
└── Capabilities = file descriptors + rights

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
┌─────────────────────────────────────────────────────────────────────┐
│                    Linux Security Modules                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  LSM Hook Points:                                                   │
│  ├── Task hooks: fork, exec, setuid                                │
│  ├── File hooks: open, read, write, mmap                           │
│  ├── Inode hooks: create, link, unlink, permission                 │
│  ├── Socket hooks: create, bind, connect, accept                   │
│  ├── Network hooks: packet filtering, labeling                     │
│  └── IPC hooks: shm, msg, sem operations                           │
│                                                                     │
│  LSM Implementations:                                               │
│  ├── SELinux: Mandatory access control                             │
│  ├── AppArmor: Path-based MAC                                      │
│  ├── Smack: Simplified MAC                                         │
│  ├── TOMOYO: Learning-based MAC                                    │
│  ├── Yama: ptrace restrictions                                     │
│  └── LoadPin: Module loading restrictions                          │
│                                                                     │
│  LSM Stacking (since 5.1):                                          │
│  ├── Multiple minor LSMs can coexist                               │
│  ├── One major LSM (SELinux/AppArmor/Smack)                        │
│  └── Chain of hooks evaluated                                      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
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
┌─────────────────────────────────────────────────────────────────────┐
│                    Linux Namespaces                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Namespace Types:                                                   │
│  ├── Mount (mnt): File system mount points                         │
│  ├── UTS: Hostname and domain name                                 │
│  ├── IPC: System V IPC, POSIX message queues                       │
│  ├── Network (net): Network devices, ports, routing                │
│  ├── PID: Process IDs                                              │
│  ├── User: User and group IDs                                      │
│  ├── Cgroup: Cgroup root directory                                 │
│  └── Time: System time (since 5.6)                                 │
│                                                                     │
│  Operations:                                                        │
│  ├── clone(CLONE_NEWNS | CLONE_NEWPID | ...)                       │
│  ├── unshare(CLONE_NEWNET)                                         │
│  └── setns(fd, CLONE_NEWUSER)                                      │
│                                                                     │
│  Container Isolation:                                               │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Container = Namespaces + Cgroups + Seccomp + Capabilities  │   │
│  │                                                              │   │
│  │  ┌─────────────────────────────────────────────────────┐    │   │
│  │  │                    Container                         │    │   │
│  │  │  ├── Own filesystem (mnt ns)                        │    │   │
│  │  │  ├── Own network (net ns)                           │    │   │
│  │  │  ├── Own PIDs (pid ns)                              │    │   │
│  │  │  ├── Resource limits (cgroups)                      │    │   │
│  │  │  ├── Syscall filter (seccomp)                       │    │   │
│  │  │  └── Limited capabilities                           │    │   │
│  │  └─────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 User Namespaces Security

```
User Namespace Isolation:

Mapping:
├── Container UID 0 → Host UID 100000
├── Container UID 1 → Host UID 100001
├── ...
└── Unprivileged in host, privileged in container

Security Implications:
├── Root in container ≠ root on host
├── CAP_SYS_ADMIN in container = limited
├── Can create other namespaces
└── Enables rootless containers

Risks:
├── Kernel attack surface expanded
├── New code paths for unprivileged users
├── CVEs in user namespace handling
└── Often disabled in production

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
┌─────────────────────────────────────────────────────────────────────┐
│                    Memory Isolation Mechanisms                       │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  VIRTUAL MEMORY:                                                    │
│  ├── Each process has own address space                            │
│  ├── Page tables translate virtual → physical                      │
│  ├── Hardware enforced (MMU)                                       │
│  └── Kernel manages mappings                                       │
│                                                                     │
│  PAGE PERMISSIONS:                                                  │
│  ├── Read (R): Can read memory                                     │
│  ├── Write (W): Can write memory                                   │
│  ├── Execute (X): Can execute code                                 │
│  ├── User/Supervisor: Ring 3 vs Ring 0                             │
│  └── NX bit: No-execute for data pages                             │
│                                                                     │
│  W^X (Write XOR Execute):                                           │
│  ├── Page cannot be both writable and executable                   │
│  ├── Prevents code injection                                       │
│  ├── Enforced by modern OSes                                       │
│  └── JIT must use mprotect() carefully                             │
│                                                                     │
│  ASLR (Address Space Layout Randomization):                         │
│  ├── Stack: Random offset                                          │
│  ├── Heap: Random base                                             │
│  ├── Libraries: Random load addresses                              │
│  ├── Executable: PIE (Position Independent Executable)             │
│  └── Entropy: ~28-30 bits on 64-bit                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Kernel Address Space Isolation

```
KPTI (Kernel Page Table Isolation):

Purpose: Mitigate Meltdown attack

Before KPTI:
┌─────────────────────────────────────────┐
│         User Page Tables                │
│  ┌───────────────────────────────────┐  │
│  │  User Space (accessible)          │  │
│  │  Kernel Space (mapped, but        │  │
│  │               supervisor-only)    │  │
│  └───────────────────────────────────┘  │
└─────────────────────────────────────────┘
Meltdown: Speculative execution could read kernel

After KPTI:
┌─────────────────────────────────────────┐
│         User Page Tables                │
│  ┌───────────────────────────────────┐  │
│  │  User Space (accessible)          │  │
│  │  Minimal kernel (syscall entry)   │  │
│  └───────────────────────────────────┘  │
└─────────────────────────────────────────┘
┌─────────────────────────────────────────┐
│         Kernel Page Tables              │
│  ┌───────────────────────────────────┐  │
│  │  Full kernel (only during syscall)│  │
│  │  User space                       │  │
│  └───────────────────────────────────┘  │
└─────────────────────────────────────────┘
Kernel not mapped in user mode → no Meltdown
```

## 2. Sandboxing Technologies

### 2.1 Chrome Sandbox Architecture

```
Chrome Multi-Process Architecture:

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  ┌───────────────────────────────────────────────────────────────┐ │
│  │                     Browser Process                            │ │
│  │  - UI, network I/O, file system                               │ │
│  │  - Full privileges                                            │ │
│  │  - Broker for sandboxed processes                             │ │
│  └───────────────────────────────────────────────────────────────┘ │
│                              │                                      │
│           ┌──────────────────┼──────────────────┐                  │
│           │                  │                  │                   │
│           ▼                  ▼                  ▼                   │
│  ┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐       │
│  │  Renderer 1     │ │  Renderer 2     │ │  GPU Process    │       │
│  │  (sandboxed)    │ │  (sandboxed)    │ │  (sandboxed)    │       │
│  │  - Seccomp-BPF  │ │  - Seccomp-BPF  │ │  - Seccomp-BPF  │       │
│  │  - Namespaces   │ │  - Namespaces   │ │  - Limited caps │       │
│  │  - No network   │ │  - No network   │ │                 │       │
│  │  - No filesystem│ │  - No filesystem│ │                 │       │
│  └─────────────────┘ └─────────────────┘ └─────────────────┘       │
│                                                                     │
│  Sandbox Layers:                                                    │
│  ├── Layer 1: seccomp-BPF (syscall filtering)                      │
│  ├── Layer 2: Namespaces (PID, network, user)                      │
│  ├── Layer 3: Capabilities (dropped)                               │
│  └── Layer 4: chroot/pivot_root (filesystem)                       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 gVisor and Firecracker

```
gVisor (Google):
├── User-space kernel
├── Intercepts syscalls via ptrace or KVM
├── Implements Linux syscalls in Go
├── Reduced kernel attack surface
├── Container runtime: runsc
└── Performance overhead: Significant for syscall-heavy workloads

Firecracker (AWS):
├── MicroVM monitor
├── Minimal virtual machine
├── KVM-based
├── ~125ms boot time
├── <5 MB memory overhead
├── Used by AWS Lambda, Fargate
└── Security: VM isolation > container isolation
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
┌─────────────────────────────────────────────────────────────────────┐
│                    File System Permission Models                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  UNIX PERMISSIONS (Traditional):                                    │
│  -rwxr-xr-x  1  owner  group  size  date  filename                 │
│   │││ │││ │││                                                       │
│   │││ │││ └┴┴── Others: r-x (read, execute)                        │
│   │││ └┴┴────── Group: r-x (read, execute)                         │
│   └┴┴────────── Owner: rwx (read, write, execute)                  │
│                                                                     │
│  Special Bits:                                                      │
│  ├── setuid (4xxx): Run as file owner                              │
│  ├── setgid (2xxx): Run as file group                              │
│  └── sticky (1xxx): Delete only by owner (directories)             │
│                                                                     │
│  POSIX ACLs (Extended):                                             │
│  # getfacl file                                                     │
│  user::rwx                                                          │
│  user:alice:r-x                                                     │
│  group::r-x                                                         │
│  group:developers:rwx                                               │
│  mask::rwx                                                          │
│  other::---                                                         │
│                                                                     │
│  Extended Attributes:                                               │
│  ├── security.*: SELinux labels                                    │
│  ├── system.*: ACLs, capabilities                                  │
│  ├── trusted.*: Requires CAP_SYS_ADMIN                             │
│  └── user.*: User-defined                                          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 File System Capabilities

```
Linux Capabilities on Files:

# Set capability on executable
setcap cap_net_bind_service=+ep /usr/bin/myserver

Capability Sets:
├── Permitted (p): Can be acquired
├── Inheritable (i): Preserved across exec
├── Effective (e): Currently active
└── Ambient: Inherited by non-setuid programs

Common File Capabilities:
├── cap_net_bind_service: Bind ports <1024
├── cap_net_raw: Raw sockets
├── cap_sys_admin: Various admin functions
├── cap_dac_override: Bypass file permissions
└── cap_setuid/cap_setgid: Change UID/GID

Security Considerations:
├── Capabilities are NOT namespaced (mostly)
├── Can grant partial root-like abilities
├── More granular than setuid
└── Still requires careful management
```

## 2. Integrity Protection

### 2.1 dm-verity and fs-verity

```
dm-verity (Block-level):

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                     Merkle Tree                              │   │
│  │                        Root Hash                             │   │
│  │                       /        \                             │   │
│  │                    Hash         Hash                         │   │
│  │                   /    \       /    \                        │   │
│  │                 H0     H1    H2     H3                       │   │
│  │                 │      │      │      │                       │   │
│  │  Data Blocks: [B0]   [B1]   [B2]   [B3]                     │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Read Operation:                                                    │
│  1. Read data block                                                │
│  2. Read hash tree path to root                                    │
│  3. Verify hash chain                                              │
│  4. If mismatch → return I/O error                                 │
│                                                                     │
│  Use Cases:                                                         │
│  ├── Android Verified Boot                                         │
│  ├── Chrome OS rootfs                                              │
│  └── Read-only system partitions                                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘

fs-verity (File-level):
├── Per-file Merkle tree
├── Enabled on individual files
├── Works with any filesystem supporting it (ext4, f2fs, btrfs)
├── File becomes read-only after enabling
└── Used by APK v4 signature
```

### 2.2 IMA/EVM (Integrity Measurement Architecture)

```
IMA (Integrity Measurement Architecture):

Measurement:
├── Record hash of files before use
├── Store in TPM PCR (extend)
├── Create IMA measurement list
└── Enable remote attestation

Appraisal:
├── Compare hash against known-good
├── Block execution if mismatch
├── Signed policy for expected hashes
└── Boot-time enforcement

EVM (Extended Verification Module):
├── Protect extended attributes
├── HMAC or digital signature
├── Prevents offline tampering
└── Requires IMA

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
┌─────────────────────────────────────────────────────────────────────┐
│                    Linux Network Stack Security                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  NETFILTER/IPTABLES (Legacy):                                       │
│                                                                     │
│  Packet Flow:                                                       │
│  Network ──► PREROUTING ──► Routing ──► FORWARD ──► POSTROUTING    │
│       In         │           │            │            │            │
│                  │           ▼            │            ▼            │
│                  │         INPUT          │        Out Network      │
│                  │           │            │                         │
│                  │           ▼            │                         │
│                  │      Local Process     │                         │
│                  │           │            │                         │
│                  │           ▼            │                         │
│                  └─────── OUTPUT ─────────┘                         │
│                                                                     │
│  Tables:                                                            │
│  ├── filter: Packet filtering (default)                            │
│  ├── nat: Network address translation                              │
│  ├── mangle: Packet modification                                   │
│  ├── raw: Connection tracking exemptions                           │
│  └── security: SELinux marking                                     │
│                                                                     │
│  NFTABLES (Modern):                                                 │
│  ├── Replaces iptables, ip6tables, arptables, ebtables            │
│  ├── Single unified framework                                      │
│  ├── Better performance (bytecode)                                 │
│  └── More flexible syntax                                          │
│                                                                     │
│  BPF/XDP (Programmable):                                            │
│  ├── eBPF: In-kernel virtual machine                               │
│  ├── XDP: Process at driver level (fastest)                        │
│  ├── TC: Traffic control integration                               │
│  └── Socket: Per-socket filtering                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
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
┌─────────────────────────────────────────────────────────────────────┐
│                    Linux Kernel Crypto API                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Algorithm Types:                                                   │
│  ├── Cipher (skcipher): AES, ChaCha20                              │
│  ├── AEAD: AES-GCM, ChaCha20-Poly1305                              │
│  ├── Hash (shash): SHA-256, SHA-3, BLAKE2                          │
│  ├── HMAC: HMAC-SHA256                                             │
│  ├── Asymmetric: RSA, ECDSA (limited)                              │
│  └── RNG: DRBG, jitterentropy                                      │
│                                                                     │
│  Hardware Acceleration:                                             │
│  ├── AES-NI: Intel AES instructions                                │
│  ├── SHA-NI: Intel SHA instructions                                │
│  ├── ARMv8 Crypto: ARM crypto extensions                           │
│  └── TPM: Hardware RNG, key operations                             │
│                                                                     │
│  User-Space Access:                                                 │
│  ├── AF_ALG socket interface                                       │
│  └── /dev/crypto (older)                                           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
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
├── user: Generic user data
├── logon: Non-readable credentials
├── keyring: Container for other keys
├── asymmetric: RSA/ECC keys
├── encrypted: Keys encrypted by master key
└── trusted: TPM-sealed keys

Keyrings:
├── @u: User keyring
├── @us: User session keyring
├── @s: Session keyring
├── @p: Process keyring
├── @t: Thread keyring
└── @g: Group keyring

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
├── fs-crypt: File encryption keys
├── dm-crypt: Disk encryption keys
├── TLS sockets: TLS keys
└── IMA: Appraisal keys
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
┌─────────────────────────────────────────────────────────────────────┐
│                    Hypervisor Types                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  TYPE 1 (Bare Metal):                                               │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  VM 1        VM 2        VM 3                               │   │
│  │  ┌─────┐    ┌─────┐    ┌─────┐                             │   │
│  │  │Guest│    │Guest│    │Guest│                             │   │
│  │  │ OS  │    │ OS  │    │ OS  │                             │   │
│  │  └─────┘    └─────┘    └─────┘                             │   │
│  ├─────────────────────────────────────────────────────────────┤   │
│  │              Hypervisor (Xen, VMware ESXi, KVM)             │   │
│  ├─────────────────────────────────────────────────────────────┤   │
│  │                       Hardware                               │   │
│  └─────────────────────────────────────────────────────────────┘   │
│  TCB: Hypervisor only (smaller)                                    │
│                                                                     │
│  TYPE 2 (Hosted):                                                   │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  VM 1        VM 2        Host Apps                          │   │
│  │  ┌─────┐    ┌─────┐    ┌─────────┐                         │   │
│  │  │Guest│    │Guest│    │         │                         │   │
│  │  │ OS  │    │ OS  │    │         │                         │   │
│  │  └─────┘    └─────┘    └─────────┘                         │   │
│  ├─────────────────────────────────────────────────────────────┤   │
│  │         Hypervisor (VirtualBox, VMware Workstation)         │   │
│  ├─────────────────────────────────────────────────────────────┤   │
│  │                       Host OS                                │   │
│  ├─────────────────────────────────────────────────────────────┤   │
│  │                       Hardware                               │   │
│  └─────────────────────────────────────────────────────────────┘   │
│  TCB: Hypervisor + Host OS (larger)                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 VM Escape Vulnerabilities

```
VM Escape Attack Vectors:

Hypervisor Vulnerabilities:
├── CVE-2017-5715 (Spectre): Cross-VM speculation attacks
├── CVE-2020-3992 (VMware): OpenSLP heap overflow
├── VENOM (CVE-2015-3456): QEMU floppy driver escape
└── Cloudburst (2009): VMware display driver escape

Attack Surface:
├── Virtual device emulation (largest)
├── Hypercall interface
├── Shared memory (ballooning)
├── Pass-through devices (IOMMU bypass)
└── Nested virtualization

Mitigations:
├── Minimize virtual devices
├── Use virtio (paravirtualized)
├── Enable IOMMU/VT-d
├── Memory encryption (SEV, TDX)
├── VM introspection
└── Hypervisor hardening
```

## 2. Container vs VM Security

### 2.1 Isolation Comparison

```
Isolation Levels:

                    Container          VM               seL4 Partition
────────────────────────────────────────────────────────────────────────
Kernel              Shared             Separate         Verified
Isolation boundary  Process/Namespace  Hardware-assisted Proved secure
Attack surface      Large (host kernel) Medium (hypervisor) Minimal
Escape difficulty   Medium             Hard             Very hard (formal)
Performance         Near-native        5-20% overhead   Minimal
Boot time           <1 second          Seconds-minutes  Milliseconds
Memory overhead     Megabytes          100+ MB          Kilobytes

Recommendation for TERAS:
├── Containers: Development, testing, less sensitive
├── VMs: Production, multi-tenant, sensitive data
└── seL4: Highest assurance, air-gapped, critical
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
┌─────────────────────────────────────────────────────────────────────┐
│                    TERAS OS Integration Architecture                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  DEPLOYMENT MODEL 1: Containerized (Standard)                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐        │   │
│  │  │ MENARA  │  │ GAPURA  │  │  ZIRAH  │  │ BENTENG │        │   │
│  │  │Container│  │Container│  │Container│  │Container│        │   │
│  │  │ Seccomp │  │ Seccomp │  │ Seccomp │  │ Seccomp │        │   │
│  │  │ AppArmor│  │ AppArmor│  │ AppArmor│  │ AppArmor│        │   │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘        │   │
│  │  ┌─────────────────────────────────────────────────────┐    │   │
│  │  │         Container Runtime (containerd/runc)         │    │   │
│  │  └─────────────────────────────────────────────────────┘    │   │
│  │  ┌─────────────────────────────────────────────────────┐    │   │
│  │  │         Host OS (Linux with SELinux)                │    │   │
│  │  └─────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  DEPLOYMENT MODEL 2: VM-Isolated (High Security)                    │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐          │   │
│  │  │   VM 1      │  │   VM 2      │  │   VM 3      │          │   │
│  │  │ TERAS Core  │  │   GAPURA    │  │   SANDI     │          │   │
│  │  │ SEV-enabled │  │ SEV-enabled │  │ SEV-enabled │          │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘          │   │
│  │  ┌─────────────────────────────────────────────────────┐    │   │
│  │  │         Hypervisor (KVM + SEV/TDX)                  │    │   │
│  │  └─────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  DEPLOYMENT MODEL 3: seL4 Partitioned (Critical)                    │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐          │   │
│  │  │   SANDI     │  │   TERAS     │  │   Linux     │          │   │
│  │  │   Signing   │  │   Core      │  │   (limited) │          │   │
│  │  │             │  │             │  │             │          │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘          │   │
│  │  ┌─────────────────────────────────────────────────────┐    │   │
│  │  │              seL4 Microkernel (Verified)            │    │   │
│  │  └─────────────────────────────────────────────────────┘    │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Security Requirements Matrix

```
TERAS Product OS Security Requirements:

Product    │ Isolation    │ MAC        │ Crypto      │ Attestation
───────────┼──────────────┼────────────┼─────────────┼─────────────
MENARA     │ App sandbox  │ SELinux    │ TEE         │ SafetyNet
GAPURA     │ Container    │ AppArmor   │ Kernel      │ IMA/TPM
ZIRAH      │ Container    │ SELinux    │ Kernel      │ IMA/TPM
BENTENG    │ VM/Container │ SELinux    │ HSM/TEE     │ TPM/TEE
SANDI      │ VM/seL4      │ Mandatory  │ HSM         │ TPM+HSM
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

*Research Track Output — Domain I: Operating Systems Security*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
