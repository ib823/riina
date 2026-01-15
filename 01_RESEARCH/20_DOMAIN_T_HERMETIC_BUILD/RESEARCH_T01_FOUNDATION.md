# TERAS-LANG Research Domain T: Hermetic Build & Recursive Bootstrap

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-T-HERMETIC-BUILD |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | T: Hermetic Build |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# T-01: The "Chicken and Egg" Problem & The TERAS Bootstrap

## 1. The Existential Threat

**Context:**
To compile a Rust compiler, you need a Rust compiler. Where did that come from? Another one.
Trace it back, and you eventually reach a binary downloaded from the internet.
**The Threat:**
"Reflections on Trusting Trust" (again). If the original seed binary was compromised 10 years ago, every subsequent version carries the infection.
**Supply Chain Attacks:** SolarWinds, XZ Utils. These attacks happen because we trust opaque binaries and build servers.

**The TERAS Reality:**
We trust **NO BINARY**. Not `gcc`, not `bash`, not `make`.
We assume the entire internet is hostile.

## 2. The Solution: Recursive Binary Bootstrap (Stage 0)

We will implement a **Hermetic Bootstrap** chain that starts from human-auditable machine code.

### 2.1 The "Big Bang" (Stage 0)
*   **The Seed:** A single ~512-byte hex file (`hex0`).
*   **Auditability:** Small enough that a single human can read the hex codes and verify they correspond to a valid x86/RISC-V instruction stream that implements a tiny hex loader.
*   **The Verification:** We provide the printed source of this hex file. The user can hand-assemble it on paper to verify it matches.

### 2.2 The Evolution Chain
1.  **Stage 0 (`hex0`)**: A minimal hex loader.
2.  **Stage 1 (`hex1`)**: A slightly more capable loader/assembler (self-hosting).
3.  **Stage 2 (`M2-Planet`)**: A subset of C implemented in assembly.
4.  **Stage 3 (`MesCC`)**: A C99 compiler written in M2-Planet C.
5.  **Stage 4 (`TinyCC` / `GCC 4.7`)**: A standard C compiler built with MesCC.
6.  **Stage 5 (`Rust mrustc`)**: A C++ implementation of Rust (not `rustc`) that can compile Rust 1.54.
7.  **Stage 6 (`Rust 1.54` -> `1.80`)**: We bootstrap up the Rust version chain.
8.  **Stage 7 (`TERAS Compiler`)**: Finally, we build our compiler.

### 2.3 Hermeticity
*   **Network Access:** DISABLED. The build environment has no network interface.
*   **Filesystem:** READ-ONLY (except output). Only the whitelisted source tarballs are visible.
*   **Clock:** FIXED. The build time is set to `1970-01-01`.
*   **Randomness:** DETERMINISTIC. CSPRNGs are seeded with fixed constants for the build process.

## 3. Architecture of Domain T

### 3.1 Diverse Double-Compilation (DDC)
To be absolutely sure, we do not just build once.
1.  Build TERAS Compiler using the Bootstrap Chain (A).
2.  Build TERAS Compiler using a "tainted" commercial compiler (B).
3.  Use Compiler A to compile Compiler B's source again (A').
4.  **Comparison:** If `A` and `B` are functionally identical (via Domain R validation), we have high confidence.
5.  **Grand Challenge:** We aim for bit-for-bit reproducibility. `SHA256(A) == SHA256(B)`.

### 3.2 The "Source of Truth"
The repository contains **ONLY SOURCE CODE**.
Binary blobs (even images or fonts) are banned unless they can be deterministically generated from text-based source.

## 4. Implementation Strategy (Infinite Timeline)

1.  **Step 1: Adopt the "Live-Bootstrap" Project.**
    *   We will mirror and pin the `live-bootstrap` repository.
    *   We will audit the initial seeds.

2.  **Step 2: The Rust Chain.**
    *   Integrate `mrustc` (Mutabah's Rust Compiler) into the chain.
    *   Verify the path from C++ -> Rust.

3.  **Step 3: The TERAS Chain.**
    *   Ensure TERAS itself is bootstrappable. No circular dependencies in our own crates.

## 5. Obsolescence of Threats

*   **Compromised CI/CD:** OBSOLETE. Any user can reproduce the bit-exact binary from `hex0` on their laptop. If the CI binary differs, it is rejected.
*   **Vendor Backdoors:** OBSOLETE. We do not use vendor compilers.
*   **Supply Chain Injection:** OBSOLETE. We verify the hash of every single input source file against a public ledger.

---

**"From dust we come, to dust we return. In between, we verify every bit."**
