# TERAS-LANG Research Domain U: Runtime Guardian & Verified Micro-Hypervisor

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-U-RUNTIME-GUARDIAN |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | U: Runtime Guardian |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# U-01: The "Physics is Hostile" Problem & The Guardian

## 1. The Existential Threat

**Context:**
Formal proofs (Track A) assume the hardware state transitions according to the rules.
**The Reality:**
Physics happens. Cosmic rays flip bits in RAM. Power supply noise glitches the CPU clock. Rowhammer induces faults.
**The Consequence:**
A single bit flip can turn `is_admin = false` to `is_admin = true`. A perfect software proof cannot stop a transistor from failing.

**The TERAS Reality:**
We assume the hardware is flaky, the environment is radioactive, and Murphy is an active adversary.

## 2. The Solution: The Runtime Guardian (TERAS-SENTINEL)

We cannot prevent bit flips. We **CAN** detect them and halt execution before damage occurs.

We introduce **TERAS-SENTINEL**: A formally verified, ultra-minimal micro-hypervisor (or "Reference Monitor") that runs *underneath* the TERAS application.

### 2.1 The Concept
The Sentinel does not run the app. It **monitors** the app.
It enforces a "Safety Enclosure" defined by:
1.  **Control Flow Integrity (CFI):** The instruction pointer (IP) must follow the valid Control Flow Graph (CFG).
2.  **Memory Integrity:** Critical data structures are checksummed or stored redundantly.
3.  **Capability Enforcement:** Access to I/O is gated by the Sentinel, not the OS.

### 2.2 The Implementation: SeL4 + Custom Monitor
We leverage **seL4** (the world's first verified microkernel) as the base, but we strip it down further.

**The "Redundant Execution" Mode:**
For maximum security (NSA-level), TERAS supports **N-Modular Redundancy (NMR)** in software.
*   The compiler generates **Two** versions of the code (Variant A and Variant B).
*   They run in parallel (on different cores or interleaved).
*   The Sentinel checks `State(A) == State(B)` at every synchronization point.
*   **Result:** A random bit flip affects only one version. The mismatch is detected. The system halts.

### 2.3 The "Panic Button"
The Sentinel is connected to a "Physical Panic Button" (e.g., a specific GPIO pin that cuts power or zeros keys).
If **ANY** invariant is violated (e.g., a Rowhammer pattern is detected, or a CFI violation occurs), the Sentinel triggers the **Panic Protocol**:
1.  **Zeroize Keys:** Wipe encryption keys from registers/RAM immediately.
2.  **Halt:** Stop execution.
3.  **Audit:** Log the violation to Write-Once Media (if available).

## 3. Architecture of Domain U

### 3.1 The Reference Monitor
*   **Formal Spec:** Written in Isabelle/HOL (like seL4).
*   **Property:** "It is impossible for the Application to bypass the Monitor."
*   **Interface:** The Application sees a "Paravirtualized" interface. It cannot touch raw hardware.

### 3.2 The Watchdog
*   A hardware timer interrupts the CPU periodically (non-maskable).
*   The Watchdog verifies the integrity of the Monitor itself ("Who watches the watchmen?").
*   If the Monitor is corrupted, the Watchdog resets the system.

## 4. Implementation Strategy (Infinite Timeline)

1.  **Step 1: Formalize the Sentinel.**
    *   Define the minimal set of invariants (CFG, Memory Bounds).

2.  **Step 2: Integration with seL4.**
    *   Prove that our Sentinel code running on seL4 maintains its properties.

3.  **Step 3: Compiler Support (Domain R).**
    *   The compiler must emit the "Map" (CFG, Data Layout) that the Sentinel uses for verification.
    *   This Map is signed by the build system.

## 5. Obsolescence of Threats

*   **Rowhammer / Fault Injection:** OBSOLETE. The Redundant Execution checks catch state divergence.
*   **Kernel Exploits:** OBSOLETE. The Application doesn't run in Ring 0. It runs in a sandbox monitored by a verified Hypervisor.
*   **Cosmic Rays:** OBSOLETE. NMR handles probabilistic errors.

---

**"Trust nothing. Not even the silicon. Not even the atoms."**
