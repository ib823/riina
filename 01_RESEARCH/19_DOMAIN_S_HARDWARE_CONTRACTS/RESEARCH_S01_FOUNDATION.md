# TERAS-LANG Research Domain S: Hardware Contracts & Microarchitectural Formalism

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-S-HARDWARE-CONTRACTS |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | S: Hardware Contracts |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# S-01: The "Lying Hardware" Problem & ISA v2.0

## 1. The Existential Threat

**Context:**
Traditional formal methods verify software against an **Instruction Set Architecture (ISA)** model (e.g., "This instruction adds two numbers").
**The Reality:**
Modern CPUs do *not* execute the ISA. They transcode it into micro-ops, execute them speculatively, out-of-order, optimizing based on branch history and cache state.
**The Consequence:**
Software that is "proven correct" on the ISA model is **INSECURE** on the actual machine because the ISA model abstracts away the very mechanisms (time, power, speculation) that leak secrets (Spectre, Meltdown).

**The TERAS Reality:**
We cannot verify code against a lie.

## 2. The Solution: Hardware-Software Contracts (ISA v2.0)

We define a new interface between hardware and software. We do not treat the CPU as a functional unit; we treat it as a **State Machine with Side Channels**.

### 2.1 The Augmented ISA Model

We extend the standard ISA tuple (S, δ) (State, Transition Function) to (S, μ, δ, λ):

1.  S (Architectural State): Registers, RAM.
2.  μ (Microarchitectural State): Cache lines, Branch Predictor History Table (PHT), Branch Target Buffer (BTB), Store Buffers, Line Fill Buffers.
3.  δ (Transition): Updates both S and μ.
    *   Example: `LOAD [addr]` updates a Register (in S) AND updates the Cache Set (in μ).
4.  λ (Leakage Model): A function defining what information is "observable" to an attacker from the state transition.
    *   `Leakage = Time(Op) + Power(Op) + EM(Op)`

### 2.2 The "Obsolescence" Standard

A program P is secure if and only if for any two initial secret states s1, s2:
$$
\text{Trace}(\lambda(P, s_1)) = \text{Trace}(\lambda(P, s_2))
$$
i.e., The physical leakage trace is indistinguishable regardless of the secret data.

This is **Constant-Time by Definition**, not by accident.

## 3. Architecture of Domain S

### 3.1 Formal ISA Specifications
We will not trust English manuals. We require formal semantics (in Sail, L3, or Coq) for:
*   **RISC-V (RV64GC)**: The primary target, due to its openness.
*   **OpenPOWER**: Secondary target.
*   **x86-64 / ARM**: "Legacy" targets. We will model them conservatively (assuming worst-case speculation).

### 3.2 The Speculation Contract
We formally model **Speculative Execution**.
*   The model allows the "CPU" to "guess" a branch direction.
*   It executes instructions in a "Shadow State".
*   If the guess is wrong, the Shadow State is discarded (Rollback).
*   **CRITICAL:** The "Microarchitectural State" (μ) is **NOT** rolled back. (This is how Spectre works).
*   **Verification Goal:** Prove that `Secret` data never influences the address of a memory access or a branch target *even in the Shadow State*.

### 3.3 Hardware-Software Co-Design
We will design **TERAS-V**, a customized RISC-V profile that disables dangerous optimizations or exposes them to software control:
*   **Instruction:** `SCUB` (Speculative Barrier).
*   **Instruction:** `CACHE_PIN` (Lock cache lines).
*   **Feature:** Deterministic ALU timing (no data-dependent latency).

## 4. Implementation Strategy (Infinite Timeline)

1.  **Step 1: Import Formal ISAs.**
    *   Import the official RISC-V Formal model into our Coq proofs.

2.  **Step 2: Model the Adversary.**
    *   Define the "Microarchitectural Adversary" who can see cache hits/misses and branch mispredictions.

3.  **Step 3: Update Compilers/Validators.**
    *   Update Domain R (Translation Validator) to use this Augmented ISA model. The validator must reject code that is functionally correct but side-channel vulnerable.

## 5. Obsolescence of Threats

*   **Spectre/Meltdown:** OBSOLETE. The formal model includes speculation. Code that leaks via speculation will fail verification.
*   **Timing Attacks:** OBSOLETE. The model exposes timing. Variable-time instructions on secrets will be rejected.
*   **Rowhammer:** OBSOLETE. We model the physical row adjacency (Contract: "Accessing Row X impacts Row X+1"). We formally prove access patterns do not trigger the threshold.

---

**"Physics is not an abstraction. It is a constraint."**
