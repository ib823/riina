# TERAS-LANG Research Domain R: Certified Compilation & Translation Validation

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-R-CERTIFIED-COMPILATION |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | R: Certified Compilation |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST | 
| Status | FOUNDATIONAL DEFINITION |

---

# R-01: The "Trusting Trust" Problem & The TERAS Solution

## 1. The Existential Threat

**Context:**
In 1984, Ken Thompson demonstrated ("Reflections on Trusting Trust") that a compiler can be backdoored to insert trojans into the binaries it produces, *including future versions of itself*. No amount of source code auditing can detect this, as the backdoor exists only in the binary of the compiler.

**The TERAS Reality:**
We have formally verified the source code (Track A). We have a paranoid prototype (Track B).
**HOWEVER:** We currently trust `rustc`, `LLVM`, and the host linker.
**Verdict:** UNACCEPTABLE. If the compiler is compromised, our proofs are hallucinations.

**The Goal:**
Eliminate the compiler from the Trusted Computing Base (TCB). Assume the compiler is actively malicious, run by an adversary, and trying to insert backdoors.

## 2. The Solution: TERAS-TV (Translation Validation)

We will **NOT** simply write a "Certified Compiler" (like CompCert). While excellent, verified compilers lag behind optimization research and are difficult to maintain.

Instead, we implement **Translation Validation**.

### 2.1 The Concept

1.  **Untrusted Compiler:** We use an optimizing compiler (like LLVM/Rust) to generate binary code. We treat this component as a "black box oracle" that might be lying.
2.  **The Validator:** A separate, formally verified tool that takes:
    *   Input: The Source Code (or high-level IR).
    *   Input: The Generated Binary (machine code).
    *   Output: A **Formal Proof** that `Semantics(Binary) ⊆ Semantics(Source)`.
3.  **The Guarantee:** If the compiler inserts a backdoor, the semantics will diverge. The Validator will fail to construct the proof. The build will abort.

### 2.2 The Mathematical Standard

For every function $f$ in the source program $P$, and its compiled version $f'$ in binary $B$:

$$
\forall \text{state } \sigma, \text{Exec}(f, \sigma) \Downarrow v \implies \text{Exec}(f', \text{Refine}(\sigma)) \Downarrow \text{Refine}(v) 
$$

Where:
*   `Refine` maps abstract source values to concrete machine states (registers/memory).
*   The property must hold **observational equivalence**, preserving all side-effects and security properties (Constant-Time).

## 3. Architecture of TERAS-TV

The validator operates in three phases, effectively "de-compiling" the binary into a form comparable with the source.

### Phase 1: Canonicalization (The "Lifter")
*   **Input:** x86-64 / ARM64 / RISC-V Binary.
*   **Action:** Lift machine instructions into a formal Intermediate Representation (TERAS-FIR).
*   **Zero Trust Requirement:** The "Lifter" semantics must be proven against the formal hardware model (Domain S).
*   **Challenge:** Disassembly is undecidable in the general case.
*   **Solution:** We require the compiler to emit "hints" (debug info, stack maps). We do *not* trust the hints, but we use them to guide the lifting. If the hints are wrong, the proof fails.

### Phase 2: Symbolic execution & SMT Solving
*   **Input:** Source IR (MIR) and Binary IR (TERAS-FIR).
*   **Action:**
    1.  Break both into Control Flow Graphs (CFG).
    2.  For each basic block, generate path verification conditions.
    3.  Use an SMT solver (Z3/CVC5) to prove equivalence of dataflow.
*   **Paranoia:** What if the SMT solver is buggy?
    *   **Solution:** The SMT solver must output a "Proof Certificate" (e.g., in Alethe or LFSC format).
    *   **Checker:** A tiny, formally verified kernel (in Coq) checks the SMT proof certificate.

### Phase 3: Global Property Verification
*   **Input:** Verified basic blocks.
*   **Action:** Prove preservation of global properties:
    *   Stack safety (no stack smashing).
    *   Memory safety (no buffer overflows).
    *   **Information Flow:** Prove that `Erasure(Secret)` in Source implies `Non-Observability(Secret)` in Binary.

## 4. Implementation Strategy (Infinite Timeline)

We do not care how long this takes. It must be correct.

1.  **Step 1: The Formal ISA (Domain S dependency).**
    *   We cannot validate translation if we don't strictly define what `ADD RAX, RBX` does.
    *   We will adopt/create formal semantics for RISC-V (Sail/L3) and verify them against silicon.

2.  **Step 2: The Coq Validator.**
    *   The core validation logic is written in Coq/Lean.
    *   It extracts to a verified executable.

3.  **Step 3: The Integration.**
    *   The build system (`teras-build`) will refuse to sign a binary unless a valid `.proof` file is generated for it.

## 5. Obsolescence of Threats

*   **Compiler Backdoors:** OBSOLETE. A backdoor changes semantics. The validator catches it.
*   **Optimization Bugs:** OBSOLETE. If an optimization changes the program logic (e.g., deleting a "useless" security check), the validator catches it.
*   **Linker Attacks:** OBSOLETE. We validate the *final linked binary*, not just object files.

## 6. Immediate Actions

1.  **Define TERAS-FIR:** A Formal Intermediate Representation that serves as the bridge between high-level TERAS and low-level Assembly.
2.  **Survey Existing Art:** Analyze `Verified LLVM` (Vellvm), `Cogito`, and `Sewer`. We will take their best ideas and enforce them with stricter constraints.

---

**"If you cannot prove it matches, it does not exist."**