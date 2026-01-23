# RIINA RESEARCH-EXECUTION MAP

## Version 1.0.0 — Complete Mapping of 218 Research Tracks to Language Features

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  RESEARCH-EXECUTION MAP                                                                              ║
║                                                                                                      ║
║  Purpose: Map ALL 218 research tracks to RIINA language features                                    ║
║  Identify: Gaps between research scope and execution state                                          ║
║  Goal: Close the gap systematically                                                                 ║
║                                                                                                      ║
║  Classification: ULTRA KIASU | ZERO TRUST | INFINITE TIMELINE                                       ║
║  Date: 2026-01-19                                                                                    ║
║                                                                                                      ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# TABLE OF CONTENTS

1. [Executive Summary](#part-i-executive-summary)
2. [The Gap Analysis](#part-ii-the-gap-analysis)
3. [Core Domains (A-L) Mapping](#part-iii-core-domains-mapping)
4. [Zero-Trust Tracks (R-Z) Mapping](#part-iv-zero-trust-tracks-mapping)
5. [Extended Tracks Mapping](#part-v-extended-tracks-mapping)
6. [Gap Closure Strategy](#part-vi-gap-closure-strategy)
7. [Execution Roadmap](#part-vii-execution-roadmap)

---

# PART I: EXECUTIVE SUMMARY

## 1.1 The Numbers

| Category | Count | Execution Status |
|----------|-------|------------------|
| **Core Research Domains (A-L)** | 175 sessions | 🟡 Partially executed |
| **Zero-Trust Tracks (R-Z)** | 9 tracks | 📋 Defined only |
| **Greek Tracks (Σ, Π, etc.)** | 14 tracks | 📋 Defined only |
| **Extended Tracks (AA-AJ)** | 10 tracks | 📋 Defined only |
| **Networking (GA-HV)** | 28 tracks | 📋 Defined only |
| **UI/UX (HA-LJ)** | 50 tracks | 📋 Defined only |
| **Post-Axiom (MA-MJ)** | 10 tracks | 📋 Defined only |
| **Domain Extensions (ΣA-FJ)** | 85 tracks | 📋 Defined only |
| **TOTAL** | **218 tracks** | **~15% executed** |

## 1.2 The Gap Visualization

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║                              RESEARCH vs EXECUTION STATE                                             ║
║                                                                                                      ║
║  RESEARCH COVERAGE:                                                                                  ║
║  ████████████████████████████████████████████████████████████████████████████████████████ 218 tracks ║
║                                                                                                      ║
║  EXECUTION STATE:                                                                                    ║
║  █████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░ ~15%       ║
║                                                                                                      ║
║  GAP: ~85% (185 tracks not yet incorporated into proofs/implementation)                             ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART II: THE GAP ANALYSIS

## 2.1 What "Execution" Means

| Execution Level | Definition | Count |
|-----------------|------------|-------|
| **Level 5: Fully Proven** | Machine-verified in Coq + tests passing | ~10 tracks |
| **Level 4: Partially Proven** | Some theorems proven, axioms remain | ~15 tracks |
| **Level 3: Implemented** | Prototype code exists, no proofs | ~8 tracks |
| **Level 2: Specified** | Specification document exists | ~30 tracks |
| **Level 1: Research Only** | Research document exists | ~50 tracks |
| **Level 0: Defined Only** | Track defined, no research done | ~105 tracks |

## 2.2 Gap by Execution Level

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  EXECUTION LEVEL DISTRIBUTION                                                                        ║
║                                                                                                      ║
║  Level 5 (Fully Proven):      ██████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  ~10 tracks (5%)   ║
║  Level 4 (Partial Proofs):    ███████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  ~15 tracks (7%)   ║
║  Level 3 (Implemented):       ████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░   ~8 tracks (4%)   ║
║  Level 2 (Specified):         ██████████████████████████████░░░░░░░░░░░░░░░░░░░░  ~30 tracks (14%)  ║
║  Level 1 (Research Only):     ████████████████████████████████████████████████░░  ~50 tracks (23%)  ║
║  Level 0 (Defined Only):      ████████████████████████████████████████████████████ ~105 tracks (48%) ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART III: CORE DOMAINS MAPPING (A-L)

## 3.1 Domain A: Type Theory (20 Sessions)

| Session | Topic | RIINA Feature | Execution Level | Gap |
|---------|-------|---------------|-----------------|-----|
| A-01 | Martin-Löf Type Theory | Foundation | Level 4 | Axioms remain |
| A-02 | Calculus of Constructions | Type constructors | Level 4 | Axioms remain |
| A-03 | HoTT/Cubical | (Not incorporated) | Level 1 | Not planned |
| A-04 | Linear Logic | Linear<T> | Level 4 | LinearSoundness axioms |
| A-05 | Affine/Relevant | Affine<T> | Level 3 | No proofs yet |
| A-06 | Uniqueness Types | (Merged with Linear) | Level 3 | No proofs |
| A-07 | Session Types | Protocol types | Level 2 | Spec only |
| A-08 | Refinement Types | SMT predicates | Level 2 | Spec only |
| A-09 | Dependent Types | Dependent functions | Level 4 | Partial proofs |
| A-10 | Gradual Types | (Not incorporated) | Level 1 | Not planned |
| A-11 | Effect Types | Effect rows | Level 4 | EffectSoundness axioms |
| A-12 | Region Types | (Not incorporated) | Level 1 | Not planned |
| A-13 | Ownership Types | Ownership system | Level 4 | Preservation axioms |
| A-14 | Capability Types | Capability tokens | Level 2 | Spec only |
| A-15 | Intersection/Union | (Not incorporated) | Level 1 | Not planned |
| A-16 | Row Types | Effect rows | Level 4 | Partial proofs |
| A-17 | Higher-Kinded | HKT support | Level 3 | No proofs |
| A-18 | Type-Level Computation | Type families | Level 2 | Spec only |
| A-19 | Type Inference | Bidirectional TC | Level 3 | Implemented |
| A-20 | Soundness Proofs | All soundness | Level 4 | 18 axioms remain |

**Domain A Summary:** 20 sessions, ~10 at Level 4, ~5 at Level 3, ~5 at Level 1-2

## 3.2 Domain B: Effect Systems (10 Sessions)

| Session | Topic | RIINA Feature | Execution Level | Gap |
|---------|-------|---------------|-----------------|-----|
| B-01 | Algebraic Effects | perform/handle | Level 4 | EffectSoundness axioms |
| B-02 | Monadic Effects | (Alternative approach) | Level 1 | Research only |
| B-03 | Coeffects | (Not incorporated) | Level 1 | Not planned |
| B-04 | Effect Handlers | Handler semantics | Level 4 | Partial proofs |
| B-05 | Koka Deep Dive | Inspiration | Level 1 | Research only |
| B-06 | Frank/Effekt | Inspiration | Level 1 | Research only |
| B-07 | Row Polymorphism | Effect rows | Level 4 | Partial proofs |
| B-08 | Effect Inference | Effect inference | Level 3 | Implemented |
| B-09 | Effect Subtyping | Effect subsumption | Level 3 | Implemented |
| B-10 | Effects in Practice | Validation | Level 1 | Research only |

**Domain B Summary:** 10 sessions, ~4 at Level 4, ~2 at Level 3, ~4 at Level 1

## 3.3 Domain C: Information Flow Control (10 Sessions)

| Session | Topic | RIINA Feature | Execution Level | Gap |
|---------|-------|---------------|-----------------|-----|
| C-01 | Denning's Lattice | Security lattice | Level 4 | Partial proofs |
| C-02 | Decentralized Label | Secret<T, L> | Level 4 | Partial proofs |
| C-03 | Language-Based IFC | Compile-time IFC | Level 4 | NonInterference axioms |
| C-04 | Dynamic IFC | (Not incorporated) | Level 1 | Not planned |
| C-05 | Hybrid IFC | (Not incorporated) | Level 1 | Not planned |
| C-06 | IFC for Concurrency | (Future) | Level 0 | Not started |
| C-07 | IFC for Distribution | (Future) | Level 0 | Not started |
| C-08 | Non-Interference | TINI/TSNI | Level 4 | 5 axioms remain |
| C-09 | Declassification | dedah() | Level 4 | Partial proofs |
| C-10 | Robust Declassification | Policy enforcement | Level 2 | Spec only |

**Domain C Summary:** 10 sessions, ~6 at Level 4, ~1 at Level 2, ~3 at Level 0-1

## 3.4 Domain D: Hardware Security (15 Sessions)

| Session | Topic | RIINA Feature | Execution Level | Gap |
|---------|-------|---------------|-----------------|-----|
| D-01 | Intel SGX | Effect Gate inspiration | Level 1 | Research only |
| D-02 | AMD SEV | Effect Gate inspiration | Level 1 | Research only |
| D-03 | ARM TrustZone/CCA | Effect Gate inspiration | Level 1 | Research only |
| D-04 | Intel TDX | Effect Gate inspiration | Level 1 | Research only |
| D-05 | RISC-V Security | Effect Gate inspiration | Level 1 | Research only |
| D-06 | CHERI Capabilities | Capability types | Level 2 | Spec only |
| D-07 | Keystone/Sanctum | Effect Gate inspiration | Level 1 | Research only |
| D-08 | Apple Secure Enclave | Effect Gate inspiration | Level 1 | Research only |
| D-09 | Google Titan | Effect Gate inspiration | Level 1 | Research only |
| D-10 | TPM Analysis | Hardware attestation | Level 1 | Research only |
| D-11 | PUFs | (Future hardware) | Level 0 | Not started |
| D-12 | HSMs | riina-crypto | Level 3 | Implemented |
| D-13 | Memory Encryption | Transparent encryption | Level 1 | Research only |
| D-14 | Secure Boot | Bootstrap | Level 2 | Spec only |
| D-15 | Root of Trust | Trust architecture | Level 2 | Spec only |

**Domain D Summary:** 15 sessions, ~1 at Level 3, ~3 at Level 2, ~10 at Level 1, ~1 at Level 0

## 3.5 Domain E: Formal Verification (15 Sessions)

| Session | Topic | RIINA Feature | Execution Level | Gap |
|---------|-------|---------------|-----------------|-----|
| E-01 | Coq Deep Dive | Primary proof assistant | Level 5 | Fully utilized |
| E-02 | Isabelle/HOL | Tertiary prover | Level 0 | Not started |
| E-03 | Lean | Secondary prover | Level 0 | Not started |
| E-04 | Agda | (Not incorporated) | Level 1 | Research only |
| E-05 | F* | (Not incorporated) | Level 1 | Research only |
| E-06 | Dafny/Why3 | (Not incorporated) | Level 1 | Research only |
| E-07 | SPARK/Ada | riina-core | Level 3 | Implemented |
| E-08 | Rust Verification | Comparison | Level 1 | Research only |
| E-09 | TLA+/Alloy | (Not incorporated) | Level 1 | Research only |
| E-10 | SMT Solvers | Refinement types | Level 2 | Spec only |
| E-11 | Model Checkers | (Not incorporated) | Level 1 | Research only |
| E-12 | Symbolic Execution | (Future) | Level 0 | Not started |
| E-13 | CompCert/CakeML | Verified compilation | Level 1 | Research only |
| E-14 | Translation Validation | Compiler verification | Level 1 | Research only |
| E-15 | Verification-Aware | Compiler design | Level 2 | Spec only |

**Domain E Summary:** 15 sessions, ~1 at Level 5, ~1 at Level 3, ~3 at Level 2, ~7 at Level 1, ~3 at Level 0

## 3.6 Domain F: Cryptography (20 Sessions)

| Session | Topic | RIINA Feature | Execution Level | Gap |
|---------|-------|---------------|-----------------|-----|
| F-01 | ML-KEM/ML-DSA | riina-crypto | Level 5 | Implemented + tested |
| F-02 | Lattice Crypto | PQC foundation | Level 5 | Implemented |
| F-03 | Code-Based | (Not incorporated) | Level 1 | Research only |
| F-04 | Hash-Based Sigs | (Future) | Level 0 | Not started |
| F-05 | Post-SIDH | (Not incorporated) | Level 1 | Research only |
| F-06 | Multivariate | (Not incorporated) | Level 1 | Research only |
| F-07 | ZK Foundations | (Future) | Level 0 | Not started |
| F-08 | SNARKs | (Future) | Level 0 | Not started |
| F-09 | STARKs | (Future) | Level 0 | Not started |
| F-10 | Bulletproofs | (Future) | Level 0 | Not started |
| F-11 | Homomorphic | (Future) | Level 0 | Not started |
| F-12 | Functional Enc | (Not incorporated) | Level 1 | Research only |
| F-13 | ABE | (Not incorporated) | Level 1 | Research only |
| F-14 | Threshold Crypto | (Future) | Level 0 | Not started |
| F-15 | MPC | (Future) | Level 0 | Not started |
| F-16 | OT/PIR | (Future) | Level 0 | Not started |
| F-17 | Constant-Time | ConstantTime<T> | Level 4 | Partial proofs |
| F-18 | Side-Channel Resist | Implementation | Level 3 | Implemented |
| F-19 | Crypto Agility | Design pattern | Level 2 | Spec only |
| F-20 | PQC Migration | Strategy | Level 1 | Research only |

**Domain F Summary:** 20 sessions, ~2 at Level 5, ~2 at Level 3-4, ~2 at Level 2, ~5 at Level 1, ~9 at Level 0

## 3.7 Domain G: Side-Channel Attacks (15 Sessions)

| Session | Topic | RIINA Feature | Execution Level | Gap |
|---------|-------|---------------|-----------------|-----|
| G-01 | Timing Attacks | ConstantTime<T> | Level 4 | Partial proofs |
| G-02 | Cache Attacks | Constant-time | Level 3 | Mitigations |
| G-03 | Spectre | Speculative defense | Level 1 | Research only |
| G-04 | Meltdown | Speculative defense | Level 1 | Research only |
| G-05 | Microarch | Defense patterns | Level 1 | Research only |
| G-06 | Power Analysis | (Hardware scope) | Level 0 | Not started |
| G-07 | EM Analysis | (Hardware scope) | Level 0 | Not started |
| G-08 | Acoustic | (Not applicable) | Level 0 | N/A |
| G-09 | Thermal | (Not applicable) | Level 0 | N/A |
| G-10 | Fault Injection | (Hardware scope) | Level 0 | Not started |
| G-11 | Rowhammer | Memory safety | Level 1 | Research only |
| G-12 | Cold Boot | Memory zeroization | Level 3 | Implemented |
| G-13 | Network Timing | Protocol design | Level 1 | Research only |
| G-14 | Compression | CRIME/BREACH | Level 1 | Research only |
| G-15 | Defense Techniques | All defenses | Level 2 | Spec only |

**Domain G Summary:** 15 sessions, ~1 at Level 4, ~2 at Level 3, ~1 at Level 2, ~6 at Level 1, ~5 at Level 0

## 3.8 Domains H-L Summary

| Domain | Sessions | Level 5 | Level 4 | Level 3 | Level 2 | Level 1 | Level 0 |
|--------|----------|---------|---------|---------|---------|---------|---------|
| H: Policy Languages | 10 | 0 | 0 | 0 | 2 | 6 | 2 |
| I: Operating Systems | 10 | 0 | 0 | 0 | 1 | 7 | 2 |
| J: Compiler | 15 | 0 | 2 | 5 | 3 | 5 | 0 |
| K: Existing Systems | 15 | 0 | 0 | 0 | 0 | 15 | 0 |
| L: Attack Research | 20 | 0 | 0 | 0 | 0 | 20 | 0 |

---

# PART IV: ZERO-TRUST TRACKS (R-Z) MAPPING

## 4.1 Track Status

| Track | Name | Sessions | RIINA Feature | Execution Level |
|-------|------|----------|---------------|-----------------|
| R | Certified Compilation | 5 | Translation validation | Level 0 |
| S | Hardware Contracts | 5 | HW/SW contracts | Level 0 |
| T | Hermetic Build | 5 | Bootstrap | Level 2 |
| U | Runtime Guardian | 5 | Micro-hypervisor | Level 0 |
| V | Termination | 5 | Sized types | Level 1 |
| W | Memory Safety | 5 | Separation logic | Level 1 |
| X | Concurrency | 5 | Session types | Level 2 |
| Y | Verified Stdlib | 5 | riina-* crates | Level 3 |
| Z | Declassification | 5 | Policy enforcement | Level 2 |

**Zero-Trust Summary:** 45 sessions total, ~1 at Level 3, ~3 at Level 2, ~2 at Level 1, ~3 at Level 0

---

# PART V: EXTENDED TRACKS MAPPING

## 5.1 Extended Track Summary

| Track Series | Count | Primary Gap |
|--------------|-------|-------------|
| Greek (Σ, Π, Δ, etc.) | 14 | All Level 0-1 (storage, performance, distribution) |
| AA-AJ | 10 | All Level 0 (extended security) |
| GA-HV (Networking) | 28 | All Level 0 (439 protocols enumerated, not implemented) |
| HA-LJ (UI/UX) | 50 | All Level 0 (627 technologies enumerated, not implemented) |
| MA-MJ (Post-Axiom) | 10 | All Level 0 (waiting for axiom elimination) |
| ΣA-FJ (Extensions) | 85 | All Level 0 (domain extensions) |

## 5.2 The Reality

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  EXTENDED TRACKS: THE BRUTAL TRUTH                                                                   ║
║                                                                                                      ║
║  These 197 extended tracks are RESEARCH ASPIRATIONS, not execution reality.                         ║
║                                                                                                      ║
║  They define WHAT RIINA SHOULD EVENTUALLY SUPPORT, not what it currently does.                      ║
║                                                                                                      ║
║  Current execution focuses on CORE TYPE SYSTEM (Tracks A-C, J).                                     ║
║  Extended tracks await AXIOM ELIMINATION completion.                                                 ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART VI: GAP CLOSURE STRATEGY

## 6.1 Priority Matrix

| Priority | Focus Area | Tracks | Rationale |
|----------|------------|--------|-----------|
| **P0** | Axiom Elimination | A, B, C | Foundation — blocks everything |
| **P1** | Core Type System | A-04, A-11, B-01, C-02 | Must be sound before expansion |
| **P2** | Effect Gate Spec | D-06, D-15, H-08 | Hardware integration |
| **P3** | Verified Stdlib | F-01, F-17, Y | Crypto primitives |
| **P4** | Compiler Verification | J-08, J-09, R | Trusted compilation |
| **P5** | Extended Security | All others | After core is proven |

## 6.2 Gap Closure Phases

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  PHASE 1: AXIOM ELIMINATION (Current)                                                               ║
║  ════════════════════════════════════                                                               ║
║  Focus: 18 axioms → 0                                                                               ║
║  Tracks: A-01 to A-20, B-01 to B-10, C-01 to C-10                                                   ║
║  Effort: 800-1,600 hours                                                                            ║
║  Gate: Cannot proceed until axioms eliminated                                                       ║
║                                                                                                      ║
║  PHASE 2: CORE SOUNDNESS                                                                            ║
║  ═══════════════════════                                                                            ║
║  Focus: Type safety, effect soundness, non-interference                                             ║
║  Tracks: A, B, C comprehensive proofs                                                               ║
║  Effort: 600-1,200 hours                                                                            ║
║  Gate: Core theorems fully proven                                                                   ║
║                                                                                                      ║
║  PHASE 3: MULTI-PROVER                                                                              ║
║  ═════════════════════                                                                              ║
║  Focus: Lean port, Isabelle port                                                                    ║
║  Tracks: E-02, E-03                                                                                 ║
║  Effort: 1,360-2,720 hours                                                                          ║
║  Gate: Triple verification achieved                                                                 ║
║                                                                                                      ║
║  PHASE 4: EFFECT GATE                                                                               ║
║  ═══════════════════                                                                                ║
║  Focus: Hardware integration specification + proofs                                                 ║
║  Tracks: D-01 to D-15, H-01 to H-10                                                                 ║
║  Effort: 800-1,600 hours                                                                            ║
║  Gate: Effect Gate formally specified + proven                                                      ║
║                                                                                                      ║
║  PHASE 5: STDLIB VERIFICATION                                                                       ║
║  ═══════════════════════════                                                                        ║
║  Focus: Verify riina-crypto, riina-io, etc.                                                         ║
║  Tracks: F-01 to F-20, Y                                                                            ║
║  Effort: 600-1,200 hours                                                                            ║
║  Gate: Stdlib formally verified                                                                     ║
║                                                                                                      ║
║  PHASE 6: EXTENDED DOMAINS                                                                          ║
║  ═════════════════════════                                                                          ║
║  Focus: Networking, UI/UX, storage, performance                                                     ║
║  Tracks: GA-HV, HA-LJ, Σ, Π, etc.                                                                   ║
║  Effort: 2,000-4,000 hours                                                                          ║
║  Gate: All 218 tracks at Level 3+                                                                   ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART VII: EXECUTION ROADMAP

## 7.1 Track A Immediate Focus (Axiom Elimination)

| Axiom Category | Count | Blocking Tracks | Priority |
|----------------|-------|-----------------|----------|
| Non-Interference | 5 | C-08 (TINI/TSNI) | P0 |
| Linear Soundness | 11 | A-04 (Linear types) | P0 |
| Effect Soundness | 3 | B-01 (Effects) | P0 |
| Preservation | 15 | A (Type safety) | P0 |
| Progress | 11 | A (Type safety) | P0 |

## 7.2 Research Track → Language Feature Mapping

| Research Track | RIINA Feature | Current State | Gap Action |
|----------------|---------------|---------------|------------|
| A-04 (Linear) | Linear<T> | 11 axioms | Prove |
| A-11 (Effects) | Effect rows | 3 axioms | Prove |
| B-01 (Algebraic) | perform/handle | Implemented | Prove |
| C-02 (DLM) | Secret<T> | Designed | Prove |
| C-08 (NonInt) | TINI/TSNI | 5 axioms | Prove |
| D-06 (CHERI) | Capabilities | Spec only | Implement |
| F-01 (ML-KEM) | riina-crypto | Implemented | Verify |
| F-17 (CT) | ConstantTime<T> | Partial | Complete |
| J-08 (PCC) | Proof bundles | Spec only | Implement |

## 7.3 Timeline Estimate

| Phase | Duration | Cumulative |
|-------|----------|------------|
| Phase 1 (Axioms) | 6-12 months | 6-12 months |
| Phase 2 (Soundness) | 4-8 months | 10-20 months |
| Phase 3 (Multi-Prover) | 8-16 months | 18-36 months |
| Phase 4 (Effect Gate) | 5-10 months | 23-46 months |
| Phase 5 (Stdlib) | 4-8 months | 27-54 months |
| Phase 6 (Extended) | 12-24 months | 39-78 months |

**Total: 3.25 - 6.5 years to complete all 218 tracks**

---

# APPENDIX A: TRACK-TO-FEATURE COMPREHENSIVE TABLE

| Track | Feature | Proof File | Test File | Status |
|-------|---------|------------|-----------|--------|
| A-01 | Type foundation | Typing.v | - | Level 4 |
| A-04 | Linear<T> | LinearSoundness.v | - | Level 4 |
| A-11 | Effect rows | EffectSystem.v | - | Level 4 |
| B-01 | perform/handle | EffectSystem.v | - | Level 4 |
| C-02 | Secret<T> | NonInterference.v | - | Level 4 |
| C-08 | TINI/TSNI | NonInterference.v | - | Level 4 |
| E-01 | Coq proofs | 02_FORMAL/coq/ | - | Level 5 |
| F-01 | ML-KEM | - | 05_TOOLING/ | Level 5 |
| F-17 | ConstantTime<T> | - | - | Level 4 |
| J-01 | Parser | - | 03_PROTO/ | Level 3 |

---

# DOCUMENT SIGNATURE

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  Document: RIINA_RESEARCH_EXECUTION_MAP_v1_0_0.md                                                   ║
║  Version: 1.0.0                                                                                      ║
║  Date: 2026-01-19                                                                                    ║
║  Status: AUTHORITATIVE — Maps all 218 research tracks to execution state                            ║
║                                                                                                      ║
║  This document identifies the gap between research scope and execution reality.                     ║
║  Phase 1 (Axiom Elimination) is the critical path that blocks all other progress.                   ║
║  218 tracks will take 3.25 - 6.5 years to fully execute.                                            ║
║                                                                                                      ║
║  RIINA: Rigorous Immutable Invariant — Normalized Axiom                                              ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

**END OF DOCUMENT**
