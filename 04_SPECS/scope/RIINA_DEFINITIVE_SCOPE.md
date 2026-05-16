# RIINA DEFINITIVE SCOPE DOCUMENT

**Verification:** live counts and per-lane claim levels in `PROOF_STATUS.md` and `website/public/metrics.json`. Active Coq build is 0 Admitted / 0 active axioms.

## Version 1.0.0 — The Single Source of Truth

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  ██████╗ ██╗██╗███╗   ██╗ █████╗     ███████╗ ██████╗ ██████╗ ██████╗ ███████╗                       ║
║  ██╔══██╗██║██║████╗  ██║██╔══██╗    ██╔════╝██╔════╝██╔═══██╗██╔══██╗██╔════╝                       ║
║  ██████╔╝██║██║██╔██╗ ██║███████║    ███████╗██║     ██║   ██║██████╔╝█████╗                         ║
║  ██╔══██╗██║██║██║╚██╗██║██╔══██║    ╚════██║██║     ██║   ██║██╔═══╝ ██╔══╝                         ║
║  ██║  ██║██║██║██║ ╚████║██║  ██║    ███████║╚██████╗╚██████╔╝██║     ███████╗                       ║
║  ╚═╝  ╚═╝╚═╝╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝    ╚══════╝ ╚═════╝ ╚═════╝ ╚═╝     ╚══════╝                       ║
║                                                                                                      ║
║  DEFINITIVE SCOPE DOCUMENT                                                                           ║
║  "What RIINA IS — Definitively, Unambiguously, Forever"                                             ║
║                                                                                                      ║
║  Classification: Comprehensive | Zero Trust                                       ║
║  Date: 2026-01-19                                                                                    ║
║  Repository: github.com/ib823/riina                                                                  ║
║                                                                                                      ║
║  RIINA: Rigorous Immutable Invariant — Normalized Axiom                                              ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# TABLE OF CONTENTS

1. [Executive Summary](#part-i-executive-summary)
2. [What RIINA IS](#part-ii-what-riina-is)
3. [What RIINA ENABLES](#part-iii-what-riina-enables)
4. [What RIINA IS NOT](#part-iv-what-riina-is-not)
5. [The Codebase Structure](#part-v-the-codebase-structure)
6. [Research Domain Mapping](#part-vi-research-domain-mapping)
7. [The 218 Research Tracks → Language Features](#part-vii-research-track-to-feature-mapping)
8. [Immutable Laws](#part-viii-immutable-laws)
9. [Verification Requirements](#part-ix-verification-requirements)

---

# PART I: EXECUTIVE SUMMARY

## 1.1 The Fundamental Truth

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  RIINA IS A PROGRAMMING LANGUAGE                                                                     ║
║                                                                                                      ║
║  • RIINA is NOT a platform                                                                          ║
║  • RIINA is NOT a collection of applications                                                        ║
║  • RIINA is NOT a framework                                                                         ║
║  • RIINA is NOT a security product suite                                                            ║
║                                                                                                      ║
║  RIINA IS:                                                                                          ║
║  ════════                                                                                           ║
║  A formally verified programming language where security properties                                  ║
║  are mathematically guaranteed at compile time.                                                     ║
║                                                                                                      ║
║  Single Codebase: github.com/ib823/riina                                                            ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

## 1.2 The Relationship Model

```
┌─────────────────────────────────────────────────────────────────────────────────────┐
│                                                                                     │
│                         RIINA (The Language)                                        │
│                         ═════════════════════                                       │
│                                                                                     │
│  ┌───────────────────────────────────────────────────────────────────────────────┐ │
│  │                                                                               │ │
│  │  COMPONENTS (ALL IN SINGLE CODEBASE):                                        │ │
│  │                                                                               │ │
│  │  1. SYNTAX & GRAMMAR          — Bahasa Melayu keywords                       │ │
│  │  2. TYPE SYSTEM               — Linear, Effect, IFC, Security types          │ │
│  │  3. EFFECT SYSTEM             — Row-polymorphic algebraic effects            │ │
│  │  4. COMPILER (riinac)         — Source → Verified binary                     │ │
│  │  5. FORMAL PROOFS             — Coq/Lean/Isabelle machine-checked proofs     │ │
│  │  6. STANDARD LIBRARY          — riina-crypto, riina-io, riina-net, etc.      │ │
│  │  7. RUNTIME                   — Minimal verified runtime                      │ │
│  │  8. EFFECT GATE INTEGRATION   — Hardware security mediation                   │ │
│  │  9. PLATFORM BACKENDS         — WASM, Android, iOS cross-compilation         │ │
│  │                                                                               │ │
│  └───────────────────────────────────────────────────────────────────────────────┘ │
│                                                                                     │
└─────────────────────────────────────────────────────────────────────────────────────┘
                                        │
                                        │ Programs written IN RIINA
                                        │ (SEPARATE codebases, FUTURE)
                                        ▼
┌─────────────────────────────────────────────────────────────────────────────────────┐
│                                                                                     │
│                    APPLICATIONS (Written in RIINA)                                  │
│                    ═══════════════════════════════                                  │
│                                                                                     │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐  │
│  │   MENARA    │ │   GAPURA    │ │   ZIRAH     │ │  BENTENG    │ │   SANDI     │  │
│  │   Mobile    │ │    WAF      │ │    EDR      │ │   eKYC      │ │   Signing   │  │
│  │  Security   │ │             │ │             │ │             │ │             │  │
│  │             │ │             │ │             │ │             │ │             │  │
│  │ SEPARATE    │ │ SEPARATE    │ │ SEPARATE    │ │ SEPARATE    │ │ SEPARATE    │  │
│  │ CODEBASE    │ │ CODEBASE    │ │ CODEBASE    │ │ CODEBASE    │ │ CODEBASE    │  │
│  └─────────────┘ └─────────────┘ └─────────────┘ └─────────────┘ └─────────────┘  │
│                                                                                     │
│  These are NOT RIINA. These are PROGRAMS written in RIINA.                         │
│                                                                                     │
└─────────────────────────────────────────────────────────────────────────────────────┘
```

---

# PART II: WHAT RIINA IS

## 2.1 Core Definition

**RIINA** is the world's first formally verified programming language with:

| Property | Description |
|----------|-------------|
| **Mathematical Guarantees** | All security properties proven in Coq/Lean/Isabelle |
| **Bahasa Melayu Syntax** | Native Malaysian language keywords |
| **Zero-Trust Architecture** | Compiler, hardware, and supply chain untrusted |
| **Compile-Time Security** | Security verified before runtime, not during |

## 2.2 The RIINA Codebase Components

### 2.2.1 Language Specification

```
/01_RESEARCH/specs/bahasa/
├── RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md    — Complete BM syntax
├── Keywords (fungsi, biar, kalau, pulang, rahsia, dedah, ...)
└── File extensions: .rii (source), .riih (headers)
```

### 2.2.2 Formal Proofs (02_FORMAL/)

```
/02_FORMAL/
├── coq/                    — PRIMARY (Rocq 9.1 / Coq 8.21)
│   ├── foundations/        — Syntax.v, Typing.v, Semantics.v
│   ├── type_system/        — Progress.v, Preservation.v
│   ├── effects/            — EffectSystem.v
│   └── properties/         — TypeSafety.v, NonInterference.v
├── lean/                   — SECONDARY (Lean 4)
└── isabelle/               — TERTIARY (Isabelle/HOL)
```

### 2.2.3 Prototype Implementation (03_PROTO/)

```
/03_PROTO/
├── Cargo.toml              — Rust workspace
└── crates/
    ├── riina-lexer/        — Tokenization
    ├── riina-parser/       — AST construction
    ├── riina-types/        — Type system implementation
    └── riinac/             — Compiler driver
```

### 2.2.4 Specifications (04_SPECS/)

```
/04_SPECS/
├── language/               — Language specifications
├── effect_gate/            — Effect Gate specifications
└── products/               — Product-specific effect profiles
```

### 2.2.5 Tooling & Standard Library (05_TOOLING/)

```
/05_TOOLING/
├── crates/
│   ├── riina-core/         — Cryptographic primitives
│   ├── riina-build/        — Build orchestrator
│   └── riina-verify/       — Verification orchestrator
├── tools/                  — Standalone tools
└── ada/                    — Ada/SPARK sources
```

## 2.3 What Makes RIINA Revolutionary

| Dimension | RIINA | Every Other Language |
|-----------|-------|---------------------|
| **Security Verification** | Compile-time, mathematically proven | Runtime testing, hope-based |
| **Type System** | Linear + Effect + IFC + Security + Capability + Session | Subset or none |
| **Third-Party Dependencies** | ZERO | Thousands |
| **Formal Verification** | Triple-verified (Coq + Lean + Isabelle) | Maybe one, usually none |
| **Hardware Integration** | Effect Gate enforcement | Trust the OS |
| **Threat Coverage** | 1,231+ threats made obsolete | Reactive patching |

---

# PART III: WHAT RIINA ENABLES

## 3.1 Products TO BE WRITTEN in RIINA (Future)

These are **NOT part of RIINA**. They are **applications that will be written in RIINA**:

| Product | Purpose | Codebase |
|---------|---------|----------|
| **MENARA** | Mobile Security | github.com/[org]/menara (future) |
| **GAPURA** | Web Application Firewall | github.com/[org]/gapura (future) |
| **ZIRAH** | Endpoint Detection & Response | github.com/[org]/zirah (future) |
| **BENTENG** | eKYC/Identity Verification | github.com/[org]/benteng (future) |
| **SANDI** | Digital Signatures | github.com/[org]/sandi (future) |

## 3.2 Platform Targets (Compiler Capability)

Platform targeting is a **compiler backend capability** — not a separate product:

| Target | Command | Output | Status |
|--------|---------|--------|--------|
| Native (C) | `riinac build file.rii` | Native binary via C compiler | Done |
| WebAssembly | `riinac build --target=wasm32 file.rii` | `.wasm` binary + JS glue | Phase 7 |
| Android | `riinac build --target=android-arm64 file.rii` | `.so` via NDK + JNI bridge | Phase 7 |
| iOS | `riinac build --target=ios-arm64 file.rii` | `.a` via Xcode + Swift bridge | Phase 7 |

## 3.3 Infrastructure TO BE WRITTEN in RIINA (Future)

| Component | Purpose | Status |
|-----------|---------|--------|
| **SIMPAN** | Verified database | Future |
| **TUKAR** | Verified serialization | Future |
| **NADI** | Verified networking | Future |
| **ATUR** | Verified orchestration | Future |
| **JEJAK** | Verified telemetry | Future |
| **MAMPAT** | Verified compression | Future |
| **AKAL** | Verified ML inference | Future |
| **BEKAS** | Verified containers | Future |
| **JALINAN** | Verified service mesh | Future |

## 3.3 Why Separate Codebases?

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  ANALOGY:                                                                                           ║
║                                                                                                      ║
║  RIINA is to MENARA as Python is to Django                                                          ║
║  RIINA is to BENTENG as Rust is to Firefox                                                          ║
║  RIINA is to SANDI as C is to Linux Kernel                                                          ║
║                                                                                                      ║
║  The LANGUAGE and the PROGRAMS WRITTEN IN IT are fundamentally different things.                    ║
║                                                                                                      ║
║  WHY SEPARATE:                                                                                      ║
║  1. Different release cycles                                                                        ║
║  2. Different teams (potentially)                                                                   ║
║  3. Different requirements                                                                          ║
║  4. Language stability vs application evolution                                                     ║
║  5. Clear dependency direction (applications depend on language, not vice versa)                    ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART IV: WHAT RIINA IS NOT

## 4.1 Explicit Non-Scopes

| NOT RIINA | Clarification |
|-----------|---------------|
| ❌ A security product suite | RIINA is a language; products are written IN it |
| ❌ A platform | RIINA is a language with compiler and proofs |
| ❌ A framework | RIINA is a language, not a framework |
| ❌ Pre-built applications | Applications are written in RIINA, not part of it |
| ❌ An operating system | TERAS-OS (if built) would be written in RIINA |
| ❌ A UI framework | RUPA (if built) would be written in RIINA |
| ❌ A database | SIMPAN (if built) would be written in RIINA |

## 4.2 The "12-Layer" Confusion

Previous documents incorrectly portrayed RIINA as having 12 layers of pre-built components:

```
INCORRECT INTERPRETATION (from previous documents):
─────────────────────────────────────────────────
"RIINA Layer 12: RUPA (UI framework)"       ← WRONG: RUPA is a program TO WRITE
"RIINA Layer 10: MENARA, GAPURA"            ← WRONG: These are programs TO WRITE  
"RIINA Layer 6: TERAS-OS"                   ← WRONG: This is a program TO WRITE
"RIINA Layer 2: Effect Gate"                ← PARTIALLY RIGHT: EG runtime is in RIINA

CORRECT INTERPRETATION:
───────────────────────
RIINA = The language itself (syntax, types, compiler, proofs, stdlib)
Everything else = Programs TO BE WRITTEN in RIINA (future, separate codebases)
```

---

# PART V: THE CODEBASE STRUCTURE

## 5.1 Single Authoritative Repository

```
Repository: github.com/ib823/riina
─────────────────────────────────

This repository contains EVERYTHING that IS RIINA:

riina/
├── README.md                    ← Project overview
├── CONTRIBUTING.md              ← Contribution guide
├── CHANGELOG.md                 ← Release history
│
├── 00_SETUP/                    ← Setup scripts
├── 02_FORMAL/                   ← Formal proofs (Track A)
├── 03_PROTO/                    ← Prototype (Track B)
├── 04_SPECS/                    ← Specifications (Track C)
├── 05_TOOLING/                  ← Tools (Track F)
└── 07_EXAMPLES/                 ← Example .rii files
```

## 5.2 Current Codebase Status

| Metric | Value | Notes |
|--------|-------|-------|
| **Axioms** | 18 | Target: 0 |
| **Admitted** | 45 | 92.9% Qed rate |
| **Coq Files** | 33 | All compiling |
| **Rust Tests** | 503 | All passing |
| **Research Tracks** | 218 | Defined |
| **Phase 0** | 85% | Foundation |

---

# PART VI: RESEARCH DOMAIN MAPPING

## 6.1 The 12 Core Research Domains

| Domain | Sessions | Purpose | RIINA Feature |
|--------|----------|---------|---------------|
| **A: Type Theory** | 20 | Type system foundations | Core type system |
| **B: Effect Systems** | 10 | Effect handling | Effect system |
| **C: Information Flow** | 10 | IFC techniques | Secret/Tainted types |
| **D: Hardware Security** | 15 | Hardware isolation | Effect Gate integration |
| **E: Formal Verification** | 15 | Proof techniques | Coq/Lean/Isabelle proofs |
| **F: Cryptography** | 20 | PQC and crypto | riina-crypto stdlib |
| **G: Side-Channel** | 15 | Timing attacks | Constant-time types |
| **H: Policy Languages** | 10 | Access control | BTP policy language |
| **I: Operating Systems** | 10 | OS security | Capability system |
| **J: Compiler Construction** | 15 | Compilation | Verified compiler |
| **K: Existing Systems** | 15 | Competitor analysis | Design validation |
| **L: Attack Research** | 20 | Threat landscape | Threat model |

**Subtotal: 175 sessions**

## 6.2 Extended Research Tracks

| Track Series | Count | Domain |
|--------------|-------|--------|
| R-Z (Zero-Trust) | 9 | Supply chain, hardware, termination |
| Greek (Σ, Π, Δ, etc.) | 14 | Storage, performance, distribution |
| AA-AJ | 10 | Extended security |
| AK-AO | 5 | Procurement, layout, AI-first, Syariah finance, blockchain |
| AP-AT | 5 | Quantum computing, distributed verification, hw-sw co-verification, post-quantum crypto, AI/ML safety |
| GA-HV (Networking) | 28 | Protocol security |
| HA-LJ (UI/UX) | 50 | Interface security |
| MA-MJ (Post-Axiom) | 10 | Advanced concerns |
| Extended (ΣA-FJ) | 85 | Domain extensions |

**Additional: 216 sessions → Total: 223 tracks**

---

# PART VII: RESEARCH TRACK TO FEATURE MAPPING

## 7.1 How Research Maps to Language Features

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  RESEARCH DOMAIN → RIINA LANGUAGE FEATURE                                                           ║
║                                                                                                      ║
╠══════════════════════════════════════════════════════════════════════════════════════════════════════╣
║                                                                                                      ║
║  Domain A (Type Theory)           →  Core type system                                               ║
║  ├── A-01 (MLTT)                  →  Dependent types foundation                                     ║
║  ├── A-04 (Linear Logic)          →  Linear<T>, Affine<T>                                           ║
║  ├── A-07 (Session Types)         →  Protocol verification                                          ║
║  ├── A-08 (Refinement Types)      →  SMT-backed predicates                                          ║
║  └── A-11 (Effect Types)          →  Effect row types                                               ║
║                                                                                                      ║
║  Domain B (Effect Systems)        →  Effect system                                                  ║
║  ├── B-01 (Algebraic Effects)     →  perform/handle syntax                                          ║
║  ├── B-07 (Row Polymorphism)      →  <E1, E2, ..Es>                                                 ║
║  └── B-09 (Effect Subtyping)      →  Effect masking                                                 ║
║                                                                                                      ║
║  Domain C (Information Flow)      →  Security types                                                 ║
║  ├── C-02 (DLM)                   →  Secret<T, L>, Tainted<T, S>                                    ║
║  ├── C-08 (Non-Interference)      →  TINI/TSNI proofs                                               ║
║  └── C-09 (Declassification)      →  dedah() with policy                                            ║
║                                                                                                      ║
║  Domain D (Hardware Security)     →  Effect Gate                                                    ║
║  ├── D-06 (CHERI)                 →  Capability types                                               ║
║  └── D-13 (Memory Encryption)     →  Transparent encryption                                         ║
║                                                                                                      ║
║  Domain F (Cryptography)          →  riina-crypto stdlib                                            ║
║  ├── F-01 (ML-KEM, ML-DSA)        →  PQC primitives                                                 ║
║  ├── F-08-F-10 (ZK Proofs)        →  Zero-knowledge support                                         ║
║  └── F-17 (Constant-Time)         →  ConstantTime<T> type                                           ║
║                                                                                                      ║
║  Domain G (Side-Channel)          →  Timing-safe types                                              ║
║  ├── G-01 (Timing Attacks)        →  Constant-time enforcement                                      ║
║  └── G-05 (Microarch)             →  Speculative execution defense                                  ║
║                                                                                                      ║
║  Domain H (Policy Languages)      →  BTP policy language                                            ║
║  ├── H-03 (Cedar)                 →  Policy syntax inspiration                                      ║
║  └── H-08 (Capabilities)          →  Capability tokens                                              ║
║                                                                                                      ║
║  Domain J (Compiler)              →  riinac compiler                                                ║
║  ├── J-03 (Bidirectional TC)      →  Type inference                                                 ║
║  ├── J-08 (PCC)                   →  Proof-carrying code                                            ║
║  └── J-09 (CompCert)              →  Verified compilation                                           ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

## 7.2 Complete Feature Matrix

| RIINA Feature | Research Source | Implementation Status |
|---------------|-----------------|----------------------|
| Linear types | A-04, A-05 | ✅ Type system designed |
| Effect system | B-01 to B-10 | ✅ Effect system designed |
| IFC types | C-01 to C-10 | ✅ Secret/Tainted types designed |
| Session types | A-07 | ✅ Protocol types designed |
| Refinement types | A-08 | ✅ SMT integration designed |
| Capability types | D-06, H-08 | ✅ Capability tokens designed |
| Constant-time | F-17, G-01 | ✅ ConstantTime<T> designed |
| Effect Gate | D-01 to D-15 | 🟡 Specification in progress |
| BTP policy | H-01 to H-10 | 🟡 Specification in progress |
| PQC crypto | F-01 to F-06, AS-01 | ✅ riina-crypto implemented |
| Verified compiler | J-01 to J-15 | 🟡 Prototype implemented |
| Quantum integration | AP-01 | 🔵 Research complete, Phase 6+ |
| Concurrent/distributed | AQ-01 | 🔵 Research complete, Phase 6+ |
| HW-SW co-verification | AR-01 | 🔵 Research complete, Phase 7+ |
| AI/ML safety | AT-01 | 🔵 Research complete, Phase 6+ |

---

# PART VIII: IMMUTABLE LAWS

## 8.1 The 11 Laws of RIINA

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║                                   THE 11 IMMUTABLE LAWS OF RIINA                                    ║
║                                                                                                      ║
╠══════════════════════════════════════════════════════════════════════════════════════════════════════╣
║                                                                                                      ║
║  LAW 1: MATHEMATICAL PROOF                                                                          ║
║  ═══════════════════════════                                                                        ║
║  Every security property MUST be proven in Coq, Lean, AND Isabelle.                                 ║
║  No property is considered secure until machine-verified in all three.                               ║
║                                                                                                      ║
║  LAW 2: CONSTANT-TIME CRYPTOGRAPHY                                                                  ║
║  ═══════════════════════════════════                                                                ║
║  All cryptographic operations MUST be constant-time.                                                ║
║  The type system enforces this at compile time.                                                     ║
║                                                                                                      ║
║  LAW 3: ZERO THIRD-PARTY DEPENDENCIES                                                               ║
║  ═════════════════════════════════════                                                              ║
║  Every line of code in the trusted computing base MUST be:                                          ║
║  • Written by us                                                                                    ║
║  • Verified by us                                                                                   ║
║  • Auditable by us                                                                                  ║
║                                                                                                      ║
║  LAW 4: POST-QUANTUM CRYPTOGRAPHY                                                                   ║
║  ═════════════════════════════════                                                                  ║
║  All cryptographic primitives MUST be quantum-resistant.                                            ║
║  ML-KEM-768, ML-DSA-65, SHA-3, AES-256 as baselines.                                               ║
║                                                                                                      ║
║  LAW 5: INFORMATION FLOW CONTROL                                                                    ║
║  ═══════════════════════════════                                                                    ║
║  All data flows MUST be tracked at compile time.                                                    ║
║  Secret data cannot flow to public outputs without explicit declassification.                       ║
║                                                                                                      ║
║  LAW 6: LINEAR RESOURCE MANAGEMENT                                                                  ║
║  ═══════════════════════════════════                                                                ║
║  Secrets MUST be used exactly once.                                                                 ║
║  Memory MUST be zeroized on deallocation.                                                           ║
║  No use-after-free. No double-free. No dangling references.                                         ║
║                                                                                                      ║
║  LAW 7: EXPLICIT EFFECT TRACKING                                                                    ║
║  ══════════════════════════════                                                                     ║
║  All side effects MUST be declared in function signatures.                                          ║
║  Pure functions are proven pure.                                                                    ║
║                                                                                                      ║
║  LAW 8: DEFENSE IN DEPTH                                                                            ║
║  ══════════════════════════                                                                         ║
║  Multiple independent security mechanisms.                                                          ║
║  Failure of one does not compromise the system.                                                     ║
║                                                                                                      ║
║  LAW 9: EFFECT GATE ENFORCEMENT                                                                     ║
║  ══════════════════════════════                                                                     ║
║  Hardware-enforced security mediation.                                                              ║
║  Software cannot bypass hardware gates.                                                             ║
║                                                                                                      ║
║  LAW 10: HARDWARE ATTESTATION                                                                       ║
║  ═════════════════════════════                                                                      ║
║  All hardware assumptions MUST be attested.                                                         ║
║  Unknown hardware = untrusted execution.                                                            ║
║                                                                                                      ║
║  LAW 11: GOVERNANCE ENFORCEMENT                                                                     ║
║  ═════════════════════════════                                                                      ║
║  Policy decisions traceable to authorized entities.                                                 ║
║  Declassification requires policy approval.                                                         ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART IX: VERIFICATION REQUIREMENTS

## 9.1 What Must Be Proven

| Property | Proof Requirement | Current Status |
|----------|-------------------|----------------|
| **Type Safety** | Progress + Preservation | 🟡 18 axioms remain |
| **Non-Interference** | TINI + TSNI | 🟡 In progress |
| **Effect Soundness** | Effect tracking sound | 🟡 Axioms needed |
| **Linear Resource Safety** | No UAF/DF/DR | 🟡 Axioms needed |
| **Memory Safety** | Spatial + temporal | 🟡 Axioms needed |
| **Constant-Time** | No timing leaks | 📋 Defined |
| **Capability Safety** | No capability forgery | 📋 Defined |

## 9.2 Verification Targets

| Target | Current | Goal |
|--------|---------|------|
| **Axioms** | 18 | 0 |
| **Admitted** | 45 | 0 |
| **Qed Rate** | 92.9% | 100% |
| **Proof Assistants** | 1 (Coq) | 3 (Coq + Lean + Isabelle) |

---

# APPENDIX A: TERMINOLOGY GLOSSARY

| Term | Definition |
|------|------------|
| **RIINA** | The programming language (Rigorous Immutable Invariant — Normalized Axiom) |
| **riinac** | The RIINA compiler |
| **Effect Gate** | Hardware security mediation layer |
| **BTP** | BENTENG Trust Policy language |
| **Proof Bundle** | Compiler-generated security proofs |
| **Secret<T>** | Type for secret data |
| **Tainted<T, S>** | Type for untrusted input |
| **Linear<T>** | Type for exactly-once use |
| **ConstantTime<T>** | Type enforcing constant-time operations |

---

# APPENDIX B: DOCUMENT CROSS-REFERENCES

| Document | Purpose | Relationship to This |
|----------|---------|---------------------|
| CTSS_v1_0_1.md | Core Type System Specification | Details of type system |
| TERAS-LANG-LEXER-SPEC_v1_0_0.md | Lexer specification | Syntax details |
| TERAS-LANG-AST_v1_0_0.md | AST specification | AST node definitions |
| TERAS_DEFINITIVE_PLAN_v1_0_0.md | Execution plan | Research session details |
| CHANGELOG.md | Release history | Public release notes |

---

# DOCUMENT SIGNATURE

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  Document: RIINA_DEFINITIVE_SCOPE_v1_0_0.md                                                         ║
║  Version: 1.0.0                                                                                      ║
║  Date: 2026-01-19                                                                                    ║
║  Status: AUTHORITATIVE — Single Source of Truth                                                      ║
║                                                                                                      ║
║  This document establishes DEFINITIVELY what RIINA is and is not.                                   ║
║  All other documents MUST align with this scope definition.                                         ║
║  Any document that contradicts this scope is INCORRECT.                                             ║
║                                                                                                      ║
║  RIINA: Rigorous Immutable Invariant — Normalized Axiom                                              ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

**END OF DOCUMENT**
