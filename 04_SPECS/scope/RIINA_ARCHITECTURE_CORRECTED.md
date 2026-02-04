# RIINA ARCHITECTURE CORRECTED

**Audit Update:** 2026-02-04 (Codex audit sync) — Active build: 0 admit., 0 Admitted., 4 axioms, 249 active files, 4,044 Qed (active), 283 total .v. Historical counts in this document remain historical.

## Version 1.0.0 — Proper Framing of Language vs Applications

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  RIINA ARCHITECTURE — CORRECTED FRAMING                                                             ║
║                                                                                                      ║
║  This document CORRECTS previous "12-Layer Vertical Integration" documents                          ║
║  that incorrectly portrayed RIINA as a platform with pre-built components.                          ║
║                                                                                                      ║
║  Classification: ULTRA KIASU | ZERO TRUST | INFINITE TIMELINE                                       ║
║  Date: 2026-01-19                                                                                    ║
║  Supersedes: RIINA_FULLSTACK_VERTICAL_INTEGRATION_v1_0_0.md (DEPRECATED)                            ║
║              RIINA_SYNERGY_MATRIX_v1_0_0.md (DEPRECATED)                                            ║
║              RIINA_COMPONENT_SPECS_v1_0_0.md (DEPRECATED)                                           ║
║                                                                                                      ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART I: THE CORRECTION

## 1.1 What Was Wrong

Previous documents incorrectly portrayed RIINA as having 12 layers of pre-built components:

```
╔═══════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                       ║
║  ❌ INCORRECT FRAMING (Previous Documents)                                            ║
║  ─────────────────────────────────────────                                            ║
║                                                                                       ║
║  "RIINA Layer 12: RUPA (Universal UI Framework)"                                      ║
║  "RIINA Layer 11: Application Runtime"                                                ║
║  "RIINA Layer 10: Security Products (MENARA, GAPURA, etc.)"                           ║
║  "RIINA Layer 9: Infrastructure (SIMPAN, NADI, etc.)"                                 ║
║  "RIINA Layer 6: TERAS-OS"                                                            ║
║  "RIINA Layer 2: Effect Gate Hardware"                                                ║
║                                                                                       ║
║  This portrayal suggested RIINA comes with pre-built:                                 ║
║  • UI frameworks                                                                      ║
║  • Security products                                                                  ║
║  • Databases                                                                          ║
║  • Operating systems                                                                  ║
║                                                                                       ║
║  THIS IS WRONG.                                                                       ║
║                                                                                       ║
╚═══════════════════════════════════════════════════════════════════════════════════════╝
```

## 1.2 What Is Correct

```
╔═══════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                       ║
║  ✅ CORRECT FRAMING                                                                   ║
║  ──────────────────                                                                   ║
║                                                                                       ║
║  RIINA = A Programming Language                                                       ║
║  ═══════════════════════════════                                                      ║
║                                                                                       ║
║  Contains (single codebase github.com/ib823/proof):                                   ║
║  • Syntax & Grammar (Bahasa Melayu)                                                   ║
║  • Type System (Linear + Effect + IFC + Security)                                     ║
║  • Compiler (riinac)                                                                  ║
║  • Formal Proofs (Coq/Lean/Isabelle)                                                  ║
║  • Standard Library (riina-crypto, riina-io, etc.)                                    ║
║  • Effect Gate Runtime Integration                                                    ║
║                                                                                       ║
║  Everything else = Programs TO BE WRITTEN in RIINA (future, separate codebases)       ║
║                                                                                       ║
╚═══════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART II: CORRECTED ARCHITECTURE VIEW

## 2.1 The Actual Architecture

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║                              RIINA ARCHITECTURE — CORRECT VIEW                                       ║
║                                                                                                      ║
╠══════════════════════════════════════════════════════════════════════════════════════════════════════╣
║                                                                                                      ║
║                          ┌─────────────────────────────────────────┐                                ║
║                          │                                         │                                ║
║                          │         RIINA (The Language)            │                                ║
║                          │         ════════════════════            │                                ║
║                          │                                         │                                ║
║                          │    Single Codebase: ib823/proof         │                                ║
║                          │                                         │                                ║
║                          │    ┌─────────────────────────────────┐  │                                ║
║                          │    │ Syntax (Bahasa Melayu)          │  │                                ║
║                          │    ├─────────────────────────────────┤  │                                ║
║                          │    │ Type System                     │  │                                ║
║                          │    │ • Linear<T>                     │  │                                ║
║                          │    │ • Secret<T>, Tainted<T>         │  │                                ║
║                          │    │ • Effect Rows                   │  │                                ║
║                          │    │ • Capability Types              │  │                                ║
║                          │    ├─────────────────────────────────┤  │                                ║
║                          │    │ Compiler (riinac)               │  │                                ║
║                          │    ├─────────────────────────────────┤  │                                ║
║                          │    │ Formal Proofs                   │  │                                ║
║                          │    │ • Coq (PRIMARY)                 │  │                                ║
║                          │    │ • Lean (SECONDARY)              │  │                                ║
║                          │    │ • Isabelle (TERTIARY)           │  │                                ║
║                          │    ├─────────────────────────────────┤  │                                ║
║                          │    │ Standard Library                │  │                                ║
║                          │    │ • riina-crypto                  │  │                                ║
║                          │    │ • riina-io                      │  │                                ║
║                          │    │ • riina-net                     │  │                                ║
║                          │    │ • riina-data                    │  │                                ║
║                          │    ├─────────────────────────────────┤  │                                ║
║                          │    │ Effect Gate Runtime             │  │                                ║
║                          │    └─────────────────────────────────┘  │                                ║
║                          │                                         │                                ║
║                          └────────────────────┬────────────────────┘                                ║
║                                               │                                                      ║
║                                               │ Programs written                                     ║
║                                               │ IN RIINA                                             ║
║                                               │                                                      ║
║                                               ▼                                                      ║
║                                                                                                      ║
║  ┌──────────────────────────────────────────────────────────────────────────────────────────────┐   ║
║  │                                                                                              │   ║
║  │                      APPLICATIONS WRITTEN IN RIINA (Future)                                  │   ║
║  │                      ══════════════════════════════════════                                  │   ║
║  │                                                                                              │   ║
║  │  ┌─────────────────────────────────────────────────────────────────────────────────────┐    │   ║
║  │  │                        SECURITY PRODUCTS                                            │    │   ║
║  │  │                                                                                     │    │   ║
║  │  │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐             │    │   ║
║  │  │  │  MENARA  │  │  GAPURA  │  │  ZIRAH   │  │ BENTENG  │  │  SANDI   │             │    │   ║
║  │  │  │  Mobile  │  │   WAF    │  │   EDR    │  │  eKYC    │  │ Signing  │             │    │   ║
║  │  │  │ Security │  │          │  │          │  │          │  │          │             │    │   ║
║  │  │  │          │  │          │  │          │  │          │  │          │             │    │   ║
║  │  │  │ SEPARATE │  │ SEPARATE │  │ SEPARATE │  │ SEPARATE │  │ SEPARATE │             │    │   ║
║  │  │  │ CODEBASE │  │ CODEBASE │  │ CODEBASE │  │ CODEBASE │  │ CODEBASE │             │    │   ║
║  │  │  └──────────┘  └──────────┘  └──────────┘  └──────────┘  └──────────┘             │    │   ║
║  │  │                                                                                     │    │   ║
║  │  └─────────────────────────────────────────────────────────────────────────────────────┘    │   ║
║  │                                                                                              │   ║
║  │  ┌─────────────────────────────────────────────────────────────────────────────────────┐    │   ║
║  │  │                        INFRASTRUCTURE                                               │    │   ║
║  │  │                                                                                     │    │   ║
║  │  │  ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐ ┌────────┐     │    │   ║
║  │  │  │ SIMPAN │ │ TUKAR  │ │  NADI  │ │  ATUR  │ │ JEJAK  │ │ MAMPAT │ │  AKAL  │     │    │   ║
║  │  │  │  (DB)  │ │(Proto) │ │ (Net)  │ │(Orch)  │ │(Telem) │ │(Compr) │ │ (ML)   │     │    │   ║
║  │  │  │        │ │        │ │        │ │        │ │        │ │        │ │        │     │    │   ║
║  │  │  │SEPARATE│ │SEPARATE│ │SEPARATE│ │SEPARATE│ │SEPARATE│ │SEPARATE│ │SEPARATE│     │    │   ║
║  │  │  └────────┘ └────────┘ └────────┘ └────────┘ └────────┘ └────────┘ └────────┘     │    │   ║
║  │  │                                                                                     │    │   ║
║  │  └─────────────────────────────────────────────────────────────────────────────────────┘    │   ║
║  │                                                                                              │   ║
║  │  ┌─────────────────────────────────────────────────────────────────────────────────────┐    │   ║
║  │  │                        SYSTEM SOFTWARE (If Desired)                                 │    │   ║
║  │  │                                                                                     │    │   ║
║  │  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐                              │    │   ║
║  │  │  │   TERAS-OS   │  │     RUPA     │  │ Effect Gate  │                              │    │   ║
║  │  │  │  (Microkernel│  │ (UI Framework│  │   Firmware   │                              │    │   ║
║  │  │  │  if built)   │  │  if built)   │  │  (if custom) │                              │    │   ║
║  │  │  │              │  │              │  │              │                              │    │   ║
║  │  │  │   SEPARATE   │  │   SEPARATE   │  │   SEPARATE   │                              │    │   ║
║  │  │  └──────────────┘  └──────────────┘  └──────────────┘                              │    │   ║
║  │  │                                                                                     │    │   ║
║  │  └─────────────────────────────────────────────────────────────────────────────────────┘    │   ║
║  │                                                                                              │   ║
║  │  NOTE: ALL of the above are PROGRAMS to be written IN RIINA.                                │   ║
║  │        They are NOT RIINA itself. They are NOT part of the RIINA codebase.                  │   ║
║  │        They would exist in SEPARATE repositories with SEPARATE release cycles.              │   ║
║  │                                                                                              │   ║
║  └──────────────────────────────────────────────────────────────────────────────────────────────┘   ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART III: DEPENDENCY DIRECTION

## 3.1 Correct Dependency Flow

```
                    ┌─────────────────────────────────────────┐
                    │                                         │
                    │              RIINA                      │
                    │         (The Language)                  │
                    │                                         │
                    │    github.com/ib823/proof               │
                    │                                         │
                    └─────────────────────────────────────────┘
                                        ▲
                                        │
                                        │ DEPENDS ON
                                        │
        ┌───────────────────────────────┼───────────────────────────────┐
        │                               │                               │
        ▼                               ▼                               ▼
┌───────────────────┐       ┌───────────────────┐       ┌───────────────────┐
│                   │       │                   │       │                   │
│      MENARA       │       │      BENTENG      │       │       SANDI       │
│                   │       │                   │       │                   │
│ Written in RIINA  │       │ Written in RIINA  │       │ Written in RIINA  │
│ Separate codebase │       │ Separate codebase │       │ Separate codebase │
│                   │       │                   │       │                   │
└───────────────────┘       └───────────────────┘       └───────────────────┘
```

## 3.2 What This Means

| Aspect | Language (RIINA) | Applications (MENARA, etc.) |
|--------|------------------|----------------------------|
| **Codebase** | github.com/ib823/proof | Separate repositories |
| **Release Cycle** | Language releases | Independent releases |
| **Dependency** | None (foundational) | Depends on RIINA |
| **Team** | Core language team | Product teams |
| **Version Stability** | Must be stable | Can evolve rapidly |

---

# PART IV: WHAT THE PREVIOUS DOCUMENTS GOT RIGHT

## 4.1 Valid Content to Preserve

Despite the incorrect framing, the previous documents contained valid content:

### 4.1.1 Valid: Research Track Integration

The mapping of research domains to features remains correct:
- Domain A (Type Theory) → Type system
- Domain B (Effects) → Effect system
- Domain C (IFC) → Security types
- etc.

### 4.1.2 Valid: Security Property Requirements

The security properties required remain correct:
- Type safety
- Non-interference
- Effect soundness
- Linear resource safety

### 4.1.3 Valid: Immutable Laws

The 11 immutable laws remain correct and unchanged.

### 4.1.4 Valid: Effect Profiles

The effect profiles for products (D40-I through D40-N) are valid as **design requirements** that inform what RIINA must support, even though the products themselves are separate.

---

# PART V: DEPRECATED DOCUMENTS

## 5.1 Documents Superseded by This

| Document | Status | Reason |
|----------|--------|--------|
| RIINA_FULLSTACK_VERTICAL_INTEGRATION_v1_0_0.md | **DEPRECATED** | Incorrect framing |
| RIINA_SYNERGY_MATRIX_v1_0_0.md | **DEPRECATED** | Based on incorrect framing |
| RIINA_COMPONENT_SPECS_v1_0_0.md | **DEPRECATED** | Based on incorrect framing |

## 5.2 How to Handle Deprecated Content

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  HANDLING DEPRECATED DOCUMENTS                                                                       ║
║                                                                                                      ║
║  1. DO NOT DELETE — They contain valid research and requirements                                    ║
║  2. MARK AS DEPRECATED — Add header noting supersession                                             ║
║  3. EXTRACT VALID CONTENT — Move to appropriate new documents                                       ║
║  4. REFRAME CORRECTLY — Products are APPLICATIONS, not LANGUAGE COMPONENTS                          ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

# PART VI: CORRECTED PRODUCT SPECIFICATIONS

## 6.1 Products as Design Drivers

The products (MENARA, GAPURA, ZIRAH, BENTENG, SANDI) serve as **design drivers** for RIINA:

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  PRODUCTS AS DESIGN DRIVERS                                                                          ║
║                                                                                                      ║
║  The products inform WHAT RIINA MUST SUPPORT, not what RIINA IS.                                    ║
║                                                                                                      ║
║  Example:                                                                                            ║
║                                                                                                      ║
║  MENARA (Mobile Security) requires:                                                                  ║
║  • Constant-time crypto operations                                                                   ║
║  • Secure enclave integration                                                                        ║
║  • Network effect tracking                                                                           ║
║  • Memory encryption                                                                                 ║
║                                                                                                      ║
║  Therefore RIINA must provide:                                                                       ║
║  • ConstantTime<T> type (enforced by type system)                                                   ║
║  • Effect system with Hardware effects                                                               ║
║  • Network effect tracking                                                                           ║
║  • Memory encryption primitives in stdlib                                                            ║
║                                                                                                      ║
║  The product DRIVES the language design.                                                            ║
║  The product is NOT part of the language.                                                           ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

## 6.2 Effect Profiles as Language Requirements

The effect profiles (D40-I through D40-N) remain valid as requirements:

| Profile | Product | Effect Requirements | RIINA Must Support |
|---------|---------|---------------------|-------------------|
| D40-I | MENARA | `EnclaveCrypto`, `SecureStorage` | Hardware effects |
| D40-J | GAPURA | `NetworkIO`, `TLSInspect` | Network effects |
| D40-K | ZIRAH | `KernelAccess`, `MemoryForensics` | System effects |
| D40-L | BENTENG | `BiometricCapture`, `FaceRecognition` | Sensor effects |
| D40-M | SANDI | `HSMAccess`, `TimestampAuthority` | Crypto effects |
| D40-N | INFRA | `PersistentStore`, `DistributedState` | Storage effects |

---

# PART VII: STANDARD LIBRARY SCOPE

## 7.1 What IS Part of RIINA (stdlib)

The standard library primitives ARE part of RIINA because they are foundational building blocks:

```
/05_TOOLING/crates/
├── riina-crypto/         ← Cryptographic primitives (AES, SHA-3, ML-KEM, etc.)
├── riina-io/             ← I/O primitives (File, Stream, etc.)
├── riina-net/            ← Network primitives (Socket, TLS, etc.)
├── riina-data/           ← Data structure primitives
└── riina-core/           ← Core types and traits
```

## 7.2 Why stdlib IS Part of RIINA

| Reason | Explanation |
|--------|-------------|
| **LAW 3** | Zero third-party dependencies — must be written by us |
| **Verification** | stdlib must be formally verified alongside language |
| **Security** | Crypto primitives are security-critical |
| **Consistency** | Guarantees consistent behavior |

## 7.3 What IS NOT Part of RIINA

| Not RIINA | Reason |
|-----------|--------|
| SIMPAN (Database) | Application-level, not primitive |
| MENARA (Mobile Security) | Complete application |
| RUPA (UI Framework) | Application framework |
| TERAS-OS | Operating system |

---

# PART VIII: INTEGRATION STRATEGY

## 8.1 How Applications Will Use RIINA

```rust
// Example: MENARA mobile security app (future, separate codebase)

// File: menara/src/main.rii

import riina.crypto.{ml_kem_768, ml_dsa_65}
import riina.io.{secure_file}
import riina.net.{tls_connection}

// MENARA uses RIINA's type system for security
fungsi main() -> Hasil<(), Ralat> {
    // Secret type from RIINA enforces no-leak
    biar kunci: Rahsia<Bait[32]> = jana_kunci_rawak()?;
    
    // Effect tracking from RIINA ensures all side effects declared
    biar sambungan = tls_connection::new("api.menara.my")?;
    
    // Linear type from RIINA ensures key zeroized after use
    biar encrypted = ml_kem_768::encapsulate(&kunci)?;
    
    pulang Ok(())
}
```

## 8.2 Dependency Management

```
MENARA Cargo.toml (hypothetical):
──────────────────────────────────

[dependencies]
riina-std = "1.0"        # RIINA standard library
riina-crypto = "1.0"     # RIINA crypto primitives

# NO other dependencies (Law 3)
```

---

# DOCUMENT SIGNATURE

```
╔══════════════════════════════════════════════════════════════════════════════════════════════════════╗
║                                                                                                      ║
║  Document: RIINA_ARCHITECTURE_CORRECTED_v1_0_0.md                                                   ║
║  Version: 1.0.0                                                                                      ║
║  Date: 2026-01-19                                                                                    ║
║  Status: AUTHORITATIVE — Supersedes previous vertical integration documents                          ║
║                                                                                                      ║
║  This document CORRECTS the incorrect framing in previous documents.                                ║
║  RIINA is a LANGUAGE. Products are PROGRAMS written in RIINA.                                       ║
║  The dependency flows FROM applications TO RIINA, not the reverse.                                  ║
║                                                                                                      ║
║  RIINA: Rigorous Immutable Invariant — Normalized Axiom                                              ║
║                                                                                                      ║
╚══════════════════════════════════════════════════════════════════════════════════════════════════════╝
```

---

**END OF DOCUMENT**