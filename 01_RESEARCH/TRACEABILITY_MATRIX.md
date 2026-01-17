# RIINA TRACEABILITY MATRIX

## Document Control

```
Version: 1.0.0
Date: 2026-01-17
Classification: FOUNDATIONAL
Purpose: Map every threat to track to proof to implementation
Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE
```

---

## 1. MATRIX STRUCTURE

```
THREAT → TRACK → PROOF FILE → PROOF STATUS → IMPLEMENTATION → VERIFIED
```

Each row must have ALL columns completed for RIINA to claim completeness.

---

## 2. MEMORY CORRUPTION ATTACKS [MEM]

| ID | Threat | Track | Proof File | Status | Implementation | Verified |
|----|--------|-------|------------|--------|----------------|----------|
| MEM-001 | Stack Buffer Overflow | A, W | Syntax.v (bounds) | ⚠️ PARTIAL | riina-types | ❌ |
| MEM-002 | Heap Buffer Overflow | W | MISSING | ❌ NONE | NONE | ❌ |
| MEM-003 | Use-After-Free | A | Syntax.v (linear) | ⚠️ PARTIAL | NONE | ❌ |
| MEM-004 | Double Free | A | Syntax.v (affine) | ⚠️ PARTIAL | NONE | ❌ |
| MEM-005 | Heap Spray | W | MISSING | ❌ NONE | NONE | ❌ |
| MEM-006 | Stack Smashing | W, R | MISSING | ❌ NONE | NONE | ❌ |
| MEM-007 | Format String | A | Typing.v | ⚠️ PARTIAL | NONE | ❌ |
| MEM-008 | Integer Overflow | A | MISSING | ❌ NONE | NONE | ❌ |
| MEM-009 | Integer Underflow | A | MISSING | ❌ NONE | NONE | ❌ |
| MEM-010 | Type Confusion | A | TypeSafety.v | ⚠️ PARTIAL | NONE | ❌ |
| MEM-011 | Uninitialized Memory | A | MISSING | ❌ NONE | NONE | ❌ |
| MEM-012 | Out-of-Bounds Read | A, W | MISSING | ❌ NONE | NONE | ❌ |
| MEM-013 | Out-of-Bounds Write | A, W | MISSING | ❌ NONE | NONE | ❌ |
| MEM-014 | Null Dereference | A | Syntax.v (Option) | ⚠️ PARTIAL | NONE | ❌ |
| MEM-015 | Dangling Pointer | A, W | MISSING | ❌ NONE | NONE | ❌ |
| MEM-016 | Wild Pointer | A | MISSING | ❌ NONE | NONE | ❌ |
| MEM-017 | Memory Leak | A, B | MISSING | ❌ NONE | NONE | ❌ |
| MEM-018 | Stack Exhaustion | V | TerminationLemmas.v | ⚠️ PARTIAL | NONE | ❌ |
| MEM-019 | Heap Exhaustion | V | MISSING | ❌ NONE | NONE | ❌ |
| MEM-020 | Memory Aliasing | A | MISSING | ❌ NONE | NONE | ❌ |

**MEM SUMMARY: 0/20 COMPLETE (0%)**

---

## 3. CONTROL FLOW ATTACKS [CTL]

| ID | Threat | Track | Proof File | Status | Implementation | Verified |
|----|--------|-------|------------|--------|----------------|----------|
| CTL-001 | ROP | R, W | MISSING | ❌ NONE | NONE | ❌ |
| CTL-002 | JOP | R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-003 | COP | R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-004 | Return-to-libc | R, W | MISSING | ❌ NONE | NONE | ❌ |
| CTL-005 | SROP | R, U | MISSING | ❌ NONE | NONE | ❌ |
| CTL-006 | Code Injection | W, R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-007 | Code Reuse | R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-008 | Data-Only Attack | C, W | NonInterference.v | ⚠️ AXIOMS | NONE | ❌ |
| CTL-009 | Control Flow Bending | R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-010 | Indirect Call Hijack | R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-011 | Virtual Table Hijack | A, R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-012 | Exception Hijack | I, R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-013 | Longjmp Hijack | R | MISSING | ❌ NONE | NONE | ❌ |
| CTL-014 | GOT/PLT Overwrite | R, T | MISSING | ❌ NONE | NONE | ❌ |
| CTL-015 | Thread Hijack | X | MISSING | ❌ NONE | NONE | ❌ |

**CTL SUMMARY: 0/15 COMPLETE (0%)**

---

## 4. INJECTION ATTACKS [INJ]

| ID | Threat | Track | Proof File | Status | Implementation | Verified |
|----|--------|-------|------------|--------|----------------|----------|
| INJ-001 | SQL Injection | C, Z | NonInterference.v | ⚠️ AXIOMS | NONE | ❌ |
| INJ-002 | Command Injection | D, B | EffectSystem.v | ⚠️ PARTIAL | NONE | ❌ |
| INJ-003 | LDAP Injection | C | MISSING | ❌ NONE | NONE | ❌ |
| INJ-004 | XPath Injection | C | MISSING | ❌ NONE | NONE | ❌ |
| INJ-005 | XXE | C, P | MISSING | ❌ NONE | NONE | ❌ |
| INJ-006 | Header Injection | C | MISSING | ❌ NONE | NONE | ❌ |
| INJ-007 | Template Injection | K | MISSING | ❌ NONE | NONE | ❌ |
| INJ-008 | Code Injection | C, A | NonInterference.v | ⚠️ AXIOMS | NONE | ❌ |
| INJ-009 | Expression Language | K | MISSING | ❌ NONE | NONE | ❌ |
| INJ-010 | Log Injection | NEW | MISSING | ❌ NONE | NONE | ❌ |
| INJ-011 | Email Header | C | MISSING | ❌ NONE | NONE | ❌ |
| INJ-012 | CSV Injection | C | MISSING | ❌ NONE | NONE | ❌ |
| INJ-013 | PDF Injection | P | MISSING | ❌ NONE | NONE | ❌ |
| INJ-014 | CRLF Injection | C | MISSING | ❌ NONE | NONE | ❌ |
| INJ-015 | Null Byte Injection | A | MISSING | ❌ NONE | NONE | ❌ |

**INJ SUMMARY: 0/15 COMPLETE (0%)**

---

## 5. WEB APPLICATION ATTACKS [WEB]

| ID | Threat | Track | Proof File | Status | Implementation | Verified |
|----|--------|-------|------------|--------|----------------|----------|
| WEB-001 | Reflected XSS | C, κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-002 | Stored XSS | C, κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-003 | DOM XSS | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-004 | CSRF | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-005 | SSRF | κ, D | MISSING | ❌ NONE | NONE | ❌ |
| WEB-006 | Clickjacking | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-007 | Open Redirect | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-008 | HTTP Smuggling | κ, Ω | MISSING | ❌ NONE | NONE | ❌ |
| WEB-009 | Cache Poisoning | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-010 | Session Hijacking | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-011 | Session Fixation | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-012 | Cookie Attacks | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-013 | Path Traversal | D, C | MISSING | ❌ NONE | NONE | ❌ |
| WEB-014 | LFI | D | MISSING | ❌ NONE | NONE | ❌ |
| WEB-015 | RFI | D | MISSING | ❌ NONE | NONE | ❌ |
| WEB-016 | Prototype Pollution | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-017 | Deserialization | C | MISSING | ❌ NONE | NONE | ❌ |
| WEB-018 | HTTP Response Split | C | MISSING | ❌ NONE | NONE | ❌ |
| WEB-019 | Parameter Pollution | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-020 | Mass Assignment | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-021 | IDOR | D | MISSING | ❌ NONE | NONE | ❌ |
| WEB-022 | Verb Tampering | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-023 | Host Header Attack | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-024 | Web Cache Deception | κ | MISSING | ❌ NONE | NONE | ❌ |
| WEB-025 | GraphQL Attacks | κ, V | MISSING | ❌ NONE | NONE | ❌ |

**WEB SUMMARY: 0/25 COMPLETE (0%)**

---

## 6. AUTHENTICATION ATTACKS [AUTH]

| ID | Threat | Track | Proof File | Status | Implementation | Verified |
|----|--------|-------|------------|--------|----------------|----------|
| AUTH-001 | Credential Stuffing | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-002 | Password Spraying | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-003 | Brute Force | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-004 | Pass-the-Hash | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-005 | Pass-the-Ticket | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-006 | Kerberoasting | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-007 | Golden Ticket | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-008 | Silver Ticket | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-009 | Credential Theft | G, W | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-010 | Session Fixation | κ | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-011 | Auth Bypass | D | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-012 | OAuth Attacks | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-013 | JWT Attacks | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-014 | SAML Attacks | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-015 | SSO Attacks | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-016 | MFA Bypass | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-017 | Biometric Spoof | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-018 | Token Theft | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-019 | Replay | AA | MISSING | ❌ NONE | NONE | ❌ |
| AUTH-020 | Phishing | Ψ, AA | MISSING | ❌ NONE | NONE | ❌ |

**AUTH SUMMARY: 0/20 COMPLETE (0%) — TRACK AA REQUIRED**

---

## 7. CRYPTOGRAPHIC ATTACKS [CRYPTO]

| ID | Threat | Track | Proof File | Status | Implementation | Verified |
|----|--------|-------|------------|--------|----------------|----------|
| CRY-001 | Timing Side Channel | G | EffectAlgebra.v | ⚠️ PARTIAL | riina-core | ⚠️ PARTIAL |
| CRY-002 | Power Analysis (SPA) | G, Φ | MISSING | ❌ NONE | NONE | ❌ |
| CRY-003 | Power Analysis (DPA) | G, Φ | MISSING | ❌ NONE | NONE | ❌ |
| CRY-004 | EM Analysis | G, Φ | MISSING | ❌ NONE | NONE | ❌ |
| CRY-005 | Acoustic Analysis | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-006 | Cache Timing | G, S | MISSING | ❌ NONE | NONE | ❌ |
| CRY-007 | Padding Oracle | G | MISSING | ❌ NONE | riina-core (AEAD) | ⚠️ PARTIAL |
| CRY-008 | Chosen Plaintext | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-009 | Chosen Ciphertext | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-010 | Known Plaintext | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-011 | Meet-in-the-Middle | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-012 | Birthday Attack | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-013 | Length Extension | G | MISSING | ❌ NONE | riina-core (SHA-3) | ⚠️ PARTIAL |
| CRY-014 | Downgrade Attack | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-015 | Protocol Attack | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-016 | Implementation Flaw | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-017 | RNG Attack | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-018 | Key Reuse | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-019 | Weak Keys | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-020 | Related-Key Attack | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-021 | Differential Cryptanalysis | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-022 | Linear Cryptanalysis | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-023 | Algebraic Attack | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-024 | Quantum Attack | G | MISSING | ❌ NONE | riina-core (ML-KEM) | ⚠️ STUB |
| CRY-025 | Harvest Now Decrypt Later | G | MISSING | ❌ NONE | riina-core (ML-KEM) | ⚠️ STUB |
| CRY-026 | Key Extraction | G, W | MISSING | ❌ NONE | NONE | ❌ |
| CRY-027 | IV/Nonce Misuse | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-028 | Certificate Attack | G | MISSING | ❌ NONE | NONE | ❌ |
| CRY-029 | Random Fault | G, Φ | MISSING | ❌ NONE | NONE | ❌ |
| CRY-030 | Bleichenbacher | G | MISSING | ❌ NONE | NONE | ❌ |

**CRYPTO SUMMARY: 0/30 COMPLETE (0%)**

---

## 8. HARDWARE/MICROARCHITECTURAL [HW]

| ID | Threat | Track | Proof File | Status | Implementation | Verified |
|----|--------|-------|------------|--------|----------------|----------|
| HW-001 | Spectre v1 | S, G | MISSING | ❌ NONE | NONE | ❌ |
| HW-002 | Spectre v2 | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-003 | Spectre v4 | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-004 | Meltdown | S, U | MISSING | ❌ NONE | NONE | ❌ |
| HW-005 | Foreshadow | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-006 | ZombieLoad | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-007 | RIDL | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-008 | Fallout | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-009 | LVI | S, R | MISSING | ❌ NONE | NONE | ❌ |
| HW-010 | CacheOut | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-011 | Platypus | S, G | MISSING | ❌ NONE | NONE | ❌ |
| HW-012 | Hertzbleed | S, G | MISSING | ❌ NONE | NONE | ❌ |
| HW-013 | PACMAN | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-014 | Augury | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-015 | Retbleed | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-016 | AEPIC Leak | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-017 | CacheWarp | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-018 | GoFetch | S, G | MISSING | ❌ NONE | NONE | ❌ |
| HW-019 | Rowhammer | S, W | MISSING | ❌ NONE | NONE | ❌ |
| HW-020 | RAMBleed | S, W | MISSING | ❌ NONE | NONE | ❌ |
| HW-021 | Throwhammer | S, Ω | MISSING | ❌ NONE | NONE | ❌ |
| HW-022 | GLitch | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-023 | Drammer | S | MISSING | ❌ NONE | NONE | ❌ |
| HW-024 | Fault Injection | S, Φ | MISSING | ❌ NONE | NONE | ❌ |
| HW-025 | Cold Boot | W, Φ | MISSING | ❌ NONE | NONE | ❌ |
| HW-026 | DMA Attack | S, U | MISSING | ❌ NONE | NONE | ❌ |
| HW-027 | Evil Maid | T, U | MISSING | ❌ NONE | NONE | ❌ |
| HW-028 | Hardware Implant | Φ, T | MISSING | ❌ NONE | NONE | ❌ |
| HW-029 | Microcode Attack | S, T | MISSING | ❌ NONE | NONE | ❌ |
| HW-030 | Firmware Attack | T, U | MISSING | ❌ NONE | NONE | ❌ |

**HW SUMMARY: 0/30 COMPLETE (0%)**

---

## 9. INFORMATION FLOW [IFC]

| ID | Threat | Track | Proof File | Status | Admits | Axioms |
|----|--------|-------|------------|--------|--------|--------|
| IFC-001 | Direct Flow | C | NonInterference.v | ⚠️ | 0 | 19 |
| IFC-002 | Implicit Flow | C | NonInterference.v | ⚠️ | 0 | 19 |
| IFC-003 | Covert Storage | AC | MISSING | ❌ | - | - |
| IFC-004 | Covert Timing | AC | MISSING | ❌ | - | - |
| IFC-005 | Declassification | Z | Declassification.v | ⚠️ | 4 | 0 |

**IFC Note: NonInterference.v has 19 AXIOMS — NOT PROVEN**

---

## 10. COMPLETENESS SUMMARY

### 10.1 Overall Statistics

| Category | Total Attacks | Proofs | Complete | Percentage |
|----------|---------------|--------|----------|------------|
| MEM | 20 | 0 | 0 | 0% |
| CTL | 15 | 0 | 0 | 0% |
| INJ | 15 | 0 | 0 | 0% |
| WEB | 25 | 0 | 0 | 0% |
| AUTH | 20 | 0 | 0 | 0% |
| CRYPTO | 30 | 0 | 0 | 0% |
| HW | 30 | 0 | 0 | 0% |
| NET | 25 | 0 | 0 | 0% |
| TIME | 15 | 0 | 0 | 0% |
| COV | 15 | 0 | 0 | 0% |
| PHYS | 20 | 0 | 0 | 0% |
| HUM | 20 | 0 | 0 | 0% |
| SUPPLY | 15 | 0 | 0 | 0% |
| AI | 15 | 0 | 0 | 0% |
| DIST | 15 | 0 | 0 | 0% |
| FUT | 10 | 0 | 0 | 0% |
| **TOTAL** | **350** | **0** | **0** | **0%** |

### 10.2 Current Coq Status

| File | Theorems | Proved | Admitted | Axioms |
|------|----------|--------|----------|--------|
| NonInterference.v | ~50 | 31 | 0 | 19 |
| TypeSafety.v | ~10 | ~8 | 0 | 0 |
| Progress.v | ~5 | ~5 | 0 | 0 |
| Preservation.v | ~5 | ~5 | 0 | 0 |
| AxiomElimination.v | ~15 | 5 | 10 | 0 |
| KripkeMutual.v | ~8 | 4 | 4 | 0 |
| Others | ~400 | ~300 | 26 | 0 |
| **TOTAL** | **~493** | **~358** | **40** | **19** |

### 10.3 Gap to Complete

```
ATTACKS ENUMERATED: 350+
ATTACKS WITH PROOFS: 0

GAP: 350 MISSING PROOFS

REQUIRED WORK:
1. Complete 40 Admitted proofs
2. Prove 19 Axioms in NonInterference.v
3. Add ~350 new proofs for attack mitigations
4. Create 10 new research tracks (AA-AJ)
5. Implement verified code for each defense
6. Certified compilation to binary
```

---

## 11. REQUIRED NEW TRACKS

| Track | Name | Attacks Covered | Priority |
|-------|------|-----------------|----------|
| AA | Verified Identity | AUTH-001 to AUTH-020 | P0 |
| AB | Verified Supply Chain | SUP-001 to SUP-015 | P0 |
| AC | Covert Channel Elimination | COV-001 to COV-015 | P0 |
| AD | Time Security | TIME-004 to TIME-015 | P1 |
| AE | Verified Audit | Logging, Forensics | P1 |
| AF | Verified Updates | SUP-010, Rollback | P1 |
| AG | Verified Key Lifecycle | Key management | P0 |
| AH | Verified Protocols | TLS, QUIC, custom | P1 |
| AI | Verified Isolation | Container, VM, Sandbox | P1 |
| AJ | Verified Compliance | Regulatory | P2 |

---

## 12. ACTION ITEMS

### Immediate (P0)

1. [ ] Prove 19 axioms in NonInterference.v
2. [ ] Complete 40 Admitted proofs
3. [ ] Create Track AA (Authentication)
4. [ ] Create Track AB (Supply Chain)
5. [ ] Create Track AG (Key Management)

### Short-term (P1)

6. [ ] Create Track AC (Covert Channels)
7. [ ] Create Track AD (Time Security)
8. [ ] Add proofs for MEM-001 through MEM-020
9. [ ] Add proofs for CTL-001 through CTL-015
10. [ ] Add proofs for CRYPTO attacks

### Medium-term (P2)

11. [ ] Complete all WEB attack proofs
12. [ ] Complete all HW attack proofs
13. [ ] Implement verified code
14. [ ] Certified compilation

### Long-term (P3)

15. [ ] 100% attack coverage
16. [ ] Hardware integration
17. [ ] Real-world deployment
18. [ ] Continuous threat updates

---

*This matrix is the AUTHORITATIVE traceability for RIINA.*
*Every attack must trace to a proof.*
*No claim is valid without this traceability.*

*Status: 0% COMPLETE*
*Last updated: 2026-01-17*
