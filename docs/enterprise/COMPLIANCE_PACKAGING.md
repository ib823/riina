# RIINA Compliance Packaging

## Overview

RIINA programs carry **machine-checkable proof certificates** that satisfy regulatory requirements. When you compile a RIINA program, the compiler can generate a compliance report mapping your code's proven properties to specific regulatory controls.

## Supported Regulations

| Regulation | Jurisdiction | RIINA Coverage |
|-----------|-------------|----------------|
| HIPAA | United States | PHI access control, audit trails, encryption at rest/transit, de-identification |
| PCI-DSS | Global | Cardholder data isolation, key management, access logging |
| GDPR | European Union | Data minimization, purpose limitation, right to erasure |
| PDPA | Malaysia | Personal data protection, cross-border transfer controls |
| PDPA | Singapore | Data protection obligations, breach notification |
| SOX | United States | Financial data integrity, audit trails |
| DO-178C | Aviation | Deterministic execution, formal verification evidence |
| ISO 26262 | Automotive | ASIL-D systematic capability, absence of interference |
| Common Criteria (EAL7) | International | Formally verified design, complete testing |
| NIST 800-53 | United States | Security controls (AC, AU, SC families) |
| CCPA | California | Consumer data rights, sale opt-out |
| FERPA | United States | Student record protection |
| BNM RMiT | Malaysia | Financial institution technology risk |
| MAS TRM | Singapore | Technology risk management |
| ISO 27001 | International | Information security management |

## How It Works

### 1. Write Your Program

```riina
// Your application code uses RIINA's security types naturally
fungsi simpan_rekod(data: Rahsia<Teks>) -> kesan (Tulis | Kripto) {
    biar terenkripsi = kripto::aes_256_gcm_sulit(kunci, data);
    fail_tulis(laluan, terenkripsi);
}
```

### 2. Generate Compliance Report

```bash
riinac verify --compliance hipaa,pci-dss myapp.rii
```

### 3. Output: Machine-Checkable Certificate

The compiler generates a structured report:

```
RIINA COMPLIANCE CERTIFICATE
============================
Program: myapp.rii
Date: 2026-01-31
Compiler: riinac 0.1.0
Prover: Rocq 9.1

HIPAA §164.312(a) — Access Control
  PROVEN: All PHI access gated by role-based authorization
  Theorem: access_control_enforced (Coq: properties/HIPAACompliance.v:42)

HIPAA §164.312(b) — Audit Controls
  PROVEN: Every PHI access logged with timestamp, user, action
  Theorem: audit_trail_complete (Coq: properties/HIPAACompliance.v:87)

HIPAA §164.312(e) — Transmission Security
  PROVEN: PHI encrypted in transit (Rahsia type prevents plaintext transmission)
  Theorem: transmission_encrypted (Coq: properties/HIPAACompliance.v:112)

PCI-DSS Req 3 — Protect Stored Cardholder Data
  PROVEN: Cardholder data type is Rahsia, encrypted at rest
  Theorem: stored_data_encrypted (Coq: properties/PCIDSSCompliance.v:34)
```

### 4. Auditor Verification

Auditors can independently verify the certificate:

```bash
# Verify that the Coq proofs compile (zero-trust)
cd 02_FORMAL/coq && make

# Check specific theorems
coqc -Q . RIINA properties/HIPAACompliance.v
Print Assumptions access_control_enforced.
# Output: "Closed under the global context" (no unproven assumptions)
```

## Integration with Existing Compliance Workflows

### For Security Auditors

RIINA compliance certificates can supplement or replace manual code review for specific controls. The certificate provides:

- **Which controls are covered** — mapped to specific regulation sections
- **The proof** — a Coq theorem that can be independently verified
- **The assumptions** — any axioms used (5 justified axioms, fully documented)

### For Compliance Officers

Include RIINA certificates in your compliance package alongside traditional evidence. The certificate demonstrates that security properties are **mathematically guaranteed**, not merely tested.

### For Procurement

RIINA programs meet the "formal methods" requirement in:
- Common Criteria EAL5-EAL7
- DO-178C Design Assurance Level A
- ISO 26262 ASIL-D Tool Confidence Level 1

## Coq Proof Files (15 Industry Compliance Proofs)

All proofs are in `02_FORMAL/coq/Industries/`:

| File | Regulation | Theorems |
|------|-----------|----------|
| MalaysiaPDPA.v | Malaysia PDPA | 10 |
| BNM_RMiT.v | Malaysia BNM | 10 |
| SingaporePDPA.v | Singapore PDPA | 10 |
| MAS_TRM.v | Singapore MAS | 10 |
| HIPAACompliance.v | US HIPAA | 10 |
| PCIDSSCompliance.v | PCI-DSS | 10 |
| GDPRCompliance.v | EU GDPR | 10 |
| SOXCompliance.v | US SOX | 10 |
| DO178CCompliance.v | Aviation DO-178C | 10 |
| ISO26262Compliance.v | Automotive ISO 26262 | 10 |
| CommonCriteriaEAL7.v | CC EAL7 | 10 |
| NISTCompliance.v | US NIST 800-53 | 10 |
| CCPACompliance.v | California CCPA | 10 |
| FERPACompliance.v | US FERPA | 10 |
| CyberTrustCompliance.v | Singapore CyberTrust | 10 |

**Total: 150 proven compliance theorems, 0 admits, 0 unjustified axioms.**

---

*RIINA — Write code. Get compliance proofs. For free.*
