# RIINA Compliance System — User Guide

**Verification:** 7,929 Coq Qed (compiled, 0 Admitted, 1 policy axiom) | 10 independent provers | 852 Rust tests

## Overview

RIINA's compliance system is **compiler-integrated** — not an external CI pipeline, not a third-party scanner. When you run `riinac check --compliance`, the compiler itself validates your code against industry-specific security rules backed by formal proofs.

This guide covers everything you need to use, verify, and extend the compliance system.

---

## Default Security (Always On)

Every RIINA program gets these guarantees **without any flags**:

| Property | What it means | Proof |
|----------|--------------|-------|
| Type safety | No runtime type errors | `type_system/TypeSafety.v` |
| Non-interference | Secret data cannot flow to public outputs | `properties/NonInterference_v2.v` |
| Effect safety | Functions cannot perform undeclared side effects | `effects/EffectSafety.v` |
| Declassification correctness | Secrets only released through authorized policy | `properties/Declassification.v` |

These are proven theorems in Coq (4,885 Qed proofs in active build, 0 admits, 4 justified axioms). The compiler IS the security tool. The `--compliance` flag adds **industry-specific** rules on top of these universal guarantees.

---

## 15 Compliance Profiles

| Slug | Regulation | Jurisdiction | Rule Count | Spec Total |
|------|-----------|-------------|------------|------------|
| `pci-dss` | PCI-DSS: Payment Card Industry Data Security Standard | Global | 3 | 78 |
| `pdpa` | PDPA: Malaysia Personal Data Protection Act 2010 | Malaysia | 2 | 14 |
| `bnm` | BNM RMiT: Bank Negara Malaysia Risk Management in Technology | Malaysia | 1 | 26 |
| `hipaa` | HIPAA: US Health Insurance Portability and Accountability Act | United States | 0 | 54 |
| `cmmc` | CMMC: US Cybersecurity Maturity Model Certification | United States | 0 | 110 |
| `sox` | SOX: Sarbanes-Oxley Act | United States | 0 | 18 |
| `gdpr` | GDPR: EU General Data Protection Regulation | European Union | 0 | 42 |
| `do-178c` | DO-178C: Airborne Systems Software | Aviation | 0 | 66 |
| `iec-62443` | IEC 62443: Industrial Automation and Control Systems Security | Industrial | 0 | 51 |
| `nerc-cip` | NERC CIP: Critical Infrastructure Protection | North America | 0 | 35 |
| `fda-21cfr` | FDA 21 CFR Part 11: Electronic Records and Signatures | United States | 0 | 22 |
| `iso-27001` | ISO 27001: Information Security Management Systems | International | 0 | 93 |
| `nist-800-53` | NIST 800-53: Security and Privacy Controls for Federal Systems | United States | 0 | 326 |
| `mas-trm` | MAS TRM: Technology Risk Management | Singapore | 0 | 38 |
| `itar` | ITAR: International Traffic in Arms Regulations | United States | 0 | 16 |

Profiles with 0 rules are stubs — the framework is in place, rules are being added incrementally. See [Current Rule Coverage](#current-rule-coverage) for details.

---

## CLI Usage

### Check with compliance profiles

```bash
# Single profile
riinac check myapp.rii --compliance pci-dss

# Multiple profiles (comma-separated)
riinac check myapp.rii --compliance pci-dss,pdpa,bnm
```

### List available profiles

```bash
riinac --list-compliance
```

### Generate audit reports

```bash
# Text report to stdout
riinac check myapp.rii --compliance hipaa --report

# JSON report to stdout
riinac check myapp.rii --compliance pci-dss --report-json

# Write report to file
riinac check myapp.rii --compliance pci-dss,pdpa --report --report-output audit_report.txt
riinac check myapp.rii --compliance pci-dss --report-json --report-output audit_report.json
```

---

## Certificate & Audit Report

### Text Format

```
═══════════════════════════════════════════════════════════════════════
  RIINA COMPLIANCE REPORT
═══════════════════════════════════════════════════════════════════════
  Compiler:    RIINA v0.2.0
  File:        myapp.rii
  SHA-256:     a1b2c3d4...
  Timestamp:   2026-02-01T12:00:00Z
  Verdict:     PASS
───────────────────────────────────────────────────────────────────────
  Rules checked: 3   Violations: 0   Errors: 0   Warnings: 0
───────────────────────────────────────────────────────────────────────

  PROFILE: PCI-DSS: Payment Card Industry Data Security Standard
  Coverage: 3/78 rules (3.8%)
  Status: CLEAN

═══════════════════════════════════════════════════════════════════════
  This report is a machine-generated audit artifact.
  Compliance rules are backed by Coq formal proofs.
  Verify integrity: sha256sum myapp.rii == a1b2c3d4...
═══════════════════════════════════════════════════════════════════════
```

### JSON Format

```json
{
  "riina_version": "0.2.0",
  "file": "myapp.rii",
  "source_sha256": "a1b2c3d4...",
  "timestamp": "2026-02-01T12:00:00Z",
  "verdict": "PASS",
  "total_rules_checked": 3,
  "total_violations": 0,
  "total_errors": 0,
  "total_warnings": 0,
  "profiles": [
    {
      "profile": "pci-dss",
      "description": "PCI-DSS: Payment Card Industry Data Security Standard",
      "rules_implemented": 3,
      "rules_total": 78,
      "coverage_pct": 3.8,
      "errors": 0,
      "warnings": 0,
      "violations": []
    }
  ]
}
```

### Verdict Logic

| Verdict | Meaning |
|---------|---------|
| `PASS` | Zero violations |
| `PASS_WITH_WARNINGS` | Warnings only, no errors |
| `FAIL` | At least one error-severity violation |

The SHA-256 hash covers the source file. Anyone with the source can recompute the hash to verify report integrity.

---

## Auditor Verification (Zero-Trust)

An auditor does not need to trust RIINA. They can verify everything independently:

```bash
# 1. Clone the repository
git clone https://github.com/ib823/riina.git && cd riina

# 2. Build the compiler from source (zero external dependencies)
cd 03_PROTO && cargo build --release -p riinac && cd ..

# 3. Run compliance check themselves
./03_PROTO/target/release/riinac check myapp.rii --compliance pci-dss --report

# 4. Verify the Coq proofs compile (proves security theorems are valid)
cd 02_FORMAL/coq && make
# Expected: 245 files, 0 errors, 0 admits

# 5. Check axiom count
grep -r "^Axiom " 02_FORMAL/coq/**/*.v | wc -l
# Expected: 4 (all justified — see 02_FORMAL/coq/AXIOM_JUSTIFICATION.md)

# 6. Verify source hash matches report
sha256sum myapp.rii
# Must match the SHA-256 in the report
```

If step 4 succeeds, every theorem backing the compliance rules is mathematically valid.

---

## Current Rule Coverage

These are the rules currently implemented. Coverage is honest — profiles with 0 rules are frameworks awaiting rule contributions.

### PCI-DSS (3 rules implemented / 78 spec total)

| Rule ID | Severity | Description |
|---------|----------|-------------|
| PCI-DSS-3.4 | Error | Secret declassification requires Prove guard |
| PCI-DSS-6.5 | Error | Card data variables must use `Secret<_>` type |
| PCI-DSS-8.3 | Warning | Authentication functions must require Crypto effect |

### PDPA Malaysia (2 rules / 14 spec total)

| Rule ID | Severity | Description |
|---------|----------|-------------|
| PDPA-S7 | Error | User input must be `Tainted<_, UserInput>` |
| PDPA-S24 | Error | No Network effect on personal data without sanitization |

### BNM RMiT (1 rule / 26 spec total)

| Rule ID | Severity | Description |
|---------|----------|-------------|
| BNM-RMiT-10 | Warning | Financial crypto must use `ConstantTime<_>` |

### All other profiles

HIPAA, CMMC, SOX, GDPR, DO-178C, IEC 62443, NERC CIP, FDA 21 CFR, ISO 27001, NIST 800-53, MAS TRM, ITAR — **0 rules implemented**. The profile framework is in place; rules will be added as the community contributes them.

---

## Requesting New Rules

Open a GitHub Issue at [github.com/ib823/riina/issues](https://github.com/ib823/riina/issues) with:

1. **Profile slug** — Which regulation (e.g., `hipaa`)
2. **Regulation section** — Specific clause (e.g., "HIPAA §164.312(a)(1)")
3. **Rule description** — What the compiler should check
4. **Severity** — `error` (blocks compilation) or `warning` (advisory)
5. **Spec reference** — Link to the regulation text or cite `04_SPECS/industries/IND_*.md`

Use the "Feature Request" issue template if available.

---

## Contributing Rules

Rules live in `03_PROTO/crates/riina-compliance/src/rules.rs`.

### Rule structure

Each rule is a function that inspects the AST and returns violations:

```rust
fn check_rule(ast: &Program, profile: &str) -> Vec<Violation> {
    // Inspect AST nodes for compliance violations
    // Return Violation { rule_id, severity, message }
}
```

### Steps to add a rule

1. Add the check function in `rules.rs`
2. Register it in the profile's rule list in `lib.rs`
3. Update the `rules_implemented` count for the profile
4. Add a test in `tests/` that exercises the rule
5. Reference the spec: add a comment `// Spec: 04_SPECS/industries/IND_*.md §X.Y`
6. Run `cargo test --all` to verify

### Testing

```bash
cd 03_PROTO
cargo test -p riina-compliance
cargo test --all   # Full suite
```

---

## Roadmap

- **More rules for existing profiles** — Priority: PCI-DSS, HIPAA, GDPR, PDPA
- **New profiles** — As requested by the community
- **Rule marketplace** — Community-contributed rule packages (concept stage)
- **Automated spec extraction** — Parse regulation documents into rule skeletons

---

## Platform-Specific Compliance

When targeting non-native platforms (Phase 7), additional compliance considerations apply:

| Platform | Compliance Note |
|----------|----------------|
| **WASM** | WASM sandboxing provides additional isolation; linear memory model preserves RIINA's security invariants within the browser sandbox |
| **Android** | Google Play Store requires APK signing; RIINA-generated `.so` libraries are compatible with standard Android build toolchains |
| **iOS** | Apple App Store requires code signing; RIINA-generated `.a` static libraries integrate with Xcode toolchain; App Transport Security (ATS) applies to network effects |

Compliance reports generated by `riinac check --compliance` are valid regardless of target platform — the formal proofs hold for all backends.

---

## Theorem Traceability

Every compliance claim maps to a named, machine-checked theorem in Coq. These are not assertions or test cases — they are formal proofs that compile with `make` in `02_FORMAL/coq/`.

### HIPAA (HIPAACompliance.v)

| HIPAA Clause | Requirement | Coq Theorem | Status |
|-------------|-------------|-------------|--------|
| §164.312(a)(1) | Access control for PHI | `COMPLY_001_01` | Qed |
| §164.312(a)(2)(iv) | Encryption at rest (AES-256) | `COMPLY_001_01` | Qed |
| §164.312(e)(1) | Encryption in transit (TLS 1.3) | `COMPLY_001_02` | Qed |
| §164.312(e)(2)(ii) | PHI integrity during transmission | `COMPLY_001_03` | Qed |
| §164.312(b) | Audit controls | `COMPLY_001_09` | Qed |
| §164.312(c)(1) | PHI integrity | `COMPLY_001_04` | Qed |

### PCI-DSS (PCIDSSCompliance.v)

| PCI-DSS Req | Requirement | Coq Theorem | Status |
|------------|-------------|-------------|--------|
| 3.3 | PAN masking (display) | `COMPLY_002_01_pan_masking` | Qed |
| 3.4 | PAN encryption (AES-256+) | `COMPLY_002_02_pan_encryption` | Qed |
| 3.2 | CVV never stored | `COMPLY_002_03_cvv_never_stored` | Qed |
| 3.2 | PIN never stored | `COMPLY_002_04_pin_never_stored` | Qed |
| 3.6 | Key rotation detection | `COMPLY_002_05_key_rotation_detection` | Qed |
| 7.1 | Need-to-know access | `COMPLY_002_06_access_requires_need_to_know` | Qed |
| 8.3 | MFA required | `COMPLY_002_08_mfa_required` | Qed |
| 10.1 | Audit trail (timestamp/user/action) | `COMPLY_002_09_audit_entry_has_timestamp` | Qed |

### DO-178C (DO178CCompliance.v)

| DO-178C Obj | Requirement | Coq Theorem | Status |
|------------|-------------|-------------|--------|
| Table A-4, Obj 1 | Trace completeness (code→tests) | `COMPLY_003_01` | Qed |
| Table A-4, Obj 2 | Trace code and test non-empty | `COMPLY_003_02` | Qed |
| Table A-3, Obj 5 | MC/DC coverage implies decision coverage | `COMPLY_003_06` | Qed |
| Table A-7, Obj 1 | Verification completeness | `COMPLY_003_09` | Qed |

### Common Criteria EAL7 (CommonCriteriaEAL7.v)

| CC Class | Requirement | Coq Theorem | Status |
|----------|-------------|-------------|--------|
| FDP_IFC | Information flow — label reflexivity | `CC_001_label_reflexivity` | Qed |
| FDP_IFC | Information flow — label transitivity | `CC_002_label_transitivity` | Qed |
| FDP_IFF | Bell-LaPadula simple security | `CC_009_blp_simple_security_sound` | Qed |
| FDP_IFF | Bell-LaPadula *-property | `CC_010_blp_star_property_sound` | Qed |
| ADV_FSP | Architecture completeness | `CC_012_architecture_completeness` | Qed |
| ADV_SPM | Formal verification required | `CC_013_formal_verification_required` | Qed |
| FPT_PHP | Non-bypassability | `CC_015_non_bypassability` | Qed |
| FPT_SEP | Domain separation | `CC_017_domain_separation` | Qed |

---

## Related Documentation

- [CERTIFICATION.md](CERTIFICATION.md) — Proof certificate format and verification
- [COMPLIANCE_PACKAGING.md](COMPLIANCE_PACKAGING.md) — Compliance packaging overview
- [04_SPECS/industries/](../../04_SPECS/industries/) — Industry-specific formal specifications (15 files)
- [02_FORMAL/coq/compliance/](../../02_FORMAL/coq/compliance/) — Coq compliance proofs
- [02_FORMAL/coq/domains/](../../02_FORMAL/coq/domains/) — Domain-specific proofs (Common Criteria, etc.)

---

*RIINA v0.2.0 — Compliance proven. Mathematically verified.*
