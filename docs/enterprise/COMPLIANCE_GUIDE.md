# RIINA Compliance System — User Guide

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

These are proven theorems in Coq (4,825 Qed proofs in active build, 0 admits, 4 justified axioms). The compiler IS the security tool. The `--compliance` flag adds **industry-specific** rules on top of these universal guarantees.

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

## Related Documentation

- [CERTIFICATION.md](CERTIFICATION.md) — Proof certificate format and verification
- [COMPLIANCE_PACKAGING.md](COMPLIANCE_PACKAGING.md) — Compliance packaging overview
- [04_SPECS/industries/](../../04_SPECS/industries/) — Industry-specific formal specifications (15 files)
- [02_FORMAL/coq/Industries/](../../02_FORMAL/coq/Industries/) — Coq compliance proofs (150 theorems)

---

*RIINA v0.2.0 — Compliance proven. Mathematically verified.*
