# RIINA Cross-Cutting Specifications

**Verification:** 12,678 Coq Qed (compiled, 0 Admitted, 0 active axioms) — Coq is the only mechanized lane | 3364 Rust tests | the other prover trees are machine-generated (claim-level tracked, not independent verification)

This directory contains cross-cutting concerns that span multiple industries and domains.

## Files

| File | Description |
|------|-------------|
| `EXHAUSTIVENESS_AUDIT.md` | Forensic audit of specification completeness |
| `DOMAIN_R5_CHECKLIST_v1_0_0.md` | Non-inflated maturity and audit standard for grading any domain `R0-R5` |
| `DOMAIN_R5_WORKSHEET_TEMPLATE_v1_0_0.md` | Reusable per-domain audit worksheet aligned to the R5 checklist |
| `SYNERGY_MATRIX.md` | Cross-industry synergy and reuse matrix |
| `PERFORMANCE_TEMPLATES.md` | Performance and size constraint templates |
| `UI_UX_TEMPLATES.md` | User interface and experience security templates |

## Purpose

These documents ensure:
- No gaps in security coverage across industries
- No domain is overstated beyond its real evidence
- Every domain can be graded with the same audit standard
- Maximum reuse of security patterns
- Consistent performance requirements
- Secure UI/UX patterns

## Integrity

All files are SHA-256 verified. See `../CHECKSUMS.sha256` for hashes.

---
*RIINA: Rigorous Immutable Invariant — Normalized Axiom*
