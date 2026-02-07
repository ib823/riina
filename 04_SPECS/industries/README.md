# RIINA Industry Specifications

**Audit Update:** 2026-02-06 (Session 78: Proof Depth 20+ All Files) — 7,929 Coq Qed + 6154 Lean theorems + 6227 Isabelle lemmas = 20,310 total proofs. 0 Admitted/sorry across all provers. 1 axiom (policy). 250 active .v, 178 .lean, 175 .thy. 6149 triple-prover theorems. 845 Rust tests.

This directory contains industry-specific security requirements and threat models for RIINA.

## Coordination Files

| File | Description |
|------|-------------|
| `00_COORDINATION.md` | Master coordination across all industries |
| `00_SUMMARY.md` | Complete summary of industry coverage |

## Industry Specifications

| File | Industry | Focus Areas |
|------|----------|-------------|
| `IND_A_MILITARY.md` | Military & Defense | Classified systems, weapons, C4ISR |
| `IND_B_HEALTHCARE.md` | Healthcare | HIPAA, medical devices, patient data |
| `IND_C_FINANCIAL.md` | Financial Services | PCI-DSS, trading, banking |
| `IND_D_AEROSPACE.md` | Aerospace | Avionics, satellites, DO-178C |
| `IND_E_ENERGY.md` | Energy & Utilities | SCADA, grid, nuclear |
| `IND_F_TELECOM.md` | Telecommunications | 5G, network infrastructure |
| `IND_G_GOVERNMENT.md` | Government | FedRAMP, classified, e-gov |
| `IND_H_TRANSPORTATION.md` | Transportation | Autonomous vehicles, rail, maritime |
| `IND_I_MANUFACTURING.md` | Manufacturing | ICS, OT, supply chain |
| `IND_J_RETAIL.md` | Retail & E-commerce | POS, payments, inventory |
| `IND_K_MEDIA.md` | Media & Entertainment | DRM, streaming, content |
| `IND_L_EDUCATION.md` | Education | FERPA, LMS, research |
| `IND_M_REALESTATE.md` | Real Estate | PropTech, smart buildings |
| `IND_N_AGRICULTURE.md` | Agriculture | AgTech, precision farming |
| `IND_O_LEGAL.md` | Legal | Attorney-client, e-discovery |

## Coverage

- **15 industries** with comprehensive threat models
- **1,500+ industry-specific threats** identified
- **Cross-industry synergies** documented in `../cross-cutting/SYNERGY_MATRIX.md`

## Integrity

All files are SHA-256 verified. See `../CHECKSUMS.sha256` for hashes.

---
*RIINA: Rigorous Immutable Invariant — Normalized Axiom*
