# RIINA Specifications (Track C)

This directory contains formal specifications for RIINA.

## Structure

```
04_SPECS/
├── scope/              ← Definitive scope and architecture (3 files)
│   ├── RIINA_DEFINITIVE_SCOPE.md
│   ├── RIINA_ARCHITECTURE_CORRECTED.md
│   └── RIINA_RESEARCH_EXECUTION_MAP.md
├── industries/         ← Industry-specific requirements (17 files)
│   ├── 00_COORDINATION.md
│   ├── 00_SUMMARY.md
│   └── IND_[A-O]_*.md
├── cross-cutting/      ← Cross-cutting concerns (4 files)
│   ├── EXHAUSTIVENESS_AUDIT.md
│   ├── SYNERGY_MATRIX.md
│   ├── PERFORMANCE_TEMPLATES.md
│   └── UI_UX_TEMPLATES.md
├── language/           ← Language specification documents
├── effect_gate/        ← Effect Gate specification
├── products/           ← Product-specific specifications
└── CHECKSUMS.sha256    ← SHA-256 verification hashes
```

## Recent Additions (2026-01-19)

- **scope/**: Definitive project boundaries and architecture
- **industries/**: 15 industry specifications (Military, Healthcare, Financial, etc.)
- **cross-cutting/**: Templates and audit documents

## Integrity Verification

```bash
cd 04_SPECS && sha256sum -c CHECKSUMS.sha256
```

## Dependencies

- Track A: Provides formal definitions to cite
- Track B: Provides implementation feedback
- Research: Provides foundation decisions

---
*RIINA: Rigorous Immutable Integrity No-attack Assured*
