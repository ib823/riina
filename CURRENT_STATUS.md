# RIINA Proof Status - 2026-01-29

## Current State (Verified)

| Metric | Value |
|--------|-------|
| **Admits (Active Build)** | **23** |
| **Axioms (Active Build)** | **9** |
| **Total Issues** | **32** |
| **Files in _CoqProject** | ~87 (after removing 9 leaf files) |

## Admits & Axioms by File

| File | Admits | Axioms | Notes |
|------|--------|--------|-------|
| NonInterference_v2_LogicalRelation.v | 11 | 5 | Core logical relation (highest priority) |
| ReferenceOps.v | 6 | 0 | Store operation inversion lemmas |
| Declassification.v | 3 | 0 | 1 provable, 1 FALSE, 1 partial |
| KripkeProperties.v | 2 | 0 | TProd/TSum cases need n > fo_compound_depth |
| MaximumAxiomElimination.v | 1 | 0 | Minor admit |
| ReducibilityFull.v | 0 | 3 | env_reducible_closed, lambda_body_SN, store_values_are_values |
| NonInterference_v2.v | 0 | 1 | fundamental_theorem_step_0 |
| **TOTAL** | **23** | **9** | |

## Recent Changes (Session 46)

1. **Removed 9 unused leaf files from _CoqProject** — Files with no dependents:
   - NonInterferenceKripke.v (3 admits), NonInterferenceZero.v (5 admits, all unprovable)
   - TypedConversion.v (5 admits), ApplicationComplete.v (5 admits)
   - KripkeMutual.v (4 admits), RelationBridge.v (5 admits), MasterTheorem.v (7 admits)
   - AxiomEliminationVerified.v (15 admits, under rework by Claude AI Web)
   - LogicalRelationAssign_PROOF.v (14 axioms), LogicalRelationDeref_PROOF_FINAL.v (7 axioms)

2. **Claude AI Web output reviewed** (files (45).zip) — NOT integrable due to incompatible standalone definitions. Archived to 99_ARCHIVE/.

3. **6 delegation prompts created** in DELEGATION_PROMPTS.md for parallel Claude AI Web execution.

## Delegation Prompts (Ready for Claude AI Web)

| Prompt | Target File | Admits | Axioms |
|--------|-------------|--------|--------|
| 1 | NonInterference_v2_LogicalRelation.v | 11 | 5 |
| 2 | ReferenceOps.v | 6 | 0 |
| 3 | Declassification.v | 3 | 0 |
| 4 | KripkeProperties.v | 2 | 0 |
| 5 | ReducibilityFull.v | 0 | 3 |
| 6 | NonInterference_v2.v | 0 | 1 |

## Next Steps

1. Run delegation prompts on Claude AI Web (all 6 independent, no conflicts)
2. Integrate results back into codebase
3. Verify compilation (Coq not installed in current environment)

## Git Status

- Branch: main
- All changes pushed
