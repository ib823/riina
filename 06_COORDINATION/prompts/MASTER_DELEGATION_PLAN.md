# MASTER DELEGATION PLAN: Complete Axiom & Admit Elimination

## Overview

| Category | Count | Target |
|----------|-------|--------|
| **Core Axioms** | 70 | → 0 (eliminate all) |
| **Total Admits** | 63 | → 0 (prove all) |
| **Industry Axioms** | 75 | KEEP (justified) |
| **TOTAL WORK** | 133 items | |

---

## PART 1: AXIOM ELIMINATION (70 total)

### Module Group 1: LogicalRelation Modules (62 axioms)

These 4 modules have local Parameter declarations that duplicate definitions from the main codebase.

| File | Axioms | Strategy |
|------|--------|----------|
| `LogicalRelationDeclassify_PROOF_REFINED.v` | 27 | Unify with NI_v2 |
| `LogicalRelationAssign_PROOF.v` | 18 | Unify with NI_v2 |
| `LogicalRelationDeclassify_PROOF.v` | 10 | Merge or deprecate |
| `LogicalRelationDeref_PROOF_FINAL.v` | 7 | Unify with NI_v2 |

**Delegation Package: PKG-H (Module Unification)**
- Analyze overlap between modules
- Extract proven lemmas into main codebase
- Eliminate duplicate Parameters

### Module Group 2: Core Infrastructure (8 axioms)

| File | Axioms | Description |
|------|--------|-------------|
| `NonInterference_v2_LogicalRelation.v` | 5 | Core relation axioms |
| `NonInterference_v2.v` | 1 | observer Parameter |
| `LogicalRelationRef_PROOF.v` | 1 | store_ty_fresh_loc_none |
| `LogicalRelationDeclassify_v2.v` | 1 | Policy axiom |

**Delegation Package: PKG-I (Core Axiom Audit)**
- Evaluate each axiom: provable, justified, or redundant
- Prove the provable ones
- Document justification for necessary ones

---

## PART 2: ADMIT ELIMINATION (63 total)

### Tier 1: High-Impact Files (27 admits)

| File | Admits | Package |
|------|--------|---------|
| `AxiomEliminationVerified.v` | 15 | **PKG-F** |
| `MasterTheorem.v` | 7 | **PKG-G** |
| `NonInterferenceZero.v` | 5 | **PKG-J** |

### Tier 2: Kripke & Monotonicity (11 admits)

| File | Admits | Package |
|------|--------|---------|
| `KripkeMutual.v` | 3 | **PKG-K** |
| `NonInterferenceKripke.v` | 3 | **PKG-K** |
| `KripkeProperties.v` | 2 | **PKG-K** |
| `CumulativeRelation.v` | 2 | **PKG-K** |
| `CumulativeMonotone.v` | 1 | **PKG-K** |

### Tier 3: Reference & Store Operations (7 admits)

| File | Admits | Package |
|------|--------|---------|
| `ReferenceOps.v` | 3 | **PKG-L** |
| `RelationBridge.v` | 3 | **PKG-L** |
| `LogicalRelationRef_PROOF.v` | 1 | **PKG-L** |

### Tier 4: Type Conversion & Declassification (12 admits)

| File | Admits | Package |
|------|--------|---------|
| `TypedConversion.v` | 2 | **PKG-M** |
| `ApplicationComplete.v` | 2 | **PKG-M** |
| `LogicalRelationDeclassify_v2.v` | 2 | **PKG-M** |
| `LogicalRelationDeclassify_PROOF_REFINED.v` | 2 | **PKG-M** |
| `LogicalRelationDeclassify_PROOF.v` | 2 | **PKG-M** |
| `Declassification.v` | 1 | **PKG-M** |
| `NonInterference_v2_LogicalRelation.v` | 1 | **PKG-M** |

### Tier 5: Termination & Misc (6 admits)

| File | Admits | Package |
|------|--------|---------|
| `ReducibilityFull.v` | 2 | **PKG-N** |
| `NonInterference_v2.v` | 2 | **PKG-N** |
| `SN_Closure.v` | 1 | **PKG-N** |
| `ValRelStepLimit_PROOF.v` | 1 | **PKG-N** |

---

## DELEGATION PACKAGE SUMMARY

| Package | Focus | Items | Priority |
|---------|-------|-------|----------|
| **PKG-F** | AxiomEliminationVerified admits | 15 | P0 |
| **PKG-G** | MasterTheorem composition | 7 | P0 |
| **PKG-H** | Module unification (62 axioms) | 62 | P0 |
| **PKG-I** | Core axiom audit (8 axioms) | 8 | P1 |
| **PKG-J** | NonInterferenceZero admits | 5 | P1 |
| **PKG-K** | Kripke & monotonicity admits | 11 | P1 |
| **PKG-L** | Reference ops admits | 7 | P2 |
| **PKG-M** | Type/Declassify admits | 12 | P2 |
| **PKG-N** | Termination & misc admits | 6 | P2 |
| **TOTAL** | | **133** | |

---

## PARALLELIZATION STRATEGY

### Wave 1 (Can Run Simultaneously)
- PKG-F: AxiomEliminationVerified (15 admits)
- PKG-G: MasterTheorem (7 admits)
- PKG-H: Module unification analysis (62 axioms)
- PKG-I: Core axiom audit (8 axioms)

**Rationale:** These are independent - different files, no dependencies.

### Wave 2 (After Wave 1)
- PKG-J: NonInterferenceZero (depends on PKG-F patterns)
- PKG-K: Kripke admits (may use PKG-H unification)

### Wave 3 (After Wave 2)
- PKG-L: Reference ops (uses patterns from PKG-K)
- PKG-M: Type/Declassify (uses PKG-H unification)
- PKG-N: Termination (uses PKG-F/G patterns)

---

## SUCCESS CRITERIA

| Milestone | Axioms | Admits |
|-----------|--------|--------|
| **Current** | 70 | 63 |
| **After Wave 1** | ~20 | ~40 |
| **After Wave 2** | ~10 | ~20 |
| **After Wave 3** | 0* | 0 |

*Only justified axioms (observer, compliance) remain.

---

## PROMPT TEMPLATE

Each package prompt should include:

1. **Context**: What file(s), what the admits/axioms are about
2. **Definitions**: Key types, relations, lemmas needed
3. **Strategy**: Recommended proof approach
4. **Dependencies**: What other lemmas are available
5. **Expected Output**: Concrete deliverables (Qed proofs, analysis docs)
6. **Build Instructions**: How to verify the work

---

## NEXT ACTION

Create prompt files for:
- [x] PKG-F (AxiomEliminationVerified)
- [x] PKG-G (MasterTheorem)
- [x] PKG-H (Module unification)
- [ ] PKG-I (Core axiom audit)
- [ ] PKG-J (NonInterferenceZero)
- [ ] PKG-K (Kripke & monotonicity)
- [ ] PKG-L (Reference ops)
- [ ] PKG-M (Type/Declassify)
- [ ] PKG-N (Termination & misc)
