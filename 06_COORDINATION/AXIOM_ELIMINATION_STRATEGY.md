# RIINA AXIOM ELIMINATION STRATEGY
## Comprehensive Analysis & Execution Plan

**Date:** 2026-01-25
**Mode:** ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

---

## 1. CURRENT STATE SUMMARY

| Category | Count |
|----------|-------|
| **Axioms** | 26 |
| **Admits** | 72 |
| **Total Proof Obligations** | 98 |

---

## 2. AXIOM INVENTORY (26 TOTAL)

### 2.1 NonInterference_v2_LogicalRelation.v (5 axioms) - TIER 1 CORE

| Line | Axiom Name | Signature | Cascade Impact |
|------|------------|-----------|----------------|
| 675 | `logical_relation_ref` | `∀ Γ Σ Δ e T l ε ρ1 ρ2 n, has_type → env_rel → rho_no_free_all → exp_rel_n` | 14 files |
| 685 | `logical_relation_deref` | `∀ Γ Σ Δ e T l ε ρ1 ρ2 n, has_type (TRef) → env_rel → exp_rel_n T` | 14 files |
| 695 | `logical_relation_assign` | `∀ Γ Σ Δ e1 e2 T l ε1 ε2 ρ1 ρ2 n, has_type (TRef) → has_type T → exp_rel_n TUnit` | 14 files |
| 708 | `logical_relation_declassify` | `∀ Γ Σ Δ e T ε p ρ1 ρ2 n, has_type (TSecret T) → exp_rel_n T` | 14 files |
| 1675 | `val_rel_n_to_val_rel` | `∀ Σ T v1 v2, value v1 → value v2 → (∃ n, val_rel_n (S n)) → val_rel` | 14 files |

### 2.2 LogicalRelationAssign_PROOF.v (14 axioms) - TIER 2

| Line | Axiom Name | Status | Notes |
|------|------------|--------|-------|
| 206 | `T_Loc` | INFRASTRUCTURE | Typing rule |
| 210 | `T_Assign` | INFRASTRUCTURE | Typing rule |
| 346 | `val_rel_n_unit` | **PROVEN** | In MaximumAxiomElimination.v |
| 351 | `val_rel_n_ref` | **PROVEN** | In MaximumAxiomElimination.v |
| 357 | `val_rel_n_ref_same_loc` | **PROVEN** | In MaximumAxiomElimination.v |
| 363 | `exp_rel_n_unfold` | NEEDED | Expression relation unfolding |
| 376 | `exp_rel_n_unit` | NEEDED | Unit expression relation |
| 380 | `exp_rel_n_base` | NEEDED | Base expression relation |
| 384 | `exp_rel_n_assign` | NEEDED | Assign expression relation |
| 390 | `val_rel_n_step_down` | **PROVEN** | In MaximumAxiomElimination.v |
| 395 | `exp_rel_n_step_down` | **PROVEN** | In MaximumAxiomElimination.v |
| 400 | `store_rel_n_step_down` | **PROVEN** | In MaximumAxiomElimination.v |
| 406 | `store_update_preserves_rel` | **PROVEN** | In MaximumAxiomElimination.v |
| 429 | `fundamental_theorem` | NEEDED | Fundamental theorem |

**IMMEDIATE WIN: 7 of 14 axioms already proven - can replace with imports**

### 2.3 LogicalRelationDeref_PROOF_FINAL.v (7 axioms) - TIER 2

| Line | Axiom Name | Category |
|------|------------|----------|
| 121 | `has_type` | Self-contained (different type system) |
| 321 | `store_contains_values` | Store property |
| 324 | `store_rel_same_domain` | Store relation |
| 330 | `store_well_typed` | Store typing |
| 338 | `fundamental_lemma` | Fundamental theorem |
| 345 | `fundamental_ref_produces_typed_loc` | Ref semantics |
| 358 | `deref_eval_structure` | Deref semantics |

---

## 3. ADMIT INVENTORY (72 TOTAL)

### 3.1 Critical Path Admits (Blocking)

| File | Admits | Blocks | Priority |
|------|--------|--------|----------|
| ReducibilityFull.v | 2 | NonInterference_v2.v | **P0** |
| NonInterference_v2.v | 3 | NonInterference_v2_LogicalRelation.v | **P0** |
| NonInterference_v2_LogicalRelation.v | 12 | Final integration | **P1** |

### 3.2 ReducibilityFull.v Admits (ROOT BLOCKERS)

**Admit 1 (Line 469): `subst_subst_env_commute`**
```coq
Lemma subst_subst_env_commute : forall ρ x v e,
  [x := v] (subst_env (extend_rho ρ x (EVar x)) e) =
  subst_env (extend_rho ρ x v) e.
```
- **Proof Strategy:** Add `closed_rho ρ` premise, prove by structural induction on `e`
- **Key insight:** For `EVar y` where `y ≠ x`, need `ρ y` closed so `[x := v] (ρ y) = ρ y`
- **Infrastructure:** `subst_not_free_in` already proven in same file

**Admit 2 (Line 739): `fundamental_reducibility`**
```coq
Lemma fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  Reducible T (subst_env ρ e).
```
- **Missing cases:** App beta reduction, Deref store_wf
- **Proof Strategy:**
  - App: Use `SN_app`, beta reduction semantics
  - Deref: Use `store_wf` premise for values in store

### 3.3 NonInterference_v2.v Admits

| Line | Context | Blocks |
|------|---------|--------|
| 1376 | `val_rel_at_type_step_up_with_IH` (TFn case) | `combined_step_up_all` |
| 2067 | `combined_step_up_all` (store_rel step-up) | `val_rel_n_step_up` |
| 2437 | `val_rel_at_type_TFn_step_0_bridge` | Final TFn proof |

---

## 4. DEPENDENCY GRAPH

```
ROOT BLOCKERS (Fix First):
═══════════════════════════════════════════════════════════════
ReducibilityFull.v
├── Admit 1: subst_subst_env_commute
│   └── Proof: Add closed_rho, structural induction
└── Admit 2: fundamental_reducibility
    └── Proof: Complete App beta, Deref store_wf cases
═══════════════════════════════════════════════════════════════
                              │
                              ▼
TIER 1 - NonInterference_v2.v (Unlocked by ReducibilityFull)
═══════════════════════════════════════════════════════════════
├── Admit 1376: val_rel_at_type_step_up_with_IH (TFn)
├── Admit 2067: combined_step_up_all
└── Admit 2437: val_rel_at_type_TFn_step_0_bridge
    └── Depends on: well_typed_SN from ReducibilityFull
═══════════════════════════════════════════════════════════════
                              │
                              ▼
TIER 2 - NonInterference_v2_LogicalRelation.v
═══════════════════════════════════════════════════════════════
├── 5 AXIOMS (logical_relation_ref/deref/assign/declassify, val_rel_n_to_val_rel)
├── 12 ADMITS (various supporting lemmas)
└── CASCADES TO: 14 dependent files
═══════════════════════════════════════════════════════════════
                              │
                              ▼
TIER 3 - Infrastructure Axioms (Can be replaced with imports)
═══════════════════════════════════════════════════════════════
├── LogicalRelationAssign_PROOF.v: 7 axioms → MaximumAxiomElimination.v
└── LogicalRelationDeref_PROOF_FINAL.v: 7 axioms (self-contained)
═══════════════════════════════════════════════════════════════
```

---

## 5. EXECUTION PHASES

### PHASE 0: IMMEDIATE WINS (No Dependencies)
**Objective:** Replace 7 axioms with existing proofs

1. **LogicalRelationAssign_PROOF.v** - Replace these axioms with imports:
   - `val_rel_n_unit` → Import from MaximumAxiomElimination
   - `val_rel_n_ref` → Import from MaximumAxiomElimination
   - `val_rel_n_ref_same_loc` → Import from MaximumAxiomElimination
   - `val_rel_n_step_down` → Import from MaximumAxiomElimination
   - `exp_rel_n_step_down` → Import from MaximumAxiomElimination
   - `store_rel_n_step_down` → Import from MaximumAxiomElimination
   - `store_update_preserves_rel` → Import from MaximumAxiomElimination

**Impact:** 26 → 19 axioms (7 eliminated)

### PHASE 1: ROOT BLOCKERS (ReducibilityFull.v)
**Objective:** Fix 2 admits to unlock NonInterference_v2.v

**Task 1.1: Prove `subst_subst_env_commute`**
- Add `closed_rho ρ` premise
- Structural induction on `e`
- Use existing `subst_not_free_in` lemma

**Task 1.2: Complete `fundamental_reducibility`**
- App case: Beta reduction with SN preservation
- Deref case: Store well-formedness invariant

**Impact:** Unlocks 3 admits in NonInterference_v2.v

### PHASE 2: TIER 1 UNLOCKING (NonInterference_v2.v)
**Objective:** Fix 3 admits using well_typed_SN from Phase 1

**Task 2.1:** Complete `val_rel_at_type_step_up_with_IH` (TFn case)
**Task 2.2:** Complete `combined_step_up_all`
**Task 2.3:** Prove `val_rel_at_type_TFn_step_0_bridge`

**Impact:** Unlocks 5 core axioms in NonInterference_v2_LogicalRelation.v

### PHASE 3: CORE AXIOMS (NonInterference_v2_LogicalRelation.v)
**Objective:** Prove 5 core axioms

**Task 3.1:** `logical_relation_ref` - Reference creation
**Task 3.2:** `logical_relation_deref` - Dereference
**Task 3.3:** `logical_relation_assign` - Assignment
**Task 3.4:** `logical_relation_declassify` - Declassification
**Task 3.5:** `val_rel_n_to_val_rel` - Step-indexed to limit

**Impact:** Cascades to 14 dependent files

### PHASE 4: REMAINING ADMITS (57 total)
Complete remaining admits across all files using established infrastructure.

---

## 6. PARALLEL EXECUTION STRATEGY

### Track A (Can run in parallel):
- Phase 0: Replace 7 axioms with imports
- Phase 1.1: Prove subst_subst_env_commute

### Track B (Sequential, depends on Track A):
- Phase 1.2 → Phase 2 → Phase 3 → Phase 4

---

## 7. VERIFICATION CHECKPOINTS

After each phase:
1. `make clean && make` - Full compilation
2. `grep -c "Admitted\." file.v` - Admit count
3. `grep -c "^Axiom " file.v` - Axiom count
4. `coqchk RIINA.properties.file` - Proof verification

---

## 8. SUCCESS CRITERIA

| Phase | Axioms | Admits | Notes |
|-------|--------|--------|-------|
| Initial | 26 | 72 | Current state |
| Phase 0 | 19 | 72 | -7 axioms (imports) |
| Phase 1 | 19 | 70 | -2 admits (ReducibilityFull) |
| Phase 2 | 19 | 67 | -3 admits (NonInterference_v2) |
| Phase 3 | 14 | 55 | -5 axioms, -12 admits |
| Phase 4 | 14 | 0 | All admits eliminated |
| Final | 0 | 0 | **TRACK A COMPLETE** |

---

*"QED Eternum."*
