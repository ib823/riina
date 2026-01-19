# Integration Guide: Verified Delegation Proofs → Axiom Elimination

## Overview

This document maps the 20 verified lemmas from Claude AI delegation to the axioms
they can help eliminate in NonInterference.v.

**Status:** Ready for integration work
**Date:** 2026-01-19

---

## Verified Proof Files (All ZERO Axioms)

| File | Lemmas | Verification |
|------|--------|--------------|
| `RIINA_exp_rel_step1_fst_PROOF.v` | 1 | coqc + coqchk PASSED |
| `RIINA_exp_rel_step1_snd_PROOF.v` | 1 | coqc + coqchk PASSED |
| `RIINA_extraction_lemmas_tasks_3_5.v` | 9 | coqc + coqchk PASSED |
| `RIINA_exp_rel_step1_case_PROOF.v` | 1 | coqc + coqchk PASSED |
| `RIINA_reference_operations_PROOF.v` | 8 | coqc + coqchk PASSED |

---

## Axiom → Verified Proof Mapping

### Category A: Step-1 Termination Axioms (7 axioms)

| Axiom in NonInterference.v | Verified Proof | Integration Path |
|---------------------------|----------------|------------------|
| `exp_rel_step1_fst` (line 1294) | `RIINA_exp_rel_step1_fst_PROOF.v` | Direct replacement with val_rel_n_base |
| `exp_rel_step1_snd` (line 1306) | `RIINA_exp_rel_step1_snd_PROOF.v` | Direct replacement with val_rel_n_base |
| `exp_rel_step1_case` (line 1318) | `RIINA_exp_rel_step1_case_PROOF.v` | Direct replacement with val_rel_n_base |
| `exp_rel_step1_if` (line 1330) | Already proven in NonInterference_v2.v | Copy from v2 |
| `exp_rel_step1_let` (line 1342) | Already proven in NonInterference_v2.v | Copy from v2 |
| `exp_rel_step1_handle` (line 1354) | Already proven in NonInterference_v2.v | Copy from v2 |
| `exp_rel_step1_app` (line 1366) | Already proven in NonInterference_v2.v | Copy from v2 (with typing premises) |

### Category B: Reference Operations (3 axioms)

| Axiom in NonInterference.v | Verified Proof | Integration Path |
|---------------------------|----------------|------------------|
| `logical_relation_ref` (line 2105) | `exp_rel_step1_ref` in ref ops proof | Adapt to full logical_relation |
| `logical_relation_deref` (line 2115) | `exp_rel_step1_deref` in ref ops proof | Adapt to full logical_relation |
| `logical_relation_assign` (line 2125) | `exp_rel_step1_assign` in ref ops proof | Adapt to full logical_relation |

**Note:** The verified proofs handle single-step behavior. Full logical_relation
requires multi-step evaluation decomposition.

### Category C: Step-Up Axioms (3 axioms)

| Axiom in NonInterference.v | Verified Proof | Integration Path |
|---------------------------|----------------|------------------|
| `val_rel_n_step_up` (line 1548) | PENDING: val_rel_n_step_up_fo | Handles FO types only |
| `store_rel_n_step_up` (line 1554) | Follows from val_rel_n_step_up | After val_rel_n_step_up |
| `val_rel_n_lam_cumulative` (line 1564) | Special case of step-up | After val_rel_n_step_up |

### Category D: Higher-Order (2 axioms)

| Axiom in NonInterference.v | Status | Notes |
|---------------------------|--------|-------|
| `val_rel_n_to_val_rel` (line 1269) | Needs step-up | After Category C |
| `val_rel_at_type_to_val_rel_ho` (line 1573) | Needs SN for TFn | Complex |

### Category E: Remaining (2 axioms)

| Axiom in NonInterference.v | Status | Notes |
|---------------------------|--------|-------|
| `tapp_step0_complete` (line 1386) | Degenerate case | Needs separate analysis |
| `logical_relation_declassify` (line 2138) | Policy-dependent | By design |

---

## Extraction Lemmas Available

From `RIINA_extraction_lemmas_tasks_3_5.v`:

```coq
(* Core extraction lemmas *)
val_rel_n_base_int    : val_rel_n_base Σ TInt v1 v2 → ∃i, v1 = EInt i ∧ v2 = EInt i
val_rel_n_base_unit   : val_rel_n_base Σ TUnit v1 v2 → v1 = EUnit ∧ v2 = EUnit
val_rel_n_base_ref    : val_rel_n_base Σ (TRef T sl) v1 v2 → ∃l, v1 = ELoc l ∧ v2 = ELoc l
val_rel_n_base_bool   : val_rel_n_base Σ TBool v1 v2 → ∃b, v1 = EBool b ∧ v2 = EBool b
val_rel_n_base_string : val_rel_n_base Σ TString v1 v2 → ∃s, v1 = EString s ∧ v2 = EString s

(* Structure extraction *)
val_rel_n_base_value  : val_rel_n_base Σ T v1 v2 → value v1 ∧ value v2
val_rel_n_base_closed : val_rel_n_base Σ T v1 v2 → closed_expr v1 ∧ closed_expr v2
val_rel_n_base_prod_fo: val_rel_n_base Σ (TProd T1 T2) v1 v2 → ∃a1 b1 a2 b2, ...
val_rel_n_base_sum_fo : val_rel_n_base Σ (TSum T1 T2) v1 v2 → (∃x1 x2, ...) ∨ (∃y1 y2, ...)
```

---

## Reference Operations Helper Lemmas

From `RIINA_reference_operations_PROOF.v`:

```coq
(* Store relation helpers *)
store_rel_fresh_eq           : store_rel_n_base Σ st1 st2 → fresh_loc st1 = fresh_loc st2
store_extend_size            : store_size (store_extend v st) = S (store_size st)
store_update_preserves_size  : (∃v', In (l, v') st) → store_size (store_update l v st) = store_size st
store_lookup_in              : store_lookup l st = Some v → In (l, v) st
```

---

## Integration Strategy

### Phase 1: Direct Axiom Replacement (Easy)
1. Replace `exp_rel_step1_fst/snd/case` axioms with proven lemmas
2. Adapt signatures if needed (add FO type premises)

### Phase 2: Copy from v2 (Medium)
1. Import proven lemmas from NonInterference_v2.v
2. Replace `exp_rel_step1_if/let/handle/app` axioms

### Phase 3: Reference Operations (Medium)
1. Build multi-step decomposition infrastructure
2. Use verified single-step proofs as building blocks

### Phase 4: Step-Up (Hard)
1. Await val_rel_n_step_up_fo verification
2. Prove store_rel_n_step_up as corollary
3. Handle TFn case separately (requires SN)

---

## Key Insight: val_rel_n_base vs val_rel_n

The verified proofs use `val_rel_n_base` which is:
```coq
Definition val_rel_n_base Σ T v1 v2 :=
  value v1 ∧ value v2 ∧ closed_expr v1 ∧ closed_expr v2 ∧
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).
```

This is MORE STRUCTURED than `val_rel_n 0` (which equals True) and provides:
- Guaranteed value/closed properties
- First-order type structural information

**Integration Benefit:** Using val_rel_n_base eliminates the "n=0 gives no info" problem
for first-order types.

---

## Files Requiring Update

1. `NonInterference.v` - Main axiom file (17 axioms)
2. `MasterTheorem.v` - Secondary file (1 axiom)
3. `ReferenceOps.v` - Higher-level ref ops proofs

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST*
*Generated: 2026-01-19*
