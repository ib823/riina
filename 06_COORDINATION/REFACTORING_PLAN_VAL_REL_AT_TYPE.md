# Refactoring Plan: val_rel_at_type TFn Preconditions

## Status: ✅ COMPLETED
## Created: 2026-01-24 (Session 42)
## Completed: 2026-01-24 (Session 42 continued)

### Result Summary
- **NonInterference_v2.v admits:** 11 → 1 (10 eliminated!)
- **Remaining admit:** Fundamental Theorem n=0 (line 1541) - requires compatibility lemmas
- **All preservation admits eliminated** by propagating store_wf postconditions through TFn

---

## Problem Summary

The 11 remaining admits in NonInterference_v2.v are all preservation-related.
They occur when trying to step-up `store_rel_n` after function application.

**Root Cause:** The TFn case of `val_rel_at_type` does not require `store_wf`
or `stores_agree_low_fo` for input stores, so we cannot use the preservation
theorem to establish these properties for output stores.

## Current TFn Definition (Lines 339-351)

```coq
| TFn T1 T2 eff =>
    forall Σ', store_ty_extends Σ Σ' ->
      forall x y,
        value x -> value y -> closed_expr x -> closed_expr y ->
        val_rel_lower Σ' T1 x y ->
        forall st1 st2 ctx,
          store_rel_pred Σ' st1 st2 ->  (* ONLY store_rel! *)
          exists v1' v2' st1' st2' ctx' Σ'',
            store_ty_extends Σ' Σ'' /\
            (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
            (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
            val_rel_lower Σ'' T2 v1' v2' /\
            store_rel_lower Σ'' st1' st2'
```

## Required Changes

### New TFn Definition (Proposed)

```coq
| TFn T1 T2 eff =>
    forall Σ', store_ty_extends Σ Σ' ->
      forall x y,
        value x -> value y -> closed_expr x -> closed_expr y ->
        val_rel_lower Σ' T1 x y ->
        forall st1 st2 ctx,
          store_rel_pred Σ' st1 st2 ->
          store_wf Σ' st1 ->                    (* ADD: precondition *)
          store_wf Σ' st2 ->                    (* ADD: precondition *)
          stores_agree_low_fo Σ' st1 st2 ->     (* ADD: precondition *)
          exists v1' v2' st1' st2' ctx' Σ'',
            store_ty_extends Σ' Σ'' /\
            (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
            (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
            val_rel_lower Σ'' T2 v1' v2' /\
            store_rel_lower Σ'' st1' st2' /\
            store_wf Σ'' st1' /\                (* ADD: postcondition *)
            store_wf Σ'' st2' /\                (* ADD: postcondition *)
            stores_agree_low_fo Σ'' st1' st2'   (* ADD: postcondition *)
```

## Impact Analysis

### Files Affected

1. **NonInterference_v2.v** (Primary)
   - `val_rel_at_type` definition (lines 321-359)
   - `val_rel_at_type_step_up_with_IH` proof (lines 1261-1359)
   - `combined_step_up_all` proof (lines 1454-1982)
   - Any other proofs using TFn case

2. **NonInterference_v2_LogicalRelation.v** (If exists)
   - May have compatibility lemmas

### Proof Obligations Added

When establishing val_rel_at_type for TFn (i.e., proving functions are related):
1. Must prove: evaluation preserves store_wf (use multi_step_preservation)
2. Must prove: evaluation preserves stores_agree_low_fo (need new lemma)

When using val_rel_at_type for TFn (i.e., applying related functions):
1. Must provide: store_wf for input stores
2. Must provide: stores_agree_low_fo for input stores
3. Gain: store_wf for output stores
4. Gain: stores_agree_low_fo for output stores

## Implementation Steps

### Phase 1: Definition Update
1. Modify TFn case in val_rel_at_type to add preconditions
2. Add postconditions to the existential

### Phase 2: Prove New Preservation Lemma
```coq
Lemma stores_agree_low_fo_preserved : forall cfg cfg',
  cfg -->* cfg' ->
  forall e e' st st' ctx ctx' Σ Σ',
    cfg = (e, st, ctx) ->
    cfg' = (e', st', ctx') ->
    store_wf Σ st ->
    stores_agree_low_fo Σ st st ->  (* Both stores same initially *)
    store_ty_extends Σ Σ' ->
    store_wf Σ' st' ->
    stores_agree_low_fo Σ' st' st'.
```

Actually, for NI proof we have TWO evaluations from potentially DIFFERENT stores.
Need more careful analysis of what preservation lemma is needed.

### Phase 3: Update Proofs

1. **val_rel_at_type_step_up_with_IH**:
   - Now has access to store_wf and stores_agree_low_fo as hypotheses
   - Can use multi_step_preservation for output stores
   - Eliminates admits at lines 1326, 1585-1593

2. **combined_step_up_all**:
   - Eliminates admits at lines 1654, 1725, 1800, 1872

3. **Top-level non-interference theorem**:
   - Must ensure initial stores satisfy store_wf and stores_agree_low_fo
   - This should be provable from typing context

## Admits Affected

| Line | Current Admit | Fix After Refactoring |
|------|---------------|----------------------|
| 1326 | store_rel step-up in TFn | Use preservation + new postcondition |
| 1585 | store_wf Σ'' st1' | Use multi_step_preservation |
| 1587 | store_wf Σ'' st2' | Use multi_step_preservation |
| 1589 | store_has_values st1' | Derive from store_wf |
| 1591 | store_has_values st2' | Derive from store_wf |
| 1593 | stores_agree_low_fo Σ'' st1' st2' | Use new preservation lemma |
| 1654 | store_rel step-up (TProd) | Propagate from TFn fix |
| 1725 | store_rel step-up (TSum) | Propagate from TFn fix |
| 1800 | store_rel step-up (nested) | Propagate from TFn fix |
| 1872 | store_rel step-up (nested) | Propagate from TFn fix |

**Note:** Line 1524 (Fundamental Theorem n=0) is separate and not fixed by this refactoring.

## Estimated Effort

- Definition change: 30 minutes
- Preservation lemma for stores_agree_low_fo: 2-4 hours
- Updating proofs: 4-6 hours
- Testing and debugging: 2-4 hours

Total: 8-14 hours of focused work

## Alternative Approaches

1. **Weaker postcondition**: Only add store_wf, not stores_agree_low_fo
   - Pro: Simpler refactoring
   - Con: May not eliminate all admits

2. **Thread preconditions through combined_step_up**:
   - Add store_wf and stores_agree_low_fo as global preconditions
   - Pro: Smaller definition change
   - Con: More complex theorem statement, may complicate usage

3. **Accept admits as justified**:
   - Document that they require preservation properties
   - Pro: No code changes
   - Con: Proofs remain incomplete

## Recommendation

Proceed with the full refactoring (adding preconditions and postconditions to TFn).
This is the cleanest design and will eliminate 10 of the 11 remaining admits.

The Fundamental Theorem n=0 admit (line 1524) requires separate treatment
using compatibility lemmas for each typing rule.
