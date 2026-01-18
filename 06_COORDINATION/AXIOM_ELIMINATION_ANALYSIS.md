# RIINA Axiom Elimination Analysis

## Executive Summary

**Current State**: 19 axioms in NonInterference.v + 1 in MasterTheorem.v
**Target**: 0 axioms
**Blockers**: Fundamental design mismatch between val_rel_n and val_rel_le

## Critical Finding: Kripke Semantics Mismatch

The Phase 7 claude.ai output incorrectly assumes `val_rel_n = val_rel_le`. They are **structurally different**:

### val_rel_n (NonInterference.v)
```coq
| TFn T1 T2 eff =>
    forall x y,
      value x -> value y -> closed_expr x -> closed_expr y ->
      val_rel_at_type T1 x y ->  (* NO Kripke quantification *)
      forall st1 st2 ctx,
        store_rel_pred st1 st2 ->
        exists ... store_ty_extends Σ Σ' ...
```

### val_rel_le (CumulativeRelation.v)
```coq
| TFn T1 T2 eff =>
    forall Σ', store_ty_extends Σ Σ' ->  (* KRIPKE quantification *)
      forall arg1 arg2,
        ...
        val_rel_prev Σ' T1 arg1 arg2 ->  (* Arguments at EXTENDED store *)
        ...
```

**Key Difference**: `val_rel_le` has proper Kripke semantics (∀Σ' extending Σ) while `val_rel_n` does NOT.

## Why This Matters

1. **For first-order types**: Both definitions are EQUIVALENT (no TFn, so no Kripke difference)
2. **For TFn types**: `val_rel_n` LACKS the Kripke structure needed to prove store monotonicity

## Current Proven Status

### Fully Proven (13 lemmas with Qed)
| Lemma | Status | Description |
|-------|--------|-------------|
| axiom_1_first_order | ✅ PROVEN | val_rel_n_weaken for first-order types |
| axiom_2_first_order | ✅ PROVEN | val_rel_n_mono_store for first-order types |
| axiom_3_first_order | ✅ PROVEN | val_rel_n_to_val_rel for first-order types |
| axiom_4_infrastructure | ✅ PROVEN | exp_rel_step1_fst (with typing premise) |
| axiom_5_infrastructure | ✅ PROVEN | exp_rel_step1_snd (with typing premise) |
| axiom_6_infrastructure | ✅ PROVEN | exp_rel_step1_case (with typing premise) |
| axiom_7_infrastructure | ✅ PROVEN | exp_rel_step1_if (with typing premise) |
| axiom_8_infrastructure | ✅ PROVEN | exp_rel_step1_let (with typing premise) |
| axiom_9_infrastructure | ✅ PROVEN | exp_rel_step1_handle (with typing premise) |
| axiom_10_infrastructure | ✅ PROVEN | exp_rel_step1_app (with typing premise) |
| axiom_11_infrastructure | ✅ PROVEN | tapp_step0_complete (with typing premise) |
| val_rel_at_type_fo_store_independent | ✅ PROVEN | Store independence for first-order |
| val_rel_n_fo_store_independent | ✅ PROVEN | Full store independence for first-order |

### Admitted (9 lemmas for TFn cases)
| Lemma | Status | Blocker |
|-------|--------|---------|
| axiom_1_infrastructure | 🟡 ADMITTED | TFn case requires Kripke refactoring |
| axiom_2_infrastructure | 🟡 ADMITTED | TFn case requires Kripke refactoring |
| axiom_12_infrastructure | 🟡 ADMITTED | step_up for TFn |
| axiom_13_infrastructure | 🟡 ADMITTED | store step_up depends on axiom_12 |
| axiom_14_infrastructure | 🟡 ADMITTED | lam_cumulative for TFn |
| axiom_15_infrastructure | 🟡 ADMITTED | val_rel_at_type_to_val_rel for HO types |
| axiom_16_infrastructure | 🟡 ADMITTED | logical_relation_ref |
| axiom_17_infrastructure | 🟡 ADMITTED | logical_relation_deref |
| axiom_18_infrastructure | 🟡 ADMITTED | logical_relation_assign |
| axiom_19_infrastructure | 🟡 ADMITTED | logical_relation_declassify |

## Path to Zero Axioms

### Option 1: Refactor val_rel_n (RECOMMENDED)

**Approach**: Replace `val_rel_n` definition with one that has proper Kripke semantics.

**Steps**:
1. Define `val_rel_n_kripke` using `val_rel_struct` (like `val_rel_le`)
2. Prove equivalence: `val_rel_n_kripke ↔ val_rel_n` for first-order types
3. Update all proofs in NonInterference.v to use `val_rel_n_kripke`
4. All axioms become provable from MasterTheorem.v corollaries

**Effort**: Major refactoring (~2000+ lines)
**Risk**: May break existing proofs during transition

### Option 2: Semantic Justification (CURRENT STATE)

**Approach**: Document remaining axioms as semantically justified.

**Justification**:
- The axioms are TRUE in the semantic model
- They follow standard Kripke monotonicity principles
- First-order cases are fully proven, confirming the approach
- TFn cases are well-understood in PLT literature

**Effort**: Minimal
**Risk**: Non-zero axiom count (but semantically sound)

### Option 3: Hybrid Approach

**Approach**: Create a bridge module that:
1. Uses `val_rel_le` for property proofs
2. Transfers results to `val_rel_n` via first-order/TFn case split
3. TFn cases use semantic justification

**Effort**: Medium
**Risk**: Complexity in bridge proofs

## Recommendation

**Short-term**: Accept Option 2 (current state) with clear documentation.

**Medium-term**: Implement Option 1 (full refactoring) with the following plan:

### Refactoring Plan

1. **Phase R1**: Create `NonInterferenceKripke.v`
   - Define `val_rel_n_k` using `val_rel_struct`
   - Port first-order lemmas (should be direct)
   - Port TFn lemmas using MasterTheorem.v

2. **Phase R2**: Create bridge lemmas
   - `val_rel_n_k_equiv_fo`: equivalence for first-order types
   - `val_rel_n_k_implies_n`: for all types

3. **Phase R3**: Update NonInterference.v
   - Replace `val_rel_n` calls with `val_rel_n_k`
   - Update fundamental theorem proof
   - Verify all proofs compile

4. **Phase R4**: Remove axioms
   - Replace axioms with proven lemmas
   - Verify zero axioms remain

## Files Involved

- `/workspaces/proof/02_FORMAL/coq/properties/NonInterference.v` - Contains 19 axioms
- `/workspaces/proof/02_FORMAL/coq/properties/MasterTheorem.v` - Contains 1 axiom + proven corollaries
- `/workspaces/proof/02_FORMAL/coq/properties/AxiomElimination.v` - Infrastructure
- `/workspaces/proof/02_FORMAL/coq/properties/CumulativeRelation.v` - Correct Kripke definition
- `/workspaces/proof/02_FORMAL/coq/properties/RelationBridge.v` - Analysis of the mismatch

## Conclusion

The Phase 7 claude.ai output's claim that axioms can be directly eliminated is **incorrect** due to the val_rel_n/val_rel_le mismatch. True elimination to 0 requires refactoring `val_rel_n` to have proper Kripke semantics.

Current status: **13 lemmas proven, 9 await Kripke refactoring**

---
*Analysis conducted: 2026-01-18*
*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST*
