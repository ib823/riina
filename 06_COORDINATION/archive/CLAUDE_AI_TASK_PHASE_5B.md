# Claude.ai Research Task - Phase 5B: TFn Store-Weakening Research

## Context

We are completing the `master_theorem` in `/workspaces/proof/02_FORMAL/coq/properties/MasterTheorem.v`. Property D (Store Weakening) for TFn is admitted and needs a proof strategy.

## The Problem

**Store Weakening for TFn**: Given `store_ty_extends Σ Σ'`, prove:
```
val_rel_le n Σ' (TFn T1 T2 eff) v1 v2 -> val_rel_le n Σ (TFn T1 T2 eff) v1 v2
```

This is HARD because TFn uses **Kripke quantification** in the structural part:
```coq
val_rel_struct R Σ (TFn T1 T2 eff) v1 v2 :=
  ... /\
  forall Σ' (Hext : store_ty_extends Σ Σ') arg1 arg2,
    ...
    R Σ' T1 arg1 arg2 ->    (* args at extended store *)
    ...
      exists Σ'', ... /\
        R Σ'' T2 res1 res2   (* results at further extended store *)
```

## The Challenge

When we weaken from Σ' to Σ (where Σ ⊆ Σ'):
- **Hypothesis**: `forall Σ'' (Hext : store_ty_extends Σ' Σ'') ...` (extensions of Σ')
- **Goal**: `forall Σ'' (Hext : store_ty_extends Σ Σ'') ...` (extensions of Σ)

The goal quantifies over MORE stores (Σ has fewer locations, so more things extend it).

## Available Resources

### IH from combined_properties for T1, T2:
```coq
StoreStr1 : forall n Σ Σ' v1 v2, store_ty_extends Σ Σ' ->
            val_rel_le n Σ T1 v1 v2 -> val_rel_le n Σ' T1 v1 v2
StoreWeak1 : forall n Σ Σ' v1 v2, store_ty_extends Σ Σ' ->
             val_rel_le n Σ' T1 v1 v2 -> val_rel_le n Σ T1 v1 v2
StoreStr2, StoreWeak2 : (same for T2)
```

### Key Insight Needed

For any Σ'' extending Σ, there are two cases:
1. **Σ'' also extends Σ'**: Then we can use the hypothesis directly
2. **Σ'' does NOT extend Σ'**: We need to construct a "common extension"

## Questions to Answer

1. **Is there a common extension?** Given Σ ⊆ Σ' and Σ ⊆ Σ'', can we find Σ''' with Σ' ⊆ Σ''' and Σ'' ⊆ Σ'''?

2. **Do we need it?** Maybe the quantification structure allows a simpler argument.

3. **Can we use monotonicity?** If the relation is monotonic in the store, weakening might follow.

4. **Semantic consideration**: What does store weakening MEAN for functions?
   - With more locations (Σ'), functions must work for more stores
   - With fewer locations (Σ), functions can be more selective
   - This suggests weakening might be straightforward?

## Current State in MasterTheorem.v

Line 717-722:
```coq
+ (* Property D: Store Weakening for TFn *)
  intros n Σ Σ' v1 v2 Hext Hrel.
  (* TFn uses Kripke quantification over store extensions *)
  (* Weakening: Σ ⊆ Σ' means Σ has fewer constraints *)
  (* This is the harder direction *)
  admit.
```

## Your Task

1. **Analyze** the store_ty_extends and Kripke quantification structure
2. **Determine** if a direct proof is possible using IH
3. **Provide** either:
   - A complete proof strategy with Coq tactics, OR
   - An explanation of why additional infrastructure is needed

## store_ty_extends Definition (Reference)

```coq
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T, lookup_store_ty Σ l = Some T -> lookup_store_ty Σ' l = Some T.
```

This means Σ' has at least all the locations of Σ with the same types.

## Proof Approach Candidates

### Approach A: Direct Transitivity
- Given Σ ⊆ Σ' and any Σ''' with Σ ⊆ Σ'''
- Show we can use transitivity: Σ ⊆ Σ' and Σ' ⊆ (Σ' ∪ Σ''') and Σ''' ⊆ (Σ' ∪ Σ''')
- Needs: store typing union operation and lemmas

### Approach B: Semantic Argument
- At step 0: relation is True, trivial
- At step n+1: use IH on cumulative, then show structural part
- Structural part: the quantification over extensions of Σ is STRONGER than extensions of Σ'
- Because any extension of Σ' is also an extension of Σ

### Approach C: Induction on n
- Base case (n=0): trivial
- Step case (n+1): extract cumulative (IH), structural needs analysis

## Deliverable

1. A detailed proof strategy explaining each step
2. Identification of any missing lemmas needed
3. If possible, draft Coq tactics

## Rules to Apply

1. **Revolutionary Solution**: The proof must be mathematically perfect and complete.

2. **Zero Vulnerabilities**: Every case and sub-case must be explicitly handled.

3. **Ultra Paranoid Verification**: Each step must be justified. No hand-waving.

4. **No Shortcuts**: If the proof is impossible without additional infrastructure, explain EXACTLY what's missing.

5. **Foundational Correctness**: Based on definitions, not intuition.
