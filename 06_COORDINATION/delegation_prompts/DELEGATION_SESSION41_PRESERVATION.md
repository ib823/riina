# Claude AI Web Delegation - Session 41 Preservation Admits

## Current State
- **NonInterference_v2.v**: 13 admits remaining
- **Coq Build**: PASSING
- **Last Commit**: `4a2d6fd` - nested TProd/TSum resolved

## Task: Eliminate Preservation-Related Admits

### Context

We have 10 preservation-related admits in `combined_step_up_all` that require proving store properties are preserved through TFn application evaluation.

### The Admits

#### Group 1: TFn Application Results (5 admits at lines ~1593-1601)
After TFn application `(EApp f x, st1, ctx) -->* (v', st1', ctx')`:
```coq
- store_wf Σ'' st1'           (* line 1593 *)
- store_wf Σ'' st2'           (* line 1595 *)
- store_has_values st1'       (* line 1597 *)
- store_has_values st2'       (* line 1599 *)
- stores_agree_low_fo Σ'' st1' st2'  (* line 1601 *)
```

#### Group 2: Nested TFn Results (4 admits at lines 1662, 1733, 1808, 1880)
```coq
{ (* store_rel step-up requires preservation *) admit. }
```

#### Group 3: Helper Lemma TFn Case (1 admit at line ~1334)
In `val_rel_at_type_step_up_with_IH`, TFn case needs store_rel step-up.

### Key Definitions

```coq
(* store_wf now includes value v - strengthened in Session 41 *)
Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  (forall l T sl,
     store_ty_lookup l Σ = Some (T, sl) ->
     exists v, store_lookup l st = Some v /\ value v /\ has_type nil Σ Public v T EffectPure)
  /\
  (forall l v,
     store_lookup l st = Some v ->
     exists T sl, store_ty_lookup l Σ = Some (T, sl) /\ value v /\ has_type nil Σ Public v T EffectPure).

Definition store_has_values (st : store) : Prop :=
  forall l v, store_lookup l st = Some v -> value v.

Definition stores_agree_low_fo (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    is_low sl = true ->
    first_order_type T = true ->
    store_lookup l st1 = store_lookup l st2.
```

### What We Have

1. **Preservation Theorem** in `type_system/Preservation.v`:
   - `preservation`: Single step preserves typing
   - `preservation_multi`: Multi-step preserves typing
   - `store_wf_update_existing`: Updating existing location preserves store_wf
   - `store_wf_update_fresh`: Adding fresh location preserves store_wf

2. **From val_rel_n/store_rel_n at level n'**:
   - Values are well-typed
   - Stores satisfy store_rel_n n' (includes val_rel for each location)

3. **From evaluation**:
   - `(EApp f x, st1, ctx) -->* (v', st1', ctx')`
   - We know `v'` is a value (from val_rel_n result)

### Required Lemmas

#### Lemma 1: store_wf_preservation
```coq
Lemma store_wf_preservation : forall Σ Σ' e e' st st' ctx ctx' T eff,
  has_type nil Σ Public e T eff ->
  store_wf Σ st ->
  (e, st, ctx) -->* (e', st', ctx') ->
  store_ty_extends Σ Σ' ->
  store_wf Σ' st'.
```

#### Lemma 2: store_has_values_preservation
```coq
Lemma store_has_values_preservation : forall e e' st st' ctx ctx',
  store_has_values st ->
  (e, st, ctx) -->* (e', st', ctx') ->
  store_has_values st'.
```

This should follow from:
- Only ST_RefValue and ST_AssignLoc modify the store
- Both require `value v` as a precondition
- So all new store entries are values

#### Lemma 3: stores_agree_low_fo_preservation
```coq
Lemma stores_agree_low_fo_preservation : forall Σ Σ' e1 e2 v1 v2 st1 st2 st1' st2' ctx ctx' T eff,
  stores_agree_low_fo Σ st1 st2 ->
  val_rel_n n Σ T e1 e2 ->  (* Related expressions *)
  store_rel_n n Σ st1 st2 ->
  (e1, st1, ctx) -->* (v1, st1', ctx') ->
  (e2, st2, ctx) -->* (v2, st2', ctx') ->
  store_ty_extends Σ Σ' ->
  stores_agree_low_fo Σ' st1' st2'.
```

This is the key non-interference property for stores:
- LOW FO locations must remain identical after related evaluations
- This follows from the non-interference of the evaluation itself

### Approach

1. **Prove store_has_values_preservation first** - Should be straightforward
   - Induction on multi-step
   - Case analysis on single step rules
   - Only ST_RefValue and ST_AssignLoc modify store, both require value

2. **Prove store_wf_preservation** - Uses preservation theorem
   - Use existing `preservation_multi` for typing
   - Use `store_wf_update_existing`/`store_wf_update_fresh` for store modifications

3. **For stores_agree_low_fo_preservation** - This is harder
   - Requires showing that related evaluations produce identical LOW FO updates
   - This is essentially the non-interference theorem for store updates
   - May need to be proved as part of the main non-interference proof

### Alternative: Use Admits Strategically

If full proofs are complex, create well-documented axioms:
```coq
Axiom store_wf_preserved_by_evaluation : forall Σ Σ' e v st st' ctx ctx',
  has_type nil Σ Public e T eff ->
  store_wf Σ st ->
  (e, st, ctx) -->* (v, st', ctx') ->
  value v ->
  store_ty_extends Σ Σ' ->
  store_wf Σ' st'.
```

### Files to Modify

1. `02_FORMAL/coq/type_system/Preservation.v` - Add preservation corollaries
2. `02_FORMAL/coq/properties/NonInterference_v2.v` - Replace admits with lemma applications

### Output Format

Please provide:
1. Complete Coq lemma statements
2. Proof sketches or full proofs where possible
3. Any new helper lemmas needed
4. Exact replacement text for each admit location

### Current Admit Locations

```
Line 1334:      admit.  (* In val_rel_at_type_step_up_with_IH TFn case *)
Line 1593:      admit.  (* store_wf Σ'' st1' *)
Line 1595:      admit.  (* store_wf Σ'' st2' *)
Line 1597:      admit.  (* store_has_values st1' *)
Line 1599:      admit.  (* store_has_values st2' *)
Line 1601:      admit.  (* stores_agree_low_fo Σ'' st1' st2' *)
Line 1662:      admit.  (* store_rel step-up requires preservation *)
Line 1733:      admit.  (* store_rel step-up requires preservation *)
Line 1808:      admit.  (* store_rel step-up requires preservation *)
Line 1880:      admit.  (* store_rel step-up requires preservation *)
```

Plus 2 justified admits (lines 284, 286) for mixed constructor cases at HIGH security.
Plus 1 Fundamental Theorem admit (line 1532) for n=0 case.
