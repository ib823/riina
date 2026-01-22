# Package G: MasterTheorem Composition Admits

## Task

Prove admits in `MasterTheorem.v` - the main non-interference composition lemmas.

## Background

`MasterTheorem.v` composes all component proofs into the main security theorem. It has 7 admits related to:
1. Step monotonicity (step-down/step-up)
2. Store relation composition
3. Expression relation composition
4. Multi-step evaluation preservation

## Key Structure

```coq
(* The ultimate goal: non-interference *)
Theorem non_interference : forall Γ Σ e T ε,
  has_type Γ Σ Public e T ε ->
  forall rho1 rho2,
    env_rel Γ Σ rho1 rho2 ->
    exp_rel Σ T (subst_rho rho1 e) (subst_rho rho2 e).
```

## Admits to Prove

### Admit 1: val_rel_n_step_up_compound (Line 110)

```coq
(* Step-up for compound types (TProd, TSum) *)
Lemma val_rel_n_step_up_compound : forall n Σ T v1 v2,
  first_order_type T = true ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
```

**Strategy:** Use well-founded induction on type measure. For TProd/TSum, decompose into components and apply IH.

### Admit 2: val_rel_n_step_up_fo_general (Line 144)

```coq
(* General step-up for FO types *)
Lemma val_rel_n_step_up_fo_general : forall n m Σ T v1 v2,
  first_order_type T = true ->
  n <= m ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
```

**Strategy:** Induction on (m - n). Use step-up lemma repeatedly.

### Admit 3: store_rel_n_deref (Line 843)

```coq
(* Deref preserves store relation *)
Lemma store_rel_n_deref : forall n Σ st1 st2 l T sl v1 v2,
  store_rel_n (S n) Σ st1 st2 ->
  store_ty_lookup l Σ = Some (T, sl) ->
  store_lookup l st1 = Some v1 ->
  store_lookup l st2 = Some v2 ->
  val_rel_n n Σ T v1 v2.
```

**Strategy:** Unfold store_rel_n (S n) which directly gives val_rel_n for typed locations.

### Admit 4: exp_rel_n_compose_let (Line 998)

```coq
(* Let binding composition *)
Lemma exp_rel_n_compose_let : forall n Σ T1 T2 e1 e2 x body1 body2,
  exp_rel_n n Σ T1 e1 e2 ->
  (forall v1 v2, val_rel_n n Σ T1 v1 v2 ->
                 exp_rel_n n Σ T2 (subst x v1 body1) (subst x v2 body2)) ->
  exp_rel_n n Σ T2 (ELet x e1 body1) (ELet x e2 body2).
```

**Strategy:** For n=0 trivial. For S n', show e1/e2 evaluate to related values, then apply continuation hypothesis.

### Admit 5: exp_rel_n_compose_app (Line 1115)

```coq
(* Application composition *)
Lemma exp_rel_n_compose_app : forall n Σ T1 T2 f1 f2 arg1 arg2,
  exp_rel_n n Σ (TFn T1 T2) f1 f2 ->
  exp_rel_n n Σ T1 arg1 arg2 ->
  exp_rel_n n Σ T2 (EApp f1 arg1) (EApp f2 arg2).
```

**Strategy:** Requires function value relation which includes body evaluation.

### Admit 6: store_rel_n_alloc (Line 1267)

```coq
(* Allocation preserves store relation (with extension) *)
Lemma store_rel_n_alloc : forall n Σ st1 st2 v1 v2 T sl,
  store_rel_n n Σ st1 st2 ->
  val_rel_n n Σ T v1 v2 ->
  exists Σ' l,
    store_ty_extends Σ Σ' /\
    store_rel_n n Σ' (store_update l v1 st1) (store_update l v2 st2).
```

**Strategy:** Extend Σ with fresh location, show new store relation holds.

### Admit 7: master_theorem_main (Line 2130)

```coq
(* Main theorem - combines everything *)
Theorem master_theorem_main : forall Γ Σ e T ε,
  has_type Γ Σ Public e T ε ->
  forall rho1 rho2,
    env_rel Γ Σ rho1 rho2 ->
    exp_rel Σ T (subst_rho rho1 e) (subst_rho rho2 e).
```

**Strategy:** Induction on typing derivation. Each case uses one of the composition lemmas above.

## Priority

Focus on admits 1-3 first (step-up and deref). These have clear strategies.
Admits 4-6 are composition lemmas that follow standard patterns.
Admit 7 (master theorem) requires all others.

## Reference

See existing proven lemmas:
- `val_rel_n_mono` - Kripke monotonicity (FO case proven)
- `store_rel_n_mono` - Step monotonicity for stores
- `exp_rel_step1_*` - Step-1 cases

## Expected Output

1. `val_rel_n_step_up_compound` - PROVEN or detailed partial
2. `store_rel_n_deref` - Should be straightforward
3. At least 2-3 other admits with progress

## File Location

`/workspaces/proof/02_FORMAL/coq/properties/MasterTheorem.v`
