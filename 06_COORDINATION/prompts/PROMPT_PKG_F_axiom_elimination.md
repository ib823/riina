# Package F: AxiomEliminationVerified Admits

## Task

Prove admits in `AxiomEliminationVerified.v` - step-1 termination lemmas.

## Background

`AxiomEliminationVerified.v` contains 15 admits related to proving that well-typed expressions terminate at step 1. The key pattern is:
- For first-order (FO) types, val_rel_n 1 requires structural equality
- The proofs need to show that typed values satisfy val_rel_at_type_fo

## Key Definitions

```coq
(* Step 1 value relation structure *)
val_rel_n 1 Σ T v1 v2 ≡
  val_rel_n 0 Σ T v1 v2 ∧
  value v1 ∧ value v2 ∧
  closed_expr v1 ∧ closed_expr v2 ∧
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)

(* First-order types *)
first_order_type TUnit = true
first_order_type TBool = true
first_order_type TInt = true
first_order_type TString = true
first_order_type (TProd T1 T2) = first_order_type T1 && first_order_type T2
first_order_type (TSum T1 T2) = first_order_type T1 && first_order_type T2
first_order_type (TFn _ _) = false
first_order_type (TRef _ _) = false  (* Depends on semantics *)
```

## Admits to Prove

### Group 1: Base Type Step-1 Termination (Lines 64-174)

```coq
(* Line 64: exp_rel_step1_unit_typed *)
Lemma exp_rel_step1_unit_typed : forall Σ st1 st2 ctx,
  store_rel_n 1 Σ st1 st2 ->
  exp_rel_n 1 Σ TUnit EUnit EUnit.

(* Line 85: exp_rel_step1_bool_typed *)
Lemma exp_rel_step1_bool_typed : forall Σ b st1 st2 ctx,
  store_rel_n 1 Σ st1 st2 ->
  exp_rel_n 1 Σ TBool (EBool b) (EBool b).

(* Line 107: exp_rel_step1_int_typed *)
Lemma exp_rel_step1_int_typed : forall Σ n st1 st2 ctx,
  store_rel_n 1 Σ st1 st2 ->
  exp_rel_n 1 Σ TInt (EInt n) (EInt n).

(* Line 127: exp_rel_step1_string_typed *)
Lemma exp_rel_step1_string_typed : forall Σ s st1 st2 ctx,
  store_rel_n 1 Σ st1 st2 ->
  exp_rel_n 1 Σ TString (EString s) (EString s).
```

### Group 2: Compound Type Step-1 (Lines 151-174)

```coq
(* Line 151: exp_rel_step1_pair_typed - needs recursive structure *)
(* Line 174: exp_rel_step1_sum_typed - needs case analysis *)
```

### Group 3: Step-Up for FO Types (Lines 281-521)

These require proving that val_rel_n n implies val_rel_n (S n) for first-order types.

## Proof Strategy

1. **For base types (Unit, Bool, Int, String):**
   - Values are already closed
   - val_rel_at_type_fo is reflexivity (same value = same value)
   - Use `val_rel_n_0_unit`, `val_rel_n_unit`, `exp_rel_n_unit` as models

2. **For compound types (Prod, Sum):**
   - Need recursive decomposition
   - Use `first_order_prod_inv` and `first_order_sum_inv` lemmas
   - May need well-founded induction on type structure

3. **For step-up:**
   - Key insight: if val_rel_n n holds for FO types, val_rel_n (S n) adds the SAME requirements
   - FO types have val_rel_at_type_fo that doesn't change with step index

## Reference Proofs

From NonInterference_v2.v (recently proven):

```coq
Lemma val_rel_n_0_unit : forall Σ,
  val_rel_n 0 Σ TUnit EUnit EUnit.
Proof.
  intros Σ. rewrite val_rel_n_0_unfold.
  split; [constructor |].
  split; [constructor |].
  split; [intros x Hfree; inversion Hfree |].
  split; [intros x Hfree; inversion Hfree |].
  simpl. split; reflexivity.
Qed.

Lemma val_rel_n_unit : forall n Σ,
  n > 0 -> val_rel_n n Σ TUnit EUnit EUnit.
Proof.
  (* Induction on n, using val_rel_n_0_unit as base *)
  ...
Qed.

Lemma exp_rel_n_unit : forall n Σ,
  exp_rel_n n Σ TUnit EUnit EUnit.
Proof.
  (* For n=0: trivial. For S n': EUnit is value, terminates to itself *)
  ...
Qed.
```

## Expected Output

At minimum, prove:
1. `exp_rel_step1_unit_typed` - PROVEN with Qed
2. `exp_rel_step1_bool_typed` - PROVEN with Qed
3. `exp_rel_step1_int_typed` - PROVEN with Qed
4. `exp_rel_step1_string_typed` - PROVEN with Qed

Stretch goals:
5. `exp_rel_step1_pair_typed` - PROVEN or detailed partial proof
6. `exp_rel_step1_sum_typed` - PROVEN or detailed partial proof

## File Location

`/workspaces/proof/02_FORMAL/coq/properties/AxiomEliminationVerified.v`

Build command: `make` (from `/workspaces/proof/02_FORMAL/coq/`)
