# Package J: NonInterferenceZero Admits

## Task

Prove the 5 admits in `NonInterferenceZero.v` - zero-step base cases for the logical relation.

## Background

In v2 semantics, `val_rel_n 0` is NOT trivially True. It requires:
- Both expressions are values
- Both expressions are closed
- For first-order types: structural equality via `val_rel_at_type_fo`

## Admits to Prove

```bash
grep -n "Admitted\." properties/NonInterferenceZero.v
```

### Common Pattern

All zero-step lemmas follow this structure:

```coq
Lemma val_rel_n_0_XXX : forall Σ ...,
  val_rel_n 0 Σ T v1 v2.
Proof.
  intros.
  rewrite val_rel_n_0_unfold.
  repeat split.
  - (* value v1 *) constructor.
  - (* value v2 *) constructor.
  - (* closed_expr v1 *) intros x Hfree; inversion Hfree.
  - (* closed_expr v2 *) intros x Hfree; inversion Hfree.
  - (* val_rel_at_type_fo or True *)
    simpl. (* depends on type *)
Qed.
```

## Reference: Already Proven

From NonInterference_v2.v (session 33):

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
```

## Key Definitions

```coq
(* val_rel_n 0 unfolds to: *)
val_rel_n 0 Σ T v1 v2 =
  value v1 ∧ value v2 ∧
  closed_expr v1 ∧ closed_expr v2 ∧
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)

(* val_rel_at_type_fo for common types: *)
val_rel_at_type_fo TUnit v1 v2 = (v1 = EUnit ∧ v2 = EUnit)
val_rel_at_type_fo TBool v1 v2 = ∃b, v1 = EBool b ∧ v2 = EBool b
val_rel_at_type_fo TInt v1 v2 = ∃n, v1 = EInt n ∧ v2 = EInt n
val_rel_at_type_fo (TProd T1 T2) v1 v2 = ∃a1 b1 a2 b2, ...
val_rel_at_type_fo (TFn _ _) v1 v2 = True  (* not first-order *)
```

## Expected Output

All 5 admits proven with Qed:
1. Check what specific lemmas are admitted
2. Apply the standard pattern above
3. Handle any type-specific cases

## Deliverables

- 5 Coq proofs ending with `Qed.`
- Identify any blockers (report if lemma requires unavailable dependencies)

## File Location

`/workspaces/proof/02_FORMAL/coq/properties/NonInterferenceZero.v`
