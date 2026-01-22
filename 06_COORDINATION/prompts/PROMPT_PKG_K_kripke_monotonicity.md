# Package K: Kripke & Monotonicity Admits

## Task

Prove the 11 admits across Kripke monotonicity and cumulative relation files.

## Files & Admits

| File | Admits | Focus |
|------|--------|-------|
| `KripkeMutual.v` | 3 | Mutual induction for store/val Kripke |
| `NonInterferenceKripke.v` | 3 | Kripke properties for NI |
| `KripkeProperties.v` | 2 | General Kripke lemmas |
| `CumulativeRelation.v` | 2 | Cumulative (step-indexed) properties |
| `CumulativeMonotone.v` | 1 | Monotonicity in step index |

## Key Concepts

### Kripke Monotonicity

"If values are related at store typing Σ, they remain related at any extended Σ' ⊇ Σ."

```coq
Lemma val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
```

**Key insight for FO types:** `val_rel_at_type_fo` doesn't depend on Σ at all, so Kripke monotonicity is trivial.

**Challenge for TFn types:** Function bodies may allocate, requiring mutual induction.

### Step Monotonicity

```coq
(* Step-down: if related at n+1, related at n *)
Lemma val_rel_n_step_down : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 ->
  val_rel_n n Σ T v1 v2.

(* Step-up: if related at n, related at n+1 (for FO types) *)
Lemma val_rel_n_step_up_fo : forall n Σ T v1 v2,
  first_order_type T = true ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
```

## Already Proven (Reference)

From NonInterference_v2.v:
- `val_rel_n_mono` - FO case proven
- `store_rel_n_mono` - Proven
- `val_rel_at_type_fo_equiv` - FO types are predicate-independent

From KripkeMonotonicity.v (Package E):
- `val_rel_n_mono_store_fo` - Qed
- `val_rel_n_step_up_fo` - Qed
- `val_rel_n_step_down` - Qed

## Strategy

### For FO-type lemmas
Use the fact that `val_rel_at_type_fo` is Σ-independent:
```coq
(* Pattern *)
destruct (first_order_type T) eqn:Hfo.
- (* FO case: use val_rel_at_type_fo_equiv *)
  apply val_rel_n_mono_store_fo; auto.
- (* Non-FO case: may need to admit or use different approach *)
```

### For mutual induction
May need to prove val_rel and store_rel monotonicity together:
```coq
Lemma val_store_rel_mono_mutual : forall n,
  (forall Σ Σ' T v1 v2, ... -> val_rel_n n Σ' T v1 v2) /\
  (forall Σ Σ' st1 st2, ... -> store_rel_n n Σ' st1 st2).
Proof.
  induction n; split; intros.
  (* ... *)
Qed.
```

## Expected Output

- At minimum: All FO-type cases proven (should be 6-8 of the 11)
- Stretch: Mutual induction for general case
- Document: Clear notes on what blocks the TFn cases

## Deliverables

1. Proofs for all FO-type admits (Qed)
2. Partial proofs or detailed sketches for TFn cases
3. Summary of which admits are truly blocked and why

## File Locations

```
/workspaces/proof/02_FORMAL/coq/properties/
├── KripkeMutual.v
├── NonInterferenceKripke.v
├── KripkeProperties.v
├── CumulativeRelation.v
└── CumulativeMonotone.v
```
