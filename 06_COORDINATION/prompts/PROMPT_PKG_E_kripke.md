# Package E: Kripke Monotonicity Properties

## Task

Prove Kripke monotonicity lemmas - that value relations are preserved under store typing extension.

## Background

"Kripke monotonicity" means: if values are related at store typing Σ, they remain related at any extended store typing Σ' ⊇ Σ.

This is essential for handling allocation: when we allocate a new reference, the store typing grows, and we need existing value relations to still hold.

## Key Definitions

```coq
(* Store typing extension *)
Definition store_ty_extends (Σ Σ' : store_typing) : Prop :=
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
                 store_ty_lookup l Σ' = Some (T, sl).

(* Properties of store_ty_extends *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 -> store_ty_extends Σ2 Σ3 -> store_ty_extends Σ1 Σ3.
```

## The Kripke Property

For first-order types, Kripke monotonicity is straightforward because `val_rel_at_type_fo` doesn't depend on the store typing Σ.

For function types (TFn), it's more complex because function bodies may allocate new references.

## Lemmas to Prove

### Lemma 1: val_rel_at_type_fo_store_independent

```coq
(* val_rel_at_type_fo doesn't depend on store typing *)
Lemma val_rel_at_type_fo_store_independent : forall T v1 v2,
  val_rel_at_type_fo T v1 v2 <-> val_rel_at_type_fo T v1 v2.
Proof.
  (* Trivially true - val_rel_at_type_fo has no Σ parameter *)
  tauto.
Qed.
```

### Lemma 2: val_rel_n_mono_store_fo (FO Version)

```coq
(* For first-order types, Kripke monotonicity is direct *)
Lemma val_rel_n_mono_store_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  intros n Σ Σ' T v1 v2 Hfo Hext Hrel.
  induction n.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in *.
    destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Htype]]]].
    repeat split; try assumption.
    (* val_rel_at_type_fo doesn't depend on Σ *)
    rewrite Hfo in *. exact Htype.
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in *.
    destruct Hrel as [Hprev [Hv1 [Hv2 [Hc1 [Hc2 Htype]]]]].
    split.
    + (* val_rel_n n' Σ' T v1 v2 *)
      apply IHn. exact Hprev.
    + repeat split; try assumption.
      (* val_rel_at_type for FO types is predicate-independent *)
      (* Use val_rel_at_type_fo_equiv *)
      apply val_rel_at_type_fo_equiv; auto.
      apply val_rel_at_type_fo_equiv in Htype; auto.
Qed.
```

### Lemma 3: store_rel_n_mono_store_fo

```coq
(* Store relation monotonicity for FO types in the store *)
Lemma store_rel_n_mono_store_fo : forall n Σ Σ' st1 st2,
  (forall l T sl, store_ty_lookup l Σ = Some (T, sl) -> first_order_type T = true) ->
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n n Σ' st1 st2.
Proof.
  (* The store relation at Σ' only needs to satisfy Σ' lookups,
     which include all Σ lookups by extension *)
Admitted.
```

### Lemma 4: val_rel_n_weaken_aux_fo

```coq
(* Auxiliary weakening for store typing *)
Lemma val_rel_n_weaken_aux_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  (forall l T' sl, store_ty_lookup l Σ = Some (T', sl) ->
                   store_ty_lookup l Σ' = Some (T', sl)) ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  (* Same as val_rel_n_mono_store_fo but with explicit extension condition *)
Admitted.
```

### Lemma 5: General Kripke (Harder - May Need to Admit)

```coq
(* General Kripke monotonicity - includes function types *)
Lemma val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  (* For TFn types, need to show function body evaluation
     still works with extended store typing.
     This requires mutual induction with store_rel_n_mono_store *)
Admitted.
```

## Proof Strategy for FO Case

1. Induction on the step index n
2. For n = 0: use val_rel_n_0_unfold, note that val_rel_at_type_fo doesn't use Σ
3. For n = S n':
   - Apply IH for val_rel_n n'
   - For val_rel_at_type, use val_rel_at_type_fo_equiv since T is first-order

## Key Insight

For first-order types:
- `val_rel_at_type_fo T v1 v2` is syntactic - it only looks at the structure of v1, v2
- It does NOT examine the store or store typing
- Therefore, any relation proved at Σ holds at any Σ' ⊇ Σ

For function types:
- `val_rel_at_type` for TFn involves evaluating the function body
- The body may allocate new references
- Need to show that evaluation at Σ' still works if it worked at Σ
- This is the "Kripke" property from possible worlds semantics

## Expected Output

1. val_rel_n_mono_store_fo - PROVEN with Qed
2. store_rel_n_mono_store_fo - PROVEN with Qed (if possible)
3. val_rel_n_weaken_aux_fo - PROVEN with Qed
4. val_rel_n_mono_store (general) - May need Admitted with notes on what's needed
