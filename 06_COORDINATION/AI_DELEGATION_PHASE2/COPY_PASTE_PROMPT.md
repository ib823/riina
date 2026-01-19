# COPY-PASTE PROMPT FOR EXTERNAL AI

Copy everything below the line and paste into Claude AI / DeepSeek / Grok:

---

I need help proving a Coq lemma for step-indexed logical relations. This is for a formally verified programming language called RIINA.

## TASK

Prove downward monotonicity for step-indexed value relations:

```coq
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
```

## KEY DEFINITIONS

```coq
(* Step-indexed value relation *)
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 =>
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end.

(* Step-indexed store relation *)
Fixpoint store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  match n with
  | 0 => store_max st1 = store_max st2
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2, store_lookup l st1 = Some v1 /\
                      store_lookup l st2 = Some v2 /\
                      val_rel_n n' Σ T v1 v2)
  end.

(* first_order_type returns true for types without function arrows *)
(* val_rel_at_type_fo is the predicate-independent relation for FO types *)
```

## ALREADY PROVEN (you can use these)

```coq
(* FO-only version - PROVEN *)
Lemma val_rel_n_mono_fo : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.

(* FO equivalence - PROVEN *)
Lemma val_rel_at_type_fo_equiv : forall T Σ SR VR SR' v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ SR VR SR' T v1 v2 <-> val_rel_at_type_fo T v1 v2.

(* Unfolding lemmas - PROVEN *)
Lemma val_rel_n_0_unfold, val_rel_n_S_unfold
Lemma store_rel_n_0_unfold, store_rel_n_S_unfold
```

## THE PROBLEM

The difficult case is `T = TFn T1 T2 eff` (function types).

For TFn, `val_rel_at_type` has a Kripke-style clause:
- Given arguments related at `val_rel_n n'`
- Given stores related at `store_rel_n n'`
- Then function applications produce related outputs

When proving mono from `n = S n'` to `m = S m'` where `m' < n'`:
- We receive arguments at `val_rel_n m'` (MORE values than at n')
- We need to call the hypothesis which expects `val_rel_n n'`
- For FO argument types: use `val_rel_n_mono_fo` (already proven)
- For HO argument types: THIS IS THE HARD PART

## SUGGESTED APPROACH

Use mutual induction with `store_rel_n_mono`:

```coq
Lemma val_store_rel_n_mono : forall m n,
  m <= n ->
  (forall Σ T v1 v2, val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2) /\
  (forall Σ st1 st2, store_rel_n n Σ st1 st2 -> store_rel_n m Σ st1 st2).
```

Or prove store_rel_n_mono first since it's simpler (no Kripke clause).

## DELIVERABLE

Provide a complete Coq proof ending with `Qed.`

If the HO argument case is unprovable without additional assumptions, document this clearly and either:
1. Add a typing precondition to make it provable
2. Use `Admitted` with explanation for that specific case only

---

END OF PROMPT
