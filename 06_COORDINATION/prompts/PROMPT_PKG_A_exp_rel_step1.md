# Package A: exp_rel_step1 Lemmas for RIINA

## Task

Prove the exp_rel_step1_fst_typed and exp_rel_step1_snd_typed lemmas in Coq.

## Background

RIINA uses step-indexed logical relations for non-interference proofs. These lemmas show that projecting from a product value (fst/snd) preserves the logical relation.

## Key Definitions

```coq
(* val_rel_n 0 in v2 semantics - NOT trivially True *)
Lemma val_rel_n_0_unfold : forall Σ T v1 v2,
  val_rel_n 0 Σ T v1 v2 =
  (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)).

(* store_rel_n 0 *)
Lemma store_rel_n_0_unfold : forall Σ st1 st2,
  store_rel_n 0 Σ st1 st2 = (store_max st1 = store_max st2).

(* val_rel_at_type_fo for products *)
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | _ => True
  end.

(* Operational semantics for fst *)
(* ST_FstPair: EFst (EPair v1 v2) --> v1 when value v1, value v2 *)

(* Canonical forms: typed value of TProd is EPair *)
Lemma canonical_forms_prod : forall Γ Σ v T1 T2 ε,
  has_type Γ Σ Public v (TProd T1 T2) ε ->
  value v ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.
```

## Lemma to Prove

```coq
Lemma exp_rel_step1_fst_typed : forall Γ Σ Σ' T1 T2 v v' st1 st2 ctx ε,
  has_type Γ Σ' Public v (TProd T1 T2) ε ->
  has_type Γ Σ' Public v' (TProd T1 T2) ε ->
  value v -> value v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EFst v, st1, ctx) -->* (a1, st1', ctx') /\
    (EFst v', st2, ctx) -->* (a2, st2', ctx') /\
    value a1 /\ value a2 /\
    val_rel_n 0 Σ'' T1 a1 a2 /\
    store_rel_n 0 Σ'' st1' st2'.
Proof.
  (* YOUR PROOF HERE *)
Admitted.
```

## Proof Sketch

1. Use canonical_forms_prod to get v = EPair a1 b1 and v' = EPair a2 b2
2. EFst (EPair a1 b1) takes one step to a1 (ST_FstPair)
3. Similarly EFst (EPair a2 b2) --> a2
4. The store doesn't change (pure operation), so st1' = st1, st2' = st2
5. Choose Σ'' = Σ' (no new allocations)
6. store_ty_extends Σ' Σ' is reflexive
7. For val_rel_n 0 Σ' T1 a1 a2:
   - Need value a1, value a2 (from canonical forms)
   - Need closed_expr a1, closed_expr a2 (from typing + value)
   - Need val_rel_at_type_fo T1 a1 a2 if first_order_type T1
8. For store_rel_n 0: same stores, same store_max

## Helper Lemmas You May Need

```coq
(* Reflexivity of store_ty_extends *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.

(* One step to multi-step *)
Lemma step_to_multi : forall e1 st1 ctx e2 st2 ctx',
  (e1, st1, ctx) --> (e2, st2, ctx') ->
  (e1, st1, ctx) -->* (e2, st2, ctx').

(* Closed under subexpressions for pairs *)
Lemma closed_pair_inv : forall v1 v2,
  closed_expr (EPair v1 v2) ->
  closed_expr v1 /\ closed_expr v2.

(* Value subexpressions of pairs are values *)
Lemma value_pair_inv : forall v1 v2,
  value (EPair v1 v2) ->
  value v1 /\ value v2.
```

## Expected Output

A complete Coq proof ending with `Qed.` for both:
1. exp_rel_step1_fst_typed
2. exp_rel_step1_snd_typed (similar, but extracts second component)

Include any helper lemmas you need to define.
