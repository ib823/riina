# Claude AI Web Delegation Prompt: Missing Proof Infrastructure

## Context

You are helping complete formal proofs for RIINA, a security-focused programming language with mathematically proven guarantees. The proofs are in Coq 8.18.0.

## Task

The codebase has 131 `Admitted` proofs. Many are blocked on missing infrastructure lemmas. Your task is to provide complete, compilable Coq proofs for the missing lemmas.

## Type System Overview

RIINA uses a rich type system with step-indexed logical relations:

```coq
Inductive ty : Type :=
  | TUnit | TBool | TInt | TString | TBytes
  | TFn : ty -> ty -> effect -> ty      (* Function types *)
  | TProd : ty -> ty -> ty              (* Product types *)
  | TSum : ty -> ty -> ty               (* Sum types *)
  | TRef : ty -> sec_label -> ty        (* Reference types *)
  | TSecret : ty -> ty                  (* Secret/classified types *)
  | TCapability : capability_ty -> ty
  | TProof : ty -> ty
  | TOption : ty -> ty
  | TList : ty -> ty
  | TVector : ty -> nat -> ty
  | TArray : ty -> ty
  | TResult : ty -> ty -> ty
  | TFuture : ty -> ty
  | TStream : ty -> ty
  | TLinear : ty -> ty.
```

Key relations:
- `val_rel_n n Σ T v1 v2`: Step-indexed value relation at step n, store typing Σ, type T
- `val_rel_le n Σ T v1 v2`: Cumulative value relation (forall m <= n, val_rel_n m Σ T v1 v2)
- `store_rel_n n Σ st1 st2`: Step-indexed store relation
- `exp_rel_le n Σ T e1 e2 st1 st2 ctx`: Expression relation for expressions e1, e2

Store typing extension:
- `store_ty_extends Σ Σ'`: Σ' extends Σ (all locations in Σ are also in Σ' with same types)

## Required Lemmas

### 1. Unfold Lemmas for val_rel_le

The `val_rel_le` relation is defined cumulatively. We need unfold lemmas:

```coq
(* val_rel_le is defined as: forall m, m <= n -> val_rel_n m Σ T v1 v2 *)

Lemma val_rel_le_0_unfold : forall Σ T v1 v2,
  val_rel_le 0 Σ T v1 v2 <->
  (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\ val_rel_struct T v1 v2).

Lemma val_rel_le_S_unfold : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 <->
  (val_rel_le n Σ T v1 v2 /\ value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\ val_rel_struct T v1 v2).
```

### 2. Store Relation Unfold Lemmas

```coq
Lemma store_rel_n_0_unfold : forall Σ st1 st2,
  store_rel_n 0 Σ st1 st2 <-> True.

Lemma store_rel_n_S_unfold : forall n Σ st1 st2,
  store_rel_n (S n) Σ st1 st2 <->
  (store_rel_n n Σ st1 st2 /\
   store_max st1 = store_max st2 /\
   forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
     exists v1 v2, store_lookup l st1 = Some v1 /\
                   store_lookup l st2 = Some v2 /\
                   val_rel_n n Σ T v1 v2).
```

### 3. Structural Conversion Lemmas

```coq
(* Convert between val_rel_struct and val_rel_at_type for first-order types *)
Lemma val_rel_struct_to_at_type_fo : forall T v1 v2 Σ sr vr srl,
  first_order_type T = true ->
  val_rel_struct T v1 v2 ->
  val_rel_at_type Σ sr vr srl T v1 v2.

Lemma val_rel_at_type_fo_to_struct : forall T v1 v2 Σ sr vr srl,
  first_order_type T = true ->
  val_rel_at_type Σ sr vr srl T v1 v2 ->
  val_rel_struct T v1 v2.

(* Higher-order type conversions *)
Lemma val_rel_struct_to_at_type_ho_0 : forall T v1 v2 Σ sr vr srl,
  first_order_type T = false ->
  val_rel_struct T v1 v2 ->
  val_rel_at_type Σ sr vr srl T v1 v2.

Lemma val_rel_struct_to_at_type_ho : forall T v1 v2 Σ sr vr srl n,
  first_order_type T = false ->
  val_rel_struct T v1 v2 ->
  store_ty_extends Σ Σ ->  (* reflexivity *)
  val_rel_at_type Σ sr vr srl T v1 v2.
```

### 4. Typing Extraction and Weakening

```coq
(* Extract typing from val_rel_le structure *)
Lemma val_rel_struct_to_typing_left : forall T v1 v2,
  val_rel_struct T v1 v2 ->
  first_order_type T = false ->
  has_type nil empty_store_ty Public v1 T EffectPure.

Lemma val_rel_struct_to_typing_right : forall T v1 v2,
  val_rel_struct T v1 v2 ->
  first_order_type T = false ->
  has_type nil empty_store_ty Public v2 T EffectPure.

(* Store typing weakening/strengthening *)
Lemma typing_weaken_store : forall Γ Σ Σ' Δ e T eff,
  has_type Γ Σ Δ e T eff ->
  store_ty_extends Σ Σ' ->
  has_type Γ Σ' Δ e T eff.

Lemma typing_strengthen_store : forall Γ Σ Σ' Δ e T eff,
  has_type Γ Σ' Δ e T eff ->
  store_ty_extends Σ Σ' ->
  (* Only valid when e doesn't use locations in Σ' \ Σ *)
  has_type Γ Σ Δ e T eff.
```

### 5. Kripke Monotonicity Helpers

```coq
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.

Lemma store_ty_extends_lookup_eq : forall Σ Σ' l T sl T' sl',
  store_ty_extends Σ Σ' ->
  store_ty_lookup l Σ = Some (T, sl) ->
  store_ty_lookup l Σ' = Some (T', sl') ->
  T = T' /\ sl = sl'.

Lemma store_ty_lookup_dec : forall l Σ,
  {exists T sl, store_ty_lookup l Σ = Some (T, sl)} +
  {store_ty_lookup l Σ = None}.

Lemma new_location_related : forall n Σ Σ' st1 st2 l T sl,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ st1 st2 ->
  store_ty_lookup l Σ = None ->
  store_ty_lookup l Σ' = Some (T, sl) ->
  exists v1 v2, store_lookup l st1 = Some v1 /\
                store_lookup l st2 = Some v2 /\
                val_rel_n n Σ' T v1 v2.
```

### 6. Evaluation Determinism and Structure

```coq
Lemma multi_step_deterministic : forall e st v1 st1 v2 st2 ctx,
  multi_step (e, st, ctx) (v1, st1, ctx) ->
  multi_step (e, st, ctx) (v2, st2, ctx) ->
  value v1 -> value v2 ->
  v1 = v2 /\ st1 = st2.

(* For declassification - same expression under related stores gives related results *)
Lemma declassify_equal_expr_equal_result : forall n Σ T e p st1 st2 ctx v1 v2,
  e = e ->  (* syntactically identical *)
  store_rel_le n Σ st1 st2 ->
  multi_step (EDeclassify e p, st1, ctx) (v1, st1, ctx) ->
  multi_step (EDeclassify e p, st2, ctx) (v2, st2, ctx) ->
  value v1 -> value v2 ->
  val_rel_le n Σ T v1 v2.
```

### 7. Security Label Helpers

```coq
Definition is_low (sl : sec_label) : bool :=
  match sl with Public => true | Secret => false end.

Lemma is_low_dec : forall sl, {is_low sl = true} + {is_low sl = false}.
```

## Output Format

For each lemma, provide:
1. The complete Coq proof (ending in `Qed.`)
2. Any helper lemmas needed
3. Notes on proof strategy

## Important Notes

1. **Type definitions are fixed** - do not change the existing type definitions
2. **Proofs must compile** - test each proof individually before combining
3. **Use existing lemmas** - check what's already proven in the codebase
4. **Avoid Admitted** - every proof must end in `Qed.`
5. **Use standard tactics** - `induction`, `destruct`, `simpl`, `auto`, `lia`, `inversion`

## First-Order Type Predicate

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TRef _ _ => true
  | TSecret _ => true
  | TCapability _ | TProof _ => true
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TOption T => first_order_type T
  | TList T => first_order_type T
  | TVector T _ => first_order_type T
  | TArray T => first_order_type T
  | TResult T1 T2 => first_order_type T1 && first_order_type T2
  | TFn _ _ _ => false  (* Functions are never first-order *)
  | TFuture _ | TStream _ | TLinear _ => false
  end.
```

## Expected Output

A single Coq file containing all the lemmas with complete proofs, organized by category, that can be added to the codebase as a new module `ProofInfrastructure.v`.
