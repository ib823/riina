(** * Store.v: Store and Store Typing for TERAS-LANG *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import TerasLang.Foundations.Syntax.

Import ListNotations.

(** ** Store Typing *)

(** Store typing maps locations to their types and security labels *)
Definition store_ty : Type := list (ty * sec_label).

(** Lookup in store typing *)
Definition store_ty_lookup (Σ : store_ty) (l : loc) : option (ty * sec_label) :=
  nth_error Σ l.

(** Store typing extension: Σ' extends Σ if it has all the same bindings *)
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl, store_ty_lookup Σ l = Some (T, sl) ->
                 store_ty_lookup Σ' l = Some (T, sl).

(** Store type extension is reflexive *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Proof.
  unfold store_ty_extends. intros. assumption.
Qed.

(** Store type extension is transitive *)
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
Proof.
  unfold store_ty_extends. intros Σ1 Σ2 Σ3 H12 H23 l T sl Hl.
  apply H23. apply H12. assumption.
Qed.

(** Empty store typing *)
Definition empty_store_ty : store_ty := [].

(** Length of store typing *)
Definition store_ty_length (Σ : store_ty) : nat := length Σ.

(** Extending store typing with a new binding *)
Definition store_ty_extend (Σ : store_ty) (T : ty) (sl : sec_label) : store_ty :=
  Σ ++ [(T, sl)].

(** Lookup in extended store typing for new location *)
Lemma store_ty_extend_lookup_new : forall Σ T sl,
  store_ty_lookup (store_ty_extend Σ T sl) (length Σ) = Some (T, sl).
Proof.
  intros Σ T sl. unfold store_ty_extend, store_ty_lookup.
  rewrite nth_error_app2.
  - replace (length Σ - length Σ) with 0 by lia.
    reflexivity.
  - lia.
Qed.

(** Lookup in extended store typing for old locations *)
Lemma store_ty_extend_lookup_old : forall Σ T sl l,
  l < length Σ ->
  store_ty_lookup (store_ty_extend Σ T sl) l = store_ty_lookup Σ l.
Proof.
  intros Σ T sl l Hl. unfold store_ty_extend, store_ty_lookup.
  rewrite nth_error_app1.
  - reflexivity.
  - assumption.
Qed.

(** Extension preserves old lookups *)
Lemma store_ty_extend_extends : forall Σ T sl,
  store_ty_extends Σ (store_ty_extend Σ T sl).
Proof.
  unfold store_ty_extends. intros Σ T sl l T' sl' Hlookup.
  unfold store_ty_extend, store_ty_lookup in *.
  rewrite nth_error_app1.
  - assumption.
  - apply nth_error_Some. intro Hnone.
    rewrite Hnone in Hlookup. discriminate.
Qed.
