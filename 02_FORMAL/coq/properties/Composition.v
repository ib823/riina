(** * Composition Properties for RIINA

    Compositionality of security properties.

    TODO: These proofs need refactoring after val_rel gained store_ty parameter.
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.SecurityProperties.
Require Import RIINA.properties.NonInterference_v2.
Require Import RIINA.properties.NonInterference_v2_LogicalRelation.

(** ** Compositionality for Related Values *)

(* Composing relations for products *)
(* ADMITTED for v2 migration: first-order product case requires nested val_rel_at_type_fo *)
Lemma val_rel_pair : forall Σ T1 T2 v1 v1' v2 v2',
  val_rel Σ T1 v1 v1' ->
  val_rel Σ T2 v2 v2' ->
  val_rel Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
Admitted.

(* ADMITTED for v2 migration: first-order sum case requires nested val_rel_at_type_fo *)
Lemma val_rel_inl : forall Σ T1 T2 v1 v2,
  val_rel Σ T1 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
Admitted.

(* ADMITTED for v2 migration: first-order sum case requires nested val_rel_at_type_fo *)
Lemma val_rel_inr : forall Σ T1 T2 v1 v2,
  val_rel Σ T2 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
Admitted.

(** ** Compositionality for Expressions *)

(** These follow directly from val_rel lemmas + exp_rel_of_val_rel *)

Lemma exp_rel_pair_values : forall Σ T1 T2 v1 v1' v2 v2',
  val_rel Σ T1 v1 v1' ->
  val_rel Σ T2 v2 v2' ->
  exp_rel Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
  intros. apply exp_rel_of_val_rel. apply val_rel_pair; assumption.
Qed.

Lemma exp_rel_inl_values : forall Σ T1 T2 v1 v2,
  val_rel Σ T1 v1 v2 ->
  exp_rel Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  intros. apply exp_rel_of_val_rel. apply val_rel_inl; assumption.
Qed.

Lemma exp_rel_inr_values : forall Σ T1 T2 v1 v2,
  val_rel Σ T2 v1 v2 ->
  exp_rel Σ (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  intros. apply exp_rel_of_val_rel. apply val_rel_inr; assumption.
Qed.

(** End of Composition.v *)
