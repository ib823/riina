(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

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
(* PROVEN using val_rel_n_prod_compose from NonInterference_v2_LogicalRelation.v *)
Lemma val_rel_pair : forall Σ T1 T2 v1 v1' v2 v2',
  val_rel Σ T1 v1 v1' ->
  val_rel Σ T2 v2 v2' ->
  val_rel Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
  intros Σ T1 T2 v1 v1' v2 v2' Hrel1 Hrel2.
  unfold val_rel in *.
  intro n.
  apply val_rel_n_prod_compose.
  - apply Hrel1.
  - apply Hrel2.
Qed.

(* PROVEN using val_rel_n_sum_inl from NonInterference_v2_LogicalRelation.v *)
Lemma val_rel_inl : forall Σ T1 T2 v1 v2,
  val_rel Σ T1 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  intros Σ T1 T2 v1 v2 Hrel.
  unfold val_rel in *.
  intro n.
  apply val_rel_n_sum_inl.
  apply Hrel.
Qed.

(* PROVEN using val_rel_n_sum_inr from NonInterference_v2_LogicalRelation.v *)
Lemma val_rel_inr : forall Σ T1 T2 v1 v2,
  val_rel Σ T2 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  intros Σ T1 T2 v1 v2 Hrel.
  unfold val_rel in *.
  intro n.
  apply val_rel_n_sum_inr.
  apply Hrel.
Qed.

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
