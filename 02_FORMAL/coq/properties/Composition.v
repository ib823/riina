(** * Composition Properties for RIINA

    Compositionality of security properties.

    TODO: These proofs need refactoring after val_rel gained store_ty parameter.
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.SecurityProperties.
Require Import RIINA.properties.NonInterference.

(** ** Compositionality for Related Values *)

(* TODO: Refactor after val_rel signature change *)
Lemma val_rel_pair : forall Σ T1 T2 v1 v1' v2 v2',
  val_rel Σ T1 v1 v1' ->
  val_rel Σ T2 v2 v2' ->
  val_rel Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
Admitted.

Lemma val_rel_inl : forall Σ T1 T2 v1 v2,
  val_rel Σ T1 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
Admitted.

Lemma val_rel_inr : forall Σ T1 T2 v1 v2,
  val_rel Σ T2 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
Admitted.

(** ** Compositionality for Expressions *)

Lemma exp_rel_pair_values : forall Σ T1 T2 v1 v1' v2 v2',
  val_rel Σ T1 v1 v1' ->
  val_rel Σ T2 v2 v2' ->
  exp_rel Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
Admitted.

Lemma exp_rel_inl_values : forall Σ T1 T2 v1 v2,
  val_rel Σ T1 v1 v2 ->
  exp_rel Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
Admitted.

Lemma exp_rel_inr_values : forall Σ T1 T2 v1 v2,
  val_rel Σ T2 v1 v2 ->
  exp_rel Σ (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
Admitted.

(** End of Composition.v *)
