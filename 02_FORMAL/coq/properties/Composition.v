(** * Composition Properties for TERAS-LANG
    
    Compositionality of security properties.
    
    TODO: Define and prove composition lemmas.
*)

Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Typing.
Require Import TERAS.properties.SecurityProperties.
Require Import TERAS.properties.NonInterference.

(** ** Compositionality for Related Values *)

Lemma val_rel_pair : forall T1 T2 v1 v1' v2 v2',
  val_rel T1 v1 v1' ->
  val_rel T2 v2 v2' ->
  val_rel (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
  intros T1 T2 v1 v1' v2 v2' H1 H2.
  destruct H1 as [Hv1 [Hv1' [Hc1 [Hc1' Hrel1]]]].
  destruct H2 as [Hv2 [Hv2' [Hc2 [Hc2' Hrel2]]]].
  split.
  - apply VPair; assumption.
  - split.
    + apply VPair; assumption.
    + split.
      * apply closed_expr_pair; assumption.
      * split.
        -- apply closed_expr_pair; assumption.
        -- exists v1, v2, v1', v2'. repeat split; try reflexivity; assumption.
Qed.

Lemma val_rel_inl : forall T1 T2 v1 v2,
  val_rel T1 v1 v2 ->
  val_rel (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  intros T1 T2 v1 v2 Hrel.
  destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hrel']]]].
  split.
  - apply VInl. exact Hv1.
  - split.
    + apply VInl. exact Hv2.
    + split.
      * apply closed_expr_inl. exact Hc1.
      * split.
        -- apply closed_expr_inl. exact Hc2.
        -- left. exists v1, v2. repeat split; try reflexivity; exact Hrel'.
Qed.

Lemma val_rel_inr : forall T1 T2 v1 v2,
  val_rel T2 v1 v2 ->
  val_rel (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  intros T1 T2 v1 v2 Hrel.
  destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hrel']]]].
  split.
  - apply VInr. exact Hv1.
  - split.
    + apply VInr. exact Hv2.
    + split.
      * apply closed_expr_inr. exact Hc1.
      * split.
        -- apply closed_expr_inr. exact Hc2.
        -- right. exists v1, v2. repeat split; try reflexivity; exact Hrel'.
Qed.

(** ** Compositionality for Expressions *)

Lemma exp_rel_pair_values : forall T1 T2 v1 v1' v2 v2',
  val_rel T1 v1 v1' ->
  val_rel T2 v2 v2' ->
  exp_rel (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
  intros T1 T2 v1 v1' v2 v2' H1 H2.
  apply exp_rel_of_val_rel.
  apply val_rel_pair; assumption.
Qed.

Lemma exp_rel_inl_values : forall T1 T2 v1 v2,
  val_rel T1 v1 v2 ->
  exp_rel (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  intros T1 T2 v1 v2 Hrel.
  apply exp_rel_of_val_rel.
  apply val_rel_inl. exact Hrel.
Qed.

Lemma exp_rel_inr_values : forall T1 T2 v1 v2,
  val_rel T2 v1 v2 ->
  exp_rel (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  intros T1 T2 v1 v2 Hrel.
  apply exp_rel_of_val_rel.
  apply val_rel_inr. exact Hrel.
Qed.

(** End of Composition.v *)
