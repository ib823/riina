(** * Composition Properties for RIINA

    Compositionality of security properties.

    TODO: These proofs need refactoring after val_rel gained store_ty parameter.
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.SecurityProperties.
Require Import RIINA.properties.NonInterference.

(** ** Compositionality for Related Values *)

(* Composing relations for products *)
Lemma val_rel_pair : forall Σ T1 T2 v1 v1' v2 v2',
  val_rel Σ T1 v1 v1' ->
  val_rel Σ T2 v2 v2' ->
  val_rel Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
  intros Σ T1 T2 v1 v1' v2 v2' Hrel1 Hrel2.
  unfold val_rel in *. intro n.
  (* Use strong induction on n to handle the cumulative part *)
  induction n as [| n' IHn].
  - simpl. trivial.
  - simpl.
    (* Get value and closed from Hrel1 and Hrel2 at S n' *)
    specialize (Hrel1 (S n')) as Hrel1_Sn. specialize (Hrel2 (S n')) as Hrel2_Sn.
    simpl in Hrel1_Sn, Hrel2_Sn.
    destruct Hrel1_Sn as [_ [Hvalv1 [Hvalv1' [Hcl1 [Hcl1' Hrat1]]]]].
    destruct Hrel2_Sn as [_ [Hvalv2 [Hvalv2' [Hcl2 [Hcl2' Hrat2]]]]].
    (* Build the product relation *)
    split.
    { (* Cumulative part: val_rel_n n' (TProd T1 T2) ... *)
      (* Use the IH which gives us val_rel_n n' for the product *)
      exact IHn. }
    split; [constructor; assumption |].
    split; [constructor; assumption |].
    split.
    { intros y Hfree. simpl in Hfree.
      destruct Hfree as [Hfree | Hfree].
      - apply (Hcl1 y). exact Hfree.
      - apply (Hcl2 y). exact Hfree. }
    split.
    { intros y Hfree. simpl in Hfree.
      destruct Hfree as [Hfree | Hfree].
      - apply (Hcl1' y). exact Hfree.
      - apply (Hcl2' y). exact Hfree. }
    (* val_rel_at_type for TProd *)
    simpl. exists v1, v2, v1', v2'.
    repeat split; try reflexivity; assumption.
Qed.

Lemma val_rel_inl : forall Σ T1 T2 v1 v2,
  val_rel Σ T1 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  intros Σ T1 T2 v1 v2 Hrel.
  unfold val_rel in *. intro n.
  induction n as [| n' IHn].
  - simpl. trivial.
  - simpl.
    specialize (Hrel (S n')) as Hrel_Sn. simpl in Hrel_Sn.
    destruct Hrel_Sn as [_ [Hval1 [Hval2 [Hcl1 [Hcl2 Hrat]]]]].
    split.
    { (* Cumulative - use IH *) exact IHn. }
    split; [constructor; assumption |].
    split; [constructor; assumption |].
    split.
    { intros y Hfree. simpl in Hfree. apply (Hcl1 y). exact Hfree. }
    split.
    { intros y Hfree. simpl in Hfree. apply (Hcl2 y). exact Hfree. }
    simpl. left. exists v1, v2.
    repeat split; try reflexivity; assumption.
Qed.

Lemma val_rel_inr : forall Σ T1 T2 v1 v2,
  val_rel Σ T2 v1 v2 ->
  val_rel Σ (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  intros Σ T1 T2 v1 v2 Hrel.
  unfold val_rel in *. intro n.
  induction n as [| n' IHn].
  - simpl. trivial.
  - simpl.
    specialize (Hrel (S n')) as Hrel_Sn. simpl in Hrel_Sn.
    destruct Hrel_Sn as [_ [Hval1 [Hval2 [Hcl1 [Hcl2 Hrat]]]]].
    split.
    { (* Cumulative - use IH *) exact IHn. }
    split; [constructor; assumption |].
    split; [constructor; assumption |].
    split.
    { intros y Hfree. simpl in Hfree. apply (Hcl1 y). exact Hfree. }
    split.
    { intros y Hfree. simpl in Hfree. apply (Hcl2 y). exact Hfree. }
    simpl. right. exists v1, v2.
    repeat split; try reflexivity; assumption.
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
