(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * SubstitutionCommute.v

    Substitution environment definitions and SAFE lemmas.
    
    Mode: Comprehensive Verification | Zero Admits
*)

Require Import String.
Require Import Bool.
Require Import List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Import ListNotations.

(** ----------------------------------------------------------------- *)
(** * Substitution Environment Definitions (Function-Based)           *)
(** ----------------------------------------------------------------- *)

Definition subst_rho_sc := ident -> expr.
Definition id_rho_sc : subst_rho_sc := fun x => EVar x.
Definition extend_rho_sc (ρ : subst_rho_sc) (x : ident) (v : expr) : subst_rho_sc :=
  fun y => if String.eqb y x then v else ρ y.

(** ----------------------------------------------------------------- *)
(** * Basic Lemmas about extend_rho                                   *)
(** ----------------------------------------------------------------- *)

Lemma extend_rho_sc_same : forall ρ x v,
  extend_rho_sc ρ x v x = v.
Proof.
  intros ρ x v. unfold extend_rho_sc.
  rewrite String.eqb_refl. reflexivity.
Qed.

Lemma extend_rho_sc_diff : forall ρ x y v,
  x <> y -> extend_rho_sc ρ x v y = ρ y.
Proof.
  intros ρ x y v Hneq. unfold extend_rho_sc.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq. symmetry in Heq. contradiction.
  - reflexivity.
Qed.

Lemma extend_rho_sc_shadow : forall ρ x v1 v2,
  extend_rho_sc (extend_rho_sc ρ x v1) x v2 = extend_rho_sc ρ x v2.
Proof.
  intros ρ x v1 v2. extensionality y.
  unfold extend_rho_sc. destruct (String.eqb y x); reflexivity.
Qed.

Lemma extend_rho_sc_comm : forall ρ x y vx vy,
  x <> y ->
  extend_rho_sc (extend_rho_sc ρ x vx) y vy = extend_rho_sc (extend_rho_sc ρ y vy) x vx.
Proof.
  intros ρ x y vx vy Hneq. extensionality z.
  unfold extend_rho_sc.
  destruct (String.eqb z y) eqn:Heqy; destruct (String.eqb z x) eqn:Heqx;
  try reflexivity.
  apply String.eqb_eq in Heqy. apply String.eqb_eq in Heqx.
  subst. contradiction.
Qed.

(** ----------------------------------------------------------------- *)
(** * Closed Range Definition                                         *)
(** ----------------------------------------------------------------- *)

Definition closed_expr_sc (e : expr) : Prop := forall x, ~ free_in x e.
Definition closed_rho_sc (ρ : subst_rho_sc) : Prop := forall x, closed_expr_sc (ρ x).

(** ----------------------------------------------------------------- *)
(** * Substitution Lemmas                                             *)
(** ----------------------------------------------------------------- *)

Lemma subst_not_free_sc : forall x v e,
  ~ free_in x e -> [x := v] e = e.
Proof.
  intros x v e Hnotfree.
  induction e; simpl; try reflexivity.
  - (* EVar i *)
    destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      exfalso. apply Hnotfree. simpl. reflexivity.
    + reflexivity.
  - (* ELam i t e *)
    destruct (String.eqb x i) eqn:Heq.
    + reflexivity.
    + f_equal. apply IHe.
      intro Hfree. apply Hnotfree. simpl. split.
      * intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
      * exact Hfree.
  - (* EApp *) f_equal; [apply IHe1 | apply IHe2];
      intro Hfree; apply Hnotfree; simpl; [left | right]; exact Hfree.
  - (* EPair *) f_equal; [apply IHe1 | apply IHe2];
      intro Hfree; apply Hnotfree; simpl; [left | right]; exact Hfree.
  - (* EFst *) f_equal. apply IHe. exact Hnotfree.
  - (* ESnd *) f_equal. apply IHe. exact Hnotfree.
  - (* EInl *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EInr *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* ECase *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + destruct (String.eqb x i) eqn:Heq1; [reflexivity|].
      apply IHe2. intro Hfree. apply Hnotfree. simpl. right. left. split.
      * intro Heq'. subst. rewrite String.eqb_refl in Heq1. discriminate.
      * exact Hfree.
    + destruct (String.eqb x i0) eqn:Heq2; [reflexivity|].
      apply IHe3. intro Hfree. apply Hnotfree. simpl. right. right. split.
      * intro Heq'. subst. rewrite String.eqb_refl in Heq2. discriminate.
      * exact Hfree.
  - (* EIf *) f_equal; [apply IHe1 | apply IHe2 | apply IHe3];
      intro Hfree; apply Hnotfree; simpl; [left | right; left | right; right]; exact Hfree.
  - (* ELet *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. intro Hfree. apply Hnotfree. simpl. right. split.
      * intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
      * exact Hfree.
  - (* EPerform *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EHandle *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. intro Hfree. apply Hnotfree. simpl. right. split.
      * intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
      * exact Hfree.
  - (* ERef *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EDeref *) f_equal. apply IHe. exact Hnotfree.
  - (* EAssign *) f_equal; [apply IHe1 | apply IHe2];
      intro Hfree; apply Hnotfree; simpl; [left | right]; exact Hfree.
  - (* EClassify *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EDeclassify *) f_equal; [apply IHe1 | apply IHe2];
      intro Hfree; apply Hnotfree; simpl; [left | right]; exact Hfree.
  - (* EProve *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* ERequire *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EGrant *) f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
Qed.

Lemma subst_closed_sc : forall x v e,
  closed_expr_sc e -> [x := v] e = e.
Proof.
  intros x v e Hclosed. apply subst_not_free_sc. apply Hclosed.
Qed.

(** Base type closed lemmas *)
Lemma closed_unit_sub : closed_expr_sc EUnit.
Proof. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_bool_sub : forall b, closed_expr_sc (EBool b).
Proof. intros b. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_int_sub : forall n, closed_expr_sc (EInt n).
Proof. intros n. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_string_sub : forall s, closed_expr_sc (EString s).
Proof. intros s. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_loc_sub : forall l, closed_expr_sc (ELoc l).
Proof. intros l. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

(** End of file - ZERO ADMITS *)
