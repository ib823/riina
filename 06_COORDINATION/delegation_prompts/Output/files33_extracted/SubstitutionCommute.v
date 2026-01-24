(** * SubstitutionCommute.v

    Substitution environment definitions and SAFE lemmas.
    
    IMPORTANT: subst_rho is a FUNCTION (ident -> expr), not a list!
    
    This file provides basic infrastructure lemmas.
    The full subst_subst_env_commute lemma is NOT proven here because
    the binder cases (ELam, ECase, ELet, EHandle) require complex
    capture-avoiding substitution reasoning.

    Mode: ULTRA KIASU | ZERO ADMITS
*)

Require Import String.
Require Import Bool.
Require Import List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Import ListNotations.

(** ----------------------------------------------------------------- *)
(** * Substitution Environment Definitions (Function-Based)           *)
(** ----------------------------------------------------------------- *)

(** Substitution environment: a FUNCTION from identifiers to expressions *)
Definition subst_rho := ident -> expr.

(** Identity substitution: maps each variable to itself *)
Definition id_rho : subst_rho := fun x => EVar x.

(** Extend substitution environment with a new binding *)
Definition extend_rho (ρ : subst_rho) (x : ident) (v : expr) : subst_rho :=
  fun y => if String.eqb y x then v else ρ y.

(** ----------------------------------------------------------------- *)
(** * Basic Lemmas about extend_rho                                   *)
(** ----------------------------------------------------------------- *)

(** Lookup the extended variable returns the new value *)
Lemma extend_rho_same : forall ρ x v,
  extend_rho ρ x v x = v.
Proof.
  intros ρ x v.
  unfold extend_rho.
  rewrite String.eqb_refl.
  reflexivity.
Qed.

(** Lookup a different variable returns the old environment's value *)
Lemma extend_rho_diff : forall ρ x y v,
  x <> y ->
  extend_rho ρ x v y = ρ y.
Proof.
  intros ρ x y v Hneq.
  unfold extend_rho.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq. 
    exfalso. apply Hneq. symmetry. exact Heq.
  - reflexivity.
Qed.

(** Shadow: extending with same variable twice keeps the latest *)
Lemma extend_rho_shadow : forall ρ x v1 v2,
  extend_rho (extend_rho ρ x v1) x v2 = extend_rho ρ x v2.
Proof.
  intros ρ x v1 v2.
  extensionality y.
  unfold extend_rho.
  destruct (String.eqb y x); reflexivity.
Qed.

(** Extending with different variables commutes *)
Lemma extend_rho_comm : forall ρ x y vx vy,
  x <> y ->
  extend_rho (extend_rho ρ x vx) y vy = extend_rho (extend_rho ρ y vy) x vx.
Proof.
  intros ρ x y vx vy Hneq.
  extensionality z.
  unfold extend_rho.
  destruct (String.eqb z y) eqn:Heqy;
  destruct (String.eqb z x) eqn:Heqx;
  try reflexivity.
  - (* z = y and z = x - contradiction since x <> y *)
    apply String.eqb_eq in Heqy.
    apply String.eqb_eq in Heqx.
    subst. exfalso. apply Hneq. reflexivity.
Qed.

(** ----------------------------------------------------------------- *)
(** * Identity Environment Properties                                 *)
(** ----------------------------------------------------------------- *)

(** id_rho returns the variable itself *)
Lemma id_rho_var : forall x, id_rho x = EVar x.
Proof.
  intros x. unfold id_rho. reflexivity.
Qed.

(** Extending id_rho with x -> EVar x is still id_rho on x *)
Lemma extend_id_rho_same : forall x,
  extend_rho id_rho x (EVar x) x = EVar x.
Proof.
  intros x.
  rewrite extend_rho_same. reflexivity.
Qed.

(** Extending id_rho with x -> EVar x behaves like id_rho on other vars *)
Lemma extend_id_rho_diff : forall x y,
  x <> y ->
  extend_rho id_rho x (EVar x) y = EVar y.
Proof.
  intros x y Hneq.
  rewrite extend_rho_diff.
  - unfold id_rho. reflexivity.
  - exact Hneq.
Qed.

(** ----------------------------------------------------------------- *)
(** * Closed Range Definition                                         *)
(** ----------------------------------------------------------------- *)

(** Import the closed expression definition *)
(** Note: We define locally to avoid import conflicts *)
Definition closed_expr_sc (e : expr) : Prop := forall x, ~ free_in x e.

(** A substitution environment has closed range if all its outputs are closed *)
(** Since ρ is a function, we express this as: for all x, ρ x is closed *)
Definition closed_rho (ρ : subst_rho) : Prop :=
  forall x, closed_expr_sc (ρ x).

(** id_rho does NOT have closed range (variables are free in themselves) *)
(** This is intentional - we need closed_rho for specific contexts *)

(** ----------------------------------------------------------------- *)
(** * Simple Substitution Lemmas (Non-Binder Cases)                   *)
(** ----------------------------------------------------------------- *)

(** These lemmas are about single-variable substitution [x := v] *)
(** They do NOT involve subst_env which has the complex binder handling *)

(** Substituting for a variable not free in the expression has no effect *)
(** This is the "not free" version - simpler than the "closed" version *)
Lemma subst_not_free : forall x v e,
  ~ free_in x e ->
  [x := v] e = e.
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
      * intro Heq'. subst. 
        apply String.eqb_neq in Heq. exact Heq.
      * exact Hfree.
  - (* EApp e1 e2 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + apply IHe2. intro Hfree. apply Hnotfree. simpl. right. exact Hfree.
  - (* EPair e1 e2 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + apply IHe2. intro Hfree. apply Hnotfree. simpl. right. exact Hfree.
  - (* EFst e *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* ESnd e *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EInl e t - 2 args: expr AND type *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EInr e t - 2 args: expr AND type *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* ECase e i e0 i0 e1 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + destruct (String.eqb x i) eqn:Heq1; [reflexivity|].
      apply IHe2. intro Hfree. apply Hnotfree. simpl. right. left. split.
      * intro Heq'. subst. apply String.eqb_neq in Heq1. exact Heq1.
      * exact Hfree.
    + destruct (String.eqb x i0) eqn:Heq2; [reflexivity|].
      apply IHe3. intro Hfree. apply Hnotfree. simpl. right. right. split.
      * intro Heq'. subst. apply String.eqb_neq in Heq2. exact Heq2.
      * exact Hfree.
  - (* EIf e1 e2 e3 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + apply IHe2. intro Hfree. apply Hnotfree. simpl. right. left. exact Hfree.
    + apply IHe3. intro Hfree. apply Hnotfree. simpl. right. right. exact Hfree.
  - (* ELet i e1 e2 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. intro Hfree. apply Hnotfree. simpl. right. split.
      * intro Heq'. subst. apply String.eqb_neq in Heq. exact Heq.
      * exact Hfree.
  - (* EPerform o e *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EHandle e i e0 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. intro Hfree. apply Hnotfree. simpl. right. split.
      * intro Heq'. subst. apply String.eqb_neq in Heq. exact Heq.
      * exact Hfree.
  - (* ERef e s - 2 args: expr AND security_level *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EDeref e *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EAssign e1 e2 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + apply IHe2. intro Hfree. apply Hnotfree. simpl. right. exact Hfree.
  - (* EClassify s e - Note: security_level THEN expr *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EDeclassify e1 e2 *)
    f_equal.
    + apply IHe1. intro Hfree. apply Hnotfree. simpl. left. exact Hfree.
    + apply IHe2. intro Hfree. apply Hnotfree. simpl. right. exact Hfree.
  - (* EProve p e *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* ERequire p e *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
  - (* EGrant c e *)
    f_equal. apply IHe. intro Hfree. apply Hnotfree. simpl. exact Hfree.
Qed.

(** ----------------------------------------------------------------- *)
(** * Variable Substitution Identity                                  *)
(** ----------------------------------------------------------------- *)

(** Substituting a variable with itself has no effect *)
Lemma subst_var_same : forall x e,
  [x := EVar x] e = e.
Proof.
  intros x e.
  induction e; simpl; try reflexivity.
  - (* EVar i *)
    destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst. reflexivity.
    + reflexivity.
  - (* ELam *)
    destruct (String.eqb x i) eqn:Heq.
    + reflexivity.
    + f_equal. exact IHe.
  - (* EApp *) f_equal; assumption.
  - (* EPair *) f_equal; assumption.
  - (* EFst *) f_equal; assumption.
  - (* ESnd *) f_equal; assumption.
  - (* EInl *) f_equal; assumption.
  - (* EInr *) f_equal; assumption.
  - (* ECase *)
    f_equal; [exact IHe1 | |].
    + destruct (String.eqb x i) eqn:Heq; [reflexivity | exact IHe2].
    + destruct (String.eqb x i0) eqn:Heq; [reflexivity | exact IHe3].
  - (* EIf *) f_equal; assumption.
  - (* ELet *)
    f_equal; [exact IHe1 |].
    destruct (String.eqb x i) eqn:Heq; [reflexivity | exact IHe2].
  - (* EPerform *) f_equal; assumption.
  - (* EHandle *)
    f_equal; [exact IHe1 |].
    destruct (String.eqb x i) eqn:Heq; [reflexivity | exact IHe2].
  - (* ERef *) f_equal; assumption.
  - (* EDeref *) f_equal; assumption.
  - (* EAssign *) f_equal; assumption.
  - (* EClassify *) f_equal; assumption.
  - (* EDeclassify *) f_equal; assumption.
  - (* EProve *) f_equal; assumption.
  - (* ERequire *) f_equal; assumption.
  - (* EGrant *) f_equal; assumption.
Qed.

(** ----------------------------------------------------------------- *)
(** * Substitution on Closed Expressions                              *)
(** ----------------------------------------------------------------- *)

(** If an expression is closed, substitution has no effect *)
Lemma subst_closed : forall x v e,
  closed_expr_sc e ->
  [x := v] e = e.
Proof.
  intros x v e Hclosed.
  apply subst_not_free.
  unfold closed_expr_sc in Hclosed.
  apply Hclosed.
Qed.

(** ----------------------------------------------------------------- *)
(** * Base Type Closed Lemmas                                         *)
(** ----------------------------------------------------------------- *)

Lemma closed_unit_sc : closed_expr_sc EUnit.
Proof. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_bool_sc : forall b, closed_expr_sc (EBool b).
Proof. intros b. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_int_sc : forall n, closed_expr_sc (EInt n).
Proof. intros n. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_string_sc : forall s, closed_expr_sc (EString s).
Proof. intros s. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_loc_sc : forall l, closed_expr_sc (ELoc l).
Proof. intros l. unfold closed_expr_sc. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

(** ----------------------------------------------------------------- *)
(** * NOTE: Full Commutation Lemma NOT Proven                         *)
(** ----------------------------------------------------------------- *)

(** The lemma subst_subst_env_commute:
    
    [x := v] (subst_env ρ e) = subst_env (extend_rho ρ x v) e
    
    requires complex reasoning about capture-avoiding substitution
    in the binder cases (ELam, ECase, ELet, EHandle).
    
    This is admitted in ReducibilityFull.v and should be handled
    by Claude Code, not proven here.
    
    The lemmas in this file provide the infrastructure needed
    for that proof without attempting the hard cases.
*)

(** End of file - ZERO ADMITS *)
