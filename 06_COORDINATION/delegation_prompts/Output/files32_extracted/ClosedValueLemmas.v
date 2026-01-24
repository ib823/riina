(** * ClosedValueLemmas.v

    Lemmas about closed expressions and values.

    Key theorem: Values typed in empty context have no free variables.

    Mode: ULTRA KIASU | ZERO ADMITS
*)

Require Import String.
Require Import List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Preservation.
Import ListNotations.

(** Closed expression: no free variables *)
Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(** Values are closed under empty context typing *)
Lemma value_typed_closed : forall Σ Δ v T ε,
  value v ->
  has_type nil Σ Δ v T ε ->
  closed_expr v.
Proof.
  intros Σ Δ v T ε Hval Hty.
  unfold closed_expr. intros x Hfree.
  (* Use free_in_context from Preservation.v: if x is free in v, x must be in context *)
  (* But context is nil, so this is impossible *)
  destruct (free_in_context x v nil Σ Δ T ε Hfree Hty) as [T' Hlook].
  simpl in Hlook. discriminate.
Qed.

(** Substitution has no effect on closed expressions *)
Lemma subst_closed_noop : forall x v e,
  closed_expr e ->
  [x := v] e = e.
Proof.
  intros x v e Hclosed.
  induction e; simpl; try reflexivity.
  - (* EVar *)
    destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      exfalso. apply (Hclosed i). simpl. reflexivity.
    + reflexivity.
  - (* ELam *)
    destruct (String.eqb x i) eqn:Heq.
    + reflexivity.
    + f_equal. apply IHe.
      unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. split.
      * intro Heq'. subst. apply String.eqb_neq in Heq. contradiction.
      * exact Hy.
  - (* EApp *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EPair *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EFst *) f_equal. apply IHe. unfold closed_expr in *. exact Hclosed.
  - (* ESnd *) f_equal. apply IHe. unfold closed_expr in *. exact Hclosed.
  - (* EInl *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EInr *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* ECase *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + destruct (String.eqb x i) eqn:Heq1; [reflexivity|].
      apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. left.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq1. contradiction.
    + destruct (String.eqb x i0) eqn:Heq2; [reflexivity|].
      apply IHe3. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. right.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq2. contradiction.
  - (* EIf *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. left. exact Hy.
    + apply IHe3. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. right. exact Hy.
  - (* ELet *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq. contradiction.
  - (* EPerform *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EHandle *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq. contradiction.
  - (* ERef *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EDeref *) f_equal. apply IHe. unfold closed_expr in *. exact Hclosed.
  - (* EAssign *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EClassify *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EDeclassify *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EProve *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* ERequire *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EGrant *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
Qed.

(** Closed expressions for compound types *)
Lemma closed_pair : forall e1 e2,
  closed_expr (EPair e1 e2) <-> closed_expr e1 /\ closed_expr e2.
Proof.
  intros e1 e2. split.
  - intros Hc. split; unfold closed_expr in *; intros x Hfree;
    apply (Hc x); simpl; [left | right]; exact Hfree.
  - intros [Hc1 Hc2]. unfold closed_expr in *. intros x Hfree.
    simpl in Hfree. destruct Hfree as [H | H]; [apply (Hc1 x H) | apply (Hc2 x H)].
Qed.

Lemma closed_inl : forall e T,
  closed_expr (EInl e T) <-> closed_expr e.
Proof.
  intros e T. split.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    apply (Hc x). simpl. exact Hfree.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    simpl in Hfree. apply (Hc x). exact Hfree.
Qed.

Lemma closed_inr : forall e T,
  closed_expr (EInr e T) <-> closed_expr e.
Proof.
  intros e T. split.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    apply (Hc x). simpl. exact Hfree.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    simpl in Hfree. apply (Hc x). exact Hfree.
Qed.

(** Values: specific closed lemmas *)
Lemma closed_unit : closed_expr EUnit.
Proof. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_bool : forall b, closed_expr (EBool b).
Proof. intros b. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_int : forall n, closed_expr (EInt n).
Proof. intros n. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_string : forall s, closed_expr (EString s).
Proof. intros s. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_loc : forall l, closed_expr (ELoc l).
Proof. intros l. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

(** End of file - ZERO ADMITS *)
