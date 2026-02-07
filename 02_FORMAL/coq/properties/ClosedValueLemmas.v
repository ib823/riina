(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

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
Definition closed_expr_cv (e : expr) : Prop := forall x, ~ free_in x e.

(** Values are closed under empty context typing *)
Lemma value_typed_closed : forall Σ Δ v T ε,
  value v ->
  has_type nil Σ Δ v T ε ->
  closed_expr_cv v.
Proof.
  intros Σ Δ v T ε Hval Hty.
  unfold closed_expr_cv. intros x Hfree.
  destruct (free_in_context x v nil Σ Δ T ε Hfree Hty) as [T' Hlook].
  simpl in Hlook. discriminate.
Qed.

(** Closed expressions for compound types - decomposition *)
Lemma closed_pair_cv : forall e1 e2,
  closed_expr_cv (EPair e1 e2) <-> closed_expr_cv e1 /\ closed_expr_cv e2.
Proof.
  intros e1 e2. split.
  - intros Hc. split; unfold closed_expr_cv in *; intros x Hfree;
    apply (Hc x); simpl; [left | right]; exact Hfree.
  - intros [Hc1 Hc2]. unfold closed_expr_cv in *. intros x Hfree.
    simpl in Hfree. destruct Hfree as [H | H]; [apply (Hc1 x H) | apply (Hc2 x H)].
Qed.

Lemma closed_inl_cv : forall e T,
  closed_expr_cv (EInl e T) <-> closed_expr_cv e.
Proof.
  intros e T. split; unfold closed_expr_cv; intros Hc x Hfree.
  - apply (Hc x). simpl. exact Hfree.
  - simpl in Hfree. apply (Hc x). exact Hfree.
Qed.

Lemma closed_inr_cv : forall e T,
  closed_expr_cv (EInr e T) <-> closed_expr_cv e.
Proof.
  intros e T. split; unfold closed_expr_cv; intros Hc x Hfree.
  - apply (Hc x). simpl. exact Hfree.
  - simpl in Hfree. apply (Hc x). exact Hfree.
Qed.

Lemma closed_app_cv : forall e1 e2,
  closed_expr_cv (EApp e1 e2) <-> closed_expr_cv e1 /\ closed_expr_cv e2.
Proof.
  intros e1 e2. split.
  - intros Hc. split; unfold closed_expr_cv in *; intros x Hfree;
    apply (Hc x); simpl; [left | right]; exact Hfree.
  - intros [Hc1 Hc2]. unfold closed_expr_cv in *. intros x Hfree.
    simpl in Hfree. destruct Hfree as [H | H]; [apply (Hc1 x H) | apply (Hc2 x H)].
Qed.

(** Values: specific closed lemmas *)
Lemma closed_unit_cv : closed_expr_cv EUnit.
Proof. unfold closed_expr_cv. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_bool_cv : forall b, closed_expr_cv (EBool b).
Proof. intros b. unfold closed_expr_cv. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_int_cv : forall n, closed_expr_cv (EInt n).
Proof. intros n. unfold closed_expr_cv. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_string_cv : forall s, closed_expr_cv (EString s).
Proof. intros s. unfold closed_expr_cv. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_loc_cv : forall l, closed_expr_cv (ELoc l).
Proof. intros l. unfold closed_expr_cv. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

(** Lambda: bound variable can be free in body but not in lambda *)
Lemma closed_lam_body_cv : forall x T body y,
  closed_expr_cv (ELam x T body) ->
  free_in y body ->
  y = x.
Proof.
  intros x T body y Hclosed Hfree.
  unfold closed_expr_cv in Hclosed.
  destruct (String.eqb_spec y x) as [Heq | Hneq].
  - exact Heq.
  - exfalso. apply (Hclosed y). simpl. split; assumption.
Qed.

(** End of file - ZERO ADMITS *)
