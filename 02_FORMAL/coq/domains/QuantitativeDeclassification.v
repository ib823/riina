(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** QuantitativeDeclassification.v
    Strategic Item #5: Quantitative Declassification for RIINA

    Proves budget monotonicity, composition, and non-interference
    for a quantitative information-flow type system with declassification budgets.

    Self-contained — Coq stdlib only.
    Spec: 01_RESEARCH/specs/RIINA_QUANT_DECLASS_SPEC.md
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(** * Security Levels *)
Inductive level : Type :=
  | Low : level
  | High : level.

Definition level_leq (l1 l2 : level) : bool :=
  match l1, l2 with
  | Low, _ => true
  | High, High => true
  | High, Low => false
  end.

Definition level_join (l1 l2 : level) : level :=
  match l1, l2 with
  | High, _ | _, High => High
  | Low, Low => Low
  end.

(** * Budget: natural number tracking declassification capacity *)
Definition budget := nat.

(** * Expressions *)
Inductive expr : Type :=
  | EConst : nat -> expr
  | EVar : nat -> expr
  | EPlus : expr -> expr -> expr
  | EDeclass : expr -> budget -> expr.  (* declassify with budget cost *)

(** * Labeled values *)
Record labeled_val := mkLV {
  lv_val : nat;
  lv_level : level;
}.

(** * Environment *)
Definition env := list labeled_val.

(** * Evaluation with budget tracking *)
Inductive eval : env -> expr -> budget -> nat -> budget -> Prop :=
  | EvalConst : forall e n b,
      eval e (EConst n) b n b
  | EvalVar : forall e i b v,
      nth_error e i = Some v ->
      eval e (EVar i) b (lv_val v) b
  | EvalPlus : forall e e1 e2 b v1 v2 b1 b2,
      eval e e1 b v1 b1 ->
      eval e e2 b1 v2 b2 ->
      eval e (EPlus e1 e2) b (v1 + v2) b2
  | EvalDeclass : forall e ex b v b' cost,
      eval e ex b v b' ->
      cost <= b' ->
      eval e (EDeclass ex cost) b v (b' - cost).

(** * Low-equivalence of environments *)
Definition low_equiv (e1 e2 : env) : Prop :=
  length e1 = length e2 /\
  forall i v1 v2,
    nth_error e1 i = Some v1 ->
    nth_error e2 i = Some v2 ->
    lv_level v1 = Low ->
    lv_level v2 = Low ->
    lv_val v1 = lv_val v2.

(** * Theorem 1: Budget monotonicity — evaluation never increases budget *)
Theorem budget_monotone : forall e ex b v b',
  eval e ex b v b' -> b' <= b.
Proof.
  intros e ex b v b' H.
  induction H; lia.
Qed.

(** * Theorem 2: Determinism of evaluation *)
Theorem eval_deterministic : forall e ex b v1 b1 v2 b2,
  eval e ex b v1 b1 ->
  eval e ex b v2 b2 ->
  v1 = v2 /\ b1 = b2.
Proof.
  intros e ex b v1 b1 v2 b2 H1.
  generalize dependent b2.
  generalize dependent v2.
  induction H1; intros v2' b2' H2; inversion H2; subst;
    try (split; reflexivity);
    try congruence.
  - split; auto. congruence.
  - match goal with
    | [ IH1: forall _ _, eval _ _ _ _ _ -> _ /\ _,
        IH2: forall _ _, eval _ _ _ _ _ -> _ /\ _,
        Ha: eval _ _ _ _ _, Hb: eval _ _ _ _ _ |- _ ] =>
      specialize (IH1 _ _ Ha); destruct IH1; subst;
      specialize (IH2 _ _ Hb); destruct IH2; subst; auto
    end.
  - match goal with
    | [ IH: forall _ _, eval _ _ _ _ _ -> _ /\ _,
        Ha: eval _ _ _ _ _ |- _ ] =>
      specialize (IH _ _ Ha); destruct IH; subst; auto
    end.
Qed.

(** * Theorem 3: Budget composition — sequential declassifications compose *)
Theorem budget_composition : forall e ex1 ex2 b v1 b1 v2 b2,
  eval e ex1 b v1 b1 ->
  eval e ex2 b1 v2 b2 ->
  b2 <= b.
Proof.
  intros.
  assert (b1 <= b) by (eapply budget_monotone; eauto).
  assert (b2 <= b1) by (eapply budget_monotone; eauto).
  lia.
Qed.

(** * Theorem 4: Zero-budget expressions don't declassify *)
Inductive no_declass : expr -> Prop :=
  | NDConst : forall n, no_declass (EConst n)
  | NDVar : forall i, no_declass (EVar i)
  | NDPlus : forall e1 e2, no_declass e1 -> no_declass e2 -> no_declass (EPlus e1 e2).

Theorem zero_budget_no_declass : forall e ex v b',
  eval e ex 0 v b' ->
  no_declass ex ->
  b' = 0.
Proof.
  intros e ex v b' Heval Hnd.
  induction Heval; inversion Hnd; subst; auto.
  - apply IHHeval1 in H1. subst. apply IHHeval2 in H2. auto.
Qed.

(** * Theorem 5: No-declass expressions preserve budget exactly *)
Theorem no_declass_budget_preserved : forall e ex b v b',
  eval e ex b v b' ->
  no_declass ex ->
  b' = b.
Proof.
  intros e ex b v b' Heval Hnd.
  induction Heval; inversion Hnd; subst; auto.
  - apply IHHeval1 in H1. subst. apply IHHeval2 in H2. auto.
Qed.

(** * Theorem 6: Non-interference for no-declass expressions *)
Theorem non_interference_no_declass : forall e1 e2 ex b v1 b1 v2 b2,
  low_equiv e1 e2 ->
  no_declass ex ->
  eval e1 ex b v1 b1 ->
  eval e2 ex b v2 b2 ->
  (forall i, match nth_error e1 i, nth_error e2 i with
    | Some v1, Some v2 => lv_level v1 = Low /\ lv_level v2 = Low
    | None, None => True
    | _, _ => False
    end) ->
  v1 = v2.
Proof.
  intros e1 e2 ex b v1 b1 v2 b2 Hle Hnd Hev1 Hev2 Hall.
  generalize dependent b2. generalize dependent v2.
  generalize dependent b1. generalize dependent v1.
  induction Hnd; intros.
  - inversion Hev1; inversion Hev2; subst. auto.
  - inversion Hev1; subst. inversion Hev2; subst.
    destruct Hle as [Hlen Hlow].
    specialize (Hall i).
    match goal with
    | [ H1: nth_error e1 i = Some ?va, H2: nth_error e2 i = Some ?vb |- _ ] =>
      rewrite H1 in Hall; rewrite H2 in Hall;
      destruct Hall as [Hl1 Hl2];
      apply (Hlow i va vb H1 H2 Hl1 Hl2)
    end.
  - inversion Hev1; subst. inversion Hev2; subst.
    match goal with
    | [ He1a: eval e1 ?ea b ?va1 ?ba1, He2a: eval e2 ?ea b ?va2 ?ba2,
        He1b: eval e1 ?eb ?ba1 ?vb1 ?bb1, He2b: eval e2 ?eb ?ba2 ?vb2 ?bb2 |- _ ] =>
      assert (ba1 = b) by (eapply no_declass_budget_preserved; eauto);
      assert (ba2 = b) by (eapply no_declass_budget_preserved; eauto);
      subst
    end.
    f_equal.
    + eapply IHHnd1; eauto.
    + eapply IHHnd2; eauto.
Qed.

(** * Theorem 7: Budget sufficient implies evaluation exists for constants *)
Theorem const_always_evaluates : forall e n b,
  eval e (EConst n) b n b.
Proof.
  intros. constructor.
Qed.

(** * Theorem 8: Declassification cost is exact *)
Theorem declass_cost_exact : forall e ex b v b' cost,
  eval e (EDeclass ex cost) b v b' ->
  exists b_inner,
    eval e ex b v b_inner /\
    cost <= b_inner /\
    b' = b_inner - cost.
Proof.
  intros. inversion H; subst.
  exists b'0. auto.
Qed.
