(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** * Reducibility.v

    RIINA Reducibility Infrastructure for Termination Proofs

    This file provides the foundation for proving termination properties
    needed to eliminate the exp_rel_step1_* axioms.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_β (Beta)
    Phase: 3 (Termination)
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.termination.SizedTypes.
Require Import RIINA.properties.TypeMeasure.

Import ListNotations.

(** ** Strong Normalization Definition

    An expression is strongly normalizing if all reduction sequences
    starting from it are finite.
*)

(** SN defined as accessibility in the step relation *)
Inductive SN (st : store) (ctx : effect_ctx) : expr -> Prop :=
  | SN_intro : forall e,
      (forall e' st' ctx',
        (e, st, ctx) --> (e', st', ctx') ->
        SN st' ctx' e') ->
      SN st ctx e.

(** Alternative characterization *)
Definition strongly_normalizing (e : expr) (st : store) (ctx : effect_ctx) : Prop :=
  SN st ctx e.

(** Values are strongly normalizing (no reduction possible) *)
Lemma value_SN : forall v st ctx,
  value v -> SN st ctx v.
Proof.
  intros v st ctx Hval.
  apply SN_intro.
  intros e' st' ctx' Hstep.
  exfalso.
  eapply value_not_step; eauto.
Qed.

(** SN is closed under single-step reduction *)
Lemma SN_step : forall e e' st st' ctx ctx',
  SN st ctx e ->
  (e, st, ctx) --> (e', st', ctx') ->
  SN st' ctx' e'.
Proof.
  intros e e' st st' ctx ctx' HSN Hstep.
  inversion HSN; subst.
  apply H. exact Hstep.
Qed.

(** ** Typed Elimination Lemmas

    These lemmas show that elimination forms on well-typed values
    produce results that eventually become values.
*)

(** Fst on typed product value steps to a value in one step *)
Lemma fst_typed_steps_to_value : forall v T1 T2 ε Σ st ctx,
  has_type nil Σ Public v (TProd T1 T2) ε ->
  value v ->
  exists v1 st' ctx',
    (EFst v, st, ctx) --> (v1, st', ctx') /\
    value v1 /\
    st' = st /\ ctx' = ctx.
Proof.
  intros v T1 T2 ε Σ st ctx Hty Hval.
  destruct (value_prod_decompose v T1 T2 ε Σ Hty Hval) as [v1 [v2 [Heq [Hval1 Hval2]]]].
  subst v.
  exists v1, st, ctx.
  split; [| split; [| split]].
  - apply ST_Fst; assumption.
  - assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** Snd on typed product value steps to a value in one step *)
Lemma snd_typed_steps_to_value : forall v T1 T2 ε Σ st ctx,
  has_type nil Σ Public v (TProd T1 T2) ε ->
  value v ->
  exists v2 st' ctx',
    (ESnd v, st, ctx) --> (v2, st', ctx') /\
    value v2 /\
    st' = st /\ ctx' = ctx.
Proof.
  intros v T1 T2 ε Σ st ctx Hty Hval.
  destruct (value_prod_decompose v T1 T2 ε Σ Hty Hval) as [v1 [v2 [Heq [Hval1 Hval2]]]].
  subst v.
  exists v2, st, ctx.
  split; [| split; [| split]].
  - apply ST_Snd; assumption.
  - assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** Case on typed sum value steps in one step *)
Lemma case_typed_steps_once : forall v T1 T2 ε Σ x1 e1 x2 e2 st ctx,
  has_type nil Σ Public v (TSum T1 T2) ε ->
  value v ->
  exists e' st' ctx',
    (ECase v x1 e1 x2 e2, st, ctx) --> (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros v T1 T2 ε Σ x1 e1 x2 e2 st ctx Hty Hval.
  destruct (value_sum_decompose v T1 T2 ε Σ Hty Hval) as [[v' [Heq Hval']] | [v' [Heq Hval']]].
  - subst v.
    exists ([x1 := v'] e1), st, ctx.
    split; [| split].
    + apply ST_CaseInl. assumption.
    + reflexivity.
    + reflexivity.
  - subst v.
    exists ([x2 := v'] e2), st, ctx.
    split; [| split].
    + apply ST_CaseInr. assumption.
    + reflexivity.
    + reflexivity.
Qed.

(** If on typed bool value steps in one step *)
Lemma if_typed_steps_once : forall v ε Σ e2 e3 st ctx,
  has_type nil Σ Public v TBool ε ->
  value v ->
  exists e' st' ctx',
    (EIf v e2 e3, st, ctx) --> (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros v ε Σ e2 e3 st ctx Hty Hval.
  destruct (value_bool_decompose v ε Σ Hty Hval) as [b Heq].
  subst v.
  destruct b.
  - exists e2, st, ctx. split; [apply ST_IfTrue | split; reflexivity].
  - exists e3, st, ctx. split; [apply ST_IfFalse | split; reflexivity].
Qed.

(** Let with value steps in one step *)
Lemma let_typed_steps_once : forall v x e2 st ctx,
  value v ->
  exists e' st' ctx',
    (ELet x v e2, st, ctx) --> (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros v x e2 st ctx Hval.
  exists ([x := v] e2), st, ctx.
  split; [| split].
  - apply ST_LetValue. assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** Handle with value steps in one step *)
Lemma handle_typed_steps_once : forall v x h st ctx,
  value v ->
  exists e' st' ctx',
    (EHandle v x h, st, ctx) --> (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros v x h st ctx Hval.
  exists ([x := v] h), st, ctx.
  split; [| split].
  - apply ST_HandleValue. assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** App with typed function value steps in one step *)
Lemma app_typed_steps_once : forall f T1 T2 ε ε' Σ a st ctx,
  has_type nil Σ Public f (TFn T1 T2 ε) ε' ->
  value f ->
  value a ->
  exists e' st' ctx',
    (EApp f a, st, ctx) --> (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros f T1 T2 ε ε' Σ a st ctx Hty Hvalf Hvala.
  destruct (value_fn_decompose f T1 T2 ε ε' Σ Hty Hvalf) as [x [body Heq]].
  subst f.
  exists ([x := a] body), st, ctx.
  split; [| split].
  - apply ST_AppAbs. assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** End of Reducibility.v *)
