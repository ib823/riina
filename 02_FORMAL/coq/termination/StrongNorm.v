(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * StrongNorm.v

    RIINA Strong Normalization Infrastructure

    This file provides termination lemmas needed to eliminate
    the exp_rel_step1_* axioms.

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
Require Import RIINA.termination.Reducibility.
Require Import RIINA.properties.TypeMeasure.

Import ListNotations.

(** ** Strong Normalization for Values

    All values are strongly normalizing because they cannot step.
*)

Theorem value_strongly_normalizing : forall v st ctx,
  value v -> SN st ctx v.
Proof.
  intros v st ctx Hval.
  apply value_SN. exact Hval.
Qed.

(** ** Multi-Step Termination Lemmas

    These lemmas show that specific expression forms eventually produce values.
*)

(** Fst on product value terminates in one step to a value *)
Lemma fst_terminates_to_value : forall v1 v2 st ctx,
  value v1 -> value v2 ->
  exists v st' ctx',
    (EFst (EPair v1 v2), st, ctx) -->* (v, st', ctx') /\
    value v /\ v = v1.
Proof.
  intros v1 v2 st ctx Hval1 Hval2.
  exists v1, st, ctx.
  split; [| split].
  - apply step_to_multi. apply ST_Fst; assumption.
  - assumption.
  - reflexivity.
Qed.

(** Snd on product value terminates in one step to a value *)
Lemma snd_terminates_to_value : forall v1 v2 st ctx,
  value v1 -> value v2 ->
  exists v st' ctx',
    (ESnd (EPair v1 v2), st, ctx) -->* (v, st', ctx') /\
    value v /\ v = v2.
Proof.
  intros v1 v2 st ctx Hval1 Hval2.
  exists v2, st, ctx.
  split; [| split].
  - apply step_to_multi. apply ST_Snd; assumption.
  - assumption.
  - reflexivity.
Qed.

(** If on bool terminates in one step to a branch *)
Lemma if_bool_terminates_once : forall b e2 e3 st ctx,
  exists e' st' ctx',
    (EIf (EBool b) e2 e3, st, ctx) -->* (e', st', ctx') /\
    st' = st /\ ctx' = ctx /\
    (b = true -> e' = e2) /\ (b = false -> e' = e3).
Proof.
  intros b e2 e3 st ctx.
  destruct b.
  - exists e2, st, ctx.
    split; [| split; [| split; [| split]]].
    + apply step_to_multi. apply ST_IfTrue.
    + reflexivity.
    + reflexivity.
    + intro. reflexivity.
    + intro Hcontra. discriminate.
  - exists e3, st, ctx.
    split; [| split; [| split; [| split]]].
    + apply step_to_multi. apply ST_IfFalse.
    + reflexivity.
    + reflexivity.
    + intro Hcontra. discriminate.
    + intro. reflexivity.
Qed.

(** Let with value terminates in one step to a substitution *)
Lemma let_terminates_once : forall x v e2 st ctx,
  value v ->
  exists e' st' ctx',
    (ELet x v e2, st, ctx) -->* (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros x v e2 st ctx Hval.
  exists ([x := v] e2), st, ctx.
  split; [| split].
  - apply step_to_multi. apply ST_LetValue. assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** Handle with value terminates in one step to a substitution *)
Lemma handle_terminates_once : forall x v h st ctx,
  value v ->
  exists e' st' ctx',
    (EHandle v x h, st, ctx) -->* (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros x v h st ctx Hval.
  exists ([x := v] h), st, ctx.
  split; [| split].
  - apply step_to_multi. apply ST_HandleValue. assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** App with lambda value terminates in one step to a substitution *)
Lemma app_lam_terminates_once : forall x T body v st ctx,
  value v ->
  exists e' st' ctx',
    (EApp (ELam x T body) v, st, ctx) -->* (e', st', ctx') /\
    st' = st /\ ctx' = ctx.
Proof.
  intros x T body v st ctx Hval.
  exists ([x := v] body), st, ctx.
  split; [| split].
  - apply step_to_multi. apply ST_AppAbs. assumption.
  - reflexivity.
  - reflexivity.
Qed.

(** ** Store Extension is Reflexive *)

Lemma store_ty_extends_refl : forall Σ,
  store_ty_extends Σ Σ.
Proof.
  intros Σ. unfold store_ty_extends.
  intros l T sl Hlookup.
  exact Hlookup.
Qed.

(** End of StrongNorm.v *)
