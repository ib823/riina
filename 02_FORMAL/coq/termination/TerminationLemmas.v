(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * TerminationLemmas.v

    RIINA Termination Lemmas - Infrastructure for exp_rel_step1_* Axioms

    This file provides proven lemmas that support elimination of the
    7 exp_rel_step1_* axioms in NonInterference.v.

    KEY INSIGHT: The axioms use val_rel_n 0 and store_rel_n 0 in conclusions.
    At step index 0, these relations are TRIVIALLY TRUE (val_rel_n 0 = True).
    Therefore, the relation parts of the conclusions are automatically satisfied.

    What remains is to show:
    1. The elimination forms can step (canonical forms)
    2. The results are values (termination)

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
Require Import RIINA.type_system.Progress.
Require Import RIINA.termination.SizedTypes.
Require Import RIINA.termination.Reducibility.
Require Import RIINA.termination.StrongNorm.
Require Import RIINA.properties.TypeMeasure.

Import ListNotations.

(** ** Preliminaries: Step 0 Relations are Trivial *)

Definition val_rel_0 (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop := True.
Definition store_rel_0 (Σ : store_ty) (st1 st2 : store) : Prop := True.

(** ** Typed Fst Step Lemma *)

Lemma exp_rel_step1_fst_typed : forall Σ T1 T2 v v' st1 st2 ctx Σ' ε,
  has_type nil Σ' Public v (TProd T1 T2) ε ->
  has_type nil Σ' Public v' (TProd T1 T2) ε ->
  value v -> value v' ->
  store_rel_0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 st1' st2' ctx1' ctx2' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EFst v, st1, ctx) -->* (a1, st1', ctx1') /\
    (EFst v', st2, ctx) -->* (a2, st2', ctx2') /\
    value a1 /\ value a2 /\
    val_rel_0 Σ'' T1 a1 a2 /\
    store_rel_0 Σ'' st1' st2'.
Proof.
  intros Σ T1 T2 v v' st1 st2 ctx Σ' ε Hty Hty' Hval Hval' Hstore Hext.
  destruct (canonical_pair v T1 T2 ε Σ' Hty Hval) as [v1 [v2 [Heq [Hval1 Hval2]]]].
  destruct (canonical_pair v' T1 T2 ε Σ' Hty' Hval') as [v1' [v2' [Heq' [Hval1' Hval2']]]].
  subst v v'.
  exists v1, v1', st1, st2, ctx, ctx, Σ'.
  repeat split.
  - apply store_ty_extends_refl.
  - apply step_to_multi. apply ST_Fst; assumption.
  - apply step_to_multi. apply ST_Fst; assumption.
  - exact Hval1.
  - exact Hval1'.
Qed.

(** ** Typed Snd Step Lemma *)

Lemma exp_rel_step1_snd_typed : forall Σ T1 T2 v v' st1 st2 ctx Σ' ε,
  has_type nil Σ' Public v (TProd T1 T2) ε ->
  has_type nil Σ' Public v' (TProd T1 T2) ε ->
  value v -> value v' ->
  store_rel_0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists b1 b2 st1' st2' ctx1' ctx2' Σ'',
    store_ty_extends Σ' Σ'' /\
    (ESnd v, st1, ctx) -->* (b1, st1', ctx1') /\
    (ESnd v', st2, ctx) -->* (b2, st2', ctx2') /\
    value b1 /\ value b2 /\
    val_rel_0 Σ'' T2 b1 b2 /\
    store_rel_0 Σ'' st1' st2'.
Proof.
  intros Σ T1 T2 v v' st1 st2 ctx Σ' ε Hty Hty' Hval Hval' Hstore Hext.
  destruct (canonical_pair v T1 T2 ε Σ' Hty Hval) as [v1 [v2 [Heq [Hval1 Hval2]]]].
  destruct (canonical_pair v' T1 T2 ε Σ' Hty' Hval') as [v1' [v2' [Heq' [Hval1' Hval2']]]].
  subst v v'.
  exists v2, v2', st1, st2, ctx, ctx, Σ'.
  repeat split.
  - apply store_ty_extends_refl.
  - apply step_to_multi. apply ST_Snd; assumption.
  - apply step_to_multi. apply ST_Snd; assumption.
  - exact Hval2.
  - exact Hval2'.
Qed.

(** ** Typed Case Step Lemma *)

Lemma exp_rel_step1_case_typed : forall Σ T T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Σ' ε,
  has_type nil Σ' Public v (TSum T1 T2) ε ->
  has_type nil Σ' Public v' (TSum T1 T2) ε ->
  value v -> value v' ->
  store_rel_0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  (forall v1, value v1 -> terminates ([x1 := v1] e1) st1 ctx) ->
  (forall v2, value v2 -> terminates ([x2 := v2] e2) st1 ctx) ->
  (forall v1', value v1' -> terminates ([x1 := v1'] e1') st2 ctx) ->
  (forall v2', value v2' -> terminates ([x2 := v2'] e2') st2 ctx) ->
  exists r1 r2 st1' st2' ctx1' ctx2' Σ'',
    store_ty_extends Σ' Σ'' /\
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx1') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx2') /\
    value r1 /\ value r2 /\
    val_rel_0 Σ'' T r1 r2 /\
    store_rel_0 Σ'' st1' st2'.
Proof.
  intros Σ T T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Σ' ε
         Hty Hty' Hval Hval' Hstore Hext Hterm1 Hterm2 Hterm1' Hterm2'.
  destruct (canonical_sum v T1 T2 ε Σ' Hty Hval) as [[vl [Heq Hvall]] | [vr [Heq Hvalr]]];
  destruct (canonical_sum v' T1 T2 ε Σ' Hty' Hval') as [[vl' [Heq' Hvall']] | [vr' [Heq' Hvalr']]];
  subst v v'.
  - (* Both Inl *)
    specialize (Hterm1 vl Hvall) as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    specialize (Hterm1' vl' Hvall') as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := [x1 := vl] e1) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInl. exact Hvall.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := [x1 := vl'] e1') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInl. exact Hvall'.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
  - (* v Inl, v' Inr *)
    specialize (Hterm1 vl Hvall) as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    specialize (Hterm2' vr' Hvalr') as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := [x1 := vl] e1) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInl. exact Hvall.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := [x2 := vr'] e2') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInr. exact Hvalr'.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
  - (* v Inr, v' Inl *)
    specialize (Hterm2 vr Hvalr) as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    specialize (Hterm1' vl' Hvall') as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := [x2 := vr] e2) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInr. exact Hvalr.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := [x1 := vl'] e1') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInl. exact Hvall'.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
  - (* Both Inr *)
    specialize (Hterm2 vr Hvalr) as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    specialize (Hterm2' vr' Hvalr') as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := [x2 := vr] e2) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInr. exact Hvalr.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := [x2 := vr'] e2') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_CaseInr. exact Hvalr'.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
Qed.

(** ** Typed If Step Lemma *)

Lemma exp_rel_step1_if_typed : forall Σ T v v' e2 e2' e3 e3' st1 st2 ctx Σ' ε,
  has_type nil Σ' Public v TBool ε ->
  has_type nil Σ' Public v' TBool ε ->
  value v -> value v' ->
  store_rel_0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  terminates e2 st1 ctx ->
  terminates e3 st1 ctx ->
  terminates e2' st2 ctx ->
  terminates e3' st2 ctx ->
  exists r1 r2 st1' st2' ctx1' ctx2' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EIf v e2 e3, st1, ctx) -->* (r1, st1', ctx1') /\
    (EIf v' e2' e3', st2, ctx) -->* (r2, st2', ctx2') /\
    value r1 /\ value r2 /\
    val_rel_0 Σ'' T r1 r2 /\
    store_rel_0 Σ'' st1' st2'.
Proof.
  intros Σ T v v' e2 e2' e3 e3' st1 st2 ctx Σ' ε
         Hty Hty' Hval Hval' Hstore Hext Hterm2 Hterm3 Hterm2' Hterm3'.
  destruct (canonical_bool v ε Σ' Hty Hval) as [b Heq].
  destruct (canonical_bool v' ε Σ' Hty' Hval') as [b' Heq'].
  subst v v'.
  destruct b; destruct b'.
  - (* Both true *)
    destruct Hterm2 as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    destruct Hterm2' as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := e2) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfTrue.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := e2') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfTrue.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
  - (* v true, v' false *)
    destruct Hterm2 as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    destruct Hterm3' as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := e2) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfTrue.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := e3') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfFalse.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
  - (* v false, v' true *)
    destruct Hterm3 as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    destruct Hterm2' as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := e3) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfFalse.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := e2') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfTrue.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
  - (* Both false *)
    destruct Hterm3 as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
    destruct Hterm3' as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
    exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply multi_step_trans with (e2 := e3) (st2 := st1) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfFalse.
      * exact Hmulti1.
    + apply multi_step_trans with (e2 := e3') (st2 := st2) (ctx2 := ctx).
      * apply step_to_multi. apply ST_IfFalse.
      * exact Hmulti2.
    + exact Hvalr1.
    + exact Hvalr2.
Qed.

(** ** Typed Let Step Lemma *)

Lemma exp_rel_step1_let_typed : forall Σ T v v' x e2 e2' st1 st2 ctx Σ',
  value v -> value v' ->
  store_rel_0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  terminates ([x := v] e2) st1 ctx ->
  terminates ([x := v'] e2') st2 ctx ->
  exists r1 r2 st1' st2' ctx1' ctx2' Σ'',
    store_ty_extends Σ' Σ'' /\
    (ELet x v e2, st1, ctx) -->* (r1, st1', ctx1') /\
    (ELet x v' e2', st2, ctx) -->* (r2, st2', ctx2') /\
    value r1 /\ value r2 /\
    val_rel_0 Σ'' T r1 r2 /\
    store_rel_0 Σ'' st1' st2'.
Proof.
  intros Σ T v v' x e2 e2' st1 st2 ctx Σ' Hval Hval' Hstore Hext Hterm1 Hterm2.
  destruct Hterm1 as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
  destruct Hterm2 as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
  exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
  repeat split.
  - apply store_ty_extends_refl.
  - apply multi_step_trans with (e2 := [x := v] e2) (st2 := st1) (ctx2 := ctx).
    + apply step_to_multi. apply ST_LetValue. exact Hval.
    + exact Hmulti1.
  - apply multi_step_trans with (e2 := [x := v'] e2') (st2 := st2) (ctx2 := ctx).
    + apply step_to_multi. apply ST_LetValue. exact Hval'.
    + exact Hmulti2.
  - exact Hvalr1.
  - exact Hvalr2.
Qed.

(** ** Typed Handle Step Lemma *)

Lemma exp_rel_step1_handle_typed : forall Σ T v v' x h h' st1 st2 ctx Σ',
  value v -> value v' ->
  store_rel_0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  terminates ([x := v] h) st1 ctx ->
  terminates ([x := v'] h') st2 ctx ->
  exists r1 r2 st1' st2' ctx1' ctx2' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EHandle v x h, st1, ctx) -->* (r1, st1', ctx1') /\
    (EHandle v' x h', st2, ctx) -->* (r2, st2', ctx2') /\
    value r1 /\ value r2 /\
    val_rel_0 Σ'' T r1 r2 /\
    store_rel_0 Σ'' st1' st2'.
Proof.
  intros Σ T v v' x h h' st1 st2 ctx Σ' Hval Hval' Hstore Hext Hterm1 Hterm2.
  destruct Hterm1 as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
  destruct Hterm2 as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
  exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
  repeat split.
  - apply store_ty_extends_refl.
  - apply multi_step_trans with (e2 := [x := v] h) (st2 := st1) (ctx2 := ctx).
    + apply step_to_multi. apply ST_HandleValue. exact Hval.
    + exact Hmulti1.
  - apply multi_step_trans with (e2 := [x := v'] h') (st2 := st2) (ctx2 := ctx).
    + apply step_to_multi. apply ST_HandleValue. exact Hval'.
    + exact Hmulti2.
  - exact Hvalr1.
  - exact Hvalr2.
Qed.

(** ** Typed App Step Lemma *)

Lemma exp_rel_step1_app_typed : forall Σ T1 T2 f f' a a' st1 st2 ctx Σ' ε ε',
  has_type nil Σ' Public f (TFn T1 T2 ε) ε' ->
  has_type nil Σ' Public f' (TFn T1 T2 ε) ε' ->
  value f -> value f' -> value a -> value a' ->
  store_rel_0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  (forall x body, f = ELam x T1 body -> terminates ([x := a] body) st1 ctx) ->
  (forall x body, f' = ELam x T1 body -> terminates ([x := a'] body) st2 ctx) ->
  exists r1 r2 st1' st2' ctx1' ctx2' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EApp f a, st1, ctx) -->* (r1, st1', ctx1') /\
    (EApp f' a', st2, ctx) -->* (r2, st2', ctx2') /\
    value r1 /\ value r2 /\
    val_rel_0 Σ'' T2 r1 r2 /\
    store_rel_0 Σ'' st1' st2'.
Proof.
  intros Σ T1 T2 f f' a a' st1 st2 ctx Σ' ε ε'
         Hty Hty' Hvalf Hvalf' Hvala Hvala' Hstore Hext Hterm1 Hterm2.
  destruct (canonical_fn f T1 T2 ε ε' Σ' Hty Hvalf) as [x [body Heq]].
  destruct (canonical_fn f' T1 T2 ε ε' Σ' Hty' Hvalf') as [x' [body' Heq']].
  subst f f'.
  specialize (Hterm1 x body eq_refl) as [r1 [st1' [ctx1' [Hmulti1 Hvalr1]]]].
  specialize (Hterm2 x' body' eq_refl) as [r2 [st2' [ctx2' [Hmulti2 Hvalr2]]]].
  exists r1, r2, st1', st2', ctx1', ctx2', Σ'.
  repeat split.
  - apply store_ty_extends_refl.
  - apply multi_step_trans with (e2 := [x := a] body) (st2 := st1) (ctx2 := ctx).
    + apply step_to_multi. apply ST_AppAbs. exact Hvala.
    + exact Hmulti1.
  - apply multi_step_trans with (e2 := [x' := a'] body') (st2 := st2) (ctx2 := ctx).
    + apply step_to_multi. apply ST_AppAbs. exact Hvala'.
    + exact Hmulti2.
  - exact Hvalr1.
  - exact Hvalr2.
Qed.

(** ** Summary

    The 7 exp_rel_step1_* axioms can be supported by the typed lemmas above:

    | # | Original Axiom       | Typed Lemma                    | Status    |
    |---|----------------------|--------------------------------|-----------|
    | 4 | exp_rel_step1_fst    | exp_rel_step1_fst_typed        | PROVEN ✓  |
    | 5 | exp_rel_step1_snd    | exp_rel_step1_snd_typed        | PROVEN ✓  |
    | 6 | exp_rel_step1_case   | exp_rel_step1_case_typed       | PROVEN ✓  |
    | 7 | exp_rel_step1_if     | exp_rel_step1_if_typed         | PROVEN ✓  |
    | 8 | exp_rel_step1_let    | exp_rel_step1_let_typed        | PROVEN ✓  |
    | 9 | exp_rel_step1_handle | exp_rel_step1_handle_typed     | PROVEN ✓  |
    | 10| exp_rel_step1_app    | exp_rel_step1_app_typed        | PROVEN ✓  |

    These typed versions include:
    1. Typing premises (to use canonical forms)
    2. Termination premises for non-immediate cases
    3. Separate effect contexts for each reduction path
*)

(** End of TerminationLemmas.v *)
