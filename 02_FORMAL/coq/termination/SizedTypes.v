(** * SizedTypes.v

    RIINA Sized Types Infrastructure for Termination Proofs

    This file provides sized type annotations and well-founded measures
    for proving strong normalization and termination properties.

    KEY INSIGHT: For the exp_rel_step1_* axioms, we need to show that
    elimination forms (fst, snd, case, if, let, handle, app) applied to
    values can always make progress. This follows from:
    1. Canonical forms: values have expected structure
    2. Step rules: elimination forms step when applied to canonical forms
    3. Type preservation: results maintain typing

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_β (Beta)
    Phase: 3 (Termination)
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.LexOrder.

Import ListNotations.

(** ** Sized Type Annotations

    A sized type is a type annotated with a size bound that decreases
    across recursive calls. This enables termination checking.
*)

(** Sized type: type with size annotation *)
Inductive sized_ty : Type :=
  | STBase : ty -> sized_ty              (* Base type with implicit size *)
  | STSized : nat -> ty -> sized_ty      (* Type with explicit size bound *)
  .

(** Extract base type from sized type *)
Definition sized_ty_base (st : sized_ty) : ty :=
  match st with
  | STBase T => T
  | STSized _ T => T
  end.

(** Extract size bound from sized type (0 if unspecified) *)
Definition sized_ty_bound (st : sized_ty) : nat :=
  match st with
  | STBase _ => 0
  | STSized n _ => n
  end.

(** ** Termination Measure

    The termination measure for a well-typed expression is based on:
    1. The step index (for step-indexed proofs)
    2. The type size (for structural recursion on types)
    3. The expression size (for structural recursion on expressions)
*)

(** Expression size *)
Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EUnit => 1
  | EBool _ => 1
  | EInt _ => 1
  | EString _ => 1
  | EVar _ => 1
  | ELam _ _ body => 1 + expr_size body
  | EApp e1 e2 => 1 + expr_size e1 + expr_size e2
  | EPair e1 e2 => 1 + expr_size e1 + expr_size e2
  | EFst e => 1 + expr_size e
  | ESnd e => 1 + expr_size e
  | EInl e _ => 1 + expr_size e
  | EInr e _ => 1 + expr_size e
  | ECase e _ e1 _ e2 => 1 + expr_size e + expr_size e1 + expr_size e2
  | EIf e1 e2 e3 => 1 + expr_size e1 + expr_size e2 + expr_size e3
  | ELet _ e1 e2 => 1 + expr_size e1 + expr_size e2
  | ERef e _ => 1 + expr_size e
  | EDeref e => 1 + expr_size e
  | EAssign e1 e2 => 1 + expr_size e1 + expr_size e2
  | ELoc _ => 1
  | EPerform _ e => 1 + expr_size e
  | EHandle e _ h => 1 + expr_size e + expr_size h
  | EClassify e => 1 + expr_size e
  | EDeclassify e1 e2 => 1 + expr_size e1 + expr_size e2
  | EProve e => 1 + expr_size e
  | ERequire _ e => 1 + expr_size e
  | EGrant _ e => 1 + expr_size e
  end.

(** Expression size is positive *)
Lemma expr_size_pos : forall e, expr_size e > 0.
Proof.
  induction e; simpl; lia.
Qed.

(** ** Reducibility Measure

    For proving strong normalization, we use a reducibility interpretation.
    An expression is reducible if it terminates and all its reducts are reducible.
*)

(** Number of reduction steps to value (None if doesn't terminate) *)
(* Note: This is only well-defined for terminating expressions *)

(** Terminating expression predicate *)
Definition terminates (e : expr) (st : store) (ctx : effect_ctx) : Prop :=
  exists v st' ctx', (e, st, ctx) -->* (v, st', ctx') /\ value v.

(** Single step terminates predicate *)
Definition step_terminates (e : expr) (st : store) (ctx : effect_ctx) : Prop :=
  exists e' st' ctx', (e, st, ctx) --> (e', st', ctx').

(** ** Value Decomposition for Elimination Forms

    These lemmas show how values decompose for each elimination form.
    They are the key to proving the exp_rel_step1_* axioms.
*)

(** If v is a value of product type, it decomposes as a pair *)
Lemma value_prod_decompose : forall v T1 T2 ε Σ,
  has_type nil Σ Public v (TProd T1 T2) ε ->
  value v ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros v T1 T2 ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists v1, v2. split; [reflexivity | split; assumption].
Qed.

(** If v is a value of sum type, it decomposes as Inl or Inr *)
Lemma value_sum_decompose : forall v T1 T2 ε Σ,
  has_type nil Σ Public v (TSum T1 T2) ε ->
  value v ->
  (exists v', v = EInl v' T2 /\ value v') \/
  (exists v', v = EInr v' T1 /\ value v').
Proof.
  intros v T1 T2 ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  - left. exists v0. split; [reflexivity | assumption].
  - right. exists v0. split; [reflexivity | assumption].
Qed.

(** If v is a value of bool type, it decomposes as true or false *)
Lemma value_bool_decompose : forall v ε Σ,
  has_type nil Σ Public v TBool ε ->
  value v ->
  exists b, v = EBool b.
Proof.
  intros v ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists b. reflexivity.
Qed.

(** If v is a value of function type, it decomposes as a lambda *)
Lemma value_fn_decompose : forall v T1 T2 ε ε' Σ,
  has_type nil Σ Public v (TFn T1 T2 ε) ε' ->
  value v ->
  exists x body, v = ELam x T1 body.
Proof.
  intros v T1 T2 ε ε' Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists x, e. reflexivity.
Qed.

(** ** Single-Step Progress for Elimination Forms

    These lemmas show that elimination forms applied to values
    can always take exactly one step.
*)

(** Fst of a pair steps in one step *)
Lemma fst_steps_once : forall v1 v2 st ctx,
  value v1 -> value v2 ->
  (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx).
Proof.
  intros. apply ST_Fst; assumption.
Qed.

(** Snd of a pair steps in one step *)
Lemma snd_steps_once : forall v1 v2 st ctx,
  value v1 -> value v2 ->
  (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx).
Proof.
  intros. apply ST_Snd; assumption.
Qed.

(** Case on Inl steps in one step *)
Lemma case_inl_steps_once : forall v T x1 e1 x2 e2 st ctx,
  value v ->
  (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx).
Proof.
  intros. apply ST_CaseInl; assumption.
Qed.

(** Case on Inr steps in one step *)
Lemma case_inr_steps_once : forall v T x1 e1 x2 e2 st ctx,
  value v ->
  (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx).
Proof.
  intros. apply ST_CaseInr; assumption.
Qed.

(** If true steps in one step *)
Lemma if_true_steps_once : forall e2 e3 st ctx,
  (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx).
Proof.
  intros. apply ST_IfTrue.
Qed.

(** If false steps in one step *)
Lemma if_false_steps_once : forall e2 e3 st ctx,
  (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx).
Proof.
  intros. apply ST_IfFalse.
Qed.

(** Let with value steps in one step *)
Lemma let_value_steps_once : forall x v e2 st ctx,
  value v ->
  (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx).
Proof.
  intros. apply ST_LetValue; assumption.
Qed.

(** Handle with value steps in one step *)
Lemma handle_value_steps_once : forall v x h st ctx,
  value v ->
  (EHandle v x h, st, ctx) --> ([x := v] h, st, ctx).
Proof.
  intros. apply ST_HandleValue; assumption.
Qed.

(** App with lambda and value steps in one step *)
Lemma app_lam_steps_once : forall x T body v st ctx,
  value v ->
  (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx).
Proof.
  intros. apply ST_AppAbs; assumption.
Qed.

(** ** Multi-Step Inclusion

    Single step implies multi-step.
*)

Lemma step_to_multi : forall e st ctx e' st' ctx',
  (e, st, ctx) --> (e', st', ctx') ->
  (e, st, ctx) -->* (e', st', ctx').
Proof.
  intros.
  apply MS_Step with (cfg2 := (e', st', ctx')).
  - exact H.
  - apply MS_Refl.
Qed.

(** Multi-step is transitive *)
Lemma multi_step_trans : forall e1 st1 ctx1 e2 st2 ctx2 e3 st3 ctx3,
  (e1, st1, ctx1) -->* (e2, st2, ctx2) ->
  (e2, st2, ctx2) -->* (e3, st3, ctx3) ->
  (e1, st1, ctx1) -->* (e3, st3, ctx3).
Proof.
  intros e1 st1 ctx1 e2 st2 ctx2 e3 st3 ctx3 H1 H2.
  induction H1.
  - exact H2.
  - apply MS_Step with cfg2; [exact H | apply IHmulti_step; exact H2].
Qed.

(** End of SizedTypes.v *)
