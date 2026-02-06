(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** WCETTypes.v
    Strategic Item #6: WCET (Worst-Case Execution Time) Types for RIINA

    Proves WCET soundness, composition, and bounds for a simple
    cost-annotated type system.

    Self-contained — Coq stdlib only.
    Spec: 01_RESEARCH/specs/RIINA_WCET_TYPES.md
*)

Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(** * Cost model: natural number of "ticks" *)
Definition cost := nat.

(** * Expressions with intrinsic cost *)
Inductive expr : Type :=
  | EConst : nat -> expr
  | EVar : nat -> expr
  | EPlus : expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | ESeq : expr -> expr -> expr.

(** * Environment *)
Definition env := list nat.

(** * Evaluation with cost tracking *)
Inductive eval : env -> expr -> nat -> cost -> Prop :=
  | EvalConst : forall e n, eval e (EConst n) n 1
  | EvalVar : forall e i v,
      nth_error e i = Some v ->
      eval e (EVar i) v 1
  | EvalPlus : forall e e1 e2 v1 v2 c1 c2,
      eval e e1 v1 c1 ->
      eval e e2 v2 c2 ->
      eval e (EPlus e1 e2) (v1 + v2) (c1 + c2 + 1)
  | EvalIfTrue : forall e ec et ef vc vt ct cc,
      eval e ec vc cc ->
      vc <> 0 ->
      eval e et vt ct ->
      eval e (EIf ec et ef) vt (cc + ct + 1)
  | EvalIfFalse : forall e ec et ef vc vf cf cc,
      eval e ec vc cc ->
      vc = 0 ->
      eval e ef vf cf ->
      eval e (EIf ec et ef) vf (cc + cf + 1)
  | EvalSeq : forall e e1 e2 v1 v2 c1 c2,
      eval e e1 v1 c1 ->
      eval e e2 v2 c2 ->
      eval e (ESeq e1 e2) v2 (c1 + c2).

(** * WCET bound computation *)
Fixpoint wcet_bound (ex : expr) : cost :=
  match ex with
  | EConst _ => 1
  | EVar _ => 1
  | EPlus e1 e2 => wcet_bound e1 + wcet_bound e2 + 1
  | EIf ec et ef => wcet_bound ec + Nat.max (wcet_bound et) (wcet_bound ef) + 1
  | ESeq e1 e2 => wcet_bound e1 + wcet_bound e2
  end.

(** * Theorem 1: WCET bound is always positive *)
Theorem wcet_positive : forall ex, 1 <= wcet_bound ex.
Proof.
  induction ex; simpl; lia.
Qed.

(** * Theorem 2: Actual cost is always positive *)
Theorem cost_positive : forall e ex v c,
  eval e ex v c -> 1 <= c.
Proof.
  intros. induction H; lia.
Qed.

(** * Theorem 3: WCET Soundness — actual cost never exceeds bound *)
Theorem wcet_sound : forall e ex v c,
  eval e ex v c -> c <= wcet_bound ex.
Proof.
  intros e ex v c H.
  induction H; simpl;
    try (assert (wcet_bound et <= Nat.max (wcet_bound et) (wcet_bound ef)) by apply Nat.le_max_l);
    try (assert (wcet_bound ef <= Nat.max (wcet_bound et) (wcet_bound ef)) by apply Nat.le_max_r);
    lia.
Qed.

(** * Theorem 4: Sequential composition WCET *)
Theorem wcet_seq_composition : forall e e1 e2 v1 v2 c1 c2,
  eval e e1 v1 c1 ->
  eval e e2 v2 c2 ->
  eval e (ESeq e1 e2) v2 (c1 + c2).
Proof.
  intros. econstructor; eauto.
Qed.

(** * Theorem 5: WCET bound of sequence is sum of bounds *)
Theorem wcet_seq_additive : forall e1 e2,
  wcet_bound (ESeq e1 e2) = wcet_bound e1 + wcet_bound e2.
Proof.
  intros. simpl. reflexivity.
Qed.

(** * Theorem 6: WCET bound of if is max of branches plus condition *)
Theorem wcet_if_max : forall ec et ef,
  wcet_bound (EIf ec et ef) = wcet_bound ec + Nat.max (wcet_bound et) (wcet_bound ef) + 1.
Proof.
  intros. simpl. reflexivity.
Qed.

(** * Theorem 7: Determinism of cost for deterministic evaluation *)
Theorem eval_deterministic : forall e ex v1 c1 v2 c2,
  eval e ex v1 c1 ->
  eval e ex v2 c2 ->
  v1 = v2 /\ c1 = c2.
Proof.
  intros e ex v1 c1 v2 c2 H1.
  generalize dependent c2. generalize dependent v2.
  induction H1; intros v2' c2' H2; inversion H2; subst;
    try (split; reflexivity);
    try congruence;
    try contradiction.
  all: repeat match goal with
       | [ IH: forall v c, eval ?env ?e v c -> _ /\ _,
           He: eval ?env ?e _ _ |- _ ] =>
         let Hv := fresh "Hv" in let Hc := fresh "Hc" in
         specialize (IH _ _ He); destruct IH as [Hv Hc]; subst
       end;
       try (split; [reflexivity | reflexivity]);
       try (split; [congruence | congruence]);
       try contradiction.
Qed.

(** * Theorem 8: Nested if WCET bound *)
Theorem wcet_nested_if_bound : forall ec1 ec2 et1 et2 ef1 ef2,
  wcet_bound (EIf ec1 (EIf ec2 et1 ef1) (EIf ec2 et2 ef2)) <=
  wcet_bound ec1 + wcet_bound ec2 +
  Nat.max (Nat.max (wcet_bound et1) (wcet_bound ef1))
          (Nat.max (wcet_bound et2) (wcet_bound ef2)) + 2.
Proof.
  intros. simpl. lia.
Qed.

(** * Theorem 9: WCET bound of Plus is additive plus one *)
Theorem wcet_plus_bound : forall e1 e2,
  wcet_bound (EPlus e1 e2) = wcet_bound e1 + wcet_bound e2 + 1.
Proof.
  intros. simpl. reflexivity.
Qed.

(** * Theorem 10: Cost of constant is exactly 1 *)
Theorem cost_const : forall e n v c,
  eval e (EConst n) v c -> c = 1.
Proof.
  intros. inversion H; subst. reflexivity.
Qed.

(** * Theorem 11: Cost of variable is exactly 1 *)
Theorem cost_var : forall e i v c,
  eval e (EVar i) v c -> c = 1.
Proof.
  intros. inversion H; subst. reflexivity.
Qed.

(** * Theorem 12: Constant evaluates to its value *)
Theorem const_eval_value : forall e n v c,
  eval e (EConst n) v c -> v = n.
Proof.
  intros. inversion H; subst. reflexivity.
Qed.

(** * Theorem 13: WCET bound is monotonic under Plus (left) *)
Theorem wcet_plus_mono_l : forall e1 e2,
  wcet_bound e1 <= wcet_bound (EPlus e1 e2).
Proof.
  intros. simpl. lia.
Qed.

(** * Theorem 14: WCET bound is monotonic under Plus (right) *)
Theorem wcet_plus_mono_r : forall e1 e2,
  wcet_bound e2 <= wcet_bound (EPlus e1 e2).
Proof.
  intros. simpl. lia.
Qed.

(** * Theorem 15: Seq cost is exactly sum of subexpression costs *)
Theorem seq_cost_sum : forall e e1 e2 v1 v2 c1 c2,
  eval e e1 v1 c1 ->
  eval e e2 v2 c2 ->
  exists c, eval e (ESeq e1 e2) v2 c /\ c = c1 + c2.
Proof.
  intros. exists (c1 + c2). split.
  - econstructor; eauto.
  - reflexivity.
Qed.

(** * Theorem 16: Cost of Plus is at least 3 *)
Theorem cost_plus_at_least_3 : forall e e1 e2 v c,
  eval e (EPlus e1 e2) v c -> c >= 3.
Proof.
  intros. inversion H; subst.
  assert (1 <= c1) by (eapply cost_positive; eauto).
  assert (1 <= c2) by (eapply cost_positive; eauto).
  lia.
Qed.

(** * Theorem 17: WCET of nested sequences *)
Theorem wcet_nested_seq : forall e1 e2 e3,
  wcet_bound (ESeq (ESeq e1 e2) e3) =
  wcet_bound e1 + wcet_bound e2 + wcet_bound e3.
Proof.
  intros. simpl. lia.
Qed.

(** * Theorem 18: WCET bound is at least 2 for Plus *)
Theorem wcet_plus_at_least_3 : forall e1 e2,
  wcet_bound (EPlus e1 e2) >= 3.
Proof.
  intros. simpl.
  assert (H1 := wcet_positive e1).
  assert (H2 := wcet_positive e2).
  lia.
Qed.

(** * Theorem 19: Evaluation cost never zero *)
Theorem cost_nonzero : forall e ex v c,
  eval e ex v c -> c > 0.
Proof.
  intros. apply cost_positive in H. lia.
Qed.

(** * Theorem 20: WCET bound of if is at least condition bound plus 1 *)
Theorem wcet_if_ge_cond : forall ec et ef,
  wcet_bound (EIf ec et ef) >= wcet_bound ec + 1.
Proof.
  intros. simpl. lia.
Qed.

(** * Theorem 21: Seq WCET is at least the WCET of its second part *)
Theorem wcet_seq_ge_right : forall e1 e2,
  wcet_bound (ESeq e1 e2) >= wcet_bound e2.
Proof.
  intros. simpl. lia.
Qed.

(** * Theorem 22: Seq WCET is at least the WCET of its first part *)
Theorem wcet_seq_ge_left : forall e1 e2,
  wcet_bound (ESeq e1 e2) >= wcet_bound e1.
Proof.
  intros. simpl. lia.
Qed.
