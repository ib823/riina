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
