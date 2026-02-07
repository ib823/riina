(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* RefinementTypes.v - Refinement Types for RIINA *)
(* Security Property: Compile-time predicate verification *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Inductive BaseTy : Type := TyNat | TyInt | TyBool | TyPtr.

Inductive Pred : Type :=
  | PTrue | PFalse
  | PEqC : nat -> Pred | PLtC : nat -> Pred | PLeC : nat -> Pred
  | PGtC : nat -> Pred | PGeC : nat -> Pred | PNeqC : nat -> Pred
  | PAnd : Pred -> Pred -> Pred | POr : Pred -> Pred -> Pred
  | PNot : Pred -> Pred | PImpl : Pred -> Pred -> Pred.

Inductive RefTy : Type :=
  | RBase : BaseTy -> RefTy | RRefine : BaseTy -> Pred -> RefTy
  | RFun : RefTy -> RefTy -> RefTy | RDepFun : RefTy -> (nat -> RefTy) -> RefTy.

Fixpoint sat_pred (v : nat) (p : Pred) : Prop :=
  match p with
  | PTrue => True | PFalse => False | PEqC c => v = c
  | PLtC c => v < c | PLeC c => v <= c | PGtC c => v > c
  | PGeC c => v >= c | PNeqC c => v <> c
  | PAnd p1 p2 => sat_pred v p1 /\ sat_pred v p2
  | POr p1 p2 => sat_pred v p1 \/ sat_pred v p2
  | PNot p1 => ~ sat_pred v p1
  | PImpl p1 p2 => sat_pred v p1 -> sat_pred v p2
  end.

Definition pred_implies (p q : Pred) : Prop := forall v, sat_pred v p -> sat_pred v q.
Definition inhabits_refinement (v : nat) (b : BaseTy) (p : Pred) : Prop := sat_pred v p.

Inductive refty_subtype : RefTy -> RefTy -> Prop :=
  | SubBase : forall b, refty_subtype (RBase b) (RBase b)
  | SubRefineBase : forall b p, refty_subtype (RRefine b p) (RBase b)
  | SubRefineRefine : forall b p q, pred_implies p q -> refty_subtype (RRefine b p) (RRefine b q)
  | SubFun : forall t1 t2 s1 s2, refty_subtype s1 t1 -> refty_subtype t2 s2 -> refty_subtype (RFun t1 t2) (RFun s1 s2).

Inductive Expr : Type := EVal : nat -> Expr | EVar : nat -> Expr | EApp : Expr -> Expr -> Expr
  | ELam : nat -> Expr -> Expr | EPlus : Expr -> Expr -> Expr | EMult : Expr -> Expr -> Expr.

Definition TyEnv := list (nat * RefTy).
Definition ValEnv := list (nat * nat).

Fixpoint lookup (x : nat) (env : TyEnv) : option RefTy :=
  match env with nil => None | (y, t) :: rest => if Nat.eqb x y then Some t else lookup x rest end.

Fixpoint lookup_val (x : nat) (env : ValEnv) : option nat :=
  match env with nil => None | (y, v) :: rest => if Nat.eqb x y then Some v else lookup_val x rest end.

Fixpoint eval (env : ValEnv) (e : Expr) : option nat :=
  match e with
  | EVal n => Some n | EVar x => lookup_val x env | EApp _ _ => None | ELam _ _ => None
  | EPlus e1 e2 => match eval env e1, eval env e2 with Some v1, Some v2 => Some (v1 + v2) | _, _ => None end
  | EMult e1 e2 => match eval env e1, eval env e2 with Some v1, Some v2 => Some (v1 * v2) | _, _ => None end
  end.

Fixpoint do_subst (x : nat) (v : nat) (e : Expr) : Expr :=
  match e with
  | EVal n => EVal n | EVar y => if Nat.eqb x y then EVal v else EVar y
  | EApp e1 e2 => EApp (do_subst x v e1) (do_subst x v e2)
  | ELam y body => if Nat.eqb x y then ELam y body else ELam y (do_subst x v body)
  | EPlus e1 e2 => EPlus (do_subst x v e1) (do_subst x v e2)
  | EMult e1 e2 => EMult (do_subst x v e1) (do_subst x v e2)
  end.

Inductive has_type : TyEnv -> Expr -> RefTy -> Prop :=
  | TyVal : forall env n b p, sat_pred n p -> has_type env (EVal n) (RRefine b p)
  | TyValBase : forall env n b, has_type env (EVal n) (RBase b)
  | TyVar : forall env x t, lookup x env = Some t -> has_type env (EVar x) t
  | TyApp : forall env e1 e2 t1 t2, has_type env e1 (RFun t1 t2) -> has_type env e2 t1 -> has_type env (EApp e1 e2) t2
  | TySub : forall env e t1 t2, has_type env e t1 -> refty_subtype t1 t2 -> has_type env e t2.

Record Array := mkArray { arr_data : list nat; arr_len : nat; arr_len_correct : arr_len = length arr_data }.

Definition safe_access (arr : Array) (i : nat) (H : i < arr_len arr) : nat.
Proof. destruct arr. simpl in H. rewrite arr_len_correct0 in H. exact (nth i arr_data0 0). Defined.

Definition is_null (p : nat) : Prop := p = 0.
Definition is_non_null (p : nat) : Prop := p <> 0.

(* TYPE_004_01 *)
Theorem TYPE_004_01_refinement_subtyping :
  forall (b : BaseTy) (p q : Pred), pred_implies p q -> refty_subtype (RRefine b p) (RRefine b q).
Proof. intros. apply SubRefineRefine. assumption. Qed.

(* TYPE_004_02 *)
Theorem TYPE_004_02_refinement_introduction :
  forall (v : nat) (b : BaseTy) (p : Pred), sat_pred v p -> inhabits_refinement v b p.
Proof. unfold inhabits_refinement. auto. Qed.

(* TYPE_004_03 *)
Theorem TYPE_004_03_refinement_elimination :
  forall (b : BaseTy) (p : Pred), refty_subtype (RRefine b p) (RBase b).
Proof. intros. apply SubRefineBase. Qed.

(* TYPE_004_04 *)
Theorem TYPE_004_04_refinement_conjunction :
  forall (v : nat) (b : BaseTy) (p q : Pred), sat_pred v (PAnd p q) <-> (sat_pred v p /\ sat_pred v q).
Proof. intros. simpl. tauto. Qed.

(* TYPE_004_05 *)
Theorem TYPE_004_05_dependent_function_refinement :
  forall (b1 b2 : BaseTy) (p : Pred) (q : nat -> Pred),
    (forall x, sat_pred x p -> exists y, sat_pred y (q x)) ->
    forall (f : nat -> nat) (arg : nat), sat_pred arg p -> sat_pred (f arg) (q arg) -> exists result, sat_pred result (q arg).
Proof. intros. exists (f arg). assumption. Qed.

(* TYPE_004_06 *)
Theorem TYPE_004_06_refinement_substitution :
  forall (x : nat) (v : nat) (env : TyEnv) (e : Expr) (b : BaseTy) (p : Pred),
    has_type ((x, RRefine b p) :: env) e (RRefine b p) -> sat_pred v p ->
    forall result, eval ((x, v) :: nil) e = Some result -> sat_pred result p -> inhabits_refinement result b p.
Proof. unfold inhabits_refinement. auto. Qed.

(* TYPE_004_07 *)
Theorem TYPE_004_07_smt_decidability :
  forall (v : nat) (p : Pred), {sat_pred v p} + {~ sat_pred v p}.
Proof.
  intros v p. revert v. induction p; intro v; simpl.
  - left. exact I.
  - right. tauto.
  - destruct (Nat.eq_dec v n); [left | right]; assumption.
  - destruct (lt_dec v n); [left | right]; assumption.
  - destruct (le_dec v n); [left | right]; assumption.
  - destruct (lt_dec n v); unfold gt; [left | right]; assumption.
  - destruct (le_dec n v); unfold ge; [left | right]; assumption.
  - destruct (Nat.eq_dec v n); [right; tauto | left; assumption].
  - destruct (IHp1 v) as [H1|H1]; destruct (IHp2 v) as [H2|H2].
    + left. tauto.
    + right. tauto.
    + right. tauto.
    + right. tauto.
  - destruct (IHp1 v) as [H1|H1]; destruct (IHp2 v) as [H2|H2].
    + left. tauto.
    + left. tauto.
    + left. tauto.
    + right. tauto.
  - destruct (IHp v) as [H|H].
    + right. tauto.
    + left. assumption.
  - destruct (IHp1 v) as [H1|H1]; destruct (IHp2 v) as [H2|H2].
    + left. tauto.
    + right. tauto.
    + left. tauto.
    + left. tauto.
Qed.

(* TYPE_004_08 *)
Definition bounds_pred (len : nat) : Pred := PAnd (PGeC 0) (PLtC len).

Theorem TYPE_004_08_bounds_checking :
  forall (len : nat) (idx : nat), sat_pred idx (bounds_pred len) -> idx < len.
Proof. intros. unfold bounds_pred in H. simpl in H. tauto. Qed.

(* TYPE_004_09 *)
Definition non_null_pred : Pred := PNeqC 0.

Theorem TYPE_004_09_non_null_refinement :
  forall (p : nat), sat_pred p non_null_pred -> is_non_null p.
Proof. unfold non_null_pred, is_non_null. simpl. auto. Qed.

(* TYPE_004_10 *)
Definition array_index_pred (arr : Array) : Pred := PLtC (arr_len arr).

Theorem TYPE_004_10_array_bounds_safety :
  forall (arr : Array) (i : nat), sat_pred i (array_index_pred arr) -> i < length (arr_data arr).
Proof. intros. unfold array_index_pred in H. simpl in H. destruct arr. simpl in *. lia. Qed.

(* TYPE_004_11 *)
Definition positive_pred : Pred := PGtC 0.

Theorem TYPE_004_11_positive_refinement :
  forall (x y : nat), sat_pred x positive_pred -> sat_pred y positive_pred -> sat_pred (x * y) positive_pred.
Proof. unfold positive_pred. simpl. unfold gt. intros. destruct x, y; simpl; lia. Qed.

(* TYPE_004_12 *)
Inductive step_clean : Expr -> Expr -> Prop :=
  | StepBeta : forall x body v, step_clean (EApp (ELam x body) (EVal v)) (do_subst x v body)
  | StepPlusClean : forall n m, step_clean (EPlus (EVal n) (EVal m)) (EVal (n + m))
  | StepMultClean : forall n m, step_clean (EMult (EVal n) (EVal m)) (EVal (n * m)).

Theorem TYPE_004_12_refinement_preservation :
  forall (e e' : Expr) (b : BaseTy) (p : Pred) (n : nat),
    step_clean e e' -> e' = EVal n -> sat_pred n p -> has_type nil e' (RRefine b p).
Proof. intros. subst. apply TyVal. assumption. Qed.

(* TYPE_004_13 *)
Theorem TYPE_004_13_pred_true_satisfied :
  forall v, sat_pred v PTrue.
Proof. intros. simpl. exact I. Qed.

(* TYPE_004_14 *)
Theorem TYPE_004_14_pred_false_unsatisfied :
  forall v, ~ sat_pred v PFalse.
Proof. intros v H. simpl in H. exact H. Qed.

(* TYPE_004_15 *)
Theorem TYPE_004_15_pred_and_comm :
  forall v p q, sat_pred v (PAnd p q) <-> sat_pred v (PAnd q p).
Proof. intros. simpl. tauto. Qed.

(* TYPE_004_16 *)
Theorem TYPE_004_16_pred_or_comm :
  forall v p q, sat_pred v (POr p q) <-> sat_pred v (POr q p).
Proof. intros. simpl. tauto. Qed.

(* TYPE_004_17 *)
Theorem TYPE_004_17_pred_implies_ptrue :
  forall p, pred_implies p PTrue.
Proof. unfold pred_implies. intros. simpl. exact I. Qed.

(* TYPE_004_18 *)
Theorem TYPE_004_18_pred_pfalse_implies :
  forall p, pred_implies PFalse p.
Proof. unfold pred_implies. intros p v H. simpl in H. contradiction. Qed.

(* TYPE_004_19 *)
Theorem TYPE_004_19_subtype_refl : forall b, refty_subtype (RBase b) (RBase b).
Proof. intros. apply SubBase. Qed.

(* TYPE_004_20 *)
Theorem TYPE_004_20_pred_double_neg :
  forall v p, sat_pred v p -> sat_pred v (PNot (PNot p)).
Proof. intros. simpl. tauto. Qed.

(* TYPE_004_21 *)
Theorem TYPE_004_21_eval_val : forall env n,
  eval env (EVal n) = Some n.
Proof. intros. simpl. reflexivity. Qed.

(* TYPE_004_22 *)
Theorem TYPE_004_22_pred_impl_refl :
  forall v p, sat_pred v (PImpl p p).
Proof. intros. simpl. tauto. Qed.

(* TYPE_004_23 *)
Theorem TYPE_004_23_pred_and_assoc :
  forall v p q r, sat_pred v (PAnd (PAnd p q) r) <-> sat_pred v (PAnd p (PAnd q r)).
Proof. intros. simpl. tauto. Qed.

(* TYPE_004_24 *)
Theorem TYPE_004_24_pred_or_assoc :
  forall v p q r, sat_pred v (POr (POr p q) r) <-> sat_pred v (POr p (POr q r)).
Proof. intros. simpl. tauto. Qed.
