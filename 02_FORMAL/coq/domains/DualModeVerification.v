(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** * DualModeVerification.v
    Strategic Item #2: Dual-Mode Verification
    Lightweight refinement types + Full Coq proofs.

    Models a refinement type system with two checking modes:
    - Lightweight (decidable, boolean-valued)
    - Full (Prop-based)

    Proves soundness, completeness for decidable fragments, and
    structural properties of refinement subtyping. *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Program.Basics.
Import ListNotations.

(** ** 1. Refinement predicates and types *)

(** A refinement predicate has both a propositional and a boolean face. *)
Record RefinementPred : Type := mkRefinement {
  full_pred : nat -> Prop;
  light_pred : nat -> bool;
  light_sound : forall n, light_pred n = true -> full_pred n;
}.

(** A refined type: base nat with a refinement predicate. *)
Definition RefinedType := RefinementPred.

(** ** 2. Expression language *)

Inductive expr : Type :=
  | EConst : nat -> expr
  | EPlus : expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr.

(** Evaluation (total, deterministic). *)
Fixpoint eval (e : expr) : nat :=
  match e with
  | EConst n => n
  | EPlus e1 e2 => eval e1 + eval e2
  | EIf guard et ef => if Nat.eqb (eval guard) 0 then eval ef else eval et
  end.

(** ** 3. Checking modes *)

Definition lightweight_check (rt : RefinedType) (v : nat) : bool :=
  light_pred rt v.

Definition full_check (rt : RefinedType) (v : nat) : Prop :=
  full_pred rt v.

(** ** 4. Decidable predicate: one where the boolean is both sound and complete. *)

Definition decidable_refinement (rt : RefinedType) : Prop :=
  forall n, full_pred rt n <-> light_pred rt n = true.

(** ** 5. Refinement subtyping *)

Definition refine_subtype (r1 r2 : RefinedType) : Prop :=
  forall n, full_pred r1 n -> full_pred r2 n.

(** ** 6. Conjunction of refinements *)

Definition refine_conj (r1 r2 : RefinedType) : RefinedType :=
  mkRefinement
    (fun n => full_pred r1 n /\ full_pred r2 n)
    (fun n => light_pred r1 n && light_pred r2 n)
    (fun n H =>
       let P := andb_prop _ _ H in
       conj (light_sound r1 n (proj1 P)) (light_sound r2 n (proj2 P))).

(** ** Theorems *)

(** Theorem 1: Lightweight checking is sound. *)
Theorem lightweight_sound : forall (rt : RefinedType) (v : nat),
  lightweight_check rt v = true -> full_check rt v.
Proof.
  intros rt v H.
  unfold lightweight_check, full_check in *.
  apply (light_sound rt). exact H.
Qed.

(** Theorem 2: For decidable predicates, lightweight is complete. *)
Theorem lightweight_complete_decidable : forall (rt : RefinedType) (v : nat),
  decidable_refinement rt ->
  full_check rt v -> lightweight_check rt v = true.
Proof.
  intros rt v Hdec Hfull.
  unfold lightweight_check, full_check in *.
  apply Hdec. exact Hfull.
Qed.

(** Theorem 3: Refinement subtyping is reflexive. *)
Theorem refine_subtype_refl : forall (rt : RefinedType),
  refine_subtype rt rt.
Proof.
  intros rt n H. exact H.
Qed.

(** Theorem 4: Refinement subtyping is transitive. *)
Theorem refine_subtype_trans : forall (r1 r2 r3 : RefinedType),
  refine_subtype r1 r2 ->
  refine_subtype r2 r3 ->
  refine_subtype r1 r3.
Proof.
  intros r1 r2 r3 H12 H23 n H1.
  apply H23. apply H12. exact H1.
Qed.

(** Theorem 5: Checked values satisfy their refinements. *)
Theorem checked_values_satisfy : forall (rt : RefinedType) (e : expr),
  lightweight_check rt (eval e) = true ->
  full_check rt (eval e).
Proof.
  intros rt e H.
  apply lightweight_sound. exact H.
Qed.

(** Theorem 6: Dual-mode agrees on decidable predicates. *)
Theorem dual_mode_agreement : forall (rt : RefinedType) (v : nat),
  decidable_refinement rt ->
  (lightweight_check rt v = true <-> full_check rt v).
Proof.
  intros rt v Hdec.
  split.
  - apply lightweight_sound.
  - apply lightweight_complete_decidable. exact Hdec.
Qed.

(** Theorem 7: Weakening — stronger refinement implies weaker. *)
Theorem refinement_weakening : forall (r1 r2 : RefinedType) (v : nat),
  refine_subtype r1 r2 ->
  full_check r1 v ->
  full_check r2 v.
Proof.
  intros r1 r2 v Hsub Hfull.
  apply Hsub. exact Hfull.
Qed.

(** Theorem 8: Conjunction subtype left projection. *)
Theorem conj_subtype_left : forall (r1 r2 : RefinedType),
  refine_subtype (refine_conj r1 r2) r1.
Proof.
  intros r1 r2 n [H1 _]. exact H1.
Qed.

(** Theorem 9: Conjunction subtype right projection. *)
Theorem conj_subtype_right : forall (r1 r2 : RefinedType),
  refine_subtype (refine_conj r1 r2) r2.
Proof.
  intros r1 r2 n [_ H2]. exact H2.
Qed.

(** Theorem 10: Conjunction is the greatest lower bound. *)
Theorem conj_greatest_lower_bound : forall (r1 r2 r3 : RefinedType),
  refine_subtype r3 r1 ->
  refine_subtype r3 r2 ->
  refine_subtype r3 (refine_conj r1 r2).
Proof.
  intros r1 r2 r3 H31 H32 n H3.
  split; [apply H31 | apply H32]; exact H3.
Qed.

(** Theorem 11: Conjunction is commutative on full_pred *)
Theorem conj_full_pred_comm : forall (r1 r2 : RefinedType) (v : nat),
  full_pred (refine_conj r1 r2) v <-> full_pred (refine_conj r2 r1) v.
Proof.
  intros. simpl. tauto.
Qed.

(** Theorem 12: Conjunction is associative on full_pred *)
Theorem conj_full_pred_assoc : forall (r1 r2 r3 : RefinedType) (v : nat),
  full_pred (refine_conj (refine_conj r1 r2) r3) v <->
  full_pred (refine_conj r1 (refine_conj r2 r3)) v.
Proof.
  intros. simpl. tauto.
Qed.

(** Theorem 13: Conjunction light_pred is AND *)
Theorem conj_light_is_andb : forall (r1 r2 : RefinedType) (v : nat),
  light_pred (refine_conj r1 r2) v = (light_pred r1 v && light_pred r2 v)%bool.
Proof.
  intros. simpl. reflexivity.
Qed.

(** Theorem 14: Eval of EConst is the constant itself *)
Theorem eval_const : forall n, eval (EConst n) = n.
Proof.
  intros. simpl. reflexivity.
Qed.

(** Theorem 15: Eval of EPlus is sum of evaluations *)
Theorem eval_plus : forall e1 e2, eval (EPlus e1 e2) = eval e1 + eval e2.
Proof.
  intros. simpl. reflexivity.
Qed.

(** Theorem 16: Lightweight check false implies not full_check for decidable *)
Theorem lightweight_false_implies_not_full : forall (rt : RefinedType) (v : nat),
  decidable_refinement rt ->
  lightweight_check rt v = false ->
  ~ full_check rt v.
Proof.
  intros rt v Hdec Hfalse Hfull.
  apply Hdec in Hfull. unfold lightweight_check in Hfalse.
  rewrite Hfull in Hfalse. discriminate.
Qed.

(** Theorem 17: Subtype preserves lightweight soundness *)
Theorem subtype_lightweight_sound : forall (r1 r2 : RefinedType) (v : nat),
  refine_subtype r1 r2 ->
  lightweight_check r1 v = true ->
  full_check r2 v.
Proof.
  intros r1 r2 v Hsub Hlight.
  apply Hsub. apply lightweight_sound. exact Hlight.
Qed.

(** Theorem 18: Conjunction of decidable refinements is decidable *)
Theorem conj_decidable : forall (r1 r2 : RefinedType),
  decidable_refinement r1 ->
  decidable_refinement r2 ->
  decidable_refinement (refine_conj r1 r2).
Proof.
  unfold decidable_refinement. intros r1 r2 H1 H2 n.
  simpl. rewrite andb_true_iff.
  specialize (H1 n). specialize (H2 n). tauto.
Qed.

(** Theorem 19: Refine_subtype is antisymmetric under full_pred equality *)
Theorem refine_subtype_antisym_eq : forall (r1 r2 : RefinedType),
  refine_subtype r1 r2 ->
  refine_subtype r2 r1 ->
  forall n, full_pred r1 n <-> full_pred r2 n.
Proof.
  intros r1 r2 H12 H21 n. split; [apply H12 | apply H21].
Qed.

(** Theorem 20: Eval of EIf with 0 guard takes else branch *)
Theorem eval_if_false : forall et ef,
  eval (EIf (EConst 0) et ef) = eval ef.
Proof.
  intros. simpl. reflexivity.
Qed.

(** Theorem 21: Eval of EIf with nonzero guard takes then branch *)
Theorem eval_if_true : forall n et ef,
  n <> 0 ->
  eval (EIf (EConst n) et ef) = eval et.
Proof.
  intros n et ef Hneq. simpl.
  destruct n.
  - contradiction.
  - simpl. reflexivity.
Qed.

(** Theorem 22: Conjunction subtyping both ways *)
Theorem conj_sub_both : forall (r1 r2 : RefinedType) (v : nat),
  full_check (refine_conj r1 r2) v ->
  full_check r1 v /\ full_check r2 v.
Proof.
  unfold full_check. intros. simpl in H. exact H.
Qed.
