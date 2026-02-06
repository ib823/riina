(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** MLSafetyTypes.v
    Strategic Item #10: AI/ML Safety Types for RIINA

    Proves tensor shape safety, differential privacy composition,
    and Lipschitz continuity properties.

    Self-contained — Coq stdlib only.
    Spec: 01_RESEARCH/specs/RIINA_ML_SAFETY_TYPES.md
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.

(** * Tensor shapes as lists of dimensions *)
Definition shape := list nat.

(** * Shape compatibility for element-wise operations *)
Definition shape_eq (s1 s2 : shape) : bool :=
  (length s1 =? length s2) &&
  forallb (fun p => fst p =? snd p) (combine s1 s2).

(** * Matrix multiplication shape check *)
Definition matmul_compat (s1 s2 : shape) : option shape :=
  match s1, s2 with
  | [r1; c1], [r2; c2] =>
      if c1 =? r2 then Some [r1; c2] else None
  | _, _ => None
  end.

(** Helper: forallb over combine s s is always true *)
Lemma forallb_combine_refl : forall s,
  forallb (fun p => fst p =? snd p) (combine s s) = true.
Proof.
  induction s as [|a s' IH]; simpl; auto.
  rewrite Nat.eqb_refl. simpl. exact IH.
Qed.

(** Helper: forallb over combine is symmetric *)
Lemma forallb_combine_sym : forall s1 s2,
  forallb (fun p => fst p =? snd p) (combine s1 s2) =
  forallb (fun p => fst p =? snd p) (combine s2 s1).
Proof.
  induction s1 as [|a s1' IH]; destruct s2 as [|b s2']; simpl; auto.
  rewrite (Nat.eqb_sym a b). f_equal. apply IH.
Qed.

(** * Theorem 1: shape_eq is reflexive *)
Theorem shape_eq_refl : forall s, shape_eq s s = true.
Proof.
  intro s. unfold shape_eq.
  rewrite Nat.eqb_refl. simpl.
  apply forallb_combine_refl.
Qed.

(** * Theorem 2: shape_eq is symmetric *)
Theorem shape_eq_sym : forall s1 s2, shape_eq s1 s2 = shape_eq s2 s1.
Proof.
  unfold shape_eq. intros s1 s2.
  rewrite (Nat.eqb_sym (length s1) (length s2)).
  rewrite forallb_combine_sym. reflexivity.
Qed.

(** * Theorem 3: matmul produces correct output shape *)
Theorem matmul_shape_correct : forall r1 c1 c2 s,
  matmul_compat [r1; c1] [c1; c2] = Some s ->
  s = [r1; c2].
Proof.
  intros r1 c1 c2 s H. simpl in H.
  rewrite Nat.eqb_refl in H.
  inversion H. reflexivity.
Qed.

(** * Theorem 4: matmul fails on incompatible inner dims *)
Theorem matmul_incompat : forall r1 c1 r2 c2,
  c1 <> r2 ->
  matmul_compat [r1; c1] [r2; c2] = None.
Proof.
  intros r1 c1 r2 c2 Hneq. simpl.
  destruct (c1 =? r2) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

(** * Differential Privacy: epsilon-budget model *)
(** We model epsilon as a natural number (scaled by some factor) *)

Record dp_config := mkDP {
  dp_epsilon : nat;  (* privacy budget, scaled *)
  dp_queries : nat;  (* number of queries made *)
}.

Definition dp_compose (d1 d2 : dp_config) : dp_config :=
  mkDP (dp_epsilon d1 + dp_epsilon d2) (dp_queries d1 + dp_queries d2).

(** * Theorem 5: DP sequential composition — epsilon adds *)
Theorem dp_composition_additive : forall d1 d2,
  dp_epsilon (dp_compose d1 d2) = dp_epsilon d1 + dp_epsilon d2.
Proof.
  intros. destruct d1, d2. simpl. reflexivity.
Qed.

(** * Theorem 6: DP composition is associative *)
Theorem dp_compose_assoc : forall d1 d2 d3,
  dp_compose (dp_compose d1 d2) d3 = dp_compose d1 (dp_compose d2 d3).
Proof.
  intros. destruct d1, d2, d3. unfold dp_compose. simpl. f_equal; lia.
Qed.

(** * Lipschitz continuity — modeled as bounded difference *)

Definition lipschitz_bound (k : nat) (f : nat -> nat) : Prop :=
  forall x y, (f x - f y) <= k * (x - y) /\ (f y - f x) <= k * (y - x).

Definition compose_fn (f g : nat -> nat) : nat -> nat := fun x => f (g x).

(** * Theorem 7: Composition of Lipschitz functions *)
Theorem lipschitz_compose : forall k1 k2 f g,
  lipschitz_bound k1 f ->
  lipschitz_bound k2 g ->
  lipschitz_bound (k1 * k2) (compose_fn f g).
Proof.
  unfold lipschitz_bound, compose_fn. intros k1 k2 f g Hf Hg x y.
  specialize (Hg x y). destruct Hg as [Hg1 Hg2].
  specialize (Hf (g x) (g y)). destruct Hf as [Hf1 Hf2].
  split.
  - apply (Nat.le_trans _ (k1 * (g x - g y)) _). exact Hf1.
    apply (Nat.le_trans _ (k1 * (k2 * (x - y))) _).
    + apply Nat.mul_le_mono_l. exact Hg1.
    + rewrite Nat.mul_assoc. lia.
  - apply (Nat.le_trans _ (k1 * (g y - g x)) _). exact Hf2.
    apply (Nat.le_trans _ (k1 * (k2 * (y - x))) _).
    + apply Nat.mul_le_mono_l. exact Hg2.
    + rewrite Nat.mul_assoc. lia.
Qed.

(** * Theorem 8: Identity is 1-Lipschitz *)
Theorem lipschitz_id : lipschitz_bound 1 (fun x => x).
Proof.
  unfold lipschitz_bound. intros x y. simpl. lia.
Qed.

(** * Theorem 9: Constant function is 0-Lipschitz *)
Theorem lipschitz_const : forall c, lipschitz_bound 0 (fun _ => c).
Proof.
  unfold lipschitz_bound. intros c x y. simpl. lia.
Qed.

(** * Theorem 10: DP composition preserves query count *)
Theorem dp_queries_additive : forall d1 d2,
  dp_queries (dp_compose d1 d2) = dp_queries d1 + dp_queries d2.
Proof.
  intros. destruct d1, d2. simpl. reflexivity.
Qed.

(** * Theorem 11: DP composition with zero-epsilon is identity for epsilon *)
Theorem dp_compose_zero_l : forall d,
  dp_epsilon (dp_compose (mkDP 0 0) d) = dp_epsilon d.
Proof.
  intros. destruct d. simpl. reflexivity.
Qed.

(** * Theorem 12: DP composition with zero-epsilon is identity for epsilon (right) *)
Theorem dp_compose_zero_r : forall d,
  dp_epsilon (dp_compose d (mkDP 0 0)) = dp_epsilon d.
Proof.
  intros. destruct d. simpl. lia.
Qed.

(** * Theorem 13: DP compose is commutative *)
Theorem dp_compose_comm : forall d1 d2,
  dp_compose d1 d2 = dp_compose d2 d1.
Proof.
  intros. destruct d1, d2. unfold dp_compose. f_equal; lia.
Qed.

(** * Theorem 14: shape_eq true means same length *)
Theorem shape_eq_implies_same_length : forall s1 s2,
  shape_eq s1 s2 = true -> length s1 = length s2.
Proof.
  unfold shape_eq. intros s1 s2 H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.eqb_eq in H. exact H.
Qed.

(** * Theorem 15: Empty shapes are equal *)
Theorem shape_eq_nil : shape_eq [] [] = true.
Proof.
  unfold shape_eq. simpl. reflexivity.
Qed.

(** * Theorem 16: Singleton shapes equal iff values equal *)
Theorem shape_eq_singleton : forall a b,
  shape_eq [a] [b] = true -> a = b.
Proof.
  unfold shape_eq. simpl. intros a b H.
  rewrite andb_true_r in H.
  apply Nat.eqb_eq in H. exact H.
Qed.

(** * Theorem 17: matmul of square matrices produces square *)
Theorem matmul_square : forall n s,
  matmul_compat [n; n] [n; n] = Some s -> s = [n; n].
Proof.
  intros. simpl in H. rewrite Nat.eqb_refl in H.
  inversion H. reflexivity.
Qed.

(** * Theorem 18: matmul with 1-row right gives column vector *)
Theorem matmul_col_vector : forall r c s,
  matmul_compat [r; c] [c; 1] = Some s -> s = [r; 1].
Proof.
  intros. simpl in H. rewrite Nat.eqb_refl in H.
  inversion H. reflexivity.
Qed.

(** * Theorem 19: DP epsilon is always non-negative for compose *)
Theorem dp_epsilon_nonneg : forall d1 d2,
  dp_epsilon (dp_compose d1 d2) >= dp_epsilon d1.
Proof.
  intros. destruct d1, d2. simpl. lia.
Qed.

(** * Theorem 20: Lipschitz bound monotonicity *)
Theorem lipschitz_mono : forall k1 k2 f,
  lipschitz_bound k1 f -> k1 <= k2 -> lipschitz_bound k2 f.
Proof.
  unfold lipschitz_bound. intros k1 k2 f Hk1 Hle x y.
  specialize (Hk1 x y). destruct Hk1 as [H1 H2].
  split.
  - apply (Nat.le_trans _ (k1 * (x - y)) _). exact H1.
    apply Nat.mul_le_mono_r. exact Hle.
  - apply (Nat.le_trans _ (k1 * (y - x)) _). exact H2.
    apply Nat.mul_le_mono_r. exact Hle.
Qed.

(** * Theorem 21: compose_fn associativity *)
Theorem compose_fn_assoc : forall f g h x,
  compose_fn f (compose_fn g h) x = compose_fn (compose_fn f g) h x.
Proof.
  unfold compose_fn. intros. reflexivity.
Qed.

(** * Theorem 22: compose_fn with id is identity (left) *)
Theorem compose_fn_id_l : forall f x,
  compose_fn (fun y => y) f x = f x.
Proof.
  unfold compose_fn. intros. reflexivity.
Qed.
