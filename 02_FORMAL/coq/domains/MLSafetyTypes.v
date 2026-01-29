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
