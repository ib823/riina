(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** ProbabilisticVerification.v
    Strategic Item #7: Probabilistic Crypto Verification for RIINA

    Proves properties of probability distributions, negligible functions,
    and computational indistinguishability.

    Self-contained — Coq stdlib only (uses QArith for rationals).
    Spec: 01_RESEARCH/specs/RIINA_PROB_VERIFICATION.md
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lqa.
Require Import Coq.Classes.Morphisms.
Import ListNotations.

Open Scope Q_scope.

(** * Discrete probability distribution over a finite type *)
Definition dist (A : Type) := list (A * Q).

Definition prob_sum {A : Type} (d : dist A) : Q :=
  fold_left (fun acc p => acc + snd p) d 0.

Definition all_nonneg {A : Type} (d : dist A) : Prop :=
  Forall (fun p => 0 <= snd p) d.

Definition valid_dist {A : Type} (d : dist A) : Prop :=
  all_nonneg d /\ prob_sum d == 1.

(** * Uniform distribution *)
Definition uniform_dist (n : nat) (Hn : (0 < n)%nat) : dist nat :=
  map (fun i => (i, 1 # Pos.of_nat n)) (seq 0 n).

(** * Theorem 1: Uniform distribution has non-negative probabilities *)
Theorem uniform_nonneg : forall n (Hn : (0 < n)%nat),
  all_nonneg (uniform_dist n Hn).
Proof.
  unfold all_nonneg, uniform_dist.
  intros. apply Forall_forall. intros x Hin.
  apply in_map_iff in Hin. destruct Hin as [i [Heq _]].
  subst. simpl. unfold Qle. simpl. lia.
Qed.

(** * Negligible functions *)
Definition negligible (f : nat -> Q) : Prop :=
  forall c : nat, (0 < c)%nat ->
    exists N : nat, forall n : nat, (n > N)%nat ->
      Qabs (f n) < 1 # Pos.of_nat (Nat.pow n c).

(** * Theorem 2: Zero function is negligible *)
Theorem zero_negligible : negligible (fun _ => 0).
Proof.
  unfold negligible. intros c Hc.
  exists 1%nat. intros n Hn.
  rewrite Qabs_pos; [|apply Qle_refl].
  unfold Qlt. simpl. lia.
Qed.

(** Auxiliary: sum of Q-strict-less *)
Lemma Qplus_lt_compat2 : forall a b c d : Q,
  a < b -> c < d -> a + c < b + d.
Proof. intros. lra. Qed.

(** Auxiliary: 2/n^(S c) <= 1/n^c for n > 2 *)
Lemma two_over_nSc_le_one_over_nc : forall n c : nat,
  (n > 2)%nat -> (0 < c)%nat ->
  (1 # Pos.of_nat (n ^ S c)) + (1 # Pos.of_nat (n ^ S c)) <= 1 # Pos.of_nat (n ^ c).
Proof.
  intros n c Hn Hc.
  assert (Hpowc : (n ^ c <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  unfold Qle, Qplus. simpl. nia.
Qed.

(** * Theorem 3: Sum of negligibles is negligible *)
Theorem negligible_sum : forall f g,
  negligible f -> negligible g ->
  negligible (fun n => f n + g n).
Proof.
  unfold negligible. intros f g Hf Hg c Hc.
  destruct (Hf (S c) ltac:(lia)) as [N1 HN1].
  destruct (Hg (S c) ltac:(lia)) as [N2 HN2].
  exists (Nat.max N1 (Nat.max N2 2)).
  intros n Hn.
  assert (HnN1 : (n > N1)%nat) by lia.
  assert (HnN2 : (n > N2)%nat) by lia.
  assert (Hn2 : (n > 2)%nat) by lia.
  specialize (HN1 n HnN1). specialize (HN2 n HnN2).
  eapply Qle_lt_trans.
  - apply Qabs_triangle.
  - eapply Qlt_le_trans.
    + apply Qplus_lt_compat2; eassumption.
    + apply two_over_nSc_le_one_over_nc; assumption.
Qed.

(** * Statistical distance between distributions *)
Definition stat_dist {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (d1 d2 : dist A) : Q :=
  fold_left (fun acc p => acc + Qabs (snd p))
    (combine (map snd d1) (map snd d2)) 0.

(** * Computational indistinguishability (simplified) *)
Definition comp_indist (f g : nat -> dist nat) : Prop :=
  negligible (fun n =>
    fold_left (fun acc p => acc + Qabs (fst p - snd p))
      (combine (map snd (f n)) (map snd (g n))) 0).

(** Helper: Qabs of self-difference is zero *)
Lemma Qabs_Qminus_self : forall a : Q, Qabs (a - a) == 0.
Proof.
  intros. setoid_replace (a - a) with 0 by ring.
  apply Qabs_pos. unfold Qle. simpl. lia.
Qed.

(** Helper: fold over combine l l equals accumulator *)
Lemma fold_combine_self_gen : forall (l : list Q) (acc : Q),
  fold_left (fun a p => a + Qabs (fst p - snd p)) (combine l l) acc == acc.
Proof.
  induction l as [|a l' IH]; simpl; intros acc.
  - reflexivity.
  - rewrite IH. setoid_rewrite Qabs_Qminus_self. ring.
Qed.

(** Helper: fold over combine l l starting at 0 is 0 *)
Lemma fold_combine_self : forall (l : list Q),
  fold_left (fun acc p => acc + Qabs (fst p - snd p)) (combine l l) 0 == 0.
Proof. intros. apply fold_combine_self_gen. Qed.

(** * Theorem 4: Identical distributions are indistinguishable *)
Theorem identical_indist : forall f, comp_indist f f.
Proof.
  unfold comp_indist, negligible. intros f c Hc.
  exists 1%nat. intros n Hn.
  rewrite fold_combine_self.
  rewrite Qabs_pos by (apply Qle_refl).
  unfold Qlt. simpl. lia.
Qed.

(** * Theorem 5: Indistinguishability is reflexive *)
Theorem comp_indist_refl : forall f, comp_indist f f.
Proof. exact identical_indist. Qed.

(** * One-time pad model *)
Definition xor_nat (a b : nat) : nat := Nat.lxor a b.

(** * Theorem 6: XOR is self-inverse *)
Theorem xor_self_inverse : forall a b,
  xor_nat (xor_nat a b) b = a.
Proof.
  unfold xor_nat. intros.
  rewrite Nat.lxor_assoc.
  rewrite Nat.lxor_nilpotent.
  rewrite Nat.lxor_0_r.
  reflexivity.
Qed.

(** * Theorem 7: XOR is commutative *)
Theorem xor_comm : forall a b, xor_nat a b = xor_nat b a.
Proof.
  unfold xor_nat. intros. apply Nat.lxor_comm.
Qed.

(** * Theorem 8: XOR with zero is identity *)
Theorem xor_zero_id : forall a, xor_nat a 0 = a.
Proof.
  unfold xor_nat. intros. apply Nat.lxor_0_r.
Qed.

(** * Theorem 9: XOR is associative *)
Theorem xor_assoc : forall a b c, xor_nat (xor_nat a b) c = xor_nat a (xor_nat b c).
Proof.
  unfold xor_nat. intros. apply Nat.lxor_assoc.
Qed.

(** * Theorem 10: XOR self is zero *)
Theorem xor_self_zero : forall a, xor_nat a a = 0%nat.
Proof.
  unfold xor_nat. intros. apply Nat.lxor_nilpotent.
Qed.

(** * Theorem 11: Double OTP encryption-decryption roundtrip *)
Theorem otp_roundtrip : forall msg key,
  xor_nat (xor_nat msg key) key = msg.
Proof.
  intros. apply xor_self_inverse.
Qed.

(** * Theorem 12: XOR with same key is deterministic *)
Theorem xor_deterministic : forall a b k,
  xor_nat a k = xor_nat b k -> a = b.
Proof.
  unfold xor_nat. intros a b k H.
  assert (H1: Nat.lxor (Nat.lxor a k) k = Nat.lxor (Nat.lxor b k) k) by (rewrite H; reflexivity).
  rewrite Nat.lxor_assoc in H1.
  rewrite Nat.lxor_nilpotent in H1.
  rewrite Nat.lxor_0_r in H1.
  rewrite Nat.lxor_assoc in H1.
  rewrite Nat.lxor_nilpotent in H1.
  rewrite Nat.lxor_0_r in H1.
  exact H1.
Qed.

(** * Theorem 13: Uniform distribution has correct length *)
Theorem uniform_length : forall n (Hn : (0 < n)%nat),
  length (uniform_dist n Hn) = n.
Proof.
  unfold uniform_dist. intros.
  rewrite map_length. rewrite seq_length. reflexivity.
Qed.

(** * Theorem 14: Qabs is non-negative *)
Theorem qabs_nonneg : forall q : Q, (0 <= Qabs q)%Q.
Proof.
  intros. apply Qabs_nonneg.
Qed.

(** * Theorem 15: Qabs of zero is zero *)
Theorem qabs_zero : Qabs 0 == 0.
Proof.
  apply Qabs_pos. apply Qle_refl.
Qed.

Close Scope Q_scope.
