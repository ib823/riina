(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * Effect Algebra for RIINA
    
    Algebraic structure of effects.
    
    This module proves that effects form a join-semilattice (linear order).
*)

Require Import RIINA.foundations.Syntax.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.

(** Effect ordering based on levels *)
Definition effect_leq (e1 e2 : effect) : Prop :=
  effect_level e1 <= effect_level e2.

(** ** Partial Order Properties *)

Lemma effect_leq_refl : forall e, effect_leq e e.
Proof.
  intros e. unfold effect_leq. apply le_n.
Qed.

Lemma effect_leq_trans : forall e1 e2 e3,
  effect_leq e1 e2 -> effect_leq e2 e3 -> effect_leq e1 e3.
Proof.
  intros e1 e2 e3 H1 H2. unfold effect_leq in *.
  eapply Nat.le_trans; eassumption.
Qed.

Lemma effect_leq_antisym : forall e1 e2,
  effect_leq e1 e2 -> effect_leq e2 e1 -> e1 = e2.
Proof.
  intros e1 e2 H1 H2.
  unfold effect_leq in *.
  assert (H: effect_level e1 = effect_level e2) by (apply Nat.le_antisymm; assumption).
  destruct e1; destruct e2; simpl in H; try reflexivity; try discriminate.
Qed.

(** ** Join Semilattice Properties *)

Lemma effect_join_comm : forall e1 e2,
  effect_join e1 e2 = effect_join e2 e1.
Proof.
  intros e1 e2.
  unfold effect_join.
  destruct (effect_level e1 <? effect_level e2) eqn:H12.
  - apply Nat.ltb_lt in H12.
    destruct (effect_level e2 <? effect_level e1) eqn:H21.
    + apply Nat.ltb_lt in H21.
      exfalso. apply (Nat.lt_asymm (effect_level e1) (effect_level e2)); assumption.
    + reflexivity.
  - apply Nat.ltb_ge in H12.
    destruct (effect_level e2 <? effect_level e1) eqn:H21.
    + reflexivity.
    + apply Nat.ltb_ge in H21.
      (* e1 >= e2 and e2 >= e1 implies e1 = e2 levels *)
      assert (Heq: effect_level e1 = effect_level e2) by (apply Nat.le_antisymm; assumption).
      apply effect_leq_antisym; unfold effect_leq; rewrite Heq; apply le_n.
Qed.

Lemma effect_level_join : forall e1 e2,
  effect_level (effect_join e1 e2) = Nat.max (effect_level e1) (effect_level e2).
Proof.
  intros e1 e2. unfold effect_join.
  destruct (effect_level e1 <? effect_level e2) eqn:H.
  - apply Nat.ltb_lt in H. rewrite Nat.max_r; lia.
  - apply Nat.ltb_ge in H. rewrite Nat.max_l; lia.
Qed.

Lemma effect_join_assoc : forall e1 e2 e3,
  effect_join e1 (effect_join e2 e3) = effect_join (effect_join e1 e2) e3.
Proof.
  intros e1 e2 e3.
  apply effect_leq_antisym; unfold effect_leq; repeat rewrite effect_level_join; rewrite Nat.max_assoc; apply le_n.
Qed.

Lemma effect_join_ub_l : forall e1 e2, effect_leq e1 (effect_join e1 e2).
Proof.
  intros e1 e2. unfold effect_join, effect_leq.
  destruct (effect_level e1 <? effect_level e2) eqn:H.
  - apply Nat.ltb_lt in H. apply Nat.lt_le_incl. assumption.
  - apply Nat.ltb_ge in H. apply le_n.
Qed.

Lemma effect_join_ub_r : forall e1 e2, effect_leq e2 (effect_join e1 e2).
Proof.
  intros e1 e2. unfold effect_join, effect_leq.
  destruct (effect_level e1 <? effect_level e2) eqn:H.
  - apply Nat.ltb_lt in H. apply le_n.
  - apply Nat.ltb_ge in H. assumption.
Qed.

Lemma effect_join_lub : forall e1 e2 e3,
  effect_leq e1 e3 -> effect_leq e2 e3 -> effect_leq (effect_join e1 e2) e3.
Proof.
  intros e1 e2 e3 H1 H2. unfold effect_join, effect_leq in *.
  destruct (effect_level e1 <? effect_level e2).
  - assumption.
  - assumption.
Qed.

(** End of EffectAlgebra.v *)
