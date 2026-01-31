(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** * LexOrder.v

    RIINA Lexicographic Well-Founded Order for Step-Indexed Proofs

    This file establishes the lexicographic order on (nat, nat) pairs
    that enables well-founded recursion on (step_index, ty_size).

    KEY INSIGHT: The TFn contravariance problem requires us to decrease
    the step index when handling function arguments. But when the step
    index stays the same, we can decrease the type size. The lexicographic
    order on (n, ty_size T) captures this precisely.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_α (Alpha)
    Phase: 1 (Foundation)
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Relations.Relation_Operators.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.properties.TypeMeasure.

(** ** Lexicographic Order on Natural Number Pairs *)

(** Definition: (m1, m2) < (n1, n2) iff m1 < n1, or m1 = n1 and m2 < n2 *)
Definition lex_lt (p1 p2 : nat * nat) : Prop :=
  let (m1, m2) := p1 in
  let (n1, n2) := p2 in
  m1 < n1 \/ (m1 = n1 /\ m2 < n2).

(** ** Well-Foundedness of Lexicographic Order *)

(** Direct proof using nested well-founded induction *)
Theorem lex_lt_wf : well_founded lex_lt.
Proof.
  unfold well_founded.
  intros [n m].
  generalize dependent m.
  (* Outer induction on n *)
  induction n as [n IHn] using (well_founded_ind lt_wf).
  intros m.
  (* Inner induction on m *)
  induction m as [m IHm] using (well_founded_ind lt_wf).
  constructor.
  intros [n' m'] Hlt.
  unfold lex_lt in Hlt.
  destruct Hlt as [Hlt_n | [Heq_n Hlt_m]].
  - (* n' < n: use outer IH *)
    apply IHn. exact Hlt_n.
  - (* n' = n and m' < m: use inner IH *)
    subst n'. apply IHm. exact Hlt_m.
Qed.

(** ** Lexicographic Induction Principle *)

Theorem lex_induction :
  forall (P : nat -> nat -> Prop),
    (forall n m, (forall n' m', lex_lt (n', m') (n, m) -> P n' m') -> P n m) ->
    forall n m, P n m.
Proof.
  intros P IH n m.
  pose (Q := fun p : nat * nat => P (fst p) (snd p)).
  change (Q (n, m)).
  apply (well_founded_ind lex_lt_wf Q).
  intros [n' m'] H.
  unfold Q. simpl.
  apply IH.
  intros n'' m'' Hlt.
  apply (H (n'', m'')). exact Hlt.
Qed.

(** ** Decrease Lemmas for Lexicographic Order *)

Lemma lex_lt_left : forall n m n' m',
  n' < n -> lex_lt (n', m') (n, m).
Proof.
  intros. unfold lex_lt. left. exact H.
Qed.

Lemma lex_lt_right : forall n m m',
  m' < m -> lex_lt (n, m') (n, m).
Proof.
  intros. unfold lex_lt. right. split; [reflexivity | exact H].
Qed.

(** ** Step-Type Lexicographic Order

    Combines step index n with type size for well-founded recursion
    on val_rel_le definitions.
*)

Definition step_ty_lt (p1 p2 : nat * ty) : Prop :=
  let (n1, T1) := p1 in
  let (n2, T2) := p2 in
  n1 < n2 \/ (n1 = n2 /\ ty_size T1 < ty_size T2).

(** step_ty_lt is well-founded *)
Theorem step_ty_lt_wf : well_founded step_ty_lt.
Proof.
  unfold well_founded.
  intros [n T].
  generalize dependent T.
  (* Outer induction on n *)
  induction n as [n IHn] using (well_founded_ind lt_wf).
  intros T.
  (* Inner induction on ty_size T *)
  induction T as [T IHT] using (well_founded_ind ty_size_lt_wf).
  constructor.
  intros [n' T'] Hlt.
  unfold step_ty_lt in Hlt.
  destruct Hlt as [Hlt_n | [Heq_n Hlt_ty]].
  - (* n' < n: use outer IH *)
    apply IHn. exact Hlt_n.
  - (* n' = n and ty_size T' < ty_size T: use inner IH *)
    subst n'. apply IHT. unfold ty_size_lt. exact Hlt_ty.
Qed.

(** Induction principle for step-type pairs *)
Theorem step_ty_induction :
  forall (P : nat -> ty -> Prop),
    (forall n T, (forall n' T', step_ty_lt (n', T') (n, T) -> P n' T') -> P n T) ->
    forall n T, P n T.
Proof.
  intros P IH n T.
  pose (Q := fun p : nat * ty => P (fst p) (snd p)).
  change (Q (n, T)).
  apply (well_founded_ind step_ty_lt_wf Q).
  intros [n' T'] H.
  unfold Q. simpl.
  apply IH.
  intros n'' T'' Hlt.
  apply (H (n'', T'')). exact Hlt.
Qed.

(** ** Useful Decrease Lemmas *)

(** Decreasing step index (the primary decrease for TFn) *)
Lemma step_ty_lt_step : forall n T T',
  step_ty_lt (n, T') (S n, T).
Proof.
  intros. unfold step_ty_lt. left. lia.
Qed.

(** Decreasing type size at same step (for recursive types) *)
Lemma step_ty_lt_ty : forall n T T',
  ty_size T' < ty_size T ->
  step_ty_lt (n, T') (n, T).
Proof.
  intros. unfold step_ty_lt. right. split; [reflexivity | exact H].
Qed.

(** TFn argument is smaller *)
Lemma step_ty_lt_fn_arg : forall n T1 T2 eff,
  step_ty_lt (n, T1) (n, TFn T1 T2 eff).
Proof.
  intros. apply step_ty_lt_ty. apply ty_size_fn_arg.
Qed.

(** TFn result is smaller *)
Lemma step_ty_lt_fn_res : forall n T1 T2 eff,
  step_ty_lt (n, T2) (n, TFn T1 T2 eff).
Proof.
  intros. apply step_ty_lt_ty. apply ty_size_fn_res.
Qed.

(** TProd components are smaller *)
Lemma step_ty_lt_prod_left : forall n T1 T2,
  step_ty_lt (n, T1) (n, TProd T1 T2).
Proof.
  intros. apply step_ty_lt_ty. apply ty_size_prod_left.
Qed.

Lemma step_ty_lt_prod_right : forall n T1 T2,
  step_ty_lt (n, T2) (n, TProd T1 T2).
Proof.
  intros. apply step_ty_lt_ty. apply ty_size_prod_right.
Qed.

(** TSum components are smaller *)
Lemma step_ty_lt_sum_left : forall n T1 T2,
  step_ty_lt (n, T1) (n, TSum T1 T2).
Proof.
  intros. apply step_ty_lt_ty. apply ty_size_sum_left.
Qed.

Lemma step_ty_lt_sum_right : forall n T1 T2,
  step_ty_lt (n, T2) (n, TSum T1 T2).
Proof.
  intros. apply step_ty_lt_ty. apply ty_size_sum_right.
Qed.

(** Step decrease combined with type *)
Lemma step_ty_lt_step_any : forall n n' T T',
  n' < n ->
  step_ty_lt (n', T') (n, T).
Proof.
  intros. unfold step_ty_lt. left. exact H.
Qed.

(** ** Triple Lexicographic Order (for full cumulative proof)

    For the cumulative monotonicity proof, we may need
    (step_index, ty_size, store_size) or similar.
*)

Definition triple_lt (p1 p2 : nat * nat * nat) : Prop :=
  let '(a1, b1, c1) := p1 in
  let '(a2, b2, c2) := p2 in
  a1 < a2 \/
  (a1 = a2 /\ b1 < b2) \/
  (a1 = a2 /\ b1 = b2 /\ c1 < c2).

Theorem triple_lt_wf : well_founded triple_lt.
Proof.
  unfold well_founded.
  intros [[a b] c].
  generalize dependent c.
  generalize dependent b.
  (* Induction on a *)
  pattern a. apply (well_founded_ind lt_wf). clear a.
  intros a IHa b.
  (* Induction on b *)
  pattern b. apply (well_founded_ind lt_wf). clear b.
  intros b IHb c.
  (* Induction on c *)
  pattern c. apply (well_founded_ind lt_wf). clear c.
  intros c IHc.
  constructor.
  intros [[a' b'] c'] Hlt.
  unfold triple_lt in Hlt.
  destruct Hlt as [Ha | [Hb_case | Hc_case]].
  - apply IHa. exact Ha.
  - destruct Hb_case as [Heq_a Hb]. rewrite Heq_a. apply IHb. exact Hb.
  - destruct Hc_case as [Heq_a [Heq_b Hc]]. rewrite Heq_a. rewrite Heq_b. apply IHc. exact Hc.
Qed.

(** End of LexOrder.v *)
