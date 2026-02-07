(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* SpeculativeExecution.v — Effect Types for Speculative Execution Safety *)
(* Strategic Item #5: Model speculative execution safety via effect types *)
(* Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md §4-§6 *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Import ListNotations.

(** * Security Effects *)

Inductive effect : Type :=
  | Eff_pure         (* no observable side-effects, safe under speculation *)
  | Eff_timed        (* timing-observable but no speculation leaks *)
  | Eff_speculative. (* may leak via speculative execution *)

(** Effect ordering: pure ≤ timed ≤ speculative *)
Definition eff_le (e1 e2 : effect) : bool :=
  match e1, e2 with
  | Eff_pure, _ => true
  | Eff_timed, Eff_pure => false
  | Eff_timed, _ => true
  | Eff_speculative, Eff_speculative => true
  | Eff_speculative, _ => false
  end.

Definition eff_join (e1 e2 : effect) : effect :=
  match e1, e2 with
  | Eff_pure, e | e, Eff_pure => e
  | Eff_speculative, _ | _, Eff_speculative => Eff_speculative
  | Eff_timed, Eff_timed => Eff_timed
  end.

(** * Values and Expressions *)

Inductive visibility : Type :=
  | Public
  | Secret.

Inductive value : Type :=
  | VNat : nat -> value
  | VBool : bool -> value.

(** Instructions with effect annotations *)
Inductive instr : Type :=
  | IConst : value -> instr                         (* constant load *)
  | IBinop : instr -> instr -> instr                (* binary operation *)
  | IBranch : visibility -> instr -> instr -> instr -> instr
      (* branch on condition with visibility tag; Secret branches may leak *)
  | ISeq : instr -> instr -> instr                  (* sequential composition *)
  | IAnnot : effect -> instr -> instr.              (* explicit effect annotation *)

(** * Effect inference *)

Fixpoint infer_effect (i : instr) : effect :=
  match i with
  | IConst _ => Eff_pure
  | IBinop a b => eff_join (infer_effect a) (infer_effect b)
  | IBranch Secret _ t f => eff_join Eff_speculative (eff_join (infer_effect t) (infer_effect f))
  | IBranch Public c t f => eff_join (infer_effect c) (eff_join (infer_effect t) (infer_effect f))
  | ISeq a b => eff_join (infer_effect a) (infer_effect b)
  | IAnnot e sub => eff_join e (infer_effect sub)
  end.

(** * Constant-time predicate: no secret-dependent branches *)

Fixpoint is_constant_time (i : instr) : bool :=
  match i with
  | IConst _ => true
  | IBinop a b => is_constant_time a && is_constant_time b
  | IBranch Secret _ _ _ => false
  | IBranch Public c t f => is_constant_time c && is_constant_time t && is_constant_time f
  | ISeq a b => is_constant_time a && is_constant_time b
  | IAnnot _ sub => is_constant_time sub
  end.

(** * Speculative safety: effect is not speculative *)

Definition is_spec_safe (i : instr) : bool :=
  negb (match infer_effect i with Eff_speculative => true | _ => false end).

(** * Simple evaluation (deterministic, total on well-formed programs) *)

Fixpoint eval_instr (i : instr) : option value :=
  match i with
  | IConst v => Some v
  | IBinop a b =>
      match eval_instr a, eval_instr b with
      | Some (VNat x), Some (VNat y) => Some (VNat (x + y))
      | _, _ => None
      end
  | IBranch _ c t f =>
      match eval_instr c with
      | Some (VBool true) => eval_instr t
      | Some (VBool false) => eval_instr f
      | _ => None
      end
  | ISeq a b =>
      match eval_instr a with
      | Some _ => eval_instr b
      | None => None
      end
  | IAnnot _ sub => eval_instr sub
  end.

(** * Helper lemmas *)

Lemma eff_join_pure_l : forall e, eff_join Eff_pure e = e.
Proof. destruct e; reflexivity. Qed.

Lemma eff_join_pure_r : forall e, eff_join e Eff_pure = e.
Proof. destruct e; reflexivity. Qed.

Lemma eff_le_refl : forall e, eff_le e e = true.
Proof. destruct e; reflexivity. Qed.

Lemma eff_le_trans : forall e1 e2 e3,
  eff_le e1 e2 = true -> eff_le e2 e3 = true -> eff_le e1 e3 = true.
Proof.
  destruct e1, e2, e3; simpl; intros; try reflexivity; try discriminate.
Qed.

(** * Theorem 1: Pure programs are constant-time *)

Theorem pure_is_constant_time : forall i,
  infer_effect i = Eff_pure -> is_constant_time i = true.
Proof.
  induction i; simpl; intros H.
  - reflexivity.
  - (* IBinop *)
    destruct (infer_effect i1) eqn:E1, (infer_effect i2) eqn:E2;
      simpl in H; try discriminate.
    rewrite IHi1, IHi2; auto.
  - (* IBranch *)
    destruct v; simpl in H.
    + (* Public *)
      destruct (infer_effect i1) eqn:E1;
        destruct (infer_effect i2) eqn:E2;
        destruct (infer_effect i3) eqn:E3;
        simpl in H; try discriminate.
      rewrite IHi1, IHi2, IHi3; auto.
    + (* Secret *)
      destruct (infer_effect i1) eqn:E1;
        destruct (infer_effect i2) eqn:E2;
        destruct (infer_effect i3) eqn:E3;
        simpl in H; discriminate.
  - (* ISeq *)
    destruct (infer_effect i1) eqn:E1, (infer_effect i2) eqn:E2;
      simpl in H; try discriminate.
    rewrite IHi1, IHi2; auto.
  - (* IAnnot *)
    destruct e; destruct (infer_effect i) eqn:Ei;
      simpl in H; try discriminate.
    apply IHi; auto.
Qed.

(** * Theorem 2: Constant-time composition *)

Theorem ct_composition : forall a b,
  is_constant_time a = true ->
  is_constant_time b = true ->
  is_constant_time (ISeq a b) = true.
Proof.
  simpl. intros a b Ha Hb. rewrite Ha, Hb. reflexivity.
Qed.

(** * Theorem 3: Speculative safety implies no secret leakage *)
(** We model "no secret leakage" as: evaluation does not depend on
    speculative side-channels, i.e., no secret branches exist. *)

Lemma no_secret_branch : forall i,
  is_constant_time i = true ->
  forall c t f, i <> IBranch Secret c t f.
Proof.
  intros i Hct c t f Heq. subst. simpl in Hct. discriminate.
Qed.

(** Speculative safety (effect not speculative) implies constant-time
    for programs whose only source of speculation is secret branches. *)

Fixpoint no_speculative_annotation (i : instr) : bool :=
  match i with
  | IConst _ => true
  | IBinop a b => no_speculative_annotation a && no_speculative_annotation b
  | IBranch _ c t f => no_speculative_annotation c &&
                        no_speculative_annotation t &&
                        no_speculative_annotation f
  | ISeq a b => no_speculative_annotation a && no_speculative_annotation b
  | IAnnot Eff_speculative _ => false
  | IAnnot _ sub => no_speculative_annotation sub
  end.

Lemma spec_safe_no_secret_branch_aux : forall i,
  no_speculative_annotation i = true ->
  infer_effect i <> Eff_speculative ->
  is_constant_time i = true.
Proof.
  induction i; simpl; intros Hna Hne; auto.
  - (* IBinop *)
    apply andb_true_iff in Hna; destruct Hna as [H1 H2].
    destruct (infer_effect i1) eqn:E1, (infer_effect i2) eqn:E2;
      simpl in Hne; try (exfalso; apply Hne; reflexivity);
      rewrite (IHi1 H1), (IHi2 H2); auto; try (intro; discriminate).
  - (* IBranch *)
    destruct v.
    + (* Public *)
      apply andb_true_iff in Hna; destruct Hna as [H12 H3].
      apply andb_true_iff in H12; destruct H12 as [H1 H2].
      destruct (infer_effect i1) eqn:E1,
               (infer_effect i2) eqn:E2,
               (infer_effect i3) eqn:E3;
        simpl in Hne;
        try (exfalso; apply Hne; reflexivity);
        rewrite (IHi1 H1), (IHi2 H2), (IHi3 H3); auto; try (intro; discriminate).
    + (* Secret — effect is always speculative *)
      exfalso; apply Hne.
      destruct (infer_effect i2), (infer_effect i3); reflexivity.
  - (* ISeq *)
    apply andb_true_iff in Hna; destruct Hna as [H1 H2].
    destruct (infer_effect i1) eqn:E1, (infer_effect i2) eqn:E2;
      simpl in Hne; try (exfalso; apply Hne; reflexivity);
      rewrite (IHi1 H1), (IHi2 H2); auto; try (intro; discriminate).
  - (* IAnnot *)
    destruct e; simpl in Hna; try discriminate;
      apply IHi; auto;
      destruct (infer_effect i); simpl in Hne; auto; try (intro; discriminate).
Qed.

Theorem spec_safe_implies_no_secret_leakage : forall i,
  no_speculative_annotation i = true ->
  is_spec_safe i = true ->
  is_constant_time i = true.
Proof.
  intros i Hna Hss.
  unfold is_spec_safe in Hss.
  apply spec_safe_no_secret_branch_aux; auto.
  destruct (infer_effect i); simpl in Hss; try discriminate.
  all: intro; discriminate.
Qed.

(** * Theorem 4: Effect ordering is a preorder *)

Theorem effect_preorder_refl : forall e, eff_le e e = true.
Proof. exact eff_le_refl. Qed.

Theorem effect_preorder_trans : forall e1 e2 e3,
  eff_le e1 e2 = true -> eff_le e2 e3 = true -> eff_le e1 e3 = true.
Proof. exact eff_le_trans. Qed.

(** * Theorem 5: Pure is bottom of the effect ordering *)

Theorem pure_is_bottom : forall e, eff_le Eff_pure e = true.
Proof. destruct e; reflexivity. Qed.

(** * Theorem 6: Sequential composition preserves speculative safety *)

Theorem seq_preserves_spec_safe : forall a b,
  is_spec_safe a = true ->
  is_spec_safe b = true ->
  is_spec_safe (ISeq a b) = true.
Proof.
  unfold is_spec_safe. simpl. intros a b Ha Hb.
  destruct (infer_effect a) eqn:Ea, (infer_effect b) eqn:Eb;
    simpl; simpl in Ha, Hb; try reflexivity; try discriminate.
Qed.

(** * Theorem 7: Secret-independent branching is constant-time *)

Theorem public_branch_ct : forall c t f,
  is_constant_time c = true ->
  is_constant_time t = true ->
  is_constant_time f = true ->
  is_constant_time (IBranch Public c t f) = true.
Proof.
  simpl. intros c t f Hc Ht Hf. rewrite Hc, Ht, Hf. reflexivity.
Qed.

(** * Theorem 8: Effect annotation soundness *)
(** If a program is annotated with effect [e] and its inferred effect
    is at most [e], then the annotation is sound. We prove that
    the inferred effect of an annotated program joins to at least [e]. *)

Definition effect_eq_dec (e1 e2 : effect) : {e1 = e2} + {e1 <> e2}.
Proof. decide equality. Defined.

Theorem annotation_soundness : forall e i,
  eff_le (infer_effect i) e = true ->
  eff_le (infer_effect (IAnnot e i)) e = true.
Proof.
  intros e i Hle. simpl.
  destruct e, (infer_effect i); simpl in *; try reflexivity; try discriminate.
Qed.

(** * Theorem 9 (Bonus): Binop preserves constant-time *)

Theorem binop_preserves_ct : forall a b,
  is_constant_time a = true ->
  is_constant_time b = true ->
  is_constant_time (IBinop a b) = true.
Proof.
  simpl. intros a b Ha Hb. rewrite Ha, Hb. reflexivity.
Qed.

(** * Theorem 10 (Bonus): Pure programs are speculatively safe *)

Theorem pure_implies_spec_safe : forall i,
  infer_effect i = Eff_pure ->
  is_spec_safe i = true.
Proof.
  intros i H. unfold is_spec_safe. rewrite H. reflexivity.
Qed.

(** * Theorem 11: Timed programs are speculatively safe *)

Theorem timed_implies_spec_safe : forall i,
  infer_effect i = Eff_timed ->
  is_spec_safe i = true.
Proof.
  intros i H. unfold is_spec_safe. rewrite H. reflexivity.
Qed.

(** * Theorem 12: Constant is always pure *)

Theorem const_is_pure : forall v,
  infer_effect (IConst v) = Eff_pure.
Proof.
  intros v. reflexivity.
Qed.

(** * Theorem 13: Effect join is commutative *)

Theorem eff_join_comm : forall e1 e2,
  eff_join e1 e2 = eff_join e2 e1.
Proof.
  destruct e1, e2; reflexivity.
Qed.
