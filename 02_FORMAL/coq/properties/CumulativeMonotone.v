(** * CumulativeMonotone.v

    RIINA Full Monotonicity Proofs for Cumulative Relations

    This file contains monotonicity proofs:
    - Step monotonicity (first-order types proven, TFn admitted)
    - Store extension monotonicity (fully proven)
    - Combined monotonicity

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_α (Alpha)
    Phase: 2 (Cumulative Relation)
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.LexOrder.
Require Import RIINA.properties.FirstOrderComplete.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.ValRelMonotone.

Import ListNotations.

(** ** Full Step Monotonicity

    Step monotonicity: if values are related at step n, they remain related
    at any m ≤ n. This follows from the cumulative structure of val_rel_le.

    The proof is provided in ValRelMonotone.v via val_rel_le_monotone.
    This theorem is an alias for compatibility with existing code.
*)

Theorem val_rel_le_mono_step : forall n m Σ T v1 v2,
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
Proof.
  (* Delegate to the proven theorem in ValRelMonotone.v *)
  intros n m Σ T v1 v2 Hle Hrel.
  apply val_rel_le_monotone with n; assumption.
Qed.

(** ** Store Extension Monotonicity

    If values are related at store typing Σ, they remain related
    at any extension Σ' of Σ. This is fully provable.
*)

Lemma val_rel_le_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le n Σ' T v1 v2.
Proof.
  intros n. induction n as [|n' IH]; intros Σ Σ' T v1 v2 Hext Hrel.
  - simpl. exact I.
  - simpl in Hrel. simpl.
    destruct Hrel as [Hprev Hstruct].
    split.
    + apply IH with (Σ := Σ); auto.
    + unfold val_rel_struct in *.
      destruct Hstruct as (Hv1 & Hv2 & Hc1 & Hc2 & HT).
      repeat split; auto.
      destruct T; auto.
      * (* TFn *)
        intros Σ'' Hext' arg1 arg2 Hvarg1 Hvarg2 Hcarg1 Hcarg2 Hargs st1 st2 ctx Hst.
        assert (Hext'' : store_ty_extends Σ Σ'').
        { apply store_ty_extends_trans with Σ'; auto. }
        apply HT; auto.
      * (* TProd *)
        destruct HT as (a1 & b1 & a2 & b2 & Heq1 & Heq2 & Hr1 & Hr2).
        exists a1, b1, a2, b2.
        repeat split; auto.
        -- apply IH with (Σ := Σ); auto.
        -- apply IH with (Σ := Σ); auto.
      * (* TSum *)
        destruct HT as [HInl | HInr].
        -- left. destruct HInl as (a1 & a2 & Heq1 & Heq2 & Hr).
           exists a1, a2. repeat split; auto.
           apply IH with (Σ := Σ); auto.
        -- right. destruct HInr as (b1 & b2 & Heq1 & Heq2 & Hr).
           exists b1, b2. repeat split; auto.
           apply IH with (Σ := Σ); auto.
Qed.

(** ** Combined Monotonicity *)

Theorem val_rel_le_mono : forall n m Σ Σ' T v1 v2,
  m <= n ->
  store_ty_extends Σ Σ' ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ' T v1 v2.
Proof.
  intros n m Σ Σ' T v1 v2 Hle Hext Hrel.
  apply val_rel_le_mono_step with n; auto.
  apply val_rel_le_mono_store with Σ; auto.
Qed.

(** ** Step-Down Lemma *)

Lemma val_rel_le_step_down : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros. apply val_rel_le_cumulative. exact H.
Qed.

(** ** Store Relation Monotonicity *)

Lemma store_rel_le_mono_step : forall n m Σ st1 st2,
  m <= n ->
  store_rel_le n Σ st1 st2 ->
  store_rel_le m Σ st1 st2.
Proof.
  intros n m Σ st1 st2 Hle [Hmax Hlocs].
  split; auto.
  intros l T sl Hlook.
  specialize (Hlocs l T sl Hlook).
  destruct (store_lookup l st1), (store_lookup l st2); auto.
  apply val_rel_le_mono_step with n; auto.
Qed.

(** End of CumulativeMonotone.v *)
