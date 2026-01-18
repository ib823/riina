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

Import ListNotations.

(** ** Full Step Monotonicity

    For TFn, step monotonicity requires careful handling.
    We state the theorem and provide a proof that handles
    first-order types completely, with TFn admitted.
*)

(** Full step monotonicity

    For first-order types, monotonicity follows from the cumulative structure.
    For TFn, we handle two cases:
    1. Argument type T1 is first-order: use step-mono on args and results
    2. Argument type T1 is higher-order: requires additional reasoning about
       function equivalence (admitted for now, will be proven in Phase 1)
*)
Theorem val_rel_le_mono_step : forall n m Σ T v1 v2,
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
Proof.
  (* For first-order types, use val_rel_le_mono_step_fo from CumulativeRelation *)
  (* For TFn, we need additional structure *)
  intros n m Σ T v1 v2 Hle Hrel.
  destruct (first_order_decidable T) as [Hfo | Hho].
  - (* First-order: use proven lemma *)
    apply val_rel_le_mono_step_fo with n; auto.
  - (* Higher-order: general case *)
    (* For TFn, we use strong induction on n with the cumulative structure *)
    revert m Σ T v1 v2 Hle Hrel Hho.
    induction n as [|n' IH]; intros m Σ T v1 v2 Hle Hrel Hho.
    + assert (m = 0) by lia. subst. simpl. exact I.
    + destruct m as [|m'].
      * simpl. exact I.
      * simpl in Hrel. simpl.
        destruct Hrel as [Hprev Hstruct].
        split.
        -- (* Cumulative part *)
           apply IH; auto. lia.
        -- (* Structural part *)
           unfold val_rel_struct in *.
           destruct Hstruct as (Hv1 & Hv2 & Hc1 & Hc2 & HT).
           repeat split; auto.
           (* The type T must be TFn since it's not first-order *)
           destruct T; simpl in Hho; try discriminate; auto.
           (* Now we're in the TFn case: TFn T1 T2 e *)
           (* Case analysis on whether the argument type T1 is first-order *)
           destruct (first_order_decidable T1) as [HfoT1 | HhoT1].
           ++ (* Argument type T1 is first-order *)
              (* This case requires step independence for first-order types.
                 The proof uses val_rel_le_fo_step_independent to lift args
                 from level m' to level n', then applies HT, then steps down
                 the results from n' to m'.

                 Edge cases:
                 - m' = 0: results at level 0 are trivial
                 - n' = 0: args at level 0 are trivial

                 The proof is straightforward but involves careful case analysis.
                 Admitted for now - will be completed in Phase 1. *)
              admit.
           ++ (* Argument type T1 is higher-order: complex case *)
              (* The contravariant position with higher-order arg type
                 requires proving that functions with same behavior at n'
                 also have same behavior at m' < n'.

                 This requires function extensionality or similar reasoning.
                 Admitted for now - will be completed in Phase 1. *)
              admit.
Admitted.

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
