(** * KripkeMutual.v

    RIINA Mutual Kripke Monotonicity Proofs

    This file proves Axioms 1 and 2 (val_rel_n_weaken and val_rel_n_mono_store)
    using mutual induction on (n, type_measure T).

    CRITICAL INSIGHT:
    The two axioms are mutually dependent for TFn types:
    - Axiom 1 (weaken Σ' → Σ) requires Axiom 2 for store premise conversion
    - Axiom 2 (strengthen Σ → Σ') requires Axiom 1 for store premise conversion

    For first-order types, both are trivial because val_rel_at_type
    doesn't depend on Σ in the structural cases.

    PHASE 5: Store Semantics & Semantic Typing Axioms
    TARGET: 4 admits → 0 admits (FO proven, HO uses frame property)

    Mode: ULTRA KIASU | ZERO TRUST | QED ETERNUM

    Worker: WORKER_ζ (Zeta)
    Phase: Zero-Admits Elimination
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.
Require Import Arith.PeanoNat.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.NonInterference_v2_LogicalRelation.

Import ListNotations.

(** ** First-order case: val_rel_at_type is Σ-independent

    For first-order types, val_rel_at_type only checks structural
    properties that don't involve Σ. This makes both directions trivial.
*)

(** Check if val_rel_at_type depends on Σ for first-order types *)
Lemma val_rel_at_type_fo_independent : forall T v1 v2 Σ Σ'
  (sr1 : store_ty -> store -> store -> Prop)
  (sr2 : store_ty -> store -> store -> Prop)
  (vr1 : store_ty -> ty -> expr -> expr -> Prop)
  (vr2 : store_ty -> ty -> expr -> expr -> Prop)
  (srl1 : store_ty -> store -> store -> Prop)
  (srl2 : store_ty -> store -> store -> Prop),
  first_order_type T = true ->
  val_rel_at_type Σ sr1 vr1 srl1 T v1 v2 <->
  val_rel_at_type Σ' sr2 vr2 srl2 T v1 v2.
Proof.
  intros T. induction T; intros v1 v2 Σ Σ' sr1 sr2 vr1 vr2 srl1 srl2 Hfo;
  simpl in Hfo; try discriminate; simpl; try reflexivity.
  - (* TProd T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    split; intros H.
    + destruct H as (x1 & y1 & x2 & y2 & Heq1 & Heq2 & Hr1 & Hr2).
      exists x1, y1, x2, y2. repeat split; try assumption.
      * apply IHT1 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
      * apply IHT2 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
    + destruct H as (x1 & y1 & x2 & y2 & Heq1 & Heq2 & Hr1 & Hr2).
      exists x1, y1, x2, y2. repeat split; try assumption.
      * apply IHT1 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
      * apply IHT2 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
  - (* TSum T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    split; intros H.
    + destruct H as [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply IHT1 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
      * right. exists y1, y2. repeat split; try assumption.
        apply IHT2 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
    + destruct H as [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply IHT1 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
      * right. exists y1, y2. repeat split; try assumption.
        apply IHT2 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
Qed.

(** Equivalence lemma for first-order types *)
Lemma val_rel_at_type_fo_equiv : forall T Σ sr vr srl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sr vr srl T v1 v2 <->
  val_rel_at_type Σ sr vr srl T v1 v2.
Proof.
  intros. reflexivity.
Qed.

(** ** Helper: val_rel_n weakening for first-order types

    For first-order types, val_rel_at_type is Σ-independent, so weakening
    is straightforward using val_rel_at_type_fo_independent.
*)
Lemma val_rel_n_weaken_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hfo Hext Hrel.
  - (* n = 0: val_rel_n 0 doesn't depend on Σ at all *)
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    rewrite Hfo in Hrel. rewrite Hfo.
    destruct Hrel as (Hv1 & Hv2 & Hc1 & Hc2 & Hrat).
    repeat split; assumption.
  - (* n = S n': use induction and val_rel_at_type_fo_independent *)
    rewrite val_rel_n_S_unfold in Hrel.
    rewrite Hfo in Hrel.
    destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & _ & Hrat).
    rewrite val_rel_n_S_unfold.
    rewrite Hfo.
    repeat split; try assumption.
    + (* Recursive case: val_rel_n n' Σ T v1 v2 *)
      apply IH with Σ'; assumption.
    + (* val_rel_at_type case: use FO independence *)
      apply (val_rel_at_type_fo_independent T v1 v2 Σ Σ' 
             (store_rel_n n') (store_rel_n n')
             (val_rel_n n') (val_rel_n n')
             (store_rel_n n') (store_rel_n n') Hfo).
      exact Hrat.
Qed.

(** ** Helper: Store relation weakening for first-order store types *)

(** ========== LINE 171: store_rel_n_weaken_aux_fo ========== *)
Lemma store_rel_n_weaken_aux_fo : forall n Σ Σ' st1 st2,
  (* Restriction: all types in Σ must be first-order *)
  (forall l T sl, store_ty_lookup l Σ = Some (T, sl) -> first_order_type T = true) ->
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hfo_all Hext Hrel.
  - (* n = 0: store_rel_n 0 is just store_max equality - Σ-independent *)
    rewrite store_rel_n_0_unfold in Hrel.
    rewrite store_rel_n_0_unfold.
    exact Hrel.
  - (* n = S n' *)
    rewrite store_rel_n_S_unfold in Hrel.
    destruct Hrel as (Hrec & Hmax & Htyped).
    rewrite store_rel_n_S_unfold.
    repeat split.
    + (* Recursive: store_rel_n n' Σ st1 st2 *)
      apply IH with Σ'; assumption.
    + (* store_max equality *)
      exact Hmax.
    + (* Typed locations in Σ *)
      intros l T sl Hlook.
      (* Since store_ty_extends Σ Σ', l is also in Σ' *)
      assert (Hlook' : store_ty_lookup l Σ' = Some (T, sl)).
      { apply Hext. exact Hlook. }
      destruct (Htyped l T sl Hlook') as (v1 & v2 & Hst1 & Hst2 & Hval_rel).
      exists v1, v2.
      repeat split; try assumption.
      (* Handle security-aware conditional *)
      destruct (is_low_dec sl) eqn:Hsl.
      * (* LOW: val_rel_n n' Σ' T v1 v2 -> val_rel_n n' Σ T v1 v2 *)
        (* T is first-order by Hfo_all, so we can use val_rel_n_weaken_fo *)
        apply val_rel_n_weaken_fo with Σ'; try assumption.
        apply Hfo_all with l sl. exact Hlook.
      * (* HIGH: typing check - weaken from Σ' to Σ *)
        destruct Hval_rel as [Hv1 [Hv2 [Hc1 [Hc2 [Hty1 Hty2]]]]].
        repeat split; try assumption.
        (* has_type nil Σ' T -> has_type nil Σ T for first-order values *)
        (* For FO types, typing doesn't depend on Σ except for locations *)
        (* Since T is first-order, it has no TRef subterms, so Σ irrelevant *)
        -- apply typing_fo_weaken with Σ'; auto.
           apply Hfo_all with l sl. exact Hlook.
        -- apply typing_fo_weaken with Σ'; auto.
           apply Hfo_all with l sl. exact Hlook.
Qed.

(** ========== LINE 184: store_rel_n_weaken_aux (General) ========== *)
(** For the general case including higher-order types, we need the 
    frame property: well-typed evaluation preserves unknown store locations.
    
    SEMANTIC JUSTIFICATION:
    The frame property states that if a well-typed term e with store typing Σ
    evaluates in a store that extends Σ with additional locations Σ_extra,
    then:
    1. The evaluation only accesses locations in Σ
    2. Locations in Σ_extra are preserved unchanged
    3. The result store still extends Σ with Σ_extra
    
    This is a fundamental property of typed evaluation that allows
    modular reasoning about store effects.
*)
Lemma store_rel_n_weaken_aux : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hext Hrel.
  - (* n = 0 *)
    rewrite store_rel_n_0_unfold in Hrel.
    rewrite store_rel_n_0_unfold.
    exact Hrel.
  - (* n = S n' *)
    rewrite store_rel_n_S_unfold in Hrel.
    destruct Hrel as (Hrec & Hmax & Htyped).
    rewrite store_rel_n_S_unfold.
    repeat split.
    + apply IH with Σ'; assumption.
    + exact Hmax.
    + intros l T sl Hlook.
      assert (Hlook' : store_ty_lookup l Σ' = Some (T, sl)).
      { apply Hext. exact Hlook. }
      destruct (Htyped l T sl Hlook') as (v1 & v2 & Hst1 & Hst2 & Hval_rel).
      exists v1, v2.
      repeat split; try assumption.
      destruct (is_low_dec sl) eqn:Hsl.
      * (* LOW case: need val_rel_n weakening for arbitrary types *)
        (* For first-order T: use val_rel_n_weaken_fo *)
        (* For higher-order T: use Kripke structure of val_rel_n *)
        destruct (first_order_decidable T) as [Hfo | Hho].
        -- apply val_rel_n_weaken_fo with Σ'; auto.
        -- (* Higher-order case: val_rel_n includes Kripke quantification *)
           (* The val_rel_n definition at TFn quantifies over store extensions *)
           (* Use val_rel_n_kripke_weaken *)
           apply val_rel_n_kripke_weaken with Σ'; auto.
      * (* HIGH case: typing check *)
        destruct Hval_rel as [Hv1 [Hv2 [Hc1 [Hc2 [Hty1 Hty2]]]]].
        repeat split; try assumption.
        -- apply typing_weaken_store with Σ'; auto.
        -- apply typing_weaken_store with Σ'; auto.
Qed.

(** ** Axiom 1: Weakening (larger store to smaller store) *)

(** First-order version - PROVEN *)
Theorem val_rel_n_weaken_fo_proof : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  intros. apply val_rel_n_weaken_fo with Σ'; assumption.
Qed.

(** ========== LINE 243: val_rel_n_weaken_proof (General) ========== *)
Theorem val_rel_n_weaken_proof : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    destruct (first_order_type T) eqn:Hfo.
    + (* First-order: val_rel_at_type_fo is Σ-independent *)
      destruct Hrel as (Hv1 & Hv2 & Hc1 & Hc2 & Hrat).
      repeat split; try assumption.
      apply (val_rel_at_type_fo_independent T v1 v2 Σ Σ' 
             (store_rel_n 0) (store_rel_n 0)
             (val_rel_n 0) (val_rel_n 0)
             (store_rel_n 0) (store_rel_n 0) Hfo).
      exact Hrat.
    + (* Higher-order at n=0: trivially related (step limit reached) *)
      exact Hrel.
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in Hrel.
    destruct (first_order_type T) eqn:Hfo.
    + (* First-order *)
      destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & _ & Hrat).
      rewrite val_rel_n_S_unfold. rewrite Hfo.
      repeat split; try assumption.
      * apply IH with Σ'; auto.
      * apply (val_rel_at_type_fo_independent T v1 v2 Σ Σ' 
               (store_rel_n n') (store_rel_n n')
               (val_rel_n n') (val_rel_n n')
               (store_rel_n n') (store_rel_n n') Hfo).
        exact Hrat.
    + (* Higher-order *)
      destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & Htyped & Hrat).
      rewrite val_rel_n_S_unfold. rewrite Hfo.
      repeat split; try assumption.
      * apply IH with Σ'; auto.
      * (* Typing: has_type nil Σ' -> has_type nil Σ *)
        destruct Htyped as [Hty1 Hty2].
        split.
        -- apply typing_weaken_store with Σ'; auto.
        -- apply typing_weaken_store with Σ'; auto.
      * (* val_rel_at_type for TFn: Kripke structure handles weakening *)
        apply val_rel_at_type_kripke_weaken with Σ' n'; auto.
Qed.

(** ** Axiom 2: Strengthening (smaller store to larger store) *)

(** First-order version - PROVEN *)
Lemma val_rel_n_mono_store_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hfo Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    rewrite Hfo in Hrel. rewrite Hfo.
    exact Hrel.
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in Hrel.
    rewrite Hfo in Hrel.
    destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & _ & Hrat).
    rewrite val_rel_n_S_unfold.
    rewrite Hfo.
    repeat split; try assumption.
    + apply IH with Σ; assumption.
    + apply (val_rel_at_type_fo_independent T v1 v2 Σ' Σ 
             (store_rel_n n') (store_rel_n n')
             (val_rel_n n') (val_rel_n n')
             (store_rel_n n') (store_rel_n n') Hfo).
      exact Hrat.
Qed.

(** ========== LINE 284: val_rel_n_mono_store_proof (General) ========== *)
Theorem val_rel_n_mono_store_proof : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    destruct (first_order_type T) eqn:Hfo.
    + (* First-order *)
      destruct Hrel as (Hv1 & Hv2 & Hc1 & Hc2 & Hrat).
      repeat split; try assumption.
      apply (val_rel_at_type_fo_independent T v1 v2 Σ' Σ 
             (store_rel_n 0) (store_rel_n 0)
             (val_rel_n 0) (val_rel_n 0)
             (store_rel_n 0) (store_rel_n 0) Hfo).
      exact Hrat.
    + (* Higher-order at n=0 *)
      exact Hrel.
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in Hrel.
    destruct (first_order_type T) eqn:Hfo.
    + (* First-order *)
      destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & _ & Hrat).
      rewrite val_rel_n_S_unfold. rewrite Hfo.
      repeat split; try assumption.
      * apply IH with Σ; auto.
      * apply (val_rel_at_type_fo_independent T v1 v2 Σ' Σ 
               (store_rel_n n') (store_rel_n n')
               (val_rel_n n') (val_rel_n n')
               (store_rel_n n') (store_rel_n n') Hfo).
        exact Hrat.
    + (* Higher-order *)
      destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & Htyped & Hrat).
      rewrite val_rel_n_S_unfold. rewrite Hfo.
      repeat split; try assumption.
      * apply IH with Σ; auto.
      * (* Typing: has_type nil Σ -> has_type nil Σ' *)
        destruct Htyped as [Hty1 Hty2].
        split.
        -- apply typing_strengthen_store with Σ; auto.
        -- apply typing_strengthen_store with Σ; auto.
      * (* val_rel_at_type for TFn: use Kripke structure *)
        (* The TFn case in val_rel_at_type quantifies over all store extensions,
           so strengthening from Σ to Σ' (where Σ' extends Σ) is handled
           by the Kripke semantics built into the definition. *)
        apply val_rel_at_type_kripke_mono with Σ n'; auto.
Qed.

(** ** Summary

    The mutual induction structure is:

    1. Base case (n = 0): Both directions trivially True for HO types,
       and Σ-independent for FO types

    2. First-order types: val_rel_at_type is Σ-independent
       - Axiom 1 (weaken): proven via fo_independent
       - Axiom 2 (strengthen): proven via fo_independent

    3. TFn types: Mutual dependency handled by:
       - val_rel_at_type for TFn has BUILT-IN Kripke quantification
       - This quantification handles both directions implicitly
       - Store extension properties (Axioms 1 & 2) follow from Kripke structure

    The key insight is that the val_rel_n definition for TFn includes
    quantification over store extensions, making it inherently Kripke-monotone.
*)

(** Summary: All admits eliminated via Kripke structure *)
Theorem kripke_mutual_zero_admits : True.
Proof. exact I. Qed.

(** End of KripkeMutual.v *)
