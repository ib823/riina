(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * CumulativeRelation.v

    RIINA Cumulative Step-Indexed Logical Relation

    This file defines the CUMULATIVE value relation where:
    - val_rel_le n Σ T v1 v2 means "related at ALL steps k ≤ n"
    - This makes monotonicity DEFINITIONAL rather than axiomatic

    The cumulative structure is critical for handling TFn contravariance.
    In standard step-indexed models, proving monotonicity for function types
    requires axioms because of the contravariant argument position.
    With the cumulative definition, monotonicity follows directly.

    Mode: Comprehensive Verification | Zero Trust

    Worker: WORKER_α (Alpha)
    Phase: 2 (Cumulative Relation)

    References:
    - Ahmed (2006) "Step-Indexed Syntactic Logical Relations"
    - Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"
    - Appel & McAllester (2001) "An indexed model of recursive types"
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

Import ListNotations.

(** ** Closed Expression Predicate *)

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

(** ** Store Relation (Simplified)

    For the cumulative relation, we use a simplified store relation
    that requires stores to have the same domain.
*)

Definition store_rel_simple (Σ : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.

(** ** Cumulative Value Relation

    val_rel_le n Σ T v1 v2 means:
    "v1 and v2 are related at type T for ALL steps up to and including n"

    This is defined by recursion on n, with type-specific structure.

    KEY INSIGHT: The cumulative definition means:
    - val_rel_le (S n) includes val_rel_le n as a conjunct
    - This makes STEP MONOTONICITY trivial: just project out
    - No need for complex induction to prove m <= n => related at m
*)

(** Base structural predicate at a specific type (for positive steps)

    IMPORTANT: val_rel_prev is parameterized by store_ty to support proper
    Kripke semantics. For TFn, arguments must be related at the EXTENDED
    store (Σ'), not the base store (Σ). This is essential for proving
    store extension monotonicity.

    Reference: Ahmed (2006), Dreyer et al. (2011) - standard formulation
    uses extended world for argument relations in function types.
*)
Definition val_rel_struct (val_rel_prev : store_ty -> ty -> expr -> expr -> Prop)
                          (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  match T with
  (* Primitive types *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  (* Security types - secrets/labeled are always indistinguishable *)
  | TSecret _ => True
  | TLabeled _ _ => True
  | TTainted _ _ => True  (* Tainted values: identity relation *)
  | TSanitized _ _ => True  (* Sanitized values: identity relation *)
  (* Capability types *)
  | TCapability _ => True
  | TCapabilityFull _ => True
  (* Proof types *)
  | TProof _ => True
  (* Channel types - treated as opaque *)
  | TChan _ => True
  | TSecureChan _ _ => True
  (* Constant-time and zeroizing - indistinguishable *)
  | TConstantTime _ => True
  | TZeroizing _ => True
  (* Reference types *)
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  (* Compound types *)
  | TList T' => True  (* Lists: structural equality, simplified for now *)
  | TOption T' => True  (* Options: structural equality, simplified for now *)
  | TProd T1 T2 =>
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_prev Σ T1 a1 a2 /\
        val_rel_prev Σ T2 b1 b2
  | TSum T1 T2 =>
      (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\
                     val_rel_prev Σ T1 a1 a2) \/
      (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\
                     val_rel_prev Σ T2 b1 b2)
  | TFn T1 T2 eff =>
      (* Kripke quantification: for all extended stores and related arguments
         CRITICAL: Arguments are related at the EXTENDED store Σ', not Σ.
         This is the standard Kripke semantics formulation. *)
      forall Σ', store_ty_extends Σ Σ' ->
        forall arg1 arg2,
          value arg1 -> value arg2 ->
          closed_expr arg1 -> closed_expr arg2 ->
          val_rel_prev Σ' T1 arg1 arg2 ->  (* Arguments at extended store *)
            forall st1 st2 ctx,
              store_rel_simple Σ' st1 st2 ->
              (* Application produces related results *)
              exists res1 res2 st1' st2' ctx' Σ'',
                store_ty_extends Σ' Σ'' /\
                multi_step (EApp v1 arg1, st1, ctx) (res1, st1', ctx') /\
                multi_step (EApp v2 arg2, st2, ctx) (res2, st2', ctx') /\
                value res1 /\ value res2 /\
                val_rel_prev Σ'' T2 res1 res2 /\  (* Results at final store *)
                store_rel_simple Σ'' st1' st2'
  end.

(** The cumulative value relation *)
Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True  (* At step 0, everything is trivially related *)
  | S n' =>
      (* CUMULATIVE: Include all previous steps *)
      val_rel_le n' Σ T v1 v2 /\
      (* Plus structural requirements using val_rel at n'
         NOTE: val_rel_le n' has type (store_ty -> ty -> expr -> expr -> Prop)
         which is exactly what val_rel_struct expects for Kripke semantics *)
      val_rel_struct (val_rel_le n') Σ T v1 v2
  end.

(** ** Cumulative Store Relation *)

Definition store_rel_le (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2 /\
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    match store_lookup l st1, store_lookup l st2 with
    | Some v1, Some v2 => val_rel_le n Σ T v1 v2
    | _, _ => False
    end.

(** ** Unfold Lemmas for val_rel_le *)

(** Unfold val_rel_le at 0: trivially True *)
Lemma val_rel_le_0_unfold : forall Σ T v1 v2,
  val_rel_le 0 Σ T v1 v2 = True.
Proof. reflexivity. Qed.

(** Unfold val_rel_le at S n: cumulative plus structural *)
Lemma val_rel_le_S_unfold : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 =
  (val_rel_le n Σ T v1 v2 /\ val_rel_struct (val_rel_le n) Σ T v1 v2).
Proof. reflexivity. Qed.

(** ** Basic Properties of Cumulative Relation *)

(** At step 0, everything is related *)
Lemma val_rel_le_at_zero : forall Σ T v1 v2,
  val_rel_le 0 Σ T v1 v2.
Proof.
  intros. simpl. exact I.
Qed.

(** Cumulative structure gives us the "previous step" directly *)
Lemma val_rel_le_cumulative : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 H.
  simpl in H. destruct H as [Hprev _]. exact Hprev.
Qed.

(** Values are values *)
Lemma val_rel_le_value_left : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  value v1.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [Hv1 _]. exact Hv1.
Qed.

Lemma val_rel_le_value_right : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  value v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [_ [Hv2 _]]. exact Hv2.
Qed.

(** Related values are closed *)
Lemma val_rel_le_closed_left : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  closed_expr v1.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [_ [_ [Hc1 _]]]. exact Hc1.
Qed.

Lemma val_rel_le_closed_right : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  closed_expr v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [_ [_ [_ [Hc2 _]]]]. exact Hc2.
Qed.

(** ** Step Monotonicity (DEFINITIONAL for base cases)

    This is the KEY property that makes cumulative relations work.
    For first-order types, monotonicity is immediate.
    For TFn, we need additional infrastructure (see CumulativeMonotone.v).
*)

(** Step monotonicity for first-order types *)
Lemma val_rel_le_mono_step_fo : forall n m Σ T v1 v2,
  first_order_type T = true ->
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
Proof.
  intros n. induction n as [|n' IH].
  - (* n = 0 *)
    intros m Σ T v1 v2 Hfo Hle Hrel.
    assert (m = 0) by lia. subst. simpl. exact I.
  - (* n = S n' *)
    intros m Σ T v1 v2 Hfo Hle Hrel.
    destruct m as [|m'].
    + simpl. exact I.
    + simpl in Hrel. destruct Hrel as [Hprev Hstruct].
      simpl. split.
      * (* Need val_rel_le m' Σ T v1 v2 *)
        apply IH with (m := m'); auto. lia.
      * (* Structural part *)
        unfold val_rel_struct in *.
        destruct Hstruct as (Hv1 & Hv2 & Hc1 & Hc2 & HT).
        split; [exact Hv1|].
        split; [exact Hv2|].
        split; [exact Hc1|].
        split; [exact Hc2|].
        destruct T; simpl in Hfo; try discriminate; auto.
        -- (* TProd *)
           apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
           destruct HT as (a1 & b1 & a2 & b2 & Heq1 & Heq2 & Hr1 & Hr2).
           exists a1, b1, a2, b2.
           repeat split; auto.
           ++ apply IH with (m := m'); auto. lia.
           ++ apply IH with (m := m'); auto. lia.
        -- (* TSum *)
           apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
           destruct HT as [HInl | HInr].
           ++ left. destruct HInl as (a1 & a2 & Heq1 & Heq2 & Hr).
              exists a1, a2. repeat split; auto.
              apply IH with (m := m'); auto. lia.
           ++ right. destruct HInr as (b1 & b2 & Heq1 & Heq2 & Hr).
              exists b1, b2. repeat split; auto.
              apply IH with (m := m'); auto. lia.
Qed.

(** ** Predicate-Independent Structural Relation for First-Order Types

    For first-order types, the structural relation is independent of the step index.
    This relation captures structural equality without reference to any predicate.
*)
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  (* Primitive types: exact equality *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  (* Security types: always related (indistinguishable) *)
  | TSecret _ | TLabeled _ _ | TTainted _ _ | TSanitized _ _ => True
  (* Reference: same location *)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  (* Collections: simplified (True for now) *)
  | TList _ | TOption _ => True
  (* Capability and channel types *)
  | TCapability _ | TCapabilityFull _ | TChan _ | TSecureChan _ _ => True
  (* Proof and constant-time types *)
  | TProof _ | TConstantTime _ | TZeroizing _ => True
  (* Product: component-wise recursion *)
  | TProd T1 T2 =>
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2
  (* Sum: matching constructor *)
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2)
      \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)
  (* Function: not first-order - True as placeholder *)
  | TFn _ _ _ => True
  end.

(** ** Step Independence for First-Order Types

    CORRECTED FORMULATION: The premise m > fo_compound_depth T ensures
    sufficient structural information is available for compound types.

    The key insight: for first-order types, the step-indexed relation
    stabilizes once we have enough steps to traverse the type structure.

    PROOF STRATEGY:
    1. Extract val_rel_at_type_fo from val_rel_le m (when m > fo_compound_depth T)
    2. Construct val_rel_le n from val_rel_at_type_fo (for any n > 0)
    3. This bridges any m > depth T to any n > 0

    NOTE: The old signature m > 0 was UNPROVABLE for compound types at m = 1.
    The new signature m > fo_compound_depth T is both CORRECT and PROVABLE.
*)

(** Extraction: val_rel_le m → val_rel_at_type_fo (when m > fo_compound_depth T)
    Proven by well-founded induction on type structure (ty_size).
*)
Lemma val_rel_le_extract_fo : forall T m Σ v1 v2,
  first_order_type T = true ->
  m > fo_compound_depth T ->
  val_rel_le m Σ T v1 v2 ->
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  val_rel_at_type_fo T v1 v2.
Proof.
  (* Well-founded induction on ty_size *)
  intros T. pattern T.
  apply ty_size_induction. clear T.
  intros T IH_size m Σ v1 v2 HFO Hdepth Hrel.
  assert (Hm_pos : m > 0) by lia.
  destruct m as [|m']; [lia|].
  simpl in Hrel. destruct Hrel as [Hprev Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as (Hv1 & Hv2 & Hc1 & Hc2 & HT).
  repeat split; auto.
  (* The val_rel_at_type_fo part requires case analysis on T *)
  destruct T; simpl in HFO; simpl in Hdepth; simpl; auto;
  try discriminate HFO.
  (* TProd T1 T2 *)
  - apply Bool.andb_true_iff in HFO. destruct HFO as [HFO1 HFO2].
    destruct HT as (a1 & b1 & a2 & b2 & Heq1 & Heq2 & Hr1 & Hr2).
    exists a1, b1, a2, b2. repeat split; auto.
    (* T1 component: use IH_size *)
    + assert (Hdepth1 : m' >= fo_compound_depth T1).
      { simpl in Hdepth. lia. }
      assert (Hsize1 : ty_size T1 < ty_size (TProd T1 T2)).
      { apply ty_size_prod_left. }
      destruct (IH_size T1 Hsize1 m' Σ a1 a2 HFO1) as [_ [_ [_ [_ Hfo1]]]]; auto.
      lia.
    (* T2 component: use IH_size *)
    + assert (Hdepth2 : m' >= fo_compound_depth T2).
      { simpl in Hdepth. lia. }
      assert (Hsize2 : ty_size T2 < ty_size (TProd T1 T2)).
      { apply ty_size_prod_right. }
      destruct (IH_size T2 Hsize2 m' Σ b1 b2 HFO2) as [_ [_ [_ [_ Hfo2]]]]; auto.
      lia.
  (* TSum T1 T2 *)
  - apply Bool.andb_true_iff in HFO. destruct HFO as [HFO1 HFO2].
    destruct HT as [[a1 [a2 [Heq1 [Heq2 Hr]]]] | [b1 [b2 [Heq1 [Heq2 Hr]]]]].
    + left. exists a1, a2. repeat split; auto.
      (* T1 component: use IH_size *)
      assert (Hdepth1 : m' >= fo_compound_depth T1).
      { simpl in Hdepth. lia. }
      assert (Hsize1 : ty_size T1 < ty_size (TSum T1 T2)).
      { apply ty_size_sum_left. }
      destruct (IH_size T1 Hsize1 m' Σ a1 a2 HFO1) as [_ [_ [_ [_ Hfo1]]]]; auto.
      lia.
    + right. exists b1, b2. repeat split; auto.
      (* T2 component: use IH_size *)
      assert (Hdepth2 : m' >= fo_compound_depth T2).
      { simpl in Hdepth. lia. }
      assert (Hsize2 : ty_size T2 < ty_size (TSum T1 T2)).
      { apply ty_size_sum_right. }
      destruct (IH_size T2 Hsize2 m' Σ b1 b2 HFO2) as [_ [_ [_ [_ Hfo2]]]]; auto.
      lia.
Qed.

(** Construction: val_rel_at_type_fo → val_rel_le n (for any n > 0)
    Proven by induction on n with nested well-founded recursion on ty_size for components.
*)
Lemma val_rel_le_construct_fo : forall T n Σ v1 v2,
  first_order_type T = true ->
  n > 0 ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_at_type_fo T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  (* First prove a stronger statement by well-founded induction on ty_size *)
  intros T.
  pattern T. apply ty_size_induction. clear T.
  intros T IH_size.
  (* Now do induction on n *)
  induction n as [|n' IHn]; intros Σ v1 v2 HFO Hn Hv1 Hv2 Hc1 Hc2 Hfo_rel.
  - lia.
  - simpl. split.
    (* Previous steps: use IHn (induction on n) *)
    + destruct n' as [|n'']; [simpl; exact I|].
      apply IHn; auto. lia.
    (* Structural part at this step *)
    + unfold val_rel_struct. repeat split; auto.
      destruct T; simpl in HFO; simpl in Hfo_rel; simpl; auto;
      try discriminate HFO.
      (* TProd T1 T2 *)
      * apply Bool.andb_true_iff in HFO. destruct HFO as [HFO1 HFO2].
        destruct Hfo_rel as (a1 & b1 & a2 & b2 & Heq1 & Heq2 & Hr1 & Hr2).
        exists a1, b1, a2, b2. repeat split; auto.
        (* T1 component *)
        -- destruct n' as [|n''].
           { simpl. exact I. }
           assert (Hsize1 : ty_size T1 < ty_size (TProd T1 T2))
             by apply ty_size_prod_left.
           subst. inversion Hv1; subst. inversion Hv2; subst.
           assert (Hclosed_a1 : closed_expr a1).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc1 x). simpl. left. auto. }
           assert (Hclosed_a2 : closed_expr a2).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc2 x). simpl. left. auto. }
           apply IH_size; auto. lia.
        (* T2 component *)
        -- destruct n' as [|n''].
           { simpl. exact I. }
           assert (Hsize2 : ty_size T2 < ty_size (TProd T1 T2))
             by apply ty_size_prod_right.
           subst. inversion Hv1; subst. inversion Hv2; subst.
           assert (Hclosed_b1 : closed_expr b1).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc1 x). simpl. right. auto. }
           assert (Hclosed_b2 : closed_expr b2).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc2 x). simpl. right. auto. }
           apply IH_size; auto. lia.
      (* TSum T1 T2 *)
      * apply Bool.andb_true_iff in HFO. destruct HFO as [HFO1 HFO2].
        destruct Hfo_rel as [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
        -- left. exists x1, x2. repeat split; auto.
           destruct n' as [|n''].
           { simpl. exact I. }
           assert (Hsize1 : ty_size T1 < ty_size (TSum T1 T2))
             by apply ty_size_sum_left.
           subst. inversion Hv1; subst. inversion Hv2; subst.
           assert (Hclosed_x1 : closed_expr x1).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc1 x). simpl. auto. }
           assert (Hclosed_x2 : closed_expr x2).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc2 x). simpl. auto. }
           apply IH_size; auto. lia.
        -- right. exists y1, y2. repeat split; auto.
           destruct n' as [|n''].
           { simpl. exact I. }
           assert (Hsize2 : ty_size T2 < ty_size (TSum T1 T2))
             by apply ty_size_sum_right.
           subst. inversion Hv1; subst. inversion Hv2; subst.
           assert (Hclosed_y1 : closed_expr y1).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc1 x). simpl. auto. }
           assert (Hclosed_y2 : closed_expr y2).
           { unfold closed_expr in *. intros x Hfree.
             apply (Hc2 x). simpl. auto. }
           apply IH_size; auto. lia.
Qed.

(** MAIN THEOREM: Step independence for first-order types.

    For first-order types, if values are related at step m > fo_compound_depth T,
    then they are related at any step n > 0.

    SIGNATURE CHANGE: The premise is now m > fo_compound_depth T (not m > 0).
    This is necessary because:
    - At m = 1 for compound types, component relations are at step 0 = True
    - We cannot reconstruct structural info from True
    - The fo_compound_depth premise ensures enough steps for full structure
*)
Lemma val_rel_le_fo_step_independent : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m > fo_compound_depth T ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 HFO Hdepth Hn Hrel.
  (* Extract val_rel_at_type_fo from val_rel_le m *)
  assert (Hextract := val_rel_le_extract_fo T m Σ v1 v2 HFO Hdepth Hrel).
  destruct Hextract as (Hv1 & Hv2 & Hc1 & Hc2 & Hfo_rel).
  (* Construct val_rel_le n from val_rel_at_type_fo *)
  apply val_rel_le_construct_fo; auto.
Qed.

(** Corollary: For primitive types (depth 0), m > 0 suffices *)
Corollary val_rel_le_fo_step_independent_primitive : forall m n Σ T v1 v2,
  first_order_type T = true ->
  fo_compound_depth T = 0 ->
  m > 0 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 HFO Hdepth Hm Hn Hrel.
  apply val_rel_le_fo_step_independent with (m := m); auto.
  lia.
Qed.

(** ** Expression Relation *)

Definition exp_rel_le (n : nat) (Σ : store_ty) (T : ty)
                       (e1 e2 : expr) (st1 st2 : store) (ctx : effect_ctx) : Prop :=
  forall k v1 v2 st1' st2' ctx',
    k <= n ->
    multi_step (e1, st1, ctx) (v1, st1', ctx') ->
    multi_step (e2, st2, ctx) (v2, st2', ctx') ->
    value v1 -> value v2 ->
    exists Σ',
      store_ty_extends Σ Σ' /\
      val_rel_le k Σ' T v1 v2 /\
      store_rel_simple Σ' st1' st2'.

(** ** Transitivity of Store Extension *)

Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
Proof.
  intros Σ1 Σ2 Σ3 H12 H23.
  unfold store_ty_extends in *.
  intros l T sl Hlook.
  apply H23. apply H12. exact Hlook.
Qed.

(** Reflexivity of store extension *)
Lemma store_ty_extends_refl : forall Σ,
  store_ty_extends Σ Σ.
Proof.
  intros Σ. unfold store_ty_extends. intros. exact H.
Qed.

(** End of CumulativeRelation.v *)
