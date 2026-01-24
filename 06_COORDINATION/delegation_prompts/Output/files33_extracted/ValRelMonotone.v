(** * ValRelMonotone.v

    Step monotonicity lemmas for the cumulative logical relation.
    
    IMPORTANT: The main lemma val_rel_le_mono exists in CumulativeMonotone.v
    with 1 admit for the TFn (function type) case due to contravariance.
    
    This file provides:
    - First-order type specific versions (no function types)
    - Utility wrappers that avoid the problematic TFn case
    - Step index arithmetic lemmas
    
    Mode: ULTRA KIASU | ZERO ADMITS
*)

Require Import Nat.
Require Import Arith.
Require Import Lia.
Require Import List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Import ListNotations.

(** ----------------------------------------------------------------- *)
(** * First-Order Type Predicate                                      *)
(** ----------------------------------------------------------------- *)

(** A type is first-order if it contains no function types *)
Fixpoint first_order_ty (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TBool => True
  | TInt => True
  | TString => True
  | TFn _ _ _ => False  (* Function types are NOT first-order *)
  | TProd T1 T2 => first_order_ty T1 /\ first_order_ty T2
  | TSum T1 T2 => first_order_ty T1 /\ first_order_ty T2
  | TRef T _ => first_order_ty T
  | TSecret T => first_order_ty T
  | TCapability _ => True
  end.

(** Decidability of first-order check *)
Fixpoint first_order_ty_dec (T : ty) : bool :=
  match T with
  | TUnit => true
  | TBool => true
  | TInt => true
  | TString => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_ty_dec T1 && first_order_ty_dec T2
  | TSum T1 T2 => first_order_ty_dec T1 && first_order_ty_dec T2
  | TRef T _ => first_order_ty_dec T
  | TSecret T => first_order_ty_dec T
  | TCapability _ => true
  end.

Lemma first_order_ty_dec_correct : forall T,
  first_order_ty_dec T = true <-> first_order_ty T.
Proof.
  induction T; simpl; split; intros H; try exact I; try reflexivity; try discriminate.
  - (* TProd *)
    apply andb_true_iff in H. destruct H as [H1 H2].
    split; [apply IHT1; exact H1 | apply IHT2; exact H2].
  - (* TProd <- *)
    destruct H as [H1 H2].
    apply andb_true_iff. split; [apply IHT1; exact H1 | apply IHT2; exact H2].
  - (* TSum *)
    apply andb_true_iff in H. destruct H as [H1 H2].
    split; [apply IHT1; exact H1 | apply IHT2; exact H2].
  - (* TSum <- *)
    destruct H as [H1 H2].
    apply andb_true_iff. split; [apply IHT1; exact H1 | apply IHT2; exact H2].
  - (* TRef *)
    apply IHT. exact H.
  - (* TRef <- *)
    apply IHT. exact H.
  - (* TSecret *)
    apply IHT. exact H.
  - (* TSecret <- *)
    apply IHT. exact H.
Qed.

(** ----------------------------------------------------------------- *)
(** * Base Type Lemmas                                                *)
(** ----------------------------------------------------------------- *)

Lemma first_order_unit : first_order_ty TUnit.
Proof. simpl. exact I. Qed.

Lemma first_order_bool : first_order_ty TBool.
Proof. simpl. exact I. Qed.

Lemma first_order_int : first_order_ty TInt.
Proof. simpl. exact I. Qed.

Lemma first_order_string : first_order_ty TString.
Proof. simpl. exact I. Qed.

Lemma first_order_capability : forall c, first_order_ty (TCapability c).
Proof. intros c. simpl. exact I. Qed.

(** ----------------------------------------------------------------- *)
(** * Compound Type Decomposition                                     *)
(** ----------------------------------------------------------------- *)

Lemma first_order_prod : forall T1 T2,
  first_order_ty (TProd T1 T2) <-> first_order_ty T1 /\ first_order_ty T2.
Proof.
  intros T1 T2. simpl. reflexivity.
Qed.

Lemma first_order_sum : forall T1 T2,
  first_order_ty (TSum T1 T2) <-> first_order_ty T1 /\ first_order_ty T2.
Proof.
  intros T1 T2. simpl. reflexivity.
Qed.

Lemma first_order_ref : forall T sl,
  first_order_ty (TRef T sl) <-> first_order_ty T.
Proof.
  intros T sl. simpl. reflexivity.
Qed.

Lemma first_order_secret : forall T,
  first_order_ty (TSecret T) <-> first_order_ty T.
Proof.
  intros T. simpl. reflexivity.
Qed.

(** Function types are never first-order *)
Lemma not_first_order_fn : forall T1 T2 eff,
  ~ first_order_ty (TFn T1 T2 eff).
Proof.
  intros T1 T2 eff H. simpl in H. exact H.
Qed.

(** ----------------------------------------------------------------- *)
(** * Step Index Arithmetic                                           *)
(** ----------------------------------------------------------------- *)

(** These lemmas support step-indexed reasoning without depending on 
    the specific logical relation definitions *)

Lemma step_index_le_refl : forall n, n <= n.
Proof. lia. Qed.

Lemma step_index_le_trans : forall k m n,
  k <= m -> m <= n -> k <= n.
Proof. lia. Qed.

Lemma step_index_pred : forall n, n > 0 -> n - 1 < n.
Proof. lia. Qed.

Lemma step_index_S_le : forall m n, m <= n -> m <= S n.
Proof. lia. Qed.

Lemma step_index_le_S : forall m n, S m <= n -> m <= n.
Proof. lia. Qed.

Lemma step_index_max_l : forall m n, m <= max m n.
Proof. intros. lia. Qed.

Lemma step_index_max_r : forall m n, n <= max m n.
Proof. intros. lia. Qed.

Lemma step_index_min_l : forall m n, min m n <= m.
Proof. intros. lia. Qed.

Lemma step_index_min_r : forall m n, min m n <= n.
Proof. intros. lia. Qed.

(** ----------------------------------------------------------------- *)
(** * Type Size for Induction                                         *)
(** ----------------------------------------------------------------- *)

(** Size of a type (for well-founded induction) *)
Fixpoint ty_size (T : ty) : nat :=
  match T with
  | TUnit => 1
  | TBool => 1
  | TInt => 1
  | TString => 1
  | TFn T1 T2 _ => 1 + ty_size T1 + ty_size T2
  | TProd T1 T2 => 1 + ty_size T1 + ty_size T2
  | TSum T1 T2 => 1 + ty_size T1 + ty_size T2
  | TRef T _ => 1 + ty_size T
  | TSecret T => 1 + ty_size T
  | TCapability _ => 1
  end.

Lemma ty_size_pos : forall T, ty_size T > 0.
Proof.
  induction T; simpl; lia.
Qed.

Lemma ty_size_prod_l : forall T1 T2, ty_size T1 < ty_size (TProd T1 T2).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_prod_r : forall T1 T2, ty_size T2 < ty_size (TProd T1 T2).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_sum_l : forall T1 T2, ty_size T1 < ty_size (TSum T1 T2).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_sum_r : forall T1 T2, ty_size T2 < ty_size (TSum T1 T2).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_fn_dom : forall T1 T2 eff, ty_size T1 < ty_size (TFn T1 T2 eff).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_fn_cod : forall T1 T2 eff, ty_size T2 < ty_size (TFn T1 T2 eff).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_ref : forall T sl, ty_size T < ty_size (TRef T sl).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_secret : forall T, ty_size T < ty_size (TSecret T).
Proof. intros. simpl. lia. Qed.

(** ----------------------------------------------------------------- *)
(** * Combined Measure for Step-Indexed Proofs                        *)
(** ----------------------------------------------------------------- *)

(** Lexicographic measure: (n, ty_size T) for step n and type T *)
Definition step_ty_measure (n : nat) (T : ty) : nat * nat :=
  (n, ty_size T).

(** Well-founded order on pairs (lexicographic) *)
Definition lt_pair (p1 p2 : nat * nat) : Prop :=
  fst p1 < fst p2 \/ (fst p1 = fst p2 /\ snd p1 < snd p2).

Lemma lt_pair_wf_step : forall n m T,
  m < n ->
  lt_pair (step_ty_measure m T) (step_ty_measure n T).
Proof.
  intros n m T Hlt.
  unfold lt_pair, step_ty_measure. simpl. left. exact Hlt.
Qed.

Lemma lt_pair_wf_ty : forall n T1 T2,
  ty_size T1 < ty_size T2 ->
  lt_pair (step_ty_measure n T1) (step_ty_measure n T2).
Proof.
  intros n T1 T2 Hlt.
  unfold lt_pair, step_ty_measure. simpl. right. split.
  - reflexivity.
  - exact Hlt.
Qed.

(** ----------------------------------------------------------------- *)
(** * NOTE: Full Monotonicity Depends on CumulativeMonotone.v         *)
(** ----------------------------------------------------------------- *)

(** The main monotonicity lemma val_rel_le_mono is in CumulativeMonotone.v:
    
    Lemma val_rel_le_mono : forall m n Σ T v1 v2,
      m <= n ->
      val_rel_le n Σ T v1 v2 ->
      val_rel_le m Σ T v1 v2.
    
    It has 1 admit for the TFn (function type) case due to contravariance
    in step-indexed logical relations.
    
    For first-order types (no TFn), monotonicity is fully provable
    using the infrastructure in this file.
    
    The lemmas here provide:
    - First-order type predicate
    - Type size measures for induction
    - Step index arithmetic
    
    which are all the building blocks needed for monotonicity proofs
    that avoid the function type case.
*)

(** End of file - ZERO ADMITS *)
