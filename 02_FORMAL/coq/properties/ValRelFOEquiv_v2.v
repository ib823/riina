(** * First-Order Type Predicate Independence - COMPILATION PERFECT
    
    This file proves that for first-order types, val_rel_at_type
    is independent of the predicate parameters.
    
    Mode: ULTRA KIASU | ZERO COMPILATION ERRORS
    Date: 2026-01-18
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ========================================================================
    SECTION 1: FIRST-ORDER TYPE CLASSIFICATION
    ======================================================================== *)

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit => true
  | TBool => true
  | TInt => true
  | TString => true
  | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList T' => first_order_type T'
  | TOption T' => first_order_type T'
  | TRef T' _ => first_order_type T'
  | TSecret T' => first_order_type T'
  | TLabeled T' _ => first_order_type T'
  | TTainted T' _ => first_order_type T'
  | TSanitized T' _ => first_order_type T'
  | TProof T' => first_order_type T'
  | TCapability _ => true
  | TCapabilityFull _ => true
  | TChan _ => false
  | TSecureChan _ _ => false
  | TConstantTime T' => first_order_type T'
  | TZeroizing T' => first_order_type T'
  end.

(** ========================================================================
    SECTION 2: FIRST-ORDER VALUE RELATION (PREDICATE INDEPENDENT)
    ======================================================================== *)

Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret T' => True
  | TLabeled T' _ => True
  | TTainted T' _ => True
  | TSanitized T' _ => True
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList T' => True
  | TOption T' => True
  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type_fo T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type_fo T2 y1 y2)
  | TFn _ _ _ => True
  | TCapability _ => True
  | TCapabilityFull _ => True
  | TProof _ => True
  | TChan _ => True
  | TSecureChan _ _ => True
  | TConstantTime T' => True
  | TZeroizing T' => True
  end.

(** ========================================================================
    SECTION 3: EXTRACTION LEMMAS
    ======================================================================== *)

(** Extract SAME boolean from val_rel_at_type_fo TBool *)
Lemma fo_bool_same : forall v1 v2,
  val_rel_at_type_fo TBool v1 v2 ->
  exists b, v1 = EBool b /\ v2 = EBool b.
Proof.
  intros v1 v2 H.
  simpl in H. exact H.
Qed.

(** Extract MATCHING constructors from val_rel_at_type_fo TSum *)
Lemma fo_sum_match : forall T1 T2 v1 v2,
  val_rel_at_type_fo (TSum T1 T2) v1 v2 ->
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_at_type_fo T1 a1 a2) \/
  (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_at_type_fo T2 b1 b2).
Proof.
  intros T1 T2 v1 v2 H.
  simpl in H. exact H.
Qed.

(** Extract pair structure from val_rel_at_type_fo TProd *)
Lemma fo_prod_struct : forall T1 T2 v1 v2,
  val_rel_at_type_fo (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2.
Proof.
  intros T1 T2 v1 v2 H.
  simpl in H. exact H.
Qed.

(** ========================================================================
    SECTION 4: FO TYPES ARE PREDICATE-INDEPENDENT (MAIN THEOREM)
    ========================================================================
    
    For first-order types, val_rel_at_type with ANY predicates
    is equivalent to val_rel_at_type_fo (which uses no predicates).
    
    This is because FO types never reach the TFn case.
*)

(** Closed expression *)
Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(** Parameterized val_rel_at_type *)
Section ValRelAtN.
  Variable Sigma : store_ty.
  Variable store_pred : store_ty -> store -> store -> Prop.
  Variable val_pred : store_ty -> ty -> expr -> expr -> Prop.
  Variable store_result : store_ty -> store -> store -> Prop.

  Fixpoint val_rel_at_type (T : ty) (v1 v2 : expr) {struct T} : Prop :=
    match T with
    | TUnit => v1 = EUnit /\ v2 = EUnit
    | TBool => exists b, v1 = EBool b /\ v2 = EBool b
    | TInt => exists i, v1 = EInt i /\ v2 = EInt i
    | TString => exists s, v1 = EString s /\ v2 = EString s
    | TBytes => v1 = v2
    | TSecret T' => True
    | TLabeled T' _ => True
    | TTainted T' _ => True
    | TSanitized T' _ => True
    | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
    | TList T' => True
    | TOption T' => True
    | TProd T1 T2 =>
        exists x1 y1 x2 y2,
          v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
          val_rel_at_type T1 x1 x2 /\ val_rel_at_type T2 y1 y2
    | TSum T1 T2 =>
        (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type T1 x1 x2) \/
        (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type T2 y1 y2)
    | TFn T1 T2 eff =>
        forall Sigma', store_ty_extends Sigma Sigma' ->
          forall x y,
            value x -> value y -> closed_expr x -> closed_expr y ->
            val_pred Sigma' T1 x y ->
            forall st1 st2 ctx,
              store_pred Sigma' st1 st2 ->
              exists v1' v2' st1' st2' ctx' Sigma'',
                store_ty_extends Sigma' Sigma'' /\
                (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
                (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
                val_pred Sigma'' T2 v1' v2' /\
                store_result Sigma'' st1' st2'
    | TCapability _ => True
    | TCapabilityFull _ => True
    | TProof _ => True
    | TChan _ => True
    | TSecureChan _ _ => True
    | TConstantTime T' => True
    | TZeroizing T' => True
    end.
End ValRelAtN.

(** THE KEY EQUIVALENCE THEOREM *)
Theorem val_rel_at_type_fo_equiv : forall T v1 v2,
  first_order_type T = true ->
  forall Sigma sp vp sr,
    val_rel_at_type Sigma sp vp sr T v1 v2 <-> val_rel_at_type_fo T v1 v2.
Proof.
  intros T.
  induction T; intros v1 v2 Hfo Sigma sp vp sr; simpl in Hfo; try discriminate.
  - (* TUnit *)
    simpl. tauto.
  - (* TBool *)
    simpl. tauto.
  - (* TInt *)
    simpl. tauto.
  - (* TString *)
    simpl. tauto.
  - (* TBytes *)
    simpl. tauto.
  - (* TProd T1 T2 *)
    apply andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2.
      repeat split; try assumption.
      * apply (IHT1 x1 x2 Hfo1 Sigma sp vp sr). exact Hr1.
      * apply (IHT2 y1 y2 Hfo2 Sigma sp vp sr). exact Hr2.
    + intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2.
      repeat split; try assumption.
      * apply (IHT1 x1 x2 Hfo1 Sigma sp vp sr). exact Hr1.
      * apply (IHT2 y1 y2 Hfo2 Sigma sp vp sr). exact Hr2.
  - (* TSum T1 T2 *)
    apply andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2.
        repeat split; try assumption.
        apply (IHT1 x1 x2 Hfo1 Sigma sp vp sr). exact Hr.
      * right. exists y1, y2.
        repeat split; try assumption.
        apply (IHT2 y1 y2 Hfo2 Sigma sp vp sr). exact Hr.
    + intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2.
        repeat split; try assumption.
        apply (IHT1 x1 x2 Hfo1 Sigma sp vp sr). exact Hr.
      * right. exists y1, y2.
        repeat split; try assumption.
        apply (IHT2 y1 y2 Hfo2 Sigma sp vp sr). exact Hr.
  - (* TRef *)
    simpl. tauto.
  - (* TSecret *)
    simpl. tauto.
  - (* TLabeled *)
    simpl. tauto.
  - (* TTainted *)
    simpl. tauto.
  - (* TSanitized *)
    simpl. tauto.
  - (* TList *)
    simpl. tauto.
  - (* TOption *)
    simpl. tauto.
  - (* TCapability *)
    simpl. tauto.
  - (* TCapabilityFull *)
    simpl. tauto.
  - (* TProof *)
    simpl. tauto.
  - (* TConstantTime *)
    simpl. tauto.
  - (* TZeroizing *)
    simpl. tauto.
Qed.

(** Corollary: Extract FO from parameterized *)
Corollary val_rel_at_type_implies_fo : forall T Sigma sp vp sr v1 v2,
  first_order_type T = true ->
  val_rel_at_type Sigma sp vp sr T v1 v2 ->
  val_rel_at_type_fo T v1 v2.
Proof.
  intros T Sigma sp vp sr v1 v2 Hfo Hrel.
  apply (val_rel_at_type_fo_equiv T v1 v2 Hfo Sigma sp vp sr).
  exact Hrel.
Qed.

(** Corollary: Build parameterized from FO *)
Corollary fo_implies_val_rel_at_type : forall T Sigma sp vp sr v1 v2,
  first_order_type T = true ->
  val_rel_at_type_fo T v1 v2 ->
  val_rel_at_type Sigma sp vp sr T v1 v2.
Proof.
  intros T Sigma sp vp sr v1 v2 Hfo Hrel.
  apply (val_rel_at_type_fo_equiv T v1 v2 Hfo Sigma sp vp sr).
  exact Hrel.
Qed.

(** ========================================================================
    END OF FILE - ALL Qed, NO Admitted
    ======================================================================== *)
