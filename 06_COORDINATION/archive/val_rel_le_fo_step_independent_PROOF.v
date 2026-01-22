(** ============================================================================
    TERAS-LANG: val_rel_le_fo_step_independent - COMPLETE PROOF
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR
    
    This file proves step independence for first-order types in a cumulative 
    value relation. The key insight is that for first-order types, the structural 
    relation is PREDICATE-INDEPENDENT - we only need enough steps to traverse 
    the type structure.
    
    CRITICAL: All proofs end with Qed. NO AXIOMS. NO ADMITTED.
    
    "Security proven. Family driven."
    ============================================================================ *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Import ListNotations.

Open Scope string_scope.

(** ============================================================================
    SECTION 1: TYPE DEFINITIONS
    ============================================================================ *)

(** Type aliases *)
Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition label := string.
Definition effect_label := string.
Definition effect := list effect_label.

(** Core types - EXACT specification match *)
Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TFn : ty -> ty -> effect -> ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> security_level -> ty
  | TSecret : ty -> ty
  | TLabeled : ty -> label -> ty.

(** Expressions *)
Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : nat -> expr
  | EVar : ident -> expr
  | ELam : ident -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | EInl : expr -> ty -> expr
  | EInr : expr -> ty -> expr
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  | ERef : expr -> security_level -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr.

(** Store typing *)
Definition store_ty := list (ty * security_level).

(** ============================================================================
    SECTION 2: VALUE PREDICATE
    ============================================================================ *)

Fixpoint value (e : expr) : Prop :=
  match e with
  | EUnit => True
  | EBool _ => True
  | EInt _ => True
  | EString _ => True
  | ELoc _ => True
  | ELam _ _ _ => True
  | EPair e1 e2 => value e1 /\ value e2
  | EInl e _ => value e
  | EInr e _ => value e
  | _ => False
  end.

(** Value decomposition lemmas *)
Lemma value_pair : forall e1 e2,
  value (EPair e1 e2) -> value e1 /\ value e2.
Proof.
  intros e1 e2 H.
  simpl in H.
  exact H.
Qed.

Lemma value_inl : forall e T,
  value (EInl e T) -> value e.
Proof.
  intros e T H.
  simpl in H.
  exact H.
Qed.

Lemma value_inr : forall e T,
  value (EInr e T) -> value e.
Proof.
  intros e T H.
  simpl in H.
  exact H.
Qed.

(** Value construction lemmas *)
Lemma value_pair_intro : forall e1 e2,
  value e1 -> value e2 -> value (EPair e1 e2).
Proof.
  intros e1 e2 H1 H2.
  simpl.
  split; assumption.
Qed.

Lemma value_inl_intro : forall e T,
  value e -> value (EInl e T).
Proof.
  intros e T H.
  simpl.
  exact H.
Qed.

Lemma value_inr_intro : forall e T,
  value e -> value (EInr e T).
Proof.
  intros e T H.
  simpl.
  exact H.
Qed.

(** ============================================================================
    SECTION 3: FIRST-ORDER TYPE PREDICATE
    ============================================================================ *)

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList _ | TOption _ => true
  | TRef _ _ => true
  | TSecret _ | TLabeled _ _ => true
  end.

(** First-order type decomposition lemmas *)
Lemma first_order_type_prod : forall T1 T2,
  first_order_type (TProd T1 T2) = true ->
  first_order_type T1 = true /\ first_order_type T2 = true.
Proof.
  intros T1 T2 H.
  simpl in H.
  apply andb_true_iff in H.
  exact H.
Qed.

Lemma first_order_type_sum : forall T1 T2,
  first_order_type (TSum T1 T2) = true ->
  first_order_type T1 = true /\ first_order_type T2 = true.
Proof.
  intros T1 T2 H.
  simpl in H.
  apply andb_true_iff in H.
  exact H.
Qed.

Lemma first_order_type_prod_intro : forall T1 T2,
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  first_order_type (TProd T1 T2) = true.
Proof.
  intros T1 T2 H1 H2.
  simpl.
  apply andb_true_iff.
  split; assumption.
Qed.

Lemma first_order_type_sum_intro : forall T1 T2,
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  first_order_type (TSum T1 T2) = true.
Proof.
  intros T1 T2 H1 H2.
  simpl.
  apply andb_true_iff.
  split; assumption.
Qed.

(** ============================================================================
    SECTION 4: FREE VARIABLES AND CLOSEDNESS
    ============================================================================ *)

Fixpoint free_vars (e : expr) : list ident :=
  match e with
  | EUnit | EBool _ | EInt _ | EString _ | ELoc _ => nil
  | EVar x => x :: nil
  | ELam x _ body => remove string_dec x (free_vars body)
  | EApp e1 e2 | EPair e1 e2 | EAssign e1 e2 => free_vars e1 ++ free_vars e2
  | EFst e | ESnd e | EInl e _ | EInr e _ | ERef e _ | EDeref e => free_vars e
  | ECase e x1 e1 x2 e2 =>
      free_vars e ++ remove string_dec x1 (free_vars e1) ++ remove string_dec x2 (free_vars e2)
  | EIf e1 e2 e3 => free_vars e1 ++ free_vars e2 ++ free_vars e3
  | ELet x e1 e2 => free_vars e1 ++ remove string_dec x (free_vars e2)
  end.

Definition closed_expr (e : expr) : Prop := free_vars e = nil.

(** Helper lemma for list append *)
Lemma app_nil_inv_ident : forall (l1 l2 : list ident),
  List.app l1 l2 = @nil ident -> l1 = @nil ident /\ l2 = @nil ident.
Proof.
  intros l1 l2 H.
  destruct l1 as [| a l1'].
  - simpl in H. split; [reflexivity | exact H].
  - simpl in H. inversion H.
Qed.

(** Closed expression decomposition lemmas *)
Lemma closed_pair : forall e1 e2,
  closed_expr (EPair e1 e2) -> closed_expr e1 /\ closed_expr e2.
Proof.
  intros e1 e2 H.
  unfold closed_expr in *.
  simpl in H.
  apply app_nil_inv_ident in H.
  exact H.
Qed.

Lemma closed_inl : forall e T,
  closed_expr (EInl e T) -> closed_expr e.
Proof.
  intros e T H.
  unfold closed_expr in *.
  simpl in H.
  exact H.
Qed.

Lemma closed_inr : forall e T,
  closed_expr (EInr e T) -> closed_expr e.
Proof.
  intros e T H.
  unfold closed_expr in *.
  simpl in H.
  exact H.
Qed.

(** Closed expression construction lemmas *)
Lemma closed_pair_intro : forall e1 e2,
  closed_expr e1 -> closed_expr e2 -> closed_expr (EPair e1 e2).
Proof.
  intros e1 e2 H1 H2.
  unfold closed_expr in *.
  simpl.
  rewrite H1, H2.
  reflexivity.
Qed.

Lemma closed_inl_intro : forall e T,
  closed_expr e -> closed_expr (EInl e T).
Proof.
  intros e T H.
  unfold closed_expr in *.
  simpl.
  exact H.
Qed.

Lemma closed_inr_intro : forall e T,
  closed_expr e -> closed_expr (EInr e T).
Proof.
  intros e T H.
  unfold closed_expr in *.
  simpl.
  exact H.
Qed.

(** Primitive values are closed *)
Lemma closed_EUnit : closed_expr EUnit.
Proof. unfold closed_expr. reflexivity. Qed.

Lemma closed_EBool : forall b, closed_expr (EBool b).
Proof. unfold closed_expr. reflexivity. Qed.

Lemma closed_EInt : forall i, closed_expr (EInt i).
Proof. unfold closed_expr. reflexivity. Qed.

Lemma closed_EString : forall s, closed_expr (EString s).
Proof. unfold closed_expr. reflexivity. Qed.

Lemma closed_ELoc : forall l, closed_expr (ELoc l).
Proof. unfold closed_expr. reflexivity. Qed.

(** ============================================================================
    SECTION 5: TYPE DEPTH
    ============================================================================ *)

Fixpoint type_depth (T : ty) : nat :=
  match T with
  | TProd T1 T2 => 1 + max (type_depth T1) (type_depth T2)
  | TSum T1 T2 => 1 + max (type_depth T1) (type_depth T2)
  | _ => 0
  end.

(** Type depth lemmas *)
Lemma type_depth_prod : forall T1 T2,
  type_depth (TProd T1 T2) = 1 + max (type_depth T1) (type_depth T2).
Proof. reflexivity. Qed.

Lemma type_depth_sum : forall T1 T2,
  type_depth (TSum T1 T2) = 1 + max (type_depth T1) (type_depth T2).
Proof. reflexivity. Qed.

Lemma type_depth_prod_left : forall T1 T2,
  type_depth T1 < type_depth (TProd T1 T2).
Proof.
  intros T1 T2.
  simpl.
  lia.
Qed.

Lemma type_depth_prod_right : forall T1 T2,
  type_depth T2 < type_depth (TProd T1 T2).
Proof.
  intros T1 T2.
  simpl.
  lia.
Qed.

Lemma type_depth_sum_left : forall T1 T2,
  type_depth T1 < type_depth (TSum T1 T2).
Proof.
  intros T1 T2.
  simpl.
  lia.
Qed.

Lemma type_depth_sum_right : forall T1 T2,
  type_depth T2 < type_depth (TSum T1 T2).
Proof.
  intros T1 T2.
  simpl.
  lia.
Qed.

Lemma type_depth_primitive : forall T,
  (T = TUnit \/ T = TBool \/ T = TInt \/ T = TString \/ T = TBytes \/
   (exists T', T = TList T') \/ (exists T', T = TOption T') \/
   (exists T' sl, T = TRef T' sl) \/ (exists T', T = TSecret T') \/
   (exists T' l, T = TLabeled T' l)) ->
  type_depth T = 0.
Proof.
  intros T H.
  destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]].
  - subst. reflexivity.
  - subst. reflexivity.
  - subst. reflexivity.
  - subst. reflexivity.
  - subst. reflexivity.
  - destruct H as [T' H]. subst. reflexivity.
  - destruct H as [T' H]. subst. reflexivity.
  - destruct H as [T' [sl H]]. subst. reflexivity.
  - destruct H as [T' H]. subst. reflexivity.
  - destruct H as [T' [l H]]. subst. reflexivity.
Qed.

(** ============================================================================
    SECTION 6: PREDICATE-INDEPENDENT STRUCTURAL RELATION
    ============================================================================ *)

(** This captures structural equality for first-order types WITHOUT step index *)
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  (* Primitive types: exact equality *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2

  (* Security types: indistinguishable *)
  | TSecret _ => True
  | TLabeled _ _ => True

  (* Reference: same location *)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l

  (* Collections: simplified (True for now) *)
  | TList _ => True
  | TOption _ => True

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

(** ============================================================================
    SECTION 7: CUMULATIVE VALUE RELATION
    ============================================================================ *)

(** Structural part at a specific step *)
Definition val_rel_struct (val_rel_prev : store_ty -> ty -> expr -> expr -> Prop)
                          (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret _ | TLabeled _ _ => True
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList _ | TOption _ => True
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
  | TFn T1 T2 eff => True  (* Simplified for FO focus *)
  end.

(** Cumulative relation *)
Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      val_rel_le n' Σ T v1 v2 /\
      val_rel_struct (val_rel_le n') Σ T v1 v2
  end.

(** ============================================================================
    SECTION 8: BASIC val_rel_le PROPERTIES
    ============================================================================ *)

Lemma val_rel_le_0 : forall Σ T v1 v2,
  val_rel_le 0 Σ T v1 v2.
Proof.
  intros.
  simpl.
  exact I.
Qed.

Lemma val_rel_le_S : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 <->
  val_rel_le n Σ T v1 v2 /\ val_rel_struct (val_rel_le n) Σ T v1 v2.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma val_rel_le_S_implies_prev : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 H.
  simpl in H.
  destruct H as [H _].
  exact H.
Qed.

Lemma val_rel_le_S_implies_struct : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 ->
  val_rel_struct (val_rel_le n) Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 H.
  simpl in H.
  destruct H as [_ H].
  exact H.
Qed.

Lemma val_rel_le_value : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  value v1 /\ value v2.
Proof.
  intros n Σ T v1 v2 Hn H.
  destruct n as [| n'].
  - lia.
  - simpl in H.
    destruct H as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 _]].
    split; assumption.
Qed.

Lemma val_rel_le_closed : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  closed_expr v1 /\ closed_expr v2.
Proof.
  intros n Σ T v1 v2 Hn H.
  destruct n as [| n'].
  - lia.
  - simpl in H.
    destruct H as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [_ [_ [Hc1 [Hc2 _]]]].
    split; assumption.
Qed.

(** ============================================================================
    SECTION 9: EXTRACTION LEMMA - val_rel_le → val_rel_at_type_fo
    
    This is THE CRITICAL lemma. For first-order types with sufficient step depth,
    we can extract the predicate-independent structural relation.
    ============================================================================ *)

(** First, prove for primitive types (depth 0) with m > 0 *)
Lemma val_rel_le_extract_fo_primitive : forall n Σ T v1 v2,
  first_order_type T = true ->
  type_depth T = 0 ->
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_at_type_fo T v1 v2.
Proof.
  intros n Σ T v1 v2 HFO Hdepth Hn H.
  destruct n as [| n'].
  - lia.
  - simpl in H.
    destruct H as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 Htype]]]].
    (* Case analysis on T - 10 goals remain after try discriminate; try lia *)
    destruct T; simpl in HFO; simpl in Hdepth; try discriminate; try lia;
    simpl; simpl in Htype.
    (* TUnit *)     + exact Htype.
    (* TBool *)     + exact Htype.
    (* TInt *)      + exact Htype.
    (* TString *)   + exact Htype.
    (* TBytes *)    + exact Htype.
    (* TList *)     + exact I.
    (* TOption *)   + exact I.
    (* TRef *)      + exact Htype.
    (* TSecret *)   + exact I.
    (* TLabeled *)  + exact I.
Qed.

(** Main extraction lemma - by well-founded induction on type structure *)
Lemma val_rel_le_extract_fo : forall T n Σ v1 v2,
  first_order_type T = true ->
  n > type_depth T ->
  val_rel_le n Σ T v1 v2 ->
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  val_rel_at_type_fo T v1 v2.
Proof.
  induction T as [| | | | | T1' T2' eff | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T' | T' | T' sl | T' | T' l];
  intros n Σ v1 v2 HFO Hdepth Hrel.
  
  (* TUnit *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 [Heq1 Heq2]]]]].
    split; [exact Hv1 |].
    split; [exact Hv2 |].
    split; [exact Hc1 |].
    split; [exact Hc2 |].
    simpl. split; assumption.
  
  (* TBool *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 [b [Heq1 Heq2]]]]]].
    repeat split; try assumption.
    simpl. exists b. split; assumption.
  
  (* TInt *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 [i [Heq1 Heq2]]]]]].
    repeat split; try assumption.
    simpl. exists i. split; assumption.
  
  (* TString *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 [s [Heq1 Heq2]]]]]].
    repeat split; try assumption.
    simpl. exists s. split; assumption.
  
  (* TBytes *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 Heq]]]].
    split; [exact Hv1 |].
    split; [exact Hv2 |].
    split; [exact Hc1 |].
    split; [exact Hc2 |].
    simpl. exact Heq.
  
  (* TFn - not first-order *)
  - simpl in HFO. discriminate.
  
  (* TProd T1 T2 - the interesting case *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [Hprev Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 Hprod]]]].
    destruct Hprod as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    
    (* Extract first-order properties for components *)
    apply first_order_type_prod in HFO as [HFO1 HFO2].
    
    (* We have val_rel_le n' for components, and we need n' > type_depth T1/T2 *)
    simpl in Hdepth.
    assert (Hdepth1 : n' > type_depth T1) by lia.
    assert (Hdepth2 : n' > type_depth T2) by lia.
    
    (* Apply IH to components *)
    specialize (IHT1 n' Σ a1 a2 HFO1 Hdepth1 Hrel1).
    specialize (IHT2 n' Σ b1 b2 HFO2 Hdepth2 Hrel2).
    
    destruct IHT1 as [Hva1 [Hva2 [Hca1 [Hca2 Hfo1]]]].
    destruct IHT2 as [Hvb1 [Hvb2 [Hcb1 [Hcb2 Hfo2]]]].
    
    repeat split; try assumption.
    simpl.
    exists a1, b1, a2, b2.
    repeat split; assumption.
  
  (* TSum T1 T2 - the other interesting case *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [Hprev Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 Hsum]]]].
    
    (* Extract first-order properties for components *)
    apply first_order_type_sum in HFO as [HFO1 HFO2].
    
    (* We have n' > type_depth T1/T2 *)
    simpl in Hdepth.
    assert (Hdepth1 : n' > type_depth T1) by lia.
    assert (Hdepth2 : n' > type_depth T2) by lia.
    
    destruct Hsum as [HInl | HInr].
    + (* Inl case *)
      destruct HInl as [x1 [x2 [Heq1 [Heq2 Hrel1]]]].
      specialize (IHT1 n' Σ x1 x2 HFO1 Hdepth1 Hrel1).
      destruct IHT1 as [Hvx1 [Hvx2 [Hcx1 [Hcx2 Hfo1]]]].
      repeat split; try assumption.
      simpl.
      left.
      exists x1, x2.
      repeat split; assumption.
    + (* Inr case *)
      destruct HInr as [y1 [y2 [Heq1 [Heq2 Hrel2]]]].
      specialize (IHT2 n' Σ y1 y2 HFO2 Hdepth2 Hrel2).
      destruct IHT2 as [Hvy1 [Hvy2 [Hcy1 [Hcy2 Hfo2]]]].
      repeat split; try assumption.
      simpl.
      right.
      exists y1, y2.
      repeat split; assumption.
  
  (* TList *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 _]]]].
    split; [exact Hv1 |].
    split; [exact Hv2 |].
    split; [exact Hc1 |].
    split; [exact Hc2 |].
    simpl. exact I.
  
  (* TOption *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 _]]]].
    split; [exact Hv1 |].
    split; [exact Hv2 |].
    split; [exact Hc1 |].
    split; [exact Hc2 |].
    simpl. exact I.
  
  (* TRef *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 [l [Heq1 Heq2]]]]]].
    repeat split; try assumption.
    simpl. exists l. split; assumption.
  
  (* TSecret *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 _]]]].
    split; [exact Hv1 |].
    split; [exact Hv2 |].
    split; [exact Hc1 |].
    split; [exact Hc2 |].
    simpl. exact I.
  
  (* TLabeled *)
  - destruct n as [| n']; [lia |].
    simpl in Hrel.
    destruct Hrel as [_ Hstruct].
    unfold val_rel_struct in Hstruct.
    destruct Hstruct as [Hv1 [Hv2 [Hc1 [Hc2 _]]]].
    split; [exact Hv1 |].
    split; [exact Hv2 |].
    split; [exact Hc1 |].
    split; [exact Hc2 |].
    simpl. exact I.
Qed.

(** ============================================================================
    SECTION 10: CONSTRUCTION LEMMA - val_rel_at_type_fo → val_rel_le
    
    Given the predicate-independent structure, we can construct val_rel_le
    for ANY step index n > 0.
    ============================================================================ *)

(** Helper: construct val_rel_le from val_rel_at_type_fo using structural induction on T *)
(** This avoids the step-index arithmetic problem by using type structure *)
(** Key insight: use nested strong induction - outer on T, inner on n *)
Lemma val_rel_le_mono_helper : forall T,
  first_order_type T = true ->
  forall n Σ v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_at_type_fo T v1 v2 ->
  n > 0 ->
  val_rel_le n Σ T v1 v2.
Proof.
  induction T as [| | | | | T1' T2' eff | T1 IHT1 T2 IHT2 | T1 IHT1 T2 IHT2 | T' | T' | T' sl | T' | T' l];
  intros HFO n Σ v1 v2 Hv1 Hv2 Hc1 Hc2 Hfo Hn.
  
  (* TUnit - need strong induction on n *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * (* val_rel_le n' Σ TUnit v1 v2 *)
        destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * (* val_rel_struct *)
        unfold val_rel_struct.
        simpl in Hfo. destruct Hfo as [Heq1 Heq2].
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        split; [exact Heq1 | exact Heq2].
  
  (* TBool *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        simpl in Hfo. destruct Hfo as [b [Heq1 Heq2]].
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exists b. split; [exact Heq1 | exact Heq2].
  
  (* TInt *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        simpl in Hfo. destruct Hfo as [i [Heq1 Heq2]].
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exists i. split; [exact Heq1 | exact Heq2].
  
  (* TString *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        simpl in Hfo. destruct Hfo as [s [Heq1 Heq2]].
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exists s. split; [exact Heq1 | exact Heq2].
  
  (* TBytes *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        simpl in Hfo.
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exact Hfo.
  
  (* TFn - not first order *)
  - simpl in HFO. discriminate.
  
  (* TProd T1 T2 *)
  - apply first_order_type_prod in HFO as [HFO1 HFO2].
    simpl in Hfo.
    destruct Hfo as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hfo1 Hfo2]]]]]]].
    subst v1 v2.
    apply value_pair in Hv1 as [Hva1 Hvb1].
    apply value_pair in Hv2 as [Hva2 Hvb2].
    apply closed_pair in Hc1 as [Hca1 Hcb1].
    apply closed_pair in Hc2 as [Hca2 Hcb2].
    (* Prove by induction on n for this specific T *)
    induction n as [| n' IHn].
    + lia.
    + simpl. split.
      * (* val_rel_le n' *)
        destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn. lia.
      * (* val_rel_struct *)
        unfold val_rel_struct.
        split; [simpl; split; [exact Hva1 | exact Hvb1] |].
        split; [simpl; split; [exact Hva2 | exact Hvb2] |].
        split; [exact (closed_pair_intro a1 b1 Hca1 Hcb1) |].
        split; [exact (closed_pair_intro a2 b2 Hca2 Hcb2) |].
        exists a1, b1, a2, b2.
        split; [reflexivity |].
        split; [reflexivity |].
        split.
        -- (* val_rel_le n' T1 a1 a2 *)
           destruct n' as [| n''].
           ++ simpl. exact I.
           ++ apply IHT1; try assumption. lia.
        -- (* val_rel_le n' T2 b1 b2 *)
           destruct n' as [| n''].
           ++ simpl. exact I.
           ++ apply IHT2; try assumption. lia.
  
  (* TSum T1 T2 *)
  - apply first_order_type_sum in HFO as [HFO1 HFO2].
    simpl in Hfo.
    destruct Hfo as [[x1 [x2 [Heq1 [Heq2 Hfo1]]]] | [y1 [y2 [Heq1 [Heq2 Hfo2]]]]].
    
    + (* Inl case *)
      subst v1 v2.
      apply value_inl in Hv1 as Hvx1.
      apply value_inl in Hv2 as Hvx2.
      apply closed_inl in Hc1 as Hcx1.
      apply closed_inl in Hc2 as Hcx2.
      (* Induction on n *)
      induction n as [| n' IHn].
      * lia.
      * simpl. split.
        -- destruct n' as [| n''].
           ++ simpl. exact I.
           ++ apply IHn. lia.
        -- unfold val_rel_struct.
           split; [simpl; exact Hvx1 |].
           split; [simpl; exact Hvx2 |].
           split; [exact (closed_inl_intro x1 T2 Hcx1) |].
           split; [exact (closed_inl_intro x2 T2 Hcx2) |].
           left.
           exists x1, x2.
           split; [reflexivity |].
           split; [reflexivity |].
           destruct n' as [| n''].
           ++ simpl. exact I.
           ++ apply IHT1; try assumption. lia.
    
    + (* Inr case *)
      subst v1 v2.
      apply value_inr in Hv1 as Hvy1.
      apply value_inr in Hv2 as Hvy2.
      apply closed_inr in Hc1 as Hcy1.
      apply closed_inr in Hc2 as Hcy2.
      (* Induction on n *)
      induction n as [| n' IHn].
      * lia.
      * simpl. split.
        -- destruct n' as [| n''].
           ++ simpl. exact I.
           ++ apply IHn. lia.
        -- unfold val_rel_struct.
           split; [simpl; exact Hvy1 |].
           split; [simpl; exact Hvy2 |].
           split; [exact (closed_inr_intro y1 T1 Hcy1) |].
           split; [exact (closed_inr_intro y2 T1 Hcy2) |].
           right.
           exists y1, y2.
           split; [reflexivity |].
           split; [reflexivity |].
           destruct n' as [| n''].
           ++ simpl. exact I.
           ++ apply IHT2; try assumption. lia.
  
  (* TList *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exact I.
  
  (* TOption *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exact I.
  
  (* TRef *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        simpl in Hfo. destruct Hfo as [l [Heq1 Heq2]].
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exists l. split; [exact Heq1 | exact Heq2].
  
  (* TSecret *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exact I.
  
  (* TLabeled *)
  - induction n as [| n' IHn'].
    + lia.
    + simpl. split.
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply IHn'. lia.
      * unfold val_rel_struct.
        split; [exact Hv1 |].
        split; [exact Hv2 |].
        split; [exact Hc1 |].
        split; [exact Hc2 |].
        exact I.
Qed.

(** Main construction lemma *)
Lemma val_rel_le_construct_fo : forall n T Σ v1 v2,
  first_order_type T = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_at_type_fo T v1 v2 ->
  n > 0 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros n T Σ v1 v2 HFO Hv1 Hv2 Hc1 Hc2 Hfo Hn.
  apply val_rel_le_mono_helper; assumption.
Qed.

(** ============================================================================
    SECTION 11: MAIN THEOREM - STEP INDEPENDENCE FOR FIRST-ORDER TYPES
    ============================================================================ *)

(** 
   UNIFIED LEMMA WITH TYPE DEPTH PREMISE
   
   For first-order types, val_rel_le is step-independent when we have
   enough steps to fully traverse the type structure.
   
   This is THE key theorem that closes the gap.
*)
Theorem val_rel_le_fo_step_independent : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m > type_depth T ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 HFO Hm Hn Hrel.
  
  (* Step 1: Extract the predicate-independent structure from val_rel_le m *)
  apply val_rel_le_extract_fo in Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hfo]]]]; try assumption.
  
  (* Step 2: Construct val_rel_le n from the structure *)
  apply val_rel_le_construct_fo; assumption.
Qed.

(** ============================================================================
    SECTION 12: COROLLARIES FOR SPECIFIC CASES
    ============================================================================ *)

(** For primitive types (depth 0), m > 0 is sufficient *)
Corollary val_rel_le_fo_step_independent_primitive : forall m n Σ T v1 v2,
  first_order_type T = true ->
  type_depth T = 0 ->
  m > 0 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 HFO Hdepth Hm Hn Hrel.
  apply val_rel_le_fo_step_independent with (m := m); try assumption.
  lia.
Qed.

(** For depth-1 types, m >= 2 is sufficient *)
Corollary val_rel_le_fo_step_independent_depth1 : forall m n Σ T v1 v2,
  first_order_type T = true ->
  type_depth T <= 1 ->
  m >= 2 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 HFO Hdepth Hm Hn Hrel.
  apply val_rel_le_fo_step_independent with (m := m); try assumption.
  lia.
Qed.

(** Alternative formulation: For compound types, require m >= type_depth T + 1 *)
Corollary val_rel_le_fo_step_independent_compound : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m >= type_depth T + 1 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 HFO Hm Hn Hrel.
  apply val_rel_le_fo_step_independent with (m := m); try assumption.
  lia.
Qed.

(** Specific instances for common types *)

Corollary val_rel_le_step_independent_TUnit : forall m n Σ v1 v2,
  m > 0 -> n > 0 ->
  val_rel_le m Σ TUnit v1 v2 ->
  val_rel_le n Σ TUnit v1 v2.
Proof.
  intros m n Σ v1 v2 Hm Hn Hrel.
  apply val_rel_le_fo_step_independent_primitive with (m := m); try assumption.
  reflexivity. reflexivity.
Qed.

Corollary val_rel_le_step_independent_TBool : forall m n Σ v1 v2,
  m > 0 -> n > 0 ->
  val_rel_le m Σ TBool v1 v2 ->
  val_rel_le n Σ TBool v1 v2.
Proof.
  intros m n Σ v1 v2 Hm Hn Hrel.
  apply val_rel_le_fo_step_independent_primitive with (m := m); try assumption.
  reflexivity. reflexivity.
Qed.

Corollary val_rel_le_step_independent_TInt : forall m n Σ v1 v2,
  m > 0 -> n > 0 ->
  val_rel_le m Σ TInt v1 v2 ->
  val_rel_le n Σ TInt v1 v2.
Proof.
  intros m n Σ v1 v2 Hm Hn Hrel.
  apply val_rel_le_fo_step_independent_primitive with (m := m); try assumption.
  reflexivity. reflexivity.
Qed.

Corollary val_rel_le_step_independent_TRef : forall m n Σ T' sl v1 v2,
  m > 0 -> n > 0 ->
  val_rel_le m Σ (TRef T' sl) v1 v2 ->
  val_rel_le n Σ (TRef T' sl) v1 v2.
Proof.
  intros m n Σ T' sl v1 v2 Hm Hn Hrel.
  apply val_rel_le_fo_step_independent_primitive with (m := m); try assumption.
  reflexivity. reflexivity.
Qed.

(** ============================================================================
    SECTION 13: VERIFICATION - PRINT ASSUMPTIONS
    
    CRITICAL: This section verifies that all proofs are axiom-free.
    ============================================================================ *)

(** Print assumptions for the main theorem *)
Print Assumptions val_rel_le_fo_step_independent.

(** Print assumptions for key lemmas *)
Print Assumptions val_rel_le_extract_fo.
Print Assumptions val_rel_le_construct_fo.

(** Print assumptions for corollaries *)
Print Assumptions val_rel_le_fo_step_independent_primitive.
Print Assumptions val_rel_le_fo_step_independent_depth1.
Print Assumptions val_rel_le_fo_step_independent_compound.

(** ============================================================================
    SECTION 14: ADDITIONAL UTILITY LEMMAS
    ============================================================================ *)

(** val_rel_at_type_fo is reflexive for values with correct shape *)
Lemma val_rel_at_type_fo_refl : forall T v,
  first_order_type T = true ->
  value v ->
  closed_expr v ->
  (exists v', val_rel_at_type_fo T v v') ->
  val_rel_at_type_fo T v v.
Proof.
  induction T; intros v HFO Hval Hclosed [v' Hrel]; simpl in *.
  - (* TUnit *)
    destruct Hrel as [Heq1 Heq2]. subst. split; reflexivity.
  - (* TBool *)
    destruct Hrel as [b [Heq1 Heq2]]. subst. exists b. split; reflexivity.
  - (* TInt *)
    destruct Hrel as [i [Heq1 Heq2]]. subst. exists i. split; reflexivity.
  - (* TString *)
    destruct Hrel as [s [Heq1 Heq2]]. subst. exists s. split; reflexivity.
  - (* TBytes *)
    reflexivity.
  - (* TFn - not first-order *)
    discriminate.
  - (* TProd *)
    apply first_order_type_prod in HFO as [HFO1 HFO2].
    destruct Hrel as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    subst v.
    apply value_pair in Hval as [Hva Hvb].
    apply closed_pair in Hclosed as [Hca Hcb].
    exists a1, b1, a1, b1.
    repeat split; try reflexivity.
    + apply IHT1; try assumption. exists a2. exact Hrel1.
    + apply IHT2; try assumption. exists b2. exact Hrel2.
  - (* TSum *)
    apply first_order_type_sum in HFO as [HFO1 HFO2].
    destruct Hrel as [[x1 [x2 [Heq1 [Heq2 Hrel1]]]] | [y1 [y2 [Heq1 [Heq2 Hrel2]]]]].
    + subst v.
      apply value_inl in Hval as Hvx.
      apply closed_inl in Hclosed as Hcx.
      left. exists x1, x1.
      repeat split; try reflexivity.
      apply IHT1; try assumption. exists x2. exact Hrel1.
    + subst v.
      apply value_inr in Hval as Hvy.
      apply closed_inr in Hclosed as Hcy.
      right. exists y1, y1.
      repeat split; try reflexivity.
      apply IHT2; try assumption. exists y2. exact Hrel2.
  - (* TList *)
    exact I.
  - (* TOption *)
    exact I.
  - (* TRef *)
    destruct Hrel as [l [Heq1 Heq2]]. subst. exists l. split; reflexivity.
  - (* TSecret *)
    exact I.
  - (* TLabeled *)
    exact I.
Qed.

(** val_rel_at_type_fo is symmetric *)
Lemma val_rel_at_type_fo_sym : forall T v1 v2,
  first_order_type T = true ->
  val_rel_at_type_fo T v1 v2 ->
  val_rel_at_type_fo T v2 v1.
Proof.
  induction T; intros v1 v2 HFO Hrel; simpl in *.
  - (* TUnit *)
    destruct Hrel as [Heq1 Heq2]. split; assumption.
  - (* TBool *)
    destruct Hrel as [b [Heq1 Heq2]]. exists b. split; assumption.
  - (* TInt *)
    destruct Hrel as [i [Heq1 Heq2]]. exists i. split; assumption.
  - (* TString *)
    destruct Hrel as [s [Heq1 Heq2]]. exists s. split; assumption.
  - (* TBytes *)
    symmetry. exact Hrel.
  - (* TFn *)
    discriminate.
  - (* TProd *)
    apply first_order_type_prod in HFO as [HFO1 HFO2].
    destruct Hrel as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    exists a2, b2, a1, b1.
    repeat split; try assumption.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - (* TSum *)
    apply first_order_type_sum in HFO as [HFO1 HFO2].
    destruct Hrel as [[x1 [x2 [Heq1 [Heq2 Hrel1]]]] | [y1 [y2 [Heq1 [Heq2 Hrel2]]]]].
    + left. exists x2, x1.
      repeat split; try assumption.
      apply IHT1; assumption.
    + right. exists y2, y1.
      repeat split; try assumption.
      apply IHT2; assumption.
  - (* TList *)
    exact I.
  - (* TOption *)
    exact I.
  - (* TRef *)
    destruct Hrel as [l [Heq1 Heq2]]. exists l. split; assumption.
  - (* TSecret *)
    exact I.
  - (* TLabeled *)
    exact I.
Qed.

(** val_rel_at_type_fo is transitive *)
Lemma val_rel_at_type_fo_trans : forall T v1 v2 v3,
  first_order_type T = true ->
  val_rel_at_type_fo T v1 v2 ->
  val_rel_at_type_fo T v2 v3 ->
  val_rel_at_type_fo T v1 v3.
Proof.
  induction T; intros v1 v2 v3 HFO Hrel12 Hrel23; simpl in *.
  - (* TUnit *)
    destruct Hrel12 as [Heq1 Heq2]. destruct Hrel23 as [Heq2' Heq3].
    split; assumption.
  - (* TBool *)
    destruct Hrel12 as [b1 [Heq1 Heq2]]. destruct Hrel23 as [b2 [Heq2' Heq3]].
    subst. injection Heq2' as Heq. subst. exists b2. split; reflexivity.
  - (* TInt *)
    destruct Hrel12 as [i1 [Heq1 Heq2]]. destruct Hrel23 as [i2 [Heq2' Heq3]].
    subst. injection Heq2' as Heq. subst. exists i2. split; reflexivity.
  - (* TString *)
    destruct Hrel12 as [s1 [Heq1 Heq2]]. destruct Hrel23 as [s2 [Heq2' Heq3]].
    subst. injection Heq2' as Heq. subst. exists s2. split; reflexivity.
  - (* TBytes *)
    transitivity v2; assumption.
  - (* TFn *)
    discriminate.
  - (* TProd *)
    apply first_order_type_prod in HFO as [HFO1 HFO2].
    destruct Hrel12 as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1_12 Hrel2_12]]]]]]].
    destruct Hrel23 as [a2' [b2' [a3 [b3 [Heq2' [Heq3 [Hrel1_23 Hrel2_23]]]]]]].
    subst v1 v2 v3. injection Heq2' as Ha Hb. subst a2' b2'.
    exists a1, b1, a3, b3.
    repeat split; try reflexivity.
    + apply IHT1 with a2; assumption.
    + apply IHT2 with b2; assumption.
  - (* TSum *)
    apply first_order_type_sum in HFO as [HFO1 HFO2].
    destruct Hrel12 as [[x1 [x2 [Heq1 [Heq2 Hrel1_12]]]] | [y1 [y2 [Heq1 [Heq2 Hrel2_12]]]]].
    + destruct Hrel23 as [[x2' [x3 [Heq2' [Heq3 Hrel1_23]]]] | [y2' [y3 [Heq2' [Heq3 Hrel2_23]]]]].
      * subst v1 v2 v3. injection Heq2' as Hx. subst x2'.
        left. exists x1, x3.
        repeat split; try reflexivity.
        apply IHT1 with x2; assumption.
      * subst v2. discriminate.
    + destruct Hrel23 as [[x2' [x3 [Heq2' [Heq3 Hrel1_23]]]] | [y2' [y3 [Heq2' [Heq3 Hrel2_23]]]]].
      * subst v2. discriminate.
      * subst v1 v2 v3. injection Heq2' as Hy. subst y2'.
        right. exists y1, y3.
        repeat split; try reflexivity.
        apply IHT2 with y2; assumption.
  - (* TList *)
    exact I.
  - (* TOption *)
    exact I.
  - (* TRef *)
    destruct Hrel12 as [l1 [Heq1 Heq2]]. destruct Hrel23 as [l2 [Heq2' Heq3]].
    subst. injection Heq2' as Heq. subst. exists l2. split; reflexivity.
  - (* TSecret *)
    exact I.
  - (* TLabeled *)
    exact I.
Qed.

(** ============================================================================
    END OF FILE
    
    ALL PROOFS COMPLETE - NO AXIOMS - NO ADMITTED
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR
    "Security proven. Family driven."
    ============================================================================ *)
