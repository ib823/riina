(** * First-Order Type Predicate Independence
    
    This file proves that for first-order types, val_rel_at_type
    is independent of the predicate parameters.
    
    This means: val_rel_at_type Σ sp vl sl T v1 v2 = val_rel_at_type_fo T v1 v2
    when first_order_type T = true.
    
    This is the KEY lemma that enables the foundational rewrite.
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** Closed expressions - no free variables *)
Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(** First-order type check *)
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
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

(** First-order value relation - predicate independent *)
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

(** val_rel_at_type with arbitrary predicates *)
Section ValRelAtType.
  Variable Σ : store_ty.
  Variable sp : store_ty -> store -> store -> Prop.
  Variable vl : store_ty -> ty -> expr -> expr -> Prop.
  Variable sl : store_ty -> store -> store -> Prop.

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
        forall Σ', store_ty_extends Σ Σ' ->
          forall x y,
            value x -> value y -> closed_expr x -> closed_expr y ->
            vl Σ' T1 x y ->
            forall st1 st2 ctx,
              sp Σ' st1 st2 ->
              exists v1' v2' st1' st2' ctx' Σ'',
                store_ty_extends Σ' Σ'' /\
                (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
                (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
                vl Σ'' T2 v1' v2' /\
                sl Σ'' st1' st2'
    | TCapability _ => True
    | TCapabilityFull _ => True
    | TProof _ => True
    | TChan _ => True
    | TSecureChan _ _ => True
    | TConstantTime T' => True
    | TZeroizing T' => True
    end.
End ValRelAtType.

(** THE KEY THEOREM: For first-order types, val_rel_at_type = val_rel_at_type_fo *)
Theorem val_rel_at_type_fo_equiv : forall T Σ sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 <-> val_rel_at_type_fo T v1 v2.
Proof.
  intros T. 
  induction T; intros Σ' sp vl sl v1 v2 Hfo; simpl in Hfo; try discriminate.
  
  - (* TUnit *)
    simpl. split; auto.
  
  - (* TBool *)
    simpl. split; auto.
  
  - (* TInt *)
    simpl. split; auto.
  
  - (* TString *)
    simpl. split; auto.
  
  - (* TBytes *)
    simpl. split; auto.
  
  - (* TProd T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + (* -> *)
      intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2.
      repeat split; try assumption.
      * apply IHT1; assumption.
      * apply IHT2; assumption.
    + (* <- *)
      intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2.
      repeat split; try assumption.
      * apply IHT1; assumption.
      * apply IHT2; assumption.
  
  - (* TSum T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption. apply IHT1; assumption.
      * right. exists y1, y2. repeat split; try assumption. apply IHT2; assumption.
    + intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption. apply IHT1; assumption.
      * right. exists y1, y2. repeat split; try assumption. apply IHT2; assumption.
  
  - (* TRef T' sl *)
    simpl. split; auto.
  
  - (* TSecret T' *)
    simpl. split; auto.
  
  - (* TLabeled T' sl *)
    simpl. split; auto.
  
  - (* TTainted T' tl *)
    simpl. split; auto.
  
  - (* TSanitized T' tl *)
    simpl. split; auto.
  
  - (* TList T' *)
    simpl. split; auto.
  
  - (* TOption T' *)
    simpl. split; auto.
  
  - (* TCapability c *)
    simpl. split; auto.
  
  - (* TCapabilityFull c *)
    simpl. split; auto.
  
  - (* TProof T' *)
    simpl. split; auto.
  
  - (* TConstantTime T' *)
    simpl. split; auto.
  
  - (* TZeroizing T' *)
    simpl. split; auto.
Qed.

(** COROLLARY: We can extract val_rel_at_type_fo from val_rel_at_type for FO types *)
Corollary val_rel_at_type_implies_fo : forall T Σ sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  val_rel_at_type_fo T v1 v2.
Proof.
  intros. apply val_rel_at_type_fo_equiv in H0; assumption.
Qed.

(** COROLLARY: We can build val_rel_at_type from val_rel_at_type_fo for FO types *)
Corollary fo_implies_val_rel_at_type : forall T Σ sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type_fo T v1 v2 ->
  val_rel_at_type Σ sp vl sl T v1 v2.
Proof.
  intros. apply val_rel_at_type_fo_equiv; assumption.
Qed.

(** THEOREM: First-order val_rel_at_type is completely store/predicate independent *)
Theorem val_rel_at_type_fo_indep : forall T Σ1 Σ2 sp1 sp2 vl1 vl2 sl1 sl2 v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ1 sp1 vl1 sl1 T v1 v2 <->
  val_rel_at_type Σ2 sp2 vl2 sl2 T v1 v2.
Proof.
  intros.
  split; intros.
  - apply fo_implies_val_rel_at_type; try assumption.
    apply val_rel_at_type_implies_fo with (Σ := Σ1) (sp := sp1) (vl := vl1) (sl := sl1); assumption.
  - apply fo_implies_val_rel_at_type; try assumption.
    apply val_rel_at_type_implies_fo with (Σ := Σ2) (sp := sp2) (vl := vl2) (sl := sl2); assumption.
Qed.

(** End of ValRelFOEquiv.v *)
