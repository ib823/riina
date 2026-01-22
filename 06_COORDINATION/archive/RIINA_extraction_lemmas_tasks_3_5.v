(** * RIINA Extraction Lemmas — Tasks 3-5
    
    Proven extraction lemmas for val_rel_n_base.
    These lemmas extract structural information from related values.
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
    Generated: 2026-01-19
    Status: ALL COMPLETE - Qed
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import ZArith.

Import ListNotations.

Open Scope Z_scope.

(* === Type Definitions === *)

Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition label := string.
Definition effect_label := string.
Definition effect := list effect_label.

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

Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc : forall l, value (ELoc l)
  | VLam : forall x T body, value (ELam x T body)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T).

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef T _ => first_order_type T
  | TList T => first_order_type T
  | TOption T => first_order_type T
  | TSecret T => first_order_type T
  | TLabeled T _ => first_order_type T
  end.

Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EVar y => x = y
  | ELam y T body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  | EPair e1 e2 => free_in x e1 \/ free_in x e2
  | EFst e => free_in x e
  | ESnd e => free_in x e
  | EInl e _ => free_in x e
  | EInr e _ => free_in x e
  | ECase e y1 e1 y2 e2 =>
      free_in x e \/ (x <> y1 /\ free_in x e1) \/ (x <> y2 /\ free_in x e2)
  | EIf e1 e2 e3 => free_in x e1 \/ free_in x e2 \/ free_in x e3
  | ELet y e1 e2 => free_in x e1 \/ (x <> y /\ free_in x e2)
  | _ => False
  end.

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

Definition store_ty := list (loc * ty * security_level).

Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret _ => True
  | TLabeled _ _ => True
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList _ => True
  | TOption _ => True
  | TProd T1 T2 =>
      exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)
  | TFn _ _ _ => True
  end.

Definition val_rel_n_base (Sigma : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).

(* ========================================================================
   TASK 3: val_rel_n_base_int
   ======================================================================== *)

(** Extract SAME integer from val_rel_n_base TInt *)
Lemma val_rel_n_base_int : forall Sigma v1 v2,
  val_rel_n_base Sigma TInt v1 v2 ->
  exists i, v1 = EInt i /\ v2 = EInt i.
Proof.
  intros Sigma v1 v2 H.
  (* Step 1: Unfold val_rel_n_base *)
  unfold val_rel_n_base in H.
  (* Step 2: Extract the conjuncts *)
  destruct H as [Hv1 [Hv2 [Hc1 [Hc2 Hfo]]]].
  (* Step 3: first_order_type TInt = true, so Hfo is val_rel_at_type_fo TInt v1 v2 *)
  (* Step 4: Simplify - val_rel_at_type_fo TInt v1 v2 = exists i, v1 = EInt i /\ v2 = EInt i *)
  simpl in Hfo.
  (* Step 5: Goal follows directly *)
  exact Hfo.
Qed.

(* ========================================================================
   TASK 4: val_rel_n_base_unit
   ======================================================================== *)

(** Extract that related TUnit values are both EUnit *)
Lemma val_rel_n_base_unit : forall Sigma v1 v2,
  val_rel_n_base Sigma TUnit v1 v2 ->
  v1 = EUnit /\ v2 = EUnit.
Proof.
  intros Sigma v1 v2 H.
  (* Step 1: Unfold val_rel_n_base *)
  unfold val_rel_n_base in H.
  (* Step 2: Extract the conjuncts *)
  destruct H as [Hv1 [Hv2 [Hc1 [Hc2 Hfo]]]].
  (* Step 3: first_order_type TUnit = true, so Hfo is val_rel_at_type_fo TUnit v1 v2 *)
  (* Step 4: Simplify - val_rel_at_type_fo TUnit v1 v2 = v1 = EUnit /\ v2 = EUnit *)
  simpl in Hfo.
  (* Step 5: Goal follows directly *)
  exact Hfo.
Qed.

(* ========================================================================
   TASK 5: val_rel_n_base_ref
   ======================================================================== *)

(** Extract SAME location from val_rel_n_base (TRef T sl) *)
Lemma val_rel_n_base_ref : forall Sigma T sl v1 v2,
  first_order_type (TRef T sl) = true ->
  val_rel_n_base Sigma (TRef T sl) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l.
Proof.
  intros Sigma T sl v1 v2 Hfo_premise Hrel.
  (* Step 1: Unfold val_rel_n_base *)
  unfold val_rel_n_base in Hrel.
  (* Step 2: Extract the conjuncts *)
  destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hfo]]]].
  (* Step 3: Rewrite using first_order_type premise *)
  rewrite Hfo_premise in Hfo.
  (* Step 4: Simplify - val_rel_at_type_fo (TRef T sl) v1 v2 = exists l, v1 = ELoc l /\ v2 = ELoc l *)
  simpl in Hfo.
  (* Step 5: Goal follows directly *)
  exact Hfo.
Qed.

(* ========================================================================
   VERIFICATION: Print assumptions to confirm no axioms
   ======================================================================== *)

Print Assumptions val_rel_n_base_int.
Print Assumptions val_rel_n_base_unit.
Print Assumptions val_rel_n_base_ref.

(** Expected output for all three:
    Closed under the global context
    
    This confirms ZERO AXIOMS used - pure constructive proofs.
*)

(* ========================================================================
   BONUS: Additional extraction lemmas for completeness
   ======================================================================== *)

(** val_rel_n_base_bool - already proven in template, included for completeness *)
Lemma val_rel_n_base_bool : forall Sigma v1 v2,
  val_rel_n_base Sigma TBool v1 v2 ->
  exists b, v1 = EBool b /\ v2 = EBool b.
Proof.
  intros Sigma v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [_ [_ [_ [_ Hfo]]]].
  simpl in Hfo.
  exact Hfo.
Qed.

(** val_rel_n_base_string *)
Lemma val_rel_n_base_string : forall Sigma v1 v2,
  val_rel_n_base Sigma TString v1 v2 ->
  exists s, v1 = EString s /\ v2 = EString s.
Proof.
  intros Sigma v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [_ [_ [_ [_ Hfo]]]].
  simpl in Hfo.
  exact Hfo.
Qed.

(** val_rel_n_base_value - extract value properties *)
Lemma val_rel_n_base_value : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 ->
  value v1 /\ value v2.
Proof.
  intros Sigma T v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [Hv1 [Hv2 _]].
  split; assumption.
Qed.

(** val_rel_n_base_closed - extract closed properties *)
Lemma val_rel_n_base_closed : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 ->
  closed_expr v1 /\ closed_expr v2.
Proof.
  intros Sigma T v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [_ [_ [Hc1 [Hc2 _]]]].
  split; assumption.
Qed.

(** val_rel_n_base_prod_fo - extract pair structure *)
Lemma val_rel_n_base_prod_fo : forall Sigma T1 T2 v1 v2,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Sigma (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2.
Proof.
  intros Sigma T1 T2 v1 v2 Hfo Hrel.
  unfold val_rel_n_base in Hrel.
  destruct Hrel as [_ [_ [_ [_ Htype]]]].
  rewrite Hfo in Htype.
  simpl in Htype.
  exact Htype.
Qed.

(** val_rel_n_base_sum_fo - extract sum structure *)
Lemma val_rel_n_base_sum_fo : forall Sigma T1 T2 v1 v2,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v1 v2 ->
  (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type_fo T1 x1 x2) \/
  (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type_fo T2 y1 y2).
Proof.
  intros Sigma T1 T2 v1 v2 Hfo Hrel.
  unfold val_rel_n_base in Hrel.
  destruct Hrel as [_ [_ [_ [_ Htype]]]].
  rewrite Hfo in Htype.
  simpl in Htype.
  exact Htype.
Qed.

Print Assumptions val_rel_n_base_bool.
Print Assumptions val_rel_n_base_string.
Print Assumptions val_rel_n_base_value.
Print Assumptions val_rel_n_base_closed.
Print Assumptions val_rel_n_base_prod_fo.
Print Assumptions val_rel_n_base_sum_fo.

(** End of RIINA_extraction_lemmas_tasks_3_5.v *)
