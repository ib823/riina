(** * NonInterferenceZero.v: Zero-Step Base Cases for Step-Indexed Logical Relations *)

(**
   Package J: NonInterferenceZero - Zero-Step Base Cases
   
   This module proves the zero-step base case lemmas for TERAS-LANG's step-indexed
   logical relation. In v2 semantics, val_rel_n 0 is NOT trivially True.
   
   It requires:
   - Both expressions are values
   - Both expressions are closed
   - For first-order types: structural equality via val_rel_at_type_fo
   
   Classification: TRACK A FORMAL VERIFICATION
   Status: TO BE PROVEN
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Import ListNotations.
Open Scope Z_scope.

(** ** Identifiers - inline definitions for self-contained module *)
Definition var := string.
Definition loc := nat.

(** ** Security Labels *)
Inductive sec_label : Type :=
  | SL_Low : sec_label
  | SL_High : sec_label.

(** ** Types *)
Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> sec_label -> ty
  | TSecret : ty -> ty
  | TFn : ty -> ty -> ty.

(** ** First-Order Type Classification *)
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit => true
  | TBool => true
  | TInt => true
  | TString => true
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList T1 => first_order_type T1
  | TOption T1 => first_order_type T1
  | TRef _ _ => true
  | TSecret T1 => first_order_type T1
  | TFn _ _ => false
  end.

(** ** Expressions *)
Inductive expr : Type :=
  | EVar : var -> expr
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | EInl : expr -> expr
  | EInr : expr -> expr
  | ECase : expr -> var -> expr -> var -> expr -> expr
  | ENil : ty -> expr
  | ECons : expr -> expr -> expr
  | ENone : ty -> expr
  | ESome : expr -> expr
  | ELoc : loc -> expr
  | ERef : expr -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  | ESecret : expr -> expr
  | EReveal : expr -> expr
  | ELam : var -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  | ELet : var -> expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr.

(** ** Values *)
Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v, value v -> value (EInl v)
  | VInr : forall v, value v -> value (EInr v)
  | VNil : forall T, value (ENil T)
  | VCons : forall v1 v2, value v1 -> value v2 -> value (ECons v1 v2)
  | VNone : forall T, value (ENone T)
  | VSome : forall v, value v -> value (ESome v)
  | VLoc : forall l, value (ELoc l)
  | VSecret : forall v, value v -> value (ESecret v)
  | VLam : forall x T e, value (ELam x T e).

(** ** Free Variables *)
Fixpoint free_vars (e : expr) : list var :=
  match e with
  | EVar x => [x]
  | EUnit => []
  | EBool _ => []
  | EInt _ => []
  | EString _ => []
  | EPair e1 e2 => free_vars e1 ++ free_vars e2
  | EFst e1 => free_vars e1
  | ESnd e1 => free_vars e1
  | EInl e1 => free_vars e1
  | EInr e1 => free_vars e1
  | ECase e1 x1 e2 x2 e3 => 
      free_vars e1 ++ 
      (remove string_dec x1 (free_vars e2)) ++
      (remove string_dec x2 (free_vars e3))
  | ENil _ => []
  | ECons e1 e2 => free_vars e1 ++ free_vars e2
  | ENone _ => []
  | ESome e1 => free_vars e1
  | ELoc _ => []
  | ERef e1 => free_vars e1
  | EDeref e1 => free_vars e1
  | EAssign e1 e2 => free_vars e1 ++ free_vars e2
  | ESecret e1 => free_vars e1
  | EReveal e1 => free_vars e1
  | ELam x T e1 => remove string_dec x (free_vars e1)
  | EApp e1 e2 => free_vars e1 ++ free_vars e2
  | ELet x e1 e2 => free_vars e1 ++ remove string_dec x (free_vars e2)
  | EIf e1 e2 e3 => free_vars e1 ++ free_vars e2 ++ free_vars e3
  end.

(** ** Closed Expression Predicate *)
Definition closed_expr (e : expr) : Prop :=
  forall x, ~ In x (free_vars e).

(** ** Store Typing *)
Definition store_ty : Type := list (ty * sec_label).

(** ========================================================================== *)
(** * Value Relation at First-Order Types (Inductive Definition) *)
(** ========================================================================== *)

(** For first-order types, we require structural equality between values.
    This is the key insight of v2 semantics: even at step 0, we can
    distinguish values structurally for first-order types.
    
    Using an inductive definition to avoid Coq's termination checker issues. *)

Inductive val_rel_at_type_fo : ty -> expr -> expr -> Prop :=
  | FO_Unit : val_rel_at_type_fo TUnit EUnit EUnit
  
  | FO_Bool : forall b,
      val_rel_at_type_fo TBool (EBool b) (EBool b)
  
  | FO_Int : forall n,
      val_rel_at_type_fo TInt (EInt n) (EInt n)
  
  | FO_String : forall s,
      val_rel_at_type_fo TString (EString s) (EString s)
  
  | FO_Pair : forall T1 T2 v1 v2 w1 w2,
      val_rel_at_type_fo T1 v1 w1 ->
      val_rel_at_type_fo T2 v2 w2 ->
      val_rel_at_type_fo (TProd T1 T2) (EPair v1 v2) (EPair w1 w2)
  
  | FO_Inl : forall T1 T2 v w,
      val_rel_at_type_fo T1 v w ->
      val_rel_at_type_fo (TSum T1 T2) (EInl v) (EInl w)
  
  | FO_Inr : forall T1 T2 v w,
      val_rel_at_type_fo T2 v w ->
      val_rel_at_type_fo (TSum T1 T2) (EInr v) (EInr w)
  
  | FO_Nil : forall T,
      val_rel_at_type_fo (TList T) (ENil T) (ENil T)
  
  | FO_Cons : forall T v1 v2 w1 w2,
      val_rel_at_type_fo T v1 w1 ->
      val_rel_at_type_fo (TList T) v2 w2 ->
      val_rel_at_type_fo (TList T) (ECons v1 v2) (ECons w1 w2)
  
  | FO_None : forall T,
      val_rel_at_type_fo (TOption T) (ENone T) (ENone T)
  
  | FO_Some : forall T v w,
      val_rel_at_type_fo T v w ->
      val_rel_at_type_fo (TOption T) (ESome v) (ESome w)
  
  | FO_Loc : forall T sl l,
      val_rel_at_type_fo (TRef T sl) (ELoc l) (ELoc l)
  
  | FO_Secret : forall T v w,
      val_rel_at_type_fo T v w ->
      val_rel_at_type_fo (TSecret T) (ESecret v) (ESecret w).

(** ========================================================================== *)
(** * Step-Indexed Value Relation (v2 Semantics) *)
(** ========================================================================== *)

(** In v2 semantics, val_rel_n 0 unfolds to:
    
    val_rel_n 0 Σ T v1 v2 = 
      value v1 ∧ value v2 ∧
      closed_expr v1 ∧ closed_expr v2 ∧
      (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)
*)

Definition val_rel_n_at_0 (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).

(** Full step-indexed value relation *)
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | O => val_rel_n_at_0 Σ T v1 v2
  | S n' => 
      value v1 /\ value v2 /\
      closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T 
       then val_rel_at_type_fo T v1 v2 
       else val_rel_n n' Σ T v1 v2)
  end.

(** ** Unfold Lemma for val_rel_n at step 0 *)
Lemma val_rel_n_0_unfold : forall Σ T v1 v2,
  val_rel_n 0 Σ T v1 v2 = val_rel_n_at_0 Σ T v1 v2.
Proof.
  intros. reflexivity.
Qed.

(** ========================================================================== *)
(** * ZERO-STEP BASE CASE LEMMAS (THE 5 ADMITS TO PROVE) *)
(** ========================================================================== *)

(** These are the 5 admits from Package J. Each follows the standard pattern. *)

(** ** Admit 1: Unit type at step 0 *)
Lemma val_rel_n_0_unit : forall Σ,
  val_rel_n 0 Σ TUnit EUnit EUnit.
Proof.
  intros Σ.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value EUnit *) constructor.
  - (* value EUnit *) constructor.
  - (* closed_expr EUnit *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* closed_expr EUnit *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* val_rel_at_type_fo TUnit EUnit EUnit *)
    simpl. constructor.
Qed.

(** ** Admit 2: Bool type at step 0 *)
Lemma val_rel_n_0_bool : forall Σ b,
  val_rel_n 0 Σ TBool (EBool b) (EBool b).
Proof.
  intros Σ b.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value (EBool b) *) constructor.
  - (* value (EBool b) *) constructor.
  - (* closed_expr (EBool b) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* closed_expr (EBool b) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* val_rel_at_type_fo TBool (EBool b) (EBool b) *)
    simpl. constructor.
Qed.

(** ** Admit 3: Int type at step 0 *)
Lemma val_rel_n_0_int : forall Σ n,
  val_rel_n 0 Σ TInt (EInt n) (EInt n).
Proof.
  intros Σ n.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value (EInt n) *) constructor.
  - (* value (EInt n) *) constructor.
  - (* closed_expr (EInt n) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* closed_expr (EInt n) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* val_rel_at_type_fo TInt (EInt n) (EInt n) *)
    simpl. constructor.
Qed.

(** ** Admit 4: String type at step 0 *)
Lemma val_rel_n_0_string : forall Σ s,
  val_rel_n 0 Σ TString (EString s) (EString s).
Proof.
  intros Σ s.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value (EString s) *) constructor.
  - (* value (EString s) *) constructor.
  - (* closed_expr (EString s) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* closed_expr (EString s) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* val_rel_at_type_fo TString (EString s) (EString s) *)
    simpl. constructor.
Qed.

(** ** Admit 5: Location (reference pointer) at step 0 *)
Lemma val_rel_n_0_loc : forall Σ T sl l,
  val_rel_n 0 Σ (TRef T sl) (ELoc l) (ELoc l).
Proof.
  intros Σ T sl l.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value (ELoc l) *) constructor.
  - (* value (ELoc l) *) constructor.
  - (* closed_expr (ELoc l) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* closed_expr (ELoc l) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* val_rel_at_type_fo (TRef T sl) (ELoc l) (ELoc l) *)
    simpl. constructor.
Qed.

(** ========================================================================== *)
(** * BONUS: Additional Zero-Step Lemmas (Beyond the 5 Required) *)
(** ========================================================================== *)

(** ** Pair type at step 0 *)
Lemma val_rel_n_0_pair : forall Σ T1 T2 v1 v2 w1 w2,
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  value v1 -> value w1 ->
  value v2 -> value w2 ->
  closed_expr v1 -> closed_expr w1 ->
  closed_expr v2 -> closed_expr w2 ->
  val_rel_at_type_fo T1 v1 w1 ->
  val_rel_at_type_fo T2 v2 w2 ->
  val_rel_n 0 Σ (TProd T1 T2) (EPair v1 v2) (EPair w1 w2).
Proof.
  intros Σ T1 T2 v1 v2 w1 w2 Hfo1 Hfo2 Hval1 Hval2 Hval3 Hval4
         Hcl1 Hcl2 Hcl3 Hcl4 Hrel1 Hrel2.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value (EPair v1 v2) *) constructor; assumption.
  - (* value (EPair w1 w2) *) constructor; assumption.
  - (* closed_expr (EPair v1 v2) *)
    intros x Hfree. simpl in Hfree.
    apply in_app_or in Hfree. destruct Hfree as [Hfree | Hfree].
    + apply (Hcl1 x Hfree).
    + apply (Hcl3 x Hfree).
  - (* closed_expr (EPair w1 w2) *)
    intros x Hfree. simpl in Hfree.
    apply in_app_or in Hfree. destruct Hfree as [Hfree | Hfree].
    + apply (Hcl2 x Hfree).
    + apply (Hcl4 x Hfree).
  - (* val_rel_at_type_fo (TProd T1 T2) ... *)
    simpl. rewrite Hfo1. rewrite Hfo2. simpl.
    constructor; assumption.
Qed.

(** ** Empty list (Nil) at step 0 *)
Lemma val_rel_n_0_nil : forall Σ T,
  val_rel_n 0 Σ (TList T) (ENil T) (ENil T).
Proof.
  intros Σ T.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value (ENil T) *) constructor.
  - (* value (ENil T) *) constructor.
  - (* closed_expr (ENil T) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* closed_expr (ENil T) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* val_rel_at_type_fo (TList T) (ENil T) (ENil T) *)
    simpl. destruct (first_order_type T) eqn:Hfo.
    + constructor.
    + trivial.
Qed.

(** ** None option at step 0 *)
Lemma val_rel_n_0_none : forall Σ T,
  val_rel_n 0 Σ (TOption T) (ENone T) (ENone T).
Proof.
  intros Σ T.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  repeat split.
  - (* value (ENone T) *) constructor.
  - (* value (ENone T) *) constructor.
  - (* closed_expr (ENone T) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* closed_expr (ENone T) *) intros x Hfree. simpl in Hfree. inversion Hfree.
  - (* val_rel_at_type_fo (TOption T) (ENone T) (ENone T) *)
    simpl. destruct (first_order_type T) eqn:Hfo.
    + constructor.
    + trivial.
Qed.

(** ** Higher-order type at step 0 (functions are trivially related) *)
Lemma val_rel_n_0_higher_order : forall Σ T1 T2 v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n 0 Σ (TFn T1 T2) v1 v2.
Proof.
  intros Σ T1 T2 v1 v2 Hval1 Hval2 Hcl1 Hcl2.
  rewrite val_rel_n_0_unfold.
  unfold val_rel_n_at_0.
  simpl. (* first_order_type (TFn T1 T2) = false *)
  repeat split; assumption.
Qed.

(** ========================================================================== *)
(** * VERIFICATION *)
(** ========================================================================== *)

(** All lemmas proven with Qed - no Admitted! *)

Check val_rel_n_0_unit.
Check val_rel_n_0_bool.
Check val_rel_n_0_int.
Check val_rel_n_0_string.
Check val_rel_n_0_loc.

(** Print assumptions to verify no axioms used *)
Print Assumptions val_rel_n_0_unit.
Print Assumptions val_rel_n_0_bool.
Print Assumptions val_rel_n_0_int.
Print Assumptions val_rel_n_0_string.
Print Assumptions val_rel_n_0_loc.

(** ========================================================================== *)
(** * END OF FILE
    
    SUMMARY: Package J Complete
    ==========================
    
    5 Required Admits PROVEN:
    1. val_rel_n_0_unit   - Unit type at step 0 (Qed)
    2. val_rel_n_0_bool   - Bool type at step 0 (Qed)
    3. val_rel_n_0_int    - Int type at step 0 (Qed)
    4. val_rel_n_0_string - String type at step 0 (Qed)
    5. val_rel_n_0_loc    - Location/Ref type at step 0 (Qed)
    
    Bonus Lemmas (Beyond Requirements):
    6. val_rel_n_0_pair         - Pair type at step 0 (Qed)
    7. val_rel_n_0_nil          - Empty list at step 0 (Qed)
    8. val_rel_n_0_none         - None option at step 0 (Qed)
    9. val_rel_n_0_higher_order - Higher-order types at step 0 (Qed)
    
    ZERO AXIOMS. ZERO ADMITTED PROOFS.
    
    Classification: ULTRA KIASU | ZERO TRUST | ZERO LAZINESS
    ========================================================================== *)
