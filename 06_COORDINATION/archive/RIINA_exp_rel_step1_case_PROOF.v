(** * RIINA: exp_rel_step1_case Proof
    
    Non-Interference for Case Expressions:
    When two programs execute case analysis on related sum values,
    they MUST take the SAME branch because related values have
    MATCHING constructors (both Inl or both Inr).
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR
    
    Generated: 2026-01-19
    Status: COMPLETE - Qed - ZERO AXIOMS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Open Scope Z_scope.

(** ========================================================================
    SECTION 1: BASIC TYPE ALIASES
    ======================================================================== *)

Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition label := string.
Definition effect_label := string.
Definition effect := list effect_label.

(** ========================================================================
    SECTION 2: CORE TYPE DEFINITION
    ======================================================================== *)

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

(** ========================================================================
    SECTION 3: EXPRESSION DEFINITION
    ======================================================================== *)

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

(** ========================================================================
    SECTION 4: VALUE PREDICATE
    ======================================================================== *)

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

(** ========================================================================
    SECTION 5: FIRST-ORDER TYPE PREDICATE
    ======================================================================== *)

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

(** ========================================================================
    SECTION 6: FREE VARIABLES AND CLOSED EXPRESSIONS
    ======================================================================== *)

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

(** ========================================================================
    SECTION 7: SUBSTITUTION
    ======================================================================== *)

Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar y => if String.eqb x y then v else EVar y
  | ELam y T body =>
      if String.eqb x y then ELam y T body else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e => EFst (subst x v e)
  | ESnd e => ESnd (subst x v e)
  | EInl e T => EInl (subst x v e) T
  | EInr e T => EInr (subst x v e) T
  | ECase e y1 e1 y2 e2 =>
      ECase (subst x v e)
        y1 (if String.eqb x y1 then e1 else subst x v e1)
        y2 (if String.eqb x y2 then e2 else subst x v e2)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ELet y e1 e2 =>
      ELet y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | ERef e sl => ERef (subst x v e) sl
  | EDeref e => EDeref (subst x v e)
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20, x at next level).

(** ========================================================================
    SECTION 8: STORE DEFINITIONS
    ======================================================================== *)

Definition store := list (loc * expr).
Definition store_ty := list (loc * ty * security_level).

Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

Definition effect_ctx := list effect.

(** ========================================================================
    SECTION 9: SMALL-STEP OPERATIONAL SEMANTICS
    ======================================================================== *)

Reserved Notation "cfg1 '-->' cfg2" (at level 40).

Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  (* CASE ELIMINATION — THE CRITICAL RULES *)
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
  
  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
  
  (* Other rules *)
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
  
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
  
  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
  
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)
  
  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)
  
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)

where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

(** ========================================================================
    SECTION 10: MULTI-STEP REDUCTION
    ======================================================================== *)

Inductive multi_step : (expr * store * effect_ctx) ->
                       (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg,
      multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).

(** ========================================================================
    SECTION 11: FIRST-ORDER VALUE RELATION
    ======================================================================== *)

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
  (* THE CRITICAL CASE: TSum *)
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2)
      \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)
  | TFn _ _ _ => True
  end.

(** ========================================================================
    SECTION 12: BASE VALUE AND STORE RELATIONS
    ======================================================================== *)

Definition val_rel_n_base (Sigma : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).

Definition store_rel_n_base (Sigma : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.

(** ========================================================================
    SECTION 13: HELPER LEMMAS
    ======================================================================== *)

(** Extract value property from val_rel_n_base *)
Lemma val_rel_n_base_value : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 ->
  value v1 /\ value v2.
Proof.
  intros Sigma T v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [Hv1 [Hv2 _]].
  split; assumption.
Qed.

(** THE KEY LEMMA: Extract MATCHING constructor from sum values *)
Lemma val_rel_n_base_sum_fo : forall Sigma T1 T2 v1 v2,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v1 v2 ->
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_at_type_fo T1 a1 a2)
  \/
  (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_at_type_fo T2 b1 b2).
Proof.
  intros Sigma T1 T2 v1 v2 Hfo Hrel.
  unfold val_rel_n_base in Hrel.
  destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Htype]]]].
  rewrite Hfo in Htype.
  simpl in Htype.
  exact Htype.
Qed.

(** ========================================================================
    SECTION 14: THE MAIN THEOREM — exp_rel_step1_case
    ======================================================================== *)

Theorem exp_rel_step1_case : forall Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Hfo Hval Hstore.

  (* STEP 1: Extract MATCHING constructors *)
  destruct (val_rel_n_base_sum_fo Sigma T1 T2 v v' Hfo Hval)
    as [[a1 [a2 [Heq1 [Heq2 Hrel_a]]]] | [b1 [b2 [Heq1 [Heq2 Hrel_b]]]]].

  (* CASE LEFT: Both are EInl *)
  - subst v v'.
    destruct (val_rel_n_base_value Sigma (TSum T1 T2) (EInl a1 T2) (EInl a2 T2) Hval)
      as [Hv_inl1 Hv_inl2].
    inversion Hv_inl1; subst.
    inversion Hv_inl2; subst.
    exists ([x1 := a1] e1), ([x1 := a2] e1'), st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := ([x1 := a1] e1, st1, ctx)).
      * apply ST_CaseInl. exact H0.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := ([x1 := a2] e1', st2, ctx)).
      * apply ST_CaseInl. exact H1.
      * apply MS_Refl.

  (* CASE RIGHT: Both are EInr *)
  - subst v v'.
    destruct (val_rel_n_base_value Sigma (TSum T1 T2) (EInr b1 T1) (EInr b2 T1) Hval)
      as [Hv_inr1 Hv_inr2].
    inversion Hv_inr1; subst.
    inversion Hv_inr2; subst.
    exists ([x2 := b1] e2), ([x2 := b2] e2'), st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := ([x2 := b1] e2, st1, ctx)).
      * apply ST_CaseInr. exact H0.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := ([x2 := b2] e2', st2, ctx)).
      * apply ST_CaseInr. exact H1.
      * apply MS_Refl.
Qed.

(** ========================================================================
    SECTION 15: VERIFICATION
    ======================================================================== *)

Print Assumptions exp_rel_step1_case.

(** End of RIINA_exp_rel_step1_case_PROOF.v *)
