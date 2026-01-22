(** * Syntax: Core Types and Expressions for TERAS-LANG *)

Require Import TerasLang.Prelude.Prelude.

(** ** Security Labels *)

Inductive sec_label : Type :=
  | SL_Low : sec_label      (* Public data *)
  | SL_High : sec_label.    (* Secret data *)

Definition sec_label_leq (l1 l2 : sec_label) : bool :=
  match l1, l2 with
  | SL_Low, _ => true
  | SL_High, SL_High => true
  | SL_High, SL_Low => false
  end.

(** ** Types *)

Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> sec_label -> ty   (* Reference with security label *)
  | TSecret : ty -> ty              (* Secret wrapper type *)
  | TLabeled : ty -> sec_label -> ty  (* Labeled type *)
  | TTainted : ty -> sec_label -> ty  (* Tainted type *)
  | TFn : ty -> ty -> ty.          (* Function type *)

(** ** First-Order Type Predicate *)

(** A type is first-order if it does not contain function types.
    For first-order types, we require structural equality at step 0. *)

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList T' | TOption T' | TRef T' _ => first_order_type T'
  | TSecret T' | TLabeled T' _ | TTainted T' _ => first_order_type T'
  | TFn _ _ => false  (* Functions are higher-order *)
  end.

(** ** Expressions *)

Inductive expr : Type :=
  (* Values *)
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : loc -> expr                   (* Memory location *)
  | EPair : expr -> expr -> expr         (* Pair constructor *)
  | EInl : expr -> expr                  (* Left injection *)
  | EInr : expr -> expr                  (* Right injection *)
  | ENil : expr                          (* Empty list *)
  | ECons : expr -> expr -> expr         (* List constructor *)
  | ENone : expr                         (* None option *)
  | ESome : expr -> expr                 (* Some option *)
  | ELam : var -> ty -> expr -> expr     (* Lambda abstraction *)
  (* Non-values *)
  | EVar : var -> expr                   (* Variable *)
  | EApp : expr -> expr -> expr          (* Application *)
  | ELet : var -> expr -> expr -> expr   (* Let binding *)
  | EIf : expr -> expr -> expr -> expr   (* Conditional *)
  | EFst : expr -> expr                  (* First projection *)
  | ESnd : expr -> expr                  (* Second projection *)
  | ECase : expr -> var -> expr -> var -> expr -> expr  (* Sum case *)
  | ERef : expr -> expr                  (* Reference creation *)
  | EDeref : expr -> expr                (* Dereference *)
  | EAssign : expr -> expr -> expr       (* Assignment *)
  | ESecret : expr -> expr               (* Secret wrapper *)
  | EUnsecret : expr -> expr.            (* Secret unwrap *)

(** ** Value Predicate *)

Inductive value : expr -> Prop :=
  | V_Unit : value EUnit
  | V_Bool : forall b, value (EBool b)
  | V_Int : forall i, value (EInt i)
  | V_String : forall s, value (EString s)
  | V_Loc : forall l, value (ELoc l)
  | V_Pair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | V_Inl : forall v, value v -> value (EInl v)
  | V_Inr : forall v, value v -> value (EInr v)
  | V_Nil : value ENil
  | V_Cons : forall v1 v2, value v1 -> value v2 -> value (ECons v1 v2)
  | V_None : value ENone
  | V_Some : forall v, value v -> value (ESome v)
  | V_Lam : forall x T e, value (ELam x T e).

(** ** Free Variables *)

Fixpoint free_vars (e : expr) : list var :=
  match e with
  | EUnit | EBool _ | EInt _ | EString _ | ELoc _ | ENil | ENone => nil
  | EVar x => [x]
  | EPair e1 e2 | EApp e1 e2 | ECons e1 e2 | EAssign e1 e2 =>
      free_vars e1 ++ free_vars e2
  | EInl e | EInr e | EFst e | ESnd e | ERef e | EDeref e 
  | ESome e | ESecret e | EUnsecret e =>
      free_vars e
  | ELam x _ e => filter (fun y => negb (String.eqb x y)) (free_vars e)
  | ELet x e1 e2 =>
      free_vars e1 ++ filter (fun y => negb (String.eqb x y)) (free_vars e2)
  | EIf e1 e2 e3 => free_vars e1 ++ free_vars e2 ++ free_vars e3
  | ECase e1 x1 e2 x2 e3 =>
      free_vars e1 ++
      filter (fun y => negb (String.eqb x1 y)) (free_vars e2) ++
      filter (fun y => negb (String.eqb x2 y)) (free_vars e3)
  end.

(** ** Free Variable Membership *)

Inductive free_in : var -> expr -> Prop :=
  | FI_Var : forall x, free_in x (EVar x)
  | FI_Pair1 : forall x e1 e2, free_in x e1 -> free_in x (EPair e1 e2)
  | FI_Pair2 : forall x e1 e2, free_in x e2 -> free_in x (EPair e1 e2)
  | FI_Inl : forall x e, free_in x e -> free_in x (EInl e)
  | FI_Inr : forall x e, free_in x e -> free_in x (EInr e)
  | FI_Cons1 : forall x e1 e2, free_in x e1 -> free_in x (ECons e1 e2)
  | FI_Cons2 : forall x e1 e2, free_in x e2 -> free_in x (ECons e1 e2)
  | FI_Some : forall x e, free_in x e -> free_in x (ESome e)
  | FI_Lam : forall x y T e, x <> y -> free_in x e -> free_in x (ELam y T e)
  | FI_App1 : forall x e1 e2, free_in x e1 -> free_in x (EApp e1 e2)
  | FI_App2 : forall x e1 e2, free_in x e2 -> free_in x (EApp e1 e2)
  | FI_Let1 : forall x y e1 e2, free_in x e1 -> free_in x (ELet y e1 e2)
  | FI_Let2 : forall x y e1 e2, x <> y -> free_in x e2 -> free_in x (ELet y e1 e2)
  | FI_If1 : forall x e1 e2 e3, free_in x e1 -> free_in x (EIf e1 e2 e3)
  | FI_If2 : forall x e1 e2 e3, free_in x e2 -> free_in x (EIf e1 e2 e3)
  | FI_If3 : forall x e1 e2 e3, free_in x e3 -> free_in x (EIf e1 e2 e3)
  | FI_Fst : forall x e, free_in x e -> free_in x (EFst e)
  | FI_Snd : forall x e, free_in x e -> free_in x (ESnd e)
  | FI_Case1 : forall x e1 x1 e2 x2 e3, 
      free_in x e1 -> free_in x (ECase e1 x1 e2 x2 e3)
  | FI_Case2 : forall x e1 x1 e2 x2 e3,
      x <> x1 -> free_in x e2 -> free_in x (ECase e1 x1 e2 x2 e3)
  | FI_Case3 : forall x e1 x1 e2 x2 e3,
      x <> x2 -> free_in x e3 -> free_in x (ECase e1 x1 e2 x2 e3)
  | FI_Ref : forall x e, free_in x e -> free_in x (ERef e)
  | FI_Deref : forall x e, free_in x e -> free_in x (EDeref e)
  | FI_Assign1 : forall x e1 e2, free_in x e1 -> free_in x (EAssign e1 e2)
  | FI_Assign2 : forall x e1 e2, free_in x e2 -> free_in x (EAssign e1 e2)
  | FI_Secret : forall x e, free_in x e -> free_in x (ESecret e)
  | FI_Unsecret : forall x e, free_in x e -> free_in x (EUnsecret e).

(** ** Closed Expression *)

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

(** Proof that values are closed for certain base types *)

Lemma value_unit_closed : closed_expr EUnit.
Proof.
  unfold closed_expr. intros x Hfree.
  inversion Hfree.
Qed.

Lemma value_bool_closed : forall b, closed_expr (EBool b).
Proof.
  unfold closed_expr. intros b x Hfree.
  inversion Hfree.
Qed.

Lemma value_int_closed : forall i, closed_expr (EInt i).
Proof.
  unfold closed_expr. intros i x Hfree.
  inversion Hfree.
Qed.

Lemma value_string_closed : forall s, closed_expr (EString s).
Proof.
  unfold closed_expr. intros s x Hfree.
  inversion Hfree.
Qed.

Lemma value_loc_closed : forall l, closed_expr (ELoc l).
Proof.
  unfold closed_expr. intros l x Hfree.
  inversion Hfree.
Qed.

Lemma value_nil_closed : closed_expr ENil.
Proof.
  unfold closed_expr. intros x Hfree.
  inversion Hfree.
Qed.

Lemma value_none_closed : closed_expr ENone.
Proof.
  unfold closed_expr. intros x Hfree.
  inversion Hfree.
Qed.
