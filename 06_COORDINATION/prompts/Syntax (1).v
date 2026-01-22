(** * Syntax.v: Core Syntax Definitions for TERAS-LANG *)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope Z_scope.

(** ** Identifiers *)
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
  | TRef _ _ => true  (* References are first-order pointers *)
  | TSecret T1 => first_order_type T1
  | TFn _ _ => false  (* Functions are higher-order *)
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

(** Closed expressions have no free variables *)
Lemma closed_nil : forall e, closed_expr e <-> free_vars e = [].
Proof.
  intros e. unfold closed_expr. split.
  - intros H. destruct (free_vars e) eqn:Hfv.
    + reflexivity.
    + exfalso. apply (H v). rewrite Hfv. left. reflexivity.
  - intros H x Hin. rewrite H in Hin. inversion Hin.
Qed.

(** Values have specific syntactic forms - useful for inversion *)
Lemma value_not_var : forall x, ~ value (EVar x).
Proof. intros x H. inversion H. Qed.

Lemma value_not_app : forall e1 e2, ~ value (EApp e1 e2).
Proof. intros e1 e2 H. inversion H. Qed.

Lemma value_not_let : forall x e1 e2, ~ value (ELet x e1 e2).
Proof. intros x e1 e2 H. inversion H. Qed.
