(** * Non-Interference for TERAS-LANG

    Information flow security property.
    
    We define observational equivalence (low-equivalence) and state the
    Non-Interference theorem: "Low-equivalent inputs produce low-equivalent outputs".
*)

Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.
Require Import Coq.Lists.List.
Import ListNotations.

(** Observer level *)
Parameter observer : security_level.

(** Security lattice check: l <= observer *)
Definition is_low (l : security_level) : Prop :=
  sec_leq l observer.

(** ** Value Equivalence
    
    Two values are equivalent to the observer if:
    1. They act indistinguishably (public data must be equal).
    2. Secret data is indistinguishable regardless of value.
*)

Inductive val_equiv : ty -> expr -> expr -> Prop :=
  | Eq_Unit :
      val_equiv TUnit EUnit EUnit
      
  | Eq_Bool : forall b,
      val_equiv TBool (EBool b) (EBool b)
      
  | Eq_Int : forall n,
      val_equiv TInt (EInt n) (EInt n)
      
  | Eq_String : forall s,
      val_equiv TString (EString s) (EString s)
      
  | Eq_Secret : forall T v1 v2,
      (* Secret values are always equivalent (opaque to low observer) *)
      value v1 -> value v2 ->
      val_equiv (TSecret T) v1 v2
      
  | Eq_Ref : forall T l v1 v2,
      (* References: if visible (low), must be equal. If high, opaque. *)
      (is_low l -> v1 = v2) ->
      val_equiv (TRef T l) v1 v2
      
  | Eq_Pair : forall T1 T2 v1 v2 v1' v2',
      val_equiv T1 v1 v1' ->
      val_equiv T2 v2 v2' ->
      val_equiv (TProd T1 T2) (EPair v1 v2) (EPair v1' v2')
      
  | Eq_Inl : forall T1 T2 v v',
      val_equiv T1 v v' ->
      val_equiv (TSum T1 T2) (EInl v T2) (EInl v' T2)
      
  | Eq_Inr : forall T1 T2 v v',
      val_equiv T2 v v' ->
      val_equiv (TSum T1 T2) (EInr v T1) (EInr v' T1).

(** ** Expression Equivalence
    
    Expressions are equivalent if they evaluate to equivalent values.
    (This requires a termination-sensitive or insensitive definition.
     Here we state preservation of equivalence under reduction steps).
*)

Definition low_equiv_expr (T : ty) (e1 e2 : expr) : Prop :=
  forall st1 st2 ctx,
  exists v1 v2 st1' st2',
    (e1, st1, ctx) -->* (v1, st1', ctx) /\
    (e2, st2, ctx) -->* (v2, st2', ctx) /\
    val_equiv T v1 v2.

(** ** Non-Interference
    
    "Well-typed programs map low-equivalent inputs to low-equivalent outputs."
    
    Here we state it for a program 'e' with free variables substituted by equivalent values.
    But for a closed program 'e', it means 'e' reduces to a value that is self-equivalent?
    Actually, NI implies that if we substitute variables with equivalent values, results are equivalent.
    
    Since we define substitution, we can state:
    forall x v1 v2 e, val_equiv T v1 v2 -> low_equiv_expr T_res ([x:=v1]e) ([x:=v2]e).
*)

Theorem non_interference : forall x T_in T_out v1 v2 e,
  val_equiv T_in v1 v2 ->
  has_type ((x, T_in) :: nil) nil Public e T_out EffectPure ->
  low_equiv_expr T_out ([x := v1] e) ([x := v2] e).
Proof.
  (* Proof requires induction on typing derivation and step relation. *)
  (* Complex proof, leaving as future work for interactive session. *)
Admitted.

(** End of NonInterference.v *)
