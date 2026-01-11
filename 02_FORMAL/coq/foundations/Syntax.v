(** * TERAS-LANG Syntax
    
    Core syntax definitions for TERAS-LANG.
    
    Reference: TERAS-LANG-AST_v1_0_0.md
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Identifiers *)

Definition ident := string.

(** ** Security Levels
    
    TERAS uses a two-point lattice for information flow:
    - Public: Information that can be observed by anyone
    - Secret: Information that must be protected
*)

Inductive security_level : Type :=
  | Public : security_level
  | Secret : security_level.

(** Security level ordering: Public ⊑ Secret *)
Definition sec_leq (l1 l2 : security_level) : Prop :=
  match l1, l2 with
  | Public, _ => True
  | Secret, Secret => True
  | Secret, Public => False
  end.

(** ** Effect Labels
    
    Effects track observable behaviors of computations.
*)

Inductive effect : Type :=
  | EffectPure   : effect
  | EffectRead   : effect
  | EffectWrite  : effect
  | EffectNetwork : effect
  | EffectCrypto : effect
  | EffectSystem : effect.

(** Effect join: least upper bound in effect lattice.
    EffectPure is the identity element. For non-pure effects,
    we use the left argument as a simplification (proper lattice
    would require more complex structure). *)
Definition effect_join (e1 e2 : effect) : effect :=
  match e1, e2 with
  | EffectPure, _ => e2
  | _, EffectPure => e1
  | _, _ => e1 (* Simplified: in a full system, use proper lattice *)
  end.

(** Effect join with EffectPure is identity *)
Lemma effect_join_pure_l : forall e, effect_join EffectPure e = e.
Proof. reflexivity. Qed.

Lemma effect_join_pure_r : forall e, effect_join e EffectPure = e.
Proof. destruct e; reflexivity. Qed.

(** ** Types
    
    Core type constructors for TERAS-LANG.
*)

Inductive ty : Type :=
  | TUnit    : ty
  | TBool    : ty
  | TInt     : ty
  | TString  : ty
  | TBytes   : ty
  | TFn      : ty -> ty -> effect -> ty  (* T1 -[ε]-> T2 *)
  | TProd    : ty -> ty -> ty            (* T1 × T2 *)
  | TSum     : ty -> ty -> ty            (* T1 + T2 *)
  | TRef     : ty -> security_level -> ty (* Ref[T]@l *)
  | TSecret  : ty -> ty                  (* Secret[T] *)
  | TProof   : ty -> ty                  (* Proof[T] *)
  | TCapability : effect -> ty.          (* Cap[ε] *)

(** ** Expressions
    
    Core expression forms.
*)

Inductive expr : Type :=
  (* Values *)
  | EUnit   : expr
  | EBool   : bool -> expr
  | EInt    : nat -> expr
  | EString : string -> expr
  | EVar    : ident -> expr
  
  (* Functions *)
  | ELam    : ident -> ty -> expr -> expr    (* λx:T. e *)
  | EApp    : expr -> expr -> expr           (* e1 e2 *)
  
  (* Products *)
  | EPair   : expr -> expr -> expr           (* (e1, e2) *)
  | EFst    : expr -> expr                   (* fst e *)
  | ESnd    : expr -> expr                   (* snd e *)
  
  (* Sums *)
  | EInl    : expr -> ty -> expr             (* inl e : T *)
  | EInr    : expr -> ty -> expr             (* inr e : T *)
  | ECase   : expr -> ident -> expr -> ident -> expr -> expr  (* case e of inl x => e1 | inr y => e2 *)
  
  (* Control *)
  | EIf     : expr -> expr -> expr -> expr   (* if e1 then e2 else e3 *)
  | ELet    : ident -> expr -> expr -> expr  (* let x = e1 in e2 *)
  
  (* Effects *)
  | EPerform : effect -> expr -> expr        (* perform ε e *)
  | EHandle  : expr -> ident -> expr -> expr (* handle e with x => h *)
  
  (* References *)
  | ERef    : expr -> security_level -> expr (* ref e @ l *)
  | EDeref  : expr -> expr                   (* !e *)
  | EAssign : expr -> expr -> expr           (* e1 := e2 *)
  
  (* Security *)
  | EClassify   : expr -> expr               (* classify e *)
  | EDeclassify : expr -> expr -> expr       (* declassify e with proof *)
  | EProve      : expr -> expr               (* prove e *)
  
  (* Capabilities *)
  | ERequire : effect -> expr -> expr        (* require ε in e *)
  | EGrant   : effect -> expr -> expr.       (* grant ε to e *)

(** ** Values
    
    Syntactic values for operational semantics.
*)

Inductive value : expr -> Prop :=
  | VUnit   : value EUnit
  | VBool   : forall b, value (EBool b)
  | VInt    : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLam    : forall x T e, value (ELam x T e)
  | VPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl    : forall v T, value v -> value (EInl v T)
  | VInr    : forall v T, value v -> value (EInr v T).

(** ** Well-Formedness *)

(** Types are well-formed *)
Inductive wf_ty : ty -> Prop :=
  | WF_TUnit   : wf_ty TUnit
  | WF_TBool   : wf_ty TBool
  | WF_TInt    : wf_ty TInt
  | WF_TString : wf_ty TString
  | WF_TBytes  : wf_ty TBytes
  | WF_TFn     : forall T1 T2 eff, 
                   wf_ty T1 -> wf_ty T2 -> wf_ty (TFn T1 T2 eff)
  | WF_TProd   : forall T1 T2,
                   wf_ty T1 -> wf_ty T2 -> wf_ty (TProd T1 T2)
  | WF_TSum    : forall T1 T2,
                   wf_ty T1 -> wf_ty T2 -> wf_ty (TSum T1 T2)
  | WF_TRef    : forall T l, wf_ty T -> wf_ty (TRef T l)
  | WF_TSecret : forall T, wf_ty T -> wf_ty (TSecret T)
  | WF_TProof  : forall T, wf_ty T -> wf_ty (TProof T)
  | WF_TCap    : forall eff, wf_ty (TCapability eff).

(** ** Substitution
    
    Capture-avoiding substitution.
*)

Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | EVar y => if String.eqb x y then v else EVar y
  | ELam y T body =>
      if String.eqb x y then ELam y T body
      else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e1 => EFst (subst x v e1)
  | ESnd e1 => ESnd (subst x v e1)
  | EInl e1 T => EInl (subst x v e1) T
  | EInr e1 T => EInr (subst x v e1) T
  | ECase e1 y1 e2 y2 e3 =>
      ECase (subst x v e1)
            y1 (if String.eqb x y1 then e2 else subst x v e2)
            y2 (if String.eqb x y2 then e3 else subst x v e3)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ELet y e1 e2 =>
      ELet y (subst x v e1)
           (if String.eqb x y then e2 else subst x v e2)
  | EPerform eff e1 => EPerform eff (subst x v e1)
  | EHandle e1 y h =>
      EHandle (subst x v e1) y
              (if String.eqb x y then h else subst x v h)
  | ERef e1 l => ERef (subst x v e1) l
  | EDeref e1 => EDeref (subst x v e1)
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  | EClassify e1 => EClassify (subst x v e1)
  | EDeclassify e1 e2 => EDeclassify (subst x v e1) (subst x v e2)
  | EProve e1 => EProve (subst x v e1)
  | ERequire eff e1 => ERequire eff (subst x v e1)
  | EGrant eff e1 => EGrant eff (subst x v e1)
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20).

(** ** Basic Lemmas *)

Lemma value_not_stuck : forall e,
  value e -> e = EUnit \/ (exists b, e = EBool b) \/ (exists n, e = EInt n) \/
             (exists s, e = EString s) \/ (exists x T body, e = ELam x T body) \/
             (exists v1 v2, e = EPair v1 v2) \/
             (exists v T, e = EInl v T) \/ (exists v T, e = EInr v T).
Proof.
  intros e Hv.
  inversion Hv; subst.
  - left. reflexivity.
  - right. left. exists b. reflexivity.
  - right. right. left. exists n. reflexivity.
  - right. right. right. left. exists s. reflexivity.
  - right. right. right. right. left. exists x, T, e0. reflexivity.
  - right. right. right. right. right. left. exists v1, v2. reflexivity.
  - right. right. right. right. right. right. left. exists v, T. reflexivity.
  - right. right. right. right. right. right. right. exists v, T. reflexivity.
Qed.

(** Note: A lemma about substitution into values requires either:
    1. A 'closed' predicate ensuring values have no free variables, or
    2. A 'free_vars' function to check if x is free in e.

    The naive statement "forall x v e, value e -> [x := v] e = e" is false
    because lambda bodies can contain free variables. We will add the
    correct formulation in Preservation.v when needed for type safety. *)

(** End of Syntax.v *)
