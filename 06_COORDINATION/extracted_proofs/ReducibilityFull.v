(* ============================================================================ *)
(*                         TERAS-LANG: REDUCIBILITY FULL                        *)
(* ============================================================================ *)
(*                                                                              *)
(*  Document: ReducibilityFull.v                                                *)
(*  Version:  1.0.0                                                             *)
(*  Date:     2026-01-19                                                        *)
(*  Purpose:  Complete step-indexed logical relations for type safety,          *)
(*            non-interference, and semantic security properties                *)
(*                                                                              *)
(*  Classification: ULTRA KIASU | ZERO TRUST | ZERO LAZINESS                    *)
(*                                                                              *)
(*  Dependencies:                                                               *)
(*    - Prelude/LibTactics.v                                                    *)
(*    - Prelude/Prelude.v                                                       *)
(*    - Typing/Syntax.v                                                         *)
(*    - Typing/Context.v                                                        *)
(*    - Typing/Typing.v                                                         *)
(*    - Typing/Values.v                                                         *)
(*    - Typing/Store.v                                                          *)
(*    - Typing/Semantics.v                                                      *)
(*    - Effects/Effects.v                                                       *)
(*    - Linear/LinearTypes.v                                                    *)
(*    - Security/SecurityTypes.v                                                *)
(*                                                                              *)
(* ============================================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ============================================================================ *)
(*                           SECTION 1: SYNTAX                                  *)
(* ============================================================================ *)

(** Security levels for information flow control *)
Inductive sec_level : Type :=
  | Low : sec_level
  | High : sec_level.

(** Security labels for types *)
Inductive sec_label : Type :=
  | SL_Low : sec_label
  | SL_High : sec_label.

Definition label_level (l : sec_label) : sec_level :=
  match l with
  | SL_Low => Low
  | SL_High => High
  end.

(** Modes: Linear, Affine, Unrestricted *)
Inductive mode : Type :=
  | MLinear : mode
  | MAffine : mode
  | MUnrestricted : mode.

(** Types *)
Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TNat : ty
  | TInt : ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TArrow : mode -> ty -> ty -> ty -> ty (* mode, param_ty, effect_row, return_ty *)
  | TRef : ty -> ty
  | TSecret : ty -> ty
  | TConstantTime : ty -> ty
  | TSpeculationSafe : ty -> ty
  | TSecretRef : ty -> ty
  | TForall : ty -> ty  (* universally quantified type *)
  | TExists : ty -> ty  (* existentially quantified type *)
  | TRec : ty -> ty     (* recursive type *)
  | TVar : nat -> ty    (* type variable (de Bruijn index) *)
  | TLabeled : sec_label -> ty -> ty.  (* labeled type for IFC *)

(** Expressions *)
Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | ENat : nat -> expr
  | EInt : Z -> expr
  | EVar : nat -> expr     (* de Bruijn index *)
  | EAbs : mode -> ty -> expr -> expr  (* lambda abstraction *)
  | EApp : expr -> expr -> expr
  | ETAbs : expr -> expr   (* type abstraction *)
  | ETApp : expr -> ty -> expr  (* type application *)
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | EInl : ty -> expr -> expr
  | EInr : ty -> expr -> expr
  | ECase : expr -> expr -> expr -> expr
  | ERef : expr -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  | ESeq : expr -> expr -> expr
  | ELet : expr -> expr -> expr
  | ELetRec : ty -> expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | EFix : expr -> expr
  | EFold : ty -> expr -> expr
  | EUnfold : expr -> expr
  | ELoc : nat -> expr     (* memory location *)
  | EDrop : expr -> expr   (* linear resource drop *)
  | ESecret : expr -> expr (* lift to secret *)
  | EDeclassify : expr -> expr (* declassification *)
  | ESanitize : expr -> expr.  (* sanitization *)

(** Values predicate *)
Fixpoint is_value (e : expr) : Prop :=
  match e with
  | EUnit => True
  | EBool _ => True
  | ENat _ => True
  | EInt _ => True
  | EAbs _ _ _ => True
  | ETAbs _ => True
  | EPair e1 e2 => is_value e1 /\ is_value e2
  | EInl _ e => is_value e
  | EInr _ e => is_value e
  | ELoc _ => True
  | EFold _ e => is_value e
  | ESecret e => is_value e
  | _ => False
  end.

(** Extract value from expression (partial) *)
Definition value := { e : expr | is_value e }.

(* ============================================================================ *)
(*                        SECTION 2: STORES AND SEMANTICS                       *)
(* ============================================================================ *)

(** Store cells contain values *)
Record store_cell : Type := mk_cell {
  cell_value : expr;
  cell_type : ty;
  cell_sec_level : sec_level;
}.

(** Store is a partial map from locations to cells *)
Definition store := nat -> option store_cell.

Definition store_empty : store := fun _ => None.

Definition store_lookup (σ : store) (l : nat) : option store_cell :=
  σ l.

Definition store_update (σ : store) (l : nat) (c : store_cell) : store :=
  fun l' => if Nat.eqb l' l then Some c else σ l'.

Definition store_alloc (σ : store) (c : store_cell) : (store * nat) :=
  let l := List.length (List.filter 
             (fun n => match σ n with Some _ => true | None => false end)
             (List.seq 0 1000)) in  (* Simplified allocation *)
  (store_update σ l c, l).

Definition store_dom (σ : store) : list nat :=
  List.filter 
    (fun n => match σ n with Some _ => true | None => false end)
    (List.seq 0 1000).

(** Store typing *)
Definition store_typing := nat -> option ty.

Definition store_typing_empty : store_typing := fun _ => None.

Definition store_typing_lookup (Σ : store_typing) (l : nat) : option ty :=
  Σ l.

Definition store_typing_update (Σ : store_typing) (l : nat) (τ : ty) : store_typing :=
  fun l' => if Nat.eqb l' l then Some τ else Σ l'.

(** Store well-formedness: store agrees with store typing *)
Definition store_well_typed (σ : store) (Σ : store_typing) : Prop :=
  forall l τ,
    Σ l = Some τ ->
    exists c, σ l = Some c /\ cell_type c = τ.

(** Small-step operational semantics *)
Inductive step : expr * store -> expr * store -> Prop :=
  (* Beta reduction *)
  | step_app_abs : forall m τ e v σ,
      is_value v ->
      step (EApp (EAbs m τ e) v, σ) (subst 0 v e, σ)
  (* Type application *)
  | step_tapp : forall e τ σ,
      step (ETApp (ETAbs e) τ, σ) (tsubst 0 τ e, σ)
  (* Pairs *)
  | step_fst : forall v1 v2 σ,
      is_value v1 -> is_value v2 ->
      step (EFst (EPair v1 v2), σ) (v1, σ)
  | step_snd : forall v1 v2 σ,
      is_value v1 -> is_value v2 ->
      step (ESnd (EPair v1 v2), σ) (v2, σ)
  (* Sums *)
  | step_case_inl : forall τ v e1 e2 σ,
      is_value v ->
      step (ECase (EInl τ v) e1 e2, σ) (EApp e1 v, σ)
  | step_case_inr : forall τ v e1 e2 σ,
      is_value v ->
      step (ECase (EInr τ v) e1 e2, σ) (EApp e2 v, σ)
  (* References *)
  | step_ref : forall v l σ σ' τ,
      is_value v ->
      store_alloc σ (mk_cell v τ Low) = (σ', l) ->
      step (ERef v, σ) (ELoc l, σ')
  | step_deref : forall l c σ,
      store_lookup σ l = Some c ->
      step (EDeref (ELoc l), σ) (cell_value c, σ)
  | step_assign : forall l v c σ,
      is_value v ->
      store_lookup σ l = Some c ->
      step (EAssign (ELoc l) v, σ) (EUnit, store_update σ l (mk_cell v (cell_type c) (cell_sec_level c)))
  (* Sequencing *)
  | step_seq : forall v e σ,
      is_value v ->
      step (ESeq v e, σ) (e, σ)
  (* Let *)
  | step_let : forall v e σ,
      is_value v ->
      step (ELet v e, σ) (subst 0 v e, σ)
  (* Conditionals *)
  | step_if_true : forall e1 e2 σ,
      step (EIf (EBool true) e1 e2, σ) (e1, σ)
  | step_if_false : forall e1 e2 σ,
      step (EIf (EBool false) e1 e2, σ) (e2, σ)
  (* Fix *)
  | step_fix : forall e σ,
      step (EFix (EAbs MUnrestricted (TArrow MUnrestricted TUnit TUnit TUnit) e), σ) 
           (subst 0 (EFix (EAbs MUnrestricted (TArrow MUnrestricted TUnit TUnit TUnit) e)) e, σ)
  (* Fold/Unfold *)
  | step_unfold : forall τ v σ,
      is_value v ->
      step (EUnfold (EFold τ v), σ) (v, σ)
  (* Secret operations *)
  | step_declassify : forall v σ,
      is_value v ->
      step (EDeclassify (ESecret v), σ) (v, σ)
  (* Congruence rules *)
  | step_app_l : forall e1 e1' e2 σ σ',
      step (e1, σ) (e1', σ') ->
      step (EApp e1 e2, σ) (EApp e1' e2, σ')
  | step_app_r : forall v e e' σ σ',
      is_value v ->
      step (e, σ) (e', σ') ->
      step (EApp v e, σ) (EApp v e', σ')
  | step_pair_l : forall e1 e1' e2 σ σ',
      step (e1, σ) (e1', σ') ->
      step (EPair e1 e2, σ) (EPair e1' e2, σ')
  | step_pair_r : forall v e e' σ σ',
      is_value v ->
      step (e, σ) (e', σ') ->
      step (EPair v e, σ) (EPair v e', σ')
  | step_fst_cong : forall e e' σ σ',
      step (e, σ) (e', σ') ->
      step (EFst e, σ) (EFst e', σ')
  | step_snd_cong : forall e e' σ σ',
      step (e, σ) (e', σ') ->
      step (ESnd e, σ) (ESnd e', σ')
  | step_inl : forall τ e e' σ σ',
      step (e, σ) (e', σ') ->
      step (EInl τ e, σ) (EInl τ e', σ')
  | step_inr : forall τ e e' σ σ',
      step (e, σ) (e', σ') ->
      step (EInr τ e, σ) (EInr τ e', σ')
  | step_case_cong : forall e e' e1 e2 σ σ',
      step (e, σ) (e', σ') ->
      step (ECase e e1 e2, σ) (ECase e' e1 e2, σ')
  | step_ref_cong : forall e e' σ σ',
      step (e, σ) (e', σ') ->
      step (ERef e, σ) (ERef e', σ')
  | step_deref_cong : forall e e' σ σ',
      step (e, σ) (e', σ') ->
      step (EDeref e, σ) (EDeref e', σ')
  | step_assign_l : forall e1 e1' e2 σ σ',
      step (e1, σ) (e1', σ') ->
      step (EAssign e1 e2, σ) (EAssign e1' e2, σ')
  | step_assign_r : forall v e e' σ σ',
      is_value v ->
      step (e, σ) (e', σ') ->
      step (EAssign v e, σ) (EAssign v e', σ')
  | step_seq_cong : forall e1 e1' e2 σ σ',
      step (e1, σ) (e1', σ') ->
      step (ESeq e1 e2, σ) (ESeq e1' e2, σ')
  | step_let_cong : forall e1 e1' e2 σ σ',
      step (e1, σ) (e1', σ') ->
      step (ELet e1 e2, σ) (ELet e1' e2, σ')
  | step_if_cong : forall e e' e1 e2 σ σ',
      step (e, σ) (e', σ') ->
      step (EIf e e1 e2, σ) (EIf e' e1 e2, σ')
  | step_fold_cong : forall τ e e' σ σ',
      step (e, σ) (e', σ') ->
      step (EFold τ e, σ) (EFold τ e', σ')
  | step_unfold_cong : forall e e' σ σ',
      step (e, σ) (e', σ') ->
      step (EUnfold e, σ) (EUnfold e', σ')
  | step_secret_cong : forall e e' σ σ',
      step (e, σ) (e', σ') ->
      step (ESecret e, σ) (ESecret e', σ')
  | step_declassify_cong : forall e e' σ σ',
      step (e, σ) (e', σ') ->
      step (EDeclassify e, σ) (EDeclassify e', σ')

(** Substitution (placeholder - needs full implementation) *)
with subst : nat -> expr -> expr -> expr := fun _ v e => e
with tsubst : nat -> ty -> expr -> expr := fun _ τ e => e.

(** Multi-step reduction *)
Inductive multi_step : expr * store -> expr * store -> Prop :=
  | multi_refl : forall e σ, multi_step (e, σ) (e, σ)
  | multi_step_trans : forall e1 σ1 e2 σ2 e3 σ3,
      step (e1, σ1) (e2, σ2) ->
      multi_step (e2, σ2) (e3, σ3) ->
      multi_step (e1, σ1) (e3, σ3).

Notation "c1 '-->*' c2" := (multi_step c1 c2) (at level 40).

(** n-step reduction *)
Inductive nsteps : nat -> expr * store -> expr * store -> Prop :=
  | nsteps_0 : forall e σ, nsteps 0 (e, σ) (e, σ)
  | nsteps_S : forall n e1 σ1 e2 σ2 e3 σ3,
      step (e1, σ1) (e2, σ2) ->
      nsteps n (e2, σ2) (e3, σ3) ->
      nsteps (S n) (e1, σ1) (e3, σ3).

(* ============================================================================ *)
(*                    SECTION 3: TYPING CONTEXTS AND JUDGMENTS                  *)
(* ============================================================================ *)

(** Typing context entry *)
Inductive ctx_entry : Type :=
  | CE_Var : ty -> mode -> ctx_entry
  | CE_TVar : ctx_entry.

(** Typing context *)
Definition context := list ctx_entry.

(** Context lookup *)
Fixpoint ctx_lookup (Γ : context) (x : nat) : option ctx_entry :=
  match Γ, x with
  | nil, _ => None
  | e :: _, 0 => Some e
  | _ :: Γ', S x' => ctx_lookup Γ' x'
  end.

(** Context well-formedness *)
Inductive ctx_wf : context -> Prop :=
  | ctx_wf_nil : ctx_wf nil
  | ctx_wf_cons_var : forall Γ τ m,
      ctx_wf Γ ->
      ctx_wf (CE_Var τ m :: Γ)
  | ctx_wf_cons_tvar : forall Γ,
      ctx_wf Γ ->
      ctx_wf (CE_TVar :: Γ).

(** Kinding *)
Inductive kind : Type :=
  | KType : kind
  | KArrow : kind -> kind -> kind.

(** Well-formed types *)
Inductive wf_ty : context -> ty -> kind -> Prop :=
  | wf_unit : forall Γ, wf_ty Γ TUnit KType
  | wf_bool : forall Γ, wf_ty Γ TBool KType
  | wf_nat : forall Γ, wf_ty Γ TNat KType
  | wf_int : forall Γ, wf_ty Γ TInt KType
  | wf_prod : forall Γ τ1 τ2,
      wf_ty Γ τ1 KType ->
      wf_ty Γ τ2 KType ->
      wf_ty Γ (TProd τ1 τ2) KType
  | wf_sum : forall Γ τ1 τ2,
      wf_ty Γ τ1 KType ->
      wf_ty Γ τ2 KType ->
      wf_ty Γ (TSum τ1 τ2) KType
  | wf_arrow : forall Γ m τ1 ε τ2,
      wf_ty Γ τ1 KType ->
      wf_ty Γ ε KType ->
      wf_ty Γ τ2 KType ->
      wf_ty Γ (TArrow m τ1 ε τ2) KType
  | wf_ref : forall Γ τ,
      wf_ty Γ τ KType ->
      wf_ty Γ (TRef τ) KType
  | wf_secret : forall Γ τ,
      wf_ty Γ τ KType ->
      wf_ty Γ (TSecret τ) KType
  | wf_ct : forall Γ τ,
      wf_ty Γ τ KType ->
      wf_ty Γ (TConstantTime τ) KType
  | wf_speculative : forall Γ τ,
      wf_ty Γ τ KType ->
      wf_ty Γ (TSpeculationSafe τ) KType
  | wf_var : forall Γ x,
      ctx_lookup Γ x = Some CE_TVar ->
      wf_ty Γ (TVar x) KType
  | wf_forall : forall Γ τ,
      wf_ty (CE_TVar :: Γ) τ KType ->
      wf_ty Γ (TForall τ) KType
  | wf_rec : forall Γ τ,
      wf_ty (CE_TVar :: Γ) τ KType ->
      wf_ty Γ (TRec τ) KType
  | wf_labeled : forall Γ l τ,
      wf_ty Γ τ KType ->
      wf_ty Γ (TLabeled l τ) KType.

(** Main typing judgment *)
Inductive has_type : context -> store_typing -> expr -> ty -> Prop :=
  (* Literals *)
  | T_Unit : forall Γ Σ,
      ctx_wf Γ ->
      has_type Γ Σ EUnit TUnit
  | T_Bool : forall Γ Σ b,
      ctx_wf Γ ->
      has_type Γ Σ (EBool b) TBool
  | T_Nat : forall Γ Σ n,
      ctx_wf Γ ->
      has_type Γ Σ (ENat n) TNat
  | T_Int : forall Γ Σ z,
      ctx_wf Γ ->
      has_type Γ Σ (EInt z) TInt
  (* Variables *)
  | T_Var : forall Γ Σ x τ m,
      ctx_wf Γ ->
      ctx_lookup Γ x = Some (CE_Var τ m) ->
      has_type Γ Σ (EVar x) τ
  (* Abstraction *)
  | T_Abs : forall Γ Σ m τ1 e τ2,
      has_type (CE_Var τ1 m :: Γ) Σ e τ2 ->
      has_type Γ Σ (EAbs m τ1 e) (TArrow m τ1 TUnit τ2)
  (* Application *)
  | T_App : forall Γ Σ e1 e2 m τ1 ε τ2,
      has_type Γ Σ e1 (TArrow m τ1 ε τ2) ->
      has_type Γ Σ e2 τ1 ->
      has_type Γ Σ (EApp e1 e2) τ2
  (* Type abstraction *)
  | T_TAbs : forall Γ Σ e τ,
      has_type (CE_TVar :: Γ) Σ e τ ->
      has_type Γ Σ (ETAbs e) (TForall τ)
  (* Type application *)
  | T_TApp : forall Γ Σ e τ1 τ2,
      has_type Γ Σ e (TForall τ1) ->
      wf_ty Γ τ2 KType ->
      has_type Γ Σ (ETApp e τ2) (ty_subst 0 τ2 τ1)
  (* Pairs *)
  | T_Pair : forall Γ Σ e1 e2 τ1 τ2,
      has_type Γ Σ e1 τ1 ->
      has_type Γ Σ e2 τ2 ->
      has_type Γ Σ (EPair e1 e2) (TProd τ1 τ2)
  | T_Fst : forall Γ Σ e τ1 τ2,
      has_type Γ Σ e (TProd τ1 τ2) ->
      has_type Γ Σ (EFst e) τ1
  | T_Snd : forall Γ Σ e τ1 τ2,
      has_type Γ Σ e (TProd τ1 τ2) ->
      has_type Γ Σ (ESnd e) τ2
  (* Sums *)
  | T_Inl : forall Γ Σ e τ1 τ2,
      has_type Γ Σ e τ1 ->
      wf_ty Γ τ2 KType ->
      has_type Γ Σ (EInl τ2 e) (TSum τ1 τ2)
  | T_Inr : forall Γ Σ e τ1 τ2,
      has_type Γ Σ e τ2 ->
      wf_ty Γ τ1 KType ->
      has_type Γ Σ (EInr τ1 e) (TSum τ1 τ2)
  | T_Case : forall Γ Σ e e1 e2 τ1 τ2 τ,
      has_type Γ Σ e (TSum τ1 τ2) ->
      has_type Γ Σ e1 (TArrow MUnrestricted τ1 TUnit τ) ->
      has_type Γ Σ e2 (TArrow MUnrestricted τ2 TUnit τ) ->
      has_type Γ Σ (ECase e e1 e2) τ
  (* References *)
  | T_Ref : forall Γ Σ e τ,
      has_type Γ Σ e τ ->
      has_type Γ Σ (ERef e) (TRef τ)
  | T_Deref : forall Γ Σ e τ,
      has_type Γ Σ e (TRef τ) ->
      has_type Γ Σ (EDeref e) τ
  | T_Assign : forall Γ Σ e1 e2 τ,
      has_type Γ Σ e1 (TRef τ) ->
      has_type Γ Σ e2 τ ->
      has_type Γ Σ (EAssign e1 e2) TUnit
  | T_Loc : forall Γ Σ l τ,
      ctx_wf Γ ->
      Σ l = Some τ ->
      has_type Γ Σ (ELoc l) (TRef τ)
  (* Control flow *)
  | T_If : forall Γ Σ e e1 e2 τ,
      has_type Γ Σ e TBool ->
      has_type Γ Σ e1 τ ->
      has_type Γ Σ e2 τ ->
      has_type Γ Σ (EIf e e1 e2) τ
  | T_Seq : forall Γ Σ e1 e2 τ,
      has_type Γ Σ e1 TUnit ->
      has_type Γ Σ e2 τ ->
      has_type Γ Σ (ESeq e1 e2) τ
  | T_Let : forall Γ Σ e1 e2 τ1 τ2 m,
      has_type Γ Σ e1 τ1 ->
      has_type (CE_Var τ1 m :: Γ) Σ e2 τ2 ->
      has_type Γ Σ (ELet e1 e2) τ2
  (* Recursive types *)
  | T_Fold : forall Γ Σ e τ,
      has_type Γ Σ e (ty_subst 0 (TRec τ) τ) ->
      has_type Γ Σ (EFold (TRec τ) e) (TRec τ)
  | T_Unfold : forall Γ Σ e τ,
      has_type Γ Σ e (TRec τ) ->
      has_type Γ Σ (EUnfold e) (ty_subst 0 (TRec τ) τ)
  (* Security types *)
  | T_Secret : forall Γ Σ e τ,
      has_type Γ Σ e τ ->
      has_type Γ Σ (ESecret e) (TSecret τ)
  | T_Declassify : forall Γ Σ e τ,
      has_type Γ Σ e (TSecret τ) ->
      has_type Γ Σ (EDeclassify e) τ
  (* Subsumption for labeled types *)
  | T_Sub : forall Γ Σ e τ1 τ2,
      has_type Γ Σ e τ1 ->
      subtype τ1 τ2 ->
      has_type Γ Σ e τ2

(** Type substitution in types *)
with ty_subst : nat -> ty -> ty -> ty := fun _ _ τ => τ

(** Subtyping relation *)
with subtype : ty -> ty -> Prop :=
  | sub_refl : forall τ, subtype τ τ
  | sub_trans : forall τ1 τ2 τ3,
      subtype τ1 τ2 ->
      subtype τ2 τ3 ->
      subtype τ1 τ3
  | sub_labeled_low_high : forall τ,
      subtype (TLabeled SL_Low τ) (TLabeled SL_High τ).

(* ============================================================================ *)
(*             SECTION 4: STEP-INDEXED LOGICAL RELATIONS (CORE)                 *)
(* ============================================================================ *)

(** Type depth for termination *)
Fixpoint type_depth (τ : ty) : nat :=
  match τ with
  | TUnit => 0
  | TBool => 0
  | TNat => 0
  | TInt => 0
  | TProd τ1 τ2 => S (max (type_depth τ1) (type_depth τ2))
  | TSum τ1 τ2 => S (max (type_depth τ1) (type_depth τ2))
  | TArrow _ τ1 _ τ2 => S (max (type_depth τ1) (type_depth τ2))
  | TRef τ => S (type_depth τ)
  | TSecret τ => S (type_depth τ)
  | TConstantTime τ => S (type_depth τ)
  | TSpeculationSafe τ => S (type_depth τ)
  | TSecretRef τ => S (type_depth τ)
  | TForall τ => S (type_depth τ)
  | TExists τ => S (type_depth τ)
  | TRec τ => S (type_depth τ)
  | TVar _ => 0
  | TLabeled _ τ => S (type_depth τ)
  end.

(** First-order type predicate *)
Fixpoint is_first_order (τ : ty) : bool :=
  match τ with
  | TUnit => true
  | TBool => true
  | TNat => true
  | TInt => true
  | TProd τ1 τ2 => is_first_order τ1 && is_first_order τ2
  | TSum τ1 τ2 => is_first_order τ1 && is_first_order τ2
  | TRef τ => is_first_order τ
  | TArrow _ _ _ _ => false
  | TForall _ => false
  | TExists _ => false
  | TRec _ => false
  | TSecret τ => is_first_order τ
  | TConstantTime τ => is_first_order τ
  | TSpeculationSafe τ => is_first_order τ
  | TSecretRef τ => is_first_order τ
  | TVar _ => false
  | TLabeled _ τ => is_first_order τ
  end.

(** Store relation type *)
Definition store_rel := store -> store_typing -> nat -> Prop.

(** Value relation at step n with store relation W *)
(** This is the CORE definition of the step-indexed logical relation *)

(** Base case for step 0: structural info without semantic content *)
Fixpoint val_rel_n_base (τ : ty) (v : expr) : Prop :=
  match τ with
  | TUnit => v = EUnit
  | TBool => exists b, v = EBool b
  | TNat => exists n, v = ENat n
  | TInt => exists z, v = EInt z
  | TProd τ1 τ2 =>
      exists v1 v2, v = EPair v1 v2 /\ 
                    is_value v1 /\ is_value v2
  | TSum τ1 τ2 =>
      (exists v', v = EInl τ2 v' /\ is_value v') \/
      (exists v', v = EInr τ1 v' /\ is_value v')
  | TArrow _ τ1 _ τ2 =>
      exists m τ' e, v = EAbs m τ' e
  | TRef τ =>
      exists l, v = ELoc l
  | TSecret τ =>
      exists v', v = ESecret v' /\ is_value v'
  | TForall τ =>
      exists e, v = ETAbs e
  | TRec τ =>
      exists v', v = EFold (TRec τ) v' /\ is_value v'
  | TLabeled _ τ => val_rel_n_base τ v
  | _ => is_value v
  end.

(** Value relation at step n for first-order types *)
Definition val_rel_at_type_fo (τ : ty) (v : expr) (σ : store) (Σ : store_typing) : Prop :=
  is_first_order τ = true /\ val_rel_n_base τ v.

(** MAIN DEFINITION: Step-indexed value relation *)
Fixpoint val_rel_n (n : nat) (τ : ty) (v : expr) (σ : store) (Σ : store_typing) 
         (W : store_rel) {struct n} : Prop :=
  is_value v /\
  match n with
  | 0 => val_rel_n_base τ v  (* THE STEP-0 FIX *)
  | S n' =>
    match τ with
    | TUnit => v = EUnit
    | TBool => exists b, v = EBool b
    | TNat => exists m, v = ENat m
    | TInt => exists z, v = EInt z
    | TProd τ1 τ2 =>
        exists v1 v2, 
          v = EPair v1 v2 /\
          val_rel_n n' τ1 v1 σ Σ W /\
          val_rel_n n' τ2 v2 σ Σ W
    | TSum τ1 τ2 =>
        (exists v', v = EInl τ2 v' /\ val_rel_n n' τ1 v' σ Σ W) \/
        (exists v', v = EInr τ1 v' /\ val_rel_n n' τ2 v' σ Σ W)
    | TArrow m τ1 ε τ2 =>
        exists m' τ' e,
          v = EAbs m' τ' e /\
          forall j v_arg σ' Σ',
            j < n' ->
            W σ' Σ' j ->
            val_rel_n j τ1 v_arg σ' Σ' W ->
            expr_rel_n j τ2 (subst 0 v_arg e) σ' Σ' W
    | TRef τ' =>
        exists l,
          v = ELoc l /\
          exists c, 
            store_lookup σ l = Some c /\
            cell_type c = τ' /\
            val_rel_n n' τ' (cell_value c) σ Σ W
    | TSecret τ' =>
        exists v',
          v = ESecret v' /\
          val_rel_n n' τ' v' σ Σ W
    | TConstantTime τ' =>
        exists v',
          v = v' /\
          val_rel_n n' τ' v' σ Σ W /\
          constant_time_value v'
    | TSpeculationSafe τ' =>
        exists v',
          v = v' /\
          val_rel_n n' τ' v' σ Σ W /\
          speculation_safe_value v'
    | TForall τ' =>
        exists e,
          v = ETAbs e /\
          forall τ'' j,
            j < n' ->
            wf_ty nil τ'' KType ->
            expr_rel_n j (ty_subst 0 τ'' τ') (tsubst 0 τ'' e) σ Σ W
    | TRec τ' =>
        exists v',
          v = EFold (TRec τ') v' /\
          val_rel_n n' (ty_subst 0 (TRec τ') τ') v' σ Σ W
    | TVar x => False  (* Open type variables don't have values *)
    | TLabeled l τ' =>
        val_rel_n n' τ' v σ Σ W
    | _ => is_value v
    end
  end

(** Expression relation at step n *)
with expr_rel_n (n : nat) (τ : ty) (e : expr) (σ : store) (Σ : store_typing) 
                (W : store_rel) {struct n} : Prop :=
  match n with
  | 0 => True  (* Step 0: vacuously true *)
  | S n' =>
      (* Safe to run for at least n steps *)
      forall j e' σ',
        j <= n' ->
        nsteps j (e, σ) (e', σ') ->
        (* Progress: either value or can step *)
        (is_value e' \/ exists e'' σ'', step (e', σ') (e'', σ'')) /\
        (* Preservation: if value, then in value relation *)
        (is_value e' -> 
         exists Σ',
           store_typing_extends Σ Σ' /\
           store_well_typed σ' Σ' /\
           val_rel_n (n' - j) τ e' σ' Σ' W)
  end

(** Store typing extension *)
with store_typing_extends (Σ1 Σ2 : store_typing) : Prop :=
  forall l τ, Σ1 l = Some τ -> Σ2 l = Some τ

(** Constant-time value (no secret-dependent branching) *)
with constant_time_value (v : expr) : Prop :=
  match v with
  | EUnit | EBool _ | ENat _ | EInt _ | ELoc _ => True
  | EPair v1 v2 => constant_time_value v1 /\ constant_time_value v2
  | EInl _ v' => constant_time_value v'
  | EInr _ v' => constant_time_value v'
  | EFold _ v' => constant_time_value v'
  | ESecret v' => constant_time_value v'
  | EAbs _ _ e => constant_time_expr e
  | ETAbs e => constant_time_expr e
  | _ => False
  end

(** Constant-time expression (no secret-dependent branching) *)
with constant_time_expr (e : expr) : Prop :=
  (* Simplified: actual impl checks for no secret-dependent control flow *)
  True

(** Speculation-safe value *)
with speculation_safe_value (v : expr) : Prop :=
  (* Value cannot be affected by speculative execution *)
  is_value v.

(* ============================================================================ *)
(*                  SECTION 5: STEP-UP AND STEP-DOWN LEMMAS                     *)
(* ============================================================================ *)

(** CRITICAL THEOREM: Step-up for first-order types *)
(** If we have the relation at step 0, we can step up to any n for FO types *)
Theorem val_rel_n_step_up_fo :
  forall τ n v σ Σ W,
    is_first_order τ = true ->
    val_rel_n 0 τ v σ Σ W ->
    val_rel_n n τ v σ Σ W.
Proof.
  induction τ; intros n v σ Σ W Hfo H0;
  try (simpl in Hfo; discriminate).
  - (* TUnit *)
    destruct n; simpl in *; auto.
    destruct H0; auto.
  - (* TBool *)
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    destruct H0 as [b Hb]; exists b; auto.
  - (* TNat *)
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    destruct H0 as [m Hm]; exists m; auto.
  - (* TInt *)
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    destruct H0 as [z Hz]; exists z; auto.
  - (* TProd *)
    simpl in Hfo.
    destruct (is_first_order τ1) eqn:Hfo1; try discriminate.
    destruct (is_first_order τ2) eqn:Hfo2; try discriminate.
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    destruct H0 as [v1 [v2 [Heq [Hv1 Hv2]]]].
    exists v1, v2.
    split; auto.
    split.
    + apply IHτ1; auto.
      simpl. split; auto.
    + apply IHτ2; auto.
      simpl. split; auto.
  - (* TSum *)
    simpl in Hfo.
    destruct (is_first_order τ1) eqn:Hfo1; try discriminate.
    destruct (is_first_order τ2) eqn:Hfo2; try discriminate.
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    destruct H0 as [[v' [Heq Hv']] | [v' [Heq Hv']]].
    + left. exists v'. split; auto.
      apply IHτ1; auto.
      simpl. split; auto.
    + right. exists v'. split; auto.
      apply IHτ2; auto.
      simpl. split; auto.
  - (* TRef *)
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    destruct H0 as [l Hl].
    exists l. split; auto.
    (* Need to handle reference cell *)
    admit. (* Requires store consistency *)
  - (* TSecret *)
    simpl in Hfo.
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    destruct H0 as [v' [Heq Hv']].
    exists v'. split; auto.
    apply IHτ; auto.
    simpl. split; auto.
  - (* TConstantTime *)
    simpl in Hfo.
    destruct n; simpl in *; auto.
  - (* TSpeculationSafe *)
    simpl in Hfo.
    destruct n; simpl in *; auto.
  - (* TSecretRef *)
    simpl in Hfo.
    destruct n; simpl in *; auto.
  - (* TLabeled *)
    simpl in Hfo.
    destruct n; simpl in *; auto.
    destruct H0 as [Hv H0].
    split; auto.
    apply IHτ; auto.
    simpl. split; auto.
Admitted.

(** Step-down lemma: relation at n implies relation at any m < n *)
Theorem val_rel_n_step_down :
  forall τ n m v σ Σ W,
    m <= n ->
    val_rel_n n τ v σ Σ W ->
    val_rel_n m τ v σ Σ W.
Proof.
  induction τ; intros n m v σ Σ W Hle Hn.
  - (* TUnit *)
    destruct n, m; simpl in *; auto.
    destruct Hn; auto.
  - (* TBool *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + destruct Hn as [Hv Hn]; split; auto.
  - (* TNat *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + destruct Hn as [Hv Hn]; split; auto.
  - (* TInt *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + destruct Hn as [Hv Hn]; split; auto.
  - (* TProd *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + lia.
    + destruct Hn as [Hv Hn].
      destruct Hn as [v1 [v2 [Heq [Hn1 Hn2]]]].
      split; auto.
      exists v1, v2.
      split; auto.
      split.
      * apply IHτ1 with (n := n); auto. lia.
      * apply IHτ2 with (n := n); auto. lia.
  - (* TSum - similar structure *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + lia.
    + destruct Hn as [Hv Hn].
      split; auto.
      destruct Hn as [[v' [Heq Hn']] | [v' [Heq Hn']]].
      * left. exists v'. split; auto.
        apply IHτ1 with (n := n); auto. lia.
      * right. exists v'. split; auto.
        apply IHτ2 with (n := n); auto. lia.
  - (* TArrow - contravariant in domain *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + lia.
    + destruct Hn as [Hv Hn].
      destruct Hn as [m' [τ' [e [Heq Hrel]]]].
      split; auto.
      exists m', τ', e.
      split; auto.
      intros j v_arg σ' Σ' Hj HW Harg.
      apply Hrel; auto.
      lia.
  - (* TRef *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + lia.
    + destruct Hn as [Hv Hn].
      destruct Hn as [l [Heq Hn']].
      split; auto.
      exists l. split; auto.
      destruct Hn' as [c [Hlook [Hty Hval]]].
      exists c. split; auto. split; auto.
      apply IHτ with (n := n); auto. lia.
  - (* TSecret *)
    destruct n, m; simpl in *; auto.
    + destruct Hn as [Hv Hn]; auto.
    + lia.
    + destruct Hn as [Hv Hn].
      destruct Hn as [v' [Heq Hn']].
      split; auto.
      exists v'. split; auto.
      apply IHτ with (n := n); auto. lia.
  - (* Other cases follow similar pattern *)
    all: destruct n, m; simpl in *; auto;
         try (destruct Hn as [Hv Hn]; auto);
         try lia.
Admitted.

(** Expression relation step-down *)
Theorem expr_rel_n_step_down :
  forall τ n m e σ Σ W,
    m <= n ->
    expr_rel_n n τ e σ Σ W ->
    expr_rel_n m τ e σ Σ W.
Proof.
  intros τ n m e σ Σ W Hle Hn.
  destruct m.
  - simpl. auto.
  - destruct n.
    + lia.
    + simpl in *.
      intros j e' σ' Hj Hsteps.
      assert (j <= n) as Hj' by lia.
      specialize (Hn j e' σ' Hj' Hsteps).
      destruct Hn as [Hprog Hpres].
      split; auto.
      intros Hval.
      specialize (Hpres Hval).
      destruct Hpres as [Σ' [Hext [Hwt Hvrel]]].
      exists Σ'.
      split; auto. split; auto.
      apply val_rel_n_step_down with (n := n - j); auto.
      lia.
Qed.

(* ============================================================================ *)
(*                 SECTION 6: FUNDAMENTAL THEOREM OF LOGICAL RELATIONS          *)
(* ============================================================================ *)

(** Semantic typing context *)
Definition sem_ctx := list (ty * mode).

(** Value environment *)
Definition val_env := list expr.

(** Environment well-formedness *)
Fixpoint env_rel_n (n : nat) (Γ : sem_ctx) (γ : val_env) 
                   (σ : store) (Σ : store_typing) (W : store_rel) : Prop :=
  match Γ, γ with
  | nil, nil => True
  | (τ, m) :: Γ', v :: γ' =>
      val_rel_n n τ v σ Σ W /\ env_rel_n n Γ' γ' σ Σ W
  | _, _ => False
  end.

(** Apply substitution from environment *)
Fixpoint subst_env (γ : val_env) (e : expr) : expr :=
  match γ with
  | nil => e
  | v :: γ' => subst_env γ' (subst 0 v e)
  end.

(** Convert typing context to semantic context *)
Fixpoint ctx_to_sem_ctx (Γ : context) : sem_ctx :=
  match Γ with
  | nil => nil
  | CE_Var τ m :: Γ' => (τ, m) :: ctx_to_sem_ctx Γ'
  | CE_TVar :: Γ' => ctx_to_sem_ctx Γ'  (* Skip type variables *)
  end.

(** Trivial store relation (for closed terms) *)
Definition trivial_store_rel : store_rel :=
  fun σ Σ n => store_well_typed σ Σ.

(** FUNDAMENTAL THEOREM *)
(** Well-typed terms are semantically well-behaved *)
Theorem fundamental :
  forall Γ Σ e τ,
    has_type Γ Σ e τ ->
    forall n γ σ,
      let Γ' := ctx_to_sem_ctx Γ in
      env_rel_n n Γ' γ σ Σ trivial_store_rel ->
      store_well_typed σ Σ ->
      expr_rel_n n τ (subst_env γ e) σ Σ trivial_store_rel.
Proof.
  intros Γ Σ e τ Hty.
  induction Hty; intros n γ σ Henv Hst.
  
  (* T_Unit *)
  - destruct n; simpl; auto.
    intros j e' σ' Hj Hsteps.
    split.
    + (* Progress *)
      inversion Hsteps; subst.
      * left. simpl. auto.
      * inversion H. (* Unit doesn't step *)
    + (* Preservation *)
      intros Hval.
      inversion Hsteps; subst.
      * exists Σ. split; [unfold store_typing_extends; auto | split; auto].
        simpl. split; auto.
      * inversion H.
  
  (* T_Bool *)
  - destruct n; simpl; auto.
    intros j e' σ' Hj Hsteps.
    split.
    + inversion Hsteps; subst.
      * left. simpl. exists b. reflexivity.
      * inversion H.
    + intros Hval.
      inversion Hsteps; subst.
      * exists Σ. split; [unfold store_typing_extends; auto | split; auto].
        simpl. split; [simpl; auto | exists b; auto].
      * inversion H.
  
  (* T_Nat *)
  - destruct n0; simpl; auto.
    intros j e' σ' Hj Hsteps.
    split.
    + inversion Hsteps; subst.
      * left. simpl. exists n. reflexivity.
      * inversion H.
    + intros Hval.
      inversion Hsteps; subst.
      * exists Σ. split; [unfold store_typing_extends; auto | split; auto].
        simpl. split; [simpl; auto | exists n; auto].
      * inversion H.
  
  (* T_Int *)
  - destruct n; simpl; auto.
    intros j e' σ' Hj Hsteps.
    split.
    + inversion Hsteps; subst.
      * left. simpl. exists z. reflexivity.
      * inversion H.
    + intros Hval.
      inversion Hsteps; subst.
      * exists Σ. split; [unfold store_typing_extends; auto | split; auto].
        simpl. split; [simpl; auto | exists z; auto].
      * inversion H.
  
  (* T_Var *)
  - (* Need to lookup in environment *)
    admit.
  
  (* T_Abs *)
  - destruct n; simpl; auto.
    intros j e' σ' Hj Hsteps.
    split.
    + inversion Hsteps; subst.
      * left. simpl. auto.
      * inversion H.
    + intros Hval.
      inversion Hsteps; subst.
      * exists Σ. split; [unfold store_typing_extends; auto | split; auto].
        simpl. split.
        -- simpl. auto.
        -- exists m, τ1, e.
           split; auto.
           intros j' v_arg σ'' Σ'' Hj' HW Harg.
           (* Use IH with extended environment *)
           admit.
      * inversion H.
  
  (* T_App *)
  - destruct n; simpl; auto.
    intros j e' σ' Hj Hsteps.
    (* Complex: need to track function and argument evaluation *)
    admit.
  
  (* Remaining cases follow similar structure *)
  all: admit.
Admitted.

(* ============================================================================ *)
(*                   SECTION 7: TYPE SAFETY COROLLARIES                         *)
(* ============================================================================ *)

(** Progress: well-typed closed terms are values or can step *)
Theorem progress :
  forall e τ Σ σ,
    has_type nil Σ e τ ->
    store_well_typed σ Σ ->
    is_value e \/ exists e' σ', step (e, σ) (e', σ').
Proof.
  intros e τ Σ σ Hty Hst.
  assert (expr_rel_n 1 τ e σ Σ trivial_store_rel) as Hrel.
  {
    apply fundamental with (γ := nil); auto.
    simpl. auto.
  }
  simpl in Hrel.
  specialize (Hrel 0 e σ).
  assert (0 <= 0) as H0 by lia.
  assert (nsteps 0 (e, σ) (e, σ)) as Hsteps by constructor.
  specialize (Hrel H0 Hsteps).
  destruct Hrel as [Hprog _].
  exact Hprog.
Qed.

(** Preservation: reduction preserves typing *)
Theorem preservation :
  forall Γ Σ e τ e' σ σ',
    has_type Γ Σ e τ ->
    store_well_typed σ Σ ->
    step (e, σ) (e', σ') ->
    exists Σ',
      store_typing_extends Σ Σ' /\
      store_well_typed σ' Σ' /\
      has_type Γ Σ' e' τ.
Proof.
  intros Γ Σ e τ e' σ σ' Hty Hst Hstep.
  (* Proof by induction on typing derivation *)
  induction Hty; inversion Hstep; subst.
  all: try (exists Σ; repeat split; auto).
  (* Handle allocation case *)
  all: admit.
Admitted.

(** Type safety: well-typed programs don't get stuck *)
Theorem type_safety :
  forall e τ σ σ' e' Σ n,
    has_type nil Σ e τ ->
    store_well_typed σ Σ ->
    nsteps n (e, σ) (e', σ') ->
    is_value e' \/ exists e'' σ'', step (e', σ') (e'', σ'').
Proof.
  intros e τ σ σ' e' Σ n Hty Hst Hsteps.
  induction Hsteps.
  - apply progress with (τ := τ) (Σ := Σ); auto.
  - assert (exists Σ', store_typing_extends Σ Σ' /\
                       store_well_typed σ2 Σ' /\
                       has_type nil Σ' e2 τ) as [Σ' [Hext [Hst' Hty']]].
    { apply preservation with (e := e1) (σ := σ1); auto. }
    apply IHHsteps with (Σ := Σ'); auto.
Qed.

(* ============================================================================ *)
(*                   SECTION 8: NON-INTERFERENCE                                *)
(* ============================================================================ *)

(** Low-equivalence of stores *)
Definition store_low_equiv (σ1 σ2 : store) : Prop :=
  forall l c1 c2,
    store_lookup σ1 l = Some c1 ->
    store_lookup σ2 l = Some c2 ->
    cell_sec_level c1 = Low ->
    cell_sec_level c2 = Low ->
    cell_value c1 = cell_value c2.

(** Low-equivalence of values at type τ *)
Fixpoint val_low_equiv (τ : ty) (v1 v2 : expr) : Prop :=
  match τ with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => v1 = v2
  | TNat => v1 = v2
  | TInt => v1 = v2
  | TProd τ1 τ2 =>
      exists v1a v1b v2a v2b,
        v1 = EPair v1a v1b /\
        v2 = EPair v2a v2b /\
        val_low_equiv τ1 v1a v2a /\
        val_low_equiv τ2 v1b v2b
  | TSum τ1 τ2 =>
      (exists v1' v2', v1 = EInl τ2 v1' /\ v2 = EInl τ2 v2' /\ val_low_equiv τ1 v1' v2') \/
      (exists v1' v2', v1 = EInr τ1 v1' /\ v2 = EInr τ1 v2' /\ val_low_equiv τ2 v1' v2')
  | TArrow _ τ1 _ τ2 =>
      (* Functions are low-equivalent if they produce low-equivalent results
         on low-equivalent inputs *)
      True  (* Simplified; full version uses logical relation *)
  | TRef τ' =>
      (* References are low-equivalent if they point to low-equivalent values *)
      exists l1 l2, v1 = ELoc l1 /\ v2 = ELoc l2 (* Must track via store *)
  | TSecret τ' =>
      (* Secret values are always low-equivalent (opaque) *)
      True
  | TLabeled SL_Low τ' => val_low_equiv τ' v1 v2
  | TLabeled SL_High τ' => True  (* High values always equivalent *)
  | _ => True
  end.

(** Step-indexed non-interference relation *)
Fixpoint ni_rel_n (n : nat) (τ : ty) (e1 e2 : expr) 
                  (σ1 σ2 : store) (Σ : store_typing) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      forall j e1' e2' σ1' σ2',
        j <= n' ->
        nsteps j (e1, σ1) (e1', σ1') ->
        nsteps j (e2, σ2) (e2', σ2') ->
        (* Both terminate to low-equivalent values *)
        (is_value e1' /\ is_value e2' -> val_low_equiv τ e1' e2') /\
        (* Or both can step further *)
        ((exists e1'' σ1'', step (e1', σ1') (e1'', σ1'')) <->
         (exists e2'' σ2'', step (e2', σ2') (e2'', σ2'')))
  end.

(** TERMINATION-INSENSITIVE NON-INTERFERENCE (TINI) *)
Theorem tini :
  forall Γ Σ e τ,
    has_type Γ Σ e (TLabeled SL_Low τ) ->
    forall σ1 σ2 γ1 γ2,
      store_low_equiv σ1 σ2 ->
      env_low_equiv (ctx_to_sem_ctx Γ) γ1 γ2 ->
      forall n,
        ni_rel_n n τ (subst_env γ1 e) (subst_env γ2 e) σ1 σ2 Σ
with env_low_equiv : sem_ctx -> val_env -> val_env -> Prop :=
  fun Γ γ1 γ2 =>
    match Γ, γ1, γ2 with
    | nil, nil, nil => True
    | (τ, _) :: Γ', v1 :: γ1', v2 :: γ2' =>
        val_low_equiv τ v1 v2 /\ env_low_equiv Γ' γ1' γ2'
    | _, _, _ => False
    end.
Proof.
  intros Γ Σ e τ Hty σ1 σ2 γ1 γ2 Hst Henv n.
  induction n.
  - simpl. auto.
  - simpl.
    intros j e1' e2' σ1' σ2' Hj Hsteps1 Hsteps2.
    split.
    + (* Low-equivalence preservation *)
      intros [Hval1 Hval2].
      (* Use fundamental theorem and semantic typing *)
      admit.
    + (* Step equivalence *)
      split; intros [e'' [σ'' Hstep]].
      * (* Left steps implies right steps *)
        admit.
      * (* Right steps implies left steps *)
        admit.
Admitted.

(** TERMINATION-SENSITIVE NON-INTERFERENCE (TSNI) *)
(** Stronger property: also preserve termination behavior *)
Theorem tsni :
  forall Γ Σ e τ,
    has_type Γ Σ e (TLabeled SL_Low τ) ->
    (* Additional totality constraint on e *)
    (forall σ γ, exists v σ', (subst_env γ e, σ) -->* (v, σ') /\ is_value v) ->
    forall σ1 σ2 γ1 γ2,
      store_low_equiv σ1 σ2 ->
      env_low_equiv (ctx_to_sem_ctx Γ) γ1 γ2 ->
      forall n,
        ni_rel_n n τ (subst_env γ1 e) (subst_env γ2 e) σ1 σ2 Σ /\
        (* Termination equivalence *)
        (exists v1 σ1' v2 σ2',
          (subst_env γ1 e, σ1) -->* (v1, σ1') /\
          (subst_env γ2 e, σ2) -->* (v2, σ2') /\
          is_value v1 /\ is_value v2 /\
          val_low_equiv τ v1 v2).
Proof.
  intros Γ Σ e τ Hty Htot σ1 σ2 γ1 γ2 Hst Henv n.
  split.
  - apply tini; auto.
  - (* Use totality and fundamental theorem *)
    destruct (Htot σ1 γ1) as [v1 [σ1' [Hsteps1 Hval1]]].
    destruct (Htot σ2 γ2) as [v2 [σ2' [Hsteps2 Hval2]]].
    exists v1, σ1', v2, σ2'.
    repeat split; auto.
    (* Prove val_low_equiv using NI *)
    admit.
Admitted.

(* ============================================================================ *)
(*               SECTION 9: CONSTANT-TIME SECURITY                              *)
(* ============================================================================ *)

(** Execution trace *)
Inductive trace_event : Type :=
  | TE_Read : nat -> trace_event   (* Memory read at location *)
  | TE_Write : nat -> trace_event  (* Memory write at location *)
  | TE_Branch : bool -> trace_event. (* Branch taken/not-taken *)

Definition trace := list trace_event.

(** Instrumented step that records trace *)
Inductive step_trace : expr * store -> expr * store * trace_event -> Prop :=
  | step_trace_deref : forall l c σ,
      store_lookup σ l = Some c ->
      step_trace (EDeref (ELoc l), σ) (cell_value c, σ, TE_Read l)
  | step_trace_assign : forall l v c σ,
      is_value v ->
      store_lookup σ l = Some c ->
      step_trace (EAssign (ELoc l) v, σ) 
                 (EUnit, store_update σ l (mk_cell v (cell_type c) (cell_sec_level c)), 
                  TE_Write l)
  | step_trace_if_true : forall e1 e2 σ,
      step_trace (EIf (EBool true) e1 e2, σ) (e1, σ, TE_Branch true)
  | step_trace_if_false : forall e1 e2 σ,
      step_trace (EIf (EBool false) e1 e2, σ) (e2, σ, TE_Branch false).
  (* ... other cases produce empty trace events *)

(** Multi-step with trace accumulation *)
Inductive multi_step_trace : expr * store -> expr * store * trace -> Prop :=
  | mst_refl : forall e σ, multi_step_trace (e, σ) (e, σ, nil)
  | mst_step : forall e1 σ1 e2 σ2 te e3 σ3 t,
      step_trace (e1, σ1) (e2, σ2, te) ->
      multi_step_trace (e2, σ2) (e3, σ3, t) ->
      multi_step_trace (e1, σ1) (e3, σ3, te :: t).

(** CONSTANT-TIME THEOREM *)
(** Well-typed constant-time expressions have identical traces on 
    low-equivalent inputs *)
Theorem constant_time_security :
  forall Γ Σ e τ,
    has_type Γ Σ e (TConstantTime τ) ->
    forall σ1 σ2 γ1 γ2 v1 v2 σ1' σ2' t1 t2,
      store_low_equiv σ1 σ2 ->
      env_low_equiv (ctx_to_sem_ctx Γ) γ1 γ2 ->
      multi_step_trace (subst_env γ1 e, σ1) (v1, σ1', t1) ->
      multi_step_trace (subst_env γ2 e, σ2) (v2, σ2', t2) ->
      is_value v1 ->
      is_value v2 ->
      t1 = t2.  (* Traces are identical *)
Proof.
  intros Γ Σ e τ Hty σ1 σ2 γ1 γ2 v1 v2 σ1' σ2' t1 t2 
         Hst Henv Hsteps1 Hsteps2 Hval1 Hval2.
  (* Proof by induction on execution trace *)
  (* Key insight: TConstantTime types forbid secret-dependent branches *)
  generalize dependent t2.
  generalize dependent v2.
  generalize dependent σ2'.
  generalize dependent σ2.
  induction Hsteps1; intros.
  - (* Base case: no steps *)
    inversion Hsteps2; subst.
    + reflexivity.
    + (* Contradiction: one terminates, other doesn't *)
      admit.
  - (* Step case *)
    inversion Hsteps2; subst.
    + (* Contradiction *)
      admit.
    + (* Both take a step *)
      assert (te = te0) as Heq_te.
      {
        (* Trace events must match due to constant-time typing *)
        admit.
      }
      subst te0.
      f_equal.
      apply IHHsteps1 with (σ2 := σ4); auto.
      * (* Store equivalence preserved *)
        admit.
Admitted.

(* ============================================================================ *)
(*               SECTION 10: SPECULATION SAFETY                                 *)
(* ============================================================================ *)

(** Speculative execution state *)
Inductive spec_state : Type :=
  | SS_Normal : spec_state
  | SS_Speculating : nat -> spec_state.  (* Speculation depth *)

(** Speculative step relation *)
Inductive spec_step : spec_state * expr * store -> 
                      spec_state * expr * store -> Prop :=
  | spec_step_normal : forall e σ e' σ',
      step (e, σ) (e', σ') ->
      spec_step (SS_Normal, e, σ) (SS_Normal, e', σ')
  | spec_step_branch_spec : forall e1 e2 σ n,
      (* Speculative execution of both branches *)
      spec_step (SS_Normal, EIf (EBool true) e1 e2, σ) 
                (SS_Speculating n, e1, σ).

(** SPECULATION SAFETY THEOREM *)
(** SpeculationSafe types cannot leak secrets through speculative execution *)
Theorem speculation_safe :
  forall Γ Σ e τ,
    has_type Γ Σ e (TSpeculationSafe τ) ->
    forall σ1 σ2 γ,
      store_low_equiv σ1 σ2 ->
      forall ss v1 v2 σ1' σ2',
        spec_step (ss, subst_env γ e, σ1) (SS_Normal, v1, σ1') ->
        spec_step (ss, subst_env γ e, σ2) (SS_Normal, v2, σ2') ->
        is_value v1 ->
        is_value v2 ->
        (* Observable behavior is identical *)
        store_low_equiv σ1' σ2'.
Proof.
  (* Proof shows that speculation-safe code doesn't create
     observable side effects that depend on secrets *)
  admit.
Admitted.

(* ============================================================================ *)
(*               SECTION 11: EFFECT SYSTEM SOUNDNESS                            *)
(* ============================================================================ *)

(** Effect labels *)
Inductive effect_label : Type :=
  | Eff_Pure : effect_label
  | Eff_Read : effect_label
  | Eff_Write : effect_label
  | Eff_Alloc : effect_label
  | Eff_IO : effect_label
  | Eff_Exn : effect_label
  | Eff_Div : effect_label.  (* Divergence *)

(** Effect row (set of effects) *)
Definition effect_row := list effect_label.

Definition effect_empty : effect_row := nil.

Definition effect_sub (ε1 ε2 : effect_row) : Prop :=
  forall e, In e ε1 -> In e ε2.

(** Effect-annotated typing *)
Inductive has_type_eff : context -> store_typing -> expr -> ty -> effect_row -> Prop :=
  | TE_Pure : forall Γ Σ e τ,
      has_type Γ Σ e τ ->
      (* Pure expressions have no effects *)
      (forall σ σ' e', step (e, σ) (e', σ') -> σ = σ') ->
      has_type_eff Γ Σ e τ effect_empty
  | TE_Read : forall Γ Σ e τ,
      has_type Γ Σ e (TRef τ) ->
      has_type_eff Γ Σ (EDeref e) τ [Eff_Read]
  | TE_Write : forall Γ Σ e1 e2 τ,
      has_type Γ Σ e1 (TRef τ) ->
      has_type Γ Σ e2 τ ->
      has_type_eff Γ Σ (EAssign e1 e2) TUnit [Eff_Write]
  | TE_Alloc : forall Γ Σ e τ,
      has_type Γ Σ e τ ->
      has_type_eff Γ Σ (ERef e) (TRef τ) [Eff_Alloc]
  | TE_Sub : forall Γ Σ e τ ε1 ε2,
      has_type_eff Γ Σ e τ ε1 ->
      effect_sub ε1 ε2 ->
      has_type_eff Γ Σ e τ ε2.

(** EFFECT SOUNDNESS *)
(** Declared effects bound actual effects *)
Theorem effect_soundness :
  forall Γ Σ e τ ε σ σ' e',
    has_type_eff Γ Σ e τ ε ->
    store_well_typed σ Σ ->
    step (e, σ) (e', σ') ->
    (* The step respects declared effects *)
    (σ = σ' \/ In Eff_Write ε \/ In Eff_Alloc ε) /\
    (* If no write/alloc effects, store unchanged *)
    (~ In Eff_Write ε /\ ~ In Eff_Alloc ε -> σ = σ').
Proof.
  intros Γ Σ e τ ε σ σ' e' Hty Hst Hstep.
  induction Hty.
  - (* Pure *)
    split.
    + left. apply H0; auto.
    + intros _. apply H0; auto.
  - (* Read *)
    split.
    + left.
      inversion Hstep; subst; auto.
      (* Deref doesn't change store *)
      admit.
    + intros _. 
      inversion Hstep; subst; auto.
      admit.
  - (* Write *)
    split.
    + right. left. simpl. auto.
    + intros [Hnw _]. simpl in Hnw. exfalso. apply Hnw. auto.
  - (* Alloc *)
    split.
    + right. right. simpl. auto.
    + intros [_ Hna]. simpl in Hna. exfalso. apply Hna. auto.
  - (* Subsumption *)
    destruct IHHty as [Heff1 Heff2]; auto.
    split.
    + destruct Heff1 as [Heq | [Hw | Ha]].
      * left; auto.
      * right. left. apply H; auto.
      * right. right. apply H; auto.
    + intros [Hnw Hna].
      apply Heff2.
      split; intros Hin; [apply Hnw | apply Hna]; apply H; auto.
Admitted.

(* ============================================================================ *)
(*               SECTION 12: LINEAR TYPE SOUNDNESS                              *)
(* ============================================================================ *)

(** Use counting for linear resources *)
Fixpoint use_count (x : nat) (e : expr) : nat :=
  match e with
  | EVar y => if Nat.eqb x y then 1 else 0
  | EAbs _ _ e' => use_count (S x) e'
  | EApp e1 e2 => use_count x e1 + use_count x e2
  | ETAbs e' => use_count x e'
  | ETApp e' _ => use_count x e'
  | EPair e1 e2 => use_count x e1 + use_count x e2
  | EFst e' => use_count x e'
  | ESnd e' => use_count x e'
  | EInl _ e' => use_count x e'
  | EInr _ e' => use_count x e'
  | ECase e' e1 e2 => use_count x e' + use_count x e1 + use_count x e2
  | ERef e' => use_count x e'
  | EDeref e' => use_count x e'
  | EAssign e1 e2 => use_count x e1 + use_count x e2
  | ESeq e1 e2 => use_count x e1 + use_count x e2
  | ELet e1 e2 => use_count x e1 + use_count (S x) e2
  | EIf e' e1 e2 => use_count x e' + use_count x e1 + use_count x e2
  | EFix e' => use_count x e'
  | EFold _ e' => use_count x e'
  | EUnfold e' => use_count x e'
  | ESecret e' => use_count x e'
  | EDeclassify e' => use_count x e'
  | ESanitize e' => use_count x e'
  | EDrop e' => use_count x e'
  | ELetRec _ e1 e2 => use_count (S x) e1 + use_count (S x) e2
  | _ => 0
  end.

(** Linear use constraint *)
Definition linear_use (x : nat) (e : expr) : Prop :=
  use_count x e = 1.

(** Affine use constraint *)
Definition affine_use (x : nat) (e : expr) : Prop :=
  use_count x e <= 1.

(** LINEAR TYPE SOUNDNESS *)
(** Linear variables are used exactly once *)
Theorem linear_soundness :
  forall Γ Σ e τ x τ_x,
    has_type (CE_Var τ_x MLinear :: Γ) Σ e τ ->
    linear_use 0 e.
Proof.
  intros Γ Σ e τ x τ_x Hty.
  (* Proof by induction on typing derivation *)
  (* Key: MLinear mode forces exactly-once usage *)
  induction Hty.
  all: unfold linear_use; simpl.
  all: try lia.
  all: admit.
Admitted.

(** AFFINE SOUNDNESS *)
(** Affine variables are used at most once *)
Theorem affine_soundness :
  forall Γ Σ e τ x τ_x,
    has_type (CE_Var τ_x MAffine :: Γ) Σ e τ ->
    affine_use 0 e.
Proof.
  intros Γ Σ e τ x τ_x Hty.
  (* Similar to linear, but allows 0 uses *)
  induction Hty.
  all: unfold affine_use; simpl.
  all: try lia.
  all: admit.
Admitted.

(* ============================================================================ *)
(*                    SECTION 13: COMPLETE SECURITY THEOREM                     *)
(* ============================================================================ *)

(** Combined security guarantee *)
Theorem complete_security :
  forall Γ Σ e τ,
    (* Well-typed with all security features *)
    has_type Γ Σ e τ ->
    (* Type safety *)
    (forall σ σ' e' n,
      store_well_typed σ Σ ->
      nsteps n (e, σ) (e', σ') ->
      is_value e' \/ exists e'' σ'', step (e', σ') (e'', σ'')) /\
    (* Non-interference for labeled types *)
    (forall l τ',
      τ = TLabeled l τ' ->
      l = SL_Low ->
      forall σ1 σ2 γ1 γ2 n,
        store_low_equiv σ1 σ2 ->
        env_low_equiv (ctx_to_sem_ctx Γ) γ1 γ2 ->
        ni_rel_n n τ' (subst_env γ1 e) (subst_env γ2 e) σ1 σ2 Σ) /\
    (* Constant-time for CT types *)
    (forall τ',
      τ = TConstantTime τ' ->
      forall σ1 σ2 γ1 γ2 v1 v2 σ1' σ2' t1 t2,
        store_low_equiv σ1 σ2 ->
        env_low_equiv (ctx_to_sem_ctx Γ) γ1 γ2 ->
        multi_step_trace (subst_env γ1 e, σ1) (v1, σ1', t1) ->
        multi_step_trace (subst_env γ2 e, σ2) (v2, σ2', t2) ->
        is_value v1 -> is_value v2 ->
        t1 = t2).
Proof.
  intros Γ Σ e τ Hty.
  split; [| split].
  - (* Type safety *)
    intros σ σ' e' n Hst Hsteps.
    apply type_safety with (τ := τ) (Σ := Σ); auto.
  - (* Non-interference *)
    intros l τ' Heq Hlow σ1 σ2 γ1 γ2 n Hst Henv.
    subst τ l.
    apply tini; auto.
    (* Need typing for labeled type *)
    admit.
  - (* Constant-time *)
    intros τ' Heq σ1 σ2 γ1 γ2 v1 v2 σ1' σ2' t1 t2 Hst Henv Hs1 Hs2 Hv1 Hv2.
    subst τ.
    apply constant_time_security with (Γ := Γ) (Σ := Σ) (τ := τ'); auto.
    (* Need typing for CT type *)
    admit.
Admitted.

(* ============================================================================ *)
(*                          END OF REDUCIBILITY FULL                            *)
(* ============================================================================ *)

(** Final verification that all key theorems are stated *)
Check val_rel_n_step_up_fo.
Check val_rel_n_step_down.
Check expr_rel_n_step_down.
Check fundamental.
Check progress.
Check preservation.
Check type_safety.
Check tini.
Check tsni.
Check constant_time_security.
Check speculation_safe.
Check effect_soundness.
Check linear_soundness.
Check affine_soundness.
Check complete_security.

(** NOTES FOR CLAUDE CODE IMPLEMENTATION:
   
   1. The Admitted proofs require completion. Priority order:
      a. val_rel_n_step_up_fo (critical for step-indexed approach)
      b. fundamental (the main theorem)
      c. type_safety (combines progress + preservation)
      d. tini/tsni (non-interference)
      e. constant_time_security (CT guarantees)
   
   2. Key proof techniques needed:
      - Induction on step index n
      - Induction on type structure
      - Induction on typing derivation
      - Lexicographic induction for mutual recursion
   
   3. The subst and tsubst functions need proper implementation
      with de Bruijn indices.
   
   4. Store operations need refinement for proper memory model.
   
   5. The effect system integration requires the effect_row type
      to align with TERAS-LANG D40 specification.
*)
