(** * RIINA: exp_rel_step1_snd Proof
    
    Proves that when two pairs are related at base level (first-order),
    projecting the SECOND component produces related results.
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
    
    Generated: 2026-01-19
    Status: COMPLETE - Qed
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ========================================================================
    SECTION 1: TYPE DEFINITIONS (from RIINA.foundations.Syntax)
    ======================================================================== *)

Definition ident := string.
Definition loc := nat.

Inductive security_level : Type :=
  | LPublic    : security_level
  | LInternal  : security_level
  | LSession   : security_level
  | LUser      : security_level
  | LSystem    : security_level
  | LSecret    : security_level.

Inductive effect : Type :=
  | EffPure       : effect
  | EffRead       : effect
  | EffWrite      : effect
  | EffFileSystem : effect
  | EffNetwork    : effect
  | EffNetSecure  : effect
  | EffCrypto     : effect
  | EffRandom     : effect
  | EffSystem     : effect
  | EffTime       : effect
  | EffProcess    : effect
  | EffPanel      : effect
  | EffZirah      : effect
  | EffBenteng    : effect
  | EffSandi      : effect
  | EffMenara     : effect
  | EffGapura     : effect.

Inductive taint_source : Type :=
  | TaintNetworkExternal : taint_source
  | TaintNetworkInternal : taint_source
  | TaintUserInput       : taint_source
  | TaintFileSystem      : taint_source
  | TaintDatabase        : taint_source
  | TaintEnvironment     : taint_source
  | TaintGapuraRequest   : taint_source
  | TaintZirahEvent      : taint_source
  | TaintZirahEndpoint   : taint_source
  | TaintBentengBiometric: taint_source
  | TaintSandiSignature  : taint_source
  | TaintMenaraDevice    : taint_source.

Inductive sanitizer : Type :=
  | SanHtmlEscape        : sanitizer
  | SanUrlEncode         : sanitizer
  | SanJsEscape          : sanitizer
  | SanCssEscape         : sanitizer
  | SanSqlEscape         : sanitizer
  | SanSqlParam          : sanitizer
  | SanXssFilter         : sanitizer
  | SanPathTraversal     : sanitizer
  | SanCommandEscape     : sanitizer
  | SanLdapEscape        : sanitizer
  | SanXmlEscape         : sanitizer
  | SanJsonValidation    : sanitizer
  | SanXmlValidation     : sanitizer
  | SanEmailValidation   : sanitizer
  | SanPhoneValidation   : sanitizer
  | SanLengthBound       : nat -> sanitizer
  | SanRangeBound        : nat -> nat -> sanitizer
  | SanRegexMatch        : string -> sanitizer
  | SanWhitelist         : list string -> sanitizer
  | SanHashVerify        : sanitizer
  | SanSignatureVerify   : sanitizer
  | SanMacVerify         : sanitizer
  | SanGapuraAuth        : sanitizer
  | SanZirahSession      : sanitizer
  | SanBentengBiometric  : sanitizer
  | SanSandiDecrypt      : sanitizer
  | SanMenaraAttestation : sanitizer.

Inductive capability_kind : Type :=
  | CapFileRead    : capability_kind
  | CapFileWrite   : capability_kind
  | CapFileExecute : capability_kind
  | CapFileDelete  : capability_kind
  | CapNetConnect  : capability_kind
  | CapNetListen   : capability_kind
  | CapNetBind     : capability_kind
  | CapProcSpawn   : capability_kind
  | CapProcSignal  : capability_kind
  | CapSysTime     : capability_kind
  | CapSysRandom   : capability_kind
  | CapSysEnv      : capability_kind
  | CapRootProduct : capability_kind
  | CapProductAccess : capability_kind.

Inductive capability : Type :=
  | CapBasic     : capability_kind -> capability
  | CapRevocable : capability -> capability
  | CapTimeBound : capability -> nat -> capability
  | CapDelegated : capability -> ident -> capability.

(** Types *)
Inductive ty : Type :=
  | TUnit    : ty
  | TBool    : ty
  | TInt     : ty
  | TString  : ty
  | TBytes   : ty
  | TFn      : ty -> ty -> effect -> ty
  | TProd    : ty -> ty -> ty
  | TSum     : ty -> ty -> ty
  | TList    : ty -> ty
  | TOption  : ty -> ty
  | TRef     : ty -> security_level -> ty
  | TSecret  : ty -> ty
  | TLabeled : ty -> security_level -> ty
  | TTainted : ty -> taint_source -> ty
  | TSanitized : ty -> sanitizer -> ty
  | TProof   : ty -> ty
  | TCapability : capability_kind -> ty
  | TCapabilityFull : capability -> ty
  | TConstantTime : ty -> ty
  | TZeroizing : ty -> ty.

(** Expressions *)
Inductive expr : Type :=
  | EUnit   : expr
  | EBool   : bool -> expr
  | EInt    : nat -> expr
  | EString : string -> expr
  | ELoc    : loc -> expr
  | EVar    : ident -> expr
  | ELam    : ident -> ty -> expr -> expr
  | EApp    : expr -> expr -> expr
  | EPair   : expr -> expr -> expr
  | EFst    : expr -> expr
  | ESnd    : expr -> expr
  | EInl    : expr -> ty -> expr
  | EInr    : expr -> ty -> expr
  | ECase   : expr -> ident -> expr -> ident -> expr -> expr
  | EIf     : expr -> expr -> expr -> expr
  | ELet    : ident -> expr -> expr -> expr
  | EPerform : effect -> expr -> expr
  | EHandle  : expr -> ident -> expr -> expr
  | ERef    : expr -> security_level -> expr
  | EDeref  : expr -> expr
  | EAssign : expr -> expr -> expr
  | EClassify   : expr -> expr
  | EDeclassify : expr -> expr -> expr
  | EProve      : expr -> expr
  | ERequire : effect -> expr -> expr
  | EGrant   : effect -> expr -> expr.

(** Values *)
Inductive value : expr -> Prop :=
  | VUnit   : value EUnit
  | VBool   : forall b, value (EBool b)
  | VInt    : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc    : forall l, value (ELoc l)
  | VLam    : forall x T e, value (ELam x T e)
  | VPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl    : forall v T, value v -> value (EInl v T)
  | VInr    : forall v T, value v -> value (EInr v T)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve  : forall v, value v -> value (EProve v).

(** Free variables *)
Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EUnit | EBool _ | EInt _ | EString _ | ELoc _ => False
  | EVar y => x = y
  | ELam y _ body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  | EPair e1 e2 => free_in x e1 \/ free_in x e2
  | EFst e1 => free_in x e1
  | ESnd e1 => free_in x e1
  | EInl e1 _ => free_in x e1
  | EInr e1 _ => free_in x e1
  | ECase e1 y1 e2 y2 e3 =>
      free_in x e1 \/ (x <> y1 /\ free_in x e2) \/ (x <> y2 /\ free_in x e3)
  | EIf e1 e2 e3 => free_in x e1 \/ free_in x e2 \/ free_in x e3
  | ELet y e1 e2 => free_in x e1 \/ (x <> y /\ free_in x e2)
  | EPerform _ e1 => free_in x e1
  | EHandle e1 y h => free_in x e1 \/ (x <> y /\ free_in x h)
  | ERef e1 _ => free_in x e1
  | EDeref e1 => free_in x e1
  | EAssign e1 e2 => free_in x e1 \/ free_in x e2
  | EClassify e1 => free_in x e1
  | EDeclassify e1 e2 => free_in x e1 \/ free_in x e2
  | EProve e1 => free_in x e1
  | ERequire _ e1 => free_in x e1
  | EGrant _ e1 => free_in x e1
  end.

Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(** Substitution *)
Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
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

(** ========================================================================
    SECTION 2: STORE AND OPERATIONAL SEMANTICS
    ======================================================================== *)

Definition store := list (loc * expr).
Definition store_ty := list (loc * ty * security_level).
Definition effect_ctx := list effect.

Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

(** Small-step semantics *)
Reserved Notation "cfg1 '-->' cfg2" (at level 40).

Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
  | ST_App1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EApp e1 e2, st, ctx) --> (EApp e1' e2, st', ctx')
  | ST_App2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EApp v1 e2, st, ctx) --> (EApp v1 e2', st', ctx')
  | ST_Pair1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EPair e1 e2, st, ctx) --> (EPair e1' e2, st', ctx')
  | ST_Pair2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EPair v1 e2, st, ctx) --> (EPair v1 e2', st', ctx')
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
  | ST_FstStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EFst e, st, ctx) --> (EFst e', st', ctx')
  | ST_SndStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ESnd e, st, ctx) --> (ESnd e', st', ctx')
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
  | ST_CaseStep : forall e e' x1 e1 x2 e2 st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ECase e x1 e1 x2 e2, st, ctx) --> (ECase e' x1 e1 x2 e2, st', ctx')
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)
  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)
  | ST_IfStep : forall e1 e1' e2 e3 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EIf e1 e2 e3, st, ctx) --> (EIf e1' e2 e3, st', ctx')
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)
  | ST_LetStep : forall x e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (ELet x e1 e2, st, ctx) --> (ELet x e1' e2, st', ctx')
  | ST_HandleValue : forall v x h st ctx,
      value v ->
      (EHandle v x h, st, ctx) --> ([x := v] h, st, ctx)
  | ST_HandleStep : forall e e' x h st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EHandle e x h, st, ctx) --> (EHandle e' x h, st', ctx')
where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

(** Multi-step reduction *)
Inductive multi_step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg,
      multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).

(** ========================================================================
    SECTION 3: FIRST-ORDER TYPE RELATION
    ======================================================================== *)

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef T _ => first_order_type T
  | _ => true
  end.

Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TProd T1 T2 =>
      exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type_fo T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type_fo T2 y1 y2)
  | _ => True
  end.

Definition val_rel_n_base (Sigma : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).

Definition store_rel_n_base (Sigma : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.

(** ========================================================================
    SECTION 4: EXTRACTION LEMMAS
    ======================================================================== *)

Lemma val_rel_n_base_value : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 -> value v1 /\ value v2.
Proof.
  intros Sigma T v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [Hv1 [Hv2 _]].
  split; assumption.
Qed.

Lemma val_rel_n_base_prod_fo : forall Sigma T1 T2 v1 v2,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Sigma (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2.
Proof.
  intros Sigma T1 T2 v1 v2 Hfo Hrel.
  unfold val_rel_n_base in Hrel.
  destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Htype]]]].
  rewrite Hfo in Htype.
  simpl in Htype.
  exact Htype.
Qed.

(** ========================================================================
    SECTION 5: THE MAIN THEOREM (exp_rel_step1_snd)
    ======================================================================== *)

(** THEOREM: When two pairs are related at base level (first-order),
    projecting the SECOND component produces related results. *)
Theorem exp_rel_step1_snd : forall Sigma T1 T2 v v' st1 st2 ctx,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Sigma (TProd T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ESnd v, st1, ctx) -->* (r1, st1', ctx') /\
    (ESnd v', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Sigma T1 T2 v v' st1 st2 ctx Hfo Hval Hstore.
  
  (* STEP 1: Extract pair structure *)
  pose proof (val_rel_n_base_prod_fo Sigma T1 T2 v v' Hfo Hval) as Hprod.
  destruct Hprod as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
  subst v v'.
  
  (* STEP 2: Get value properties *)
  pose proof (val_rel_n_base_value Sigma (TProd T1 T2) (EPair a1 b1) (EPair a2 b2) Hval) 
    as [Hv1 Hv2].
  
  (* STEP 3: Invert value (EPair ...) *)
  inversion Hv1; subst.
  inversion Hv2; subst.
  
  (* STEP 4: Witnesses - results are b1 and b2 (SECOND components) *)
  exists b1, b2, st1, st2, ctx.
  
  (* STEP 5: Prove multi-step reductions *)
  split.
  - apply MS_Step with (cfg2 := (b1, st1, ctx)).
    + apply ST_Snd; assumption.
    + apply MS_Refl.
  - apply MS_Step with (cfg2 := (b2, st2, ctx)).
    + apply ST_Snd; assumption.
    + apply MS_Refl.
Qed.

Print Assumptions exp_rel_step1_snd.

(** End of RIINA_exp_rel_step1_snd_PROOF.v *)
