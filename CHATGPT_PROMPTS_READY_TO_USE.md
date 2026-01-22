# CHATGPT PROMPTS - READY TO COPY/PASTE (RIINA CODEBASE-ALIGNED)

## Instructions
- Use these prompts in ChatGPT (web). ChatGPT has NO access to local files.
- The context below is copied from the current codebase under /workspaces/proof/02_FORMAL/coq.
- Do NOT assume any missing definitions or lemmas. If something is missing, say so explicitly.
- Output COMPLETE Coq code only unless the prompt asks for a short explanation.
- No admits, no Admitted, no placeholders, no ellipses.
- End every proof with Qed.
- If the task involves an axiom or security property, first identify the spec reference and include a Coq comment of the form:
  `(* Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md §X.Y *)`

---

# CHAT 0: MASTER CONTEXT (SEND THIS FIRST)

```
You are proving Coq lemmas in the RIINA codebase. You do NOT have access to files.
Use ONLY the definitions and lemmas provided here. Do NOT assume anything else.
If a lemma or definition is missing, explicitly ask for it.

CRITICAL OUTPUT RULES
1) Output COMPLETE, COMPILABLE Coq code only
2) NO admit, NO Admitted, NO placeholders, NO ellipses
3) Every proof ends with Qed.
4) Use standard tactics: intros, destruct, inversion, induction, apply, eapply, exact, auto, simpl, unfold, lia
5) Follow the exact names and signatures below.

========================
CORE DEFINITIONS (RIINA)
========================

(* --- Syntax.v (excerpt) --- *)

Definition ident := string.
Definition loc := nat.

Inductive security_level : Type :=
  | LPublic
  | LInternal
  | LSession
  | LUser
  | LSystem
  | LSecret.

Definition Public := LPublic.
Definition Secret := LSecret.

Inductive effect : Type :=
  | EffPure
  | EffRead
  | EffWrite
  | EffFileSystem
  | EffNetwork
  | EffNetSecure
  | EffCrypto
  | EffRandom
  | EffSystem
  | EffTime
  | EffProcess
  | EffPanel
  | EffZirah
  | EffBenteng
  | EffSandi
  | EffMenara
  | EffGapura.

Definition EffectPure := EffPure.
Definition EffectRead := EffRead.
Definition EffectWrite := EffWrite.
Definition EffectNetwork := EffNetwork.
Definition EffectCrypto := EffCrypto.
Definition EffectSystem := EffSystem.

Definition effect_level (e : effect) : nat :=
  match e with
  | EffPure => 0
  | EffRead => 1 | EffWrite => 2 | EffFileSystem => 3
  | EffNetwork => 4 | EffNetSecure => 5
  | EffCrypto => 6 | EffRandom => 7
  | EffSystem => 8 | EffTime => 9 | EffProcess => 10
  | EffPanel => 11 | EffZirah => 12 | EffBenteng => 13
  | EffSandi => 14 | EffMenara => 15 | EffGapura => 16
  end.

Definition effect_join (e1 e2 : effect) : effect :=
  if Nat.ltb (effect_level e1) (effect_level e2) then e2 else e1.

Inductive taint_source : Type :=
  | TaintNetworkExternal
  | TaintNetworkInternal
  | TaintUserInput
  | TaintFileSystem
  | TaintDatabase
  | TaintEnvironment
  | TaintGapuraRequest
  | TaintZirahEvent
  | TaintZirahEndpoint
  | TaintBentengBiometric
  | TaintSandiSignature
  | TaintMenaraDevice.

Inductive sanitizer : Type :=
  | SanHtmlEscape
  | SanUrlEncode
  | SanJsEscape
  | SanCssEscape
  | SanSqlEscape
  | SanSqlParam
  | SanXssFilter
  | SanPathTraversal
  | SanCommandEscape
  | SanLdapEscape
  | SanXmlEscape
  | SanJsonValidation
  | SanXmlValidation
  | SanEmailValidation
  | SanPhoneValidation
  | SanLengthBound : nat -> sanitizer.

Inductive capability_kind : Type :=
  | CapNetConnect
  | CapNetSecure
  | CapFileRead
  | CapFileWrite
  | CapFileDelete
  | CapCryptoEncrypt
  | CapCryptoDecrypt
  | CapCryptoSign
  | CapCryptoVerify
  | CapSysTime
  | CapSysRandom
  | CapSysEnv
  | CapRootProduct
  | CapProductAccess.

Inductive capability : Type :=
  | CapBasic : capability_kind -> capability
  | CapRevocable : capability -> capability
  | CapTimeBound : capability -> nat -> capability
  | CapDelegated : capability -> ident -> capability.

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
  | TLabeled : ty -> security_level -> ty
  | TTainted : ty -> taint_source -> ty
  | TSanitized : ty -> sanitizer -> ty
  | TProof : ty -> ty
  | TCapability : capability_kind -> ty
  | TCapabilityFull : capability -> ty
  | TChan : session_type -> ty
  | TSecureChan : session_type -> security_level -> ty
  | TConstantTime : ty -> ty
  | TZeroizing : ty -> ty
with session_type : Type :=
  | SessEnd : session_type
  | SessSend : ty -> session_type -> session_type
  | SessRecv : ty -> session_type -> session_type
  | SessSelect : session_type -> session_type -> session_type
  | SessBranch : session_type -> session_type -> session_type
  | SessRec : ident -> session_type -> session_type
  | SessVar : ident -> session_type.

Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : nat -> expr
  | EString : string -> expr
  | ELoc : loc -> expr
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
  | EPerform : effect -> expr -> expr
  | EHandle : expr -> ident -> expr -> expr
  | ERef : expr -> security_level -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  | EClassify : expr -> expr
  | EDeclassify : expr -> expr -> expr
  | EProve : expr -> expr
  | ERequire : effect -> expr -> expr
  | EGrant : effect -> expr -> expr.

Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc : forall l, value (ELoc l)
  | VLam : forall x T e, value (ELam x T e)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve : forall v, value v -> value (EProve v).

Definition declass_ok (e1 e2 : expr) : Prop :=
  exists v, value v /\ e1 = EClassify v /\ e2 = EProve (EClassify v).

Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar y => if String.eqb x y then v else EVar y
  | ELam y T body => if String.eqb x y then ELam y T body else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e1 => EFst (subst x v e1)
  | ESnd e1 => ESnd (subst x v e1)
  | EInl e1 T => EInl (subst x v e1) T
  | EInr e1 T => EInr (subst x v e1) T
  | ECase e1 y1 e2 y2 e3 =>
      ECase (subst x v e1) y1 (if String.eqb x y1 then e2 else subst x v e2)
                        y2 (if String.eqb x y2 then e3 else subst x v e3)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ELet y e1 e2 => ELet y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | EPerform eff e1 => EPerform eff (subst x v e1)
  | EHandle e1 y h => EHandle (subst x v e1) y (if String.eqb x y then h else subst x v h)
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

(* --- Semantics.v (excerpt) --- *)
Definition store := list (loc * expr).

Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' => if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.

Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

Definition fresh_loc (st : store) : loc := S (store_max st).

Definition effect_ctx := list effect.

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
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)
  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)
  | ST_HandleValue : forall v x h st ctx,
      value v ->
      (EHandle v x h, st, ctx) --> ([x := v] h, st, ctx)
  | ST_RefValue : forall v sl st ctx l,
      value v ->
      l = fresh_loc st ->
      (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)
  | ST_DerefLoc : forall v l st ctx,
      store_lookup l st = Some v ->
      (EDeref (ELoc l), st, ctx) --> (v, st, ctx)
  | ST_AssignLoc : forall v1 l st ctx v2,
      store_lookup l st = Some v1 ->
      value v2 ->
      (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)
where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

Inductive multi_step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3, step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).

(* --- Typing.v (excerpt) --- *)
Definition type_env := list (ident * ty).

Fixpoint lookup (x : ident) (G : type_env) : option ty :=
  match G with
  | nil => None
  | (y, T) :: G' => if String.eqb x y then Some T else lookup x G'
  end.

Definition store_ty := list (loc * ty * security_level).

Fixpoint store_ty_lookup (l : loc) (S : store_ty) : option (ty * security_level) :=
  match S with
  | nil => None
  | (l', T, sl) :: S' => if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l S'
  end.

Fixpoint store_ty_update (l : loc) (T : ty) (sl : security_level) (S : store_ty) : store_ty :=
  match S with
  | nil => (l, T, sl) :: nil
  | (l', T', sl') :: S' =>
      if Nat.eqb l l' then (l, T, sl) :: S' else (l', T', sl') :: store_ty_update l T sl S'
  end.

Definition store_ty_extends (S S' : store_ty) : Prop :=
  forall l T sl, store_ty_lookup l S = Some (T, sl) -> store_ty_lookup l S' = Some (T, sl).

Inductive has_type : type_env -> store_ty -> security_level -> expr -> ty -> effect -> Prop :=
  | T_Unit : forall Γ Σ Δ, has_type Γ Σ Δ EUnit TUnit EffectPure
  | T_Bool : forall Γ Σ Δ b, has_type Γ Σ Δ (EBool b) TBool EffectPure
  | T_Int : forall Γ Σ Δ n, has_type Γ Σ Δ (EInt n) TInt EffectPure
  | T_String : forall Γ Σ Δ s, has_type Γ Σ Δ (EString s) TString EffectPure
  | T_Loc : forall Γ Σ Δ l T sl,
      store_ty_lookup l Σ = Some (T, sl) ->
      has_type Γ Σ Δ (ELoc l) (TRef T sl) EffectPure
  | T_Var : forall Γ Σ Δ x T,
      lookup x Γ = Some T ->
      has_type Γ Σ Δ (EVar x) T EffectPure
  | T_Lam : forall Γ Σ Δ x T1 T2 e ε,
      has_type ((x, T1) :: Γ) Σ Δ e T2 ε ->
      has_type Γ Σ Δ (ELam x T1 e) (TFn T1 T2 ε) EffectPure
  | T_App : forall Γ Σ Δ e1 e2 T1 T2 ε ε1 ε2,
      has_type Γ Σ Δ e1 (TFn T1 T2 ε) ε1 ->
      has_type Γ Σ Δ e2 T1 ε2 ->
      has_type Γ Σ Δ (EApp e1 e2) T2 (effect_join ε (effect_join ε1 ε2))
  | T_Pair : forall Γ Σ Δ e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type Γ Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (EPair e1 e2) (TProd T1 T2) (effect_join ε1 ε2)
  | T_Fst : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e (TProd T1 T2) ε ->
      has_type Γ Σ Δ (EFst e) T1 ε
  | T_Snd : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e (TProd T1 T2) ε ->
      has_type Γ Σ Δ (ESnd e) T2 ε
  | T_Inl : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e T1 ε ->
      has_type Γ Σ Δ (EInl e T2) (TSum T1 T2) ε
  | T_Inr : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e T2 ε ->
      has_type Γ Σ Δ (EInr e T1) (TSum T1 T2) ε
  | T_Case : forall Γ Σ Δ e x1 e1 x2 e2 T1 T2 T ε ε1 ε2,
      has_type Γ Σ Δ e (TSum T1 T2) ε ->
      has_type ((x1, T1) :: Γ) Σ Δ e1 T ε1 ->
      has_type ((x2, T2) :: Γ) Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ (ECase e x1 e1 x2 e2) T (effect_join ε (effect_join ε1 ε2))
  | T_If : forall Γ Σ Δ e1 e2 e3 T ε1 ε2 ε3,
      has_type Γ Σ Δ e1 TBool ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ e3 T ε3 ->
      has_type Γ Σ Δ (EIf e1 e2 e3) T (effect_join ε1 (effect_join ε2 ε3))
  | T_Let : forall Γ Σ Δ x e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (ELet x e1 e2) T2 (effect_join ε1 ε2)
  | T_Perform : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EPerform eff e) T (effect_join ε eff)
  | T_Handle : forall Γ Σ Δ e x h T1 T2 ε1 ε2,
      has_type Γ Σ Δ e T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ h T2 ε2 ->
      has_type Γ Σ Δ (EHandle e x h) T2 (effect_join ε1 ε2)
  | T_Ref : forall Γ Σ Δ e T l ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (ERef e l) (TRef T l) (effect_join ε EffectWrite)
  | T_Deref : forall Γ Σ Δ e T l ε,
      has_type Γ Σ Δ e (TRef T l) ε ->
      has_type Γ Σ Δ (EDeref e) T (effect_join ε EffectRead)
  | T_Assign : forall Γ Σ Δ e1 e2 T l ε1 ε2,
      has_type Γ Σ Δ e1 (TRef T l) ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ (EAssign e1 e2) TUnit (effect_join ε1 (effect_join ε2 EffectWrite))
  | T_Classify : forall Γ Σ Δ e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EClassify e) (TSecret T) ε
  | T_Declassify : forall Γ Σ Δ e1 e2 T ε1 ε2,
      has_type Γ Σ Δ e1 (TSecret T) ε1 ->
      has_type Γ Σ Δ e2 (TProof (TSecret T)) ε2 ->
      declass_ok e1 e2 ->
      has_type Γ Σ Δ (EDeclassify e1 e2) T (effect_join ε1 ε2)
  | T_Prove : forall Γ Σ Δ e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EProve e) (TProof T) ε
  | T_Require : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (ERequire eff e) T (effect_join ε eff)
  | T_Grant : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EGrant eff e) T ε.

(* --- Typing.v (excerpt): free variables --- *)
Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EUnit => False
  | EBool _ => False
  | EInt _ => False
  | EString _ => False
  | ELoc _ => False
  | EVar y => x = y
  | ELam y _ body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  | EPair e1 e2 => free_in x e1 \/ free_in x e2
  | EFst e0 => free_in x e0
  | ESnd e0 => free_in x e0
  | EInl e0 _ => free_in x e0
  | EInr e0 _ => free_in x e0
  | ECase e0 y1 e1 y2 e2 =>
      free_in x e0 \/ (x <> y1 /\ free_in x e1) \/ (x <> y2 /\ free_in x e2)
  | EIf e1 e2 e3 => free_in x e1 \/ free_in x e2 \/ free_in x e3
  | ELet y e1 e2 => free_in x e1 \/ (x <> y /\ free_in x e2)
  | EPerform _ e0 => free_in x e0
  | EHandle e0 y h => free_in x e0 \/ (x <> y /\ free_in x h)
  | ERef e0 _ => free_in x e0
  | EDeref e0 => free_in x e0
  | EAssign e1 e2 => free_in x e1 \/ free_in x e2
  | EClassify e0 => free_in x e0
  | EDeclassify e1 e2 => free_in x e1 \/ free_in x e2
  | EProve e0 => free_in x e0
  | ERequire _ e0 => free_in x e0
  | EGrant _ e0 => free_in x e0
  end.

(* --- NonInterference.v (excerpt): val_rel_at_type, val_rel_n, store_rel_n, exp_rel_n --- *)

Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(* --- NonInterference.v (excerpt): environment substitution --- *)
Definition rho_shadow (rho : ident -> expr) (x : ident) : ident -> expr :=
  fun y => if String.eqb y x then EVar y else rho y.

Definition rho_extend (rho : ident -> expr) (x : ident) (v : expr) : ident -> expr :=
  fun y => if String.eqb y x then v else rho y.

(* val_rel_at_type uses store-parameterized predicates for Kripke semantics *)
Section ValRelAtN.
  Variable S : store_ty.
  Variable store_rel_pred : store_ty -> store -> store -> Prop.
  Variable val_rel_lower : store_ty -> ty -> expr -> expr -> Prop.
  Variable store_rel_lower : store_ty -> store -> store -> Prop.

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
        forall S', store_ty_extends S S' ->
          forall x y,
            value x -> value y -> closed_expr x -> closed_expr y ->
            val_rel_lower S' T1 x y ->
            forall st1 st2 ctx,
              store_rel_pred S' st1 st2 ->
              exists (v1' : expr) (v2' : expr) (st1' : store) (st2' : store)
                     (ctx' : effect_ctx) (S'' : store_ty),
                store_ty_extends S' S'' /\
                (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
                (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
                val_rel_lower S'' T2 v1' v2' /\
                store_rel_lower S'' st1' st2'
    | TCapability _ => True
    | TCapabilityFull _ => True
    | TProof _ => True
    | TChan _ => True
    | TSecureChan _ _ => True
    | TConstantTime T' => True
    | TZeroizing T' => True
    end.
End ValRelAtN.

Definition val_rel_at_type (S : store_ty)
  (store_rel_pred : store_ty -> store -> store -> Prop)
  (val_rel_lower : store_ty -> ty -> expr -> expr -> Prop)
  (store_rel_lower : store_ty -> store -> store -> Prop)
  (T : ty) (v1 v2 : expr) : Prop :=
  @ValRelAtN.val_rel_at_type S store_rel_pred val_rel_lower store_rel_lower T v1 v2.

Fixpoint val_rel_n (n : nat) (S : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      val_rel_n n' S T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type S (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end
with store_rel_n (n : nat) (S : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      store_rel_n n' S st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l S = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' S T v1 v2)
  end.

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

Fixpoint exp_rel_n (n : nat) (S : store_ty) (T : ty) (e1 e2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      forall S_cur st1 st2 ctx,
        store_ty_extends S S_cur ->
        store_rel_n n' S_cur st1 st2 ->
        exists (v1 : expr) (v2 : expr) (st1' : store) (st2' : store)
               (ctx' : effect_ctx) (S' : store_ty),
          store_ty_extends S_cur S' /\
          (e1, st1, ctx) -->* (v1, st1', ctx') /\
          (e2, st2, ctx) -->* (v2, st2', ctx') /\
          value v1 /\ value v2 /\
          val_rel_n n' S' T v1 v2 /\
          store_rel_n n' S' st1' st2'
  end.

Definition env_rel_n (n : nat) (S : store_ty) (G : type_env) (rho1 rho2 : ident -> expr) : Prop :=
  forall x T, lookup x G = Some T -> val_rel_n n S T (rho1 x) (rho2 x).

Definition env_rel (S : store_ty) (G : type_env) (rho1 rho2 : ident -> expr) : Prop :=
  forall n, env_rel_n n S G rho1 rho2.

Fixpoint subst_rho (rho : ident -> expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar x => rho x
  | ELam x T body => ELam x T (subst_rho (rho_shadow rho x) body)
  | EApp e1 e2 => EApp (subst_rho rho e1) (subst_rho rho e2)
  | EPair e1 e2 => EPair (subst_rho rho e1) (subst_rho rho e2)
  | EFst e1 => EFst (subst_rho rho e1)
  | ESnd e1 => ESnd (subst_rho rho e1)
  | EInl e1 T => EInl (subst_rho rho e1) T
  | EInr e1 T => EInr (subst_rho rho e1) T
  | ECase e x1 e1 x2 e2 =>
      ECase (subst_rho rho e)
            x1 (subst_rho (rho_shadow rho x1) e1)
            x2 (subst_rho (rho_shadow rho x2) e2)
  | EIf e1 e2 e3 => EIf (subst_rho rho e1) (subst_rho rho e2) (subst_rho rho e3)
  | ELet x e1 e2 => ELet x (subst_rho rho e1) (subst_rho (rho_shadow rho x) e2)
  | EPerform eff e1 => EPerform eff (subst_rho rho e1)
  | EHandle e1 x h => EHandle (subst_rho rho e1) x (subst_rho (rho_shadow rho x) h)
  | ERef e1 l => ERef (subst_rho rho e1) l
  | EDeref e1 => EDeref (subst_rho rho e1)
  | EAssign e1 e2 => EAssign (subst_rho rho e1) (subst_rho rho e2)
  | EClassify e1 => EClassify (subst_rho rho e1)
  | EDeclassify e1 e2 => EDeclassify (subst_rho rho e1) (subst_rho rho e2)
  | EProve e1 => EProve (subst_rho rho e1)
  | ERequire eff e1 => ERequire eff (subst_rho rho e1)
  | EGrant eff e1 => EGrant eff (subst_rho rho e1)
  end.

========================
AVAILABLE LEMMAS (EXCERPTS)
========================

Lemma canonical_forms_fn : forall Γ Σ Δ v T1 T2 ε_fn ε,
  value v ->
  has_type Γ Σ Δ v (TFn T1 T2 ε_fn) ε ->
  exists x body, v = ELam x T1 body.

Lemma canonical_forms_prod : forall Γ Σ Δ v T1 T2 ε,
  value v ->
  has_type Γ Σ Δ v (TProd T1 T2) ε ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.

Lemma canonical_forms_sum : forall Γ Σ Δ v T1 T2 ε,
  value v ->
  has_type Γ Σ Δ v (TSum T1 T2) ε ->
  (exists v', v = EInl v' T2 /\ value v') \/
  (exists v', v = EInr v' T1 /\ value v').

Lemma val_rel_at_type_fo_full_indep : forall T Σ Σ'
  (sp1 sp2 : store_ty -> store -> store -> Prop)
  (vl1 vl2 : store_ty -> ty -> expr -> expr -> Prop)
  (sl1 sl2 : store_ty -> store -> store -> Prop) v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp1 vl1 sl1 T v1 v2 ->
  val_rel_at_type Σ' sp2 vl2 sl2 T v1 v2.

Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.

Lemma store_ty_extends_trans_early : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.

========================
PROOF TASKS (REQUESTED)
========================
I will now provide exact lemma statements to prove. Use ONLY the above context.
For each lemma: output COMPLETE Coq proof with Qed.

Ready for the first lemma?
```

---

# CHAT 1: STEP-1 AXIOM REPLACEMENTS (TYPED)

## PROMPT 1.1
```
Prove this lemma (Axiom elimination with typing) from AxiomEliminationVerified.v:

Lemma exp_rel_step1_app_typed : forall Γ Σ Σ' T1 T2 ε_fn ε f f' a a' st1 st2 ctx,
  has_type Γ Σ' Public f (TFn T1 T2 ε_fn) ε ->
  has_type Γ Σ' Public f' (TFn T1 T2 ε_fn) ε ->
  value f -> value f' -> value a -> value a' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists r1 r2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EApp f a, st1, ctx) -->* (r1, st1', ctx') /\
    (EApp f' a', st2, ctx) -->* (r2, st2', ctx') /\
    val_rel_n 0 Σ'' T2 r1 r2 /\
    store_rel_n 0 Σ'' st1' st2'.

Use canonical_forms_fn to extract lambda bodies from f and f'.
Use ST_AppAbs for the beta step.
```

## PROMPT 1.2
```
Prove this lemma from AxiomEliminationVerified.v:

Lemma exp_rel_step1_let_typed : forall Σ Σ' T v v' x e2 e2' st1 st2 ctx,
  value v -> value v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists r1 r2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (ELet x v e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ELet x v' e2', st2, ctx) -->* (r2, st2', ctx') /\
    val_rel_n 0 Σ'' T r1 r2 /\
    store_rel_n 0 Σ'' st1' st2'.

Use ST_LetValue.
```

## PROMPT 1.3
```
Prove this lemma from AxiomEliminationVerified.v:

Lemma exp_rel_step1_if_same_bool : forall Σ Σ' T b e2 e2' e3 e3' st1 st2 ctx,
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists r1 r2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EIf (EBool b) e2 e3, st1, ctx) -->* (r1, st1', ctx') /\
    (EIf (EBool b) e2' e3', st2, ctx) -->* (r2, st2', ctx') /\
    val_rel_n 0 Σ'' T r1 r2 /\
    store_rel_n 0 Σ'' st1' st2'.

Split on b; use ST_IfTrue / ST_IfFalse.
```

---

# CHAT 2: VALUE/STORE STEP-UP

## PROMPT 2.1
```
Prove this lemma from NonInterference.v:

Lemma val_rel_n_step_up_fo : forall n Σ T v1 v2,
  n > 0 ->
  first_order_type T = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.

Use the cumulative structure of val_rel_n and val_rel_at_type_fo_full_indep.
```

---

# CHAT 3: FIXES

Use this template for any compilation error:

```
The following Coq proof fails:

[PASTE PROOF]

Error:
[PASTE ERROR]

Fix the proof. Requirements:
- Must compile with coqc
- No admits
- Use only the provided context
```
