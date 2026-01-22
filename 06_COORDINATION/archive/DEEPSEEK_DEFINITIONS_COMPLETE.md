# COMPLETE DEFINITIONS FOR DEEPSEEK AI

## 1. Reducible (simplified to SN)

```coq
(** Reducibility predicate - simplified to SN for all types *)
Definition Reducible (T : ty) (e : expr) : Prop := SN_expr e.
```

**Key insight:** `Reducible T e` is just `SN_expr e` - strong normalization. This simplifies the proof significantly.

---

## 2. SN_expr Definition

```coq
(** Configuration = (expression, store, effect_context) *)
Definition config := (expr * store * effect_ctx)%type.

(** Step relation inverse for well-foundedness *)
Definition step_inv (cfg1 cfg2 : config) : Prop :=
  let (p, ctx2) := cfg2 in
  let (e2, st2) := p in
  let (p', ctx1) := cfg1 in
  let (e1, st1) := p' in
  step (e2, st2, ctx2) (e1, st1, ctx1).

(** Strong normalization via accessibility *)
Definition SN (cfg : config) : Prop := Acc step_inv cfg.

(** SN for expressions (store-polymorphic) *)
Definition SN_expr (e : expr) : Prop :=
  forall st ctx, SN (e, st, ctx).
```

---

## 3. env_reducible

```coq
(** Environment reducibility: all bindings are reducible values *)
Definition env_reducible (Γ : list (ident * ty)) (ρ : subst_rho) : Prop :=
  forall x T,
    lookup x Γ = Some T ->
    value (ρ x) /\ Reducible T (ρ x).
```

---

## 4. subst_env (Full Definition)

```coq
(** Substitution environment *)
Definition subst_rho := ident -> expr.

(** Identity substitution *)
Definition id_rho : subst_rho := fun x => EVar x.

(** Environment extension *)
Definition extend_rho (ρ : subst_rho) (x : ident) (v : expr) : subst_rho :=
  fun y => if String.eqb y x then v else ρ y.

(** Apply substitution to expression *)
Fixpoint subst_env (ρ : subst_rho) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar x => ρ x
  | ELam x T body => ELam x T (subst_env (extend_rho ρ x (EVar x)) body)
  | EApp e1 e2 => EApp (subst_env ρ e1) (subst_env ρ e2)
  | EPair e1 e2 => EPair (subst_env ρ e1) (subst_env ρ e2)
  | EFst e => EFst (subst_env ρ e)
  | ESnd e => ESnd (subst_env ρ e)
  | EInl e T => EInl (subst_env ρ e) T
  | EInr e T => EInr (subst_env ρ e) T
  | ECase e x1 e1 x2 e2 =>
      ECase (subst_env ρ e)
            x1 (subst_env (extend_rho ρ x1 (EVar x1)) e1)
            x2 (subst_env (extend_rho ρ x2 (EVar x2)) e2)
  | EIf e1 e2 e3 => EIf (subst_env ρ e1) (subst_env ρ e2) (subst_env ρ e3)
  | ELet x e1 e2 => ELet x (subst_env ρ e1) (subst_env (extend_rho ρ x (EVar x)) e2)
  | EPerform eff e => EPerform eff (subst_env ρ e)
  | EHandle e x h => EHandle (subst_env ρ e) x (subst_env (extend_rho ρ x (EVar x)) h)
  | ERef e sl => ERef (subst_env ρ e) sl
  | EDeref e => EDeref (subst_env ρ e)
  | EAssign e1 e2 => EAssign (subst_env ρ e1) (subst_env ρ e2)
  | EClassify e => EClassify (subst_env ρ e)
  | EDeclassify e1 e2 => EDeclassify (subst_env ρ e1) (subst_env ρ e2)
  | EProve e => EProve (subst_env ρ e)
  | ERequire eff e => ERequire eff (subst_env ρ e)
  | EGrant eff e => EGrant eff (subst_env ρ e)
  end.
```

---

## 5. store_ty and store_ty_lookup

```coq
Definition store_ty := list (loc * ty * security_level).

Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * security_level) :=
  match Σ with
  | nil => None
  | (l', T, sl) :: Σ' =>
      if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l Σ'
  end.
```

---

## 6. store_ty_extends and store_ty_compatible

```coq
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).

Definition store_ty_compatible (Σ' Σ'' : store_ty) : Prop :=
  forall l T1 sl1 T2 sl2,
    store_ty_lookup l Σ' = Some (T1, sl1) ->
    store_ty_lookup l Σ'' = Some (T2, sl2) ->
    T1 = T2 /\ sl1 = sl2.
```

---

## 7. lookup (type environment)

```coq
Definition type_env := list (ident * ty).

Fixpoint lookup (x : ident) (Γ : type_env) : option ty :=
  match Γ with
  | nil => None
  | (y, T) :: Γ' => if String.eqb x y then Some T else lookup x Γ'
  end.
```

---

## 8. has_type (ALL constructors)

```coq
Inductive has_type : type_env -> store_ty -> security_level ->
                      expr -> ty -> effect -> Prop :=
  (* Values *)
  | T_Unit : forall Γ Σ Δ,
      has_type Γ Σ Δ EUnit TUnit EffectPure

  | T_Bool : forall Γ Σ Δ b,
      has_type Γ Σ Δ (EBool b) TBool EffectPure

  | T_Int : forall Γ Σ Δ n,
      has_type Γ Σ Δ (EInt n) TInt EffectPure

  | T_String : forall Γ Σ Δ s,
      has_type Γ Σ Δ (EString s) TString EffectPure

  | T_Loc : forall Γ Σ Δ l T sl,
      store_ty_lookup l Σ = Some (T, sl) ->
      has_type Γ Σ Δ (ELoc l) (TRef T sl) EffectPure

  | T_Var : forall Γ Σ Δ x T,
      lookup x Γ = Some T ->
      has_type Γ Σ Δ (EVar x) T EffectPure

  (* Functions *)
  | T_Lam : forall Γ Σ Δ x T1 T2 e ε,
      has_type ((x, T1) :: Γ) Σ Δ e T2 ε ->
      has_type Γ Σ Δ (ELam x T1 e) (TFn T1 T2 ε) EffectPure

  | T_App : forall Γ Σ Δ e1 e2 T1 T2 ε ε1 ε2,
      has_type Γ Σ Δ e1 (TFn T1 T2 ε) ε1 ->
      has_type Γ Σ Δ e2 T1 ε2 ->
      has_type Γ Σ Δ (EApp e1 e2) T2 (effect_join ε (effect_join ε1 ε2))

  (* Products *)
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

  (* Sums *)
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

  (* Control *)
  | T_If : forall Γ Σ Δ e1 e2 e3 T ε1 ε2 ε3,
      has_type Γ Σ Δ e1 TBool ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ e3 T ε3 ->
      has_type Γ Σ Δ (EIf e1 e2 e3) T (effect_join ε1 (effect_join ε2 ε3))

  | T_Let : forall Γ Σ Δ x e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (ELet x e1 e2) T2 (effect_join ε1 ε2)

  (* Effects *)
  | T_Perform : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EPerform eff e) T (effect_join ε eff)

  | T_Handle : forall Γ Σ Δ e x h T1 T2 ε1 ε2,
      has_type Γ Σ Δ e T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ h T2 ε2 ->
      has_type Γ Σ Δ (EHandle e x h) T2 (effect_join ε1 ε2)

  (* References *)
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

  (* Security *)
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

  (* Capabilities *)
  | T_Require : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (ERequire eff e) T (effect_join ε eff)

  | T_Grant : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EGrant eff e) T ε.
```

---

## 9. Key Helper Lemmas (Already Proven)

```coq
(** Values are SN *)
Lemma value_SN : forall v,
  value v -> SN_expr v.

(** SN is preserved by reduction *)
Lemma SN_step : forall e st ctx e' st' ctx',
  SN (e, st, ctx) ->
  (e, st, ctx) --> (e', st', ctx') ->
  SN (e', st', ctx').

(** Identity substitution *)
Lemma subst_env_id : forall e,
  subst_env id_rho e = e.

(** Empty env is trivially reducible *)
Lemma env_reducible_nil : forall ρ,
  env_reducible nil ρ.

(** Extending reducible env with reducible value *)
Lemma env_reducible_cons : forall Γ ρ x T v,
  env_reducible Γ ρ ->
  value v ->
  Reducible T v ->
  env_reducible ((x, T) :: Γ) (extend_rho ρ x v).
```

---

## 10. The Axiom to Prove

```coq
(** CURRENT (AXIOM - TO BE PROVEN): *)
Axiom fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  Reducible T (subst_env ρ e).
```

---

## CRITICAL INSIGHT

Since `Reducible T e = SN_expr e`, the proof simplifies to:

**Goal:** Well-typed terms under reducible substitution are strongly normalizing.

**Strategy:**
1. Induction on `has_type Γ Σ pc e T ε`
2. For each typing rule, show `SN_expr (subst_env ρ e)`
3. Values → `value_SN`
4. Compounds → IH + SN closure properties

**The key missing lemma** (probably needs to be proven first):
```coq
Lemma SN_app_general : forall e1 e2,
  SN_expr e1 -> SN_expr e2 -> SN_expr (EApp e1 e2).
```

This follows from the step relation: `EApp e1 e2` steps either by reducing `e1`, reducing `e2`, or beta-reducing when `e1 = ELam x T body`.

---

## FOR store_ty_extensions_compatible

**DeepSeek's analysis is correct:** The axiom as stated is NOT generally true. Two extensions can add the same new location with different types.

**Options:**
1. **Prove restricted version:** "They agree on locations from the base Σ" (true and useful)
2. **Add NoDup invariant:** Require store_ty to have unique locations
3. **Strengthen extends:** Make it track "new" locations distinctly

**Recommendation:** Add this provable lemma:
```coq
Lemma store_ty_extensions_agree_on_base : forall Σ Σ' Σ'' l T sl,
  store_ty_extends Σ Σ' ->
  store_ty_extends Σ Σ'' ->
  store_ty_lookup l Σ = Some (T, sl) ->
  (store_ty_lookup l Σ' = Some (T, sl) /\ store_ty_lookup l Σ'' = Some (T, sl)).
```

Then refactor MasterTheorem.v to use this instead.
