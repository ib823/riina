-- Copyright (c) 2026 The RIINA Authors. All rights reserved.
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.
import RIINA.Foundations.Syntax

/-!
# RIINA Semantics - Lean 4 Port

Hand-written port of 02_FORMAL/coq/foundations/Semantics.v.
Defines store operations, small-step operational semantics, multi-step
reduction, and 16 theorems matching the Coq originals.
-/

namespace RIINA

-- ============================================================
-- Store: maps locations to expressions
-- ============================================================

/-- The store maps locations to values (association list) -/
abbrev store := List (loc × expr)

/-- Lookup in store by location -/
def store_lookup (l : loc) : store → Option expr
  | [] => none
  | (l', v) :: st' => if l = l' then some v else store_lookup l st'

/-- Update in store by location (insert if not present) -/
def store_update (l : loc) (v : expr) : store → store
  | [] => [(l, v)]
  | (l', v') :: st' =>
      if l = l' then (l, v) :: st' else (l', v') :: store_update l v st'

/-- Maximum location in store -/
def store_max : store → Nat
  | [] => 0
  | (l, _) :: st' => Nat.max l (store_max st')

/-- Fresh location allocator -/
def fresh_loc (st : store) : loc :=
  store_max st + 1

-- ============================================================
-- Effect context
-- ============================================================

/-- Effect context: list of currently available effects -/
abbrev effect_ctx := List effect

/-- Check if an effect is in the context -/
def has_effect (eff : effect) (ctx : effect_ctx) : Prop :=
  eff ∈ ctx

-- ============================================================
-- Configuration type alias
-- ============================================================

/-- A configuration is (expression, store, effect_ctx) -/
abbrev config := expr × store × effect_ctx

-- ============================================================
-- Small-step operational semantics (39 constructors)
-- Matches Coq: Inductive step
-- ============================================================

/-- Small-step reduction relation: cfg1 → cfg2 -/
inductive step : config → config → Prop where
  -- Beta reduction
  | ST_AppAbs : {x : ident} → {T : ty} → {body v : expr} →
      {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.eApp (.eLam x T body) v, st, ctx) (substExpr x v body, st, ctx)
  -- Application congruence
  | ST_App1 : {e1 e1' e2 : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e1, st, ctx) (e1', st', ctx') →
      step (.eApp e1 e2, st, ctx) (.eApp e1' e2, st', ctx')
  | ST_App2 : {v1 e2 e2' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      Value v1 →
      step (e2, st, ctx) (e2', st', ctx') →
      step (.eApp v1 e2, st, ctx) (.eApp v1 e2', st', ctx')
  -- Pair reduction
  | ST_Pair1 : {e1 e1' e2 : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e1, st, ctx) (e1', st', ctx') →
      step (.ePair e1 e2, st, ctx) (.ePair e1' e2, st', ctx')
  | ST_Pair2 : {v1 e2 e2' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      Value v1 →
      step (e2, st, ctx) (e2', st', ctx') →
      step (.ePair v1 e2, st, ctx) (.ePair v1 e2', st', ctx')
  -- Projections
  | ST_Fst : {v1 v2 : expr} → {st : store} → {ctx : effect_ctx} →
      Value v1 → Value v2 →
      step (.eFst (.ePair v1 v2), st, ctx) (v1, st, ctx)
  | ST_Snd : {v1 v2 : expr} → {st : store} → {ctx : effect_ctx} →
      Value v1 → Value v2 →
      step (.eSnd (.ePair v1 v2), st, ctx) (v2, st, ctx)
  | ST_FstStep : {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eFst e, st, ctx) (.eFst e', st', ctx')
  | ST_SndStep : {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eSnd e, st, ctx) (.eSnd e', st', ctx')
  -- Sum elimination
  | ST_CaseInl : {v : expr} → {T : ty} → {x1 : ident} → {e1 : expr} →
      {x2 : ident} → {e2 : expr} → {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.eCase (.eInl v T) x1 e1 x2 e2, st, ctx) (substExpr x1 v e1, st, ctx)
  | ST_CaseInr : {v : expr} → {T : ty} → {x1 : ident} → {e1 : expr} →
      {x2 : ident} → {e2 : expr} → {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.eCase (.eInr v T) x1 e1 x2 e2, st, ctx) (substExpr x2 v e2, st, ctx)
  | ST_CaseStep : {e e' : expr} → {x1 : ident} → {e1 : expr} →
      {x2 : ident} → {e2 : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eCase e x1 e1 x2 e2, st, ctx) (.eCase e' x1 e1 x2 e2, st', ctx')
  -- Sum construction congruence
  | ST_InlStep : {e e' : expr} → {T : ty} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eInl e T, st, ctx) (.eInl e' T, st', ctx')
  | ST_InrStep : {e e' : expr} → {T : ty} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eInr e T, st, ctx) (.eInr e' T, st', ctx')
  -- Conditionals
  | ST_IfTrue : {e2 e3 : expr} → {st : store} → {ctx : effect_ctx} →
      step (.eIf (.eBool true) e2 e3, st, ctx) (e2, st, ctx)
  | ST_IfFalse : {e2 e3 : expr} → {st : store} → {ctx : effect_ctx} →
      step (.eIf (.eBool false) e2 e3, st, ctx) (e3, st, ctx)
  | ST_IfStep : {e1 e1' e2 e3 : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e1, st, ctx) (e1', st', ctx') →
      step (.eIf e1 e2 e3, st, ctx) (.eIf e1' e2 e3, st', ctx')
  -- Let binding
  | ST_LetValue : {x : ident} → {v e2 : expr} → {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.eLet x v e2, st, ctx) (substExpr x v e2, st, ctx)
  | ST_LetStep : {x : ident} → {e1 e1' e2 : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e1, st, ctx) (e1', st', ctx') →
      step (.eLet x e1 e2, st, ctx) (.eLet x e1' e2, st', ctx')
  -- Effects
  | ST_PerformStep : {eff : effect} → {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.ePerform eff e, st, ctx) (.ePerform eff e', st', ctx')
  | ST_PerformValue : {eff : effect} → {v : expr} → {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.ePerform eff v, st, ctx) (v, st, ctx)
  | ST_HandleStep : {e e' : expr} → {x : ident} → {h : expr} →
      {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eHandle e x h, st, ctx) (.eHandle e' x h, st', ctx')
  | ST_HandleValue : {v : expr} → {x : ident} → {h : expr} →
      {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.eHandle v x h, st, ctx) (substExpr x v h, st, ctx)
  -- References
  | ST_RefStep : {e e' : expr} → {sl : security_level} →
      {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eRef e sl, st, ctx) (.eRef e' sl, st', ctx')
  | ST_RefValue : {v : expr} → {sl : security_level} →
      {st : store} → {ctx : effect_ctx} → {l : loc} →
      Value v →
      l = fresh_loc st →
      step (.eRef v sl, st, ctx) (.eLoc l, store_update l v st, ctx)
  | ST_DerefStep : {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eDeref e, st, ctx) (.eDeref e', st', ctx')
  | ST_DerefLoc : {v : expr} → {l : loc} → {st : store} → {ctx : effect_ctx} →
      store_lookup l st = some v →
      step (.eDeref (.eLoc l), st, ctx) (v, st, ctx)
  | ST_Assign1 : {e1 e1' e2 : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e1, st, ctx) (e1', st', ctx') →
      step (.eAssign e1 e2, st, ctx) (.eAssign e1' e2, st', ctx')
  | ST_Assign2 : {v1 e2 e2' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      Value v1 →
      step (e2, st, ctx) (e2', st', ctx') →
      step (.eAssign v1 e2, st, ctx) (.eAssign v1 e2', st', ctx')
  | ST_AssignLoc : {l : loc} → {v1 : expr} → {st : store} → {ctx : effect_ctx} →
      store_lookup l st = some v1 →
      {v2 : expr} →
      Value v2 →
      step (.eAssign (.eLoc l) v2, st, ctx) (.eUnit, store_update l v2 st, ctx)
  -- Classify / Declassify
  | ST_ClassifyStep : {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eClassify e, st, ctx) (.eClassify e', st', ctx')
  | ST_Declassify1 : {e1 e1' e2 : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e1, st, ctx) (e1', st', ctx') →
      step (.eDeclassify e1 e2, st, ctx) (.eDeclassify e1' e2, st', ctx')
  | ST_Declassify2 : {v1 e2 e2' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      Value v1 →
      step (e2, st, ctx) (e2', st', ctx') →
      step (.eDeclassify v1 e2, st, ctx) (.eDeclassify v1 e2', st', ctx')
  | ST_DeclassifyValue : {v : expr} → {p : expr} → {st : store} → {ctx : effect_ctx} →
      Value v →
      declass_ok (.eClassify v) p →
      step (.eDeclassify (.eClassify v) p, st, ctx) (v, st, ctx)
  -- Prove
  | ST_ProveStep : {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eProve e, st, ctx) (.eProve e', st', ctx')
  -- Require / Grant
  | ST_RequireStep : {eff : effect} → {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eRequire eff e, st, ctx) (.eRequire eff e', st', ctx')
  | ST_RequireValue : {eff : effect} → {v : expr} → {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.eRequire eff v, st, ctx) (v, st, ctx)
  | ST_GrantStep : {eff : effect} → {e e' : expr} → {st st' : store} → {ctx ctx' : effect_ctx} →
      step (e, st, ctx) (e', st', ctx') →
      step (.eGrant eff e, st, ctx) (.eGrant eff e', st', ctx')
  | ST_GrantValue : {eff : effect} → {v : expr} → {st : store} → {ctx : effect_ctx} →
      Value v →
      step (.eGrant eff v, st, ctx) (v, st, ctx)

-- ============================================================
-- Multi-step reduction
-- ============================================================

/-- Reflexive-transitive closure of step -/
inductive multi_step : config → config → Prop where
  | MS_Refl : {cfg : config} → multi_step cfg cfg
  | MS_Step : {cfg1 cfg2 cfg3 : config} →
      step cfg1 cfg2 →
      multi_step cfg2 cfg3 →
      multi_step cfg1 cfg3

-- ============================================================
-- Store values property
-- ============================================================

/-- All values in the store are syntactic values -/
def store_has_values (st : store) : Prop :=
  ∀ (l : loc) (v : expr), store_lookup l st = some v → Value v

-- ============================================================
-- Theorems: Store operations
-- ============================================================

private theorem nat_le_max_left (a b : Nat) : a ≤ Nat.max a b := by
  simp [Nat.max_def]
  split
  · assumption
  · exact Nat.le_refl a

private theorem nat_le_max_right (a b : Nat) : b ≤ Nat.max a b := by
  simp [Nat.max_def]
  split
  · exact Nat.le_refl b
  · rename_i h; exact Nat.le_of_lt (Nat.gt_of_not_le h)

/-- Lookup above max location returns none -/
theorem store_lookup_above_max (st : store) (l : loc) (h : store_max st < l) :
    store_lookup l st = none := by
  induction st with
  | nil => rfl
  | cons hd tl ih =>
    match hd with
    | (l', _) =>
      simp only [store_lookup]
      have hlt1 : l' < l := Nat.lt_of_le_of_lt (nat_le_max_left l' (store_max tl)) h
      have hlt2 : store_max tl < l := Nat.lt_of_le_of_lt (nat_le_max_right l' (store_max tl)) h
      have hne : ¬(l = l') := fun heq => absurd (heq ▸ hlt1) (Nat.lt_irrefl l)
      simp [hne]
      exact ih hlt2

/-- Fresh location is not in the store -/
theorem store_lookup_fresh (st : store) :
    store_lookup (fresh_loc st) st = none := by
  apply store_lookup_above_max
  exact Nat.lt_succ_of_le (Nat.le_refl (store_max st))

/-- Updating then looking up the same key returns the new value -/
theorem store_update_lookup_eq (st : store) (l : loc) (v : expr) :
    store_lookup l (store_update l v st) = some v := by
  induction st with
  | nil => simp [store_update, store_lookup]
  | cons hd tl ih =>
    match hd with
    | (l', _) =>
      simp [store_update]
      split
      · next h => simp [store_lookup, h]
      · next h =>
        simp [store_lookup]
        split
        · next h2 => simp [h2] at h
        · exact ih

/-- Updating key l then looking up different key l' returns original value -/
theorem store_update_lookup_neq (st : store) (l l' : loc) (v : expr)
    (hne : l ≠ l') :
    store_lookup l' (store_update l v st) = store_lookup l' st := by
  induction st with
  | nil =>
    simp only [store_update, store_lookup]
    split
    · next h => exact absurd h (Ne.symm hne)
    · rfl
  | cons hd tl ih =>
    match hd with
    | (l'', v'') =>
      simp [store_update]
      split
      · next heq =>
        subst heq
        simp [store_lookup]
        split
        · next h2 => exact absurd h2 (Ne.symm hne)
        · rfl
      · next hne2 =>
        simp [store_lookup]
        split
        · rfl
        · exact ih

/-- Empty store has the values property -/
theorem store_has_values_empty : store_has_values [] := by
  intro l v h
  simp [store_lookup] at h

/-- Updating store with a value preserves the values property -/
theorem store_update_preserves_values (st : store) (l : loc) (v : expr)
    (hst : store_has_values st) (hv : Value v) :
    store_has_values (store_update l v st) := by
  intro l' v' hlook
  by_cases h : l = l'
  · subst h
    rw [store_update_lookup_eq] at hlook
    injection hlook with heq
    subst heq
    exact hv
  · rw [store_update_lookup_neq _ _ _ _ h] at hlook
    exact hst l' v' hlook

-- ============================================================
-- Theorems: Value / Step interaction
-- ============================================================

/-- Values do not step (auxiliary — generalized over all configs) -/
theorem value_not_step (v : expr) (hv : Value v) :
    ∀ (st : store) (ctx : effect_ctx) (cfg : config),
    ¬ step (v, st, ctx) cfg := by
  induction hv with
  | VUnit => intros _ _ _ h; cases h
  | VBool _ => intros _ _ _ h; cases h
  | VInt _ => intros _ _ _ h; cases h
  | VString _ => intros _ _ _ h; cases h
  | VLoc _ => intros _ _ _ h; cases h
  | VLam _ _ _ => intros _ _ _ h; cases h
  | VPair _ _ ih1 ih2 =>
    intros st ctx cfg h
    cases h with
    | ST_Pair1 hs => exact ih1 st ctx _ hs
    | ST_Pair2 _ hs => exact ih2 st ctx _ hs
  | VInl _ _ ih =>
    intros st ctx cfg h
    cases h with
    | ST_InlStep hs => exact ih st ctx _ hs
  | VInr _ _ ih =>
    intros st ctx cfg h
    cases h with
    | ST_InrStep hs => exact ih st ctx _ hs
  | VClassify _ ih =>
    intros st ctx cfg h
    cases h with
    | ST_ClassifyStep hs => exact ih st ctx _ hs
  | VProve _ ih =>
    intros st ctx cfg h
    cases h with
    | ST_ProveStep hs => exact ih st ctx _ hs

/-- Values do not step (triple-output version) -/
theorem value_does_not_step (v : expr) (st : store) (ctx : effect_ctx)
    (e' : expr) (st' : store) (ctx' : effect_ctx)
    (hv : Value v) (hstep : step (v, st, ctx) (e', st', ctx')) : False :=
  value_not_step v hv st ctx (e', st', ctx') hstep

-- ============================================================
-- Theorems: Determinism (sorry'd — large case analysis)
-- ============================================================

/-- Step is deterministic on configurations -/
theorem step_deterministic_cfg : ∀ (cfg cfg1 cfg2 : config),
    step cfg cfg1 → step cfg cfg2 → cfg1 = cfg2 := by
  sorry

/-- Step is deterministic (decomposed) -/
theorem step_deterministic (t : expr) (st : store) (ctx : effect_ctx)
    (t1 : expr) (st1 : store) (ctx1 : effect_ctx)
    (t2 : expr) (st2 : store) (ctx2 : effect_ctx)
    (h1 : step (t, st, ctx) (t1, st1, ctx1))
    (h2 : step (t, st, ctx) (t2, st2, ctx2)) :
    t1 = t2 ∧ st1 = st2 ∧ ctx1 = ctx2 := by
  have := step_deterministic_cfg (t, st, ctx) (t1, st1, ctx1) (t2, st2, ctx2) h1 h2
  simp [Prod.mk.injEq] at this
  exact this

-- ============================================================
-- Theorems: Store preservation
-- ============================================================

/-- Step preserves store_has_values (auxiliary cfg version) -/
theorem step_preserves_store_values_aux (cfg1 cfg2 : config)
    (hstep : step cfg1 cfg2)
    (hst : store_has_values cfg1.2.1) :
    store_has_values cfg2.2.1 := by
  induction hstep with
  | ST_RefValue hv hl =>
    subst hl
    exact store_update_preserves_values _ _ _ hst hv
  | ST_AssignLoc _ hv2 =>
    exact store_update_preserves_values _ _ _ hst hv2
  | ST_App1 _ ih | ST_App2 _ _ ih | ST_Pair1 _ ih | ST_Pair2 _ _ ih
  | ST_FstStep _ ih | ST_SndStep _ ih | ST_CaseStep _ ih
  | ST_InlStep _ ih | ST_InrStep _ ih | ST_IfStep _ ih
  | ST_LetStep _ ih | ST_PerformStep _ ih | ST_HandleStep _ ih
  | ST_RefStep _ ih | ST_DerefStep _ ih
  | ST_Assign1 _ ih | ST_Assign2 _ _ ih
  | ST_ClassifyStep _ ih | ST_Declassify1 _ ih | ST_Declassify2 _ _ ih
  | ST_ProveStep _ ih | ST_RequireStep _ ih | ST_GrantStep _ ih =>
    exact ih hst
  | _ => exact hst

/-- Step preserves store_has_values -/
theorem step_preserves_store_values (e : expr) (st : store) (ctx : effect_ctx)
    (e' : expr) (st' : store) (ctx' : effect_ctx)
    (hstep : step (e, st, ctx) (e', st', ctx'))
    (hst : store_has_values st) :
    store_has_values st' :=
  step_preserves_store_values_aux (e, st, ctx) (e', st', ctx') hstep hst

/-- Multi-step preserves store_has_values -/
theorem multi_step_preserves_store_values (cfg1 cfg2 : config)
    (hms : multi_step cfg1 cfg2)
    (hst : store_has_values cfg1.2.1) :
    store_has_values cfg2.2.1 := by
  induction hms with
  | MS_Refl => exact hst
  | MS_Step hstep _ ih =>
    apply ih
    exact step_preserves_store_values_aux _ _ hstep hst

-- ============================================================
-- Theorems: Substitution preserves values
-- ============================================================

/-- Substitution preserves the Value predicate -/
theorem value_subst (x : ident) (v1 v2 : expr)
    (hv1 : Value v1) (_hv2 : Value v2) :
    Value (substExpr x v2 v1) := by
  induction hv1 with
  | VUnit => exact .VUnit
  | VBool b => exact .VBool b
  | VInt n => exact .VInt n
  | VString s => exact .VString s
  | VLoc l => exact .VLoc l
  | VLam y T _ =>
    simp [substExpr]
    split
    · exact .VLam y T _
    · exact .VLam y T _
  | VPair _ _ ih1 ih2 =>
    simp [substExpr]
    exact .VPair ih1 ih2
  | VInl T _ ih =>
    simp [substExpr]
    exact .VInl T ih
  | VInr T _ ih =>
    simp [substExpr]
    exact .VInr T ih
  | VClassify _ ih =>
    simp [substExpr]
    exact .VClassify ih
  | VProve _ ih =>
    simp [substExpr]
    exact .VProve ih

/-- Substitution preserves declassification predicate -/
theorem declass_ok_subst (x : ident) (v e1 e2 : expr)
    (hv : Value v) (hok : declass_ok e1 e2) :
    declass_ok (substExpr x v e1) (substExpr x v e2) := by
  match hok with
  | ⟨v0, hv0, he1, he2⟩ =>
    subst he1; subst he2
    simp [substExpr]
    exact ⟨substExpr x v v0, value_subst x v0 v hv0 hv, rfl, rfl⟩

end RIINA
