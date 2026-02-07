-- Copyright (c) 2026 The RIINA Authors. All rights reserved.
import RIINA.Foundations.Syntax
import RIINA.Foundations.Semantics

/-!
# RIINA Typing Rules - Lean 4 Port

Port of 02_FORMAL/coq/foundations/Typing.v (648 lines, 12 Qed).
Uses definitions from Syntax.lean and Semantics.lean.
-/

namespace RIINA

/-! ## Type Environments -/

/-- Type environment: list of (identifier, type) pairs -/
abbrev type_env := List (ident × ty)

/-- Lookup in type environment -/
def type_env_lookup (x : ident) : type_env → Option ty
  | [] => none
  | (y, T) :: Γ' => if x = y then some T else type_env_lookup x Γ'

/-! ## Store Typing -/

/-- Store typing: list of (location, type, security level) -/
abbrev store_ty := List (loc × ty × security_level)

/-- Lookup in store typing -/
def store_ty_lookup (l : loc) : store_ty → Option (ty × security_level)
  | [] => none
  | entry :: rest =>
      let (l', Tsl) := entry
      if l = l' then some Tsl else store_ty_lookup l rest

/-- Update store typing -/
def store_ty_update (l : loc) (T : ty) (sl : security_level) : store_ty → store_ty
  | [] => [(l, T, sl)]
  | entry :: rest =>
      let (l', _) := entry
      if l = l' then (l, T, sl) :: rest else entry :: store_ty_update l T sl rest

/-- Store typing extension -/
def store_ty_extends (σ σ' : store_ty) : Prop :=
  ∀ (l : loc) (T : ty) (sl : security_level),
    store_ty_lookup l σ = some (T, sl) → store_ty_lookup l σ' = some (T, sl)

/-! ## Effect join (for typing) -/

/-- Join of two effects (max by level) -/
def eff_join (e1 e2 : effect) : effect :=
  effect_join e1 e2

/-! ## Typing Judgment

has_type Γ Σ Δ e T ε means: under environment Γ, store typing Σ,
and security context Δ, expression e has type T with effect ε.
-/

/-- Typing judgment (28 rules matching Coq) -/
inductive has_type : type_env → store_ty → security_level → expr → ty → effect → Prop where
  -- Values
  | T_Unit : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      has_type Γ σ Δ .eUnit .tUnit .effPure
  | T_Bool : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} → {b : Bool} →
      has_type Γ σ Δ (.eBool b) .tBool .effPure
  | T_Int : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} → {n : Nat} →
      has_type Γ σ Δ (.eInt n) .tInt .effPure
  | T_String : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} → {s : String} →
      has_type Γ σ Δ (.eString s) .tString .effPure
  | T_Loc : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {l : loc} → {T : ty} → {sl : security_level} →
      store_ty_lookup l σ = some (T, sl) →
      has_type Γ σ Δ (.eLoc l) (.tRef T sl) .effPure
  | T_Var : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {x : ident} → {T : ty} →
      type_env_lookup x Γ = some T →
      has_type Γ σ Δ (.eVar x) T .effPure
  -- Functions
  | T_Lam : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {x : ident} → {T1 T2 : ty} → {e : expr} → {ε : effect} →
      has_type ((x, T1) :: Γ) σ Δ e T2 ε →
      has_type Γ σ Δ (.eLam x T1 e) (.tFn T1 T2 ε) .effPure
  | T_App : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e1 e2 : expr} → {T1 T2 : ty} → {ε ε1 ε2 : effect} →
      has_type Γ σ Δ e1 (.tFn T1 T2 ε) ε1 →
      has_type Γ σ Δ e2 T1 ε2 →
      has_type Γ σ Δ (.eApp e1 e2) T2 (eff_join ε (eff_join ε1 ε2))
  -- Products
  | T_Pair : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e1 e2 : expr} → {T1 T2 : ty} → {ε1 ε2 : effect} →
      has_type Γ σ Δ e1 T1 ε1 →
      has_type Γ σ Δ e2 T2 ε2 →
      has_type Γ σ Δ (.ePair e1 e2) (.tProd T1 T2) (eff_join ε1 ε2)
  | T_Fst : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T1 T2 : ty} → {ε : effect} →
      has_type Γ σ Δ e (.tProd T1 T2) ε →
      has_type Γ σ Δ (.eFst e) T1 ε
  | T_Snd : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T1 T2 : ty} → {ε : effect} →
      has_type Γ σ Δ e (.tProd T1 T2) ε →
      has_type Γ σ Δ (.eSnd e) T2 ε
  -- Sums
  | T_Inl : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T1 T2 : ty} → {ε : effect} →
      has_type Γ σ Δ e T1 ε →
      has_type Γ σ Δ (.eInl e T2) (.tSum T1 T2) ε
  | T_Inr : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T1 T2 : ty} → {ε : effect} →
      has_type Γ σ Δ e T2 ε →
      has_type Γ σ Δ (.eInr e T1) (.tSum T1 T2) ε
  | T_Case : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {x1 : ident} → {e1 : expr} → {x2 : ident} → {e2 : expr} →
      {T1 T2 T : ty} → {ε ε1 ε2 : effect} →
      has_type Γ σ Δ e (.tSum T1 T2) ε →
      has_type ((x1, T1) :: Γ) σ Δ e1 T ε1 →
      has_type ((x2, T2) :: Γ) σ Δ e2 T ε2 →
      has_type Γ σ Δ (.eCase e x1 e1 x2 e2) T (eff_join ε (eff_join ε1 ε2))
  -- Control
  | T_If : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e1 e2 e3 : expr} → {T : ty} → {ε1 ε2 ε3 : effect} →
      has_type Γ σ Δ e1 .tBool ε1 →
      has_type Γ σ Δ e2 T ε2 →
      has_type Γ σ Δ e3 T ε3 →
      has_type Γ σ Δ (.eIf e1 e2 e3) T (eff_join ε1 (eff_join ε2 ε3))
  | T_Let : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {x : ident} → {e1 e2 : expr} → {T1 T2 : ty} → {ε1 ε2 : effect} →
      has_type Γ σ Δ e1 T1 ε1 →
      has_type ((x, T1) :: Γ) σ Δ e2 T2 ε2 →
      has_type Γ σ Δ (.eLet x e1 e2) T2 (eff_join ε1 ε2)
  -- Effects
  | T_Perform : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {eff : effect} → {e : expr} → {T : ty} → {ε : effect} →
      has_type Γ σ Δ e T ε →
      has_type Γ σ Δ (.ePerform eff e) T (eff_join ε eff)
  | T_Handle : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {x : ident} → {h : expr} → {T1 T2 : ty} → {ε1 ε2 : effect} →
      has_type Γ σ Δ e T1 ε1 →
      has_type ((x, T1) :: Γ) σ Δ h T2 ε2 →
      has_type Γ σ Δ (.eHandle e x h) T2 (eff_join ε1 ε2)
  -- References
  | T_Ref : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T : ty} → {sl : security_level} → {ε : effect} →
      has_type Γ σ Δ e T ε →
      has_type Γ σ Δ (.eRef e sl) (.tRef T sl) (eff_join ε .effWrite)
  | T_Deref : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T : ty} → {sl : security_level} → {ε : effect} →
      has_type Γ σ Δ e (.tRef T sl) ε →
      has_type Γ σ Δ (.eDeref e) T (eff_join ε .effRead)
  | T_Assign : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e1 e2 : expr} → {T : ty} → {sl : security_level} → {ε1 ε2 : effect} →
      has_type Γ σ Δ e1 (.tRef T sl) ε1 →
      has_type Γ σ Δ e2 T ε2 →
      has_type Γ σ Δ (.eAssign e1 e2) .tUnit (eff_join ε1 (eff_join ε2 .effWrite))
  -- Security
  | T_Classify : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T : ty} → {ε : effect} →
      has_type Γ σ Δ e T ε →
      has_type Γ σ Δ (.eClassify e) (.tSecret T) ε
  | T_Declassify : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e1 e2 : expr} → {T : ty} → {ε1 ε2 : effect} →
      has_type Γ σ Δ e1 (.tSecret T) ε1 →
      has_type Γ σ Δ e2 (.tProof (.tSecret T)) ε2 →
      declass_ok e1 e2 →
      has_type Γ σ Δ (.eDeclassify e1 e2) T (eff_join ε1 ε2)
  | T_Prove : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {e : expr} → {T : ty} → {ε : effect} →
      has_type Γ σ Δ e T ε →
      has_type Γ σ Δ (.eProve e) (.tProof T) ε
  -- Capabilities
  | T_Require : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {eff : effect} → {e : expr} → {T : ty} → {ε : effect} →
      has_type Γ σ Δ e T ε →
      has_type Γ σ Δ (.eRequire eff e) T (eff_join ε eff)
  | T_Grant : {Γ : type_env} → {σ : store_ty} → {Δ : security_level} →
      {eff : effect} → {e : expr} → {T : ty} → {ε : effect} →
      has_type Γ σ Δ e T ε →
      has_type Γ σ Δ (.eGrant eff e) T ε

/-! ## Store Well-Formedness -/

/-- Well-typed store -/
def store_wf (σ : store_ty) (st : store) : Prop :=
  (∀ (l : loc) (T : ty) (sl : security_level),
     store_ty_lookup l σ = some (T, sl) →
     ∃ (v : expr), store_lookup l st = some v ∧ Value v ∧
       has_type [] σ .lPublic v T .effPure) ∧
  (∀ (l : loc) (v : expr),
     store_lookup l st = some v →
     ∃ (T : ty) (sl : security_level),
       store_ty_lookup l σ = some (T, sl) ∧ Value v ∧
       has_type [] σ .lPublic v T .effPure)

/-! ## Canonical Forms -/

/-- Unit type: only eUnit is a value of type tUnit -/
theorem canonical_forms_unit {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v .tUnit ε) :
    v = .eUnit := by
  cases hval <;> cases htype <;> rfl

/-- Bool type: only eBool b is a value of type tBool -/
theorem canonical_forms_bool {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v .tBool ε) :
    ∃ (b : Bool), v = .eBool b := by
  cases hval <;> cases htype
  exact ⟨_, rfl⟩

/-- Int type: only eInt n is a value of type tInt -/
theorem canonical_forms_int {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v .tInt ε) :
    ∃ (n : Nat), v = .eInt n := by
  cases hval <;> cases htype
  exact ⟨_, rfl⟩

/-- String type: only eString s is a value of type tString -/
theorem canonical_forms_string {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v .tString ε) :
    ∃ (s : String), v = .eString s := by
  cases hval <;> cases htype
  exact ⟨_, rfl⟩

/-- Function type: only eLam is a value of function type -/
theorem canonical_forms_fn {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {T1 T2 : ty} {ε_fn ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v (.tFn T1 T2 ε_fn) ε) :
    ∃ (x : ident) (body : expr), v = .eLam x T1 body := by
  cases hval <;> cases htype
  exact ⟨_, _, rfl⟩

/-- Product type: only ePair is a value of product type -/
theorem canonical_forms_prod {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {T1 T2 : ty} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v (.tProd T1 T2) ε) :
    ∃ (v1 v2 : expr), v = .ePair v1 v2 ∧ Value v1 ∧ Value v2 := by
  cases hval with
  | VUnit => cases htype
  | VBool _ => cases htype
  | VInt _ => cases htype
  | VString _ => cases htype
  | VLoc _ => cases htype
  | VLam _ _ _ => cases htype
  | VPair hv1 hv2 => cases htype; exact ⟨_, _, rfl, hv1, hv2⟩
  | VInl _ _ => cases htype
  | VInr _ _ => cases htype
  | VClassify _ => cases htype
  | VProve _ => cases htype

/-- Sum type: only eInl or eInr is a value of sum type -/
theorem canonical_forms_sum {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {T1 T2 : ty} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v (.tSum T1 T2) ε) :
    (∃ (v' : expr), v = .eInl v' T2 ∧ Value v') ∨
    (∃ (v' : expr), v = .eInr v' T1 ∧ Value v') := by
  cases hval with
  | VUnit => cases htype
  | VBool _ => cases htype
  | VInt _ => cases htype
  | VString _ => cases htype
  | VLoc _ => cases htype
  | VLam _ _ _ => cases htype
  | VPair _ _ => cases htype
  | VInl _ hv => cases htype; exact Or.inl ⟨_, rfl, hv⟩
  | VInr _ hv => cases htype; exact Or.inr ⟨_, rfl, hv⟩
  | VClassify _ => cases htype
  | VProve _ => cases htype

/-- Reference type: only eLoc is a value of reference type -/
theorem canonical_forms_ref {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {T : ty} {sl : security_level} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v (.tRef T sl) ε) :
    ∃ (l : loc), v = .eLoc l := by
  cases hval <;> cases htype
  exact ⟨_, rfl⟩

/-- Secret type: only eClassify is a value of secret type -/
theorem canonical_forms_secret {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {T : ty} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v (.tSecret T) ε) :
    ∃ (v' : expr), v = .eClassify v' ∧ Value v' := by
  cases hval with
  | VUnit => cases htype
  | VBool _ => cases htype
  | VInt _ => cases htype
  | VString _ => cases htype
  | VLoc _ => cases htype
  | VLam _ _ _ => cases htype
  | VPair _ _ => cases htype
  | VInl _ _ => cases htype
  | VInr _ _ => cases htype
  | VClassify hv => cases htype; exact ⟨_, rfl, hv⟩
  | VProve _ => cases htype

/-- Proof type: only eProve is a value of proof type -/
theorem canonical_forms_proof {Γ : type_env} {σ : store_ty} {Δ : security_level}
    {v : expr} {T : ty} {ε : effect}
    (hval : Value v) (htype : has_type Γ σ Δ v (.tProof T) ε) :
    ∃ (v' : expr), v = .eProve v' ∧ Value v' := by
  cases hval with
  | VUnit => cases htype
  | VBool _ => cases htype
  | VInt _ => cases htype
  | VString _ => cases htype
  | VLoc _ => cases htype
  | VLam _ _ _ => cases htype
  | VPair _ _ => cases htype
  | VInl _ _ => cases htype
  | VInr _ _ => cases htype
  | VClassify _ => cases htype
  | VProve hv => cases htype; exact ⟨_, rfl, hv⟩

end RIINA
