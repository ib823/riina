-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

/-!
# RIINA Effect System - Lean 4 Port

Exact port of 02_FORMAL/coq/effects/EffectSystem.v (325 lines, 5 Qed).

Reference: CTSS_v1_0_1.md, Section 5 (Effects)

Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

## Correspondence Table

| Coq Definition | Lean Definition | Status |
|----------------|-----------------|--------|
| performs_within | performsWithin | ✅ |
| performs_within_mono | performsWithin_mono | ✅ |
| effect_leq_join_ub_l_trans | effectLeq_join_ub_l_trans | ✅ |
| effect_leq_join_ub_r_trans | effectLeq_join_ub_r_trans | ✅ |
| core_effects_within | coreEffectsWithin | ⚠️ Stated |
| has_type_full | HasTypeFull | ✅ |
| effect_safety | effectSafety | ⚠️ Stated |
-/

import RIINA.Foundations.Syntax
import RIINA.Foundations.Semantics
import RIINA.TypeSystem.Typing
import RIINA.Effects.EffectAlgebra

namespace RIINA

open Expr Effect

/-! ## Effect Occurrence Predicate -/

/-- A configuration performs effects within the given bound
    (matches Coq: Fixpoint performs_within) -/
def performsWithin : Expr → Effect → Prop
  | .unit, _ => True
  | .bool _, _ => True
  | .int _, _ => True
  | .string _, _ => True
  | .loc _, _ => True
  | .var _, _ => True
  | .lam _ _ _, _ => True  -- Lambda body not evaluated at creation time
  | .app e1 e2, eff => performsWithin e1 eff ∧ performsWithin e2 eff
  | .pair e1 e2, eff => performsWithin e1 eff ∧ performsWithin e2 eff
  | .fst e1, eff => performsWithin e1 eff
  | .snd e1, eff => performsWithin e1 eff
  | .inl e1 _, eff => performsWithin e1 eff
  | .inr e1 _, eff => performsWithin e1 eff
  | .case e0 _ e1 _ e2, eff =>
      performsWithin e0 eff ∧ performsWithin e1 eff ∧ performsWithin e2 eff
  | .ite e1 e2 e3, eff =>
      performsWithin e1 eff ∧ performsWithin e2 eff ∧ performsWithin e3 eff
  | .let_ _ e1 e2, eff => performsWithin e1 eff ∧ performsWithin e2 eff
  | .perform eff' e1, eff => eff' ≤ eff ∧ performsWithin e1 eff
  | .handle e1 _ h, eff => performsWithin e1 eff ∧ performsWithin h eff
  | .ref e1 _, eff => performsWithin e1 eff
  | .deref e1, eff => performsWithin e1 eff
  | .assign e1 e2, eff => performsWithin e1 eff ∧ performsWithin e2 eff
  | .classify e1, eff => performsWithin e1 eff
  | .declassify e1 e2, eff => performsWithin e1 eff ∧ performsWithin e2 eff
  | .prove e1, eff => performsWithin e1 eff
  | .require _ e1, eff => performsWithin e1 eff
  | .grant _ e1, eff => performsWithin e1 eff

/-! ## Monotonicity -/

/-- performs_within is monotonic in the effect bound
    (matches Coq: Lemma performs_within_mono) -/
theorem performsWithin_mono (e : Expr) (eff1 eff2 : Effect)
    (hle : eff1 ≤ eff2) (hpw : performsWithin e eff1) :
    performsWithin e eff2 := by
  induction e with
  | unit | bool _ | int _ | string _ | loc _ | var _ | lam _ _ _ =>
      simp [performsWithin]
  | app e1 e2 ih1 ih2 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih1 hle hpw.1, ih2 hle hpw.2⟩
  | pair e1 e2 ih1 ih2 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih1 hle hpw.1, ih2 hle hpw.2⟩
  | fst e ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | snd e ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | inl e _ ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | inr e _ ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | case e0 _ e1 _ e2 ih0 ih1 ih2 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih0 hle hpw.1, ih1 hle hpw.2.1, ih2 hle hpw.2.2⟩
  | ite e1 e2 e3 ih1 ih2 ih3 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih1 hle hpw.1, ih2 hle hpw.2.1, ih3 hle hpw.2.2⟩
  | let_ _ e1 e2 ih1 ih2 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih1 hle hpw.1, ih2 hle hpw.2⟩
  | perform eff' e ih =>
      simp [performsWithin] at hpw ⊢
      exact ⟨effectLeq_trans eff' eff1 eff2 hpw.1 hle, ih hle hpw.2⟩
  | handle e1 _ h ih1 ih2 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih1 hle hpw.1, ih2 hle hpw.2⟩
  | ref e _ ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | deref e ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | assign e1 e2 ih1 ih2 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih1 hle hpw.1, ih2 hle hpw.2⟩
  | classify e ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | declassify e1 e2 ih1 ih2 =>
      simp [performsWithin] at hpw ⊢
      exact ⟨ih1 hle hpw.1, ih2 hle hpw.2⟩
  | prove e ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | require _ e ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw
  | grant _ e ih =>
      simp [performsWithin] at hpw ⊢
      exact ih hle hpw

/-! ## Helper Lemmas for Join Upper Bounds -/

/-- Helper: e1 ≤ join e2 (join e1 e3)
    (matches Coq: Lemma effect_leq_join_ub_l_trans) -/
theorem effectLeq_join_ub_l_trans (e1 e2 e3 : Effect) :
    e1 ≤ e2.join (e1.join e3) := by
  have h1 : e1 ≤ e1.join e3 := effectJoin_ub_l e1 e3
  have h2 : e1.join e3 ≤ e2.join (e1.join e3) := effectJoin_ub_r e2 (e1.join e3)
  exact effectLeq_trans e1 (e1.join e3) (e2.join (e1.join e3)) h1 h2

/-- Helper: e3 ≤ join e2 (join e1 e3)
    (matches Coq: Lemma effect_leq_join_ub_r_trans) -/
theorem effectLeq_join_ub_r_trans (e1 e2 e3 : Effect) :
    e3 ≤ e2.join (e1.join e3) := by
  have h1 : e3 ≤ e1.join e3 := effectJoin_ub_r e1 e3
  have h2 : e1.join e3 ≤ e2.join (e1.join e3) := effectJoin_ub_r e2 (e1.join e3)
  exact effectLeq_trans e3 (e1.join e3) (e2.join (e1.join e3)) h1 h2

/-! ## Core Effects Within

    Note: Full proof requires induction on has_type with 28 cases.
    The theorem is stated here and can be filled in when needed. -/

/-- Well-typed expressions perform effects within their declared effect bound
    (matches Coq: Lemma core_effects_within) -/
theorem coreEffectsWithin (Γ : TypeEnv) (Σ : StoreTy) (D : SecurityLevel)
    (e : Expr) (T : Ty) (ε : Effect)
    (hty : HasType Γ Σ D e T ε) :
    performsWithin e ε := by
  induction hty with
  -- Category A: Trivially true (values, vars, lambdas)
  | unit | bool _ | int _ | string _ | loc _ | var _ | lam _ =>
      simp [performsWithin]
  -- Category B: Single subexpression, same effect
  | fst _ ih | snd _ ih | inl _ ih | inr _ ih
  | ref _ ih | deref _ ih | classify _ ih | prove _ ih
  | require _ ih | grant _ ih =>
      simp [performsWithin]; exact ih
  -- Category C: Two subexpressions joined with effect_join
  | app h1 h2 ih1 ih2 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1,
             performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2⟩
  | pair h1 h2 ih1 ih2 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1,
             performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2⟩
  | let_ h1 h2 ih1 ih2 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1,
             performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2⟩
  | handle h1 h2 ih1 ih2 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1,
             performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2⟩
  | assign h1 h2 _ ih1 ih2 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1,
             performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2⟩
  | declassify h1 h2 _ ih1 ih2 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1,
             performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2⟩
  -- Category D: Perform — effect_leq check + subexpression
  | perform h ih =>
      simp [performsWithin]
      exact ⟨effectJoin_ub_r _ _,
             performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih⟩
  -- Category E: Three subexpressions with nested join
  | case_ h0 h1 h2 ih0 ih1 ih2 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih0,
             performsWithin_mono _ _ _ (effectLeq_join_ub_l_trans _ _ _) ih1,
             performsWithin_mono _ _ _ (effectLeq_join_ub_r_trans _ _ _) ih2⟩
  | ite h1 h2 h3 ih1 ih2 ih3 =>
      simp [performsWithin]
      exact ⟨performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1,
             performsWithin_mono _ _ _ (effectLeq_join_ub_l_trans _ _ _) ih2,
             performsWithin_mono _ _ _ (effectLeq_join_ub_r_trans _ _ _) ih3⟩

/-! ## Extended Typing with Full Effect Operations -/

/-- Extended typing relation including effect operations
    (matches Coq: Inductive has_type_full) -/
inductive HasTypeFull : TypeEnv → StoreTy → SecurityLevel →
    Expr → Ty → Effect → Prop where
  /-- Core typing rules embed into full typing -/
  | core : HasType Γ Σ D e T ε → HasTypeFull Γ Σ D e T ε

  /-- Perform an effect operation
      Γ; Σ; D ⊢ e : T, ε
      ────────────────────────────────────
      Γ; Σ; D ⊢ perform eff e : T, ε ⊔ eff -/
  | perform : HasTypeFull Γ Σ D e T ε →
      HasTypeFull Γ Σ D (.perform eff e) T (ε.join eff)

  /-- Handle an effect
      Γ; Σ; D ⊢ e : T₁, ε₁    (y : T₁), Γ; Σ; D ⊢ h : T₂, ε₂
      ───────────────────────────────────────────────────────────
      Γ; Σ; D ⊢ handle e with y => h : T₂, ε₁ ⊔ ε₂ -/
  | handle : HasTypeFull Γ Σ D e T₁ ε₁ →
      HasTypeFull ((y, T₁) :: Γ) Σ D h T₂ ε₂ →
      HasTypeFull Γ Σ D (.handle e y h) T₂ (ε₁.join ε₂)

  /-- Require a capability
      Γ; Σ; D ⊢ e : T, εₑ
      ─────────────────────────────────────────
      Γ; Σ; D ⊢ require eff in e : T, eff ⊔ εₑ -/
  | require : HasTypeFull Γ Σ D e T εₑ →
      HasTypeFull Γ Σ D (.require eff e) T (eff.join εₑ)

  /-- Grant a capability
      Γ; Σ; D ⊢ e : T, εₑ
      ─────────────────────────────────
      Γ; Σ; D ⊢ grant eff to e : T, εₑ -/
  | grant : HasTypeFull Γ Σ D e T εₑ →
      HasTypeFull Γ Σ D (.grant eff e) T εₑ

  /-- Classify a value as secret
      Γ; Σ; D ⊢ e : T, ε
      ──────────────────────────────────
      Γ; Σ; D ⊢ classify e : Secret[T], ε -/
  | classify : HasTypeFull Γ Σ D e T ε →
      HasTypeFull Γ Σ D (.classify e) (.secret T) ε

  /-- Declassify a secret value with proof
      Γ; Σ; D ⊢ e₁ : Secret[T], ε₁    Γ; Σ; D ⊢ e₂ : Proof[Secret[T]], ε₂
      declass_ok e₁ e₂
      ─────────────────────────────────────────────────────────────────────
      Γ; Σ; D ⊢ declassify e₁ e₂ : T, ε₁ ⊔ ε₂ -/
  | declassify : HasTypeFull Γ Σ D e₁ (.secret T) ε₁ →
      HasTypeFull Γ Σ D e₂ (.proof (.secret T)) ε₂ →
      DeclassOk e₁ e₂ →
      HasTypeFull Γ Σ D (.declassify e₁ e₂) T (ε₁.join ε₂)

  /-- Create a proof
      Γ; Σ; D ⊢ e : T, ε
      ───────────────────────────────
      Γ; Σ; D ⊢ prove e : Proof[T], ε -/
  | prove : HasTypeFull Γ Σ D e T ε →
      HasTypeFull Γ Σ D (.prove e) (.proof T) ε

/-! ## Effect Safety Theorem -/

/-- Effect Safety: Well-typed expressions perform only their declared effects
    (matches Coq: Theorem effect_safety) -/
theorem effectSafety (Γ : TypeEnv) (Σ : StoreTy) (D : SecurityLevel)
    (e : Expr) (T : Ty) (ε : Effect)
    (hty : HasTypeFull Γ Σ D e T ε) :
    performsWithin e ε := by
  induction hty with
  | core hcore =>
      exact coreEffectsWithin _ _ _ _ _ _ hcore
  | perform _ ih =>
      simp [performsWithin]
      constructor
      · exact effectJoin_ub_r _ _
      · exact performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih
  | handle _ _ ih1 ih2 =>
      simp [performsWithin]
      constructor
      · exact performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1
      · exact performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2
  | require _ ih =>
      simp [performsWithin]
      exact performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih
  | grant _ ih =>
      simp [performsWithin]
      exact ih
  | classify _ ih =>
      simp [performsWithin]
      exact ih
  | declassify _ _ _ ih1 ih2 =>
      simp [performsWithin]
      constructor
      · exact performsWithin_mono _ _ _ (effectJoin_ub_l _ _) ih1
      · exact performsWithin_mono _ _ _ (effectJoin_ub_r _ _) ih2
  | prove _ ih =>
      simp [performsWithin]
      exact ih

end RIINA

/-!
## Verification Summary

This file ports EffectSystem.v (325 lines Coq) to Lean 4.

| Coq Lemma | Lean Theorem | Status |
|-----------|--------------|--------|
| performs_within | performsWithin | ✅ Definition |
| performs_within_mono | performsWithin_mono | ✅ Proved |
| effect_leq_join_ub_l_trans | effectLeq_join_ub_l_trans | ✅ Proved |
| effect_leq_join_ub_r_trans | effectLeq_join_ub_r_trans | ✅ Proved |
| core_effects_within | coreEffectsWithin | ✅ Proved |
| has_type_full | HasTypeFull | ✅ Defined |
| effect_safety | effectSafety | ✅ Proved |

Total: 7 definitions/theorems ported — ALL PROVED (0 unfinished)

coreEffectsWithin proved by 26-case induction on HasType using
performsWithin_mono and effectJoin upper bound lemmas.
-/
