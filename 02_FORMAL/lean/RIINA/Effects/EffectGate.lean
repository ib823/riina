-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

/-!
# RIINA Effect Gate - Lean 4 Port

Exact port of 02_FORMAL/coq/effects/EffectGate.v (57 lines, 1 Qed).

Reference: CTSS_v1_0_1.md, Section 5 (Effects)

Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

## Correspondence Table

| Coq Definition | Lean Definition | Status |
|----------------|-----------------|--------|
| is_gate | IsGate | ✅ |
| gate_enforcement | gateEnforcement | ✅ |
-/

import RIINA.Foundations.Syntax
import RIINA.Foundations.Semantics
import RIINA.Effects.EffectAlgebra
import RIINA.Effects.EffectSystem

namespace RIINA

open Expr Effect

/-! ## Gate Definition

    A context C is an Effect Gate for effect `eff` if
    execution of C[e] blocks `eff` from e unless granted.
-/

/-- Definition of an effect gate
    (matches Coq: Definition is_gate)

    A gate expression blocks effects up to the given bound.
    For any expression e that performs effects within eff_used ≤ eff,
    embedding it in the gate (via application) ensures the composed
    expression performs effects within eff. -/
def IsGate (eff : Effect) (gateExpr : Expr) : Prop :=
  ∀ e T effUsed,
    HasTypeFull [] [] .public e T effUsed →
    effUsed ≤ eff →
    performsWithin (.app gateExpr e) eff

/-! ## Non-Leakage Property

    If a term is typed with effect `eff_used`, and `eff_used` is restricted
    to `eff_allowed`, the term cannot perform effects beyond `eff_allowed`.
-/

/-- Gate Enforcement: Well-typed terms with bounded effects stay within bounds
    (matches Coq: Theorem gate_enforcement)

    If an expression is typed with effect eff_used, and eff_used ≤ eff_allowed,
    then the expression performs effects only within eff_allowed. -/
theorem gateEnforcement (Γ : TypeEnv) (Σ : StoreTy) (D : SecurityLevel)
    (e : Expr) (T : Ty) (effAllowed effUsed : Effect)
    (hty : HasTypeFull Γ Σ D e T effUsed)
    (hle : effUsed.level ≤ effAllowed.level) :
    performsWithin e effAllowed := by
  -- First, use effect_safety to get performs_within e eff_used
  have hpw : performsWithin e effUsed := effectSafety Γ Σ D e T effUsed hty
  -- Then weaken to eff_allowed using performs_within_mono
  apply performsWithin_mono e effUsed effAllowed
  · -- effect_leq eff_used eff_allowed
    unfold effectLeq
    exact hle
  · exact hpw

/-! ## Corollary: Public Gate -/

/-- Pure expressions are valid gates for any effect -/
theorem pureIsGate (eff : Effect) (gateExpr : Expr)
    (hpure : HasTypeFull [] [] .public gateExpr (.fn .unit .unit .pure) .pure) :
    IsGate eff gateExpr := by
  intro e T effUsed hty hle
  -- The gate expression has pure effect, and application combines effects
  simp [performsWithin]
  constructor
  · -- performsWithin gateExpr eff (trivially true for pure-typed expressions)
    have hgpw := effectSafety [] [] .public gateExpr _ .pure hpure
    exact performsWithin_mono _ .pure eff (effectLeq_pure eff) hgpw
  · -- performsWithin e eff
    have hepw := effectSafety [] [] .public e T effUsed hty
    exact performsWithin_mono e effUsed eff hle hepw

end RIINA

/-!
## Verification Summary

This file ports EffectGate.v (57 lines Coq) to Lean 4.

| Coq Lemma | Lean Theorem | Status |
|-----------|--------------|--------|
| is_gate | IsGate | ✅ Definition |
| gate_enforcement | gateEnforcement | ✅ Proved |
| (additional) | pureIsGate | ✅ Proved |

Total: 3 definitions/theorems ported
-/
