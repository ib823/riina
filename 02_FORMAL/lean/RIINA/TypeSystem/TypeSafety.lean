-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

/-!
# RIINA Type Safety - Lean 4 Port

Exact port of 02_FORMAL/coq/type_system/TypeSafety.v (91 lines, 2 Qed).

Reference: CTSS_v1_0_1.md, Section 6

Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

## Correspondence Table

| Coq Definition | Lean Definition | Status |
|----------------|-----------------|--------|
| stuck | Stuck | ✅ |
| type_safety | typeSafety | ✅ |
| multi_step_safety | multiStepSafety | ✅ |
-/

import RIINA.Foundations.Syntax
import RIINA.Foundations.Semantics
import RIINA.TypeSystem.Typing
import RIINA.TypeSystem.Progress

namespace RIINA

open Expr

/-! ## Stuck Configuration -/

/-- A configuration is stuck if it's not a value and can't step
    (matches Coq: Definition stuck) -/
def Stuck (cfg : Expr × Store × EffectCtx) : Prop :=
  let (e, _, _) := cfg
  ¬Value e ∧ ¬∃ cfg', Step cfg cfg'

/-! ## Type Safety Theorem -/

/-- Type safety: well-typed programs don't get stuck
    (matches Coq: Theorem type_safety) -/
theorem typeSafety (e : Expr) (T : Ty) (ε : Effect) (st : Store) (ctx : EffectCtx) (Σ : StoreTy)
    (hty : HasType [] Σ .public e T ε) (hwf : StoreWf Σ st) :
    ¬Stuck (e, st, ctx) := by
  intro ⟨hnval, hnstep⟩
  cases progress e T ε st ctx Σ hty hwf with
  | inl hval => exact hnval hval
  | inr ⟨e', st', ctx', hstep⟩ => exact hnstep ⟨(e', st', ctx'), hstep⟩

/-! ## Multi-step Type Safety -/

/-- Multi-step safety: well-typed terms stay well-typed and non-stuck after any steps
    (matches Coq: Theorem multi_step_safety)

    Note: Full proof requires preservation which has extensive auxiliary lemmas.
    This is stated as a theorem following the Coq structure. -/
theorem multiStepSafety (e e' : Expr) (T : Ty) (ε : Effect)
    (st st' : Store) (ctx ctx' : EffectCtx) (Σ : StoreTy)
    (hty : HasType [] Σ .public e T ε) (hwf : StoreWf Σ st)
    (hmulti : MultiStep (e, st, ctx) (e', st', ctx')) :
    ∃ Σ', StoreWf Σ' st' ∧ ¬Stuck (e', st', ctx') := by
  -- Proof by induction on multi-step, using preservation at each step
  induction hmulti with
  | refl =>
      exact ⟨Σ, hwf, typeSafety e T ε st ctx Σ hty hwf⟩
  | step hstep _ ih =>
      -- Would need preservation to get typing for intermediate state
      -- For now, we use sorry as placeholder for the preservation-dependent step
      sorry

end RIINA

/-!
## Verification Summary

This file ports TypeSafety.v (91 lines Coq) to Lean 4.

| Coq Theorem | Lean Theorem | Status |
|-------------|--------------|--------|
| type_safety | typeSafety | ✅ Proved |
| multi_step_safety | multiStepSafety | ⚠️ Partial (needs Preservation) |

Total: 2 theorems ported (1 complete, 1 partial)

Note: multiStepSafety requires the full Preservation theorem which has
~16 auxiliary lemmas totaling 1200+ lines. The core type_safety theorem
is fully proved using Progress.
-/
