-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

/-!
# RIINA Effect Algebra - Lean 4 Port

Exact port of 02_FORMAL/coq/effects/EffectAlgebra.v (108 lines, 8 Qed).

Reference: CTSS_v1_0_1.md, Section 5 (Effects)

Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

## Correspondence Table

| Coq Definition | Lean Definition | Status |
|----------------|-----------------|--------|
| effect_leq | effectLeq | ✅ |
| effect_leq_refl | effectLeq_refl | ✅ |
| effect_leq_trans | effectLeq_trans | ✅ |
| effect_leq_antisym | effectLeq_antisym | ✅ |
| effect_join_comm | effectJoin_comm | ✅ |
| effect_level_join | effectLevel_join | ✅ |
| effect_join_assoc | effectJoin_assoc | ✅ |
| effect_join_ub_l | effectJoin_ub_l | ✅ |
| effect_join_ub_r | effectJoin_ub_r | ✅ |
| effect_join_lub | effectJoin_lub | ✅ |
-/

import RIINA.Foundations.Syntax

namespace RIINA

open Effect

/-! ## Effect Ordering -/

/-- Effect ordering based on levels
    (matches Coq: Definition effect_leq) -/
def effectLeq (e1 e2 : Effect) : Prop :=
  e1.level ≤ e2.level

instance : LE Effect where
  le := effectLeq

/-! ## Partial Order Properties -/

/-- Reflexivity of effect ordering
    (matches Coq: Lemma effect_leq_refl) -/
theorem effectLeq_refl (e : Effect) : e ≤ e := by
  unfold effectLeq
  exact Nat.le_refl _

/-- Transitivity of effect ordering
    (matches Coq: Lemma effect_leq_trans) -/
theorem effectLeq_trans (e1 e2 e3 : Effect)
    (h1 : e1 ≤ e2) (h2 : e2 ≤ e3) : e1 ≤ e3 := by
  unfold effectLeq at *
  exact Nat.le_trans h1 h2

/-- Helper: effect level determines effect equality
    Effects with equal levels are equal -/
theorem effect_eq_of_level_eq (e1 e2 : Effect)
    (h : e1.level = e2.level) : e1 = e2 := by
  cases e1 <;> cases e2 <;> simp [level] at h <;> try rfl <;> try omega

/-- Antisymmetry of effect ordering
    (matches Coq: Lemma effect_leq_antisym) -/
theorem effectLeq_antisym (e1 e2 : Effect)
    (h1 : e1 ≤ e2) (h2 : e2 ≤ e1) : e1 = e2 := by
  unfold effectLeq at *
  have heq : e1.level = e2.level := Nat.le_antisymm h1 h2
  exact effect_eq_of_level_eq e1 e2 heq

/-! ## Join Semilattice Properties -/

/-- Effect level of join is max of levels
    (matches Coq: Lemma effect_level_join) -/
theorem effectLevel_join (e1 e2 : Effect) :
    (e1.join e2).level = max e1.level e2.level := by
  simp [join]
  split
  · -- e1.level < e2.level case
    rename_i h
    have hlt : e1.level < e2.level := h
    omega
  · -- e1.level ≥ e2.level case
    rename_i h
    have hge : ¬(e1.level < e2.level) := h
    omega

/-- Commutativity of effect join
    (matches Coq: Lemma effect_join_comm) -/
theorem effectJoin_comm (e1 e2 : Effect) :
    e1.join e2 = e2.join e1 := by
  apply effect_eq_of_level_eq
  simp only [effectLevel_join]
  omega

/-- Associativity of effect join
    (matches Coq: Lemma effect_join_assoc) -/
theorem effectJoin_assoc (e1 e2 e3 : Effect) :
    e1.join (e2.join e3) = (e1.join e2).join e3 := by
  apply effect_eq_of_level_eq
  simp only [effectLevel_join]
  omega

/-- Left upper bound of join
    (matches Coq: Lemma effect_join_ub_l) -/
theorem effectJoin_ub_l (e1 e2 : Effect) : e1 ≤ e1.join e2 := by
  unfold effectLeq
  simp [join]
  split
  · rename_i h; omega
  · exact Nat.le_refl _

/-- Right upper bound of join
    (matches Coq: Lemma effect_join_ub_r) -/
theorem effectJoin_ub_r (e1 e2 : Effect) : e2 ≤ e1.join e2 := by
  unfold effectLeq
  simp [join]
  split
  · exact Nat.le_refl _
  · rename_i h; omega

/-- Join is least upper bound
    (matches Coq: Lemma effect_join_lub) -/
theorem effectJoin_lub (e1 e2 e3 : Effect)
    (h1 : e1 ≤ e3) (h2 : e2 ≤ e3) : e1.join e2 ≤ e3 := by
  unfold effectLeq at *
  simp [join]
  split
  · exact h2
  · exact h1

/-! ## Additional Properties -/

/-- Pure is bottom element
    (matches Coq: Lemma effect_leq_pure in EffectSystem.v) -/
theorem effectLeq_pure (e : Effect) : .pure ≤ e := by
  unfold effectLeq
  simp [level]
  exact Nat.zero_le _

end RIINA

/-!
## Verification Summary

This file ports EffectAlgebra.v (108 lines Coq) to Lean 4.

| Coq Lemma | Lean Theorem | Status |
|-----------|--------------|--------|
| effect_leq_refl | effectLeq_refl | ✅ Proved |
| effect_leq_trans | effectLeq_trans | ✅ Proved |
| effect_leq_antisym | effectLeq_antisym | ✅ Proved |
| effect_join_comm | effectJoin_comm | ✅ Proved |
| effect_level_join | effectLevel_join | ✅ Proved |
| effect_join_assoc | effectJoin_assoc | ✅ Proved |
| effect_join_ub_l | effectJoin_ub_l | ✅ Proved |
| effect_join_ub_r | effectJoin_ub_r | ✅ Proved |
| effect_join_lub | effectJoin_lub | ✅ Proved |
| effect_leq_pure | effectLeq_pure | ✅ Proved |

Total: 10 theorems ported (vs 8 in Coq + 1 from EffectSystem.v)
-/
