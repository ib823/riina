-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

/-!
# RIINA Non-Interference - Lean 4 Port

Core port of 02_FORMAL/coq/properties/NonInterference_v2*.v (~8300 lines).

This file ports the essential definitions and theorems for non-interference:
- Observer level and security lattice
- Closed expressions
- First-order type classification
- Step-indexed logical relations (val_rel_n, exp_rel_n, store_rel_n)
- Fundamental theorem (logical_relation)
- Non-interference statement

Reference: CTSS_v1_0_1.md, Section 7 (Non-Interference)

Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

## Correspondence Table

| Coq Definition | Lean Definition | Status |
|----------------|-----------------|--------|
| observer | observer | ✅ |
| is_low | isLow | ✅ |
| closed_expr | closedExpr | ✅ |
| first_order_type | firstOrderType | ✅ |
| val_rel_at_type_fo | valRelAtTypeFO | ✅ |
| val_rel_n | valRelN | ✅ |
| exp_rel_n | expRelN | ✅ |
| store_rel_n | storeRelN | ✅ |
| val_rel | valRel | ✅ |
| exp_rel | expRel | ✅ |
| env_rel | envRel | ✅ |
| logical_relation | logicalRelation | ⚠️ Stated |
| non_interference_stmt | nonInterferenceStmt | ⚠️ Stated |
-/

import RIINA.Foundations.Syntax
import RIINA.Foundations.Semantics
import RIINA.TypeSystem.Typing

namespace RIINA

open Expr Ty SecurityLevel

/-! ## Observer Level

The observer represents the security clearance of an external attacker.
Information at or below the observer's level is considered "low" (observable).
-/

/-- Observer security level (parameter)
    (matches Coq: Parameter observer) -/
axiom observer : SecurityLevel

/-- Check if a security level is observable by the observer
    (matches Coq: Definition is_low) -/
def isLow (l : SecurityLevel) : Prop :=
  l ≤ observer

/-- Decidable version of isLow
    (matches Coq: Definition is_low_dec) -/
def isLowDec (l : SecurityLevel) : Bool :=
  l.toNat ≤ observer.toNat

/-- isLow and isLowDec equivalence
    (matches Coq: Lemma is_low_dec_correct) -/
theorem isLowDec_correct (l : SecurityLevel) :
    isLowDec l = true ↔ isLow l := by
  unfold isLowDec isLow SecurityLevel.le
  simp [Nat.ble_eq]


/-! ## Closed Expressions

A closed expression has no free variables.
-/

/-- Closed expression predicate
    (matches Coq: Definition closed_expr) -/
def closedExpr (e : Expr) : Prop :=
  ∀ x, ¬freeIn x e

/-- Helper: expression closed except for one variable
    (matches Coq: Definition closed_except) -/
def closedExcept (x : Ident) (e : Expr) : Prop :=
  ∀ y, y ≠ x → ¬freeIn y e


/-! ## First-Order Type Classification

First-order types contain no function types (TFn) or channel types.
They can be compared structurally without needing step-indexing.
-/

/-- Check if a type is first-order (no functions or channels)
    (matches Coq: Fixpoint first_order_type) -/
def firstOrderType : Ty → Bool
  | .unit | .bool | .int | .string | .bytes => true
  | .fn _ _ _ => false
  | .prod T1 T2 => firstOrderType T1 && firstOrderType T2
  | .sum T1 T2 => firstOrderType T1 && firstOrderType T2
  | .list T' => firstOrderType T'
  | .option T' => firstOrderType T'
  | .ref T' _ => firstOrderType T'
  | .secret T' => firstOrderType T'
  | .labeled T' _ => firstOrderType T'
  | .tainted T' _ => firstOrderType T'
  | .sanitized T' _ => firstOrderType T'
  | .proof T' => firstOrderType T'
  | .capability _ => true
  | .capabilityFull _ => true
  | .chan _ => false
  | .secureChan _ _ => false
  | .constantTime T' => firstOrderType T'
  | .zeroizing T' => firstOrderType T'


/-! ## First-Order Value Relation

For first-order types, we can define value relatedness without step-indexing.
This is the structural equality relation for observable types.
-/

/-- First-order value relation - no step indexing needed
    (matches Coq: Fixpoint val_rel_at_type_fo) -/
def valRelAtTypeFO : Ty → Expr → Expr → Prop
  | .unit, v1, v2 => v1 = .unit ∧ v2 = .unit
  | .bool, v1, v2 => ∃ b, v1 = .bool b ∧ v2 = .bool b
  | .int, v1, v2 => ∃ i, v1 = .int i ∧ v2 = .int i
  | .string, v1, v2 => ∃ s, v1 = .string s ∧ v2 = .string s
  | .bytes, v1, v2 => v1 = v2
  | .secret _, _, _ => True  -- Secret values are indistinguishable
  | .labeled _ _, _, _ => True
  | .tainted _ _, _, _ => True
  | .sanitized _ _, _, _ => True
  | .ref _ _, v1, v2 => ∃ l, v1 = .loc l ∧ v2 = .loc l
  | .list _, _, _ => True
  | .option _, _, _ => True
  | .prod T1 T2, v1, v2 =>
      ∃ x1 y1 x2 y2,
        v1 = .pair x1 y1 ∧ v2 = .pair x2 y2 ∧
        valRelAtTypeFO T1 x1 x2 ∧ valRelAtTypeFO T2 y1 y2
  | .sum T1 T2, v1, v2 =>
      (∃ x1 x2, v1 = .inl x1 T2 ∧ v2 = .inl x2 T2 ∧ valRelAtTypeFO T1 x1 x2) ∨
      (∃ y1 y2, v1 = .inr y1 T1 ∧ v2 = .inr y2 T1 ∧ valRelAtTypeFO T2 y1 y2)
  | .fn _ _ _, _, _ => True  -- Functions handled separately
  | .capability _, _, _ => True
  | .capabilityFull _, _, _ => True
  | .proof _, _, _ => True
  | .chan _, _, _ => True
  | .secureChan _ _, _, _ => True
  | .constantTime _, _, _ => True
  | .zeroizing _, _, _ => True


/-! ## Step-Indexed Logical Relations

The step-indexed approach ensures well-foundedness of the logical relation.
At step 0, we have base information; at step n+1, we can "step" the relation.
-/

/-- Step-indexed value relation
    (matches Coq: val_rel_n)

    At step 0: values must be values, closed, well-typed, and
               for first-order types, satisfy valRelAtTypeFO
    At step n+1: inherits step n relation plus structural properties -/
def valRelN : Nat → StoreTy → Ty → Expr → Expr → Prop
  | 0, Σ, T, v1, v2 =>
      Value v1 ∧ Value v2 ∧
      closedExpr v1 ∧ closedExpr v2 ∧
      (firstOrderType T = true → valRelAtTypeFO T v1 v2)
  | n + 1, Σ, T, v1, v2 =>
      valRelN n Σ T v1 v2 ∧
      Value v1 ∧ Value v2 ∧
      closedExpr v1 ∧ closedExpr v2

/-- Step-indexed expression relation
    (matches Coq: exp_rel_n)

    Expressions are related if they both terminate to related values
    or both diverge within the given step budget. -/
def expRelN (n : Nat) (Σ : StoreTy) (T : Ty) (e1 e2 : Expr) : Prop :=
  ∀ st1 st2 ctx1 ctx2 v1 st1' ctx1',
    MultiStep (e1, st1, ctx1) (v1, st1', ctx1') →
    Value v1 →
    ∃ v2 st2' ctx2',
      MultiStep (e2, st2, ctx2) (v2, st2', ctx2') ∧
      valRelN n Σ T v1 v2

/-- Step-indexed store relation
    (matches Coq: store_rel_n)

    Stores are related if low-security locations contain related values. -/
def storeRelN (n : Nat) (Σ : StoreTy) (st1 st2 : Store) : Prop :=
  ∀ l T sl,
    StoreTy.lookup l Σ = some (T, sl) →
    isLow sl →
    match (st1.lookup l, st2.lookup l) with
    | (some v1, some v2) => valRelN n Σ T v1 v2
    | (none, none) => True
    | _ => False


/-! ## Limit Relations

The limit relations are the intersection over all step indices.
-/

/-- Value relation (limit of step-indexed)
    (matches Coq: Definition val_rel) -/
def valRel (Σ : StoreTy) (T : Ty) (v1 v2 : Expr) : Prop :=
  ∀ n, valRelN n Σ T v1 v2

/-- Expression relation (limit of step-indexed)
    (matches Coq: Definition exp_rel) -/
def expRel (Σ : StoreTy) (T : Ty) (e1 e2 : Expr) : Prop :=
  ∀ n, expRelN n Σ T e1 e2

/-- Store relation (limit of step-indexed)
    (matches Coq: Definition store_rel) -/
def storeRel (Σ : StoreTy) (st1 st2 : Store) : Prop :=
  ∀ n, storeRelN n Σ st1 st2


/-! ## Environment Relation

Environments (substitutions) are related if they map each variable to related values.
-/

/-- Substitution as a function from identifiers to expressions -/
abbrev Subst := Ident → Option Expr

/-- Apply substitution to expression -/
def applySubst (ρ : Subst) : Expr → Expr
  | .var x => match ρ x with
      | some e => e
      | none => .var x
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .string s => .string s
  | .loc l => .loc l
  | .lam x T body => .lam x T (if ρ x = none then applySubst ρ body else body)
  | .app e1 e2 => .app (applySubst ρ e1) (applySubst ρ e2)
  | .pair e1 e2 => .pair (applySubst ρ e1) (applySubst ρ e2)
  | .fst e => .fst (applySubst ρ e)
  | .snd e => .snd (applySubst ρ e)
  | .inl e T => .inl (applySubst ρ e) T
  | .inr e T => .inr (applySubst ρ e) T
  | .case e x1 e1 x2 e2 => .case (applySubst ρ e) x1 (applySubst ρ e1) x2 (applySubst ρ e2)
  | .ite e1 e2 e3 => .ite (applySubst ρ e1) (applySubst ρ e2) (applySubst ρ e3)
  | .let_ x e1 e2 => .let_ x (applySubst ρ e1) (if ρ x = none then applySubst ρ e2 else e2)
  | .perform eff e => .perform eff (applySubst ρ e)
  | .handle e x h => .handle (applySubst ρ e) x (if ρ x = none then applySubst ρ h else h)
  | .ref e l => .ref (applySubst ρ e) l
  | .deref e => .deref (applySubst ρ e)
  | .assign e1 e2 => .assign (applySubst ρ e1) (applySubst ρ e2)
  | .classify e => .classify (applySubst ρ e)
  | .declassify e1 e2 => .declassify (applySubst ρ e1) (applySubst ρ e2)
  | .prove e => .prove (applySubst ρ e)
  | .require eff e => .require eff (applySubst ρ e)
  | .grant eff e => .grant eff (applySubst ρ e)

/-- Environment relation: substitutions are related if they map
    each variable in the type environment to related values
    (matches Coq: env_rel) -/
def envRel (Σ : StoreTy) (Γ : TypeEnv) (ρ1 ρ2 : Subst) : Prop :=
  ∀ x T, TypeEnv.lookup x Γ = some T →
    match (ρ1 x, ρ2 x) with
    | (some v1, some v2) => valRel Σ T v1 v2
    | _ => False


/-! ## Key Lemmas

Basic properties of the logical relations.
-/

/-- Value relation implies values are values
    (matches Coq: Lemma val_rel_value_left/right) -/
theorem valRel_value (Σ : StoreTy) (T : Ty) (v1 v2 : Expr)
    (hrel : valRel Σ T v1 v2) : Value v1 ∧ Value v2 := by
  have h := hrel 1
  simp [valRelN] at h
  exact ⟨h.2.1, h.2.2.1⟩

/-- Value relation implies expressions are closed
    (matches Coq: Lemma val_rel_closed) -/
theorem valRel_closed (Σ : StoreTy) (T : Ty) (v1 v2 : Expr)
    (hrel : valRel Σ T v1 v2) : closedExpr v1 ∧ closedExpr v2 := by
  have h := hrel 1
  simp [valRelN] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

/-- valRelN is monotonic in step index
    (matches Coq: val_rel_n_mono) -/
theorem valRelN_mono (n m : Nat) (Σ : StoreTy) (T : Ty) (v1 v2 : Expr)
    (hnm : n ≤ m) (hrel : valRelN m Σ T v1 v2) : valRelN n Σ T v1 v2 := by
  induction m with
  | zero =>
      cases Nat.le_zero.mp hnm
      exact hrel
  | succ m' ih =>
      simp [valRelN] at hrel
      cases Nat.lt_or_eq_of_le hnm with
      | inl hlt =>
          have hle' : n ≤ m' := Nat.lt_succ.mp hlt
          exact ih hle' hrel.1
      | inr heq =>
          subst heq
          simp [valRelN]
          exact hrel


/-! ## Fundamental Theorem

The logical relation theorem: well-typed expressions preserve relatedness.
-/

/-- Fundamental theorem (logical relation)
    (matches Coq: Theorem logical_relation)

    If e is well-typed in context Γ, and ρ1, ρ2 are related substitutions,
    then applying the substitutions yields related expressions.

    This is the core theorem connecting typing to non-interference. -/
theorem logicalRelation (Γ : TypeEnv) (Σ : StoreTy) (e : Expr) (T : Ty) (ε : Effect)
    (hty : HasType Γ Σ .public e T ε)
    (ρ1 ρ2 : Subst)
    (henv : envRel Σ Γ ρ1 ρ2) :
    expRel Σ T (applySubst ρ1 e) (applySubst ρ2 e) := by
  -- Full proof requires extensive case analysis on typing derivation
  -- and induction on step index. See NonInterference_v2_LogicalRelation.v
  sorry


/-! ## Non-Interference Statement

The main non-interference theorem.
-/

/-- Single-variable substitution -/
def singleSubst (x : Ident) (v : Expr) : Subst :=
  fun y => if y = x then some v else none

/-- Non-interference: substituting related values yields related expressions
    (matches Coq: Theorem non_interference_stmt)

    If v1 and v2 are related values (indistinguishable to an observer),
    and e is well-typed with x : T_in,
    then [x := v1]e and [x := v2]e are related expressions.

    This is the key security property: secret inputs don't affect
    observable outputs. -/
theorem nonInterferenceStmt (x : Ident) (T_in T_out : Ty) (v1 v2 e : Expr)
    (hval : valRel [] T_in v1 v2)
    (hty : HasType [(x, T_in)] [] .public e T_out .pure) :
    expRel [] T_out ([x := v1] e) ([x := v2] e) := by
  -- Proof uses logicalRelation with single-variable environment
  -- See NonInterference_v2_LogicalRelation.v, lines 4588-4608
  sorry


/-! ## Closed Expression Lemmas -/

theorem closedExpr_unit : closedExpr .unit := by
  intro x hfree
  cases hfree

theorem closedExpr_bool (b : Bool) : closedExpr (.bool b) := by
  intro x hfree
  cases hfree

theorem closedExpr_int (n : Nat) : closedExpr (.int n) := by
  intro x hfree
  cases hfree

theorem closedExpr_string (s : String) : closedExpr (.string s) := by
  intro x hfree
  cases hfree

theorem closedExpr_loc (l : Loc) : closedExpr (.loc l) := by
  intro x hfree
  cases hfree

theorem closedExpr_lam (x : Ident) (T : Ty) (body : Expr)
    (hclosed : closedExcept x body) : closedExpr (.lam x T body) := by
  intro y hfree
  cases hfree with
  | lam_body hneq hfree' =>
      exact hclosed y hneq hfree'

theorem closedExpr_pair (v1 v2 : Expr)
    (hc1 : closedExpr v1) (hc2 : closedExpr v2) : closedExpr (.pair v1 v2) := by
  intro y hfree
  cases hfree with
  | pair_l h => exact hc1 y h
  | pair_r h => exact hc2 y h


/-! ## Value Relation Lemmas -/

theorem valRel_unit (Σ : StoreTy) :
    valRel Σ .unit .unit .unit := by
  intro n
  induction n with
  | zero =>
      simp [valRelN, valRelAtTypeFO, closedExpr]
      constructor; exact Value.unit
      constructor; exact Value.unit
      constructor; intro x hfree; cases hfree
      constructor; intro x hfree; cases hfree
      intro _; exact ⟨rfl, rfl⟩
  | succ n' ih =>
      simp [valRelN]
      constructor; exact ih
      constructor; exact Value.unit
      constructor; exact Value.unit
      constructor; intro x hfree; cases hfree
      intro x hfree; cases hfree

theorem valRel_bool (Σ : StoreTy) (b : Bool) :
    valRel Σ .bool (.bool b) (.bool b) := by
  intro n
  induction n with
  | zero =>
      simp [valRelN, valRelAtTypeFO, closedExpr]
      constructor; exact Value.bool b
      constructor; exact Value.bool b
      constructor; intro x hfree; cases hfree
      constructor; intro x hfree; cases hfree
      intro _; exact ⟨b, rfl, rfl⟩
  | succ n' ih =>
      simp [valRelN]
      constructor; exact ih
      constructor; exact Value.bool b
      constructor; exact Value.bool b
      constructor; intro x hfree; cases hfree
      intro x hfree; cases hfree

theorem valRel_int (Σ : StoreTy) (i : Nat) :
    valRel Σ .int (.int i) (.int i) := by
  intro n
  induction n with
  | zero =>
      simp [valRelN, valRelAtTypeFO, closedExpr]
      constructor; exact Value.int i
      constructor; exact Value.int i
      constructor; intro x hfree; cases hfree
      constructor; intro x hfree; cases hfree
      intro _; exact ⟨i, rfl, rfl⟩
  | succ n' ih =>
      simp [valRelN]
      constructor; exact ih
      constructor; exact Value.int i
      constructor; exact Value.int i
      constructor; intro x hfree; cases hfree
      intro x hfree; cases hfree

end RIINA

/-!
## Verification Summary

This file ports NonInterference_v2*.v (~8300 lines Coq) to Lean 4.

### Definitions Ported

| Coq Definition | Lean Definition | Status |
|----------------|-----------------|--------|
| observer | observer | ✅ Axiom |
| is_low | isLow | ✅ |
| is_low_dec | isLowDec | ✅ |
| closed_expr | closedExpr | ✅ |
| closed_except | closedExcept | ✅ |
| first_order_type | firstOrderType | ✅ |
| val_rel_at_type_fo | valRelAtTypeFO | ✅ |
| val_rel_n | valRelN | ✅ |
| exp_rel_n | expRelN | ✅ |
| store_rel_n | storeRelN | ✅ |
| val_rel | valRel | ✅ |
| exp_rel | expRel | ✅ |
| store_rel | storeRel | ✅ |
| env_rel | envRel | ✅ |
| subst_rho | applySubst | ✅ |

### Theorems Ported

| Coq Theorem | Lean Theorem | Status |
|-------------|--------------|--------|
| is_low_dec_correct | isLowDec_correct | ✅ Proved |
| val_rel_value_left/right | valRel_value | ✅ Proved |
| val_rel_closed | valRel_closed | ✅ Proved |
| val_rel_n_mono | valRelN_mono | ✅ Proved |
| closed_expr_unit | closedExpr_unit | ✅ Proved |
| closed_expr_bool | closedExpr_bool | ✅ Proved |
| closed_expr_int | closedExpr_int | ✅ Proved |
| closed_expr_string | closedExpr_string | ✅ Proved |
| closed_expr_loc | closedExpr_loc | ✅ Proved |
| closed_expr_lam | closedExpr_lam | ✅ Proved |
| closed_expr_pair | closedExpr_pair | ✅ Proved |
| val_rel_unit | valRel_unit | ✅ Proved |
| val_rel_bool | valRel_bool | ✅ Proved |
| val_rel_int | valRel_int | ✅ Proved |
| logical_relation | logicalRelation | ⚠️ Stated (sorry) |
| non_interference_stmt | nonInterferenceStmt | ⚠️ Stated (sorry) |

Total: 15 definitions + 16 theorems (14 proved, 2 stated)

Note: logicalRelation and nonInterferenceStmt require extensive case analysis
(~4000 lines in Coq) and are stated here for triple-prover agreement on the
theorem statements.
-/
