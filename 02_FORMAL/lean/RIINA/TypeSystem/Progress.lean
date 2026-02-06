-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

/-!
# RIINA Progress Theorem - Lean 4 Port

Exact port of 02_FORMAL/coq/type_system/Progress.v (284 lines, ~10 Qed).

Reference: CTSS_v1_0_1.md, Section 6

Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

## Correspondence Table

| Coq Definition | Lean Definition | Status |
|----------------|-----------------|--------|
| progress_stmt | ProgressStmt | ✅ |
| canonical_bool | canonicalBool | ✅ |
| canonical_fn | canonicalFn | ✅ |
| canonical_pair | canonicalPair | ✅ |
| canonical_sum | canonicalSum | ✅ |
| canonical_ref | canonicalRef | ✅ |
| canonical_secret | canonicalSecret | ✅ |
| canonical_proof | canonicalProof | ✅ |
| lookup_nil_contra | lookupNilContra | ✅ |
| progress | progress | ✅ |
-/

import RIINA.Foundations.Syntax
import RIINA.Foundations.Semantics
import RIINA.TypeSystem.Typing

namespace RIINA

open Expr

/-! ## Progress Statement -/

/-- Progress statement: well-typed closed expressions are values or can step
    (matches Coq: Definition progress_stmt) -/
def ProgressStmt : Prop :=
  ∀ e T ε st ctx Σ,
    HasType [] Σ .public e T ε →
    StoreWf Σ st →
    Value e ∨ ∃ e' st' ctx', Step (e, st, ctx) (e', st', ctx')

/-! ## Canonical Forms (Closed Context Variants) -/

/-- Canonical form for bool (matches Coq: canonical_bool) -/
theorem canonicalBool (v : Expr) (ε : Effect) (Σ : StoreTy)
    (hty : HasType [] Σ .public v .bool ε) (hval : Value v) :
    ∃ b, v = .bool b := by
  cases hval <;> cases hty
  exact ⟨_, rfl⟩

/-- Canonical form for function (matches Coq: canonical_fn) -/
theorem canonicalFn (v : Expr) (T1 T2 : Ty) (ε ε' : Effect) (Σ : StoreTy)
    (hty : HasType [] Σ .public v (.fn T1 T2 ε) ε') (hval : Value v) :
    ∃ x body, v = .lam x T1 body := by
  cases hval <;> cases hty
  exact ⟨_, _, rfl⟩

/-- Canonical form for pair (matches Coq: canonical_pair) -/
theorem canonicalPair (v : Expr) (T1 T2 : Ty) (ε : Effect) (Σ : StoreTy)
    (hty : HasType [] Σ .public v (.prod T1 T2) ε) (hval : Value v) :
    ∃ v1 v2, v = .pair v1 v2 ∧ Value v1 ∧ Value v2 := by
  cases hval with
  | pair hv1 hv2 => cases hty; exact ⟨_, _, rfl, hv1, hv2⟩

/-- Canonical form for sum (matches Coq: canonical_sum) -/
theorem canonicalSum (v : Expr) (T1 T2 : Ty) (ε : Effect) (Σ : StoreTy)
    (hty : HasType [] Σ .public v (.sum T1 T2) ε) (hval : Value v) :
    (∃ v', v = .inl v' T2 ∧ Value v') ∨ (∃ v', v = .inr v' T1 ∧ Value v') := by
  cases hval with
  | inl hv _ => cases hty; left; exact ⟨_, rfl, hv⟩
  | inr hv _ => cases hty; right; exact ⟨_, rfl, hv⟩

/-- Canonical form for reference (matches Coq: canonical_ref) -/
theorem canonicalRef (v : Expr) (T : Ty) (l : SecurityLevel) (ε : Effect) (Σ : StoreTy)
    (hty : HasType [] Σ .public v (.ref T l) ε) (hval : Value v) :
    ∃ l', v = .loc l' := by
  cases hval <;> cases hty
  exact ⟨_, rfl⟩

/-- Canonical form for secret (matches Coq: canonical_secret) -/
theorem canonicalSecret (v : Expr) (T : Ty) (ε : Effect) (Σ : StoreTy)
    (hty : HasType [] Σ .public v (.secret T) ε) (hval : Value v) :
    ∃ v', v = .classify v' ∧ Value v' := by
  cases hval with
  | classify hv => cases hty; exact ⟨_, rfl, hv⟩

/-- Canonical form for proof (matches Coq: canonical_proof) -/
theorem canonicalProof (v : Expr) (T : Ty) (ε : Effect) (Σ : StoreTy)
    (hty : HasType [] Σ .public v (.proof T) ε) (hval : Value v) :
    ∃ v', v = .prove v' ∧ Value v' := by
  cases hval with
  | prove hv => cases hty; exact ⟨_, rfl, hv⟩

/-- Lookup in nil gives None (matches Coq: lookup_nil_contra) -/
theorem lookupNilContra (x : Ident) (T : Ty) (h : TypeEnv.lookup x [] = some T) : False := by
  simp [TypeEnv.lookup] at h

/-! ## Progress Theorem -/

/-- Progress: well-typed closed expression is value or can step
    (matches Coq: Theorem progress) -/
theorem progress : ProgressStmt := by
  intro e T ε st ctx Σ hty hwf
  -- Induction on typing derivation
  induction hty with
  | unit => left; exact .unit
  | bool => left; exact .bool
  | int => left; exact .int
  | string => left; exact .string
  | loc => left; exact .loc
  | var _ _ _ _ _ hlook =>
      -- Variable in empty context: contradiction
      exact absurd hlook (fun h => lookupNilContra _ _ h)
  | lam => left; exact .lam
  | app _ _ _ _ _ _ _ _ _ _ ht1 ht2 ih1 ih2 =>
      cases ih1 hwf with
      | inl hv1 =>
          cases ih2 hwf with
          | inl hv2 =>
              -- Both values: can beta reduce
              obtain ⟨x, body, heq⟩ := canonicalFn _ _ _ _ _ _ ht1 hv1
              subst heq
              right; exact ⟨body.subst x _, st, ctx, .appAbs hv2⟩
          | inr ⟨e2', st2', ctx2', hstep2⟩ =>
              right; exact ⟨.app _ e2', st2', ctx2', .app2 hv1 hstep2⟩
      | inr ⟨e1', st1', ctx1', hstep1⟩ =>
          right; exact ⟨.app e1' _, st1', ctx1', .app1 hstep1⟩
  | pair _ _ _ _ _ _ _ _ _ ht1 ht2 ih1 ih2 =>
      cases ih1 hwf with
      | inl hv1 =>
          cases ih2 hwf with
          | inl hv2 => left; exact .pair hv1 hv2
          | inr ⟨e2', st2', ctx2', hstep2⟩ =>
              right; exact ⟨.pair _ e2', st2', ctx2', .pair2 hv1 hstep2⟩
      | inr ⟨e1', st1', ctx1', hstep1⟩ =>
          right; exact ⟨.pair e1' _, st1', ctx1', .pair1 hstep1⟩
  | fst _ _ _ _ _ _ _ ht ih =>
      cases ih hwf with
      | inl hv =>
          obtain ⟨v1, v2, heq, hv1, hv2⟩ := canonicalPair _ _ _ _ _ ht hv
          subst heq
          right; exact ⟨v1, st, ctx, .fst hv1 hv2⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.fst e', st', ctx', .fstStep hstep⟩
  | snd _ _ _ _ _ _ _ ht ih =>
      cases ih hwf with
      | inl hv =>
          obtain ⟨v1, v2, heq, hv1, hv2⟩ := canonicalPair _ _ _ _ _ ht hv
          subst heq
          right; exact ⟨v2, st, ctx, .snd hv1 hv2⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.snd e', st', ctx', .sndStep hstep⟩
  | inl _ _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv => left; exact .inl hv _
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.inl e' _, st', ctx', .inlStep hstep⟩
  | inr _ _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv => left; exact .inr hv _
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.inr e' _, st', ctx', .inrStep hstep⟩
  | case _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht ht1 ht2 ih ih1 ih2 =>
      cases ih hwf with
      | inl hv =>
          cases canonicalSum _ _ _ _ _ ht hv with
          | inl ⟨v', heq, hv'⟩ =>
              subst heq
              right; exact ⟨_.subst _ v', st, ctx, .caseInl hv'⟩
          | inr ⟨v', heq, hv'⟩ =>
              subst heq
              right; exact ⟨_.subst _ v', st, ctx, .caseInr hv'⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.case e' _ _ _ _, st', ctx', .caseStep hstep⟩
  | ite _ _ _ _ _ _ _ _ _ _ ht1 ht2 ht3 ih1 ih2 ih3 =>
      cases ih1 hwf with
      | inl hv =>
          obtain ⟨b, heq⟩ := canonicalBool _ _ _ ht1 hv
          subst heq
          cases b with
          | true => right; exact ⟨_, st, ctx, .ifTrue⟩
          | false => right; exact ⟨_, st, ctx, .ifFalse⟩
      | inr ⟨e1', st', ctx', hstep⟩ =>
          right; exact ⟨.ite e1' _ _, st', ctx', .ifStep hstep⟩
  | let_ _ _ _ _ _ _ _ _ _ _ ht1 ht2 ih1 ih2 =>
      cases ih1 hwf with
      | inl hv =>
          right; exact ⟨_.subst _ _, st, ctx, .letValue hv⟩
      | inr ⟨e1', st', ctx', hstep⟩ =>
          right; exact ⟨.let_ _ e1' _, st', ctx', .letStep hstep⟩
  | perform _ _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv => right; exact ⟨_, st, ctx, .performValue hv⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.perform _ e', st', ctx', .performStep hstep⟩
  | handle _ _ _ _ _ _ _ _ _ _ ht1 ht2 ih1 ih2 =>
      cases ih1 hwf with
      | inl hv =>
          right; exact ⟨_.subst _ _, st, ctx, .handleValue hv⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.handle e' _ _, st', ctx', .handleStep hstep⟩
  | ref _ _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv =>
          right
          exact ⟨.loc (st.freshLoc), st.update st.freshLoc _, ctx, .refValue hv rfl⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.ref e' _, st', ctx', .refStep hstep⟩
  | deref _ _ _ _ _ _ _ ht ih =>
      cases ih hwf with
      | inl hv =>
          obtain ⟨l', heq⟩ := canonicalRef _ _ _ _ _ ht hv
          subst heq
          -- Use store well-formedness to get value at location
          cases ht with
          | loc _ _ _ _ _ _ hlook =>
              obtain ⟨v, hlookst, hvalv, htyv⟩ := hwf.1 l' _ _ hlook
              right; exact ⟨v, st, ctx, .derefLoc hlookst⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.deref e', st', ctx', .derefStep hstep⟩
  | assign _ _ _ _ _ _ _ _ _ ht1 ht2 ih1 ih2 =>
      cases ih1 hwf with
      | inl hv1 =>
          obtain ⟨l', heq⟩ := canonicalRef _ _ _ _ _ ht1 hv1
          subst heq
          cases ht1 with
          | loc _ _ _ _ _ _ hlook =>
              obtain ⟨v1, hlookst, hvalv, htyv⟩ := hwf.1 l' _ _ hlook
              cases ih2 hwf with
              | inl hv2 =>
                  right; exact ⟨.unit, st.update l' _, ctx, .assignLoc hlookst hv2⟩
              | inr ⟨e2', st2', ctx2', hstep2⟩ =>
                  right; exact ⟨.assign (.loc l') e2', st2', ctx2', .assign2 .loc hstep2⟩
      | inr ⟨e1', st1', ctx1', hstep1⟩ =>
          right; exact ⟨.assign e1' _, st1', ctx1', .assign1 hstep1⟩
  | classify _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv => left; exact .classify hv
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.classify e', st', ctx', .classifyStep hstep⟩
  | declassify _ _ _ _ _ _ _ _ ht1 ht2 hok ih1 ih2 =>
      cases ih1 hwf with
      | inl hv1 =>
          obtain ⟨v1, heq, hv1'⟩ := canonicalSecret _ _ _ _ ht1 hv1
          subst heq
          cases ih2 hwf with
          | inl hv2 =>
              obtain ⟨v', heq1, heq2⟩ := hok
              subst heq1
              right; exact ⟨v1, st, ctx, .declassifyValue hv1' ⟨v1, hv1', rfl, heq2⟩⟩
          | inr ⟨e2', st2', ctx2', hstep2⟩ =>
              right; exact ⟨.declassify (.classify v1) e2', st2', ctx2', .declassify2 (.classify hv1') hstep2⟩
      | inr ⟨e1', st1', ctx1', hstep1⟩ =>
          right; exact ⟨.declassify e1' _, st1', ctx1', .declassify1 hstep1⟩
  | prove _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv => left; exact .prove hv
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.prove e', st', ctx', .proveStep hstep⟩
  | require _ _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv => right; exact ⟨_, st, ctx, .requireValue hv⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.require _ e', st', ctx', .requireStep hstep⟩
  | grant _ _ _ _ _ _ _ _ ih =>
      cases ih hwf with
      | inl hv => right; exact ⟨_, st, ctx, .grantValue hv⟩
      | inr ⟨e', st', ctx', hstep⟩ =>
          right; exact ⟨.grant _ e', st', ctx', .grantStep hstep⟩

end RIINA

/-!
## Verification Summary

This file ports Progress.v (284 lines Coq) to Lean 4.

| Coq Theorem | Lean Theorem | Status |
|-------------|--------------|--------|
| canonical_bool | canonicalBool | ✅ Proved |
| canonical_fn | canonicalFn | ✅ Proved |
| canonical_pair | canonicalPair | ✅ Proved |
| canonical_sum | canonicalSum | ✅ Proved |
| canonical_ref | canonicalRef | ✅ Proved |
| canonical_secret | canonicalSecret | ✅ Proved |
| canonical_proof | canonicalProof | ✅ Proved |
| lookup_nil_contra | lookupNilContra | ✅ Proved |
| progress | progress | ✅ Proved |

Total: 9 theorems ported
-/
