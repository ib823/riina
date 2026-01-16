# RIINA Axiom Elimination Plan v2.0

**Created:** 2026-01-16
**Status:** Active
**Current Axiom Count:** 31
**Target:** 5-7 semantic axioms

---

## Executive Summary

The RIINA NonInterference.v proof contains **31 axioms** that block full formal verification claims. This document provides a comprehensive analysis of each axiom and a detailed elimination strategy.

**Key Finding:** Of the 31 axioms:
- **16 are mechanically provable** (value extraction, step-up, closedness) — 28-42 hours
- **6 require typing refactoring** (step-index manipulation) — 20-40 hours
- **4 are Kripke semantic properties** (may remain as axioms) — design decision
- **5 are language constructs** (3 provable, 2 intentional trust boundaries) — 20-40 hours

**Total Estimated Effort:** 68-122 hours to reduce to 5-7 semantic axioms

---

## Axiom Taxonomy

### Category 1: Value & Closedness Extraction (8 axioms) 🟢 LOW RISK

**Lines:** 247-285
**Risk Level:** 🟢 LOW
**Provability:** HIGH (mechanical proofs)
**Effort:** 2-4 hours each (16-32 hours total)

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `val_rel_at_type_value_left` | 247 | v1 is a value if related at first-order type | Should be provable by induction on type structure |
| `val_rel_at_type_value_right` | 252 | v2 is a value if related at first-order type | Should be provable by induction on type structure |
| `val_rel_at_type_closed_left` | 257 | v1 is closed if related at first-order type | Should be provable by induction on type structure |
| `val_rel_at_type_closed_right` | 262 | v2 is closed if related at first-order type | Should be provable by induction on type structure |
| `val_rel_at_type_value_any_left` | 271 | v1 is a value if related at ANY type | Higher-order version (includes TFn) |
| `val_rel_at_type_value_any_right` | 275 | v2 is a value if related at ANY type | Higher-order version (includes TFn) |
| `val_rel_at_type_closed_any_left` | 279 | v1 is closed if related at ANY type | Higher-order version (includes TFn) |
| `val_rel_at_type_closed_any_right` | 283 | v2 is closed if related at ANY type | Higher-order version (includes TFn) |

**Proof Strategy:**
```coq
Lemma val_rel_at_type_value_left : forall T Σ sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  value v1.
Proof.
  intros T Σ sp vl sl v1 v2 Hfo Hrel.
  induction T; simpl in Hfo; try discriminate.
  - (* TUnit: v1 = EUnit *) unfold val_rel_at_type in Hrel. ...
  - (* TBool: v1 = EBool b *) unfold val_rel_at_type in Hrel. ...
  - (* TInt: v1 = EInt n *) unfold val_rel_at_type in Hrel. ...
  - (* TProd: destruct pair, apply IH *) ...
  - (* TSum: destruct inl/inr, apply IH *) ...
Qed.
```

**Blocking Dependencies:** None
**Priority:** P1 (Wave 1a)

---

### Category 2: Kripke Monotonicity (4 axioms) 🟡 MODERATE RISK

**Lines:** 510-561
**Risk Level:** 🟡 MODERATE (semantic properties)
**Provability:** UNKNOWN (may be design axioms)
**Effort:** 40-80 hours OR accept as semantic axioms

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `val_rel_n_weaken` | 510 | Value relation is contravariant in store typing (Σ' ⊇ Σ) | Requires mutual induction with TFn contravariance |
| `store_rel_n_weaken` | 522 | Store relation is contravariant in store typing | Mutual with val_rel_n_weaken |
| `val_rel_n_mono_store` | 545 | Value relation is covariant in store typing (Σ ⊆ Σ') | Kripke "world extension" property |
| `store_rel_n_mono_store` | 558 | Store relation is covariant in store typing | Mutual with val_rel_n_mono_store |

**Semantic Justification (from comments):**

> "Kripke monotonicity property: extending the 'world' (store typing) preserves
> established relations. For function types (TFn): The function's specification
> (store_ty_extends Σ Σ'') becomes easier to satisfy with a larger starting Σ'
> because Σ' ⊆ Σ'' is a weaker requirement than Σ ⊆ Σ'' when Σ ⊆ Σ'."

**References Cited:**
- Appel & McAllester (2001) "An indexed model of recursive types"
- Ahmed (2006) "Step-Indexed Syntactic Logical Relations"
- Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"
- Birkedal & Harper (1999) "Relational interpretations of recursive types"

**Proof Strategy:**

These axioms encode **fundamental semantic properties** of Kripke worlds in step-indexed logical relations. They may be:

1. **Provable by mutual induction** on `val_rel_n` and `store_rel_n` — requires refactoring definitions
2. **Semantic axioms by design** — accepted as fundamental properties (justified by cited papers)

**Decision Point:** Attempt mutual induction proof (40-80 hours). If blocked, document as **justified semantic axioms** with references.

**Blocking Dependencies:** Requires understanding TFn contravariance
**Priority:** P2 (Wave 2a) OR accept as semantic axioms

---

### Category 3: Step-Index Manipulation (6 axioms) 🟡 MODERATE RISK

**Lines:** 600-670
**Risk Level:** 🟡 MODERATE
**Provability:** HIGH (requires typing assumption)
**Effort:** 10-20 hours total

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `exp_rel_step1_fst` | 600 | At step 1, EFst evaluation terminates | Requires termination or typing tracking |
| `exp_rel_step1_snd` | 612 | At step 1, ESnd evaluation terminates | Requires termination or typing tracking |
| `exp_rel_step1_case` | 624 | At step 1, ECase evaluation terminates | Requires termination or typing tracking |
| `exp_rel_step1_if` | 636 | At step 1, EIf evaluation terminates | Requires termination or typing tracking |
| `exp_rel_step1_let` | 648 | At step 1, ELet evaluation terminates | Requires termination or typing tracking |
| `exp_rel_step1_app` | 660 | At step 1, EApp evaluation terminates | Requires termination or typing tracking |

**Semantic Justification (from comments):**

> "At step index 1 (exp_rel_n (S 0)), evaluation produces values v, v'
> related at val_rel_n 0 = True. For elimination forms (EFst, ESnd, ECase,
> EIf, EApp), we need the structure of v to continue evaluation.
>
> These axioms assert that step-1 evaluation terminates, which follows from
> termination (not proven but standard for this calculus)
>
> These axioms can be eliminated by either:
> - Proving termination/strong normalization
> - Tracking typing through the logical relation
> - Using a larger step index in the base case"

**Proof Strategy:**

**Option A:** Add typing assumption to `exp_rel_n` definition
```coq
(* Current *)
Fixpoint exp_rel_n (n : nat) (Σ : store_ty) (T : ty) (e1 e2 : expr) : Prop := ...

(* Proposed *)
Fixpoint exp_rel_n (Γ : ctx) (n : nat) (Σ : store_ty) (T : ty) (e1 e2 : expr) : Prop :=
  has_type Γ Σ empty_effectrow e1 T ε /\  (* Add typing invariant *)
  has_type Γ Σ empty_effectrow e2 T ε /\
  ...
```

With typing, we can prove progress: well-typed elimination forms with value arguments step.

**Option B:** Use larger step index in base case (n=2 instead of n=1)

**Option C:** Prove termination (Track V) — long-term solution

**Blocking Dependencies:** Requires refactoring exp_rel_n or proving termination
**Priority:** P2 (Wave 2a)

---

### Category 4: Step-Up Lemmas (6 axioms) 🟢 LOW RISK

**Lines:** 575, 680, 699-724
**Risk Level:** 🟢 LOW
**Provability:** HIGH (mechanical proofs)
**Effort:** 10 hours total

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `val_rel_n_to_val_rel` | 575 | val_rel_n (S n) for values implies val_rel | Step index doesn't matter for values |
| `tapp_step0_complete` | 680 | At step 0, function application output inflates to step 1 | val_rel_n 0 = True inflates to val_rel_n 1 |
| `val_rel_n_step_up` | 699 | val_rel_n n for values implies val_rel_n (S n) | Cumulative structure: S n includes n |
| `store_rel_n_step_up` | 705 | store_rel_n n implies store_rel_n (S n) | Cumulative structure: S n includes n |
| `val_rel_n_lam_cumulative` | 715 | Lambda relation is cumulative in step index | Function values don't reduce |
| `val_rel_at_type_to_val_rel_ho` | 724 | val_rel_at_type implies val_rel for higher-order types | Type-structural relation implies full relation |

**Semantic Justification (from comments):**

> "For actual values (not expressions that step), if val_rel_n holds at any
> positive step index, it holds at all step indices. This is because:
> 1. Values don't reduce, so step index doesn't decrease
> 2. The val_rel_at_type predicates for first-order types don't depend on step index
> 3. For function types, the property holds by induction on types"

**Proof Strategy:**

These are **cumulative structure lemmas**. The val_rel_n and store_rel_n definitions should have:

```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True  (* Base case: vacuously true *)
  | S n' =>
      value v1 /\ value v2 /\
      closed_expr v1 /\ closed_expr v2 /\
      val_rel_n n' Σ T v1 v2 /\  (* CUMULATIVE: includes previous level *)
      val_rel_at_type Σ ... T v1 v2
  end.
```

**Proof by induction on n:**
- Base case n=0: trivial (True implies anything)
- Inductive case S n: unfold definition, apply IH, reconstruct

**Blocking Dependencies:** None (definition structure)
**Priority:** P1 (Wave 1b)

---

### Category 5: Language Constructs (5 axioms) 🟠 MODERATE-HIGH RISK

**Lines:** 919-976, 1006-1016
**Risk Level:** 🟠 MODERATE-HIGH
**Provability:** MIXED (3 provable, 2 intentional)
**Effort:** 20-40 hours

#### Subcategory 5a: Effect Handling (1 axiom)

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `logical_relation_handle` | 919 | EHandle preserves relatedness | Complex evaluation semantics |

**Proof Strategy:** Requires understanding multi_step semantics for effect handlers. Should be provable by induction on evaluation steps.

**Effort:** 10-20 hours
**Priority:** P2 (Wave 2b)

#### Subcategory 5b: References (3 axioms)

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `logical_relation_ref` | 938 | ERef preserves relatedness | Requires store weakening axioms |
| `logical_relation_deref` | 948 | EDeref preserves relatedness | Requires store weakening axioms |
| `logical_relation_assign` | 958 | EAssign preserves relatedness | Requires store weakening axioms |

**Circular Dependency:** These axioms depend on `val_rel_n_weaken` and `store_rel_n_weaken` (Category 2). Must prove Category 2 first.

**Proof Strategy:**
1. Prove Category 2 (Kripke monotonicity) first
2. Use store weakening to show new locations don't break relatedness
3. Prove by induction on evaluation steps

**Effort:** 10-20 hours (after Category 2)
**Priority:** P3 (after Category 2)

#### Subcategory 5c: Declassification (1 axiom) 🔴 INTENTIONAL

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `logical_relation_declassify` | 971 | EDeclassify preserves relatedness | **Intentional trust boundary** |

**Semantic Justification (from comments):**

> "Declassification unwraps secret values to their underlying type.
> This is safe because val_rel_at_type for TSecret is True,
> so any secret values are trivially related."

**Assessment:** This is an **intentional trust boundary**. Declassification is a controlled violation of non-interference. The axiom encodes the security policy decision.

**Decision:** **KEEP as semantic axiom** with justification. This is part of the security model, not a proof gap.

**Priority:** Document, do not eliminate

#### Subcategory 5d: Closedness (2 axioms) 🟢 LOW RISK

| Axiom | Line | What It Claims | Why It's an Axiom |
|-------|------|----------------|-------------------|
| `lam_closedness_contradiction` | 1006 | env_rel ensures rho1 values are closed | Missing "free vars ⊆ dom(Γ)" lemma |
| `lam_closedness_contradiction2` | 1012 | env_rel ensures rho2 values are closed | Missing "free vars ⊆ dom(Γ)" lemma |

**Proof Strategy:**

Add intermediate lemma:
```coq
Lemma typing_free_vars_in_context : forall Γ Σ Δ e T ε x,
  has_type Γ Σ Δ e T ε ->
  free_in x e ->
  exists T', lookup x Γ = Some T'.
```

Then prove:
```coq
Lemma env_rel_implies_closed : forall Σ Γ rho1 rho2 x,
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  free_in y (rho1 x) ->
  False.
Proof.
  intros. unfold rho_no_free_all in H0.
  specialize (H0 x y). apply H0. reflexivity.
Qed.
```

**Effort:** 2 hours
**Priority:** P1 (Wave 1c)

---

## Elimination Roadmap

### Phase 1: Quick Wins (1-2 weeks, 28-42 hours)

**Wave 1a: Value Extraction (8 axioms, 16-32 hours)**
- `val_rel_at_type_value_left/right` (4 hours each)
- `val_rel_at_type_closed_left/right` (4 hours each)
- `val_rel_at_type_value_any_left/right` (4 hours each)
- `val_rel_at_type_closed_any_left/right` (4 hours each)

**Method:** Induction on type structure
**Blockers:** None
**Result:** 31 axioms → 23 axioms

---

**Wave 1b: Step-Up Lemmas (6 axioms, 10 hours)**
- `val_rel_n_to_val_rel` (2 hours)
- `tapp_step0_complete` (2 hours)
- `val_rel_n_step_up` (2 hours)
- `store_rel_n_step_up` (1 hour)
- `val_rel_n_lam_cumulative` (2 hours)
- `val_rel_at_type_to_val_rel_ho` (1 hour)

**Method:** Induction on step index (cumulative structure)
**Blockers:** None
**Result:** 23 axioms → 17 axioms

---

**Wave 1c: Closedness (2 axioms, 2 hours)**
- Add `typing_free_vars_in_context` lemma
- Prove `lam_closedness_contradiction` (1 hour)
- Prove `lam_closedness_contradiction2` (1 hour)

**Method:** Use `rho_no_free_all` definition
**Blockers:** None
**Result:** 17 axioms → 15 axioms

---

### Phase 2: Harder Proofs (3-4 weeks, 40-80 hours)

**Wave 2a: Kripke Monotonicity (4 axioms, 40-80 hours OR accept)**
- Attempt mutual induction proof for:
  - `val_rel_n_weaken` + `store_rel_n_weaken`
  - `val_rel_n_mono_store` + `store_rel_n_mono_store`

**Method:** Mutual induction on val_rel_n/store_rel_n
**Blockers:** May require semantic justification (design axioms)
**Decision Point:** If blocked after 80 hours, accept as **justified semantic axioms**
**Result:** 15 axioms → 11 axioms (or 15 if accepted as semantic)

---

**Wave 2b: Step-Index Manipulation (6 axioms, 10-20 hours)**
- Refactor `exp_rel_n` to include typing assumption
- Prove termination for step-1 evaluation
- Eliminate:
  - `exp_rel_step1_fst/snd/case/if/let/app`

**Method:** Add typing invariant to exp_rel_n
**Blockers:** Requires refactoring logical relation definition
**Result:** 11 axioms → 5 axioms

---

**Wave 2c: Reference Operations (3 axioms, 10-20 hours)**
- After Category 2 (Kripke) proven, eliminate:
  - `logical_relation_ref`
  - `logical_relation_deref`
  - `logical_relation_assign`

**Method:** Use store weakening + induction
**Blockers:** Depends on Category 2 completion
**Result:** 5 axioms → 2 axioms (+ declassify)

---

**Wave 2d: Effect Handling (1 axiom, 10-20 hours)**
- Prove `logical_relation_handle` by evaluation induction

**Method:** Multi-step semantics + handler cases
**Blockers:** None
**Result:** 2 axioms → 1 axiom (+ declassify)

---

### Final State: 5-7 Semantic Axioms (Acceptable)

After all waves, remaining axioms should be:

1. **Declassification** (1 axiom) — Intentional security policy
2. **Kripke Properties** (0 or 4 axioms) — If accepted as semantic axioms

**Documentation Required:**
- Justify each remaining axiom with:
  - Semantic explanation
  - Academic references (Ahmed 2006, Dreyer 2011, etc.)
  - Why it's a design decision, not a proof gap

---

## Verification Checklist

After each wave, verify:

```bash
cd /home/user/proof/02_FORMAL/coq
make clean && make

# Count remaining axioms
grep -c "^Axiom" properties/NonInterference.v

# Verify no admits
grep -r "Admitted\|admit" *.v

# Check for todos
grep -r "TODO\|FIXME\|HACK" *.v
```

---

## Risk Assessment

| Risk | Probability | Mitigation |
|------|-------------|------------|
| Kripke axioms unprovable | 40% | Document as semantic axioms with references |
| Refactoring breaks proofs | 30% | Incremental changes with frequent verification |
| Time estimates too optimistic | 50% | Buffer 50% additional time |
| Coq compilation fails | 20% | Install Coq first (blocked in current environment) |

---

## Dependencies

**Critical Path:**

```
Install Coq → Wave 1a,1b,1c → Wave 2a (Kripke) → Wave 2c (References) → Wave 2b,2d
     ↓              ↓                 ↓                  ↓                    ↓
  (30 min)    (28-42 hrs)       (40-80 hrs)        (10-20 hrs)        (20-40 hrs)
```

**Parallel Tracks:**
- Wave 1a, 1b, 1c can be done in parallel (independent)
- Wave 2b (step-index) is independent of Wave 2a (Kripke)
- Wave 2c (references) depends on Wave 2a (Kripke)

---

## Success Metrics

| Milestone | Axiom Count | Confidence | Effort |
|-----------|-------------|------------|--------|
| Current | 31 | Proven core, axiom-dependent extensions | 0 hrs |
| After Wave 1 | 15 | High confidence in mechanical proofs | 28-42 hrs |
| After Wave 2a | 11 (or 15) | Depends on Kripke provability | 68-122 hrs |
| After Wave 2b | 5 | High confidence with typing | 78-142 hrs |
| After Wave 2c | 2 | High confidence | 88-162 hrs |
| After Wave 2d | 1 | Only intentional trust boundary | 98-182 hrs |
| Final | 5-7 | Justified semantic axioms | 98-182 hrs |

---

## Next Actions

**Immediate (Blocked in current environment):**
1. ❌ Install Coq 8.18.0 (network access required)
2. ❌ Run `make` to verify all proofs compile

**When Coq Available:**
1. ✅ Begin Wave 1a: Value extraction axioms (16-32 hours)
2. ✅ Begin Wave 1b: Step-up lemmas (10 hours)
3. ✅ Begin Wave 1c: Closedness axioms (2 hours)

**Current Session (Without Coq):**
1. ✅ Document axiom analysis (COMPLETE)
2. ✅ Create elimination roadmap (COMPLETE)
3. Next: Verify test execution status (Track B and Track F)

---

## References

1. Appel & McAllester (2001) "An indexed model of recursive types"
2. Ahmed (2006) "Step-Indexed Syntactic Logical Relations for Imperative Objects"
3. Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"
4. Birkedal & Harper (1999) "Relational interpretations of recursive types in an operational setting"
5. Ahmed et al. (2009) "L³: A Linear Language with Locations"
6. Swasey et al. (2017) "A Logical Relation for Monadic Encapsulation of State"

---

**Document Status:** Active
**Last Updated:** 2026-01-16
**Next Review:** After Wave 1 completion
**Maintainer:** RIINA Formal Verification Track
