# AXIOM ELIMINATION: ULTIMATE ATTACK PLAN

## Mission: ZERO AXIOMS - The Most Rigorous Formally Verified Language in Human History

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║                                                                                  ║
║     ██████╗ ██╗██╗███╗   ██╗ █████╗                                              ║
║     ██╔══██╗██║██║████╗  ██║██╔══██╗                                             ║
║     ██████╔╝██║██║██╔██╗ ██║███████║                                             ║
║     ██╔══██╗██║██║██║╚██╗██║██╔══██║                                             ║
║     ██║  ██║██║██║██║ ╚████║██║  ██║                                             ║
║     ╚═╝  ╚═╝╚═╝╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝                                             ║
║                                                                                  ║
║     ZERO AXIOM ELIMINATION PLAN                                                  ║
║     Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE        ║
║                                                                                  ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## EXECUTIVE SUMMARY

**Current State:** 17 axioms in NonInterference.v
**Target State:** 0 axioms (ZERO TRUST)
**Approach:** Foundational rebuild using three pillars

The 17 axioms are NOT independent bugs to fix. They are SYMPTOMS of incomplete foundations.
We must rebuild the foundations so these properties DERIVE from first principles.

---

## THE 17 AXIOMS: COMPLETE ANALYSIS

### Category A: Step Conversion (3 axioms)

| Axiom | Purpose | Root Cause | Solution |
|-------|---------|------------|----------|
| `val_rel_n_to_val_rel` | Convert step-indexed to unindexed | Missing limit construction | Prove via SN + completeness |
| `val_rel_n_step_up` | Relation persists at higher steps | Missing termination proof | STRONG NORMALIZATION |
| `store_rel_n_step_up` | Store relation persists | Depends on val_rel_n_step_up | Follows from SN |

**BLOCKER:** Strong Normalization for TFn (function types)

### Category B: Step-1 Termination (7 axioms)

| Axiom | Purpose | Root Cause | Solution |
|-------|---------|------------|----------|
| `exp_rel_step1_fst` | Pair projection terminates in 1 step | Missing canonical forms | Type inversion lemma |
| `exp_rel_step1_snd` | Pair projection terminates in 1 step | Missing canonical forms | Type inversion lemma |
| `exp_rel_step1_case` | Case analysis terminates in 1 step | Missing canonical forms | Type inversion lemma |
| `exp_rel_step1_if` | Conditional terminates in 1 step | Missing canonical forms | Type inversion lemma |
| `exp_rel_step1_let` | Let binding terminates in 1 step | Missing value semantics | Substitution lemma |
| `exp_rel_step1_handle` | Effect handling terminates in 1 step | Missing handler semantics | Effect inversion |
| `exp_rel_step1_app` | Application terminates in 1 step | Missing canonical forms | Lambda inversion |

**BLOCKER:** Canonical forms lemmas not proven in Typing.v

### Category C: Application (1 axiom)

| Axiom | Purpose | Root Cause | Solution |
|-------|---------|------------|----------|
| `tapp_step0_complete` | App completes at step 0 | Missing step-up + typing | Follows from SN + canonical |

**BLOCKER:** Depends on Categories A and B

### Category D: Higher-Order (2 axioms)

| Axiom | Purpose | Root Cause | Solution |
|-------|---------|------------|----------|
| `val_rel_n_lam_cumulative` | Lambda relation is cumulative | Missing Kripke semantics | World-indexed relations |
| `val_rel_at_type_to_val_rel_ho` | Type-indexed to value relation | Missing parametricity | Relational parametricity |

**BLOCKER:** Need proper Kripke model with world monotonicity

### Category E: Reference Operations (4 axioms)

| Axiom | Purpose | Root Cause | Solution |
|-------|---------|------------|----------|
| `logical_relation_ref` | ref operation preserves relation | Missing store invariant | Store typing theorem |
| `logical_relation_deref` | deref operation preserves relation | Missing store invariant | Store typing theorem |
| `logical_relation_assign` | assign operation preserves relation | Missing store invariant | Store typing theorem |
| `logical_relation_declassify` | declassify preserves security | Missing policy semantics | Declassification theorem |

**BLOCKER:** Store typing invariant not established

---

## THE THREE PILLARS

### PILLAR 1: STRONG NORMALIZATION

**What it is:** Proof that every well-typed closed term reduces to a value in finite steps.

**Why it matters:** Without SN, we cannot prove that step-indexed relations "step up" -
a relation at step n might not hold at step n+1 if evaluation could diverge.

**The approach:**

```
┌─────────────────────────────────────────────────────────────────┐
│  STRONG NORMALIZATION PROOF STRUCTURE                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  1. Define REDUCIBILITY CANDIDATES                              │
│     - For each type T, define RC(T) ⊆ terms                     │
│     - RC(TUnit) = {e | e →* EUnit}                              │
│     - RC(TBool) = {e | e →* EBool b}                            │
│     - RC(TFn T1 T2) = {e | e →* λx.body ∧                       │
│                            ∀v ∈ RC(T1). body[v/x] ∈ RC(T2)}     │
│                                                                 │
│  2. Prove CLOSURE PROPERTIES                                    │
│     - RC(T) closed under reduction                              │
│     - RC(T) closed under expansion (anti-reduction)             │
│     - RC(T) contains all values of type T                       │
│                                                                 │
│  3. Prove FUNDAMENTAL LEMMA                                     │
│     - If Γ ⊢ e : T and ρ ∈ RC(Γ), then e[ρ] ∈ RC(T)            │
│     - By induction on typing derivation                         │
│                                                                 │
│  4. Conclude STRONG NORMALIZATION                               │
│     - Every closed well-typed term is in RC(T)                  │
│     - RC(T) ⊆ SN (strongly normalizing terms)                   │
│     - Therefore all well-typed closed terms normalize           │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Files involved:**
- `SN_Core_v3.v` - Already has SN infrastructure (ZERO admits)
- `StrongNormalization_v2.v` - Partial SN proof
- `StepUpFromSN.v` - Derives step-up from SN

**Axioms eliminated by Pillar 1:**
- `val_rel_n_step_up` (3 total with store)
- `store_rel_n_step_up`
- `tapp_step0_complete` (partial)

### PILLAR 2: CANONICAL FORMS + TYPE INVERSION

**What it is:** Proof that values of each type have a specific syntactic form.

**Why it matters:** To prove exp_rel_step1_fst, we need to know that a value of type
TProd T1 T2 is actually EPair a b, not some arbitrary expression.

**The approach:**

```
┌─────────────────────────────────────────────────────────────────┐
│  CANONICAL FORMS LEMMAS                                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  For each type constructor, prove:                              │
│                                                                 │
│  canonical_forms_unit:                                          │
│    Γ ⊢ v : TUnit → value v → v = EUnit                          │
│                                                                 │
│  canonical_forms_bool:                                          │
│    Γ ⊢ v : TBool → value v → ∃b. v = EBool b                    │
│                                                                 │
│  canonical_forms_int:                                           │
│    Γ ⊢ v : TInt → value v → ∃n. v = EInt n                      │
│                                                                 │
│  canonical_forms_fn:                                            │
│    Γ ⊢ v : TFn T1 T2 ε → value v → ∃x body. v = ELam x T1 body ε│
│                                                                 │
│  canonical_forms_prod:                                          │
│    Γ ⊢ v : TProd T1 T2 → value v → ∃a b. v = EPair a b          │
│                                                                 │
│  canonical_forms_sum:                                           │
│    Γ ⊢ v : TSum T1 T2 → value v →                               │
│      (∃x. v = EInl x T2) ∨ (∃y. v = EInr y T1)                  │
│                                                                 │
│  canonical_forms_ref:                                           │
│    Γ ⊢ v : TRef T sl → value v → ∃l. v = ELoc l                 │
│                                                                 │
│  ... (for all 22 type constructors)                             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Proof technique:**
- Inversion on typing derivation
- Case analysis on value
- Show contradictions for impossible cases

**Files involved:**
- `Typing.v` - Add canonical forms lemmas here
- `NonInterference.v` - Use in exp_rel_step1_* proofs

**Axioms eliminated by Pillar 2:**
- `exp_rel_step1_fst`
- `exp_rel_step1_snd`
- `exp_rel_step1_case`
- `exp_rel_step1_if`
- `exp_rel_step1_let`
- `exp_rel_step1_handle`
- `exp_rel_step1_app`

### PILLAR 3: KRIPKE WORLD SEMANTICS

**What it is:** A proper formalization of logical relations over "possible worlds"
(store typings) with monotonicity guarantees.

**Why it matters:** Higher-order functions and references require reasoning about
"future" stores that might have more locations. Relations must be monotone over
these world extensions.

**The approach:**

```
┌─────────────────────────────────────────────────────────────────┐
│  KRIPKE LOGICAL RELATIONS                                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  World = Store Typing Σ                                         │
│  World Extension: Σ ⊑ Σ' iff Σ ⊆ Σ' (prefix)                    │
│                                                                 │
│  Value Relation (world-indexed):                                │
│    V⟦T⟧(Σ) : Value × Value → Prop                               │
│                                                                 │
│  MONOTONICITY REQUIREMENT:                                      │
│    If (v1, v2) ∈ V⟦T⟧(Σ) and Σ ⊑ Σ'                             │
│    Then (v1, v2) ∈ V⟦T⟧(Σ')                                     │
│                                                                 │
│  For TFn T1 T2:                                                 │
│    (λx.e1, λx.e2) ∈ V⟦TFn T1 T2⟧(Σ) iff                         │
│    ∀Σ' ⊒ Σ. ∀(v1,v2) ∈ V⟦T1⟧(Σ').                               │
│      (e1[v1/x], e2[v2/x]) ∈ E⟦T2⟧(Σ')                           │
│                                                                 │
│  KEY INSIGHT: The universal quantification over Σ' ⊒ Σ          │
│  ensures monotonicity is BUILT INTO the definition.             │
│                                                                 │
│  For TRef T:                                                    │
│    (l, l) ∈ V⟦TRef T⟧(Σ) iff                                    │
│    l ∈ dom(Σ) ∧ Σ(l) = T                                        │
│                                                                 │
│  Store Relation:                                                │
│    (st1, st2) ∈ S⟦Σ⟧ iff                                        │
│    ∀l ∈ dom(Σ). (st1[l], st2[l]) ∈ V⟦Σ(l)⟧(Σ)                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**Files involved:**
- `KripkeProperties.v` - Kripke monotonicity lemmas
- `KripkeMutual.v` - Mutual induction for Kripke relations
- `NonInterferenceKripke.v` - Kripke-based non-interference

**Axioms eliminated by Pillar 3:**
- `val_rel_n_lam_cumulative`
- `val_rel_at_type_to_val_rel_ho`
- `logical_relation_ref`
- `logical_relation_deref`
- `logical_relation_assign`
- `logical_relation_declassify`
- `val_rel_n_to_val_rel`

---

## EXECUTION PLAN

### Phase 1: Canonical Forms (LOW RISK, HIGH REWARD)

**Duration:** 1-2 sessions
**Axioms targeted:** 7 (Category B)
**Success probability:** HIGH (95%)

**Tasks:**
1. Add canonical_forms_unit to Typing.v
2. Add canonical_forms_bool to Typing.v
3. Add canonical_forms_int to Typing.v
4. Add canonical_forms_string to Typing.v
5. Add canonical_forms_fn to Typing.v
6. Add canonical_forms_prod to Typing.v
7. Add canonical_forms_sum to Typing.v
8. Add canonical_forms_ref to Typing.v
9. Add remaining 14 canonical forms
10. Use canonical forms to prove exp_rel_step1_fst
11. Use canonical forms to prove exp_rel_step1_snd
12. Use canonical forms to prove exp_rel_step1_case
13. Use canonical forms to prove exp_rel_step1_if
14. Use canonical forms to prove exp_rel_step1_let
15. Use canonical forms to prove exp_rel_step1_handle
16. Use canonical forms to prove exp_rel_step1_app

**Verification:**
```bash
# After each lemma
coqc -R . RIINA foundations/Typing.v
coqchk -R . RIINA RIINA.foundations.Typing
```

### Phase 2: Store Invariants (MEDIUM RISK, MEDIUM REWARD)

**Duration:** 2-3 sessions
**Axioms targeted:** 4 (Category E)
**Success probability:** MEDIUM (70%)

**Tasks:**
1. Define store_typing_invariant in StoreRelation.v
2. Prove store_typing_preserved_by_ref
3. Prove store_typing_preserved_by_deref
4. Prove store_typing_preserved_by_assign
5. Connect store invariant to val_rel_le
6. Prove logical_relation_ref
7. Prove logical_relation_deref
8. Prove logical_relation_assign
9. Prove logical_relation_declassify

**Key insight:** The store invariant must state:
```coq
Definition store_typing_invariant (Σ : store_ty) (st : store) : Prop :=
  length st = length Σ /\
  forall l, l < length Σ ->
    has_type empty (nth l st EUnit) (nth l Σ TUnit).
```

### Phase 3: Strong Normalization Integration (HIGH RISK, HIGH REWARD)

**Duration:** 3-5 sessions
**Axioms targeted:** 5 (Categories A, C, D partial)
**Success probability:** MEDIUM (60%)

**Tasks:**
1. Review SN_Core_v3.v (already ZERO admits)
2. Connect SN_Core_v3 reducibility candidates to val_rel_n
3. Prove val_rel_n_step_up for first-order types (done via fo_compound_depth)
4. Prove val_rel_n_step_up for TFn using SN
5. Prove store_rel_n_step_up as corollary
6. Prove tapp_step0_complete using SN + canonical forms

**The key lemma:**
```coq
Lemma sn_implies_step_up : forall T e,
  strongly_normalizing e ->
  has_type empty e T ->
  forall n Σ, val_rel_n n Σ T e e ->
  forall m, m >= n -> val_rel_n m Σ T e e.
```

### Phase 4: Kripke Semantics (HIGH RISK, HIGH REWARD)

**Duration:** 3-5 sessions
**Axioms targeted:** 3 (Category D + val_rel_n_to_val_rel)
**Success probability:** MEDIUM (60%)

**Tasks:**
1. Refactor val_rel_n to be explicitly Kripke-indexed
2. Prove Kripke monotonicity lemma
3. Prove val_rel_n_lam_cumulative using Kripke quantification
4. Prove val_rel_at_type_to_val_rel_ho using relational parametricity
5. Prove val_rel_n_to_val_rel as limit construction

**The Kripke insight:**
```coq
(* OLD: val_rel_n n Σ T v1 v2 *)
(* NEW: val_rel Σ T v1 v2 with built-in world quantification *)

Definition val_rel_fn (Σ : store_ty) (T1 T2 : ty) (v1 v2 : expr) : Prop :=
  exists x1 body1 x2 body2,
    v1 = ELam x1 T1 body1 /\ v2 = ELam x2 T1 body2 /\
    (* KEY: quantify over ALL future worlds *)
    forall Σ' (Hext : store_ty_extends Σ Σ'),
    forall a1 a2, val_rel Σ' T1 a1 a2 ->
    exp_rel Σ' T2 (subst x1 a1 body1) (subst x2 a2 body2).
```

---

## VERIFICATION PROTOCOL

### For EVERY lemma proven:

1. **Compile:**
   ```bash
   coqc -R . RIINA <file>.v
   ```

2. **Check for axioms:**
   ```bash
   coqchk -R . RIINA RIINA.<module>.<lemma>
   ```

3. **Verify dependencies:**
   ```bash
   Print Assumptions <lemma>.
   ```

4. **Document in SESSION_LOG.md**

### For EVERY axiom eliminated:

1. **Update NonInterference.v** - Remove axiom, add lemma
2. **Update PROGRESS.md** - Decrease axiom count
3. **Run full make** - Ensure nothing breaks
4. **Commit immediately** - With detailed message

---

## SUCCESS CRITERIA

### ZERO AXIOMS achieved when:

1. `grep "^Axiom " properties/NonInterference.v` returns empty
2. `coqchk -R . RIINA RIINA.properties.NonInterference` passes
3. `Print Assumptions non_interference.` shows only standard library

### REVOLUTIONARY status achieved when:

1. All 17 axioms eliminated
2. All proofs verified by coqchk
3. Multi-prover verification (Coq + Lean + Isabelle)
4. Published formal verification certificate
5. Third-party audit confirms ZERO unproven assumptions

---

## TIMELINE

| Phase | Duration | Axioms | Cumulative |
|-------|----------|--------|------------|
| Phase 1: Canonical Forms | 1-2 sessions | -7 | 10 remaining |
| Phase 2: Store Invariants | 2-3 sessions | -4 | 6 remaining |
| Phase 3: Strong Normalization | 3-5 sessions | -3 | 3 remaining |
| Phase 4: Kripke Semantics | 3-5 sessions | -3 | 0 remaining |
| **TOTAL** | **9-15 sessions** | **-17** | **ZERO AXIOMS** |

---

## RISK ANALYSIS

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Canonical forms unprovable | LOW (5%) | HIGH | Already have partial proofs in Typing.v |
| Store invariant too weak | MEDIUM (30%) | MEDIUM | Can strengthen definition |
| SN proof incomplete | MEDIUM (40%) | HIGH | SN_Core_v3 is solid foundation |
| Kripke semantics complex | HIGH (50%) | MEDIUM | Can split FO/HO approaches |

---

## FALLBACK STRATEGIES

### If canonical forms fail:
- Add type annotations to values
- Use runtime type information

### If store invariants fail:
- Weaken reference operations
- Add explicit type casts

### If SN fails for TFn:
- Split proof: FO types proven, HO types marked
- Use effect system to bound recursion

### If Kripke fails:
- Use simpler unary logical relations
- Accept some axioms for HO functions

---

## COMMITMENT

This plan represents the MOST RIGOROUS path to ZERO AXIOMS.

We will NOT:
- Skip any proof step
- Accept "good enough"
- Use unverified shortcuts
- Leave any assumption unproven

We WILL:
- Verify every lemma with coqchk
- Document every decision
- Test every edge case
- Achieve mathematical perfection

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE*

*"Not a single unproven assumption. Not a single security gap."*

*RIINA: The world's first ZERO AXIOM formally verified programming language.*
