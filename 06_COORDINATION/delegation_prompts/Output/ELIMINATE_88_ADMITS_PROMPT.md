# RIINA Proof Repository: Eliminate All 88 Admits

## ABSOLUTE DIRECTIVE

**ELIMINATE ALL 88 ADMITS. ZERO TOLERANCE. 100% SUCCESS REQUIRED.**

Every `Admitted.` must be replaced with a complete proof. No exceptions.

---

## CODEBASE OVERVIEW

### Core Infrastructure (Already Proven)
```
foundations/Syntax.v      - Types, expressions, values
foundations/Semantics.v   - Operational semantics (step, multi_step)
foundations/Typing.v      - Typing rules (has_type), free_in, closed_expr

type_system/Progress.v    - Progress theorem
type_system/Preservation.v - Preservation theorem

properties/CumulativeRelation.v - Step-indexed logical relation (val_rel_le, exp_rel_le)
properties/ValRelMonotone.v     - Step monotonicity (val_rel_le_monotone) ✓ PROVEN
properties/ClosedValueLemmas.v  - Closed value properties ✓ PROVEN
properties/SubstitutionCommute.v - Substitution lemmas ✓ PROVEN
```

### Key Definitions

```coq
(* Step-indexed value relation *)
Definition val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop := ...

(* Step-indexed expression relation *)
Definition exp_rel_le (n : nat) (Σ : store_ty) (T : ty) (e1 e2 : expr) : Prop := ...

(* Cumulative property - PROVEN *)
Lemma val_rel_le_cumulative : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 -> val_rel_le n Σ T v1 v2.

(* Step monotonicity - PROVEN *)
Theorem val_rel_le_monotone : forall m n Σ T v1 v2,
  m <= n -> val_rel_le n Σ T v1 v2 -> val_rel_le m Σ T v1 v2.
```

---

## ADMIT INVENTORY (88 Total)

### Category 1: FundamentalTheorem.v (24 admits)
**Pattern:** Compatibility lemmas for each syntactic form

| Line | Lemma | Strategy |
|------|-------|----------|
| 424 | compat_pair | Use exp_rel_le definition, IH on e1, e2 |
| 465 | compat_fst | Destruct pair, apply val_rel_le for T1 |
| 496 | compat_snd | Destruct pair, apply val_rel_le for T2 |
| 522 | compat_inl | Wrap with EInl, preserve relation |
| 541 | compat_inr | Wrap with EInr, preserve relation |
| 558 | compat_case | Case analysis on sum, IH on branches |
| 589 | compat_if | Boolean case split, IH on branches |
| 602 | compat_let | Sequential composition, substitution |
| 631 | compat_perform | Effect typing, IH on argument |
| 665 | compat_handle | Handler composition, IH on body/handler |
| 685 | compat_ref | Allocation, store extension |
| 702 | compat_deref | Store lookup, val_rel preservation |
| 721 | compat_assign | Store update, unit result |
| 738 | compat_classify | Security label, IH on argument |
| 751 | compat_declassify | Policy check, IH on arguments |
| 765 | compat_prove | Proof term, IH on argument |
| 797 | compat_require | Effect check, IH on argument |
| 811 | compat_grant | Effect grant, IH on argument |
| 837-1114 | fund_theorem cases | Mutual induction on typing derivation |

**Proof Pattern for Compatibility Lemmas:**
```coq
Lemma compat_X : forall n Σ T ... e e',
  exp_rel_le n Σ T1 e1 e1' ->
  exp_rel_le n Σ T (EX e1 ...) (EX e1' ...).
Proof.
  intros n Σ T ... e e' Hrel.
  unfold exp_rel_le in *.
  intros k v1 v2 st1 st2 ctx Hk Heval1 Heval2 Hst.
  (* Invert evaluation, apply IH, reconstruct *)
  inversion Heval1; subst.
  inversion Heval2; subst.
  (* Use Hrel with appropriate k' < k *)
  apply Hrel with (k := k - 1); try lia.
  (* Complete with val_rel_le properties *)
  ...
Qed.
```

---

### Category 2: AxiomEliminationVerified.v (15 admits)
**Pattern:** Step-1 expression relations for specific reductions

| Line | Lemma | Strategy |
|------|-------|----------|
| 64 | exp_rel_step1_fst_typed | Fst reduction, pair destruction |
| 85 | exp_rel_step1_snd_typed | Snd reduction, pair destruction |
| 107 | exp_rel_step1_let_typed | Let substitution, IH |
| 127 | exp_rel_step1_handle_typed | Handler application |
| 151 | exp_rel_step1_if_same_bool | Boolean branch selection |
| 174 | exp_rel_step1_app_typed | Beta reduction (KEY LEMMA) |
| 281 | val_rel_n_step_up_identical_fo | First-order step-up |
| 360 | val_rel_n_step_0_to_1 | Zero to one step |
| 412-524 | case/inl/inr/ref/deref/assign | Specific reduction rules |

**Key Insight:** These lemmas establish that one-step reductions preserve the logical relation. Use:
1. Operational semantics inversion
2. Canonical forms lemmas
3. Substitution preserves typing

---

### Category 3: NonInterference_v2_LogicalRelation.v (11 admits)
**Pattern:** Logical relation construction for security types

| Line | Lemma | Strategy |
|------|-------|----------|
| 1836-2022 | val_rel_n construction | Build relation by type structure |
| 2068-2078 | sum injection lemmas | EInl/EInr preservation |
| 2201-2211 | classify/prove lemmas | Security label operations |
| 2351 | step_up lemma | Use val_rel_le_monotone |
| 2523 | main theorem | Mutual induction, all cases |

---

### Category 4: TypedConversion.v (5 admits)
**Pattern:** Type conversion/coercion proofs

| Line | Strategy |
|------|----------|
| 308 | Type equality implies val_rel |
| 383 | Subtyping preserves relation |
| 393 | Coercion semantics |
| 436 | Higher-order conversion |
| 538 | Store type extension |

---

### Category 5: ApplicationComplete.v (5 admits)
**Pattern:** Application completeness for function types

| Line | Strategy |
|------|----------|
| 132 | App reduces to value |
| 182 | Beta reduction preserves type |
| 305 | Argument substitution |
| 477 | Result type preservation |
| 538 | Effect composition |

---

### Category 6: Remaining Files (28 admits)

**NonInterferenceZero.v (4):** Zero-step base cases
**KripkeMutual.v (4):** Kripke world monotonicity
**RelationBridge.v (3):** Bridge between relation variants
**ReferenceOps.v (3):** Reference operation proofs
**NonInterference_v2.v (2):** Main NI theorem
**MasterTheorem.v (2):** Master composition
**LogicalRelationDeclassify*.v (4):** Declassification
**ValRelStepLimit_PROOF.v (1):** Step limit conversion
**LogicalRelationRef_PROOF.v (1):** Reference relation
**Declassification.v (1):** Declassify semantics
**ReducibilityFull.v (1):** Substitution commute
**LinearTypes.v (1):** Weakening invalidity

---

## AVAILABLE LEMMAS (Use These!)

### From ValRelMonotone.v
```coq
Theorem val_rel_le_monotone : forall m n Σ T v1 v2,
  m <= n -> val_rel_le n Σ T v1 v2 -> val_rel_le m Σ T v1 v2.

Corollary val_rel_le_zero : forall n Σ T v1 v2,
  val_rel_le n Σ T v1 v2 -> val_rel_le 0 Σ T v1 v2.

Lemma val_rel_le_pred : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 -> val_rel_le n Σ T v1 v2.
```

### From CumulativeRelation.v
```coq
Lemma val_rel_le_cumulative : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 -> val_rel_le n Σ T v1 v2.

Lemma val_rel_le_mono_step_fo : forall n m Σ T v1 v2,
  first_order_type T = true ->
  m <= n -> val_rel_le n Σ T v1 v2 -> val_rel_le m Σ T v1 v2.
```

### From ClosedValueLemmas.v
```coq
Lemma value_typed_closed : forall Σ Δ v T ε,
  value v -> has_type nil Σ Δ v T ε -> closed_expr_cv v.

Lemma closed_pair_cv : forall e1 e2,
  closed_expr_cv (EPair e1 e2) <-> closed_expr_cv e1 /\ closed_expr_cv e2.
```

### From Typing.v
```coq
Lemma free_in_context : forall x e Γ Σ Δ T ε,
  free_in x e -> has_type Γ Σ Δ e T ε -> exists T', lookup x Γ = Some T'.

Lemma typing_nil_implies_closed : forall Σ pc e T ε,
  has_type nil Σ pc e T ε -> closed_expr e.
```

### From Preservation.v
```coq
Theorem preservation : forall Γ Σ Δ e T ε e' st st',
  has_type Γ Σ Δ e T ε -> step e st e' st' -> has_type Γ Σ Δ e' T ε.
```

---

## PROOF STRATEGIES BY CATEGORY

### Strategy A: Compatibility Lemmas (FundamentalTheorem.v)
1. Unfold `exp_rel_le` definition
2. Introduce hypotheses: step count k, values v1 v2, stores st1 st2
3. Invert evaluation to get subterm evaluations
4. Apply induction hypothesis with k-1 steps
5. Reconstruct val_rel_le using type structure

### Strategy B: Step-1 Lemmas (AxiomEliminationVerified.v)
1. These handle single-step reductions
2. Use operational semantics rules (ST_*)
3. Apply canonical forms for value shapes
4. Use substitution lemma for beta reduction
5. Preservation gives typing of reduct

### Strategy C: Logical Relation Construction (NonInterference*.v)
1. Build val_rel_n by induction on type structure
2. For TFn: universal quantification over arguments
3. For TProd: component-wise relation
4. For TSum: case analysis on injection
5. For TRef: store lookup with val_rel

### Strategy D: Store Relations
1. Store extension: `store_ty_extends Σ Σ'`
2. Store well-formedness: all locations typed
3. Store relation: pointwise val_rel on locations
4. Allocation: fresh location, extend store typing

---

## CRITICAL DEPENDENCIES

```
val_rel_le_monotone (PROVEN)
    ↓
val_rel_le_mono_step (PROVEN - uses monotone)
    ↓
store_rel_le_mono_step (uses val_rel_le_mono_step)
    ↓
exp_rel_le_mono_step (uses val_rel + store_rel)
    ↓
fundamental_theorem (uses all monotonicity)
```

**DO NOT BREAK THIS CHAIN.** Each lemma depends on the ones above.

---

## OUTPUT FORMAT

For each file, provide:

```coq
(* ═══════════════════════════════════════════════════════════════ *)
(* FILE: <filename>.v                                               *)
(* ADMITS ELIMINATED: X → 0                                         *)
(* ═══════════════════════════════════════════════════════════════ *)

(* Line NNN: <lemma_name> *)
Lemma <lemma_name> : <statement>.
Proof.
  <complete proof with no admits>
Qed.

(* Line NNN: <next_lemma> *)
...
```

---

## VERIFICATION CHECKLIST

For each fixed file:
- [ ] `coqc -Q . RIINA <file>.v` compiles
- [ ] `grep "Admitted" <file>.v` returns empty
- [ ] `grep "admit" <file>.v` returns empty (tactical admits)
- [ ] No new `Axiom` declarations
- [ ] All dependencies still compile

---

## FILES TO FIX (Priority Order)

### Priority 1: Foundation (Fix First)
1. `properties/ValRelStepLimit_PROOF.v` (1 admit)
2. `properties/RelationBridge.v` (3 admits)
3. `properties/Declassification.v` (1 admit)

### Priority 2: Logical Relation Core
4. `properties/KripkeMutual.v` (4 admits)
5. `properties/NonInterferenceZero.v` (4 admits)
6. `properties/ReferenceOps.v` (3 admits)

### Priority 3: Step-1 Infrastructure
7. `properties/AxiomEliminationVerified.v` (15 admits)
8. `properties/TypedConversion.v` (5 admits)

### Priority 4: Main Theorems
9. `properties/ApplicationComplete.v` (5 admits)
10. `properties/NonInterference_v2_LogicalRelation.v` (11 admits)
11. `properties/NonInterference_v2.v` (2 admits)

### Priority 5: Fundamental Theorem
12. `properties/FundamentalTheorem.v` (24 admits)
13. `properties/MasterTheorem.v` (2 admits)

### Priority 6: Declassification
14. `properties/LogicalRelationDeclassify_v2.v` (2 admits)
15. `properties/LogicalRelationDeclassify_PROOF.v` (1 admit)
16. `properties/LogicalRelationDeclassify_PROOF_REFINED.v` (2 admits)
17. `properties/LogicalRelationRef_PROOF.v` (1 admit)

### Priority 7: Remaining
18. `termination/ReducibilityFull.v` (1 admit)
19. `domains/LinearTypes.v` (1 admit)

---

## SUCCESS CRITERIA

| Metric | Requirement |
|--------|-------------|
| Admits | 88 → 0 |
| Compilation | All files compile |
| Dependencies | No breakage |
| Tactics | No `admit` or `Admitted` |
| Axioms | No new unjustified axioms |

**ANYTHING LESS THAN 100% IS FAILURE.**

---

## RIINA PHILOSOPHY

```
RIINA = Rigorous Immutable Invariant — Normalized Axiom

Mode: ULTRA KIASU | ZERO ADMITS | INFINITE TIMELINE | QED ETERNUM
```

Every proof must be:
- **Complete** — No admits, no shortcuts
- **Verified** — Compiles with Coq 8.18+
- **Compatible** — Works with existing infrastructure
- **Documented** — Clear proof structure

---

**BEGIN ELIMINATION OF ALL 88 ADMITS. ABSOLUTE PERFECTION REQUIRED.**
