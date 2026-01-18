# AXIOM ELIMINATION ANALYSIS FOR NONINTERFERENCE.V

**Document ID:** AXIOM_ELIMINATION_ANALYSIS_v1.0.0
**Classification:** ULTRA KIASU | ZERO TRUST | ZERO LAZINESS
**Date:** 2026-01-18

---

## EXECUTIVE SUMMARY

This document provides a rigorous analysis of the 17 axioms in NonInterference.v and their proof strategies. The axioms concern **step-indexed logical relations** for proving noninterference properties.

### Axiom Status Matrix

| # | Axiom | Status | Blocking Factor |
|---|-------|--------|-----------------|
| 1 | `val_rel_n_to_val_rel` | ✅ PROVABLE | Requires `val_rel_n_step_up` |
| 2 | `val_rel_n_step_up` | ⚠️ CORE | Requires type structure induction |
| 3 | `store_rel_n_step_up` | ⚠️ DEPENDENT | Requires `val_rel_n_step_up` |
| 4-10 | `exp_rel_step1_*` | ⚠️ INFRASTRUCTURE | Requires small-step semantics |
| 11 | `tapp_step0_complete` | ✅ TRIVIAL | None |
| 12 | `val_rel_n_lam_cumulative` | ⚠️ DEPENDENT | Requires `val_rel_n_step_up` |
| 13 | `val_rel_at_type_to_val_rel_ho` | ⚠️ COMPLEX | Requires type induction |
| 14-17 | `logical_relation_*` | ⚠️ INFRASTRUCTURE | Requires store semantics |

---

## SECTION 1: TRIVIAL AXIOM

### 1.1 Axiom 11: `tapp_step0_complete`

**Statement:**
```coq
Axiom tapp_step0_complete : forall Σ' Σ''' T2
  (v1 v2 arg1 arg2 res1 res2 : expr) (st1 st2 st1' st2' : store)
  (ctx ctx' : effect_ctx),
  val_rel_n 0 Σ''' T2 res1 res2.
```

**Proof:**
```coq
Proof.
  intros. simpl. exact I.
Qed.
```

**Analysis:**
- By definition, `val_rel_n 0 Σ T v1 v2 = True` for all arguments
- This is the base case of the step-indexed relation
- The premises are completely irrelevant

**Effort:** 0 hours (literally trivial)

---

## SECTION 2: STEP CONVERSION AXIOMS (Category A)

### 2.1 Axiom 1: `val_rel_n_to_val_rel`

**Statement:**
```coq
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```

**Proof Strategy:**
1. Unfold `val_rel` as `forall n, val_rel_n n Σ T v1 v2`
2. For any target step `m`:
   - If `m <= S n`: Use `val_rel_n_mono` (monotonicity downward)
   - If `m > S n`: Use `val_rel_n_step_up` iteratively

**Key Insight:** The cumulative structure of `val_rel_n` means that higher steps contain lower steps, and we can always step up if values are proper values.

**Proof Skeleton:**
```coq
Proof.
  intros Σ T v1 v2 Hval1 Hval2 [n Hrel].
  unfold val_rel. intros m.
  destruct (le_lt_dec m (S n)) as [Hle | Hgt].
  - (* m <= S n *) eapply val_rel_n_mono; eassumption.
  - (* m > S n *) 
    (* Extract closed_expr from val_rel_n (S n) *)
    assert (Hcl1: closed_expr v1) by (simpl in Hrel; tauto).
    assert (Hcl2: closed_expr v2) by (simpl in Hrel; tauto).
    (* Iterate step-up from S n to m *)
    induction m.
    + simpl. exact I.
    + destruct (le_lt_dec (S m) (S n)).
      * eapply val_rel_n_mono; eassumption.
      * apply val_rel_n_step_up; try assumption.
        apply IHm. omega.
Qed.
```

**Dependencies:** `val_rel_n_mono` (available), `val_rel_n_step_up` (Axiom 2)

### 2.2 Axiom 2: `val_rel_n_step_up` (CRITICAL PATH)

**Statement:**
```coq
Axiom val_rel_n_step_up : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
```

**Proof Strategy:**
This is the **core lemma** requiring careful analysis by cases on `n`:

**Case n = 0:**
- Need to show `val_rel_n 1 Σ T v1 v2` from `val_rel_n 0 Σ T v1 v2 = True`
- This requires showing `val_rel_at_type` at step 0
- At step 0, the predicates `store_rel_n 0` and `val_rel_n 0` are `(fun _ => True)`
- So `val_rel_at_type` at step 0 reduces to checking **structural properties only**

**Case n = S n':**
- `val_rel_n (S n') Σ T v1 v2` gives us:
  - `val_rel_n n' Σ T v1 v2` (cumulative)
  - `value`, `closed_expr` properties
  - `val_rel_at_type Σ (store_rel_n n') (val_rel_n n') ... T v1 v2`
- Need to show `val_rel_n (S (S n')) Σ T v1 v2`:
  - Cumulative part: already have `val_rel_n (S n')`
  - Value/closed: given by hypothesis
  - `val_rel_at_type` at step `S n'`: **REQUIRES val_rel_at_type MONOTONICITY**

**Critical Sub-lemma Needed:**
```coq
Lemma val_rel_at_type_step_mono : forall T Σ 
  (sp sp' : store_ty -> store -> store -> Prop)
  (vl vl' : store_ty -> ty -> expr -> expr -> Prop)
  (sl sl' : store_ty -> store -> store -> Prop)
  v1 v2,
  (* If predicates step up... *)
  (forall Σ' st1 st2, sp Σ' st1 st2 -> sp' Σ' st1 st2) ->
  (forall Σ' T' x y, vl Σ' T' x y -> vl' Σ' T' x y) ->
  (forall Σ' st1 st2, sl Σ' st1 st2 -> sl' Σ' st1 st2) ->
  (* ...then val_rel_at_type steps up *)
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  val_rel_at_type Σ sp' vl' sl' T v1 v2.
```

**Proof by Induction on Type:**

| Type | Step-up Strategy |
|------|------------------|
| `TUnit` | Trivial: just check `v1 = EUnit /\ v2 = EUnit` |
| `TBool` | Trivial: check `exists b, v1 = EBool b /\ v2 = EBool b` |
| `TInt` | Trivial: check `v1 = v2` |
| `TProd T1 T2` | Structural: components step up by IH |
| `TSum T1 T2` | Structural: tagged values step up by IH |
| `TFn T1 T2 eff` | **COMPLEX**: Kripke property preserved by strengthening predicates |
| `TRef T sl` | Trivial: check location equality |

**The TFn Case in Detail:**

For function types, `val_rel_at_type` says:
```
forall Σ', store_ty_extends Σ Σ' ->
  forall x y, value x -> value y -> closed_expr x -> closed_expr y ->
    val_rel_lower Σ' T1 x y ->
    forall st1 st2 ctx, store_rel_pred Σ' st1 st2 ->
      exists v1' v2' st1' st2' ctx' Σ'',
        store_ty_extends Σ' Σ'' /\
        (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
        (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
        val_rel_lower Σ'' T2 v1' v2' /\
        store_rel_lower Σ'' st1' st2'
```

When stepping up:
- `val_rel_lower` changes from `val_rel_n n'` to `val_rel_n (S n')` 
- We must show: if the relation holds with weaker predicates, it holds with stronger ones
- This is **contravariant in premises** and **covariant in conclusions**

The key insight is:
- Input argument relation `val_rel_lower Σ' T1 x y` is used as a **premise**
- If we have `val_rel_n (S n') x y`, we can derive `val_rel_n n' x y` by monotonicity
- So **stronger input predicates are acceptable** (we just weaken them)
- Output relations are conclusions, so **stronger outputs are directly derivable**

### 2.3 Axiom 3: `store_rel_n_step_up`

**Statement:**
```coq
Axiom store_rel_n_step_up : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_rel_n (S n) Σ st1 st2.
```

**Proof Strategy:**
- Unfold `store_rel_n (S n)`:
  - `store_rel_n n Σ st1 st2` (given)
  - `store_max st1 = store_max st2` (from the given, by unwrapping)
  - For all locations `l, T, sl`: stored values are related at step `n`
- The third conjunct requires: `val_rel_n n Σ T v1 v2` for stored values
- From `store_rel_n n`, we have `val_rel_n (n-1) Σ T v1 v2`
- **PROBLEM**: We need `val_rel_n n` but only have `val_rel_n (n-1)`

**Resolution:**
The statement as written is **NOT provable without additional premises**.

**Corrected Statement:**
```coq
Lemma store_rel_n_step_up_strong : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  (* All stored values must be proper values that can step up *)
  (forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    forall v1 v2,
      store_lookup l st1 = Some v1 ->
      store_lookup l st2 = Some v2 ->
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2) ->
  store_rel_n (S n) Σ st1 st2.
```

**Alternative:** If stores only contain values (enforced by typing), then the additional premise is automatically satisfied.

---

## SECTION 3: STEP-1 TERMINATION AXIOMS (Category B)

These axioms follow a uniform pattern:

### General Pattern

```coq
(* For elimination form E *)
Lemma exp_rel_step1_E : forall Σ T v v' st1 st2 ctx Σ',
  store_ty_extends Σ Σ' ->
  val_rel_n 1 Σ' (input_type) v v' ->
  store_rel_n 1 Σ' st1 st2 ->
  exists v1' v2' st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (E v, st1, ctx) -->* (v1', st1', ctx') /\
    (E v', st2, ctx) -->* (v2', st2', ctx') /\
    val_rel_n 1 Σ'' (output_type) v1' v2' /\
    store_rel_n 1 Σ'' st1' st2'.
```

### Required Infrastructure

1. **Canonical Forms Lemmas:**
```coq
Lemma canonical_forms_prod : forall v T1 T2,
  value v -> has_type v (TProd T1 T2) ->
  exists e1 e2, v = EPair e1 e2.

Lemma canonical_forms_sum : forall v T1 T2,
  value v -> has_type v (TSum T1 T2) ->
  (exists e, v = EInl e) \/ (exists e, v = EInr e).

Lemma canonical_forms_bool : forall v,
  value v -> has_type v TBool ->
  exists b, v = EBool b.

Lemma canonical_forms_fn : forall v T1 T2 eff,
  value v -> has_type v (TFn T1 T2 eff) ->
  exists x body, v = ELam x T1 body.
```

2. **Small-Step Reduction Lemmas:**
```coq
Lemma step_fst : forall e1 e2 st ctx,
  (EFst (EPair e1 e2), st, ctx) --> (e1, st, ctx).

Lemma step_snd : forall e1 e2 st ctx,
  (ESnd (EPair e1 e2), st, ctx) --> (e2, st, ctx).

Lemma step_case_inl : forall e e1 e2 st ctx,
  (ECase (EInl e) e1 e2, st, ctx) --> (EApp e1 e, st, ctx).

Lemma step_case_inr : forall e e1 e2 st ctx,
  (ECase (EInr e) e1 e2, st, ctx) --> (EApp e2 e, st, ctx).

Lemma step_if_true : forall e1 e2 st ctx,
  (EIf (EBool true) e1 e2, st, ctx) --> (e1, st, ctx).

Lemma step_if_false : forall e1 e2 st ctx,
  (EIf (EBool false) e1 e2, st, ctx) --> (e2, st, ctx).

Lemma step_app_lam : forall x T body arg st ctx,
  value arg ->
  (EApp (ELam x T body) arg, st, ctx) --> (subst x arg body, st, ctx).
```

### Specific Axiom Proofs

**Axiom 4 (fst):**
```coq
Proof.
  intros.
  (* From val_rel_n 1 for TProd, extract pair structure *)
  simpl in H0. destruct H0 as [_ [Hv1 [Hv2 [Hc1 [Hc2 Hat]]]]].
  simpl in Hat. 
  destruct Hat as [e1 [e2 [e1' [e2' [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
  subst.
  (* EFst (EPair e1 e2) --> e1 *)
  exists e1, e1', st1, st2, ctx, Σ'.
  split; [apply store_ty_extends_refl|].
  repeat split.
  - apply multi_step_single. apply step_fst.
  - apply multi_step_single. apply step_fst.
  - (* Show val_rel_n 1 for e1, e1' from Hr1 which is val_rel_n 0 *)
    (* Requires: e1, e1' are values (follows from EPair value) *)
    apply val_rel_n_step_up; [admit | admit | admit | admit | exact Hr1].
  - assumption.
Qed.
```

**Axiom 7 (if):** Already proven in axiom_elimination_proofs.v

---

## SECTION 4: HIGHER-ORDER HELPERS (Category D)

### 4.1 Axiom 12: `val_rel_n_lam_cumulative`

This is a **specialization** of `val_rel_n_step_up` for lambda expressions:

```coq
Proof.
  intros.
  apply val_rel_n_step_up.
  - (* value (ELam ...) *) apply value_lam.
  - (* value (ELam ...) *) apply value_lam.
  - (* closed_expr (ELam ...) *) apply closed_lam. (* with body closed under x *)
  - (* closed_expr (ELam ...) *) apply closed_lam.
  - assumption.
Qed.
```

**Required Lemmas:**
```coq
Lemma value_lam : forall x T body, value (ELam x T body).
Lemma closed_lam : forall x T body,
  closed_under [x] body -> closed_expr (ELam x T body).
```

### 4.2 Axiom 13: `val_rel_at_type_to_val_rel_ho`

This is the **strongest and most complex** axiom.

**Statement:**
```coq
Axiom val_rel_at_type_to_val_rel_ho : forall Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2,
  val_rel_at_type Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2 ->
  value arg1 -> value arg2 ->
  val_rel Σ T arg1 arg2.
```

**The Problem:**
- `val_rel_at_type` uses **arbitrary predicates** as parameters
- We need to show these imply `val_rel`, which is defined using **specific step-indexed predicates**
- This is only valid if the provided predicates are **at least as strong** as `val_rel_n n` for all `n`

**Required Strengthening:**
```coq
Lemma val_rel_at_type_to_val_rel_ho_strong : 
  forall Σ (store_rel_lower : store_ty -> store -> store -> Prop)
         (val_rel_lower : store_ty -> ty -> expr -> expr -> Prop)
         (store_rel_any : store_ty -> store -> store -> Prop)
         T arg1 arg2,
  val_rel_at_type Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2 ->
  value arg1 -> value arg2 ->
  closed_expr arg1 -> closed_expr arg2 ->
  (* CRITICAL: predicates must imply val_rel *)
  (forall Σ' T' v1 v2, val_rel_lower Σ' T' v1 v2 -> val_rel Σ' T' v1 v2) ->
  (forall Σ' st1 st2, store_rel_lower Σ' st1 st2 -> store_rel Σ' st1 st2) ->
  (forall Σ' st1 st2, store_rel_any Σ' st1 st2 -> store_rel Σ' st1 st2) ->
  val_rel Σ T arg1 arg2.
```

**Proof by Type Induction:**

For base types (Unit, Bool, Int, Ref): structural matching suffices.

For compound types (Prod, Sum): IH on components.

For function types: The Kripke property must be shown to hold at all steps.

---

## SECTION 5: REFERENCE OPERATIONS (Category E)

These require the **expression logical relation** definition:

```coq
Definition exp_rel_n (n : nat) (Σ : store_ty) (Γ Δ : env)
                      (e : expr) (T : ty) (ε : effect_ctx)
                      (ρ1 ρ2 : subst) : Prop :=
  forall st1 st2 ctx,
    store_rel_n n Σ st1 st2 ->
    subst_rel_n n Σ Γ ρ1 ρ2 ->  (* Substitutions are related *)
    exists v1 v2 st1' st2' ctx' Σ',
      store_ty_extends Σ Σ' /\
      (subst_expr ρ1 e, st1, ctx) -->* (v1, st1', ctx') /\
      (subst_expr ρ2 e, st2, ctx) -->* (v2, st2', ctx') /\
      val_rel_n n Σ' T v1 v2 /\
      store_rel_n n Σ' st1' st2'.
```

### 5.1 Axiom 14: `logical_relation_ref`

**Key Challenge:** Allocation extends the store typing.

```coq
Proof.
  intros.
  unfold exp_rel_n. intros st1 st2 ctx Hsrel Hsubst.
  (* 1. Evaluate e to related values v1, v2 *)
  specialize (H st1 st2 ctx Hsrel Hsubst).
  destruct H as [v1 [v2 [st1' [st2' [ctx' [Σ' [...]]]]]]].
  (* 2. Allocate in both stores at a fresh location l *)
  (* st1'' = st1'[l := v1], st2'' = st2'[l := v2] *)
  (* Σ'' = Σ' extended with (l, T, sec_label) *)
  exists l, l, st1'', st2'', ctx', Σ''.
  repeat split.
  - (* store_ty_extends Σ' Σ'' *) apply store_ty_extends_alloc.
  - (* Reduction steps *)
  - (* val_rel_n for locations: same location *)
    simpl. exists l. reflexivity.
  - (* store_rel_n: must include new location *)
    (* At location l: values v1, v2 are related by construction *)
Qed.
```

**Required Lemmas:**
```coq
Lemma store_ty_extends_alloc : forall Σ l T sl,
  l >= store_ty_max Σ ->
  store_ty_extends Σ (store_ty_add l T sl Σ).

Lemma store_rel_n_alloc : forall n Σ Σ' l T sl st1 st2 v1 v2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ st1 st2 ->
  val_rel_n n Σ' T v1 v2 ->
  store_rel_n n Σ' (store_add l v1 st1) (store_add l v2 st2).
```

---

## SECTION 6: COMPLETE DEPENDENCY GRAPH

```
                    ┌─────────────────────────────────────┐
                    │ val_rel_n_step_up (AXIOM 2)         │
                    │ [TYPE STRUCTURE INDUCTION]          │
                    └──────────────────┬──────────────────┘
                                       │
           ┌───────────────────────────┼───────────────────────────┐
           │                           │                           │
           ▼                           ▼                           ▼
┌──────────────────────┐    ┌────────────────────────┐    ┌────────────────────┐
│ store_rel_n_step_up  │    │ val_rel_n_to_val_rel   │    │ val_rel_n_lam_     │
│ (AXIOM 3)            │    │ (AXIOM 1)              │    │ cumulative (AX 12) │
└──────────────────────┘    └────────────────────────┘    └────────────────────┘
                                       │
                                       ▼
                            ┌────────────────────────┐
                            │ val_rel_at_type_to_    │
                            │ val_rel_ho (AXIOM 13)  │
                            └────────────────────────┘

INFRASTRUCTURE DEPENDENCIES:
┌────────────────────────────────────────────────────────────────────────────┐
│                                                                            │
│  SMALL-STEP SEMANTICS ────────► exp_rel_step1_* (AXIOMS 4-10)             │
│                                                                            │
│  CANONICAL FORMS ─────────────► exp_rel_step1_* (AXIOMS 4-10)             │
│                                                                            │
│  STORE ALLOCATION/LOOKUP ─────► logical_relation_* (AXIOMS 14-17)         │
│                                                                            │
└────────────────────────────────────────────────────────────────────────────┘
```

---

## SECTION 7: RECOMMENDED PROOF ORDER

### Phase 1: Infrastructure (Must be done first)
1. Prove `value_lam`, `closed_lam`, `value_pair`, etc.
2. Prove canonical forms lemmas
3. Prove small-step reduction lemmas for eliminators
4. Prove store allocation/lookup lemmas

### Phase 2: Core Step-Up (Critical Path)
1. **`val_rel_n_step_up`** (Axiom 2) - The KEY lemma
2. `store_rel_n_step_up` (Axiom 3) - Follows from Axiom 2
3. `val_rel_n_to_val_rel` (Axiom 1) - Uses Axioms 2 and monotonicity

### Phase 3: Step-1 Termination
4. `exp_rel_step1_fst` (Axiom 4)
5. `exp_rel_step1_snd` (Axiom 5)
6. `exp_rel_step1_case` (Axiom 6)
7. `exp_rel_step1_if` (Axiom 7) - Already proven
8. `exp_rel_step1_let` (Axiom 8) - Already proven
9. `exp_rel_step1_handle` (Axiom 9)
10. `exp_rel_step1_app` (Axiom 10)

### Phase 4: Higher-Order
11. `val_rel_n_lam_cumulative` (Axiom 12)
12. `val_rel_at_type_to_val_rel_ho` (Axiom 13)

### Phase 5: Reference Operations
13. `logical_relation_ref` (Axiom 14)
14. `logical_relation_deref` (Axiom 15)
15. `logical_relation_assign` (Axiom 16)
16. `logical_relation_declassify` (Axiom 17)

### Phase 6: Trivial
17. `tapp_step0_complete` (Axiom 11) - Can be done anytime

---

## SECTION 8: EFFORT ESTIMATES

| Phase | Axiom Count | Hours (Min) | Hours (Max) |
|-------|-------------|-------------|-------------|
| Infrastructure | N/A | 40 | 80 |
| Core Step-Up | 3 | 60 | 120 |
| Step-1 Termination | 7 | 56 | 112 |
| Higher-Order | 2 | 40 | 80 |
| Reference Operations | 4 | 48 | 96 |
| Trivial | 1 | 0 | 1 |
| **TOTAL** | **17** | **244** | **489** |

---

## SECTION 9: FINAL NOTES

### Critical Insights

1. **The Kripke Structure is Essential**: Store typing extension (`store_ty_extends`) is what makes the logical relation work with mutable state.

2. **Cumulative Structure Enables Monotonicity**: `val_rel_n (S n)` contains `val_rel_n n` as a conjunct, making downward monotonicity trivial.

3. **Step-Up is Harder Than Step-Down**: Going from step `n` to step `S n` requires proving `val_rel_at_type` with stronger predicates.

4. **First-Order Types are Easy**: For types without function arrows, the structural matching is straightforward.

5. **Function Types Require Contravariance Analysis**: Input predicates are premises (can be weakened), output predicates are conclusions (must be strengthened).

---

**Document Hash:** [To be computed on finalization]
**Classification:** ULTRA KIASU | ZERO TRUST | ZERO LAZINESS
