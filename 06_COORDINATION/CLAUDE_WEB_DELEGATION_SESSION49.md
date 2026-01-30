# Claude AI Web Delegation — Session 49

## Assessment & Limitations

### What Claude AI Web CAN do
- Read public GitHub repos
- Prove self-contained Coq lemmas when given ALL definitions
- Work on files that DON'T conflict with Claude Code's concurrent work

### What Claude AI Web CANNOT do reliably
- Reconstruct Coq proof state mid-proof (4000+ line files with 30 imports)
- Invent new infrastructure lemmas for complex step-indexed relations
- Work on the same file Claude Code is editing (merge conflicts)

### Track record on this codebase
- Session 47: 3/4 outputs rejected (hallucinated lemmas, wrong proofs)
- Session 45.5: Phase 4 outputs not integrable (simplified type systems)
- Success rate: ~25% for complex proofs, ~80% for standalone structural proofs

---

## DELEGATION TASK 1: ReferenceOps.v — 3 Lemmas (exp_rel_le_ref/deref/assign)

**Conflict-free:** YES — Claude Code will work on NonInterference_v2_LogicalRelation.v
**Estimated success probability:** 60% (concrete fix, all helpers exist)
**File to modify:** `02_FORMAL/coq/properties/ReferenceOps.v`

### PROMPT (copy-paste to Claude AI Web)

---

**START OF PROMPT**

You are a Coq proof engineer. Your task is to prove 3 admitted lemmas in a formal verification project.

**Repository:** https://github.com/ib823/proof (public)
**Target file:** `02_FORMAL/coq/properties/ReferenceOps.v`

### Step 1: Read these files from the repository (in order)

1. `02_FORMAL/coq/foundations/Syntax.v` — Core types: `expr`, `ty`, `store`, `store_ty`, `value`, `store_lookup`, `store_update`, `fresh_loc`
2. `02_FORMAL/coq/foundations/Semantics.v` — `step` inductive (all constructors), `multi_step` inductive, `store_has_values`, `value_not_step`
3. `02_FORMAL/coq/foundations/Typing.v` — `store_wf`, `store_ty_extends`, `has_type`
4. `02_FORMAL/coq/properties/CumulativeRelation.v` — `val_rel_le`, `exp_rel_le`, `store_rel_le`, `store_rel_simple`
5. `02_FORMAL/coq/properties/StoreRelation.v` — `store_rel_le_lookup`, `store_rel_le_update`, `store_ty_extends_alloc`, `fresh_loc_not_in_store_ty`, `val_rel_le_build_ref`
6. `02_FORMAL/coq/properties/KripkeProperties.v` — `val_rel_le_unit`, `val_rel_le_build_unit`
7. `02_FORMAL/coq/properties/ReferenceOps.v` — THE TARGET FILE (read entire file)

### Step 2: Understand the root cause

All 3 lemmas are admitted because of a **context mismatch**:

- `exp_rel_le` quantifies over `ctx'` (final context may differ from initial `ctx`)
- `multi_step_ref_inversion`, `multi_step_deref_inversion`, `multi_step_assign_inversion` all require `ctx' = ctx`

The fix: `step` preserves context (already proven at line 50-54 of ReferenceOps.v):

```coq
Lemma step_preserves_ctx : forall e st ctx e' st' ctx',
  (e, st, ctx) --> (e', st', ctx') -> ctx' = ctx.
```

You need to extend this to `multi_step`:

```coq
Lemma multi_step_preserves_ctx : forall e st ctx e' st' ctx',
  multi_step (e, st, ctx) (e', st', ctx') -> ctx' = ctx.
```

This is a trivial induction on `multi_step` using `step_preserves_ctx`.

### Step 3: Prove the 3 lemmas

**Lemma 1: `exp_rel_le_ref`** (line 257-264)
```coq
Lemma exp_rel_le_ref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ T e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ (TRef T sl) (ERef e1 sl) (ERef e2 sl) st1 st2 ctx.
```

Proof sketch:
1. Unfold `exp_rel_le`. Intros.
2. Given `multi_step (ERef e1 sl, st1, ctx) (v1, st1', ctx')` and `multi_step (ERef e2 sl, st2, ctx) (v2, st2', ctx')`.
3. Assert `ctx' = ctx` using `multi_step_preserves_ctx`. Subst.
4. Apply `multi_step_ref_inversion` to decompose both evaluations.
5. From inversion: inner expression evaluates to values, result is `ELoc l`, store updated.
6. Apply premise `He_rel` (the `exp_rel_le n Σ T e1 e2` hypothesis) to the inner multi-steps.
7. Get `Σ'` with `val_rel_le k Σ' T v1_inner v2_inner` and `store_rel_simple Σ' st1_mid st2_mid`.
8. Use `logical_relation_ref_proven` or construct the reference relation directly.
9. Show `val_rel_le k Σ_ext (TRef T sl) (ELoc l1) (ELoc l2)` and `store_rel_simple` for updated stores.

**WARNING:** The tricky part is that `multi_step_ref_inversion` gives `l = fresh_loc st_mid` for EACH side independently. For the proof to work, you need `fresh_loc st1_mid = fresh_loc st2_mid`, which follows from `store_rel_simple Σ' st1_mid st2_mid` (which implies `store_max st1_mid = store_max st2_mid`, and `fresh_loc` depends only on `store_max`).

Check: how is `fresh_loc` defined? Read Syntax.v or Semantics.v.

**Lemma 2: `exp_rel_le_deref`** (line 293-300)
```coq
Lemma exp_rel_le_deref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ T (EDeref e1) (EDeref e2) st1 st2 ctx.
```

Proof sketch:
1. Same context fix as above.
2. Apply `multi_step_deref_inversion` (needs `store_has_values` — check if this is available or needs to be assumed).
3. From inversion: inner expressions evaluate to `ELoc l`, store unchanged, `store_lookup l st' = Some v`.
4. Apply `He_rel` to inner multi-steps to get `val_rel_le` at ref type.
5. Extract that both locations are the same `l` (from `val_rel_le` at `TRef T sl` — related refs point to same location).
6. Use `store_rel_le_lookup` to get related values from the store.

**WARNING:** `multi_step_deref_inversion` has premise `store_has_values st`. You need to either:
- Add this as a premise to `exp_rel_le_deref`, OR
- Derive it from `store_rel_le` or `store_wf`, OR
- Show it's preserved from the initial store

Check the exact signature of `multi_step_deref_inversion` in ReferenceOps.v.

**Lemma 3: `exp_rel_le_assign`** (line 334-342)
```coq
Lemma exp_rel_le_assign : forall n Σ T sl e1 e2 e1' e2' st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  exp_rel_le n Σ T e1' e2' st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ TUnit (EAssign e1 e1') (EAssign e2 e2') st1 st2 ctx.
```

This is the hardest. It requires:
1. Context fix.
2. `multi_step_assign_inversion` decomposition (3-phase: eval location, eval value, perform assign).
3. Sequential application of `exp_rel_le` twice.
4. `store_rel_le_update` to show stores remain related after update.
5. `val_rel_le_unit` for the unit result.

### Step 4: Important checks before writing proofs

Before writing any proof, verify:

1. **`fresh_loc` definition** — Is `fresh_loc st = S (store_max st)` or similar? This matters for `exp_rel_le_ref`.
2. **`store_rel_simple` definition** — Does it give `store_max st1 = store_max st2`? If so, `fresh_loc st1 = fresh_loc st2`.
3. **`multi_step_deref_inversion` premises** — Does it require `store_has_values`? If so, can this be derived from `store_rel_le`?
4. **`val_rel_le` at `TRef T sl`** — What does it unfold to? Does it give `v1 = ELoc l1 /\ v2 = ELoc l2 /\ l1 = l2`?
5. **`exp_rel_le` at step 0** — Is it `True`? (Check CumulativeRelation.v.) If so, some lemmas may need case split on `n`.

### Deliverable

Provide the complete replacement for lines 257-264, 293-300, and 334-342 of ReferenceOps.v. Include:
- The `multi_step_preserves_ctx` helper lemma (to be placed before the 3 main lemmas)
- Any other helper lemmas needed
- Complete tactic proofs ending with `Qed.`
- NO `admit`, `Admitted`, or new `Axiom`

If any lemma is UNPROVABLE with the current definitions, say so explicitly and explain exactly why. Do not provide a fake proof.

**END OF PROMPT**

---

## DELEGATION TASK 2: store_wf/stores_agree extraction from store_rel_n

**Conflict-free:** YES — different region of NI_v2_LR (lines 3082-3084) than step-1 admits
**Estimated success probability:** 40% (store_wf is NOT directly in store_rel_n; stores_agree_low_fo MAY be extractable)
**File to modify:** `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v` (lines 3082-3084 only)

**CRITICAL NOTE:** After reading `store_rel_n` definition (NonInterference_v2.v:420-439):
- `store_rel_n (S n')` contains: pointwise `val_rel_n` at typed locations, `store_max` equality
- It does NOT contain `store_wf` (which requires bidirectional: typed→value AND value→typed)
- `stores_agree_low_fo` MAY be derivable from `store_rel_n` for FO low types
- Claude AI Web should honestly report if these are NOT provable from available hypotheses

### PROMPT (copy-paste to Claude AI Web)

---

**START OF PROMPT**

You are a Coq proof engineer. Your task is to prove 3 small assertions inside a larger proof in a formal verification project.

**Repository:** https://github.com/ib823/proof (public)
**Target file:** `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v`

### Context

At lines 3082-3084, there are 3 `admit` calls:

```coq
assert (Hwf1'' : store_wf Σ'' st1'') by admit.
assert (Hwf2'' : store_wf Σ'' st2'') by admit.
assert (Hagree'' : stores_agree_low_fo Σ'' st1'' st2'') by admit.
```

These are inside the T_App case of the `logical_relation` theorem, after evaluating both function and argument.

### What you need to understand

Read these files:

1. `02_FORMAL/coq/foundations/Typing.v` — `store_wf` definition (lines ~215-222)
2. `02_FORMAL/coq/properties/NonInterference_v2.v` — Search for:
   - `store_rel_n` definition (what does it contain?)
   - `stores_agree_low_fo` definition
   - Any lemma that extracts `store_wf` from `store_rel_n`
   - `store_rel_n_store_wf` or similar

3. `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v` — Read lines 3060-3090 for the full context around the admits.

### The key question

The hypothesis available is:
```coq
Hstore2 : store_rel_n n'' Σ'' st1'' st2''
```

Does `store_rel_n n Σ st1 st2` contain or imply:
- `store_wf Σ st1`?
- `store_wf Σ st2`?
- `stores_agree_low_fo Σ st1 st2`?

Search for the definition of `store_rel_n` in `NonInterference_v2.v`. It's a `Fixpoint` that unfolds based on `n`. Check what fields it contains at both `n = 0` and `n = S n'`.

### What I need

1. Either prove the 3 assertions from `Hstore2`, OR
2. Tell me it's impossible (explain exactly what's missing from `store_rel_n`), OR
3. Identify what additional hypothesis is needed and where it could come from

### Deliverable

If provable, provide 3 replacement lines:
```coq
assert (Hwf1'' : store_wf Σ'' st1'') by (PROOF_HERE).
assert (Hwf2'' : store_wf Σ'' st2'') by (PROOF_HERE).
assert (Hagree'' : stores_agree_low_fo Σ'' st1'' st2'') by (PROOF_HERE).
```

Or helper extraction lemmas:
```coq
Lemma store_rel_n_store_wf_left : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 -> store_wf Σ st1.
(* ... *)
```

If NOT provable, explain what `store_rel_n` actually contains and what's missing.

**END OF PROMPT**

---

## WHAT CLAUDE CODE DOES IN PARALLEL (NO CONFLICTS)

While Claude AI Web works on Tasks 1 and 2:

| Claude Code Task | File/Region | Why No Conflict |
|-----------------|-------------|-----------------|
| Eliminate step-1 admits (lines 3055, 3409-3415, 3588, 3686, 3798) | NI_v2_LR lines 3040-3800 | Task 1 is in ReferenceOps.v; Task 2 is lines 3082-3084 only (different region) |
| Eliminate fundamental admit (line 2828) | NI_v2_LR line 2820-2830 | Different region from both tasks |
| Rust prototype work (Track B) | 03_PROTO/ | Completely separate codebase |
| Tooling crypto (Track F) | 05_TOOLING/ | Completely separate codebase |

**IMPORTANT:** Claude Code should NOT touch ReferenceOps.v or lines 3082-3084 of NI_v2_LR while delegation is running.

---

## HOW TO INTEGRATE CLAUDE AI WEB OUTPUT

### For Task 1 (ReferenceOps.v):
1. Receive output from Claude AI Web
2. Create a test file: `02_FORMAL/coq/properties/ReferenceOps_test.v` with the proposed proofs
3. Run `coqc -Q . RIINA properties/ReferenceOps_test.v`
4. If compiles: replace admits in ReferenceOps.v
5. If fails: analyze error, decide if fixable or reject

### For Task 2 (store_wf extraction):
1. Receive output from Claude AI Web
2. If it provides extraction lemmas: add to NonInterference_v2.v or NI_v2_LR
3. Replace the 3 `by admit` lines
4. Run `make` to verify

### Rejection criteria
- Any output using `admit`, `Admitted`, or new `Axiom` → REJECT
- Any output redefining existing types → REJECT
- Any output that doesn't compile against current codebase → REJECT (but may be fixable)
- Any output proving the wrong lemma → REJECT

---

## ASSESSMENT SUMMARY

| Task | File | Success Prob. | Conflict Risk | Value if Successful |
|------|------|--------------|---------------|---------------------|
| 1: ReferenceOps 3 lemmas | ReferenceOps.v | 60% | NONE | −6 admits (3 admit + 3 Admitted) |
| 2: store_wf extraction | NI_v2_LR:3082-84 | 40% | NONE | −3 admits (or honest "not provable" report) |
| **Total potential** | | | | **−6 to −9 admits** |

**Honest assessment:** Task 1 is the better bet. The context preservation fix is concrete and all helpers exist. Task 2 is harder than it looks — `store_rel_n` does NOT contain `store_wf` directly (it only has forward direction: typed locations → values exist, not reverse). The most valuable outcome from Task 2 may be an honest "this requires threading store_wf through exp_rel_n" report, which informs architectural decisions.

**What to expect:** If Claude AI Web succeeds on Task 1, that's −6 admits from ReferenceOps.v (bringing it to 0 admits). Task 2 will likely either partially succeed (stores_agree provable, store_wf not) or provide a useful analysis of what's missing.
