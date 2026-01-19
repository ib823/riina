# RIINA Coq Proof Delegation Prompts

## Generated: 2026-01-19
## Target: Claude AI, DeepSeek, Grok

---

## INSTRUCTIONS FOR EXTERNAL AI

You are helping prove lemmas for RIINA, a formally verified programming language.
The proofs use step-indexed logical relations for non-interference.

**Key Definitions:**
- `val_rel_n n Σ T v1 v2` - values v1, v2 are related at type T with step index n
- `store_rel_n n Σ st1 st2` - stores st1, st2 are related with step index n
- `exp_rel_le n Σ T e1 e2 st1 st2 ctx` - expressions are related
- `first_order_type T` - returns true if T has no function types

**Step-Index Structure:**
```coq
val_rel_n 0 Σ T v1 v2 = base case (structural info)
val_rel_n (S n) Σ T v1 v2 = val_rel_n n ∧ val_rel_struct conditions
```

---

## PRIORITY 0: CRITICAL BLOCKERS (3 lemmas)

### P0-1: val_rel_n_mono (HIGHEST PRIORITY)

**File:** `properties/NonInterference_v2.v`

```coq
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
```

**Proof Strategy:**
- This is DOWNWARD monotonicity (larger index implies smaller)
- Use strong induction on (n - m) or induction on n with generalized m
- Key insight: val_rel_n (S n) contains val_rel_n n as first conjunct
- Base case m = n is trivial (reflexivity)
- Inductive case: extract val_rel_n n from val_rel_n (S n), apply IH

**Expected Proof Pattern:**
```coq
Proof.
  intros m n Σ T v1 v2 Hle Hrel.
  generalize dependent m.
  induction n as [|n' IHn]; intros m Hle.
  - (* n = 0: m must be 0 *)
    assert (m = 0) by lia. subst. exact Hrel.
  - (* n = S n' *)
    destruct m as [|m'].
    + (* m = 0 *) simpl. exact I.  (* or appropriate base *)
    + (* m = S m' *)
      simpl in Hrel. destruct Hrel as [Hprev Hstruct].
      simpl. split.
      * apply IHn; [lia | exact Hprev].
      * exact Hstruct.
Qed.
```

---

### P0-2: val_rel_n_step_up

**File:** `properties/NonInterference_v2.v`

```coq
Lemma val_rel_n_step_up : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  val_rel_n (S n) Σ T v1 v2.
```

**Proof Strategy:**
- UPWARD step (from n to S n)
- For first-order types: use val_rel_n_step_up_fo (already proven)
- For higher-order types: need typing to ensure termination
- Case split on `first_order_type T`

---

### P0-3: store_rel_n_step_up

**File:** `properties/NonInterference_v2.v`

```coq
Lemma store_rel_n_step_up : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_rel_n (S n) Σ st1 st2.
```

**Proof Strategy:**
- Similar to val_rel_n_step_up but for stores
- Stores contain values at locations
- Need to show each location's values step up
- May require val_rel_n_step_up as helper

---

## PRIORITY 1: CRITICAL INFRASTRUCTURE (12 lemmas)

### P1-1: val_rel_le_to_n_attempt

**File:** `properties/RelationBridge.v`

```coq
Lemma val_rel_le_to_n_attempt : forall n Σ T v1 v2,
  val_rel_le n Σ T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

**Note:** This may be unprovable due to definition mismatch. Document if so.

---

### P1-2: store_rel_n_strengthen

**File:** `properties/RelationBridge.v`

```coq
Lemma store_rel_n_strengthen : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n n Σ' st1 st2.
```

**Proof Strategy:**
- Induction on n
- For S n case, show each location in Σ' has related values
- Use store_ty_extends to map locations

---

### P1-3: store_rel_n_weaken

**File:** `properties/RelationBridge.v`

```coq
Lemma store_rel_n_weaken : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
```

**Proof Strategy:**
- Opposite direction of strengthen
- Locations in Σ are subset of Σ'
- Should be straightforward with induction

---

### P1-4: exp_rel_le_ref

**File:** `properties/ReferenceOps.v`

```coq
Lemma exp_rel_le_ref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ T e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ (TRef T sl) (ERef e1 sl) (ERef e2 sl) st1 st2 ctx.
```

**Proof Strategy:**
- Unfold exp_rel_le
- Show ERef e evaluates by first evaluating e
- Apply exp_rel_le hypothesis to get related values
- Construct related references

---

### P1-5: exp_rel_le_deref

**File:** `properties/ReferenceOps.v`

```coq
Lemma exp_rel_le_deref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ T (EDeref e1) (EDeref e2) st1 st2 ctx.
```

---

### P1-6: exp_rel_le_assign

**File:** `properties/ReferenceOps.v`

```coq
Lemma exp_rel_le_assign : forall n Σ T sl e1 e2 e1' e2' st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  exp_rel_le n Σ T e1' e2' st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ TUnit (EAssign e1 e1') (EAssign e2 e2') st1 st2 ctx.
```

---

### P1-7: exp_rel_le_declassify

**File:** `properties/Declassification.v`

```coq
Lemma exp_rel_le_declassify : forall n Σ T e1 e2 p st1 st2 ctx,
  exp_rel_le n Σ (TSecret T) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ T (EDeclassify e1 p) (EDeclassify e2 p) st1 st2 ctx.
```

---

### P1-8: val_rel_n_mono_store_proof

**File:** `properties/KripkeMutual.v`

```coq
Theorem val_rel_n_mono_store_proof : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

---

### P1-9: val_rel_k_kripke_mono

**File:** `properties/NonInterferenceKripke.v`

```coq
Lemma val_rel_k_kripke_mono : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_k n Σ' T v1 v2 ->
  val_rel_k n Σ T v1 v2.
```

---

### P1-10: val_rel_le_to_inf

**File:** `properties/NonInterferenceZero.v`

```coq
Lemma val_rel_le_to_inf : forall Σ T v1 v2,
  (forall n, val_rel_le n Σ T v1 v2) ->
  val_rel_inf Σ T v1 v2.
```

---

### P1-11: val_rel_le_construct_fo

**File:** `properties/CumulativeRelation.v`

```coq
Lemma val_rel_le_construct_fo : forall T n Σ v1 v2,
  first_order_type T = true ->
  n > fo_compound_depth T ->
  is_value v1 = true ->
  is_value v2 = true ->
  closed_expr v1 = true ->
  closed_expr v2 = true ->
  val_rel_at_type_fo T v1 v2 ->
  val_rel_le n Σ T v1 v2.
```

---

### P1-12: fundamental_theorem (partial)

**File:** `properties/FundamentalTheorem.v`

```coq
Theorem fundamental_theorem : forall Γ Σ l e T ε,
  has_type Γ Σ l e T ε ->
  exp_rel Γ Σ T e e.
```

**Note:** Many cases remain. Focus on T_Var, T_Unit, T_Int, T_Bool first.

---

## PRIORITY 2: STANDARD (20+ lemmas)

### P2-1 through P2-7: MasterTheorem.v admits

See file for full context. Key lemmas:
- `master_fo_step_up`
- `store_ty_extensions_compatible`
- `step_preserves_closed`
- `fo_step_up_from_master`
- `store_wf_preserved`

### P2-8 through P2-12: NonInterferenceZero.v admits

- `val_rel_le_inf_to_n`
- `val_rel_le_inf_mono_store`
- Plus 3 more structural lemmas

### P2-13 through P2-15: StrongNormalization_v2.v admits

- `fundamental_reducibility` (large - 1000+ lines)
- `subst_env_commute`
- `SN_gives_val_rel_at_type_fn`

### P2-16 through P2-18: StepUpFromSN.v admits

- `val_rel_n_step_up_ho`
- `store_rel_n_step_up` (duplicate)
- `step_up_from_SN`

### P2-19 through P2-20: ReducibilityFull.v admits

- `subst_subst_env_commute`
- `fundamental_reducibility_full` (8 cases remain)

---

## BATCH PROCESSING TEMPLATE

For each lemma, use this template:

```
TASK: Prove this Coq lemma for RIINA step-indexed logical relations.

LEMMA:
[paste lemma statement]

CONTEXT:
[paste relevant definitions from context files]

HINTS:
[paste proof strategy from above]

REQUIREMENTS:
1. Complete Coq proof with intros, tactics, Qed
2. No admits or Admitted
3. Handle all cases
4. Use standard Coq tactics (induction, destruct, simpl, auto, lia)

OUTPUT FORMAT:
```coq
Proof.
  [your proof here]
Qed.
```
```

---

## CONTEXT FILES TO INCLUDE

When delegating, include these files (or relevant excerpts):

1. **Core Definitions:** `properties/NonInterference_v2.v` (lines 1-350)
2. **Type Definitions:** `foundations/Syntax.v` (full file)
3. **Semantics:** `foundations/Semantics.v` (step relation)
4. **Store Relations:** `properties/StoreRelation.v`
5. **Cumulative:** `properties/CumulativeRelation.v`

---

## SUCCESS CRITERIA

A proof is acceptable if:
1. Compiles with `coqc` without errors
2. Uses `Qed.` not `Admitted.`
3. Does not introduce new axioms
4. Follows existing code style

---

*Generated for RIINA Proof Delegation*
*Total Admits: 45*
*Priority P0: 3 (blocks everything)*
*Priority P1: 12 (critical infrastructure)*
*Priority P2: 30 (standard)*
