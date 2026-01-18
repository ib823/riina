# TASK PROMPTS FOR CLAUDE AI (WEB)

Use these by copying the CLAUDE_AI_DELEGATION_PROMPT.md first, then appending one of these tasks in Section 4.

---

## TASK 1: Type Measure for Well-Founded Induction

**SPECIFIC TASK:**

Create a complete Coq implementation for well-founded induction on types:

1. Define `ty_measure : ty -> nat` that satisfies:
   - Primitive types (TUnit, TBool, TInt, TString, TBytes) have measure 0
   - `ty_measure (TFn T1 T2 _) = 1 + ty_measure T1 + ty_measure T2`
   - `ty_measure (TProd T1 T2) = 1 + ty_measure T1 + ty_measure T2`
   - `ty_measure (TSum T1 T2) = 1 + ty_measure T1 + ty_measure T2`
   - All other compound types: `1 + ty_measure T_inner`
   - Security wrapper types (TSecret, TLabeled, etc.): `1 + ty_measure T_inner`

2. Prove `ty_measure_TFn_arg : forall T1 T2 eff, ty_measure T1 < ty_measure (TFn T1 T2 eff)`

3. Prove `ty_measure_TFn_ret : forall T1 T2 eff, ty_measure T2 < ty_measure (TFn T1 T2 eff)`

4. Prove `ty_measure_TProd_fst : forall T1 T2, ty_measure T1 < ty_measure (TProd T1 T2)`

5. Prove `ty_measure_TProd_snd : forall T1 T2, ty_measure T2 < ty_measure (TProd T1 T2)`

6. Define an induction principle using `Wf_nat.lt_wf`:
   ```coq
   Lemma ty_measure_ind : forall (P : ty -> Prop),
     (forall T, (forall T', ty_measure T' < ty_measure T -> P T') -> P T) ->
     forall T, P T.
   ```

**OUTPUT:** Complete Coq code with ALL proofs ending in `Qed.`

---

## TASK 2: Step-Up for Primitive First-Order Types

**SPECIFIC TASK:**

Prove step-up lemmas for each primitive first-order type. The general pattern:

For type T in {TUnit, TBool, TInt, TString, TBytes}:

```coq
Lemma val_rel_le_step_up_T : forall n Σ v1 v2,
  val_rel_le n Σ T v1 v2 ->
  n > 0 ->
  forall m, val_rel_le m Σ T v1 v2.
```

**Proof Strategy for each:**
1. Destruct n; the n=0 case contradicts n > 0
2. For n = S n', extract structural info from val_rel_le (S n')
3. The structural info is step-independent (equality)
4. Use induction on m to rebuild val_rel_le m with same structural info

**OUTPUT:** Five complete lemmas with proofs for TUnit, TBool, TInt, TString, TBytes.

---

## TASK 3: Substitution Typing Lemma

**SPECIFIC TASK:**

Prove that substitution preserves typing:

```coq
Lemma substitution_preserves_typing : forall Γ Σ Δ x T1 e T2 ε v,
  has_type ((x, T1) :: Γ) Σ Δ e T2 ε ->
  has_type nil Σ Δ v T1 EffectPure ->
  value v ->
  closed_expr v ->
  has_type Γ Σ Δ ([x := v] e) T2 ε.
```

Where `[x := v] e` is defined as:
```coq
Fixpoint subst (x : ident) (v : expr) (e : expr) : expr := ...
Notation "[ x := v ] e" := (subst x v e).
```

**Proof Strategy:**
1. Induction on the typing derivation `has_type ((x, T1) :: Γ) Σ Δ e T2 ε`
2. Handle each typing rule case
3. Key cases:
   - T_Var: if y = x, substitute; if y ≠ x, lookup unchanged
   - T_Lam: handle shadowing when binding same variable
   - T_App: apply IH to both subterms

**OUTPUT:** Complete proof with all cases handled.

---

## TASK 4: Value Inversion Lemmas

**SPECIFIC TASK:**

Prove canonical forms lemmas for each type:

```coq
Lemma canonical_forms_unit : forall v,
  value v -> (* and v has type TUnit *)
  v = EUnit.

Lemma canonical_forms_bool : forall v,
  value v -> (* and v has type TBool *)
  exists b, v = EBool b.

Lemma canonical_forms_int : forall v,
  value v -> (* and v has type TInt *)
  exists i, v = EInt i.

Lemma canonical_forms_fn : forall v T1 T2 eff,
  value v -> (* and v has type TFn T1 T2 eff *)
  exists x body, v = ELam x T1 body.

Lemma canonical_forms_pair : forall v T1 T2,
  value v -> (* and v has type TProd T1 T2 *)
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.

Lemma canonical_forms_sum : forall v T1 T2,
  value v -> (* and v has type TSum T1 T2 *)
  (exists v', v = EInl v' T2 /\ value v') \/
  (exists v', v = EInr v' T1 /\ value v').
```

**Proof Strategy:**
- Inversion on the value hypothesis
- Combined with typing if needed

**OUTPUT:** Six complete lemmas with proofs.

---

## TASK 5: Store Typing Extension Transitivity

**SPECIFIC TASK:**

Prove properties about store typing extension:

```coq
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
                 store_ty_lookup l Σ' = Some (T, sl).

Lemma store_ty_extends_refl : forall Σ,
  store_ty_extends Σ Σ.

Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.

Lemma store_ty_extends_lookup : forall Σ Σ' l T sl,
  store_ty_extends Σ Σ' ->
  store_ty_lookup l Σ = Some (T, sl) ->
  store_ty_lookup l Σ' = Some (T, sl).
```

**OUTPUT:** Three complete lemmas with proofs.

---

## TASK 6: First-Order Type Decidability

**SPECIFIC TASK:**

Prove that first_order_type is decidable and its key properties:

```coq
Lemma first_order_decidable : forall T,
  {first_order_type T = true} + {first_order_type T = false}.

Lemma first_order_TFn_false : forall T1 T2 eff,
  first_order_type (TFn T1 T2 eff) = false.

Lemma first_order_TProd : forall T1 T2,
  first_order_type (TProd T1 T2) = first_order_type T1 && first_order_type T2.

Lemma first_order_TSum : forall T1 T2,
  first_order_type (TSum T1 T2) = first_order_type T1 && first_order_type T2.

Lemma first_order_components : forall T1 T2,
  first_order_type (TProd T1 T2) = true ->
  first_order_type T1 = true /\ first_order_type T2 = true.
```

**OUTPUT:** Five complete lemmas with proofs.

---

---

## TASK 7: exp_rel_step1_if — AXIOM ELIMINATION (HIGH PRIORITY)

**SPECIFIC TASK:**

Using the REVOLUTIONARY `val_rel_n_base` from Section 4.5, prove that IF expressions with related boolean conditions step to related branches:

```coq
(** exp_rel_step1_if: Related booleans take SAME branch

    KEY INSIGHT: val_rel_n_base TBool gives us SAME boolean (exists b, v1 = EBool b /\ v2 = EBool b)
    This means both step to the SAME branch!
*)
Theorem exp_rel_step1_if : forall Σ v v' e2 e2' e3 e3' st1 st2 ctx,
  val_rel_n_base Σ TBool v v' ->
  store_rel_n_base Σ st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (EIf v e2 e3, st1, ctx) -->* (r1, st1', ctx') /\
    (EIf v' e2' e3', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Σ v v' e2 e2' e3 e3' st1 st2 ctx Hval Hstore.
  (* Step 1: Extract SAME boolean from val_rel_n_base *)
  destruct (val_rel_n_base_bool Σ v v' Hval) as [b [Heq1 Heq2]].
  subst v v'.
  (* Step 2: Case on b - both take SAME branch *)
  destruct b.
  - (* b = true: both step to then-branch *)
    exists e2, e2', st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := (e2, st1, ctx)).
      * apply ST_IfTrue.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := (e2', st2, ctx)).
      * apply ST_IfTrue.
      * apply MS_Refl.
  - (* b = false: both step to else-branch *)
    exists e3, e3', st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := (e3, st1, ctx)).
      * apply ST_IfFalse.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := (e3', st2, ctx)).
      * apply ST_IfFalse.
      * apply MS_Refl.
Qed.
```

**VERIFY THE FOLLOWING EXTRACTION LEMMA EXISTS:**
```coq
Lemma val_rel_n_base_bool : forall Σ v1 v2,
  val_rel_n_base Σ TBool v1 v2 ->
  exists b, v1 = EBool b /\ v2 = EBool b.
```

**OUTPUT:** The complete theorem with proof ending in `Qed.`

---

## TASK 8: exp_rel_step1_case — AXIOM ELIMINATION (HIGH PRIORITY)

**SPECIFIC TASK:**

Using the `val_rel_n_base` structure for sum types, prove that CASE expressions with related sums step to MATCHING branches:

```coq
(** exp_rel_step1_case: Related sums take MATCHING constructor branch

    KEY INSIGHT: val_rel_at_type_fo for TSum gives MATCHING constructors:
    - Both EInl: step to first branch
    - Both EInr: step to second branch
*)
Theorem exp_rel_step1_case_fo : forall Σ T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Σ (TSum T1 T2) v v' ->
  store_rel_n_base Σ st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx').
```

**PROOF STRATEGY:**
1. Use `val_rel_n_base_sum_fo` to extract matching constructors
2. Case on whether both are EInl or both are EInr
3. For EInl: both step to `[x1 := a] e1` and `[x1 := a'] e1'`
4. For EInr: both step to `[x2 := b] e2` and `[x2 := b'] e2'`

**REQUIRED EXTRACTION LEMMA:**
```coq
Lemma val_rel_n_base_sum_fo : forall Σ T1 T2 v1 v2,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Σ (TSum T1 T2) v1 v2 ->
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_at_type_fo T1 a1 a2) \/
  (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_at_type_fo T2 b1 b2).
```

**OUTPUT:** Complete theorem with proof ending in `Qed.`

---

## TASK 9: exp_rel_step1_let and exp_rel_step1_handle — AXIOM ELIMINATION

**SPECIFIC TASK:**

Prove the simpler stepping lemmas that only require value properties:

```coq
(** exp_rel_step1_let: Let with values steps to substituted body *)
Theorem exp_rel_step1_let : forall Σ T v v' x e2 e2' st1 st2 ctx,
  val_rel_n_base Σ T v v' ->
  store_rel_n_base Σ st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ELet x v e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ELet x v' e2', st2, ctx) -->* (r2, st2', ctx').

(** exp_rel_step1_handle: Handle with values steps to substituted handler *)
Theorem exp_rel_step1_handle : forall Σ T v v' x h h' st1 st2 ctx,
  val_rel_n_base Σ T v v' ->
  store_rel_n_base Σ st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (EHandle v x h, st1, ctx) -->* (r1, st1', ctx') /\
    (EHandle v' x h', st2, ctx) -->* (r2, st2', ctx').
```

**PROOF STRATEGY:**
1. Extract `value v1` and `value v2` from `val_rel_n_base`
2. Apply `ST_LetValue` / `ST_HandleValue` using value premises
3. Result is one-step reduction to substituted body

**EXTRACTION LEMMA NEEDED:**
```coq
Lemma val_rel_n_base_value : forall Σ T v1 v2,
  val_rel_n_base Σ T v1 v2 ->
  value v1 /\ value v2.
```

**OUTPUT:** Both theorems with proofs ending in `Qed.`

---

## TASK 10: exp_rel_step1_fst and exp_rel_step1_snd — AXIOM ELIMINATION

**SPECIFIC TASK:**

Prove projection stepping for first-order product types:

```coq
(** exp_rel_step1_fst: Projection of related pairs gives related components *)
Theorem exp_rel_step1_fst_fo : forall Σ T1 T2 v v' st1 st2 ctx,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Σ (TProd T1 T2) v v' ->
  store_rel_n_base Σ st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (EFst v, st1, ctx) -->* (r1, st1', ctx') /\
    (EFst v', st2, ctx) -->* (r2, st2', ctx').

(** exp_rel_step1_snd: Similar for second projection *)
Theorem exp_rel_step1_snd_fo : forall Σ T1 T2 v v' st1 st2 ctx,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Σ (TProd T1 T2) v v' ->
  store_rel_n_base Σ st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ESnd v, st1, ctx) -->* (r1, st1', ctx') /\
    (ESnd v', st2, ctx) -->* (r2, st2', ctx').
```

**PROOF STRATEGY:**
1. Use `val_rel_n_base_prod_fo` to extract pair structure:
   `v = EPair a1 b1`, `v' = EPair a2 b2`
2. Use value extraction to get `value a1, value b1, value a2, value b2`
3. Apply `ST_Fst` / `ST_Snd` step rules
4. Results are `a1, a2` for fst and `b1, b2` for snd

**EXTRACTION LEMMA NEEDED:**
```coq
Lemma val_rel_n_base_prod_fo : forall Σ T1 T2 v1 v2,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Σ (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2.
```

**OUTPUT:** Both theorems with proofs ending in `Qed.`

---

## TASK 11: val_rel_le_extract_struct_0 — INFRASTRUCTURE

**SPECIFIC TASK:**

Prove the helper lemma that extracts step-0 structural relation from cumulative:

```coq
(** KEY INSIGHT: The cumulative definition means val_rel_le n for n >= 1
    always contains val_rel_struct (val_rel_le 0) through the chain:
    val_rel_le n -> val_rel_le (n-1) -> ... -> val_rel_le 1
    And val_rel_le 1 = val_rel_le 0 /\ val_rel_struct (val_rel_le 0).
*)
Lemma val_rel_le_extract_struct_0 : forall n Σ T v1 v2,
  n >= 1 ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_struct (val_rel_le 0) Σ T v1 v2.
Proof.
  induction n as [|n' IH]; intros Σ T v1 v2 Hge Hrel.
  - lia. (* n >= 1 but n = 0, contradiction *)
  - simpl in Hrel. destruct Hrel as [Hprev Hstruct].
    destruct n' as [|n''].
    + (* n' = 0, so n = 1, Hstruct is exactly val_rel_struct (val_rel_le 0) *)
      exact Hstruct.
    + (* n' = S n'' > 0, use IH on Hprev *)
      apply IH; [lia | exact Hprev].
Qed.
```

**PURPOSE:** This lemma is critical for proving TFn step monotonicity in the m' = 0 case.

**OUTPUT:** Complete lemma with proof ending in `Qed.`

---

## USAGE INSTRUCTIONS

1. Copy the entire CLAUDE_AI_DELEGATION_PROMPT.md
2. Replace the `[INSERT YOUR SPECIFIC TASK HERE]` in Section 5 with one of the tasks above
3. Send to Claude AI (web)
4. Verify the output compiles locally before integrating

**IMPORTANT:** Always verify outputs locally. Claude AI (web) cannot test compilation.

---

## RECOMMENDED TASK ORDER FOR AXIOM ZERO

**Phase 1: Extraction Lemmas (Tasks 7, 9, 10)**
These are simpler and build foundation for later proofs.

**Phase 2: Step-1 Axiom Elimination (Tasks 7, 8, 9, 10)**
- TASK 7: exp_rel_step1_if — THE BIG WIN
- TASK 8: exp_rel_step1_case — CRITICAL FOR SUM TYPES
- TASK 9: exp_rel_step1_let, exp_rel_step1_handle — STRAIGHTFORWARD
- TASK 10: exp_rel_step1_fst, exp_rel_step1_snd — PROJECTIONS

**Phase 3: Infrastructure (Task 11)**
- val_rel_le_extract_struct_0 — ENABLES TFN MONOTONICITY

**Expected Impact:** 6-7 axioms eliminated, reducing from 42 to ~35 admits.
