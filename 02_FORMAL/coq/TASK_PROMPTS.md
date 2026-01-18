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

## USAGE INSTRUCTIONS

1. Copy the entire CLAUDE_AI_DELEGATION_PROMPT.md
2. Replace the `[INSERT YOUR SPECIFIC TASK HERE]` in Section 4 with one of the tasks above
3. Send to Claude AI (web)
4. Verify the output compiles locally before integrating

**IMPORTANT:** Always verify outputs locally. Claude AI (web) cannot test compilation.
