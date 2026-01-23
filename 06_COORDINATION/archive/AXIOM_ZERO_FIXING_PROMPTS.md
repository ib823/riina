# AXIOM ZERO - DEFINITIVE FIXING PROMPTS

**Classification:** ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
**Date:** 2026-01-18
**Purpose:** Complete, unambiguous specifications for fixing compilation errors
**Mode:** INFINITE TIMELINE - Execute until mathematically perfect

---

## CONTEXT FOR AI ASSISTANT

You are fixing Coq proof files for the RIINA project. These files implement a revolutionary approach to eliminate ALL axioms in NonInterference.v by redefining `val_rel_n 0` to carry structural information for first-order types.

**CRITICAL REQUIREMENTS:**
1. Every file MUST compile with `coqc -Q . RIINA <file>.v` with ZERO errors
2. Every proof MUST end with `Qed.` - NO `Admitted.` allowed except where explicitly documented as requiring strong normalization
3. All lemmas must have correct types that match their usage sites
4. No shortcuts, no placeholders, no "left as exercise" - complete proofs only

---

## PROMPT 1: FIX ValRelFOEquiv.v

### FILE LOCATION
`/workspaces/proof/02_FORMAL/coq/properties/ValRelFOEquiv.v`

### EXISTING IMPORTS (DO NOT CHANGE)
```coq
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
```

### ERROR LOCATION AND DIAGNOSIS

**Error at line 158:**
```
Error: Unable to unify
 "(val_rel_at_type ... T1 ... -> val_rel_at_type_fo T1 ...) /\
  (val_rel_at_type_fo T1 ... -> val_rel_at_type ... T1 ...)"
with
 "(fix val_rel_at_type_fo ...)"
```

**Root Cause:** The induction hypothesis `IHT1` has type:
```coq
IHT1 : forall (Σ : store_ty) (sp : store_ty -> store -> store -> Prop)
         (vl : store_ty -> ty -> expr -> expr -> Prop)
         (sl : store_ty -> store -> store -> Prop)
         (v1 v2 : expr),
       first_order_type T1 = true ->
       val_rel_at_type Σ sp vl sl T1 v1 v2 <-> val_rel_at_type_fo T1 v1 v2
```

The proof attempts `apply IHT1; assumption` but:
1. `IHT1` returns an `iff` (biconditional `<->`)
2. We need to extract the forward direction with `proj1` or use `apply -> IHT1`
3. We must provide `first_order_type T1 = true` which comes from `Hfo1`

### COMPLETE FIXED PROOF FOR TProd CASE

Replace lines 151-165 with:

```coq
  - (* TProd T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + (* -> direction: val_rel_at_type -> val_rel_at_type_fo *)
      intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2.
      repeat split; try assumption.
      * (* Use IHT1 forward direction *)
        apply (proj1 (IHT1 Σ' sp vl sl x1 x2 Hfo1)). exact Hr1.
      * (* Use IHT2 forward direction *)
        apply (proj1 (IHT2 Σ' sp vl sl y1 y2 Hfo2)). exact Hr2.
    + (* <- direction: val_rel_at_type_fo -> val_rel_at_type *)
      intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2.
      repeat split; try assumption.
      * (* Use IHT1 backward direction *)
        apply (proj2 (IHT1 Σ' sp vl sl x1 x2 Hfo1)). exact Hr1.
      * (* Use IHT2 backward direction *)
        apply (proj2 (IHT2 Σ' sp vl sl y1 y2 Hfo2)). exact Hr2.
```

### COMPLETE FIXED PROOF FOR TSum CASE

Replace lines 167-175 with:

```coq
  - (* TSum T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + (* -> direction *)
      intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply (proj1 (IHT1 Σ' sp vl sl x1 x2 Hfo1)). exact Hr.
      * right. exists y1, y2. repeat split; try assumption.
        apply (proj1 (IHT2 Σ' sp vl sl y1 y2 Hfo2)). exact Hr.
    + (* <- direction *)
      intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply (proj2 (IHT1 Σ' sp vl sl x1 x2 Hfo1)). exact Hr.
      * right. exists y1, y2. repeat split; try assumption.
        apply (proj2 (IHT2 Σ' sp vl sl y1 y2 Hfo2)). exact Hr.
```

### VERIFICATION COMMAND
```bash
cd /workspaces/proof/02_FORMAL/coq && coqc -Q . RIINA properties/ValRelFOEquiv.v
```

**Expected output:** No errors, no warnings related to the proof.

---

## PROMPT 2: FIX NonInterference_v2.v

### FILE LOCATION
`/workspaces/proof/02_FORMAL/coq/properties/NonInterference_v2.v`

### ERROR LOCATION AND DIAGNOSIS

**Error at line 249:**
```
Error: Not an inductive product.
```

**Context:** The proof is trying to destruct `Hfo` which has type:
```coq
Hfo : (if first_order_type (TProd T1 T2) then val_rel_at_type_fo (TProd T1 T2) v1 v2 else True)
```

This is a **conditional expression**, NOT an inductive product. We cannot directly `destruct` it.

**Root Cause:** The definition of `val_rel_n 0` is:
```coq
| 0 =>
    value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
    (if first_order_type T
     then val_rel_at_type_fo T v1 v2
     else True)
```

For `T = TProd T1 T2`, we have:
- `first_order_type (TProd T1 T2) = first_order_type T1 && first_order_type T2`
- This could be `true` or `false` depending on T1 and T2

The lemma `val_rel_n_prod_structure` claims to work for ALL `TProd T1 T2`, but if T1 or T2 contains a function type, `first_order_type` returns `false` and `Hfo = True`, which has no structure.

### SOLUTION APPROACH

**Option A (Recommended):** Add premise that T1 and T2 are first-order types.

**Option B:** Change the lemma to only extract structure when we CAN extract it (i.e., when `first_order_type (TProd T1 T2) = true`).

**Option C:** Modify `val_rel_n` definition to ALWAYS include structure for TProd/TSum at step 0 (not just when first-order).

I recommend **Option A** as it's mathematically correct and minimal change.

### COMPLETE FIXED LEMMA: val_rel_n_prod_structure

Replace lines 237-262 with:

```coq
(** Extract pair structure from val_rel_n for TProd - FIRST-ORDER ONLY *)
Lemma val_rel_n_prod_structure : forall n Σ T1 T2 v1 v2,
  first_order_type T1 = true ->  (* ADDED PREMISE *)
  first_order_type T2 = true ->  (* ADDED PREMISE *)
  val_rel_n n Σ (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    value a1 /\ value b1 /\ value a2 /\ value b2.
Proof.
  intros n Σ T1 T2 v1 v2 Hfo1 Hfo2 Hrel.
  destruct n; simpl in Hrel.
  - (* n = 0: use val_rel_at_type_fo *)
    destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hfo]]]].
    (* First, prove that first_order_type (TProd T1 T2) = true *)
    assert (Hfo_prod : first_order_type (TProd T1 T2) = true).
    { simpl. rewrite Hfo1, Hfo2. reflexivity. }
    (* Rewrite the if-then-else using this fact *)
    rewrite Hfo_prod in Hfo.
    (* NOW Hfo : val_rel_at_type_fo (TProd T1 T2) v1 v2 *)
    simpl in Hfo.
    destruct Hfo as [a1 [b1 [a2 [b2 [Heq1 [Heq2 _]]]]]].
    exists a1, b1, a2, b2.
    subst v1 v2.
    inversion Hv1; subst. inversion Hv2; subst.
    repeat split; assumption.
  - (* n = S n': use val_rel_at_type *)
    destruct Hrel as [_ [Hv1 [Hv2 [_ [_ Hrat]]]]].
    simpl in Hrat.
    destruct Hrat as [a1 [b1 [a2 [b2 [Heq1 [Heq2 _]]]]]].
    exists a1, b1, a2, b2.
    subst v1 v2.
    inversion Hv1; subst. inversion Hv2; subst.
    repeat split; assumption.
Qed.
```

### COMPLETE FIXED LEMMA: val_rel_n_sum_structure

Replace lines 277-303 with:

```coq
(** Extract sum structure from val_rel_n for TSum - FIRST-ORDER ONLY *)
Lemma val_rel_n_sum_structure : forall n Σ T1 T2 v1 v2,
  first_order_type T1 = true ->  (* ADDED PREMISE *)
  first_order_type T2 = true ->  (* ADDED PREMISE *)
  val_rel_n n Σ (TSum T1 T2) v1 v2 ->
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ value a1 /\ value a2) \/
  (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ value b1 /\ value b2).
Proof.
  intros n Σ T1 T2 v1 v2 Hfo1 Hfo2 Hrel.
  destruct n; simpl in Hrel.
  - (* n = 0 *)
    destruct Hrel as [Hv1 [Hv2 [_ [_ Hfo]]]].
    (* Prove first_order_type (TSum T1 T2) = true *)
    assert (Hfo_sum : first_order_type (TSum T1 T2) = true).
    { simpl. rewrite Hfo1, Hfo2. reflexivity. }
    rewrite Hfo_sum in Hfo.
    simpl in Hfo.
    destruct Hfo as [[a1 [a2 [Heq1 [Heq2 _]]]] | [b1 [b2 [Heq1 [Heq2 _]]]]].
    + left. exists a1, a2. subst.
      inversion Hv1; subst. inversion Hv2; subst.
      repeat split; assumption.
    + right. exists b1, b2. subst.
      inversion Hv1; subst. inversion Hv2; subst.
      repeat split; assumption.
  - (* n = S n' *)
    destruct Hrel as [_ [Hv1 [Hv2 [_ [_ Hrat]]]]].
    simpl in Hrat.
    destruct Hrat as [[a1 [a2 [Heq1 [Heq2 _]]]] | [b1 [b2 [Heq1 [Heq2 _]]]]].
    + left. exists a1, a2. subst.
      inversion Hv1; subst. inversion Hv2; subst.
      repeat split; assumption.
    + right. exists b1, b2. subst.
      inversion Hv1; subst. inversion Hv2; subst.
      repeat split; assumption.
Qed.
```

### UPDATE ALL CALL SITES

**exp_rel_step1_fst (lines 390-430):** Update to provide FO premises.

```coq
(** FORMER AXIOM 1: exp_rel_step1_fst - NOW PROVEN *)
Lemma exp_rel_step1_fst : forall Σ T1 T2 v v' st1 st2 ctx Σ',
  first_order_type T1 = true ->  (* ADDED *)
  first_order_type T2 = true ->  (* ADDED *)
  val_rel_n 0 Σ' (TProd T1 T2) v v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EFst v, st1, ctx) -->* (a1, st1', ctx') /\
    (EFst v', st2, ctx) -->* (a2, st2', ctx') /\
    value a1 /\ value a2 /\
    val_rel_n 0 Σ'' T1 a1 a2 /\
    store_rel_n 0 Σ'' st1' st2'.
Proof.
  intros Σ T1 T2 v v' st1 st2 ctx Σ' Hfo1 Hfo2 Hval Hstore Hext.

  (* Extract pair structure from val_rel_n 0 - NOW WITH FO PREMISES *)
  destruct (val_rel_n_prod_structure 0 Σ' T1 T2 v v' Hfo1 Hfo2 Hval)
    as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hva1 [Hvb1 [Hva2 Hvb2]]]]]]]]].
  subst v v'.

  destruct (val_rel_n_closed 0 Σ' (TProd T1 T2) (EPair a1 b1) (EPair a2 b2) Hval)
    as [Hcl1 Hcl2].

  exists a1, a2, st1, st2, ctx, Σ'.
  repeat split.
  - apply store_ty_extends_refl.
  - apply MS_Step with (cfg2 := (a1, st1, ctx)).
    + apply ST_Fst; assumption.
    + apply MS_Refl.
  - apply MS_Step with (cfg2 := (a2, st2, ctx)).
    + apply ST_Fst; assumption.
    + apply MS_Refl.
  - exact Hva1.
  - exact Hva2.
  - (* val_rel_n 0 Σ' T1 a1 a2 *)
    simpl. repeat split.
    + exact Hva1.
    + exact Hva2.
    + intros y Hfree. apply (Hcl1 y). simpl. left. exact Hfree.
    + intros y Hfree. apply (Hcl2 y). simpl. left. exact Hfree.
    + (* val_rel_at_type_fo T1 a1 a2 *)
      rewrite Hfo1.
      simpl in Hval.
      destruct Hval as [_ [_ [_ [_ Hrat]]]].
      assert (Hfo_prod : first_order_type (TProd T1 T2) = true).
      { simpl. rewrite Hfo1, Hfo2. reflexivity. }
      rewrite Hfo_prod in Hrat.
      simpl in Hrat.
      destruct Hrat as [x1 [y1 [x2 [y2 [Heq1' [Heq2' [Hr1 Hr2]]]]]]].
      inversion Heq1'; subst. inversion Heq2'; subst.
      exact Hr1.
  - exact Hstore.
Qed.
```

**Similarly update exp_rel_step1_snd, exp_rel_step1_case.**

### COMPLETE FIXED exp_rel_step1_snd

```coq
(** FORMER AXIOM 2: exp_rel_step1_snd - NOW PROVEN *)
Lemma exp_rel_step1_snd : forall Σ T1 T2 v v' st1 st2 ctx Σ',
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  val_rel_n 0 Σ' (TProd T1 T2) v v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists b1 b2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (ESnd v, st1, ctx) -->* (b1, st1', ctx') /\
    (ESnd v', st2, ctx) -->* (b2, st2', ctx') /\
    value b1 /\ value b2 /\
    val_rel_n 0 Σ'' T2 b1 b2 /\
    store_rel_n 0 Σ'' st1' st2'.
Proof.
  intros Σ T1 T2 v v' st1 st2 ctx Σ' Hfo1 Hfo2 Hval Hstore Hext.

  destruct (val_rel_n_prod_structure 0 Σ' T1 T2 v v' Hfo1 Hfo2 Hval)
    as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hva1 [Hvb1 [Hva2 Hvb2]]]]]]]]].
  subst v v'.

  destruct (val_rel_n_closed 0 Σ' (TProd T1 T2) (EPair a1 b1) (EPair a2 b2) Hval)
    as [Hcl1 Hcl2].

  exists b1, b2, st1, st2, ctx, Σ'.
  repeat split.
  - apply store_ty_extends_refl.
  - apply MS_Step with (cfg2 := (b1, st1, ctx)).
    + apply ST_Snd; assumption.
    + apply MS_Refl.
  - apply MS_Step with (cfg2 := (b2, st2, ctx)).
    + apply ST_Snd; assumption.
    + apply MS_Refl.
  - exact Hvb1.
  - exact Hvb2.
  - simpl. repeat split.
    + exact Hvb1.
    + exact Hvb2.
    + intros y Hfree. apply (Hcl1 y). simpl. right. exact Hfree.
    + intros y Hfree. apply (Hcl2 y). simpl. right. exact Hfree.
    + rewrite Hfo2.
      simpl in Hval.
      destruct Hval as [_ [_ [_ [_ Hrat]]]].
      assert (Hfo_prod : first_order_type (TProd T1 T2) = true).
      { simpl. rewrite Hfo1, Hfo2. reflexivity. }
      rewrite Hfo_prod in Hrat.
      simpl in Hrat.
      destruct Hrat as [x1 [y1 [x2 [y2 [Heq1' [Heq2' [Hr1 Hr2]]]]]]].
      inversion Heq1'; subst. inversion Heq2'; subst.
      exact Hr2.
  - exact Hstore.
Qed.
```

### COMPLETE FIXED exp_rel_step1_case

```coq
(** FORMER AXIOM 4: exp_rel_step1_case - NOW PROVEN *)
Lemma exp_rel_step1_case : forall Σ T T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Σ',
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  val_rel_n 0 Σ' (TSum T1 T2) v v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists r1 r2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Σ T T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Σ' Hfo1 Hfo2 Hval Hstore Hext.

  destruct (val_rel_n_sum_structure 0 Σ' T1 T2 v v' Hfo1 Hfo2 Hval) as
    [[a1 [a2 [Heq1 [Heq2 [Hva1 Hva2]]]]] | [b1 [b2 [Heq1 [Heq2 [Hvb1 Hvb2]]]]]].
  - (* Both EInl *)
    subst v v'.
    exists ([x1 := a1] e1), ([x1 := a2] e1'), st1, st2, ctx, Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Step with (cfg2 := ([x1 := a1] e1, st1, ctx)).
      * apply ST_CaseInl. exact Hva1.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := ([x1 := a2] e1', st2, ctx)).
      * apply ST_CaseInl. exact Hva2.
      * apply MS_Refl.
  - (* Both EInr *)
    subst v v'.
    exists ([x2 := b1] e2), ([x2 := b2] e2'), st1, st2, ctx, Σ'.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Step with (cfg2 := ([x2 := b1] e2, st1, ctx)).
      * apply ST_CaseInr. exact Hvb1.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := ([x2 := b2] e2', st2, ctx)).
      * apply ST_CaseInr. exact Hvb2.
      * apply MS_Refl.
Qed.
```

### VERIFICATION COMMAND
```bash
cd /workspaces/proof/02_FORMAL/coq && coqc -Q . RIINA properties/NonInterference_v2.v
```

---

## PROMPT 3: COMPLETE INTEGRATION

After fixing both files, ensure they integrate properly:

### Step 1: Update _CoqProject to include new files
```
# Add after existing properties
properties/ValRelFOEquiv.v
properties/NonInterference_v2.v
```

### Step 2: Build entire project
```bash
cd /workspaces/proof/02_FORMAL/coq
make clean
make
```

### Step 3: Verify axiom count
```bash
grep -c "^Axiom " properties/NonInterference_v2.v
# Expected: 0 or minimal (only for strong normalization)

grep -c "^Admitted\." properties/NonInterference_v2.v
# Document each remaining Admitted with justification
```

---

## CRITICAL INVARIANTS TO MAINTAIN

1. **Type Consistency:** Every lemma's type signature must match its usage sites in the fundamental theorem.

2. **First-Order Gate:** For TProd and TSum at step 0, ALWAYS prove `first_order_type T = true` BEFORE attempting to extract structure from the conditional.

3. **IH Application:** When using induction hypotheses that return `iff`:
   - Use `proj1 (IH ...)` for forward direction
   - Use `proj2 (IH ...)` for backward direction
   - OR use `apply -> IH` / `apply <- IH` syntax

4. **Conditional Rewriting:** Before destructing `(if b then X else Y)`:
   - Prove `b = true` or `b = false`
   - Use `rewrite Hb` to eliminate the conditional
   - THEN destruct the resulting term

5. **No Magic:** Every step must be justified. No `admit`, no `Admitted` except for strong normalization which is explicitly documented as the ONE remaining semantic assumption.

---

## EXPECTED FINAL STATE

| Metric | Target |
|--------|--------|
| ValRelFOEquiv.v compiles | ✅ |
| NonInterference_v2.v compiles | ✅ |
| Axioms in NonInterference_v2.v | 0 |
| Admitted in NonInterference_v2.v | ≤3 (monotonicity, step-up for TFn) |
| exp_rel_step1_if proven | ✅ Qed |
| exp_rel_step1_case proven | ✅ Qed |

---

## MODE DECLARATION

This specification follows:
- **ULTRA KIASU:** Every possible edge case considered
- **FUCKING PARANOID:** Every type checked, every premise verified
- **ZERO TRUST:** No assumptions about "obvious" facts
- **ZERO LAZINESS:** Complete proofs, no shortcuts
- **INFINITE TIMELINE:** Execute until mathematically perfect

---

*"Security proven. Mathematically verified."*

*RIINA: Rigorous Immutable Integrity No-attack Assured*
