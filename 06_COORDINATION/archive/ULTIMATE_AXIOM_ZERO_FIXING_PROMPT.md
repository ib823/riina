# ULTIMATE AXIOM ZERO FIXING PROMPT

**Mode:** ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO SHORTCUTS | INFINITE TIMELINE
**Date:** 2026-01-18
**Purpose:** Generate COMPILATION-PERFECT Coq files for RIINA AXIOM ZERO

---

## CRITICAL REQUIREMENTS

1. **EVERY FILE MUST COMPILE WITH `Qed.`** - No `Admitted.` allowed except where explicitly documented as semantic assumptions
2. **EVERY BULLET MUST MATCH** - Coq bullet structure must be verified for every proof
3. **EVERY REFERENCE MUST EXIST** - All used lemmas/definitions must be imported or defined first
4. **EVERY TACTIC MUST WORK** - Test each tactic step in your mind before writing

---

## COMPILATION ERRORS IDENTIFIED

### File 1: StrongNormalization_v2.v
**Error:** Line 99 - "Wrong bullet -: Current bullet - is not finished"

**Root Cause:** The `value_no_step` lemma proof structure:
```coq
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  inversion Hstep; subst;
  try (inversion Hval; fail).
  - (* ST_AppAbs: v = ELam x T body, but need v to be the redex *)
    inversion Hval.
  - (* ST_App1: v steps, contradiction with value *)
    inversion Hval.
  ...
Qed.
```

**Problem:**
- `inversion Hstep` generates N subgoals (one per step constructor)
- `try (inversion Hval; fail)` attempts to solve each, but behavior varies
- The `-` bullets don't match the actual remaining goals

**FIX:**
```coq
Lemma value_no_step : forall v st ctx e' st' ctx',
  value v ->
  ~ (v, st, ctx) --> (e', st', ctx').
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  induction Hval; inversion Hstep; subst;
  try discriminate;
  try (match goal with
       | [H : value ?e |- _] => inversion H; fail
       end).
Qed.
```

Or simpler (if it works):
```coq
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  induction Hval; inversion Hstep.
Qed.
```

**VERIFY:** Count the number of cases from `inversion Hstep` for your step relation. Match exactly.

---

### File 2: SN_Closure.v
**Error:** Line 49 - "Unexpected introduction pattern: H"

**Root Cause:**
```coq
inversion Hsn as [_ H].
```

**Problem:** The `as` pattern syntax for `inversion` on `Acc` doesn't work this way in Coq.

**FIX:**
```coq
Lemma SN_step : forall e st ctx e' st' ctx',
  SN (e, st, ctx) ->
  (e, st, ctx) --> (e', st', ctx') ->
  SN (e', st', ctx').
Proof.
  intros e st ctx e' st' ctx' Hsn Hstep.
  inversion Hsn.
  apply H.
  unfold step_inv.
  exact Hstep.
Qed.
```

**NOTE:** Just use `inversion Hsn.` without the `as` pattern. Coq will name the hypothesis automatically (usually `H`).

---

### File 3: StepUpFromSN.v
**Error:** Line 35 - "The reference step_inv was not found"

**Root Cause:**
```coq
Parameter strong_normalization : forall e T Σ ε,
  has_type nil Σ Public e T ε ->
  forall st ctx, Acc step_inv (e, st, ctx).
```

**Problems:**
1. `step_inv` is not defined in this file or imported
2. Using `Parameter` is essentially an axiom

**FIX:** Either:
1. Import the file that defines `step_inv`:
   ```coq
   Require Import RIINA.properties.StrongNormalization_v2.
   ```
2. Or define `step_inv` locally:
   ```coq
   Definition step_inv (cfg1 cfg2 : config) : Prop :=
     let '(e2, st2, ctx2) := cfg2 in
     let '(e1, st1, ctx1) := cfg1 in
     (e2, st2, ctx2) --> (e1, st1, ctx1).
   ```

---

### File 4: FundamentalTheorem.v
**Error:** Line 54 - "Attempt to save an incomplete proof"

**Root Cause:**
```coq
Lemma value_no_step : forall v st ctx e' st' ctx',
  value v ->
  ~ (v, st, ctx) --> (e', st', ctx').
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  induction Hval; inversion Hstep.
Qed.
```

**Problem:** `induction Hval; inversion Hstep` doesn't solve all goals. Some step constructors may leave subgoals.

**FIX:** Add explicit case handling:
```coq
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  induction Hval; inversion Hstep; subst; auto;
  try (inversion H0; fail);
  try (inversion H1; fail).
Qed.
```

Or use a more explicit approach:
```coq
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  destruct Hval; inversion Hstep; subst.
  (* For each remaining case, provide explicit proof *)
Qed.
```

---

### File 5: ValRelFOEquiv.v (from previous batch)
**Status:** ✅ COMPILES after fix

**Fix Applied:** Use `proj1` and `proj2` to extract directions from IH iff:
```coq
(* For TProd case *)
apply (proj1 (IHT1 Σ' sp vl sl x1 x2 Hfo1)). exact Hr1.
apply (proj2 (IHT1 Σ' sp vl sl x1 x2 Hfo1)). exact Hr1.
```

---

### File 6: NonInterference_v2.v (from previous batch)
**Error:** Line 435 - "Not an inductive goal with 1 constructor"

**Root Cause:** After `simpl`, `val_rel_n 0 Σ' T1 a1 a2` doesn't unfold to a conjunction.

**Problem:** `simpl` may not unfold mutual fixpoints defined with `with`.

**FIX:** Use explicit unfold:
```coq
unfold val_rel_n.
(* If it still doesn't unfold because of mutual fixpoint,
   need to restructure the definition *)
```

**ALTERNATIVE:** Use `destruct` instead of `simpl`:
```coq
destruct (val_rel_n 0 Σ' T1 a1 a2) as ...
```

**CRITICAL:** The definition of `val_rel_n` uses:
```coq
Fixpoint val_rel_n (n : nat) ...
with store_rel_n (n : nat) ...
```

Mutual fixpoints may not unfold with `simpl`. You may need to:
1. Separate the definitions
2. Use `Lemma val_rel_n_0_unfold` to explicitly prove the unfolding

---

## STRUCTURAL REQUIREMENTS FOR ALL FILES

### 1. Proof Bullet Rules
- `-` for top-level goals
- `+` for first level nested
- `*` for second level nested
- `{ }` braces can scope any nested proof

**Example:**
```coq
Proof.
  intros. split.
  - (* first conjunct *)
    destruct H as [A B].
    + (* case 1 *) exact A.
    + (* case 2 *) exact B.
  - (* second conjunct *)
    auto.
Qed.
```

### 2. Conditional Rewriting Pattern
When you have `Hfo : if cond then X else Y` and `Hcond : cond = true`:

**WRONG:**
```coq
assert (Hcond : cond = true). { simpl. ... }
rewrite Hcond in Hfo.  (* FAILS: can't find cond in Hfo *)
```

**RIGHT:**
```coq
(* Method 1: Simplify the condition first *)
simpl cond in Hfo.  (* Unfolds cond *)
rewrite Hcond_part1, Hcond_part2 in Hfo.  (* Substitute components *)
simpl in Hfo.  (* Reduces if true then X else Y to X *)

(* Method 2: Use destruct on the condition *)
destruct cond eqn:Heq.
+ (* true case: Hfo simplifies to X *)
  simpl in Hfo. ...
+ (* false case: derive contradiction *)
  discriminate.
```

### 3. Inversion on Acc
```coq
(* For Hsn : Acc R x *)
inversion Hsn.
(* Creates: H : forall y, R y x -> Acc R y *)
apply H.
```

### 4. Value-No-Step Lemma Pattern
This lemma is critical and appears in multiple files. The cleanest proof:

```coq
Lemma value_no_step : forall v st ctx e' st' ctx',
  value v ->
  ~ (v, st, ctx) --> (e', st', ctx').
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  (* Induction on value, inversion on step *)
  induction Hval.
  - (* V_Unit *) inversion Hstep.
  - (* V_Bool *) inversion Hstep.
  - (* V_Int *) inversion Hstep.
  - (* V_String *) inversion Hstep.
  - (* V_Lam *) inversion Hstep.
    (* If ST_AppAbs applies to lambda, v is the function not the app *)
  - (* V_Pair *) inversion Hstep; subst.
    + apply IHHval1. exact H3.
    + apply IHHval2. exact H4.
  - (* V_Inl *) inversion Hstep; subst. apply IHHval. exact H3.
  - (* V_Inr *) inversion Hstep; subst. apply IHHval. exact H3.
  - (* etc for other value constructors *)
Qed.
```

**KEY:** Match the number of bullets to your value constructors and handle each step case.

---

## DEPENDENCY ORDER

Compile in this order:
1. `foundations/Syntax.v`
2. `foundations/Semantics.v`
3. `foundations/Typing.v`
4. `type_system/Preservation.v`
5. `properties/ValRelFOEquiv.v`
6. `properties/StrongNormalization_v2.v`
7. `properties/SN_Closure.v`
8. `properties/StepUpFromSN.v`
9. `properties/FundamentalTheorem.v`
10. `properties/NonInterference_v2.v`

---

## AXIOM AUDIT CHECKLIST

For each file, verify:
- [ ] No `Admitted.` without explicit justification
- [ ] No `Parameter` or `Axiom` without explicit justification
- [ ] All `Qed.` complete successfully
- [ ] Bullet structure verified
- [ ] All imports exist and compile

---

## DELIVERABLES

Please regenerate ALL files with:

1. **100% compilation success** - `coqc -Q . RIINA <file>.v` must succeed
2. **Zero bullet errors** - Verify every proof's bullet structure
3. **Zero missing references** - All lemmas/defs must be imported or defined
4. **Explicit case handling** - No `try` that might fail silently
5. **Clear comments** - Document the proof strategy for complex proofs

---

## TESTING COMMAND

After generating each file, test with:
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA properties/<filename>.v
```

If error, analyze EXACT line number and character position, then fix.

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST*
*"Every Qed must succeed. Every proof must complete. Zero exceptions."*
