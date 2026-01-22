# CLAUDE AI DELEGATION TASK: Fix NonInterference_v2.v Compilation

## MISSION CRITICAL - ZERO TOLERANCE FOR FAILURE

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  TASK: Fix ALL compilation errors in NonInterference_v2.v                        ║
║  MODE: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE ITERATIONS         ║
║  SUCCESS CRITERIA: coqc compiles with ZERO errors                                ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## PROBLEM STATEMENT

File: `/workspaces/proof/02_FORMAL/coq/properties/NonInterference_v2.v`

**Current Error:**
```
File "./properties/NonInterference_v2.v", line 435, characters 4-10:
Error: Not an inductive goal with 1 constructor.
```

**Root Cause:** The `split` tactic is being applied to a goal that is NOT a conjunction (`A /\ B`). This happens because `unfold val_rel_n` and `simpl val_rel_n` do NOT properly expand mutual fixpoints in Coq.

---

## TECHNICAL CONTEXT

### The Mutual Fixpoint Definition (lines 181-206)

```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 =>
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T
       then val_rel_at_type_fo T v1 v2
       else True)
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end
with store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => store_max st1 = store_max st2
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' Σ T v1 v2)
  end.
```

### The Problem

When the goal is `val_rel_n 0 Σ' T1 a1 a2`, we need to prove:
```coq
value a1 /\ value a2 /\ closed_expr a1 /\ closed_expr a2 /\
(if first_order_type T1 then val_rel_at_type_fo T1 a1 a2 else True)
```

But `unfold val_rel_n` does NOT work on mutual fixpoints. It leaves the goal as `val_rel_n 0 Σ' T1 a1 a2` which is NOT a conjunction, so `split` fails.

---

## SOLUTION APPROACHES

### Approach 1: Use `simpl` (preferred)
```coq
simpl.  (* This SHOULD expand val_rel_n 0 to its definition *)
```

### Approach 2: Use `destruct` on the nat argument
```coq
(* If we have val_rel_n n ... as a hypothesis or goal where n is concrete *)
destruct n.  (* Forces case split *)
```

### Approach 3: Define an unfolding lemma
```coq
Lemma val_rel_n_0_unfold : forall Σ T v1 v2,
  val_rel_n 0 Σ T v1 v2 =
  (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)).
Proof. reflexivity. Qed.
```
Then use `rewrite val_rel_n_0_unfold`.

### Approach 4: Use `change` tactic
```coq
change (val_rel_n 0 Σ' T1 a1 a2) with
  (value a1 /\ value a2 /\ closed_expr a1 /\ closed_expr a2 /\
   (if first_order_type T1 then val_rel_at_type_fo T1 a1 a2 else True)).
```

---

## EXECUTION INSTRUCTIONS

### Step 1: Read the file
```bash
cat /workspaces/proof/02_FORMAL/coq/properties/NonInterference_v2.v
```

### Step 2: Identify ALL locations with the error pattern
Search for:
- `unfold val_rel_n` followed by `split`
- `simpl val_rel_n` followed by `split`
- Any place trying to destruct `val_rel_n 0` or `val_rel_n (S n)`

### Step 3: Fix each location
For each problematic proof:
1. Try `simpl.` first (simplest)
2. If that doesn't work, add an unfolding lemma
3. Use `change` as a last resort

### Step 4: Compile and verify
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -R . RIINA properties/NonInterference_v2.v
```

### Step 5: If errors remain, ITERATE
- Read the new error message
- Identify the line number
- Fix that specific issue
- Recompile
- Repeat until ZERO errors

---

## VERIFICATION CHECKLIST

After fixing, verify:
1. [ ] `coqc -R . RIINA properties/NonInterference_v2.v` completes with NO errors
2. [ ] Count admits: `grep -c "Admitted\." properties/NonInterference_v2.v` (should be exactly 3)
3. [ ] Count axioms: `grep -c "^Axiom " properties/NonInterference_v2.v` (should be exactly 0)
4. [ ] The file structure is preserved (same lemma names, same logical structure)

---

## EXPECTED ERRORS AND FIXES

### Error: "Not an inductive goal with 1 constructor"
**Cause:** `split` on non-conjunction
**Fix:** Use `simpl.` before `split`, or add unfolding lemma

### Error: "Found no subterm matching X"
**Cause:** `rewrite` can't find the term
**Fix:** The goal might not be unfolded yet. Use `simpl.` first.

### Error: "Wrong bullet"
**Cause:** Tactic generated different number of goals than expected
**Fix:** Adjust bullet structure or use `{ }` brackets

### Error: "Unable to unify"
**Cause:** Types don't match after simplification
**Fix:** Check if `first_order_type` conditions are correct

---

## CRITICAL CONSTRAINTS

1. **DO NOT change the logical structure** - only fix proof tactics
2. **DO NOT remove any lemmas** - they are needed
3. **DO NOT change lemma signatures** - they must remain compatible
4. **DO NOT introduce new axioms** - we are eliminating them, not adding
5. **PRESERVE all admits** - they are documented and intentional (for now)

---

## SUCCESS DEFINITION

The task is COMPLETE when:
```bash
$ coqc -R . RIINA properties/NonInterference_v2.v
$ echo $?
0
```

No output, exit code 0.

---

## ITERATION PROTOCOL

If you cannot fix all errors in one pass:

1. Fix as many as you can
2. Document what you fixed
3. Document remaining errors with exact line numbers
4. Explain what you tried and why it didn't work
5. Request another iteration with specific questions

**There is NO limit on iterations. Keep iterating until 100% success.**

---

## FINAL REMINDER

```
Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

- Do NOT assume anything works without testing
- Do NOT skip verification steps
- Do NOT declare success until coqc returns 0
- EVERY change must be compiled and verified
- ITERATE as many times as needed
```

This file MUST compile. Failure is not an option.
