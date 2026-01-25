# RIINA AXIOM ELIMINATION - PHASE 0 DELEGATION PROMPT
## For Claude AI Web Execution

**CRITICAL: READ THIS ENTIRE PROMPT BEFORE TAKING ANY ACTION**

---

## MISSION STATEMENT

You are executing Phase 0 of the RIINA Axiom Elimination Strategy. Your task is to replace 7 axioms in `LogicalRelationAssign_PROOF.v` with imports from `MaximumAxiomElimination.v`, where these lemmas are already proven.

**Success Criteria:** Compile passes, 7 fewer axioms, zero new admits.

---

## CONTEXT

### Repository Structure
```
/workspaces/proof/02_FORMAL/coq/
├── properties/
│   ├── LogicalRelationAssign_PROOF.v  ← TARGET FILE
│   ├── MaximumAxiomElimination.v      ← SOURCE OF PROVEN LEMMAS
│   └── ... (other files)
├── _CoqProject                        ← Build configuration
└── Makefile                           ← Build system
```

### Current State of Target File
`LogicalRelationAssign_PROOF.v` contains 14 axioms. 7 of these are ALREADY PROVEN in `MaximumAxiomElimination.v`:

| Axiom in LogicalRelationAssign_PROOF.v | Proven Lemma in MaximumAxiomElimination.v |
|----------------------------------------|-------------------------------------------|
| `val_rel_n_unit` (line 346) | `val_rel_n_unit` |
| `val_rel_n_ref` (line 351) | `val_rel_n_ref` |
| `val_rel_n_ref_same_loc` (line 357) | `val_rel_n_ref_same_loc` |
| `val_rel_n_step_down` (line 390) | `val_rel_n_step_down` |
| `exp_rel_n_step_down` (line 395) | `exp_rel_n_step_down` |
| `store_rel_n_step_down` (line 400) | `store_rel_n_step_down` |
| `store_update_preserves_rel` (line 406) | `store_update_preserves_rel` |

---

## TASK SPECIFICATION

### STEP 1: Read Both Files

Read the following files completely before making any changes:

1. `/workspaces/proof/02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v`
2. `/workspaces/proof/02_FORMAL/coq/properties/MaximumAxiomElimination.v`

### STEP 2: Verify Lemma Signatures Match

For EACH of the 7 lemmas, verify the signature in MaximumAxiomElimination.v matches what's expected in LogicalRelationAssign_PROOF.v.

**CRITICAL:** The signatures may differ slightly in parameter names or ordering. Document any differences.

### STEP 3: Analyze Type Compatibility

LogicalRelationAssign_PROOF.v has its OWN type definitions (it's self-contained). MaximumAxiomElimination.v also has its own definitions. You CANNOT simply import between them if the types are different.

**Check:**
1. Does LogicalRelationAssign_PROOF.v define its own `ty`, `expr`, `store`, etc.?
2. Does MaximumAxiomElimination.v use the same definitions?
3. If they're different, direct import won't work.

### STEP 4: Decision Point

**IF types are compatible (same definitions):**
- Proceed to Step 5A (Direct Import)

**IF types are incompatible (different definitions):**
- Proceed to Step 5B (Bridge Module) OR
- Proceed to Step 5C (Inline Proofs)

### STEP 5A: Direct Import (If Compatible)

Add this import near the top of LogicalRelationAssign_PROOF.v:
```coq
Require Import RIINA.properties.MaximumAxiomElimination.
```

Then REMOVE these 7 axiom declarations:
```coq
(* DELETE: Axiom val_rel_n_unit *)
(* DELETE: Axiom val_rel_n_ref *)
(* DELETE: Axiom val_rel_n_ref_same_loc *)
(* DELETE: Axiom val_rel_n_step_down *)
(* DELETE: Axiom exp_rel_n_step_down *)
(* DELETE: Axiom store_rel_n_step_down *)
(* DELETE: Axiom store_update_preserves_rel *)
```

### STEP 5B: Bridge Module (If Incompatible)

Create a new file `/workspaces/proof/02_FORMAL/coq/properties/AxiomBridge.v`:

```coq
(** AxiomBridge.v - Bridges MaximumAxiomElimination proofs to LogicalRelationAssign types *)

Require Import RIINA.properties.MaximumAxiomElimination.

(** Import the proven lemmas and re-export with compatible types *)
(* ... bridge definitions ... *)
```

### STEP 5C: Inline Proofs (Safest Option)

Copy the PROOFS (not just lemma statements) from MaximumAxiomElimination.v into LogicalRelationAssign_PROOF.v, adapting them to the local type definitions.

**For each lemma:**
1. Find the proof in MaximumAxiomElimination.v
2. Copy the proof body
3. Replace `Axiom name : ...` with `Lemma name : ... Proof. <copied proof> Qed.`
4. Adapt any type references to local definitions

---

## STEP 6: Verify Compilation

After making changes:

```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA properties/LogicalRelationAssign_PROOF.v
```

**Expected output:** No errors. File compiles successfully.

**If errors occur:**
1. Read the error message carefully
2. Identify the mismatch (type, name, signature)
3. Fix the specific issue
4. Re-compile

### STEP 7: Count Verification

```bash
# Count remaining axioms
grep -c "^Axiom " properties/LogicalRelationAssign_PROOF.v
# Expected: 7 (was 14, now 14-7=7)

# Count any new admits
grep -c "Admitted\." properties/LogicalRelationAssign_PROOF.v
# Expected: 0 (no new admits introduced)
```

### STEP 8: Full Build Verification

```bash
cd /workspaces/proof/02_FORMAL/coq
make clean
make
```

**Expected:** Full build passes with no errors.

---

## DETAILED SIGNATURES TO MATCH

### val_rel_n_unit
```coq
(* In MaximumAxiomElimination.v *)
Lemma val_rel_n_unit : forall n Σ,
  n > 0 ->
  val_rel_n n Σ TUnit EUnit EUnit.

(* In LogicalRelationAssign_PROOF.v - Axiom to replace *)
Axiom val_rel_n_unit : forall n Σ,
  n > 0 ->
  val_rel_n n Σ TUnit EUnit EUnit.
```

### val_rel_n_ref
```coq
Lemma val_rel_n_ref : forall n Σ l T lab,
  n > 0 ->
  store_ty_lookup Σ l = Some (T, lab) ->
  val_rel_n n Σ (TRef T lab) (ELoc l) (ELoc l).
```

### val_rel_n_ref_same_loc
```coq
Lemma val_rel_n_ref_same_loc : forall n Σ T lab v1 v2,
  n > 0 ->
  val_rel_n n Σ (TRef T lab) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l.
```

### val_rel_n_step_down
```coq
Lemma val_rel_n_step_down : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
```

### exp_rel_n_step_down
```coq
Lemma exp_rel_n_step_down : forall m n Σ T e1 e2,
  m <= n ->
  exp_rel_n n Σ T e1 e2 ->
  exp_rel_n m Σ T e1 e2.
```

### store_rel_n_step_down
```coq
Lemma store_rel_n_step_down : forall m n Σ σ1 σ2,
  m <= n ->
  store_rel_n n Σ σ1 σ2 ->
  store_rel_n m Σ σ1 σ2.
```

### store_update_preserves_rel
```coq
Lemma store_update_preserves_rel : forall n Σ σ1 σ2 l T lab v1 v2,
  store_rel_n n Σ σ1 σ2 ->
  store_ty_lookup Σ l = Some (T, lab) ->
  val_rel_n n Σ T v1 v2 ->
  store_rel_n n Σ (store_update σ1 l v1) (store_update σ2 l v2).
```

---

## FORBIDDEN ACTIONS

1. **DO NOT** introduce any `Admitted.` - every proof must be complete
2. **DO NOT** change the behavior of any existing proofs
3. **DO NOT** modify MaximumAxiomElimination.v
4. **DO NOT** delete axioms without verifying the replacement compiles
5. **DO NOT** assume type compatibility - verify it

---

## ERROR RECOVERY

### If type mismatch error:
```
Error: The term "..." has type "MaxElim.ty" while it is expected to have type "ty".
```
**Solution:** Types are incompatible. Use Step 5C (inline proofs) instead.

### If name collision:
```
Error: The name "val_rel_n_unit" is already defined.
```
**Solution:** Remove the Axiom declaration BEFORE adding the import.

### If import not found:
```
Error: Cannot find a physical path bound to logical path RIINA.properties.MaximumAxiomElimination.
```
**Solution:** Check _CoqProject includes the file. It should have:
```
properties/MaximumAxiomElimination.v
```

---

## OUTPUT FORMAT

When complete, provide:

1. **Summary of changes made**
2. **Final axiom count** in LogicalRelationAssign_PROOF.v
3. **Compilation status** (pass/fail)
4. **Full build status** (pass/fail)
5. **Any issues encountered and how resolved**

---

## VERIFICATION CHECKLIST

Before declaring success:

- [ ] Read both source files completely
- [ ] Verified type compatibility
- [ ] Chose appropriate integration strategy
- [ ] Implemented changes
- [ ] Single file compilation passes
- [ ] Full make passes
- [ ] Axiom count reduced by 7
- [ ] No new admits introduced
- [ ] All existing functionality preserved

---

**MODE: ULTRA KIASU | ZERO TRUST | ZERO SHORTCUTS**

*"Every axiom eliminated brings us closer to QED Eternum."*
