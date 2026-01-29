# RIINA AXIOM ELIMINATION - MASTER PROMPT FOR CLAUDE AI WEB

## CRITICAL: READ THIS ENTIRE PROMPT BEFORE TAKING ANY ACTION

**Mission:** Eliminate ALL 26 axioms and ALL 57 admits from the RIINA Coq proof base.

**Mode:** ULTRA KIASU | ZERO TRUST | ZERO SHORTCUTS | INFINITE PATIENCE

---

## 1. CURRENT STATE

| Category | Count | Target |
|----------|-------|--------|
| Axioms | 26 | 0 |
| Admits | 57 | 0 |
| **Total** | **83** | **0** |

---

## 2. FILE INVENTORY

### 2.1 Files with Axioms (26 total)

| File | Axioms | Priority |
|------|--------|----------|
| NonInterference_v2_LogicalRelation.v | 5 | P0 - CORE |
| LogicalRelationAssign_PROOF.v | 14 | P1 |
| LogicalRelationDeref_PROOF_FINAL.v | 7 | P1 |

### 2.2 Files with Admits (57 total)

| File | Admits | Priority |
|------|--------|----------|
| AxiomEliminationVerified.v | 15 | P2 |
| NonInterference_v2_LogicalRelation.v | 11 | P0 |
| TypedConversion.v | 5 | P2 |
| ApplicationComplete.v | 5 | P2 |
| NonInterferenceZero.v | 4 | P2 |
| KripkeMutual.v | 4 | P2 |
| RelationBridge.v | 3 | P2 |
| ReferenceOps.v | 3 | P2 |
| NonInterference_v2.v | 2 | P1 |
| MasterTheorem.v | 2 | P2 |
| ReducibilityFull.v | 1 | P0 - ROOT BLOCKER |
| Declassification.v | 1 | P2 |
| ValRelStepLimit_PROOF.v | 1 | P2 |

### 2.3 Reference File (Proven Lemmas)

**MaximumAxiomElimination.v** - Contains 53 proven lemmas with ZERO axioms, ZERO admits.
Use this file as a REFERENCE for proof patterns, NOT for imports (type incompatibility).

---

## 3. CRITICAL TYPE INCOMPATIBILITY WARNING

Each file defines its **OWN type system**. They are self-contained modules.

**You CANNOT do this:**
```coq
Require Import MaximumAxiomElimination.
(* Will cause: Error: The term "..." has type "MaxElim.ty" while expected to have type "ty" *)
```

**You MUST do this instead:**
1. Study the proof pattern in MaximumAxiomElimination.v
2. Adapt the proof to the local type definitions
3. Replace `Axiom X : ...` with `Lemma X : ... Proof. <adapted proof> Qed.`

---

## 4. EXECUTION ORDER (DEPENDENCY-RESPECTING)

### Phase 0: ROOT BLOCKER (Do First!)

**File:** ReducibilityFull.v
**Admit:** `subst_subst_env_commute` (line ~469)

```coq
(* Current: *)
Lemma subst_subst_env_commute : forall ρ x v e,
  [x := v] (subst_env (extend_rho ρ x (EVar x)) e) =
  subst_env (extend_rho ρ x v) e.
Proof.
  (* ... *)
Admitted.
```

**Proof Strategy:**
1. Add premise `closed_rho ρ` (values in ρ have no free variables)
2. Structural induction on `e`
3. For `EVar y` case where `y ≠ x`: need `ρ y` closed so `[x := v] (ρ y) = ρ y`
4. Use existing `subst_not_free_in` lemma in same file

### Phase 1: NonInterference_v2.v (Unlocked by Phase 0)

**Admits to fix:**
1. Line ~1376: `val_rel_at_type_step_up_with_IH` (TFn case)
2. Line ~2067: `combined_step_up_all`

These depend on `well_typed_SN` from ReducibilityFull.v being proven.

### Phase 2: Core Axioms (NonInterference_v2_LogicalRelation.v)

**5 Core Axioms:**

1. `logical_relation_ref` (line ~675)
   - Reference creation preserves logical relation
   - Proof: new location, related values, extended store typing

2. `logical_relation_deref` (line ~685)
   - Dereference preserves logical relation
   - Proof: related refs → same location → same value read

3. `logical_relation_assign` (line ~695)
   - Assignment preserves logical relation
   - Proof: related refs → same location, store update with related values

4. `logical_relation_declassify` (line ~708)
   - Declassification preserves logical relation
   - Proof: dependent on security label constraints

5. `val_rel_n_to_val_rel` (line ~1675)
   - Step-indexed → limit relation
   - Proof: if ∃n. val_rel_n (S n), then val_rel exists

### Phase 3: LogicalRelationAssign_PROOF.v (14 axioms)

**7 axioms can be proven using patterns from MaximumAxiomElimination.v:**

| Axiom | Line | Proof Pattern Source |
|-------|------|---------------------|
| val_rel_n_unit | 346 | MaxElim L2 |
| val_rel_n_ref | 351 | MaxElim L5 |
| val_rel_n_ref_same_loc | 357 | MaxElim L6 |
| val_rel_n_step_down | 390 | MaxElim L8 |
| exp_rel_n_step_down | 395 | MaxElim L28 |
| store_rel_n_step_down | 400 | MaxElim L17 |
| store_update_preserves_rel | 406 | MaxElim L19 |

**For each axiom:**
1. Find the proof in MaximumAxiomElimination.v
2. Note the proof strategy (induction scheme, cases, tactics)
3. Adapt to local type definitions
4. Replace `Axiom name : type.` with `Lemma name : type. Proof. <proof> Qed.`

**Remaining 7 axioms in LogicalRelationAssign_PROOF.v:**
- T_Loc (line 206) - typing rule, keep as axiom or derive from has_type
- T_Assign (line 210) - typing rule, keep as axiom or derive
- exp_rel_n_unfold (line 363) - expression unfolding
- exp_rel_n_unit (line 376) - unit expression
- exp_rel_n_base (line 380) - base case
- exp_rel_n_assign (line 384) - assign expression
- fundamental_theorem (line 429) - THE fundamental theorem

### Phase 4: LogicalRelationDeref_PROOF_FINAL.v (7 axioms)

Self-contained type system. Prove each axiom using local definitions.

### Phase 5: Remaining 57 Admits

Tackle by file, in priority order from the table above.

---

## 5. PROOF PATTERN REFERENCE

### Pattern A: Step-indexed induction (for step_down lemmas)

```coq
Lemma val_rel_n_step_down : forall n m Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  induction n as [|n' IHn].
  - intros m Σ T v1 v2 Hle Hrel.
    assert (m = 0) by lia. subst. simpl. exact I.
  - intros m Σ T v1 v2 Hle Hrel.
    destruct m as [|m'].
    + simpl. exact I.
    + simpl in Hrel. destruct Hrel as [Hprev Hstruct].
      simpl. split.
      * apply IHn with (m := m'); auto. lia.
      * (* structural cases by type *)
        destruct T; (* handle each type constructor *) ...
Qed.
```

### Pattern B: Store relation preservation (for store_update_preserves_rel)

```coq
Lemma store_update_preserves_rel : forall n Σ σ1 σ2 l T lab v1 v2,
  store_rel_n n Σ σ1 σ2 ->
  store_ty_lookup l Σ = Some (T, lab) ->
  val_rel_n n Σ T v1 v2 ->
  store_rel_n n Σ (store_update σ1 l v1) (store_update σ2 l v2).
Proof.
  intros n Σ σ1 σ2 l T lab v1 v2 Hrel Hty Hvrel.
  unfold store_rel_n in *.
  intros l' T' sl' Hty' v1' v2' Hv1' Hv2'.
  destruct (Nat.eq_dec l l') as [Heq | Hneq].
  - (* l = l': updated location *)
    subst l'. rewrite store_update_lookup_eq in *.
    inversion Hv1'. inversion Hv2'. subst.
    rewrite Hty in Hty'. inversion Hty'. subst.
    exact Hvrel.
  - (* l ≠ l': other location, use original relation *)
    rewrite store_update_lookup_neq in *; auto.
    apply (Hrel l' T' sl' Hty' v1' v2' Hv1' Hv2').
Qed.
```

### Pattern C: Reference value inversion (for val_rel_n_ref_same_loc)

```coq
Lemma val_rel_n_ref_same_loc : forall n Σ T lab v1 v2,
  n > 0 ->
  val_rel_n n Σ (TRef T lab) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l /\ store_ty_lookup l Σ = Some (T, lab).
Proof.
  intros n Σ T lab v1 v2 Hgt Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [l [H1 [H2 H3]]]]]].
  exists l. auto.
Qed.
```

---

## 6. VERIFICATION PROTOCOL

After EACH file modification:

```bash
# 1. Compile the modified file
coqc -Q . RIINA properties/FILENAME.v

# 2. If successful, check for remaining admits
grep -c "Admitted\." properties/FILENAME.v

# 3. Check for remaining axioms
grep -c "^Axiom " properties/FILENAME.v

# 4. Full build verification
make clean && make
```

---

## 7. FORBIDDEN ACTIONS

1. **NEVER** use `Admitted.` - every proof must end with `Qed.`
2. **NEVER** leave partial proofs
3. **NEVER** assume type compatibility between files
4. **NEVER** use `admit.` tactic
5. **NEVER** break existing proofs
6. **NEVER** modify the type definitions (only replace Axioms with Lemmas)

---

## 8. SUCCESS CRITERIA

| Metric | Before | After |
|--------|--------|-------|
| Axioms | 26 | 0 |
| Admits | 57 | 0 |
| Compilation | Pass | Pass |
| `make` | Pass | Pass |

---

## 9. OUTPUT FORMAT

For each file modified, report:

1. **File:** name.v
2. **Axioms eliminated:** count and names
3. **Admits eliminated:** count and names
4. **Compilation status:** Pass/Fail
5. **New axioms/admits:** 0 (must be zero)

---

## 10. NOTES ON SELF-CONTAINED FILES

Each proof file defines:
- Its own `ty` (type)
- Its own `expr` (expression)
- Its own `val_rel_n`, `exp_rel_n`, `store_rel_n`
- Its own `store`, `store_typing`

This means you MUST adapt proof patterns to local definitions.
The logical structure is the same, but identifiers may differ.

Example adaptation:
```coq
(* In MaximumAxiomElimination.v: *)
store_ty_lookup l Σ = Some (T, lab)

(* In LogicalRelationAssign_PROOF.v: *)
Σ l = Some (T, lab)

(* These are semantically equivalent but syntactically different *)
```

---

**MODE: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE**

*"Every axiom eliminated brings us closer to QED Eternum."*

*"QED Eternum."*
