# Worker B Spec: store_rel_n Rewrite (5 Axioms → 1)

## Mission

Rewrite `store_rel_n` and `val_rel_n` step-0 definitions to eliminate 4 of 5 remaining axioms.
The 5th axiom (`logical_relation_declassify`) is a policy axiom and stays.

**Branch:** `track-a/store-rel-v3`
**Files to modify:** ONLY files in `02_FORMAL/coq/properties/`
**Conflict risk:** LOW — Worker A works on Track B (03_PROTO/) or other tracks

---

## Background

### Current Architecture

The step-indexed logical relation has two design choices causing unprovable axioms:

1. **`store_rel_n` uses `is_low_dec`** — at step `S n'`, LOW locations get `val_rel_n n'` but HIGH locations only get typing. This means reading from a HIGH `TRef` at step 0 for a FO stored type cannot recover structural equality.

2. **`val_rel_n 0` splits FO/HO** — FO types get `val_rel_at_type_fo` (structural equality) but HO types get `True` (just typing). The `fundamental_theorem_step_0` axiom bridges this gap.

### The 5 Axioms

| # | Name | File | Why Unprovable |
|---|------|------|----------------|
| 1 | `logical_relation_ref` | NI_v2_LR.v:779 | store_rel_n loses val_rel for HIGH locs |
| 2 | `logical_relation_deref` | NI_v2_LR.v:795 | HIGH deref at step 0 needs lost val_rel |
| 3 | `logical_relation_assign` | NI_v2_LR.v:811 | Same store_rel_n limitation |
| 4 | `logical_relation_declassify` | NI_v2_LR.v:828 | **KEEP — policy axiom** |
| 5 | `fundamental_theorem_step_0` | NI_v2.v:992 | val_rel_n 0 for HO = True, need structure |

### Target: Eliminate 1, 2, 3, 5. Keep 4.

---

## Step-by-Step Plan

### Step 1: Create Working Branch

```bash
cd /workspaces/proof
git checkout -b track-a/store-rel-v3
```

### Step 2: Fix `store_rel_n` — Track ALL Locations

**File:** `properties/NonInterference_v2.v`

Find the current `store_rel_n` definition (search for `Fixpoint store_rel_n` or `Definition store_rel_n`).

Current structure (pseudocode):
```
store_rel_n (S n') Σ st1 st2 :=
  store_max st1 = store_max st2 /\
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
    if is_low sl then
      val_rel_n n' Σ T (store_lookup l st1) (store_lookup l st2)
    else
      (* HIGH: only typing, no val_rel *)
      has_type ... (store_lookup l st1) T ... /\
      has_type ... (store_lookup l st2) T ...
```

**Change to:**
```
store_rel_n (S n') Σ st1 st2 :=
  store_max st1 = store_max st2 /\
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
    val_rel_n n' Σ T (store_lookup l st1) (store_lookup l st2)
```

Remove the `is_low_dec` branch entirely. ALL locations now carry `val_rel_n`.

### Step 3: Fix `val_rel_n 0` — Make Uniform

**File:** `properties/NonInterference_v2.v`

Current structure:
```
val_rel_n 0 Σ T v1 v2 :=
  value v1 /\ value v2 /\ closed v1 /\ closed v2 /\
  has_type nil Σ Public v1 T EffectPure /\
  has_type nil Σ Public v2 T EffectPure /\
  if first_order_type T then val_rel_at_type_fo T v1 v2
  else True  (* <-- THIS is the problem *)
```

**Change to:**
```
val_rel_n 0 Σ T v1 v2 :=
  value v1 /\ value v2 /\ closed v1 /\ closed v2 /\
  has_type nil Σ Public v1 T EffectPure /\
  has_type nil Σ Public v2 T EffectPure /\
  True  (* Step 0 is purely typing-based for ALL types *)
```

Remove the FO/HO split entirely at step 0. FO structural equality moves to step 1+.

### Step 4: Fix `stores_agree_low_fo`

The `stores_agree_low_fo` predicate and `exp_rel_n` output may need adjustment. With the new `store_rel_n`, low FO agreement should be derivable from `store_rel_n` directly (since all locations now carry `val_rel_n`).

Check if `stores_agree_low_fo` can be derived as a lemma from `store_rel_n (S n')` rather than threaded separately.

### Step 5: Repair Broken Lemmas

The main lemmas that will break:

1. **`store_rel_n_step_up`** — needs re-proof since store_rel now tracks all locations
2. **`val_rel_n_step_up`** (in combined_step_up_all) — FO base case changes
3. **`exp_rel_step1_fst_general` / `snd_general`** — may simplify since step 0 is uniform
4. **`val_rel_at_type_fo_equiv`** — may need adjustment
5. **Monotonicity lemmas** in `NonInterference_v2_Monotone.v`
6. **`logical_relation` theorem** in NI_v2_LR.v — cases that used axioms now get real proofs

### Step 6: Replace Axioms 1-3 with Proofs

**File:** `properties/NonInterference_v2_LogicalRelation.v`

With the new `store_rel_n` that tracks all locations:

**T_Ref proof sketch:**
- IH gives: e evaluates to values v1, v2 with val_rel_n n' Σ' T v1 v2
- Allocate at fresh_loc: store_update creates new location
- New store_rel: old locations preserved, new location has val_rel_n n' for v1, v2
- Result: ELoc (fresh_loc) in both, val_rel_n for TRef T sl

**T_Deref proof sketch:**
- IH gives: e evaluates to ELoc l, ELoc l with val_rel_n for TRef T sl
- store_rel_n gives: val_rel_n n' for store_lookup l st1, store_lookup l st2
- (Previously failed because HIGH locations had no val_rel — now they do)

**T_Assign proof sketch:**
- IH on e1: ELoc l with val_rel for TRef T sl
- IH on e2: v1, v2 with val_rel_n for T
- Update store: store_update l v1 st1, store_update l v2 st2
- New store_rel: location l gets new val_rel, rest preserved

### Step 7: Replace Axiom 5 with Proof

**File:** `properties/NonInterference_v2.v`

With uniform step 0 (just True), `fundamental_theorem_step_0` becomes trivial:
- val_rel_n 0 for HO types = True (just typing)
- val_rel_at_type for most HO types at step 0 with val_rel_n 0 predicates...
- Check each type constructor. For TFn: the Kripke property at step 0 with store_rel_n 0 (just domain equality) should be satisfiable since any evaluation under store_rel_n 0 gives exp_rel_n 0 = True.

This axiom may become trivially provable or may need careful case analysis.

### Step 8: Verify

```bash
cd /workspaces/proof/02_FORMAL/coq
eval $(opam env)
make clean && make -j4

# Check axioms
grep -rn "^Axiom\b" properties/*.v
# Expected: only logical_relation_declassify

# Check admits
grep -rn "Admitted\." properties/*.v
grep -rn "admit\." properties/*.v
# Expected: 0 for both
```

### Step 9: Merge

```bash
git checkout main
git merge track-a/store-rel-v3
git push origin main
```

---

## Key Files to Read First

Before starting, read these in order:

1. `properties/NonInterference_v2.v` — definitions of val_rel_n, store_rel_n, exp_rel_n, combined_step_up_all
2. `properties/NonInterference_v2_LogicalRelation.v` — the logical_relation theorem and 4 axioms
3. `properties/NonInterference_v2_Monotone.v` — monotonicity lemmas
4. `properties/ReferenceOps.v` — OLD proofs for ref/deref/assign (uses store_rel_le which tracks ALL locations — this is the model to follow)
5. `properties/StoreRelation.v` — store infrastructure

### Critical Insight

`ReferenceOps.v` contains **working proofs** of ref/deref/assign for the OLD logical relation (`store_rel_le`). That old relation tracked val_rel for ALL locations (no is_low_dec). The rewrite essentially makes `store_rel_n` behave like `store_rel_le` but step-indexed.

---

## What NOT to Touch

- `foundations/` — DO NOT MODIFY
- `type_system/` — DO NOT MODIFY
- `effects/` — DO NOT MODIFY
- `termination/` — DO NOT MODIFY
- `03_PROTO/` (Rust) — DO NOT MODIFY
- `properties/Declassification.v` — probably unchanged
- `properties/TypeSafety.v` — probably unchanged

---

## Estimated Scope

- ~200 lines of definition changes
- ~50-100 lemma re-proofs
- 2-3 files modified
- Result: 4 axioms eliminated, 1 remains (declassify)
