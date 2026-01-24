# RIINA Non-Interference: Summary of 13 Remaining Admits

## The Core Structural Problem

**The `val_rel_at_type` definition for TFn does NOT include `store_wf` as a precondition.**

This means when we're inside the TFn case and need to prove preservation properties for the result stores `st1'`, `st2'`, we don't have `store_wf` for the input stores `st1`, `st2`.

### Current TFn Definition (Problematic)
```coq
| TFn T1 T2 eff =>
    forall Σ', store_ty_extends Σ Σ' ->
      forall x y, ... val_rel_lower Σ' T1 x y ->
      forall st1 st2 ctx,
        store_rel_pred Σ' st1 st2 ->    (* ONLY store_rel! *)
        exists v1' v2' st1' st2' ctx' Σ'',
          ...
```

### What's Missing
```coq
        store_wf Σ' st1 ->              (* MISSING! *)
        store_wf Σ' st2 ->              (* MISSING! *)
        stores_agree_low_fo Σ' st1 st2 -> (* MISSING! *)
```

---

## Classification of 13 Admits

| Lines | Category | Root Cause | Solution |
|-------|----------|------------|----------|
| 1334, 1593-1601, 1662, 1733, 1808, 1880 | Preservation | Missing store_wf in TFn | **Refactor definition** |
| 284, 286 | Mixed constructors | Looks impossible | **Prove contradiction** |
| 1532 | Fundamental Theorem n=0 | Complex | **Canonical forms + substitution** |

### Count
- **10 admits**: Structural issue (need definition refactor)
- **2 admits**: Should be impossible (prove contradiction)
- **1 admit**: Complex but provable (Fundamental Theorem)

---

## Recommended Solutions

### Solution A: Refactor val_rel_at_type (RECOMMENDED)

**Change the TFn case to include store_wf:**

```coq
| TFn T1 T2 eff =>
    forall Σ', store_ty_extends Σ Σ' ->
      forall x y, ... val_rel_lower Σ' T1 x y ->
      forall st1 st2 ctx,
        store_rel_pred Σ' st1 st2 ->
        store_wf Σ' st1 ->              (* ADD *)
        store_wf Σ' st2 ->              (* ADD *)
        store_has_values st1 ->          (* ADD - trivial from store_wf *)
        store_has_values st2 ->          (* ADD - trivial from store_wf *)
        stores_agree_low_fo Σ' st1 st2 -> (* ADD *)
        exists v1' v2' st1' st2' ctx' Σ'',
          store_ty_extends Σ' Σ'' /\
          ... /\
          store_wf Σ'' st1' /\           (* ADD to postcondition *)
          store_wf Σ'' st2' /\           (* ADD to postcondition *)
          stores_agree_low_fo Σ'' st1' st2' /\ (* ADD *)
          ...
```

**Impact**: This fixes ALL 10 preservation-related admits at once.

---

### Solution for Admits 284, 286 (Mixed Constructors)

These are in `val_rel_at_type_fo` for TSum where we have `EInl` vs `EInr`.

**Why impossible**: The definition of `val_rel_at_type_fo` for TSum requires SAME constructor:
```coq
| TSum T1 T2 =>
    (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ ...) \/
    (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ ...)
```

Mixed cases (EInl vs EInr) simply don't match this definition!

**Replacement code**:
```coq
(* Case is impossible - val_rel_at_type_fo for TSum requires same constructor *)
destruct Hrel as [[x1 [x2 [Heq1 [Heq2 _]]]] | [y1 [y2 [Heq1 [Heq2 _]]]]].
- (* Both Inl *) subst. discriminate.  (* Contradicts assumption v2 = EInr *)
- (* Both Inr *) subst. discriminate.  (* Contradicts assumption v1 = EInl *)
```

---

### Solution for Admit 1532 (Fundamental Theorem n=0)

At step index 0, for HO types, `val_rel_n 0` only requires TYPING (not structural equality).

**Proof approach**:
1. Use `canonical_forms_fn` to extract lambda structure
2. Beta reduction gives us the application result
3. `substitution_preserves_typing` gives us typing for result
4. For n=0 with HO result type, typing is sufficient

**The tricky part**: Showing the substituted body is a `value`. Options:
- If evaluation terminates, we get a value
- For n=0, we might be able to use the substituted body directly (not required to be value?)
- May need strong normalization

---

## Action Items

1. **Run the extraction prompt** from `ULTIMATE_EXTRACTION_PROMPT.md` in Claude Code CLI
2. **Share the output** with me
3. I will provide:
   - Exact refactored `val_rel_at_type` definition
   - Proof code for admits 284, 286
   - Proof code for admit 1532
   - Updated proofs for all 10 preservation admits

---

## Files Delivered

| File | Purpose |
|------|---------|
| `COMPLETE_ANALYSIS_13_ADMITS.v` | Detailed analysis of all admits |
| `ULTIMATE_EXTRACTION_PROMPT.md` | Prompt to extract all needed context |
| `SESSION41_SUMMARY.md` | This summary |

---

## Expected Final State

After applying the fixes:
- **0 admits** (or only truly justified axioms)
- **Build passes**
- **Non-interference theorem complete**
