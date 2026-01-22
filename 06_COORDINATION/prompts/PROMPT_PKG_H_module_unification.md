# Package H: LogicalRelation Module Unification

## Task

Analyze and propose unification strategy for the 4 separate LogicalRelation proof modules.

## Background

The codebase has accumulated 4 separate proof modules for logical relation operations:

| File | Purpose | Axioms | Status |
|------|---------|--------|--------|
| `LogicalRelationRef_PROOF.v` | Reference creation (ERef) | 7 | ✅ Main theorem Qed |
| `LogicalRelationDeref_PROOF_FINAL.v` | Dereferencing (EDeref) | 7 | ✅ Complete |
| `LogicalRelationAssign_PROOF.v` | Assignment (EAssign) | 18 | ✅ Complete |
| `LogicalRelationDeclassify_PROOF_REFINED.v` | Declassification | 27 | 🟡 Partial |

**Problem:** Each module defines its own local copies of:
- Types, expressions, values
- Store, store_typing
- val_rel_n, store_rel_n
- Helper lemmas

This duplication causes:
1. 59 axioms across these 4 files alone
2. Potential inconsistencies
3. Maintenance burden
4. Integration difficulties

## Analysis Task

### Step 1: Catalog Definitions

For each file, list:
- All `Inductive` definitions
- All `Definition` definitions
- All `Parameter` / `Axiom` declarations
- All proven `Lemma` / `Theorem` statements

### Step 2: Identify Common Core

Find definitions that are:
- Identical across files (copy-paste)
- Semantically equivalent but syntactically different
- Unique to each module

### Step 3: Propose Unification

Design a unified module structure:

```coq
(* Proposed structure *)
Module LogicalRelationCore.
  (* Shared definitions *)
  Definition store_typing := ...
  Definition val_rel_n := ...
  Definition store_rel_n := ...

  (* Shared lemmas *)
  Lemma val_rel_n_0_unfold : ...
  Lemma store_rel_n_mono : ...
End LogicalRelationCore.

Module LogicalRelationRef.
  Import LogicalRelationCore.
  (* Ref-specific proofs *)
End LogicalRelationRef.

(* etc. *)
```

### Step 4: Integration with Main Codebase

Map local definitions to `NonInterference_v2.v`:

| Local Definition | Main Codebase Equivalent |
|------------------|-------------------------|
| `val_rel_n` (local) | `val_rel_n` in NI_v2 |
| `store_rel_n` (local) | `store_rel_n` in NI_v2 |
| ... | ... |

## Key Questions

1. **Can the 59 axioms be reduced?** Many axioms in these modules are:
   - Basic type/expression constructors
   - Lemmas provable from `NonInterference_v2.v` definitions

2. **What's truly unique to each module?**
   - Ref: Fresh location properties
   - Deref: Store lookup properties
   - Assign: Store update properties
   - Declassify: Security label properties

3. **What's the best unification approach?**
   - Option A: Merge all into one file
   - Option B: Extract common module, keep operation-specific modules
   - Option C: Integrate proofs directly into `NonInterference_v2.v`

## Deliverables

1. **Catalog document** listing all definitions/axioms per file
2. **Dependency graph** showing which axioms depend on which
3. **Unification proposal** with concrete Coq module structure
4. **Migration plan** for moving proven lemmas to main codebase

## File Locations

```
/workspaces/proof/02_FORMAL/coq/properties/
├── LogicalRelationRef_PROOF.v          (7 axioms)
├── LogicalRelationDeref_PROOF_FINAL.v  (7 axioms)
├── LogicalRelationAssign_PROOF.v       (18 axioms)
├── LogicalRelationDeclassify_PROOF_REFINED.v (27 axioms)
└── NonInterference_v2.v                (main, 2 axioms)
```

## Expected Output

1. **Analysis Report** (markdown) with:
   - Definition catalog
   - Axiom analysis (which are truly needed vs. derivable)
   - Unification proposal

2. **Sample Unified Module** (Coq) demonstrating the approach

3. **Axiom Reduction Estimate** - how many of the 59 can be eliminated through unification
