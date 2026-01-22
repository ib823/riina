# Package L: Reference Operations Admits

## Task

Prove the 7 admits related to reference operations (allocation, lookup, update).

## Files & Admits

| File | Admits | Focus |
|------|--------|-------|
| `ReferenceOps.v` | 3 | Store operations |
| `RelationBridge.v` | 3 | Bridging step-indexed relations |
| `LogicalRelationRef_PROOF.v` | 1 | Ref creation proof |

## Key Operations

### Store Operations

```coq
(* Allocation *)
store_alloc : expr -> store -> loc * store

(* Lookup *)
store_lookup : loc -> store -> option expr

(* Update *)
store_update : loc -> expr -> store -> store

(* Fresh location *)
fresh_loc : store -> loc
```

### Key Properties

```coq
(* Fresh location is not in store *)
Lemma fresh_loc_not_in_store : forall st,
  store_lookup (fresh_loc st) st = None.

(* Update preserves other locations *)
Lemma store_update_preserves_other : forall st l l' v,
  l <> l' -> store_lookup l' (store_update l v st) = store_lookup l' st.

(* Update at location gives value *)
Lemma store_update_at_loc : forall st l v,
  store_lookup l (store_update l v st) = Some v.
```

## RelationBridge Pattern

Bridging between different relation formulations:

```coq
(* Bridge from step-indexed to limit *)
Lemma val_rel_bridge : forall Σ T v1 v2,
  (forall n, val_rel_n n Σ T v1 v2) ->
  val_rel Σ T v1 v2.

(* Bridge from limit to step-indexed *)
Lemma val_rel_to_n : forall Σ T v1 v2 n,
  val_rel Σ T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

## Strategy

### For ReferenceOps admits

Most should follow from basic definitions:
- Lookup/update are functional - use reflexivity
- Fresh location properties use store_max axioms

### For RelationBridge admits

These are typically definitional:
- `val_rel Σ T v1 v2 := forall n, val_rel_n n Σ T v1 v2`
- So bridges are often `unfold val_rel; exact H` or similar

### For LogicalRelationRef admit

Check what specifically is admitted - likely related to:
- Store extension after allocation
- Kripke monotonicity for new locations

## Reference: Package C Results

From the Claude.ai delegation (ReferenceOps.v):
- `fresh_loc_not_in_store` - Qed
- `store_update_preserves_other` - Qed
- `store_update_at_loc` - Qed
- `store_alloc_fresh` - Qed

These techniques can be adapted to the main codebase.

## Expected Output

- All 7 admits proven with Qed
- These are typically straightforward functional reasoning

## Deliverables

1. 7 Coq proofs ending with Qed
2. If any are blocked, document the specific issue

## File Locations

```
/workspaces/proof/02_FORMAL/coq/properties/
├── ReferenceOps.v
├── RelationBridge.v
└── LogicalRelationRef_PROOF.v
```
