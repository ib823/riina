# Package I: Core Axiom Audit

## Task

Audit and eliminate the 8 core infrastructure axioms that aren't part of the LogicalRelation modules.

## Axiom Inventory

### File: NonInterference_v2_LogicalRelation.v (5 axioms)

```bash
grep -n "^Axiom\|^Parameter" properties/NonInterference_v2_LogicalRelation.v
```

Expected axioms related to:
- Environment relations
- Substitution properties
- Free variable handling

### File: NonInterference_v2.v (1 axiom)

```coq
Parameter observer : expr -> Prop.
```

**Status:** This is a configuration parameter, not a mathematical axiom.
**Action:** Document as justified (observer is language-specific).

### File: LogicalRelationRef_PROOF.v (1 axiom)

```coq
Axiom store_ty_fresh_loc_none : forall Σ st,
  store_ty_well_formed Σ st ->
  store_ty_lookup (fresh_loc st) Σ = None.
```

**Status:** Justified axiom about well-formed stores.
**Action:** Can potentially be proven from store_ty_well_formed definition.

### File: LogicalRelationDeclassify_v2.v (1 axiom)

Policy-related axiom for declassification security.

## Analysis Tasks

For each axiom:

### 1. Classification

| Category | Description | Action |
|----------|-------------|--------|
| PROVABLE | Can be derived from existing definitions | Prove it |
| JUSTIFIED | External assumption (config, policy) | Document justification |
| REDUNDANT | Already proven elsewhere | Remove |
| BLOCKED | Needs other work first | Document dependency |

### 2. For PROVABLE axioms

Provide:
- The proof (ending with Qed)
- Or a detailed proof sketch with specific blockers

### 3. For JUSTIFIED axioms

Provide:
- Clear English explanation of why this must be assumed
- Reference to specification (if applicable)
- Confirmation it doesn't introduce unsoundness

## Expected Output

| Axiom | File | Classification | Resolution |
|-------|------|----------------|------------|
| `observer` | NI_v2.v | JUSTIFIED | Config parameter |
| `store_ty_fresh_loc_none` | LR_Ref.v | PROVABLE? | Attempt proof |
| (5 from NI_v2_LR.v) | NI_v2_LR.v | TBD | Analyze each |
| (1 from LR_Decl_v2.v) | LR_Decl_v2.v | TBD | Analyze |

## Deliverables

1. **Classification table** for all 8 axioms
2. **Proofs** for any PROVABLE axioms (Coq code)
3. **Justification document** for JUSTIFIED axioms
4. **Dependency notes** for BLOCKED axioms

## Build Verification

```bash
cd /workspaces/proof/02_FORMAL/coq
make clean && make
# Should compile with fewer axioms after this work
```
