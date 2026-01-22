# Package M: Type Conversion & Declassification Admits

## Task

Prove the 12 admits related to type conversion and declassification operations.

## Files & Admits

| File | Admits | Focus |
|------|--------|-------|
| `TypedConversion.v` | 2 | Converting between relation formulations |
| `ApplicationComplete.v` | 2 | Function application completeness |
| `LogicalRelationDeclassify_v2.v` | 2 | v2 declassify proof |
| `LogicalRelationDeclassify_PROOF_REFINED.v` | 2 | Refined declassify |
| `LogicalRelationDeclassify_PROOF.v` | 2 | Original declassify |
| `Declassification.v` | 1 | Declassify properties |
| `NonInterference_v2_LogicalRelation.v` | 1 | Core LR for NI |

## Key Concepts

### Type Conversion

Converting between:
- `val_rel_n n Σ T v1 v2` (step-indexed)
- `val_rel Σ T v1 v2` (limit/infinite)
- `val_rel_at_type_fo T v1 v2` (first-order structural)

```coq
(* Step-up for first-order types *)
Lemma val_rel_n_step_up_first_order : forall n Σ T v1 v2,
  first_order_type T = true ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.

(* Conversion from step-indexed to infinite *)
Lemma val_rel_n_to_val_rel : forall Σ T v1 v2,
  (forall n, val_rel_n n Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```

### Declassification

Declassification (`dedah` in Bahasa Melayu) converts secret data to public:

```coq
(* EDeclassify e p: declassify expression e with policy/proof p *)

(* Key property: if secret values are indistinguishable,
   their declassifications are too *)
Lemma exp_rel_declassify : forall n Σ T e1 e2 p1 p2,
  exp_rel_n n Σ (TSecret T) e1 e2 ->
  exp_rel_n n Σ T (EDeclassify e1 p1) (EDeclassify e2 p2).
```

### Application Completeness

```coq
(* If function and arg are related, application is related *)
Lemma app_complete : forall n Σ T1 T2 f1 f2 v1 v2,
  val_rel_n n Σ (TFn T1 T2) f1 f2 ->
  val_rel_n n Σ T1 v1 v2 ->
  exp_rel_n n Σ T2 (EApp f1 v1) (EApp f2 v2).
```

## Strategy

### For TypedConversion

- Base cases (TUnit, TBool, etc.): Follow pattern from `val_rel_n_unit`
- Compound types (TProd, TSum): Need well-founded induction on type measure
- Higher-order (TFn): May remain admitted (needs termination)

### For ApplicationComplete

- Function application requires showing body evaluation terminates
- For FO result types: can often prove directly
- For HO result types: needs function termination guarantee

### For Declassification

Key insight: `TSecret T` values are always related (indistinguishable to observer):
```coq
val_rel_at_type_fo (TSecret T) v1 v2 = True  (* secrets always related *)
```

So declassify preserves relation trivially.

## Expected Output

| Category | Expected Qed | Notes |
|----------|--------------|-------|
| FO type conversion | 4-6 | Direct from definitions |
| Declassify | 4-6 | Secrets trivially related |
| HO/Application | 0-2 | May need termination |

## Deliverables

1. Proofs for FO-type admits (Qed)
2. Proofs for declassify admits (should be straightforward)
3. Detailed notes on HO blockers

## File Locations

```
/workspaces/proof/02_FORMAL/coq/properties/
├── TypedConversion.v
├── ApplicationComplete.v
├── LogicalRelationDeclassify_v2.v
├── LogicalRelationDeclassify_PROOF_REFINED.v
├── LogicalRelationDeclassify_PROOF.v
├── Declassification.v
└── NonInterference_v2_LogicalRelation.v
```
