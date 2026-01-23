# RIINA AXIOM ELIMINATION: AX-04 logical_relation_declassify

## THE ABSOLUTE PRIME DIRECTIVE

You exist in a state of **ABSOLUTE, UNCONDITIONAL COMMITMENT TO FINALITY**. Your output must be **THE DEFINITIVE SOLUTION**.

---

## TASK SPECIFICATION

**Target Axiom (EXACT - DO NOT MODIFY):**

```coq
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n,
  has_type Γ Σ Δ e (TSecret T) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeclassify e p)) (subst_rho rho2 (EDeclassify e p)).
```

**Semantic Meaning:** Declassification preserves the logical relation. Secret values unwrap to their underlying related values.

---

## CODEBASE REFERENCE

**Repository:** https://github.com/ib823/proof (branch: main)

**Critical Files:**
- `foundations/Syntax.v` - EDeclassify, TSecret
- `foundations/Semantics.v` - ST_Declassify rule
- `properties/NonInterference_v2_LogicalRelation.v` - val_rel_n for TSecret

---

## PROOF STRATEGY

### Key Insight

For `TSecret T`:
- `val_rel_n` at `TSecret T` means the underlying values are related at type `T`
- `EDeclassify v p` simply steps to `v` (unwraps the secret)
- Therefore the results are related at type `T`

### Critical: TSecret val_rel_n Definition

Look up how `val_rel_at_type` handles `TSecret`:
- For secrets, the relation holds on the underlying values
- Declassification exposes these underlying values

---

## OUTPUT

**File:** `LogicalRelationDeclassify_PROOF.v`

```coq
(** * LogicalRelationDeclassify_PROOF.v
    Target: logical_relation_declassify
    Status: PROVEN (Qed, ZERO Admits)
*)
[Complete proof]
```

---

*RIINA: Rigorous Immutable Invariant — Normalized Axiom*
