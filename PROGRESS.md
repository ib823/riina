# TERAS Progress Tracker

## Last Updated: 2026-01-14 (Track A - NonInterference Lemma Audit)

## Current Focus: Track A (Formal Proofs) - STRICT MODE

**STATUS:** CORE SOUNDNESS VERIFIED. SECURITY PROPERTIES IN PROGRESS.
**TRACK B:** PAUSED PENDING FULL FORMAL ASSURANCE.

### COMPLETED & VERIFIED (0 ADMITS)

- [x] `foundations/Syntax.v` — Core syntax with linear effect lattice.
- [x] `foundations/Semantics.v` — **FULLY PROVEN**. `step_deterministic` proved.
- [x] `foundations/Typing.v` — **FULLY PROVEN**. `type_uniqueness` proved.
- [x] `type_system/Progress.v` — **FULLY PROVEN**.
- [x] `type_system/Preservation.v` — **FULLY PROVEN**.
- [x] `type_system/TypeSafety.v` — **FULLY PROVEN**.
- [x] `effects/EffectAlgebra.v` — **FULLY PROVEN**.

### IN PROGRESS (NOT YET VERIFIED THIS SESSION)

| File | Item | Status | Justification |
|------|------|--------|---------------|
| `properties/NonInterference.v` | `non_interference_stmt` | **BLOCKED** | `subst_rho_extend` is not provable without an explicit environment/substitution stability assumption; build currently fails in its `EVar` case. |

### Summary

**Core Language Soundness: VERIFIED**
The operational semantics are deterministic, and the type system ensures Progress and Preservation.
The foundation is mathematically solid for the core language.

**Security Properties: PARTIAL**
`non_interference_stmt` proof is present but blocked on `subst_rho_extend`. The lemma is false without a stronger environment invariant (e.g., substitution stability or closedness of `rho` images).

### Next Steps (Extreme Rigor Protocol)

1. **Assumption Ledger (Required)**: Declare the exact environment invariant needed for `subst_rho_extend`.
   - Option A: `forall y, y <> x -> [x := v] (rho y) = rho y`.
   - Option B: Define `closed_expr` using `free_in` and require all `rho y` closed.
2. **Lemma Repair**: Reprove `subst_rho_extend` with the explicit invariant and thread it through `logical_relation`.
3. **Security Proof**: Rebuild `non_interference_stmt` with the corrected lemma.
4. **Verification**: `make -C 02_FORMAL/coq` must pass with 0 admits.
5. **Track B**: **REMAIN PAUSED** until Track A security property is verified.

## Track B Progress (PAUSED)

**WARNING:** Development paused to ensure formal foundations are complete.

- [x] Workspace structure
- [x] Lexer implementation (Completed before pause)
- [ ] Parser (BLOCKED)
