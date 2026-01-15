# ULTIMATE RESUMPTION PROMPT

**Copy and paste this into the next session to resume immediately.**

---

## CONTEXT: The "Infinite Timeline" / "Zero Trust" Project

We are building **TERAS-LANG**, a formally verified security language.
**Mode:** ULTRA KIASU | PARANOID | ZERO TRUST.

**Current State:**
1.  **Track B (Prototype):** **OPERATIONAL.** `terasc` works but is ahead of the proofs.
2.  **Track A (Formal Proofs):** **IN PROGRESS - EXTENDING.**
    *   `Typing.v`: Extended `has_type` to include References, Algebraic Effects, and Security primitives.
    *   **BLOCKER:** `type_uniqueness` proof is failing at `T_App`. The inversion of the function type is correctly identifying `TFn T0 T2 eps = TFn T0 T2' ε`, but `subst` is not effectively unifying `eps` and `ε` in the effect join expression.

## IMMEDIATE TASK: Fix `Typing.v` and Re-verify Soundness

We need to fix the `type_uniqueness` proof and then update the safety proofs.
*   **Goal:** 
    1. Fix `type_uniqueness` in `02_FORMAL/coq/foundations/Typing.v`.
    2. Update `02_FORMAL/coq/type_system/Progress.v` and `Preservation.v` to handle the new `has_type` constructors.
*   **Proof Note:** For `T_App`, manually use `injection H; intros; subst` to ensure the effect equality is propagated correctly before trying to unify the `effect_join` terms.

## COMMANDS TO RUN ON START
```bash
# 1. Setup OPAM environment
eval $(opam env)

# 2. Check current proof failure
cd 02_FORMAL/coq
coqc -Q . TERAS foundations/Typing.v

# 3. Verify Prototype (Optional)
cd ../../03_PROTO
cargo test
```

**Instruction to Agent:**
Resume fixing Track A.
1.  Open `02_FORMAL/coq/foundations/Typing.v`.
2.  Fix the `type_uniqueness` proof for `T_App` (and potentially other cases like `T_Case`, `T_If`, `T_Let`).
3.  Once `Typing.v` compiles, move to `type_system/Progress.v` and `Preservation.v`.
4.  Expect many failures in `Progress.v` and `Preservation.v` as they were written for the core calculus. You will need to add cases for the new expressions or use `Admitted` to keep the build moving while focusing on the core logic.
**PRIORITY:** Get `Typing.v` fully verified first.
