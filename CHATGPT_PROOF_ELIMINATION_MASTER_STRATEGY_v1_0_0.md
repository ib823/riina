# CHATGPT PROOF ELIMINATION MASTER STRATEGY (RIINA CODEBASE-ALIGNED)

Version: 1.0.0
Target codebase: /workspaces/proof/02_FORMAL/coq
Scope: NonInterference.v step-indexed logical relations (RIINA)

This strategy is aligned to the current RIINA definitions (ty/expr/value, val_rel_n, store_rel_n, exp_rel_n).
ChatGPT web has no filesystem access, so every prompt must carry full context.

---

## 1) Required Context
Use `CHATGPT_PROMPTS_READY_TO_USE.md` as the context pack. It includes:
- Syntax: ty, expr, value, subst
- Semantics: step, multi_step, store
- Typing: store_ty, store_ty_extends, free_in
- Logical relations: val_rel_at_type, val_rel_n, store_rel_n, exp_rel_n
- Environment substitution: rho_shadow, subst_rho
- Key lemmas: canonical_forms_fn/prod/sum, val_rel_at_type_fo_full_indep

Do not attempt proof tasks without pasting the full context.

---

## 2) Primary Proof Targets (Aligned)

### 2.1 Step-1 Axiom Replacements (Typed)
File: `02_FORMAL/coq/properties/AxiomEliminationVerified.v`
Goal: replace non-typed axioms in `NonInterference.v` with typed lemmas.

Key lemmas to prove in ChatGPT (see prompt file for statements):
- exp_rel_step1_app_typed
- exp_rel_step1_let_typed
- exp_rel_step1_if_same_bool

Note: these are already present as lemmas in `AxiomEliminationVerified.v`. If you are regenerating proofs, use the exact signatures and rely on canonical forms.

### 2.2 First-Order Step-Up Lemma
File: `02_FORMAL/coq/properties/NonInterference.v`
Goal: fill `val_rel_n_step_up_fo` using `val_rel_at_type_fo_full_indep`.

---

## 3) Why the Original Prompts Were Misaligned
The old prompts referenced:
- TERAS-LANG (not RIINA)
- type/value/expr definitions that do not exist in the current code
- TArrow/TRef/TLabeled shapes that differ from RIINA
- exp_rel/val_rel signatures that do not match the code

The updated prompt pack fixes these mismatches.

---

## 4) Verification Protocol (Local)
After integrating any proof into the codebase:

```bash
cd /workspaces/proof/02_FORMAL/coq
make clean && make -j4

echo "=== FINAL COUNT ==="
echo "Remaining Axioms: $(grep -r '^Axiom' . --include='*.v' | wc -l)"
echo "Remaining Admitted: $(grep -r 'Admitted\.' . --include='*.v' | wc -l)"
echo "Total Qed: $(grep -r '^Qed\.' . --include='*.v' | wc -l)"
```

---

## 5) Extension Plan (Optional)
If you want to target `FundamentalTheorem.v` admits or `ReferenceOps.v` lemmas:
- These require different contexts (Red/SN semantics or cumulative relations)
- Create a separate context pack for each file
- Do not mix `val_rel_n` and `val_rel_le` contexts in the same ChatGPT session

