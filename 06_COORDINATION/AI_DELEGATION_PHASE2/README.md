# AI Delegation Package - Phase 2: Mutual Induction

## Purpose

Prove `val_rel_n_mono` and `store_rel_n_mono` via mutual induction.

## Contents

| File | Description |
|------|-------------|
| `COPY_PASTE_PROMPT.md` | Ready-to-use prompt for external AI |
| `PHASE2_DELEGATION_PROMPT.md` | Detailed analysis and strategies |
| `01_Definitions.v` | All Coq definitions (450 lines) |
| `02_Current_val_rel_n_mono.v` | Current partial proof with admits |
| `03_store_rel_n_mono.v` | Store relation mono code |

## Quick Start

1. Open `COPY_PASTE_PROMPT.md`
2. Copy everything below the `---` line
3. Paste into Claude AI / DeepSeek / Grok
4. Receive proof
5. Test: `coqc -Q . RIINA properties/NonInterference_v2.v`

## What's Already Proven

- `val_rel_n_mono_fo` - FO-only monotonicity ✅
- `val_rel_n_fo_equiv` - FO step equivalence ✅
- `val_rel_n_step_up_fo` - FO step-up ✅

## What Needs Proving

- `val_rel_n_mono` - Full monotonicity (TFn case has 2 admits)
- `store_rel_n_mono` - Store monotonicity

## Known Difficulties

The TFn (function type) case requires:
1. For FO arguments: Use `val_rel_n_mono_fo` (solvable)
2. For HO arguments: May need typing assumptions (hard)

## Expected Outcomes

| Outcome | Likelihood | Action |
|---------|------------|--------|
| Full proof | 30% | Integrate directly |
| Partial proof (FO case) | 50% | Integrate FO, document HO |
| Needs typing precondition | 20% | Accept weaker lemma |

## Validation

```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA properties/NonInterference_v2.v
```

---

*RIINA Phase 2 Delegation Package*
*Generated: 2026-01-19*
