# Claude.ai Delegation Prompts

## Purpose

This folder contains ready-to-use prompts for delegating axiom elimination tasks to Claude.ai.

## Usage

1. Open Claude.ai (claude.ai)
2. Copy the entire contents of the relevant prompt file
3. Paste into Claude.ai
4. Claude.ai will access the GitHub repository and generate the proof
5. Copy the generated Coq file back to the codebase
6. Verify compilation with `make`

## Available Prompts

| File | Axiom | Status |
|------|-------|--------|
| `PROMPT_AX01_logical_relation_ref.md` | Reference creation | READY |
| `PROMPT_AX02_logical_relation_deref.md` | Dereference | READY |
| `PROMPT_AX03_logical_relation_assign.md` | Assignment | READY |
| `PROMPT_AX04_logical_relation_declassify.md` | Declassification | READY |

## Coordination

See `../CLAUDE_AI_DELEGATION_AXIOM_ELIMINATION.md` for:
- Full task breakdown
- Assignment tracking
- Integration instructions

## Important Notes

- Each task produces a SEPARATE file (no conflicts)
- All generated proofs must compile with ZERO admits
- Integration handled by main coordinator (Claude Code)
- Do NOT modify existing codebase files

---

*RIINA: Rigorous Immutable Invariant — Normalized Axiom*
