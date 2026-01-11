# TERAS Progress Tracker

## Last Updated: 2026-01-11 (Session End)

## Current Focus: Track A (Formal Proofs)

### COMPLETED (No Admits)

- [x] `foundations/Syntax.v` — Core syntax
- [x] `foundations/Typing.v` — **COMPLETE** (type_uniqueness proven)
- [x] `type_system/Progress.v` — **COMPLETE**
- [x] `type_system/Preservation.v` — **COMPLETE**
- [x] `type_system/TypeSafety.v` — **COMPLETE**

### REMAINING ADMITS

| File | Lemma | Status | Notes |
|------|-------|--------|-------|
| `foundations/Semantics.v` | `step_deterministic` | Admitted | Build passes, but proof needs interactive debugging |

### Summary

**Core Type Safety is formally verified.**
The `type_uniqueness` lemma was successfully proven after fixing `T_Let` and `T_If` dependency handling and adding missing Effect cases for `T_Fst`/`T_Snd`.
`step_deterministic` remains admitted due to persistent tactic failures in non-interactive mode, but does not block type safety (which relies on `Preservation` and `Progress`, not determinism).

### Next Steps

1. **Complete `step_deterministic`**: Requires careful interactive proof.
2. **Effect System**: Implement `effects/EffectAlgebra.v` (Lattice proofs).
3. **Security**: Implement `properties/NonInterference.v`.

## Track B Progress (Not Active)

- [x] Workspace structure
- [ ] Lexer implementation
