# RIINA Self-Hosting Compiler

This directory contains the scaffolding for RIINA's self-hosted compiler.

## Status: Phase 5 Scaffolding

The self-hosting effort is part of **Phase 8: Long-term Vision** in the
Materialization Plan. This directory provides initial structure and
placeholder files for the eventual self-hosted implementation.

## Directory Structure

```
compiler/
├── README.md           ← This file
├── main.rii            ← Compiler driver (port of riinac)
├── lexer.rii           ← Tokenizer (port of riina-lexer) [scaffolding]
├── parser.rii          ← Parser (port of riina-parser) [scaffolding]
├── types.rii           ← Type definitions (port of riina-types) [scaffolding]
├── typechecker.rii     ← Typechecker (port of riina-typechecker) [scaffolding]
└── codegen.rii         ← Code generator (port of riina-codegen) [scaffolding]
```

All 6 core modules are scaffolded. Implementation pending language feature additions.

## Bootstrap Strategy

1. **Stage 0**: Current Rust compiler (`riinac-rust`)
2. **Stage 1**: `riinac-rust` compiles RIINA compiler → `riinac-stage1`
3. **Stage 2**: `riinac-stage1` compiles RIINA compiler → `riinac-stage2`
4. **Fixpoint**: Verify `riinac-stage1` output == `riinac-stage2` output

## Language Features Required

The following language features must be added before self-hosting:

- [x] `kesan Ubah` (Effect::Mut) — Local mutable state
- [ ] Generic type inference
- [ ] StringBuilder / efficient string building
- [ ] Deep pattern matching for AST traversal

## References

- Materialization Plan: `04_SPECS/language/RIINA_MATERIALIZATION_PLAN_v1_0_0.md`
- Lexer spec: `01_RESEARCH/specs/bahasa/RIINA-LANG-LEXER-SPEC_v1_0_0.md`
- Grammar spec: `01_RESEARCH/specs/bahasa/RIINA-LANG-GRAMMAR-*.md`
- AST spec: `01_RESEARCH/specs/bahasa/RIINA-LANG-AST_v1_0_0.md`

---

RIINA = Rigorous Immutable Invariant, No Assumptions

"Q.E.D. Aeternum."
