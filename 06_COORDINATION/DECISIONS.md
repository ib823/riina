# RIINA Architecture Decisions

## Decision Log

### D001: Repository Structure

**Date**: 2026-01-11
**Decision**: Single repository with track-based directories
**Rationale**: Simplifies coordination for solo developer
**Status**: IMPLEMENTED

### D002: Coq as Primary Proof Assistant

**Date**: 2026-01-11
**Decision**: Use Coq 8.18.0 as primary, Lean 4 as secondary
**Rationale**: Better library support for PL proofs, mature ecosystem
**Status**: IMPLEMENTED

### D003: Zero Third-Party Crypto Dependencies

**Date**: 2026-01-03
**Decision**: Implement all crypto from scratch (Law 8)
**Rationale**: Nation-state resistance requires no supply chain trust
**Status**: IMPLEMENTED (symmetric), IN PROGRESS (asymmetric)

### D004: Lexer-First Prototype Development

**Date**: 2026-01-11
**Decision**: Track B starts with complete lexer before parser
**Rationale**: Lexer is self-contained, enables early testing
**Status**: IN PROGRESS

### D005: Certified Compilation (Domain R)

**Date**: 2026-01-15
**Decision**: Implement Translation Validation (TERAS-TV) instead of just a certified compiler.
**Rationale**: Eliminates "Trusting Trust" attacks. If the compiler lies, the proof fails.
**Status**: RESEARCH (Foundational)

### D006: Hardware Contracts (Domain S)

**Date**: 2026-01-15
**Decision**: Verify against an Augmented ISA model (ISA v2.0) that includes microarchitectural leakage.
**Rationale**: "Normal" proofs are invalid on speculative hardware (Spectre). We must model the hardware as an adversary.
**Status**: RESEARCH (Foundational)

### D007: Hermetic Recursive Bootstrap (Domain T)

**Date**: 2026-01-15
**Decision**: Bootstrap the entire toolchain from a single ~512-byte hex seed (`hex0`).
**Rationale**: Eliminates all supply chain attacks. We trust no binary on Earth.
**Status**: RESEARCH (Foundational)

### D008: Runtime Guardian (Domain U)

**Date**: 2026-01-15
**Decision**: Run applications under a formally verified Micro-Hypervisor (Sentinel).
**Rationale**: Physical faults (cosmic rays) bypass static proofs. The Sentinel enforces invariants at runtime.
**Status**: RESEARCH (Foundational)

### D009: Security-Aware Store Relation

**Date**: 2026-01-23
**Decision**: Make store_rel_n security-level aware - LOW locations require val_rel_n, HIGH only require typing.
**Rationale**: HIGH security data is not observable by low-security observers, so requiring structural equality is unnecessary and creates unprovable admits.
**Status**: IMPLEMENTED (Session 40)

### D010: Strong Induction for Step-Up

**Date**: 2026-01-23
**Decision**: Use strong induction via `lt_wf_ind` for combined_step_up_all theorem.
**Rationale**: Resolves mutual dependency between val_rel_n and store_rel_n step-up by providing IH for all m < n.
**Status**: IMPLEMENTED (Session 40)

### D011: Type Size Induction for TFn

**Date**: 2026-01-23
**Decision**: Use ty_size_induction for TFn case in val_rel step-up.
**Rationale**: Arguments T1 in TFn T1 T2 have strictly smaller ty_size, enabling recursive IH application.
**Status**: IMPLEMENTED (Session 41)

### D012: Materialization Plan Adoption

**Date**: 2026-01-30
**Decision**: Adopt `RIINA_MATERIALIZATION_PLAN_v1_0_0.md` as authoritative 7-phase plan for taking RIINA from prototype to production.
**Rationale**: Comprehensive plan correcting inaccurate state assumptions, incorporating syntax improvement spec, with concrete file paths, line estimates, and dependency graph.
**Status**: DOCUMENTED (execution deferred until Track A stabilizes)

### D013: Parser Desugaring Principle

**Date**: 2026-01-30
**Decision**: New parser syntax (pipe `|>`, guard `pastikan`, for-in, while) MUST desugar to existing `expr` constructors (EApp, EIf, ELet, ELam) — zero Coq impact.
**Rationale**: Avoids expensive re-verification of formal proofs when adding syntactic sugar.
**Status**: DOCUMENTED (pending implementation in Phase 1.2)

### D014: While Loop Termination Strategy (OPEN)

**Date**: 2026-01-30
**Decision**: PENDING — requires decision between (a) bounded iteration with fuel parameter, (b) effect-based divergence marker, or (c) termination proof obligation.
**Rationale**: While loops can diverge; RIINA's strong normalization guarantee (well_typed_SN) must be reconciled.
**Status**: OPEN (see materialization plan §15 for details)