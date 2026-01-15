# TERAS Architecture Decisions

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