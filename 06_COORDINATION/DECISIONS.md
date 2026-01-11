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
