# RIINA Session Resumption Guide

## Quick Start (30 Seconds)

```bash
cd /workspaces/proof
git pull origin main
head -50 PROGRESS.md
tail -50 SESSION_LOG.md
```

---

## Session Recovery Checklist

### 1. Git Sync
```bash
cd /workspaces/proof
git pull origin main
git status
```

### 2. Check Current Status
```bash
# Quick status (key metrics)
head -50 PROGRESS.md

# Recent session (what was done)
tail -50 SESSION_LOG.md

# Track coordination (dependencies)
head -100 06_COORDINATION/COORDINATION_LOG.md
```

### 3. Verify Build Status
```bash
# Coq proofs
cd /workspaces/proof/02_FORMAL/coq && make 2>&1 | tail -20

# Rust prototype
cd /workspaces/proof && cargo test --workspace 2>&1 | tail -20
```

---

## Current Metrics (2026-01-18)

| Metric | Value |
|--------|-------|
| Overall Grade | B+ (80%) |
| Research Tracks | 218 |
| Axioms | 19 (target: 0) |
| Theorems Required | ~2,500 |
| Threats Covered | 1,231+ |
| Coq Status | ✅ COMPILES |
| Rust Tests | ✅ 503 PASSING |

---

## Current Phase

**Phase 0: Foundation Verification** (85% complete)

Next tasks:
1. Fix CumulativeMonotone.v TFn case
2. Complete step monotonicity proof
3. Begin axiom elimination

---

## Authoritative Documents (Read Order)

| Order | Document | Purpose |
|-------|----------|---------|
| 1 | `PROGRESS.md` | Current status & metrics |
| 2 | `SESSION_LOG.md` | Recent session details |
| 3 | `CLAUDE.md` | Master instructions |
| 4 | `06_COORDINATION/COORDINATION_LOG.md` | Track coordination |
| 5 | `01_RESEARCH/MASTER_ATTACK_PLAN_COMPLETE.md` | Full attack plan |

---

## Key Files by Task

### If Working on Coq Proofs (Track A)
```
02_FORMAL/coq/foundations/Syntax.v      # Core definitions
02_FORMAL/coq/foundations/Semantics.v   # Operational semantics
02_FORMAL/coq/properties/TypeSafety.v   # Safety proofs
02_FORMAL/coq/properties/TypeMeasure.v  # Measure definitions
```

### If Working on Axiom Elimination
```
02_FORMAL/coq/properties/LogicalRelation.v  # 19 axioms here
02_FORMAL/coq/properties/CumulativeMonotone.v  # Step monotonicity
```

### If Working on Rust Prototype (Track B)
```
03_PROTO/crates/riina-lexer/     # Tokenizer
03_PROTO/crates/riina-parser/    # Parser
03_PROTO/crates/riina-types/     # Type checker
03_PROTO/crates/riinac/          # Compiler driver
```

### If Working on Tooling (Track F)
```
05_TOOLING/crates/riina-core/src/crypto/  # Crypto primitives
```

---

## Attack Plan Quick Reference

| Phase | Status | Focus |
|-------|--------|-------|
| 0 | 🟡 85% | Foundation Verification |
| 1 | ⚪ 0% | Axiom Elimination (19→0) |
| 2 | ⚪ 0% | Core Properties (~375 theorems) |
| 3 | ⚪ 0% | Domain Properties (~2,570 theorems) |
| 4 | ⚪ 0% | Implementation Verification |
| 5 | ⚪ 0% | Multi-Prover Verification |
| 6 | ⚪ 0% | Production Hardening |

---

## Commit Checklist

Before committing:
```bash
# 1. Verify Coq compiles
cd /workspaces/proof/02_FORMAL/coq && make

# 2. Verify Rust tests pass
cd /workspaces/proof && cargo test --workspace

# 3. Commit with proper format
git add -A
git commit -m "[TRACK_X] [TYPE] Description"
git push origin main
```

---

## Emergency Recovery

If something breaks:
```bash
# Check last working commit
git log --oneline -10

# Revert if needed
git revert HEAD

# Check for uncommitted work
git diff
git stash
```

---

## Contact

Questions? Check:
1. `CLAUDE.md` for instructions
2. `01_RESEARCH/MASTER_ATTACK_PLAN_COMPLETE.md` for strategy
3. `06_COORDINATION/DECISIONS.md` for past decisions

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE*

*RIINA: Rigorous Immutable Integrity No-attack Assured*

*"Security proven. Family driven."*
