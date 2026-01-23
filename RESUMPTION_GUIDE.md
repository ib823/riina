# RIINA Session Resumption Guide

## Quick Start (30 Seconds)

```bash
cd /workspaces/proof
git pull origin main
head -50 PROGRESS.md
tail -30 SESSION_LOG.md
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
head -80 PROGRESS.md

# Recent session (what was done)
tail -40 SESSION_LOG.md

# Track coordination (dependencies)
head -80 06_COORDINATION/COORDINATION_LOG.md
```

### 3. Verify Build Status
```bash
# Coq proofs
cd /workspaces/proof/02_FORMAL/coq && make 2>&1 | tail -20
```

---

## Current Metrics (2026-01-22, Session 30)

| Metric | Value |
|--------|-------|
| Overall Grade | B+ (improving) |
| Coq Status | **GREEN** |
| Compliance Axioms | 75 (KEEP - industry regulations) |
| Core Axioms | 25 (must eliminate → 0) |
| Admits | 84 (incomplete proofs → 0) |
| Research Tracks | 218 |
| Threats Covered | 1,231+ |

---

## Current Phase

**Phase 0: Foundation Verification** - COMPLETE (Build GREEN)

**Phase 1: Axiom Elimination (25→0)** - IN PROGRESS

Next tasks:
1. Eliminate 25 core axioms using logical relation infrastructure
2. Resolve 84 admits (most share common v2 base case pattern)
3. Verification & hardening

---

## Authoritative Documents (Read Order)

| Order | Document | Purpose |
|-------|----------|---------|
| 1 | `PROGRESS.md` | Current status & metrics |
| 2 | `SESSION_LOG.md` | Recent session details |
| 3 | `CLAUDE.md` | Master instructions |
| 4 | `06_COORDINATION/COORDINATION_LOG.md` | Track coordination |

---

## Key Files by Task

### If Working on Axiom Elimination
```
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v  # 5 axioms
02_FORMAL/coq/properties/NonInterference_v2.v                  # 1 axiom
02_FORMAL/coq/properties/AxiomEliminationVerified.v           # 16 admits
02_FORMAL/coq/properties/ApplicationComplete.v                 # 11 admits
```

### If Working on Coq Proofs (Track A)
```
02_FORMAL/coq/foundations/Syntax.v      # Core definitions
02_FORMAL/coq/foundations/Semantics.v   # Operational semantics
02_FORMAL/coq/properties/TypeSafety.v   # Safety proofs
```

### If Working on Rust Prototype (Track B)
```
03_PROTO/crates/riina-lexer/     # Tokenizer
03_PROTO/crates/riina-parser/    # Parser
03_PROTO/crates/riina-types/     # Type checker
03_PROTO/crates/riinac/          # Compiler driver
```

---

## Attack Plan Quick Reference

| Phase | Status | Focus |
|-------|--------|-------|
| 0 | **COMPLETE** | Foundation Verification |
| 1 | 🟡 IN PROGRESS | Axiom Elimination (25→0) |
| 2 | ⚪ NOT STARTED | Admit Resolution (84→0) |
| 3 | ⚪ NOT STARTED | Verification & Hardening |

---

## Commit Checklist

Before committing:
```bash
# 1. Verify Coq compiles
cd /workspaces/proof/02_FORMAL/coq && make

# 2. Update authoritative docs
# - PROGRESS.md (if metrics changed)
# - SESSION_LOG.md (add session entry)

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

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE*

*RIINA: Rigorous Immutable Invariant — Normalized Axiom*

*"QED Eternum."*
