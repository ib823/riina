# Improvement Coordination Protocol

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  COORDINATION PROTOCOL: REVOLUTIONARY IMPROVEMENTS                               ║
║  Version: 1.0.0                                                                  ║
║  Date: 2026-01-16                                                                ║
║  Status: ACTIVE                                                                  ║
║                                                                                  ║
║  Purpose: Prevent conflicts while implementing improvements systematically       ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

## 1. Overview

This protocol ensures that multiple implementers (human or AI agents) can work on
RIINA improvements without conflicts. It defines:

1. **File ownership rules** - Who can modify what
2. **Locking mechanism** - How to claim work
3. **Safe zones** - Areas that can be worked on concurrently
4. **Conflict resolution** - What to do if conflicts occur
5. **Progress tracking** - How to communicate status

---

## 2. Current Work Tracking

### 2.1 Active Work Registry

**Format:** Update this table when starting/completing work.

| Improvement ID | Worker | Started | Status | Files Affected |
|----------------|--------|---------|--------|----------------|
| (none active) | | | | |

### 2.2 Lock File Mechanism

Before modifying any existing file, check and update the lock:

**File:** `06_COORDINATION/.locks`

```
# Format: FILE_PATH|WORKER_ID|TIMESTAMP|IMPROVEMENT_ID
# Example:
# 02_FORMAL/coq/properties/NonInterference.v|claude-123|2026-01-16T10:00:00Z|P1-001
```

**Rules:**
1. Check if file is locked before starting
2. If locked by another worker, DO NOT modify
3. Lock expires after 4 hours of inactivity
4. Always release lock when done

---

## 3. Safe Zones (No Coordination Needed)

### 3.1 NEW Files - Always Safe

Creating new files in these locations requires NO coordination:

| Location | Purpose |
|----------|---------|
| `03_PROTO/crates/riina-symbols/` | NEW crate |
| `03_PROTO/crates/riina-arena/` | NEW crate |
| `03_PROTO/crates/riina-span/` | NEW crate |
| `03_PROTO/crates/riina-errors/` | NEW crate |
| `03_PROTO/crates/riina-constants/` | NEW crate |
| `05_TOOLING/crates/teras-core/src/crypto/aes_ni.rs` | NEW file |
| `05_TOOLING/crates/teras-core/src/crypto/aes_bitsliced.rs` | NEW file |
| `01_RESEARCH/specs/*` | Specifications |
| `01_RESEARCH/IMPROVEMENT_ROADMAP*.md` | Planning docs |

### 3.2 Test Files - Usually Safe

Adding new test files is generally safe:

| Location | Notes |
|----------|-------|
| `02_FORMAL/coq/tests/` | NEW test proofs |
| `03_PROTO/crates/*/tests/` | NEW test modules |
| `05_TOOLING/crates/*/tests/` | NEW test modules |

### 3.3 Documentation - Usually Safe

| Location | Notes |
|----------|-------|
| `01_RESEARCH/**/*.md` | Research docs |
| `06_COORDINATION/*.md` | Coordination docs |

---

## 4. Restricted Zones (Coordination Required)

### 4.1 Coq Proofs - HIGH CONFLICT RISK

**Files:**
- `02_FORMAL/coq/foundations/*.v`
- `02_FORMAL/coq/type_system/*.v`
- `02_FORMAL/coq/effects/*.v`
- `02_FORMAL/coq/properties/*.v`

**Protocol:**
1. MUST lock before modifying
2. MUST check `_CoqProject` and `Makefile` for dependencies
3. MUST run `make` to verify all proofs still compile
4. Only ONE worker on Coq files at a time recommended

### 4.2 Rust Core Types - MEDIUM CONFLICT RISK

**Files:**
- `03_PROTO/crates/riina-types/src/lib.rs`
- `03_PROTO/crates/riina-lexer/src/token.rs`

**Protocol:**
1. These are foundational - changes affect many files
2. Prefer additive changes (new variants) over modifications
3. Coordinate if removing or changing existing definitions

### 4.3 Workspace Configurations - MEDIUM CONFLICT RISK

**Files:**
- `03_PROTO/Cargo.toml`
- `05_TOOLING/Cargo.toml`
- `02_FORMAL/coq/_CoqProject`
- `02_FORMAL/coq/Makefile`

**Protocol:**
1. Adding new crates/members is usually safe
2. Changing existing configurations requires lock

---

## 5. Improvement Implementation Order

### 5.1 Phase 0: Foundation (Can Start Immediately)

These improvements create NEW infrastructure with NO conflicts:

```
┌─────────────────────────────────────────────────────────┐
│  PHASE 0: SAFE TO START ANYTIME                         │
├─────────────────────────────────────────────────────────┤
│  P0-001: riina-constants crate (NEW)                    │
│  P0-002: riina-symbols crate (NEW)                      │
│  P0-003: riina-arena crate (NEW)                        │
│  P0-004: riina-errors crate (NEW)                       │
│  P0-005: riina-span crate (NEW)                         │
└─────────────────────────────────────────────────────────┘
```

### 5.2 Phase 1: Proofs (Requires Lock on 02_FORMAL/)

```
┌─────────────────────────────────────────────────────────┐
│  PHASE 1: REQUIRES COQ FILE LOCKS                       │
├─────────────────────────────────────────────────────────┤
│  P1-001: KripkeWorlds.v (NEW FILE - safer)              │
│  P1-002: ValueRelation.v (NEW FILE - safer)             │
│  P1-003: NonInterference.v (MODIFY - lock required)     │
│  P1-004: Semantics.v (MODIFY - lock required)           │
│  P1-005: EffectAlgebra.v (MODIFY - lock required)       │
└─────────────────────────────────────────────────────────┘
```

### 5.3 Phase 2: Performance (Modular)

```
┌─────────────────────────────────────────────────────────┐
│  PHASE 2: CAN BE PARALLELIZED                           │
├─────────────────────────────────────────────────────────┤
│  P2-001: fast_lexer.rs (NEW FILE - safe)                │
│  P2-002: simd.rs (NEW FILE - safe)                      │
│  P2-003: ast.rs (NEW FILE - safe)                       │
│  P2-004: Migrate lexer.rs (MODIFY - needs lock)         │
│  P2-005: Migrate parser (MODIFY - needs lock)           │
└─────────────────────────────────────────────────────────┘
```

### 5.4 Phase 3: Crypto (Independent Track)

```
┌─────────────────────────────────────────────────────────┐
│  PHASE 3: MOSTLY INDEPENDENT                            │
├─────────────────────────────────────────────────────────┤
│  P3-001: aes_ni.rs (NEW FILE - safe)                    │
│  P3-002: aes_bitsliced.rs (NEW FILE - safe)             │
│  P3-003: ml_kem.rs (REWRITE - lock required)            │
│  P3-004: ml_dsa.rs (REWRITE - lock required)            │
│  P3-005: x25519.rs (REWRITE - lock required)            │
└─────────────────────────────────────────────────────────┘
```

---

## 6. Step-by-Step Work Protocol

### 6.1 Before Starting Work

```bash
# 1. Pull latest changes
cd /workspaces/proof
git pull origin main

# 2. Check current locks
cat 06_COORDINATION/.locks 2>/dev/null || echo "No locks"

# 3. Check PROGRESS.md for ongoing work
cat PROGRESS.md | grep -A5 "Current Work"

# 4. Check SESSION_LOG.md for recent activity
tail -30 SESSION_LOG.md
```

### 6.2 Claiming Work

```bash
# 1. Update lock file (if modifying existing files)
echo "FILE_PATH|WORKER_ID|$(date -u +%Y-%m-%dT%H:%M:%SZ)|IMPROVEMENT_ID" >> 06_COORDINATION/.locks

# 2. Update Active Work Registry in this file

# 3. Update SESSION_LOG.md
echo "## $(date -u +%Y-%m-%dT%H:%M:%SZ)" >> SESSION_LOG.md
echo "Worker: YOUR_ID" >> SESSION_LOG.md
echo "Starting: IMPROVEMENT_ID" >> SESSION_LOG.md
echo "Files: LIST_OF_FILES" >> SESSION_LOG.md

# 4. Commit the claim
git add -A
git commit -m "[COORD] Claiming IMPROVEMENT_ID"
git push origin main
```

### 6.3 During Work

```bash
# Commit frequently (every 30 min or significant change)
git add -A
git commit -m "[IMPROVEMENT_ID] Description of change"
git push origin main
```

### 6.4 Completing Work

```bash
# 1. Run verification
# For Coq:
cd 02_FORMAL/coq && make clean && make

# For Rust:
cd 03_PROTO && cargo test --all && cargo clippy -- -D warnings

# 2. Remove lock
# Edit 06_COORDINATION/.locks to remove your entry

# 3. Update Active Work Registry (mark complete)

# 4. Update PROGRESS.md

# 5. Final commit
git add -A
git commit -m "[IMPROVEMENT_ID] COMPLETE: Description"
git push origin main
```

---

## 7. Conflict Resolution

### 7.1 If You Encounter a Locked File

1. **DO NOT modify** the locked file
2. Work on something else from the safe zones
3. Check back after lock expires (4 hours)
4. If urgent, coordinate with lock holder

### 7.2 If Git Merge Conflict Occurs

```bash
# 1. Stash your changes
git stash

# 2. Pull latest
git pull origin main

# 3. Apply your changes
git stash pop

# 4. Resolve conflicts manually
# 5. Test thoroughly before committing
# 6. If unsure, ask for help
```

### 7.3 If Coq Proofs Break

```bash
# 1. Identify the breaking change
git log --oneline -10
git diff HEAD~1

# 2. If your change broke it, fix it
# 3. If someone else's change broke it:
#    - Document in PROGRESS.md
#    - DO NOT force your change
#    - Coordinate with the other worker
```

---

## 8. Communication Protocol

### 8.1 SESSION_LOG.md Format

```markdown
## Session: YYYY-MM-DDTHH:MM:SSZ
Worker: [identifier]
Improvement: [P#-###]
Status: [Starting|In Progress|Blocked|Complete]
Files Modified:
- file1.rs
- file2.v
Notes:
- [Any relevant notes]
Blockers:
- [Any blockers encountered]
```

### 8.2 Commit Message Format

```
[IMPROVEMENT_ID] [TYPE] Brief description

TYPE:
- START: Beginning work on improvement
- WIP: Work in progress
- FIX: Bug fix
- COMPLETE: Improvement finished
- COORD: Coordination-only (locks, registry)

Examples:
[P0-002] START: Creating riina-symbols crate
[P1-001] WIP: Implementing KripkeWorlds.v
[P2-001] COMPLETE: Fast lexer implementation
[COORD] Releasing lock on NonInterference.v
```

---

## 9. Recommended Parallel Work Assignments

### 9.1 For Multiple Workers

If multiple workers are available, assign by track:

| Worker | Track | Improvements |
|--------|-------|--------------|
| Worker A | Foundation | P0-001, P0-002, P0-003, P0-004, P0-005 |
| Worker B | Proofs | P1-001, P1-002 (new files first) |
| Worker C | Performance | P2-001, P2-002, P2-003 (new files first) |
| Worker D | Crypto | P3-001, P3-002 (new files first) |

### 9.2 Single Worker Priority

If only one worker, prioritize:

1. **P0-*** (Foundation) - Enables everything else
2. **P3-001, P3-002** (Crypto new files) - Independent
3. **P2-001, P2-002** (Lexer new files) - Independent
4. **P1-001, P1-002** (Proof new files) - New structure
5. Then migration/modification tasks

---

## 10. Quick Reference

### 10.1 Safe Actions (No Lock Needed)

- Creating new crates in `03_PROTO/crates/`
- Creating new files in `01_RESEARCH/specs/`
- Creating new `.rs` files with `_new` or `_v2` suffix
- Adding tests
- Adding documentation

### 10.2 Unsafe Actions (Lock Required)

- Modifying any `.v` file in `02_FORMAL/coq/`
- Modifying `lib.rs` in existing crates
- Modifying `Cargo.toml` workspace files
- Modifying `_CoqProject` or `Makefile`
- Renaming or deleting any file

### 10.3 Emergency Contacts

If blocked or uncertain:
1. Document in `PROGRESS.md`
2. Add note to `SESSION_LOG.md`
3. Move to safe zone work
4. Wait for coordination

---

## 11. Initialization Checklist

Before implementing ANY improvement, verify:

- [ ] Read `01_RESEARCH/IMPROVEMENT_ROADMAP_REVOLUTIONARY.md`
- [ ] Read relevant `01_RESEARCH/specs/SPEC_*.md`
- [ ] Check `06_COORDINATION/.locks` for conflicts
- [ ] Check `PROGRESS.md` for ongoing work
- [ ] Check `SESSION_LOG.md` for recent activity
- [ ] Create lock if modifying existing files
- [ ] Update Active Work Registry
- [ ] Begin implementation

---

*Protocol Status: ACTIVE*
*Last Updated: 2026-01-16*
