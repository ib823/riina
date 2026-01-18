# CLAUDE.md — RIINA Proof Repository

## CRITICAL: READ THIS ENTIRE FILE BEFORE ANY ACTION

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║                                                                                  ║
║  ██████╗ ██╗██╗███╗   ██╗ █████╗                                                ║
║  ██╔══██╗██║██║████╗  ██║██╔══██╗                                               ║
║  ██████╔╝██║██║██╔██╗ ██║███████║                                               ║
║  ██╔══██╗██║██║██║╚██╗██║██╔══██║                                               ║
║  ██║  ██║██║██║██║ ╚████║██║  ██║                                               ║
║  ╚═╝  ╚═╝╚═╝╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝                                               ║
║                                                                                  ║
║  Rigorous Immutable Integrity No-attack Assured                                  ║
║                                                                                  ║
║  RIINA PROOF REPOSITORY — CLAUDE CODE GUIDE                                      ║
║                                                                                  ║
║  Repository: https://github.com/ib823/proof                                      ║
║  Purpose: Formal proofs and prototype for RIINA                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE           ║
║                                                                                  ║
║  "Security proven. Family driven."                                               ║
║                                                                                  ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## 0. ABOUT RIINA

### 0.1 Name Origin

```
RIINA = Reena + Isaac + Imaan + No-attack + Assured

R  — Reena (foundation, the queen)
I  — Isaac (first pillar)
I  — Imaan (second pillar)
NA — No-attack Assured (the guarantee)

Technical Acronym:
RIINA = Rigorous Immutable Integrity No-attack Assured
```

### 0.2 What Is RIINA?

RIINA is the world's **first formally verified programming language** with:

1. **Mathematical guarantees** — All security properties proven in Coq
2. **Bahasa Melayu syntax** — Native Malaysian language keywords
3. **Zero-trust architecture** — Compiler, hardware, and supply chain untrusted
4. **Family legacy** — Named for Reena, Isaac, and Imaan

### 0.3 File Extension

| Extension | Purpose |
|-----------|---------|
| `.rii` | RIINA source files |
| `.riih` | RIINA header/interface files |

### 0.4 Key Syntax (Bahasa Melayu)

| Bahasa Melayu | English | Example |
|---------------|---------|---------|
| `fungsi` | fn | `fungsi tambah(x: Nombor) -> Nombor` |
| `biar` | let | `biar nama = "Ahmad";` |
| `kalau` | if | `kalau x > 0 { ... }` |
| `pulang` | return | `pulang hasil;` |
| `rahsia` | secret | `biar kunci: Rahsia<Teks>` |
| `dedah` | declassify | `dedah(nilai, dasar: "..."}` |

**Full syntax specification:** `01_RESEARCH/specs/bahasa/RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md`

### 0.5 Current Project Status (2026-01-18)

| Metric | Value | Notes |
|--------|-------|-------|
| **Overall Grade** | B+ (80%) | Foundations solid, proofs ongoing |
| **Research Tracks** | 218 | 55 existing + 163 new identified |
| **Axioms (Current)** | 19 | Target: 0 |
| **Theorems (Required)** | ~2,500 | Comprehensive coverage |
| **Threats Covered** | 1,231+ | All made obsolete |
| **Coq Compilation** | ✅ PASSING | make succeeds |
| **Rust Tests** | ✅ 503 PASSING | All tests pass |

**Phase Status:**
- Phase 0 (Foundation): 85% complete
- Phase 1-6: Defined, not started

**See `PROGRESS.md` for detailed status.**

---

## 1. REPOSITORY OVERVIEW

This repository contains the **formal foundations** and **prototype implementation**
for RIINA, a security-focused programming language where security properties
are mathematically guaranteed at compile time.

### 1.1 Directory Structure

```
/workspaces/proof/
├── CLAUDE.md                    ← THIS FILE (master instructions)
├── README.md                    ← Public repository README
├── PROGRESS.md                  ← Current progress tracker
├── SESSION_LOG.md               ← Session continuity log
│
├── 00_SETUP/                    ← Setup scripts and initialization
│   ├── SETUP_COMPLETE.marker    ← Created after successful setup
│   └── scripts/
│       ├── install_coq.sh       ← Coq 8.18.0 installation
│       ├── install_lean.sh      ← Lean 4.x installation
│       ├── install_rust.sh      ← Rust toolchain installation
│       └── verify_setup.sh      ← Verification script
│
├── 01_RESEARCH/                 ← Research track archive (READ-ONLY reference)
│   ├── ... (Domains A-Q)
│   ├── 18_DOMAIN_R_CERTIFIED_COMPILATION/  ← Track R: Translation Validation
│   ├── 19_DOMAIN_S_HARDWARE_CONTRACTS/     ← Track S: HW/SW Co-Verification
│   ├── 20_DOMAIN_T_HERMETIC_BUILD/         ← Track T: Binary Bootstrap
│   ├── 21_DOMAIN_U_RUNTIME_GUARDIAN/       ← Track U: Verified Micro-Hypervisor
│   ├── 22_DOMAIN_V_TERMINATION_GUARANTEES/ ← Track V: Termination Proofs
│   ├── 23_DOMAIN_W_VERIFIED_MEMORY/        ← Track W: Memory Safety
│   ├── 24_DOMAIN_X_CONCURRENCY_MODEL/      ← Track X: Concurrency
│   ├── 25_DOMAIN_Y_VERIFIED_STDLIB/        ← Track Y: Verified Library
│   ├── 26_DOMAIN_Z_DECLASSIFICATION_POLICY/← Track Z: Declassification
│   └── specs/bahasa/                       ← Bahasa Melayu syntax specs
│
├── 02_FORMAL/                   ← Track A: Formal proofs
│   ├── coq/                     ← Coq proofs (PRIMARY)
│   │   ├── _CoqProject          ← Coq project configuration
│   │   ├── Makefile             ← Build configuration
│   │   ├── foundations/         ← Core definitions
│   │   ├── type_system/         ← Type safety proofs
│   │   ├── effects/             ← Effect system proofs
│   │   └── properties/          ← Security properties
│   ├── lean/                    ← Lean 4 proofs (SECONDARY)
│   └── isabelle/                ← Isabelle proofs (TERTIARY)
│
├── 03_PROTO/                    ← Track B: Rust prototype
│   ├── Cargo.toml               ← Workspace configuration
│   └── crates/
│       ├── riina-lexer/         ← Lexer implementation
│       ├── riina-parser/        ← Parser implementation
│       ├── riina-types/         ← Type system implementation
│       └── riinac/              ← Compiler driver
│
├── 04_SPECS/                    ← Track C: Specifications
│   ├── language/                ← Language specifications
│   ├── effect_gate/             ← Effect gate specifications
│   └── products/                ← Product-specific specs
│
├── 05_TOOLING/                  ← Track F: Build tools & crypto
│   ├── Cargo.toml               ← Tooling workspace
│   ├── crates/
│   │   ├── riina-core/          ← Cryptographic primitives
│   │   ├── riina-build/         ← Build orchestrator
│   │   └── riina-verify/        ← Verification orchestrator
│   ├── tools/                   ← Standalone tools
│   ├── ada/                     ← Ada/SPARK sources
│   └── .github/workflows/       ← CI/CD configuration
│
├── 07_EXAMPLES/                 ← Example .rii files
│   ├── hello_dunia.rii          ← Hello World in RIINA
│   ├── pengesahan.rii           ← Authentication example
│   └── kripto.rii               ← Cryptography example
│
└── 06_COORDINATION/             ← Cross-track coordination
    ├── COORDINATION_LOG.md      ← Master coordination state
    ├── DEPENDENCY_GRAPH.md      ← Track dependencies
    └── DECISIONS.md             ← Architecture decisions
```

---

## 2. FIRST-TIME SETUP PROCEDURE

### 2.1 Prerequisites Check

Before ANY work, verify the environment:

```bash
# Check if setup is already complete
if [ -f "/workspaces/proof/00_SETUP/SETUP_COMPLETE.marker" ]; then
    echo "Setup already complete. Skip to Section 3."
else
    echo "First-time setup required. Continue with 2.2."
fi
```

### 2.2 Extract Archive (If Not Done)

If the repository is empty or only contains this CLAUDE.md:

```bash
cd /workspaces/proof

# Check if archive exists
if [ -f "RIINA_PROOF_REPOSITORY_COMPLETE.zip" ]; then
    unzip -o RIINA_PROOF_REPOSITORY_COMPLETE.zip
    echo "Archive extracted successfully"
else
    echo "ERROR: Archive not found. Request upload from user."
fi
```

### 2.3 Install Dependencies

Run the setup scripts in order:

```bash
cd /workspaces/proof/00_SETUP/scripts

# 1. Install Rust (required for tooling)
chmod +x install_rust.sh
./install_rust.sh

# 2. Install Coq (required for formal proofs)
chmod +x install_coq.sh
./install_coq.sh

# 3. Install Lean (optional, for secondary proofs)
chmod +x install_lean.sh
./install_lean.sh

# 4. Verify installation
chmod +x verify_setup.sh
./verify_setup.sh
```

### 2.4 Create Setup Marker

After successful setup:

```bash
echo "Setup completed: $(date -u +%Y-%m-%dT%H:%M:%SZ)" > /workspaces/proof/00_SETUP/SETUP_COMPLETE.marker
echo "Coq version: $(coqc --version | head -1)" >> /workspaces/proof/00_SETUP/SETUP_COMPLETE.marker
echo "Rust version: $(rustc --version)" >> /workspaces/proof/00_SETUP/SETUP_COMPLETE.marker
```

---

## 3. SESSION MANAGEMENT

### 3.1 At Session Start

ALWAYS execute these steps at the beginning of EVERY session:

```bash
cd /workspaces/proof

# 1. Pull latest changes
git pull origin main

# 2. Read progress state
cat PROGRESS.md

# 3. Read session log
tail -50 SESSION_LOG.md

# 4. Check coordination state
cat 06_COORDINATION/COORDINATION_LOG.md | head -100
```

### 3.2 During Session

Commit frequently (every 30 minutes or after verified change):

```bash
# After each verified change
git add -A
git commit -m "[TRACK_X] Description of change"
git push origin main
```

Update SESSION_LOG.md continuously:

```markdown
## Session: YYYY-MM-DD HH:MM UTC
Started: [file], [line/function]
Working on: [specific task]
Status: In progress
Blockers: [if any]
```

### 3.3 At Session End

ALWAYS execute these steps before ending:

```bash
cd /workspaces/proof

# 1. Update PROGRESS.md with checkpoint
# 2. Update SESSION_LOG.md with status

# 3. Commit all changes
git add -A
git commit -m "[SESSION END] Checkpoint at [specific location]"
git push origin main

# 4. Verify push succeeded
git status
```

---

## 4. TRACK-SPECIFIC INSTRUCTIONS

### 4.1 Track A: Formal Proofs (02_FORMAL/)

#### Priority Order
1. **Coq** (PRIMARY) — All core proofs must be in Coq first
2. **Lean** (SECONDARY) — Port verified Coq proofs to Lean
3. **Isabelle** (TERTIARY) — Port for additional verification

#### Coq Workflow

```bash
cd /workspaces/proof/02_FORMAL/coq

# Build all proofs
make

# Build specific file
coqc -Q . RIINA foundations/Syntax.v

# Check for admits (FORBIDDEN in final)
grep -r "Admitted\|admit\|todo" *.v
```

#### Proof Standards

- **NO `Admitted.`** — Every proof must be complete
- **NO `admit.`** — No tactical admits allowed
- **NO `Axiom` without justification** — Document in ASSUMPTIONS.md
- **All three provers must agree** — Cross-verify critical lemmas

#### Current Priority (Track A)

1. `foundations/Syntax.v` — Core syntax definitions
2. `foundations/Semantics.v` — Operational semantics
3. `type_system/Typing.v` — Typing rules
4. `type_system/Progress.v` — Progress theorem
5. `type_system/Preservation.v` — Preservation theorem
6. `effects/EffectSystem.v` — Effect type system
7. `properties/TypeSafety.v` — Type safety composition
8. `properties/NonInterference.v` — Security property

### 4.2 Track B: Prototype (03_PROTO/)

#### Rust Workflow

```bash
cd /workspaces/proof/03_PROTO

# Build
cargo build --all

# Test
cargo test --all

# Lint
cargo clippy -- -D warnings

# Format
cargo fmt --check
```

#### Implementation Order

1. `riina-lexer/` — Tokenizer (Bahasa Melayu keywords)
2. `riina-parser/` — AST construction
3. `riina-types/` — Type checker
4. `riinac/` — Compiler driver

#### Coordination with Track A

- Lexer tokens MUST match `foundations/Syntax.v` definitions
- Parser AST MUST match `foundations/Syntax.v` types
- Type checker MUST implement rules from `type_system/Typing.v`

### 4.3 Track F: Tooling (05_TOOLING/)

#### Current Status

- ✅ Build system complete
- ✅ CI/CD complete
- ✅ Symmetric crypto complete
- 🟡 Asymmetric crypto interface only (X25519, Ed25519, ML-KEM, ML-DSA)

#### Remaining Work

```bash
cd /workspaces/proof/05_TOOLING/crates/riina-core/src/crypto

# Files needing implementation:
# - x25519.rs (Montgomery ladder)
# - ed25519.rs (Edwards curve)
# - ml_kem.rs (NTT, SHAKE)
# - ml_dsa.rs (NTT, rejection sampling)
```

### 4.4 Zero-Trust Tracks (R, S, T, U)

- **Track R (Certified Compilation):** Verify binary equivalence.
- **Track S (Hardware Contracts):** Model CPU side-channels.
- **Track T (Hermetic Build):** Bootstrap from `hex0`.
- **Track U (Runtime Guardian):** Verified micro-hypervisor.

### 4.5 Completeness Tracks (V, W, X, Y, Z)

- **Track V (Termination Guarantees):** Sized types, strong normalization.
- **Track W (Verified Memory):** Separation logic, verified allocator.
- **Track X (Concurrency Model):** Session types, data-race freedom.
- **Track Y (Verified Stdlib):** Proven standard library functions.
- **Track Z (Declassification Policy):** Robust declassification with budgets.

*(See 01_RESEARCH for definitive plans)*

---

## 5. VERIFICATION REQUIREMENTS

### 5.1 Before ANY Commit

```bash
# For Coq changes
cd /workspaces/proof/02_FORMAL/coq
make clean && make
grep -r "Admitted" *.v  # MUST be empty

# For Rust changes
cd /workspaces/proof/03_PROTO
cargo test --all
cargo clippy -- -D warnings

# For Tooling changes
cd /workspaces/proof/05_TOOLING
cargo test --all
cargo clippy -- -D warnings
```

### 5.2 Commit Message Format

```
[TRACK_X] [TYPE] Brief description

TYPE:
- PROOF: New proof or proof completion
- IMPL: Implementation code
- FIX: Bug fix
- DOCS: Documentation
- REFACTOR: Code restructuring
- RENAME: TERAS → RIINA migration

Examples:
[TRACK_A] PROOF: Complete Progress lemma for function application
[TRACK_B] IMPL: Lexer tokenizes Bahasa Melayu keywords
[TRACK_F] FIX: Constant-time comparison in HMAC verify
[ALL] RENAME: Migrate TERAS references to RIINA
```

---

## 6. FORBIDDEN ACTIONS

### 6.1 NEVER Do These

1. **NEVER commit code that doesn't compile**
2. **NEVER commit Coq proofs with `Admitted`**
3. **NEVER commit failing tests**
4. **NEVER use `unsafe` in Rust without documented justification**
5. **NEVER add third-party crypto dependencies**
6. **NEVER skip verification before commit**
7. **NEVER force push to main**
8. **NEVER modify 01_RESEARCH/** (read-only reference, except for new tracks)

### 6.2 ALWAYS Do These

1. **ALWAYS read PROGRESS.md at session start**
2. **ALWAYS update SESSION_LOG.md during work**
3. **ALWAYS run verification before commit**
4. **ALWAYS commit and push frequently**
5. **ALWAYS document assumptions and axioms**
6. **ALWAYS cross-reference Track A proofs with Track B implementations**
7. **ALWAYS use Bahasa Melayu keywords in .rii example files**

---

## 7. RECOVERY PROCEDURES

### 7.1 If Coq Proof Stuck

```bash
# 1. Save current state
cp file.v file.v.stuck

# 2. Check proof context
Print Assumptions lemma_name.

# 3. Try different approach or add intermediate lemma

# 4. If truly stuck, document in PROGRESS.md and move to next task
```

### 7.2 If Build Broken

```bash
# 1. Check last working commit
git log --oneline -10

# 2. Identify breaking change
git diff HEAD~1

# 3. Revert if necessary
git revert HEAD

# 4. Fix and recommit
```

### 7.3 If Session Disconnected

```bash
# 1. On reconnect, check git status
git status

# 2. Check for uncommitted work
git diff

# 3. Commit if valid, discard if broken
git add -A && git commit -m "[RECOVERY] Uncommitted work from disconnect"

# 4. Continue from PROGRESS.md checkpoint
```

---

## 8. CURRENT PRIORITIES

### Phase 0: Foundation Verification (Current Phase - 85% Complete)

1. **Fix CumulativeMonotone.v TFn case** — Step monotonicity proof
2. **Complete step monotonicity proof** — Required for axiom elimination
3. **Verify all foundations compile** — Zero compilation errors

### Phase 1: Axiom Elimination (19 → 0) — Next Phase

| Priority | Axiom Category | Count | Target |
|----------|----------------|-------|--------|
| P0 | Semantic typing axioms | 4 | Prove or eliminate |
| P0 | Step-up axioms | 3 | Prove via step-indexed structure |
| P1 | Step-1 termination axioms | 7 | Extract from semantics |
| P1 | Higher-order conversion | 2 | Prove type compatibility |
| P2 | Higher-order Kripke | 2 | Prove world monotonicity |
| P2 | Application | 1 | Complete application proof |

### Phase 2-6: Future Phases

- **Phase 2**: Core Properties (~375 theorems)
- **Phase 3**: Domain Properties (~2,570 theorems)
- **Phase 4**: Implementation Verification
- **Phase 5**: Multi-Prover Verification (Coq + Lean + Isabelle)
- **Phase 6**: Production Hardening

**See `01_RESEARCH/MASTER_ATTACK_PLAN_COMPLETE.md` for full phase definitions.**

---

## 9. REFERENCE MATERIALS

### 9.1 Key Specifications (in 01_RESEARCH/)

**Authoritative Planning Documents:**
- `MASTER_ATTACK_PLAN_COMPLETE.md` — **Definitive 6-phase attack plan**
- `MASTER_THREAT_MODEL.md` — All 350+ threat categories
- `TRACEABILITY_MATRIX.md` — Threat → Proof mapping
- `COMPLETE_GAP_ANALYSIS.md` — Consolidated gap analysis

**Gap Analysis Documents:**
- `NETWORKING_COMPLETE_ENUMERATION.md` — 439 protocols, 449 threats
- `FULLSTACK_UIUX_REVOLUTIONARY.md` — 627 technologies, 432 threats
- `DATA_STORAGE_COMPLETE_ENUMERATION.md` — 77 types, 312 threats
- `PERFORMANCE_ABSOLUTE_SUPREMACY.md` — 127 techniques, proven bounds
- `REMAINING_CONCERNS_ZERO_AXIOMS.md` — 74 post-axiom concerns

**Language Specifications:**
- `RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md` — **Bahasa Melayu syntax specification**
- `CTSS_v1_0_1.md` — Core Type System Specification
- `RIINA-LANG-LEXER-SPEC_v1_0_0.md` — Lexer specification
- `RIINA-LANG-GRAMMAR-*.md` — Grammar specifications
- `RIINA-LANG-AST_v1_0_0.md` — AST specification

**Track Foundation Documents:**
- `RESEARCH_R01_FOUNDATION.md` — Translation Validation
- `RESEARCH_S01_FOUNDATION.md` — Hardware Contracts
- `RESEARCH_T01_FOUNDATION.md` — Hermetic Bootstrap
- `RESEARCH_U01_FOUNDATION.md` — Runtime Guardian
- `RESEARCH_V01_FOUNDATION.md` — Termination Guarantees
- `RESEARCH_W01_FOUNDATION.md` — Verified Memory
- `RESEARCH_X01_FOUNDATION.md` — Concurrency Model
- `RESEARCH_Y01_FOUNDATION.md` — Verified Stdlib
- `RESEARCH_Z01_FOUNDATION.md` — Declassification Policy

### 9.2 Bahasa Melayu Quick Reference

| Bahasa Melayu | English | Usage |
|---------------|---------|-------|
| `fungsi` | fn | Function declaration |
| `biar` | let | Variable binding |
| `ubah` | mut | Mutable modifier |
| `tetap` | const | Constant |
| `kalau` | if | Conditional |
| `lain` | else | Alternative |
| `untuk` | for | For loop |
| `selagi` | while | While loop |
| `ulang` | loop | Infinite loop |
| `pulang` | return | Return value |
| `padan` | match | Pattern match |
| `betul` | true | True value |
| `salah` | false | False value |
| `rahsia` | secret | Secret type |
| `dedah` | declassify | Declassify |
| `kesan` | effect | Effect annotation |
| `bersih` | pure | Pure effect |

---

## 10. CONTACT AND ESCALATION

If blocked or uncertain:

1. **Document the blocker** in PROGRESS.md
2. **Search 01_RESEARCH/** for relevant guidance
3. **Check 06_COORDINATION/DECISIONS.md** for prior decisions
4. **If still blocked**: Note in SESSION_LOG.md and proceed with alternate task

---

## 11. LEGACY NAME MIGRATION

The language was previously named "TERAS". All references are being migrated to "RIINA".

| Old Name | New Name |
|----------|----------|
| TERAS | RIINA |
| TERAS-LANG | RIINA |
| teras-lang-* | riina-* |
| .teras | .rii |
| terasc | riinac |

When encountering old references, update them to the new naming.

---

*This CLAUDE.md follows ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE principles.*

*RIINA: Rigorous Immutable Integrity No-attack Assured*

*Reena. Isaac. Imaan. Forever in code.*

*"Security proven. Family driven."*

*Last updated: 2026-01-18*
