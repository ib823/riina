# CLAUDE.md — TERAS Proof Repository

## CRITICAL: READ THIS ENTIRE FILE BEFORE ANY ACTION

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║                                                                                  ║
║                    TERAS PROOF REPOSITORY — CLAUDE CODE GUIDE                    ║
║                                                                                  ║
║  Repository: https://github.com/ib823/proof                                      ║
║  Purpose: Formal proofs and prototype for TERAS-LANG                             ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS               ║
║                                                                                  ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## 1. REPOSITORY OVERVIEW

This repository contains the **formal foundations** and **prototype implementation** 
for TERAS-LANG, a security-focused programming language where security properties 
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
│   └── [132 research files]
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
│       ├── teras-lang-lexer/    ← Lexer implementation
│       ├── teras-lang-parser/   ← Parser implementation
│       ├── teras-lang-types/    ← Type system implementation
│       └── terasc/              ← Compiler driver
│
├── 04_SPECS/                    ← Track C: Specifications
│   ├── language/                ← Language specifications
│   ├── effect_gate/             ← Effect gate specifications
│   └── products/                ← Product-specific specs
│
├── 05_TOOLING/                  ← Track F: Build tools & crypto
│   ├── Cargo.toml               ← Tooling workspace
│   ├── crates/
│   │   ├── teras-core/          ← Cryptographic primitives
│   │   ├── teras-build/         ← Build orchestrator
│   │   └── teras-verify/        ← Verification orchestrator
│   ├── tools/                   ← Standalone tools
│   ├── ada/                     ← Ada/SPARK sources
│   └── .github/workflows/       ← CI/CD configuration
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
if [ -f "TERAS_PROOF_REPOSITORY_COMPLETE.zip" ]; then
    unzip -o TERAS_PROOF_REPOSITORY_COMPLETE.zip
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
coqc -Q . TERAS foundations/Syntax.v

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

1. `teras-lang-lexer/` — Tokenizer
2. `teras-lang-parser/` — AST construction
3. `teras-lang-types/` — Type checker
4. `terasc/` — Compiler driver

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
cd /workspaces/proof/05_TOOLING/crates/teras-core/src/crypto

# Files needing implementation:
# - x25519.rs (Montgomery ladder)
# - ed25519.rs (Edwards curve)
# - ml_kem.rs (NTT, SHAKE)
# - ml_dsa.rs (NTT, rejection sampling)
```

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

Examples:
[TRACK_A] PROOF: Complete Progress lemma for function application
[TRACK_B] IMPL: Lexer tokenizes all keyword tokens
[TRACK_F] FIX: Constant-time comparison in HMAC verify
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
8. **NEVER modify 01_RESEARCH/** (read-only reference)

### 6.2 ALWAYS Do These

1. **ALWAYS read PROGRESS.md at session start**
2. **ALWAYS update SESSION_LOG.md during work**
3. **ALWAYS run verification before commit**
4. **ALWAYS commit and push frequently**
5. **ALWAYS document assumptions and axioms**
6. **ALWAYS cross-reference Track A proofs with Track B implementations**

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

### Immediate (This Session)

1. **Verify repository structure** — Ensure all directories exist
2. **Run setup scripts** — Install Coq, Rust, Lean
3. **Build existing code** — Verify everything compiles
4. **Start Track A** — Begin `foundations/Syntax.v`

### Short-term (This Week)

1. Complete `foundations/Syntax.v` and `foundations/Semantics.v`
2. Begin `type_system/Typing.v`
3. Start Track B lexer implementation

### Medium-term (This Month)

1. Complete Progress and Preservation theorems
2. Complete lexer and parser
3. Begin type checker implementation

---

## 9. REFERENCE MATERIALS

### 9.1 Key Specifications (in 01_RESEARCH/)

- `teras-lang-foundation-v0_3_1.md` — Language foundation
- `CTSS_v1_0_1.md` — Core Type System Specification
- `TERAS-LANG-LEXER-SPEC_v1_0_0.md` — Lexer specification
- `TERAS-LANG-GRAMMAR-*.md` — Grammar specifications
- `TERAS-LANG-AST_v1_0_0.md` — AST specification

### 9.2 Architecture Documents

- `TERAS_MASTER_ARCHITECTURE_v3_2_2_CONSOLIDATED.md` — Master architecture
- `TERAS_DEFINITIVE_PLAN_v1_0_0.md` — Development roadmap

---

## 10. CONTACT AND ESCALATION

If blocked or uncertain:

1. **Document the blocker** in PROGRESS.md
2. **Search 01_RESEARCH/** for relevant guidance
3. **Check 06_COORDINATION/DECISIONS.md** for prior decisions
4. **If still blocked**: Note in SESSION_LOG.md and proceed with alternate task

---

*This CLAUDE.md follows ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS principles.*
*Last updated: 2026-01-11*
