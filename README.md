# RIINA™

**Formally verified programming language.**

***Formal claims, verification status, and gaps published openly.***

Security properties in RIINA are tracked as a mix of machine-checked proofs, compiler checks, and explicitly documented gaps. The current verified state lives in `RIINA_MASTER_PLAN.md` Part 2.

**[Get Started in 10 Minutes](docs/guide/GETTING_STARTED.md)** | **[Writing Secure RIINA](docs/guide/WRITING_SECURE_RIINA.md)** | **[Try the Playground](https://ib823.github.io/riina/#playground)** | **[RIINA vs Rust](07_EXAMPLES/showcase/riina_vs_rust/)** | **[Website](https://ib823.github.io/riina/)**

```
  ██████╗ ██╗██╗███╗   ██╗ █████╗
  ██╔══██╗██║██║████╗  ██║██╔══██╗
  ██████╔╝██║██║██╔██╗ ██║███████║
  ██╔══██╗██║██║██║╚██╗██║██╔══██║
  ██║  ██║██║██║██║ ╚████║██║  ██║
  ╚═╝  ╚═╝╚═╝╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝

  Rigorous Immutable Invariant, No Assumptions
```

**[Bahasa Melayu](docs/i18n/README_ms.md)** | **[中文](docs/i18n/README_zh.md)**

> **Write with vibes. Ship with proofs.**

---

## AI-Native Language

RIINA is a programming language that combines formal verification work with **AI-native** tooling. The repository contains machine-checked proofs, active compiler checks, and explicitly documented verification gaps, and it is designed from the ground up for AI agents to read, write, and reason about.

**AI-Writability: a design goal, not a benchmarked score.** Consistent Bahasa Melayu keywords, minimal syntax, strong types, and deterministic compilation are intended to make RIINA easy for AI agents to read and write. (Any single-number "writability score" is an internal self-assessment, not an externally validated metric.)

AI agents: See [llms.txt](llms.txt) for a machine-readable language reference.

### For AI Agents

RIINA provides first-class support for AI-assisted development:

- **Programmatic compilation:** `riinac check --json --stdin` accepts source on stdin and returns structured JSON diagnostics
- **Full machine reference:** [llms-full.txt](llms-full.txt) contains the complete language specification, type system, and effect system in a single file
- **Stdlib API reference:** [docs/api/STDLIB.md](docs/api/STDLIB.md) — every builtin and its type signature, generated from the compiler's own registry (drift-guarded by a test)
- **Proof guide:** [docs/guide/PROOF_GUIDE.md](docs/guide/PROOF_GUIDE.md) — how to read, build, and extend the Coq lane
- **Code patterns:** [07_EXAMPLES/](07_EXAMPLES/) contains 130+ annotated examples across 10 categories (security, effects, compliance, design patterns, FFI, and more)
- **IDE integration:** [.cursorrules](.cursorrules) and [.clinerules](.clinerules) provide pre-configured rules for Cursor and Cline; [.github/copilot-instructions.md](.github/copilot-instructions.md) provides GitHub Copilot context

---

## What is RIINA?

RIINA is a programming language with a machine-checked Coq proof corpus and a security-oriented compiler. **Coq is the only fully mechanized lane.** The repository also contains Lean, Isabelle, F\*, TLA+, Alloy, and SMT trees, but these are machine-*generated* from the Coq sources and are mostly unproven placeholders or small smoke artifacts — they are tracked honestly with per-lane claim levels in `website/public/metrics.json`, not presented as independent verification. The shipped compiler enforces core type/effect checks today; broader proof coverage and known gaps are tracked explicitly in `RIINA_MASTER_PLAN.md` Part 2.

Most languages ask you to *trust* that your code is secure. RIINA asks you to *verify* it.

| What RIINA has today | Current status |
|---|---|
| Type safety theorems | Machine-checked in Coq; Rust checker active |
| Effect algebra and gate model | Machine-checked in Coq; compiler tracks effects |
| Information-flow / non-interference development | Machine-checked in Coq; compiler enforcement partial |
| Declassification model | Machine-checked in Coq; shipped compiler/runtime alignment still in progress |
| Termination and memory models | Formalized in the Coq corpus |

These are real formal artifacts that compile today, but not every theorem is wired end-to-end into the shipped compiler yet.

---

## Why RIINA?

**If you write software where security matters, RIINA is for you.**

- Building a payments system? RIINA gives you explicit secrets, effects, and auditable formal models.
- Building healthcare software? RIINA gives you language support for confidentiality-focused design and verification.
- Building infrastructure? RIINA gives you explicit effects, proof artifacts, and a narrow trusted surface.
- Building anything? RIINA is aimed at zero-trust software, but current compiler-enforced coverage is narrower than the full proof corpus.

RIINA doesn't care what industry you're in. If you care about getting security right — provably, permanently, without hoping your tests caught everything — RIINA is the tool.

### What makes RIINA different from every other language

| Feature | RIINA | Rust | Haskell | Ada/SPARK |
|---------|-------|------|---------|-----------|
| Memory safety | Formal model; compiler/runtime alignment in progress | Borrow checker (no proof) | GC | Proven (SPARK subset) |
| Information flow control | Formal model; compiler enforcement partial | None | None | None |
| Effect tracking | Implemented + formal model | None | Monads (no proof) | None |
| Type safety | Formalized in Coq; checker active | Tested | Tested | Proven (SPARK subset) |
| Zero external dependencies | Yes (compiler, crypto, stdlib) | No | No | No |
| Formal proof corpus in repo | Yes — 12,613 Coq Qed (mechanized); other lanes generated, see below | No | No | Partial |
| Multi-prover work | Coq mechanized; 9 other lanes are generated/smoke-only (not independent verification) | No | No | No |
| Session-typed actors | Yes (JALINAN: pelaku, lahir, hantar, terima) | No | No | No |
| Bahasa Melayu native syntax | Yes | No | No | No |

---

**Website:** [ib823.github.io/riina](https://ib823.github.io/riina/)

---

## Quick Start

### Install

```bash
git clone https://github.com/ib823/riina.git
cd riina/03_PROTO
cargo build --release
```

The compiler binary is `riinac`. Zero external dependencies — everything is built from source.

**Alternative install methods:**

```bash
# Docker (build from source)
docker build -t riina .
docker run --rm riina check myfile.rii

# Nix
nix run github:ib823/riina

# Portable installer (builds from source)
bash scripts/install.sh
```

For the pinned Isabelle/F* toolchains and TLA+/Alloy formal jars used by repo verification on a fresh clone:

```bash
bash scripts/provision-smoke-toolchains.sh
```

### Hello World

Create `hello.rii`:

```riina
// Hello World in RIINA
// Keywords are in Bahasa Melayu (Malaysian Malay)
// (This example type-checks and runs on the shipped compiler.)

fungsi utama() -> Teks kesan Sistem {
    biar mesej = "Selamat datang ke RIINA!";
    cetak(mesej);          // 'cetak' prints; its effect is 'Sistem' (System)
    mesej                  // trailing expression is the return value (no 'pulang;')
}
```

```bash
riinac check hello.rii    # Type-check and verify
riinac run hello.rii      # Run directly
riinac build hello.rii    # Compile to native binary via C
```

### Security in Action (illustrative — intended model)

> The snippet below shows the *intended* information-flow model. It uses syntax
> (`kesan Crypto`, `pulang …;`) that the shipped parser does not yet fully accept;
> treat it as a design illustration, not a runnable example.

```riina
// RIINA prevents information leaks at compile time

fungsi proses_pembayaran(kad: Rahsia<Teks>, jumlah: Nombor) -> Teks kesan Crypto {
    // 'kad' is Secret in the language model; compiler/runtime alignment is ongoing

    biar hash = sha256(kad);           // OK: crypto on secret data
    biar resit = "Jumlah: " + ke_teks(jumlah);  // OK: amount is public

    // cetakln(kad);                   // COMPILE ERROR: secret data in IO effect
    // pulang kad;                     // COMPILE ERROR: secret in public return

    pulang resit;                      // OK: only public data returned
}
```

This is the intended security model. Current compiler enforcement is narrower than the full proof corpus; see `RIINA_MASTER_PLAN.md` Part 2 for the verified state and current gaps.

### Effect System (illustrative — intended model)

> As above, this illustrates the intended effect syntax; `kesan IO` and `pulang …;`
> are not accepted by the shipped parser yet. Valid effect names today include
> `Bersih`, `Tulis`, `Baca`, `Kripto`, `Rangkaian`, `Rawak`, `Masa`, `Sistem`.

```riina
// Effects are explicit in the language and formal model

fungsi baca_config(laluan: Teks) -> Teks kesan IO {
    biar kandungan = fail_baca(laluan);
    pulang kandungan;
}

fungsi kira_cukai(pendapatan: Nombor) -> Nombor kesan Bersih {
    // This function is intended to remain pure
    // The effect annotation documents that contract
    pulang pendapatan * 0.06;
}

// Dependencies cannot escalate effects without explicit permission
// A crypto library cannot secretly open network connections
```

---

## Bahasa Melayu Syntax

RIINA uses **Bahasa Melayu** (Malaysian Malay) keywords — the first systems programming language with native Southeast Asian syntax.

| RIINA | English | Example |
|-------|---------|---------|
| `fungsi` | fn | `fungsi tambah(x: Nombor) -> Nombor` |
| `biar` | let | `biar nama = "Ahmad";` |
| `kalau` | if | `kalau x > 0 { ... }` |
| `lain` | else | `lain { ... }` |
| `untuk` | for | `untuk x dalam senarai { ... }` |
| `selagi` | while | `selagi aktif { ... }` |
| `pulang` | return | `pulang hasil;` |
| `padan` | match | `padan nilai { ... }` |
| `rahsia` | secret | `biar kunci: Rahsia<Teks>` |
| `dedah` | declassify | `dedah(nilai)` |
| `kesan` | effect | `kesan IO` |
| `bersih` | pure | `kesan Bersih` |
| `betul` / `salah` | true / false | Boolean values |
| `ubah` | mut | `biar ubah x = 0;` |

You don't need to speak Malay to use RIINA. The keywords are consistent, short, and learnable in an afternoon. But if you *do* speak Malay, this is the first language that speaks your language.

---

## What's Been Built

This is not a whitepaper. This is working software.

### Formal Proofs — Current Verified State

| Prover | What is actually proven | Notes |
|--------|-------------------------|-------|
| **Rocq 9.2** (Primary) | 12,613 Qed in the active build; 0 Admitted, 0 `Axiom`, 0 Abort | The only fully mechanized lane. Caveat: the active build also contains **30 `Parameter` declarations** (logically equivalent to axioms in Coq), the propositional ones modelling the trusted hardware interface — see `PROOF_STATUS.md` |
| **Lean 4** | **215 theorems across 7 files** actually elaborate (measured 2026-06-01, Lean 4.16.0; self-contained `Domains/Verified*` files — the core type-safety files do **not** compile) | The other ~12,360 declarations are transpiler-generated with placeholder tactics (`simp_all [Bool.and_eq_true]`, in 304 files) that do **not** prove their goals; `lake build RIINA` passes only because its default target is a 0-theorem shim. See `02_FORMAL/lean/COMPILATION_STATUS.md`. Claim level: **generated**, not mechanized |
| **Isabelle/HOL** | `RIINA_CORE` smoke session — **unverified** (`smokeBuildOk:false`; toolchain download 403 here) | 368 `.thy` files total, machine-generated from Coq; remainder unverified generated corpora |
| **F\*** | Effectively nothing | 315 `.fst` files, but **`admit()` appears ~12,010 times** — nearly every lemma body is `admit ()`. Generated, not proven |
| **TLA+ / Alloy / SMT** | 1 small hand-written smoke artifact each | Remainder are generated per-domain mirrors; only a handful have runnable configs |
| **Verus / Kani / TV** | None | Explicitly quarantined (`quarantined: true` in metrics.json); generated stubs |

**Honest scope:**
- **Only the Coq active lane constitutes real machine-checked verification** (and even it rests on 30 `Parameter` assumptions).
- The Lean, Isabelle, F\*, TLA+, Alloy, SMT, Verus, Kani, and TV trees were produced by `scripts/generate-full-stack.py` / `generate-multiprover.py` fanning the Coq tree into other syntaxes. They inflate file/theorem counts but are stubbed (`admit`/placeholder tactics) or are single small smoke artifacts — **not** nine additional independent verifications.
- Core Coq theorems cover foundations, type safety, effects, non-interference, declassification, and termination. Many *domain* Coq files are formal models/specifications, not compiler-enforced guarantees.
- See `website/public/metrics.json` for per-lane claim levels (the authoritative source of truth).

### Compiler & Toolchain (Rust)

| Metric | Value |
|--------|-------|
| Rust crates | 19 proto + 5 tooling = 24 |
| Test count | 2,479 proto + 248 tooling = 2,727 (all passing) |
| External dependencies | **0** at runtime |
| Lines of Rust | ~73,500 (proto) |
| Standard library builtins | 88 across 9 modules |

**Crates:**

| Crate | Purpose |
|-------|---------|
| `riinac` | Compiler driver — check, run, build, emit-c, emit-ir, repl, fmt, doc, lsp, verify, pkg |
| `riina-lexer` | Tokenizer with 70+ bilingual keywords |
| `riina-parser` | AST construction |
| `riina-types` | Type system definitions (22 types, 17 effects, 6 security levels) |
| `riina-typechecker` | Type inference and checking |
| `riina-codegen` | IR lowering, C/WASM/mobile code generation, interpreter, FFI |
| `riina-wasm` | WASM playground library (in-browser compiler via cdylib) |
| `riina-fmt` | Code formatter |
| `riina-lsp` | Language Server Protocol (VS Code integration) |
| `riina-doc` | HTML documentation generator |
| `riina-pkg` | Package manager (SemVer resolution, SHA-256 integrity, effect escalation checking) |
| `riina-arena` | Memory arena allocator |
| `riina-span` | Source location tracking |
| `riina-symbols` | String interning |
| `riina-compliance` | Industry compliance validation (15 profiles, audit report generator) |

### Developer Tools

- **VS Code extension** — Syntax highlighting, 12 code snippets, LSP integration
- **Formatter** — `riinac fmt` for consistent code style
- **Doc generator** — `riinac doc` produces HTML documentation
- **LSP server** — Diagnostics, hover info, keyword completion
- **Package manager** — `riinac pkg init/add/remove/lock/build/publish/list/tree/clean`
- **Verification gate** — `riinac verify --fast` (zero-trust: runs tests, clippy, Coq audit)
- **Docker image** — Multi-stage build, ~85MB runtime image
- **Nix flake** — `nix run github:ib823/riina` or `nix develop` for full dev shell
- **Release scripts** — `scripts/release.sh` (one-command release: bump, tag, tarball, GitHub Release, deploy website), `scripts/bump-version.sh`, `scripts/install.sh`
- **Website** — 15-page site at [ib823.github.io/riina](https://ib823.github.io/riina/) — includes "Why Proof" executive page, 15 industry verticals, Releases page; deployed via `scripts/deploy-website.sh`
- **REPL** — Interactive mode for experimentation

### Example Programs

155 example `.rii` files across 18 category directories (security, effects, compliance, design patterns, FFI, AI context, JALINAN, showcase, and more).

> **Parser-support caveat (honest):** Many of these examples — including most of `00_basics/` — use a multi-statement block-body function form that the *shipped* parser does not yet accept; only ~19 currently pass `riinac check`. They document the intended language surface. See [`07_EXAMPLES/README.md`](07_EXAMPLES/README.md) for exactly which forms compile today and a list of the verified-working examples.

### Cryptographic Tooling

The `05_TOOLING/` workspace contains 35,000+ lines of hand-written cryptographic primitives:

- **Symmetric:** AES-256, SHA-256 (FIPS 180-4), HMAC, ChaCha20-Poly1305
- **Asymmetric:** X25519, Ed25519 (interfaces + partial implementations)
- **Post-quantum:** **ML-KEM-768 — ✅ FIPS 203 compliant** (byte-exact vs authentic NIST ACVP keyGen + encapDecap) and **ML-DSA-65 — ✅ FIPS 204 compliant** (byte/behaviour-exact vs NIST ACVP keyGen + sigGen + sigVer). Hand-rolled, zero external crypto deps — see `reports/precrypto_audit_secondmodel.md`
- **Zero external crypto dependencies** — everything auditable from source

---

## Repository Structure

```
riina/
├── 02_FORMAL/coq/         317 Coq proof files (277 active)
│   ├── foundations/        Core language semantics
│   ├── type_system/        Progress, Preservation, Type Safety
│   ├── properties/         Non-Interference, Declassification, Composition
│   ├── effects/            Effect algebra and gate proofs
│   ├── domains/            201 domain-specific proofs (R-Z, Σ, compliance)
│   ├── termination/        Strong normalization, sized types
│   ├── compliance/         DO-178C, ISO-26262, Common Criteria models
│   └── Industries/         Regulatory/domain formal models
│
├── 02_FORMAL/lean/          Lean 4 (generated from Coq; 215 thms across 7 files elaborate, rest placeholder tactics)
│   └── RIINA/               See COMPILATION_STATUS.md for the honest per-file state
│
├── 02_FORMAL/isabelle/      Isabelle/HOL (368 .thy, generated; smoke theory unverified)
├── 02_FORMAL/tlaplus/       TLA+ (317 .tla, generated; 1 smoke spec TLC-checked)
│   └── ...                  (F*, alloy, smt, verus, kani, tv: generated/quarantined — see metrics.json)
│
├── 03_PROTO/               Rust compiler (19 crates, 2,479 tests, 0 deps)
│   └── crates/
│       ├── riinac/         Compiler driver (11 subcommands)
│       ├── riina-lexer/    Tokenizer
│       ├── riina-parser/   Parser
│       ├── riina-types/    Type system
│       ├── riina-typechecker/
│       ├── riina-codegen/  IR + C backend + interpreter
│       ├── riina-pkg/      Package manager
│       ├── riina-fmt/      Formatter
│       ├── riina-lsp/      Language server
│       ├── riina-doc/      Doc generator
│       ├── riina-arena/    Memory allocator
│       ├── riina-span/     Source spans
│       ├── riina-symbols/  String interning
│       └── riina-compliance/ Compliance profile validator
│
├── 04_SPECS/               Language specifications, compliance specs
├── 05_TOOLING/             Crypto primitives, build system (35K lines Rust)
├── 07_EXAMPLES/            155 example .rii files
├── docs/                   Enterprise docs, multilingual READMEs
├── VERSION                 Semver source of truth (0.3.0)
├── CHANGELOG.md            Public-facing changelog
├── website/                15-page Vite/React website (Why Proof, Enterprise, Playground, etc.)
├── scripts/                Build, install, release, deploy, sync scripts
└── riina-vscode/           VS Code extension
```

---

## Research Scope

Every research track in `01_RESEARCH/` (55 domains, A through AJ, plus Greek letter tracks) has corresponding Coq proofs in the active build. 100% coverage, verified by audit.

| Track | Domain | Coq Proofs | Status |
|-------|--------|-----------|--------|
| A | Core type system, non-interference | 55 files (38K lines) | Proven |
| R | Certified compilation (translation validation) | 1 file (955 lines) | Proven |
| S | Hardware contracts (CPU side-channel models) | 1 file (560 lines) | Proven |
| T | Hermetic build (binary bootstrap verification) | 1 file (502 lines) | Proven |
| U | Runtime guardian (verified micro-hypervisor) | 1 file (604 lines) | Proven |
| V | Termination guarantees (strong normalization — recursion-free core; general recursion is type-safe but not normalizing, REQ-44) | 6 files (3K lines) | Proven (scoped) |
| W | Verified memory (separation logic) | 1 file (739 lines) | Proven |
| X | Concurrency (session types, data-race freedom) | 1 file (750 lines) | Proven |
| Y | Verified standard library | 1 file (780 lines) | Proven |
| Z | Declassification policy (budgets, robust) | 1 file (665 lines) | Proven |
| Σ | Verified persistent storage | 1 file (712 lines) | Proven |
| — | Industry compliance (15 jurisdictions) | 15 files (2K lines) | Proven |
| — | Domain security (timing, protocols, hardware, ...) | 183 files (76K lines) | Proven |
| Π | Verified performance (WCET, SIMD, lock-free) | 1 file (470 lines) | Proven |
| Δ | Verified distribution (Raft, BFT, CRDTs) | 1 file (500 lines) | Proven |
| Ω | Network defense (rate limiting, SYN cookies) | 1 file (530 lines) | Proven |
| Ψ | Operational security (Shamir, duress, dead man) | 1 file (560 lines) | Proven |
| L | FFI boundary safety, attack surface research | 1 file (17 Qed) | Proven |
| — | Mobile OS security (27 subsystems) | 27 files | Proven |
| — | Security foundations (boot, IOMMU, crypto) | 11 files | Proven |
| — | UI/UX accessibility and safety | 7 files | Proven |
| — | Capital markets (order matching, settlement) | 1 file (15 Qed) | Proven |
| — | Physical systems security (sensors, timing) | 1 file (16 Qed) | Proven |

---

## Current Status

**Build:** Passing.
**Verification:** 12,678 Coq Qed (compiled, 0 Admitted, 0 active axioms) — Coq is the only mechanized lane | 3365 Rust tests | the other prover trees are machine-generated (claim-level tracked, not independent verification)

| Area | Status |
|------|--------|
| Core compiler | Lexer/parser/typechecker/codegen/interpreter build and pass 2,727 tests; end-to-end security alignment still in progress |
| Standard library and tools | Implemented and test-covered |
| Formal verification | **Coq active lane is the only real machine-checked verification** (0 admit/0 axiom, modulo 30 `Parameter` assumptions). Lean/Isabelle/F*/TLA+/Alloy/SMT/Verus/Kani/TV are generated from Coq and are stubbed or single smoke artifacts — see `02_FORMAL/lean/COMPILATION_STATUS.md` and `metrics.json` |
| WASM/mobile backends | Present as scaffolding, not full production backends |
| Example programs | Many `.rii` examples use a block-statement syntax the shipped parser does not yet accept; see `07_EXAMPLES/README.md` for which forms currently compile |

### What's next

- **Compiler alignment:** Switch the shipped compiler path to the Coq-matching checker.
- **Axiom status:** Active Coq build has `Axiom = 0` and `Admitted = 0`, but carries **30 `Parameter` declarations** that are axioms in all but name (the propositional ones model the trusted hardware interface). These are the de-facto trusted assumptions; see `PROOF_STATUS.md`.
- **Multi-prover honesty (Gate D):** The 9 non-Coq prover trees are generated/stubbed. The roadmap is to either industrialize them or retract the "multi-prover" framing — tracked as REQ-29.
- **Compliance system:** `--compliance` exposes 15 profile names today, but only 3 have implemented heuristic checks so far.

---

## Security & Verification

RIINA uses compiler-integrated fast checks plus repository-level proof and audit flows. Not every formal verification lane runs inside `riinac` itself.

```bash
riinac verify --fast    # Tests + clippy (runs on every commit via pre-commit hook)
riinac verify --full    # + proof/tooling scans used by the repo hooks
```

**Git hooks** enforce verification automatically:
- **Pre-commit:** `riinac verify --fast` blocks commits with failing tests
- **Pre-push:** `riinac verify --full` + GPG signature check + secret detection + Trojan source scan

Install hooks: `./00_SETUP/scripts/install_hooks.sh`

**Deep verification** (manual, 7 levels): `bash 05_TOOLING/scripts/verify.sh [0-6]`

Verification is enforced automatically via git hooks installed by `./00_SETUP/scripts/install_hooks.sh`.

---

## Contributing

RIINA is source-available under the [RIINA Proprietary License](LICENSE).

```bash
# Clone and set up
git clone https://github.com/ib823/riina.git
cd riina

# Verify environment
bash 00_SETUP/scripts/verify_setup.sh

# Build compiler
cd 03_PROTO && cargo build --release -p riinac && cd ..

# Run all tests
cd 03_PROTO && cargo test --all && cd ..

# Check a .rii file
./03_PROTO/target/release/riinac check 07_EXAMPLES/hello_dunia.rii

# Run the REPL
./03_PROTO/target/release/riinac repl

# Run the verification gate
./03_PROTO/target/release/riinac verify --fast

# Install git hooks (recommended for contributors)
./00_SETUP/scripts/install_hooks.sh
```

Read [`CONTRIBUTING.md`](CONTRIBUTING.md) for detailed development instructions and coding standards.

---

## FAQ

**Is RIINA production-ready?**
The compiler, proofs, and toolchain are functional, but the project is not finished. The repository has passed Phase 4 of the master plan. You can write, compile, and run RIINA programs today, but end-to-end alignment between the shipped compiler and the full proof corpus is still in progress.

**Do I need to know Bahasa Melayu?**
No. The keywords are short and consistent — `fungsi` (function), `biar` (let), `kalau` (if), `pulang` (return). You'll learn them in minutes. A [cheatsheet](07_EXAMPLES/06_ai_context/RIINA_CHEATSHEET.md) is included.

**Do I need to understand Coq or formal verification?**
No. You can use the language without reading the proofs. Some guarantees are enforced directly by the compiler today, while the broader proof corpus is there for auditability and future compiler alignment.

**Why zero external dependencies?**
Trust. Every line of RIINA — compiler, crypto, standard library — is auditable from source. No supply chain attacks. No dependency confusion. No left-pad incidents.

**Why Bahasa Melayu?**
RIINA developed by Malaysians for the world. Programming languages have been English-only for 70 years. RIINA proves that formal verification and native-language syntax are not mutually exclusive. If a language can be proven correct, it can be proven correct in any language.

**How does RIINA compare to SPARK/Ada?**
SPARK ships mature compile-time proof integration for a well-defined Ada subset. RIINA's research scope includes information flow, effects, and declassification, but the shipped compiler is not yet aligned with the full proof corpus. Today the comparison is strongest at the level of formal ambition and proof inventory, not end-to-end enforcement maturity.

---

*RIINA — Rigorous Immutable Invariant, No Assumptions*

*Q.E.D. Aeternum.*

---

<sub>RIINA™ is a trademark of The RIINA Authors. First use in commerce: February 2026. All rights reserved.</sub>
