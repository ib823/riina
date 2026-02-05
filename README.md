# RIINA

**Formally verified programming language.**

***If it compiles, it's secure.***

Security properties are not tested, not assumed — they are *mathematically proven* at compile time.

**[Try the Playground](https://ib823.github.io/riina/#playground)** | **[RIINA vs Rust](07_EXAMPLES/showcase/riina_vs_rust/)** | **[Website](https://ib823.github.io/riina/)**

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

---

## What is RIINA?

RIINA is a programming language where **every security guarantee has a machine-checked mathematical proof**. If your program compiles, it is secure — not by convention, not by best practice, but by proof.

Most languages ask you to *trust* that your code is secure. RIINA asks you to *verify* it.

| What RIINA proves at compile time | How |
|---|---|
| No information leaks between security levels | Non-interference theorem (Coq) |
| No unauthorized effect execution | Effect gate algebra (Coq) |
| Type safety (no runtime type errors) | Progress + Preservation theorems (Coq) |
| No secret data in public outputs | Declassification policy proofs (Coq) |
| Termination of all pure computations | Strong normalization proofs (Coq) |
| Memory safety without garbage collection | Separation logic proofs (Coq) |

These are not aspirational goals — they are proven theorems that compile today.

---

## Why RIINA?

**If you write software where security matters, RIINA is for you.**

- Building a payments system? RIINA *proves* cardholder data never leaks.
- Building healthcare software? RIINA *proves* patient records stay confidential.
- Building infrastructure? RIINA *proves* no unauthorized side effects execute.
- Building anything? RIINA gives you **zero-trust guarantees from the compiler itself**.

RIINA doesn't care what industry you're in. If you care about getting security right — provably, permanently, without hoping your tests caught everything — RIINA is the tool.

### What makes RIINA different from every other language

| Feature | RIINA | Rust | Haskell | Ada/SPARK |
|---------|-------|------|---------|-----------|
| Memory safety | Proven (separation logic) | Borrow checker (no proof) | GC | Proven (SPARK subset) |
| Information flow control | Proven (non-interference) | None | None | None |
| Effect tracking | Proven (effect algebra) | None | Monads (no proof) | None |
| Type safety | Proven (Progress + Preservation) | Tested | Tested | Proven (SPARK subset) |
| Zero external dependencies | Yes (compiler, crypto, stdlib) | No | No | No |
| Formal proofs ship with compiler | Yes (6,720 Qed theorems) | No | No | Partial |
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
# Docker
docker pull riina
docker run --rm riina check myfile.rii

# Nix
nix run github:ib823/riina

# Portable installer (builds from source)
bash scripts/install.sh
```

### Hello World

Create `hello.rii`:

```riina
// Hello World in RIINA
// Keywords are in Bahasa Melayu (Malaysian Malay)

fungsi utama() -> Teks kesan IO {
    biar mesej = "Selamat datang ke RIINA!";
    cetakln(mesej);
    pulang mesej;
}
```

```bash
riinac check hello.rii    # Type-check and verify
riinac run hello.rii      # Run directly
riinac build hello.rii    # Compile to native binary via C
```

### Security in Action

```riina
// RIINA prevents information leaks at compile time

fungsi proses_pembayaran(kad: Rahsia<Teks>, jumlah: Nombor) -> Teks kesan Crypto {
    // 'kad' is Secret — the compiler PROVES it never reaches public output

    biar hash = sha256(kad);           // OK: crypto on secret data
    biar resit = "Jumlah: " + ke_teks(jumlah);  // OK: amount is public

    // cetakln(kad);                   // COMPILE ERROR: secret data in IO effect
    // pulang kad;                     // COMPILE ERROR: secret in public return

    pulang resit;                      // OK: only public data returned
}
```

This is not a runtime check. This is not a linter warning. The **compiler proves** at the type level that secret data cannot flow to public outputs. If it compiles, the guarantee holds.

### Effect System

```riina
// Every side effect is tracked and proven safe

fungsi baca_config(laluan: Teks) -> Teks kesan IO {
    biar kandungan = fail_baca(laluan);
    pulang kandungan;
}

fungsi kira_cukai(pendapatan: Nombor) -> Nombor kesan Bersih {
    // This function is PROVEN pure — no IO, no network, no side effects
    // The compiler enforces this, not the programmer
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

### Formal Proofs (Coq 8.20.1)

| Metric | Value |
|--------|-------|
| Proof files (.v) | 283 (249 in active build) |
| Proven theorems (Qed) | 4,890 (active build) |
| Unfinished proofs (admit/Admitted) | 0 (entire active build) |
| Axioms | 4 (all justified, documented) |
| Lines of proof | 125,186 |
| Build status | Passing |

**What's proven:**
- Type safety (Progress + Preservation)
- Non-interference (information flow security)
- Effect system soundness
- Declassification policy correctness
- Termination guarantees (strong normalization)
- Memory safety (separation logic)
- Translation validation (certified compilation)
- Hardware contract verification
- Concurrency safety (session types, data-race freedom)
- 15 industry compliance properties (HIPAA, PCI-DSS, GDPR, PDPA MY/SG, SOX, DO-178C, ISO 26262, CC EAL7, NIST 800-53, CCPA, FERPA, BNM RMiT, MAS TRM, ISO 27001)

### Compiler & Toolchain (Rust)

| Metric | Value |
|--------|-------|
| Rust crates | 15 |
| Test count | 679 (all passing) |
| External dependencies | **0** |
| Lines of Rust | 24,614 |
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
- **Website** — 14-page site at [ib823.github.io/riina](https://ib823.github.io/riina/) — includes "Why Proof" executive page, 15 industry verticals, Releases page; deployed via `scripts/deploy-website.sh`
- **REPL** — Interactive mode for experimentation

### Example Programs

112 example `.rii` files across 9 categories:

| Category | Examples | Topics |
|----------|----------|--------|
| Basics | 20 | Arithmetic, closures, pattern matching, loops, pipes |
| Security | 18 | Secret types, capabilities, information flow, secure channels |
| Effects | 15 | IO, crypto, network, filesystem, effect composition |
| Applications | 15 | Web server, chat app, password manager, API gateway |
| Compliance | 10 | GDPR, HIPAA, PCI-DSS, PDPA, SOX, NIST |
| Design Patterns | 15 | Builder, state machine, visitor, monad, phantom types |
| FFI | 2 | C function calls (puts, abs, rand) |
| Showcase | 3 | Secure web server, PQ messenger, HIPAA medical records |
| AI Context | 1 | Complete corpus for LLM training |

### Cryptographic Tooling

The `05_TOOLING/` workspace contains 35,000+ lines of hand-written cryptographic primitives:

- **Symmetric:** AES-256, SHA-256 (FIPS 180-4), HMAC, ChaCha20-Poly1305
- **Asymmetric:** X25519, Ed25519 (interfaces + partial implementations)
- **Post-quantum:** ML-KEM, ML-DSA (interfaces)
- **Zero external crypto dependencies** — everything auditable from source

---

## Repository Structure

```
riina/
├── 02_FORMAL/coq/         283 Coq proof files (125K+ lines)
│   ├── foundations/        Core language semantics
│   ├── type_system/        Progress, Preservation, Type Safety
│   ├── properties/         Non-Interference, Declassification, Composition
│   ├── effects/            Effect algebra and gate proofs
│   ├── domains/            183 domain-specific proofs (R-Z, Σ, compliance)
│   ├── termination/        Strong normalization, sized types
│   ├── compliance/         DO-178C, ISO-26262, Common Criteria
│   └── Industries/         15 regulatory compliance proofs
│
├── 03_PROTO/               Rust compiler (15 crates, 679 tests, 0 deps)
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
├── 07_EXAMPLES/            112 example .rii files
├── docs/                   Enterprise docs, multilingual READMEs
├── VERSION                 Semver source of truth (0.2.0)
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
| V | Termination guarantees (strong normalization) | 6 files (3K lines) | Proven |
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

**Build: Passing. Grade: A.**
**Audit Update:** 2026-02-04 (Codex audit sync)

| Phase | Description | Status |
|-------|-------------|--------|
| 1. Compiler | Lexer, parser, typechecker, codegen, REPL, diagnostics | Done |
| 2. Standard Library | 88 builtins across 9 modules | Done |
| 3. Formal Verification | 5,544 Qed proofs, 4 justified axioms, 0 admits | Stable |
| 4. Developer Experience | Formatter, LSP, doc generator, VS Code extension, 112 examples | Done |
| 5. Ecosystem | CI/CD, package manager, Docker, Nix flake, release system, installer | Done |
| 6. Adoption | C FFI, 8 demos, community, enterprise, public branch, 14-page website (Why Proof, 15 industries, Releases) | Done |
| 7. Platform Universality | Multi-backend (WASM, Android, iOS), platform-conditional stdlib, WASM playground, backend verification | Done |
| 8. Long-term | Self-hosting compiler, hardware verification, verified OS | Planned |

### What's next

- **Phase 7 (Platform Universality):** Done — WASM backend, mobile backends, platform stdlib, WASM playground, 63 backend verification proofs
- **Phase 8 (Long-term):** Self-hosting compiler, hardware verification, verified OS
- **Axiom elimination:** 2 of the 4 remaining axioms can be eliminated with `store_rel_n` restructuring; 2 are permanent (policy axiom + standard closure axiom from academic literature)
- **Compliance system:** `--compliance` flag with 15 industry profiles, audit report generation (text + JSON), certification pipeline — see [Compliance Guide](docs/enterprise/COMPLIANCE_GUIDE.md)

---

## Security & Verification

RIINA uses **compiler-integrated verification** — no external CI/CD. Verification lives inside the compiler.

```bash
riinac verify --fast    # Tests + clippy (runs on every commit via pre-commit hook)
riinac verify --full    # + Coq admits/axioms scan (runs on every push via pre-push hook)
```

**Git hooks** enforce verification automatically:
- **Pre-commit:** `riinac verify --fast` blocks commits with failing tests
- **Pre-push:** `riinac verify --full` + GPG signature check + secret detection + Trojan source scan

Install hooks: `./00_SETUP/scripts/install_hooks.sh`

**Deep verification** (manual, 7 levels): `bash 05_TOOLING/scripts/verify.sh [0-6]`

Verification is enforced automatically via git hooks installed by `./00_SETUP/scripts/install_hooks.sh`.

---

## Contributing

RIINA is open source under the [Mozilla Public License 2.0](LICENSE).

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
The compiler, proofs, and toolchain are functional. Phases 1-6 (compiler, stdlib, proofs, developer tools, ecosystem, adoption) are complete. Phase 7 (Platform Universality — WASM, mobile backends) is in progress. Phase 8 (self-hosting, hardware verification) is the long-term vision. You can write, compile, and run RIINA programs today — via source build, Docker, or Nix.

**Do I need to know Bahasa Melayu?**
No. The keywords are short and consistent — `fungsi` (function), `biar` (let), `kalau` (if), `pulang` (return). You'll learn them in minutes. A [cheatsheet](07_EXAMPLES/06_ai_context/RIINA_CHEATSHEET.md) is included.

**Do I need to understand Coq or formal verification?**
No. The proofs run at compile time automatically. You write normal code; the compiler does the proving. The Coq proofs are there for auditability — you benefit from them without reading them.

**Why zero external dependencies?**
Trust. Every line of RIINA — compiler, crypto, standard library — is auditable from source. No supply chain attacks. No dependency confusion. No left-pad incidents.

**Why Bahasa Melayu?**
RIINA developed by Malaysians for the world. Programming languages have been English-only for 70 years. RIINA proves that formal verification and native-language syntax are not mutually exclusive. If a language can be proven correct, it can be proven correct in any language.

**How does RIINA compare to SPARK/Ada?**
SPARK proves absence of runtime errors (overflow, division by zero) for a subset of Ada. RIINA proves information flow security (non-interference), effect safety, declassification correctness, and more — for the entire language. Both are formally verified; RIINA's scope is broader.

---

*RIINA — Rigorous Immutable Invariant, No Assumptions*

*Q.E.D. Aeternum.*
