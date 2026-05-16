# Contributing to RIINA™

**Verification:** live counts and per-lane claim levels in `PROOF_STATUS.md` and `website/public/metrics.json`. Active Coq build is 0 Admitted / 0 active axioms; 10 prover lanes are tracked alongside Rust test suites in `03_PROTO` and `05_TOOLING`.

Thank you for your interest in RIINA. This guide covers how to contribute effectively.

## Prerequisites

- **Rust** 1.84.0+ — `rustup install stable`
- **Coq 8.20.1** — Only needed for formal proof work (files use `From Coq`; see CHANGELOG.md for the prior Rocq migration)
- No external dependencies required

## Getting Started

```bash
git clone https://github.com/ib823/riina.git
cd riina

# Verify environment
bash 00_SETUP/scripts/verify_setup.sh

# Build the compiler
cd 03_PROTO && cargo build --release -p riinac && cd ..

# Run all tests
cd 03_PROTO && cargo test --workspace && cd ..

# Try it out
./03_PROTO/target/release/riinac run 07_EXAMPLES/demos/selamat_datang.rii
```

## Project Structure

| Directory | What | Language |
|-----------|------|---------|
| `02_FORMAL/` | Formal proofs (Coq primary, Lean secondary, additional smoke lanes) | Coq/Lean/Isabelle + 7 more |
| `03_PROTO/crates/` | Compiler (15 crates) | Rust |
| `04_SPECS/` | Language specifications | Markdown |
| `05_TOOLING/` | Crypto primitives, build tools | Rust |
| `07_EXAMPLES/` | Example `.rii` programs | RIINA |
| `riina-vscode/` | VS Code extension | TypeScript/JSON |
| `website/` | Project website | React |

## How to Contribute

### Bug Reports

Use the [Bug Report template](https://github.com/ib823/riina/issues/new?template=bug_report.md). Include:
- Steps to reproduce
- Expected vs actual behavior
- `riinac` version (`riinac --version`)
- `.rii` file that triggers the bug (if applicable)

### Feature Requests

Use the [Feature Request template](https://github.com/ib823/riina/issues/new?template=feature_request.md). Describe:
- The problem you're solving
- Your proposed solution
- How it fits with RIINA's security model

### Code Contributions

1. **Fork** the repository
2. **Create a branch** from `main` — `git checkout -b my-feature main`
3. **Make your changes** — see coding standards below
4. **Run tests** — `cd 03_PROTO && cargo test --all && cargo clippy -- -D warnings`
5. **Submit a pull request** against `main`

### Writing Example Programs

We welcome new `.rii` examples. Place them in the appropriate category under `07_EXAMPLES/`:

- `00_basics/` — Language fundamentals
- `01_security/` — Security type demonstrations
- `02_effects/` — Effect system usage
- `03_applications/` — Real-world applications
- `04_compliance/` — Regulatory compliance
- `05_patterns/` — Design patterns

Use **Bahasa Melayu** keywords in all examples. See `07_EXAMPLES/06_ai_context/RIINA_CHEATSHEET.md` for the keyword reference.

## Coding Standards

### Rust (03_PROTO/, 05_TOOLING/)

- **Zero external dependencies** — Do not add crates to any `Cargo.toml`. This is a security decision.
- `cargo test --all` must pass
- `cargo clippy -- -D warnings` must pass
- `cargo fmt --check` must pass
- No `unsafe` without documented justification
- No panics in library code — use `Result`

### Coq (02_FORMAL/coq/)

- **No `Admitted.`** — Every proof must be complete
- **No `admit.`** — No tactical admits
- **No unjustified `Axiom`** — All axioms must be documented with rationale
- Build with `make` in `02_FORMAL/coq/` — must succeed with zero errors

### RIINA Examples (07_EXAMPLES/)

- Use Bahasa Melayu keywords (`fungsi`, `biar`, `kalau`, etc.)
- Include doc comments (`///`) explaining what the example demonstrates
- Include the `riinac` command to run/check the file

### Platform Backends (03_PROTO/crates/riina-codegen/)

Backend contributions must:
- Implement the `Backend` trait from `backend.rs`
- Preserve RIINA's security invariants (non-interference, effect safety) in emitted code
- Include tests that verify output validity for the target platform
- Not introduce platform-specific dependencies — all encoding is hand-written

Current backends: C (native), WASM (`wasm.rs`), Mobile (`mobile.rs` + `jni.rs` + `swift_bridge.rs`)

## Verification

Before submitting a PR, run the verification gate:

```bash
# Quick check (tests + clippy)
./03_PROTO/target/release/riinac verify --fast

# Full check (+ Coq audit) — required for proof changes
./03_PROTO/target/release/riinac verify --full
```

## Continuous Integration

Five GitHub Actions workflows run on every push to `main` / `claude/**` and
on every pull request to `main`. They mirror — and are intended to replace —
the manual `scripts/godzilla-pipeline.sh` invocation for the subset of checks
that do not require a Rocq/Lean/Isabelle/F* toolchain.

| Workflow              | File                                | What it runs                                                                          | Reproduce locally                                                       |
| --------------------- | ----------------------------------- | ------------------------------------------------------------------------------------- | ----------------------------------------------------------------------- |
| `ci`                  | `.github/workflows/ci.yml`          | `cargo build --release --workspace` and `cargo test --workspace` on both Rust workspaces | `(cd 03_PROTO && cargo build --release --workspace && cargo test --workspace)` and the same in `05_TOOLING` |
| `quality-gates`       | `.github/workflows/quality-gates.yml` | `bash scripts/public-quality-gates.sh`                                                | `bash scripts/public-quality-gates.sh`                                  |
| `security`            | `.github/workflows/security.yml`    | `bash scripts/security-gates.sh --no-signing-check --range <event-range>`             | `bash scripts/security-gates.sh`                                        |
| `website`             | `.github/workflows/website.yml`     | `npm install && npx vite build` in `website/` (only when `website/**` changes)        | `(cd website && npm install && npx vite build)`                         |
| `release`             | `.github/workflows/release.yml`     | On `v*.*.*` tag push: build source tarball + SHA256SUMS, attach to GitHub Release    | See `scripts/release.sh` for the full pre-tag pipeline                  |

### What is NOT in CI

The following gates are part of `scripts/godzilla-pipeline.sh` but are **not**
wired into GitHub Actions today, by design:

- **Coq / Lean / Isabelle / F* proof checks.** They require provisioning the
  formal toolchain (`scripts/provision-formal-tools.sh`) and tens of CPU-minutes
  per run. Run them locally before submitting proof changes.
- **`riinac verify --full`.** Drives the Coq audit; same toolchain constraint.
- **Deep verify level 4 (`05_TOOLING/scripts/verify.sh`).** Same constraint.
- **`cargo clippy -- -D warnings` and `cargo fmt --check`.** Listed in the
  coding standards above. Both `05_TOOLING` and `03_PROTO` are clean on
  `cargo fmt --check` and `cargo clippy --workspace --all-targets -- -D warnings`,
  but neither is wired into CI as a required gate yet — promote them once
  the next round of changes has been reviewed.

### Signed-commit policy

Signed commits are mandatory for `main`. CI cannot verify this (runner commits
are unsigned by definition), so the policy is enforced server-side via
**GitHub branch protection**:

- Settings → Branches → Branch protection rule for `main` → "Require signed
  commits".

The `security` workflow passes `--no-signing-check` to `scripts/security-gates.sh`
precisely because of this — never use that flag in local pre-push runs.

### Known CI failures at the time of this writing

None. Both workspaces (`03_PROTO`, `05_TOOLING`) pass `cargo build`,
`cargo test`, `cargo fmt --check`, and `cargo clippy --workspace --all-targets -- -D warnings`;
`bash scripts/public-quality-gates.sh`, `bash scripts/audit-docs.sh`, and
`bash scripts/security-gates.sh --no-signing-check` all pass locally.
Promoting the clippy/fmt commands to required CI gates is the natural
next step once the change has been reviewed.

## Communication

- **Issues** — [github.com/ib823/riina/issues](https://github.com/ib823/riina/issues)
- **Discussions** — [github.com/ib823/riina/discussions](https://github.com/ib823/riina/discussions)

## License

By contributing, you agree that your contributions will be licensed under the [RIINA Proprietary License](LICENSE).

---

*RIINA — Rigorous Immutable Invariant, No Assumptions*
