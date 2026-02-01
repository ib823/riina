# Contributing to RIINA

Thank you for your interest in RIINA. This guide covers how to contribute effectively.

## Prerequisites

- **Rust** 1.84.0+ — `rustup install stable`
- **Rocq 9.1 / Coq 8.21** — Only needed for formal proof work
- No external dependencies required

## Getting Started

```bash
git clone https://github.com/ib823/proof.git
cd proof

# Verify environment
bash 00_SETUP/scripts/verify_setup.sh

# Build the compiler
cd 03_PROTO && cargo build --release -p riinac && cd ..

# Run all tests (should show 651+ passing)
cd 03_PROTO && cargo test --all && cd ..

# Try it out
./03_PROTO/target/release/riinac run 07_EXAMPLES/demos/selamat_datang.rii
```

## Project Structure

| Directory | What | Language |
|-----------|------|---------|
| `02_FORMAL/coq/` | Formal proofs (5,308 theorems) | Coq |
| `03_PROTO/crates/` | Compiler (14 crates) | Rust |
| `04_SPECS/` | Language specifications | Markdown |
| `05_TOOLING/` | Crypto primitives, build tools | Rust |
| `07_EXAMPLES/` | Example `.rii` programs | RIINA |
| `riina-vscode/` | VS Code extension | TypeScript/JSON |
| `website/` | Project website | React |

## How to Contribute

### Bug Reports

Use the [Bug Report template](https://github.com/ib823/proof/issues/new?template=bug_report.md). Include:
- Steps to reproduce
- Expected vs actual behavior
- `riinac` version (`riinac --version`)
- `.rii` file that triggers the bug (if applicable)

### Feature Requests

Use the [Feature Request template](https://github.com/ib823/proof/issues/new?template=feature_request.md). Describe:
- The problem you're solving
- Your proposed solution
- How it fits with RIINA's security model

### Code Contributions

1. **Fork** the repository
2. **Create a branch** from `public` — `git checkout -b my-feature public`
3. **Make your changes** — see coding standards below
4. **Run tests** — `cd 03_PROTO && cargo test --all && cargo clippy -- -D warnings`
5. **Submit a pull request** against `public`

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

## Communication

- **Issues** — [github.com/ib823/proof/issues](https://github.com/ib823/proof/issues)
- **Discussions** — [github.com/ib823/proof/discussions](https://github.com/ib823/proof/discussions)

## License

By contributing, you agree that your contributions will be licensed under the [Mozilla Public License 2.0](LICENSE).

---

*RIINA — Rigorous Immutable Invariant, No Assumptions*
