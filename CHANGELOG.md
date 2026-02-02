# Changelog

All notable changes to RIINA will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added
- Phase 7: Platform Universality — modular backend trait architecture (`Backend` trait, `Target` enum)
- WebAssembly backend (`--target=wasm32`) with direct IR-to-WASM binary emission
- Platform-conditional standard library (`platform.rs`) for cross-platform compilation
- Mobile backend scaffolding: Android JNI bridge generation, iOS Swift bridge generation
- `--target` flag for `riinac build` and `riinac emit` commands
- Roadmap updated across all documentation (11 files)

## [0.2.0] - 2026-02-01

### Added
- Compliance system user guide (`docs/enterprise/COMPLIANCE_GUIDE.md`)
- 15 industry compliance profiles with CLI integration (`--compliance`, `--report`, `--report-json`)
- Audit report generation (text + JSON formats with SHA-256 integrity)
- `riina-compliance` crate: PCI-DSS (3 rules), PDPA (2 rules), BNM RMiT (1 rule)

### Changed
- Version bump to 0.2.0 across all manifests

### Fixed
- CERTIFICATION.md: corrected axiom count (5 → 4) and file count (244 → 245)

## [0.1.0] - 2026-02-01

### Added
- RIINA compiler (`riinac`) with Bahasa Melayu syntax
- Lexer, parser, type checker, and C code generation
- Effect system with `kesan` (effect) and `bersih` (pure) annotations
- Security types: `Rahsia<T>` (secret) with `dedah` (declassify)
- Standard library: 88 builtins across 9 modules
- Developer tools: `riina-fmt`, `riina-lsp`, `riina-doc`
- VS Code extension (`riina-vscode`)
- Package manager (`riina-pkg`)
- 112 example `.rii` files across 9 categories
- Formal verification: 4,885 Qed proofs in Coq active build (0 admits, 4 justified axioms)
- Compliance system: 15 industry profiles with audit report generation
- C FFI support via `luaran "C" { ... }`
- REPL with `:jenis` (type) and `:kesan` (effect) commands
- Nix flake, Dockerfile, and install script
- Website with documentation

### Security
- Non-interference proven via logical relations in Coq
- Type safety (progress + preservation) formally verified
- Effect system soundness proven
- Zero third-party runtime dependencies

[Unreleased]: https://github.com/ib823/riina/compare/v0.2.0...HEAD
[0.2.0]: https://github.com/ib823/riina/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/ib823/riina/releases/tag/v0.1.0
