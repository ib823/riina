# Changelog

**Verification:** live counts and per-lane claim levels in `PROOF_STATUS.md` and `website/public/metrics.json`. Active Coq build is 0 Admitted / 0 active axioms. Historical session entries below preserve their as-of-release numbers.

All notable changes to RIINA™ will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added (Session 88 — 2026-03-16 — Linear Types, Multi-Prover Mechanization, WASM Backend)
- Linear type enforcement: `biar sekali` (affine), `biar paling` (relevant), `biar mesti` (linear) wired through lexer→parser→typechecker; Phase 3 gate PASSED
- WASM backend working end-to-end: .rii → WASM → wasmtime for integers, arithmetic, if/else, function calls, closures with captures, recursive functions (REQ-14 DONE)
- 19 Lean 4 domain files fixed — Lean upgraded to mechanized (4,458 theorems, 0 sorry)
- 267 SMT/Z3 files fixed and verified — SMT dequarantined and mechanized (11,843 assertions)
- Isabelle 10 core theories compile — Isabelle upgraded to mechanized (9,092 lemmas, 0 sorry)
- F*, TLA+, Alloy dequarantined — Track B1 worker fixes merged
- Total proofs: 48,913 across 10 provers (4 mechanized, 3 compiled, 3 generated)
- 980 Rust tests passing, clippy clean

### Fixed (Session 88)
- `generate-metrics.sh`: `escape_json` fix for newlines in pending reasons

### Added (Session 87 — Phase 3 Compiler Enforcement Alignment)
- Declassification strict mode: `declassify(e)` now rejects non-Secret types (matches Coq T_Declassify)
- Handle effect join: `handle e with x → h` returns `eff_e ⊔ eff_h` (matches Coq T_Handle)
- Handle handler binding: handler variable `x` bound to body result type in handler scope
- Top-level binding purity enforcement: `biar x = e` at module level rejects effectful expressions
- Capability Grant/Require context tracking: `TypingContext.granted` set propagated through Grant/Require/LetRec
- Function body capability granting: declared function effects auto-granted in body scope
- Phase 3 and Phase 4 task tables updated with DONE/TODO status
- 968 Rust tests passing (up from 924), 0 failures

### Added (Session 86 — Core Deepening)
- `properties/TypingInversion.v`: 53 Qed — 22 typing inversion lemmas, value purity theorem, type/effect determinism, type constructor disjointness (12) and injectivity (6)
- `domains/TaintSystemCorrectness.v`: 47 Qed — compile-time taint tracking with typing uniqueness proving 9 injection attack categories impossible (SQL, XSS, command, path traversal, LDAP, XML, header, template, eval)
- Resolved 4 design decisions: D014 (fuel-based while loops), D019 (file-based modules), D020 (u64 core + signed library), D021 (infix operator desugaring)
- Active Coq build: 9,171 Qed across 259 files, 0 Admitted, 0 active axioms

### Added
- REQ-13: End-to-end .rii → C → executable pipeline verified
  - Fixed `riinac build` path handling for files outside working directory
  - Fixed C codegen `str_val` → `string_val.data` in `riina_binop_add` string concatenation
  - Fixed C codegen missing `_XOPEN_SOURCE` for `strptime`
  - Fixed IR lowering: `FixClosure` only emitted for genuinely recursive functions (was segfaulting non-recursive top-level functions)
  - 6 end-to-end integration tests: hello, arithmetic, conditionals, declassification, multi-function, non-trivial full pipeline
  - Non-trivial test exercises: multiple functions, arithmetic, if/else, Secret<T> classify/declassify with proof, System effect
- REQ-12: Compiler enforces information flow control (Bell-LaPadula model)
  - T_Assign: no-write-down (`Δ ⊑ sl`) prevents implicit flows through control structure
  - T_Deref: no-read-up (`sl ⊑ Δ`) prevents unauthorized reads
  - IFC-aware branching: If/Case elevate Δ in branches based on condition security level
  - New `ImplicitFlowViolation` error (S0003) with clear diagnostics
  - 7 new IFC enforcement tests (Bell-LaPadula, implicit flow prevention)
- Lean 4 active lane mechanized: 3,895 theorem/lemma declarations across 136 files, 0 sorry, 0 axioms
- AlgebraicEffects.lean: 48 axioms eliminated via first-order defunctionalization + step-indexed typing (Appel-McAllester 2001)
- Z3 security lattice verification: 25 properties verified (matching Coq Syntax.v lattice lemmas)
- Isabelle/HOL smoke session: 1 compiled theory (RIINA_CORE, Syntax.thy)
- Phase 2 prover closure gate passed for scoped provers (Lean, F*, TLA+, Alloy, Z3)

### Fixed
- Coq 8.20.1 compatibility: migrated from Rocq 9.1, fixed all import paths (`Stdlib.*` → `Coq.*`), fixed API changes (`filter_length` → `filter_length_le`), fixed recursive definitions, updated proofs for new semantics
- Eliminated all 7 previously-tracked Admitted proofs (DELTA001, Platform/WASM/Mobile stubs, ValRelStepLimit)
- Eliminated remaining active proof assumptions; active Coq build is now `Axioms=0`, `Admitted=0`, explicit assumptions `=0`
- Active Coq build now at 11,905 Qed proofs

### Added (Phase 7)
- Phase 7: Platform Universality — modular backend trait architecture (`Backend` trait, `Target` enum)
- WebAssembly backend (`--target=wasm32`) with direct IR-to-WASM binary emission
- Platform-conditional standard library (`platform.rs`) for cross-platform compilation
- Mobile backend scaffolding: Android JNI bridge generation, iOS Swift bridge generation
- `--target` flag for `riinac build` and `riinac emit` commands
- `riina-wasm` crate: in-browser compiler via WASM (cdylib with `extern "C"` exports)
- WASM Playground page on website (split-pane editor, 5 examples, Web Worker compilation)
- 4 backend verification Coq proofs: WASM correctness, JNI/Swift bridge, platform stdlib, backend trait (63 Qed)
- Phase 7 complete (all M7.1–M7.6 milestones done)
- WASM backend production: bump allocator, string constants, pair/sum types, closures (table + call_indirect), refs, builtin imports
- WASM bug fixes: Mod (I32RemS), And/Or (I32And/I32Or), Call (function index resolution)
- Android JNI production: full C implementation (JNI_OnLoad, type marshaling, callback routing, permissions from effects)
- iOS Swift production: extended type conversion, C bridge routing, Info.plist generation, SPM Package.swift
- Playground build pipeline: build-wasm.sh, Vite WASM integration, deploy pipeline
- Backend composition Coq proofs: NI preservation through compiled backends (BackendComposition.v, 11 Qed)
- Extended WASM verification (+23 Qed: strings, closures, pairs, allocator, completeness)
- Extended mobile bridge verification (+17 Qed: JNI string roundtrip, Swift type safety, callback safety)

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
- Formal verification: 4,890 Qed proofs in Coq active build (0 admits, 4 justified axioms)
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
