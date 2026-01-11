# TRACK F: BUILD SYSTEM SPECIFICATION

## Version 1.0.0 — Foundation for ALL TERAS Development

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                    TERAS BUILD SYSTEM SPECIFICATION                          ║
║                           TRACK_F-TOOL-BUILD                                 ║
║                                                                              ║
║  DOCUMENT TYPE: Tool Specification                                           ║
║  VERSION: 1.0.0                                                              ║
║  STATUS: ACTIVE                                                              ║
║  DATE: 2026-01-03                                                            ║
║                                                                              ║
║  PRINCIPLE: If tools don't work, NOTHING works.                              ║
║  MODE: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST                           ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

# TABLE OF CONTENTS

1. [Document Metadata](#1-document-metadata)
2. [Executive Summary](#2-executive-summary)
3. [Build System Architecture](#3-build-system-architecture)
4. [Rust Workspace Configuration](#4-rust-workspace-configuration)
5. [Ada/SPARK Build Integration](#5-adaspark-build-integration)
6. [TERAS-LANG Build Pipeline](#6-teras-lang-build-pipeline)
7. [Hardware Build Integration](#7-hardware-build-integration)
8. [Reproducible Build Specification](#8-reproducible-build-specification)
9. [Build Security Requirements](#9-build-security-requirements)
10. [Hash Chain Tooling](#10-hash-chain-tooling)
11. [CI/CD Foundation Configuration](#11-cicd-foundation-configuration)
12. [Development Environment Setup](#12-development-environment-setup)
13. [Build Verification Protocol](#13-build-verification-protocol)
14. [Cross-Track Build Support](#14-cross-track-build-support)
15. [Monitoring and Alerting](#15-monitoring-and-alerting)
16. [Validation and Testing](#16-validation-and-testing)

---

# 1. DOCUMENT METADATA

## 1.1 Version Information

| Field | Value |
|-------|-------|
| Document ID | TRACK_F-TOOL-BUILD_v1_0_0 |
| Version | 1.0.0 |
| Status | ACTIVE |
| Created | 2026-01-03 |
| Author | Track F: Tooling |
| Classification | INTERNAL |

## 1.2 Dependencies

| Document | Version | Relationship |
|----------|---------|--------------|
| TERAS_MASTER_CONTEXT | v1.0.0 | NORMATIVE |
| TERAS_DEFINITIVE_PLAN | v1.0.0 | NORMATIVE |
| TERAS_MASTER_ARCHITECTURE_v3_2_2_CONSOLIDATED | v3.2.2 | REFERENCE |
| TERAS_COORDINATION_LOG | v1.0.0 | COORDINATION |

## 1.3 Consumers

| Track | Usage |
|-------|-------|
| Track A: Formal | Verification tool builds |
| Track B: Prototype | Rust/Ada prototype builds |
| Track C: Specification | Documentation builds |
| Track D: Adversarial | Security testing builds |
| Track E: Hardware | RTL/FPGA builds |
| Research | Tool builds |

## 1.4 Hash Chain Entry

```
DOCUMENT: TRACK_F-TOOL-BUILD_v1_0_0.md
PREDECESSOR: TERAS_COORDINATION_LOG_v1_0_0.md
SHA-256: [COMPUTED AT FINALIZATION]
```

---

# 2. EXECUTIVE SUMMARY

## 2.1 Purpose

This document specifies the complete build system infrastructure for TERAS. The build system is the foundation upon which ALL other tracks depend. A broken build system means:

- Track A cannot verify proofs
- Track B cannot compile prototypes
- Track C cannot generate documentation
- Track D cannot run security tests
- Track E cannot synthesize hardware
- Research cannot execute experiments

**IF THE BUILD SYSTEM FAILS, EVERYTHING FAILS.**

## 2.2 Design Principles

```
PRINCIPLE 1: REPRODUCIBILITY
├── Bit-for-bit identical outputs given identical inputs
├── Hermetic builds with no external state dependencies
├── Deterministic ordering in all build operations
├── Captured environment in build manifests
└── Verified reproducibility through hash comparison

PRINCIPLE 2: SECURITY
├── Zero arbitrary code execution in build scripts
├── Sandboxed build environments
├── Verified inputs before processing
├── Signed outputs with provenance
└── Complete audit trail of all build actions

PRINCIPLE 3: RELIABILITY
├── No single points of failure
├── Graceful degradation under load
├── Automatic recovery from transient failures
├── Comprehensive error reporting
└── Health monitoring and alerting

PRINCIPLE 4: PERFORMANCE
├── Incremental builds for fast iteration
├── Parallel builds where dependencies permit
├── Distributed builds for CI workloads
├── Intelligent caching with cache invalidation
└── Sub-second feedback for trivial changes

PRINCIPLE 5: MAINTAINABILITY
├── Self-documenting configuration
├── Modular build definitions
├── Version-controlled everything
├── Automated testing of build system itself
└── Clear ownership and responsibility
```

## 2.3 Technology Stack

```
BUILD ORCHESTRATION:
├── Primary: Custom TERAS Build System (teras-build)
├── Rust: Cargo (with custom extensions)
├── Ada/SPARK: GPRbuild with GNAT
├── Documentation: mdBook, rustdoc, ada2doc
├── Hardware: Yosys, nextpnr, verilator
└── Coordination: Custom hash chain tooling

VERIFICATION:
├── Rust: Verus, Creusot, Prusti, Kani, Miri
├── Ada/SPARK: GNATprove
├── Proofs: Coq, Lean 4, Isabelle/HOL
├── Hardware: SymbiYosys, Yosys-SMTBMC
└── Integration: Custom verification orchestrator

CI/CD:
├── Primary: Self-hosted runners (security requirement)
├── Configuration: YAML with schema validation
├── Secrets: HashiCorp Vault
├── Artifacts: Content-addressed storage
└── Monitoring: Custom dashboard
```

---

# 3. BUILD SYSTEM ARCHITECTURE

## 3.1 High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           TERAS BUILD SYSTEM                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                      BUILD ORCHESTRATOR (teras-build)               │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌────────────┐ │   │
│  │  │ Dependency  │  │   Build     │  │  Parallel   │  │  Result    │ │   │
│  │  │ Resolution  │  │  Ordering   │  │  Execution  │  │ Verification│ │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘  └────────────┘ │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                   │                                         │
│         ┌─────────────────────────┼─────────────────────────┐              │
│         │                         │                         │              │
│         ▼                         ▼                         ▼              │
│  ┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐      │
│  │   RUST BUILDER  │     │  ADA/SPARK      │     │  TERAS-LANG     │      │
│  │                 │     │   BUILDER       │     │   BUILDER       │      │
│  │  ┌───────────┐  │     │  ┌───────────┐  │     │  ┌───────────┐  │      │
│  │  │   cargo   │  │     │  │ gprbuild  │  │     │  │  terasc   │  │      │
│  │  └───────────┘  │     │  └───────────┘  │     │  └───────────┘  │      │
│  │  ┌───────────┐  │     │  ┌───────────┐  │     │  ┌───────────┐  │      │
│  │  │  rustc    │  │     │  │   gnat    │  │     │  │   llvm    │  │      │
│  │  └───────────┘  │     │  └───────────┘  │     │  └───────────┘  │      │
│  └────────┬────────┘     └────────┬────────┘     └────────┬────────┘      │
│           │                       │                       │                │
│           ▼                       ▼                       ▼                │
│  ┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐      │
│  │  RUST VERIFIER  │     │ SPARK VERIFIER  │     │ TERAS VERIFIER  │      │
│  │  ├── verus     │     │  ├── gnatprove  │     │  ├── type-check │      │
│  │  ├── creusot   │     │  └── z3/cvc5    │     │  ├── effect-chk │      │
│  │  ├── prusti    │     │                 │     │  └── proof-gen  │      │
│  │  ├── kani      │     │                 │     │                 │      │
│  │  └── miri      │     │                 │     │                 │      │
│  └────────┬────────┘     └────────┬────────┘     └────────┬────────┘      │
│           │                       │                       │                │
│           └───────────────────────┼───────────────────────┘                │
│                                   │                                         │
│                                   ▼                                         │
│                    ┌──────────────────────────────┐                        │
│                    │      ARTIFACT MANAGER        │                        │
│                    │  ├── Hash computation        │                        │
│                    │  ├── Signature generation    │                        │
│                    │  ├── Provenance recording    │                        │
│                    │  └── Content-addressed store │                        │
│                    └──────────────────────────────┘                        │
│                                   │                                         │
│                                   ▼                                         │
│                    ┌──────────────────────────────┐                        │
│                    │   HASH CHAIN INTEGRATION     │                        │
│                    │  ├── Build manifest          │                        │
│                    │  ├── Chain verification      │                        │
│                    │  └── Audit trail             │                        │
│                    └──────────────────────────────┘                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## 3.2 Component Specifications

### 3.2.1 Build Orchestrator (teras-build)

```
COMPONENT: teras-build
PURPOSE: Central build coordination and execution

RESPONSIBILITIES:
├── Parse build configuration (teras-build.toml)
├── Resolve dependencies (topological sort)
├── Schedule build tasks (parallel where possible)
├── Execute builders (Rust, Ada, TERAS-LANG, HDL)
├── Collect and verify results
├── Generate build manifests
├── Update hash chain
└── Report results

IMPLEMENTATION:
├── Language: Rust (verified with Kani)
├── Concurrency: tokio async runtime
├── Configuration: TOML with JSON Schema validation
├── IPC: Unix domain sockets
├── State: Content-addressed file system
└── Logging: Structured JSON logs

INTERFACES:
├── CLI: teras-build [OPTIONS] <COMMAND>
├── Configuration: teras-build.toml
├── Output: build-manifest.json, artifacts/
└── Exit codes: 0=success, 1=build-error, 2=verification-error
```

### 3.2.2 Rust Builder

```
COMPONENT: rust-builder
PURPOSE: Build and verify Rust components

RESPONSIBILITIES:
├── Compile Rust code (cargo build)
├── Run Rust tests (cargo test)
├── Execute verification tools (verus, creusot, prusti, kani, miri)
├── Check formatting (rustfmt)
├── Run lints (clippy)
├── Generate documentation (rustdoc)
└── Package artifacts

CONFIGURATION:
├── Cargo.toml (workspace-level)
├── rust-toolchain.toml (pinned version)
├── .cargo/config.toml (build settings)
├── clippy.toml (lint configuration)
└── rustfmt.toml (format configuration)

VERIFICATION LEVELS:
├── Level 0: Compilation only
├── Level 1: + clippy + rustfmt
├── Level 2: + miri (unsafe code verification)
├── Level 3: + kani (bounded model checking)
├── Level 4: + prusti (Viper-based verification)
├── Level 5: + creusot (Why3-based verification)
└── Level 6: + verus (SMT-based verification)

BUILD PROFILES:
├── dev: Level 1, debug info, no optimization
├── test: Level 3, debug info, some optimization
├── ci: Level 4, no debug info, full optimization
├── release: Level 6, no debug info, full optimization, LTO
└── paranoid: Level 6 + all optional checks
```

### 3.2.3 Ada/SPARK Builder

```
COMPONENT: ada-builder
PURPOSE: Build and verify Ada/SPARK components

RESPONSIBILITIES:
├── Compile Ada code (gprbuild)
├── Verify SPARK annotations (gnatprove)
├── Run Ada tests (gnattest)
├── Check style (gnatcheck)
├── Generate documentation (ada2doc)
└── Package artifacts

CONFIGURATION:
├── teras.gpr (GPR project file)
├── gnatprove.adc (SPARK configuration)
├── gnatcheck.rules (style rules)
└── ada_style.cfg (formatting)

VERIFICATION LEVELS:
├── Level 0: Compilation only
├── Level 1: + gnatcheck style
├── Level 2: + SPARK flow analysis
├── Level 3: + SPARK proof (gold level)
├── Level 4: + SPARK proof (platinum level)
└── Level 5: + All external provers (z3, cvc5, alt-ergo)

BUILD PROFILES:
├── dev: Level 1, debug info, no optimization
├── test: Level 3, debug info, -O1
├── ci: Level 4, no debug info, -O2
├── release: Level 5, no debug info, -O3
└── paranoid: Level 5 + all provers + counterexample search
```

### 3.2.4 TERAS-LANG Builder

```
COMPONENT: teras-lang-builder
PURPOSE: Build TERAS-LANG compiler and compile TERAS-LANG code

RESPONSIBILITIES:
├── Bootstrap TERAS-LANG compiler
├── Compile TERAS-LANG sources
├── Verify type safety
├── Verify effect properties
├── Generate proof bundles
├── Generate documentation
└── Package artifacts

PIPELINE STAGES:
├── Stage 0: Bootstrap (written in Rust)
│   ├── Lexer (hand-written)
│   ├── Parser (hand-written)
│   ├── Type checker (hand-written)
│   └── Code generator (LLVM)
│
├── Stage 1: Self-hosted compiler
│   ├── Lexer (TERAS-LANG)
│   ├── Parser (TERAS-LANG)
│   ├── Type checker (TERAS-LANG)
│   └── Code generator (TERAS-LANG)
│
└── Stage 2: Verified compiler
    ├── All components formally verified
    ├── Compiler correctness proof
    └── Hash chain verification

VERIFICATION LEVELS:
├── Level 0: Syntax check only
├── Level 1: + Type checking
├── Level 2: + IFC checking
├── Level 3: + Effect checking
├── Level 4: + Capability checking
├── Level 5: + Proof bundle generation
└── Level 6: + Proof bundle verification
```

## 3.3 Build Flow

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                            BUILD FLOW                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────┐                │
│  │   SOURCE     │────▶│    PARSE     │────▶│   RESOLVE    │                │
│  │   INPUTS     │     │    CONFIG    │     │   DEPS       │                │
│  └──────────────┘     └──────────────┘     └──────────────┘                │
│         │                    │                    │                         │
│         │                    │                    │                         │
│         ▼                    ▼                    ▼                         │
│  ┌──────────────────────────────────────────────────────────────┐          │
│  │                     VERIFY INPUTS                             │          │
│  │  ├── Check file hashes against expected                       │          │
│  │  ├── Verify no unauthorized modifications                     │          │
│  │  ├── Validate configuration schema                            │          │
│  │  └── Check dependency versions                                │          │
│  └──────────────────────────────────────────────────────────────┘          │
│                              │                                              │
│                              ▼                                              │
│  ┌──────────────────────────────────────────────────────────────┐          │
│  │                    SCHEDULE TASKS                             │          │
│  │  ├── Topological sort of dependencies                         │          │
│  │  ├── Identify parallelizable tasks                            │          │
│  │  ├── Allocate resources                                       │          │
│  │  └── Create execution plan                                    │          │
│  └──────────────────────────────────────────────────────────────┘          │
│                              │                                              │
│         ┌────────────────────┼────────────────────┐                        │
│         │                    │                    │                         │
│         ▼                    ▼                    ▼                         │
│  ┌────────────┐       ┌────────────┐       ┌────────────┐                  │
│  │   BUILD    │       │   BUILD    │       │   BUILD    │                  │
│  │   TASK 1   │       │   TASK 2   │       │   TASK N   │                  │
│  └────────────┘       └────────────┘       └────────────┘                  │
│         │                    │                    │                         │
│         ▼                    ▼                    ▼                         │
│  ┌────────────┐       ┌────────────┐       ┌────────────┐                  │
│  │   VERIFY   │       │   VERIFY   │       │   VERIFY   │                  │
│  │   TASK 1   │       │   TASK 2   │       │   TASK N   │                  │
│  └────────────┘       └────────────┘       └────────────┘                  │
│         │                    │                    │                         │
│         └────────────────────┼────────────────────┘                        │
│                              │                                              │
│                              ▼                                              │
│  ┌──────────────────────────────────────────────────────────────┐          │
│  │                    COLLECT RESULTS                            │          │
│  │  ├── Gather all artifacts                                     │          │
│  │  ├── Compute artifact hashes                                  │          │
│  │  ├── Verify all verification passed                           │          │
│  │  └── Check for any failures                                   │          │
│  └──────────────────────────────────────────────────────────────┘          │
│                              │                                              │
│                              ▼                                              │
│  ┌──────────────────────────────────────────────────────────────┐          │
│  │                    SIGN AND STORE                             │          │
│  │  ├── Generate build manifest                                  │          │
│  │  ├── Sign artifacts with build key                            │          │
│  │  ├── Store in content-addressed storage                       │          │
│  │  └── Update hash chain                                        │          │
│  └──────────────────────────────────────────────────────────────┘          │
│                              │                                              │
│                              ▼                                              │
│  ┌──────────────────────────────────────────────────────────────┐          │
│  │                    REPORT RESULTS                             │          │
│  │  ├── Generate build report                                    │          │
│  │  ├── Update coordination log                                  │          │
│  │  ├── Notify dependent tracks                                  │          │
│  │  └── Archive logs                                             │          │
│  └──────────────────────────────────────────────────────────────┘          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

# 4. RUST WORKSPACE CONFIGURATION

## 4.1 Workspace Structure

```
teras/
├── Cargo.toml                 # Workspace root
├── rust-toolchain.toml        # Pinned Rust version
├── .cargo/
│   └── config.toml           # Cargo configuration
├── rustfmt.toml              # Formatting rules
├── clippy.toml               # Lint configuration
├── deny.toml                 # Dependency policy
│
├── crates/
│   ├── teras-core/           # Core primitives
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── types/
│   │       ├── crypto/
│   │       └── zeroize/
│   │
│   ├── teras-effect/         # Effect system runtime
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── capability.rs
│   │       ├── proof_bundle.rs
│   │       └── effect_gate.rs
│   │
│   ├── teras-lang-lexer/     # TERAS-LANG lexer
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   │
│   ├── teras-lang-parser/    # TERAS-LANG parser
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   │
│   ├── teras-lang-types/     # TERAS-LANG type system
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   │
│   ├── teras-lang-codegen/   # TERAS-LANG code generator
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── lib.rs
│   │
│   ├── terasc/               # TERAS-LANG compiler binary
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── main.rs
│   │
│   ├── teras-build/          # Build orchestrator
│   │   ├── Cargo.toml
│   │   └── src/
│   │       └── main.rs
│   │
│   └── teras-verify/         # Verification orchestrator
│       ├── Cargo.toml
│       └── src/
│           └── main.rs
│
├── tools/
│   ├── hash-chain/           # Hash chain tool
│   ├── build-manifest/       # Manifest generator
│   └── artifact-sign/        # Artifact signing
│
└── tests/
    ├── integration/          # Integration tests
    ├── verification/         # Verification tests
    └── fuzzing/              # Fuzz tests
```

## 4.2 Root Cargo.toml

```toml
# teras/Cargo.toml
# TERAS Workspace Root Configuration
# Version: 1.0.0
# 
# CRITICAL: This file defines the ENTIRE Rust workspace.
# ALL crates must be members of this workspace.
# NO external dependencies at runtime (Law 8).

[workspace]
resolver = "2"

members = [
    "crates/teras-core",
    "crates/teras-effect",
    "crates/teras-lang-lexer",
    "crates/teras-lang-parser",
    "crates/teras-lang-types",
    "crates/teras-lang-codegen",
    "crates/terasc",
    "crates/teras-build",
    "crates/teras-verify",
    "tools/hash-chain",
    "tools/build-manifest",
    "tools/artifact-sign",
]

# Exclude test crates from main build
exclude = [
    "tests/fuzzing",
]

[workspace.package]
version = "0.1.0"
edition = "2024"
rust-version = "1.84.0"
license = "PROPRIETARY"
repository = "https://internal.teras.my/git/teras"
authors = ["TERAS Team <security@teras.my>"]

[workspace.dependencies]
# =============================================================================
# INTERNAL DEPENDENCIES (from workspace)
# =============================================================================
teras-core = { path = "crates/teras-core" }
teras-effect = { path = "crates/teras-effect" }
teras-lang-lexer = { path = "crates/teras-lang-lexer" }
teras-lang-parser = { path = "crates/teras-lang-parser" }
teras-lang-types = { path = "crates/teras-lang-types" }
teras-lang-codegen = { path = "crates/teras-lang-codegen" }

# =============================================================================
# BUILD-TIME ONLY DEPENDENCIES
# =============================================================================
# These are used during build/test but NOT linked into runtime binaries

# Testing
proptest = "1.4"
criterion = "0.5"
arbitrary = "1.3"

# Verification (build-time only)
kani-verifier = { version = "0.50", optional = true }

# Serialization (build-time configuration only)
serde = { version = "1.0", features = ["derive"] }
toml = "0.8"

# Async runtime (build tools only)
tokio = { version = "1.36", features = ["full"] }

# CLI (build tools only)
clap = { version = "4.5", features = ["derive"] }

# =============================================================================
# RUNTIME DEPENDENCIES — ZERO EXTERNAL
# =============================================================================
# Per Law 8: ZERO third-party runtime dependencies.
# All runtime code is implemented from scratch in the workspace.

[workspace.lints.rust]
# Strictest warnings
unsafe_code = "deny"
missing_docs = "warn"
trivial_casts = "warn"
trivial_numeric_casts = "warn"
unused_results = "warn"
unused_lifetimes = "warn"
unused_qualifications = "warn"

[workspace.lints.clippy]
# Enable all clippy lints
all = "warn"
pedantic = "warn"
nursery = "warn"
cargo = "warn"

# Deny dangerous patterns
unwrap_used = "deny"
expect_used = "deny"
panic = "deny"
unreachable = "deny"
todo = "deny"
unimplemented = "deny"
dbg_macro = "deny"
print_stdout = "deny"
print_stderr = "deny"

[profile.dev]
opt-level = 0
debug = true
debug-assertions = true
overflow-checks = true
lto = false
panic = "unwind"
incremental = true

[profile.release]
opt-level = 3
debug = false
debug-assertions = false
overflow-checks = true  # Keep for safety
lto = "fat"
panic = "abort"
codegen-units = 1
strip = "symbols"

[profile.test]
opt-level = 1
debug = true
debug-assertions = true
overflow-checks = true

[profile.paranoid]
inherits = "release"
overflow-checks = true
debug-assertions = true  # Enable assertions even in release
lto = "fat"
codegen-units = 1
```

## 4.3 Rust Toolchain Configuration

```toml
# rust-toolchain.toml
# Pinned Rust version for reproducible builds

[toolchain]
channel = "1.84.0"
profile = "complete"
components = [
    "rustc",
    "cargo",
    "rust-std",
    "rust-src",           # For verification tools
    "rustfmt",
    "clippy",
    "miri",               # For unsafe code verification
    "rust-analyzer",      # For IDE support
    "llvm-tools-preview", # For coverage
]
targets = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "x86_64-unknown-linux-musl",    # For static linking
    "aarch64-unknown-linux-musl",   # For static linking
]
```

## 4.4 Cargo Configuration

```toml
# .cargo/config.toml
# Cargo build configuration

[build]
# Force consistent builds
jobs = 8
incremental = true
rustflags = [
    # Warnings as errors in CI
    "-Dwarnings",
    # Additional safety checks
    "-Dunsafe_code",
    # Enable all features for verification
    "-Csymbol-mangling-version=v0",
]

[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = [
    "-Clink-arg=-fuse-ld=lld",
    "-Ctarget-feature=+crt-static",
]

[target.x86_64-unknown-linux-musl]
linker = "clang"
rustflags = [
    "-Clink-arg=-fuse-ld=lld",
    "-Ctarget-feature=+crt-static",
]

[env]
# Reproducible builds
SOURCE_DATE_EPOCH = "0"
CARGO_INCREMENTAL = "0"
RUSTFLAGS = "-Cembed-bitcode=yes"

[net]
# Security: require locked dependencies
offline = false

[http]
# Security: enable certificate verification
check-revoke = true
ssl-version = "tlsv1.3"

[registries.crates-io]
# Disable default registry for runtime deps
# All runtime code is local

[alias]
# Custom aliases
b = "build"
t = "test"
c = "check"
verify = "run --package teras-verify --"
build-all = "build --workspace --all-targets"
test-all = "test --workspace --all-targets"
```

## 4.5 Formatting Configuration

```toml
# rustfmt.toml
# Rust formatting configuration

# Stable options
edition = "2024"
max_width = 100
tab_spaces = 4
newline_style = "Unix"
use_small_heuristics = "Max"

# Import organization
imports_granularity = "Module"
group_imports = "StdExternalCrate"
reorder_imports = true
reorder_modules = true

# Comment handling
normalize_comments = true
normalize_doc_attributes = true
wrap_comments = true
format_code_in_doc_comments = true

# Misc
format_strings = true
format_macro_matchers = true
format_macro_bodies = true
hex_literal_case = "Upper"
```

## 4.6 Clippy Configuration

```toml
# clippy.toml
# Clippy lint configuration

# Complexity thresholds
cognitive-complexity-threshold = 25
too-many-arguments-threshold = 7
too-many-lines-threshold = 100
type-complexity-threshold = 250

# Naming requirements  
doc-valid-idents = ["TERAS", "TERAS-LANG", "IFC", "PQ", "HSM", "TPM"]

# Disallowed patterns
disallowed-methods = [
    { path = "std::process::exit", reason = "Use proper error handling" },
    { path = "std::panic::catch_unwind", reason = "Avoid panic-based flow" },
]

disallowed-types = [
    { path = "std::collections::HashMap", reason = "Use BTreeMap for determinism" },
    { path = "std::collections::HashSet", reason = "Use BTreeSet for determinism" },
]

# Security
msrv = "1.84.0"
```

## 4.7 Dependency Policy (deny.toml)

```toml
# deny.toml
# cargo-deny configuration

[graph]
targets = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
]

[advisories]
vulnerability = "deny"
unmaintained = "deny"
yanked = "deny"
ignore = []

[licenses]
unlicensed = "deny"
copyleft = "deny"
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-2-Clause",
    "BSD-3-Clause",
    "ISC",
    "Zlib",
    "0BSD",
]
confidence-threshold = 0.8

[bans]
multiple-versions = "deny"
wildcards = "deny"
highlight = "all"
workspace-default-features = "allow"
external-default-features = "allow"

# No duplicate dependencies
deny = []

# Skip specific versions (with justification)
skip = []

[sources]
unknown-registry = "deny"
unknown-git = "deny"
allow-registry = ["https://github.com/rust-lang/crates.io-index"]
allow-git = []
```

---

# 5. ADA/SPARK BUILD INTEGRATION

## 5.1 GPR Project Structure

```
teras-ada/
├── teras.gpr                  # Root project file
├── gnatprove.adc             # SPARK configuration
├── gnatcheck.rules           # Style rules
│
├── src/
│   ├── teras.ads             # Root package spec
│   ├── teras.adb             # Root package body
│   │
│   ├── teras-crypto/         # Cryptographic operations
│   │   ├── teras-crypto.ads
│   │   ├── teras-crypto.adb
│   │   ├── teras-crypto-aes.ads
│   │   ├── teras-crypto-aes.adb
│   │   ├── teras-crypto-sha3.ads
│   │   ├── teras-crypto-sha3.adb
│   │   ├── teras-crypto-ml_kem.ads
│   │   ├── teras-crypto-ml_kem.adb
│   │   ├── teras-crypto-ml_dsa.ads
│   │   └── teras-crypto-ml_dsa.adb
│   │
│   ├── teras-effect/         # Effect Gate runtime
│   │   ├── teras-effect.ads
│   │   ├── teras-effect.adb
│   │   ├── teras-effect-capability.ads
│   │   ├── teras-effect-capability.adb
│   │   ├── teras-effect-proof_bundle.ads
│   │   └── teras-effect-proof_bundle.adb
│   │
│   └── teras-timing/         # Constant-time operations
│       ├── teras-timing.ads
│       └── teras-timing.adb
│
├── tests/
│   ├── teras_tests.gpr       # Test project
│   └── src/
│       └── ...
│
└── proofs/
    ├── lemmas/               # Manual proof lemmas
    └── user_profiles/        # User proof profiles
```

## 5.2 GPR Project File

```ada
-- teras.gpr
-- TERAS Ada/SPARK Project Configuration
-- Version: 1.0.0

project TERAS is

   -- Project type
   type Build_Mode is ("dev", "test", "release", "paranoid");
   Mode : Build_Mode := external ("TERAS_BUILD_MODE", "dev");

   -- Source directories
   for Source_Dirs use ("src/**");
   for Object_Dir use "obj/" & Mode;
   for Exec_Dir use "bin/" & Mode;
   
   -- Main programs (if any)
   for Main use ();

   -- Language configuration
   for Languages use ("Ada");

   -- Compiler configuration
   package Compiler is
      Common_Switches := (
         "-gnatwa",        -- All warnings
         "-gnatyy",        -- Style checks
         "-gnatwe",        -- Warnings as errors
         "-gnata",         -- Enable assertions
         "-gnat2022",      -- Ada 2022
         "-gnatX"          -- Language extensions
      );

      case Mode is
         when "dev" =>
            for Default_Switches ("Ada") use Common_Switches & (
               "-g",         -- Debug info
               "-O0",        -- No optimization
               "-gnateE"     -- Extra exception info
            );

         when "test" =>
            for Default_Switches ("Ada") use Common_Switches & (
               "-g",         -- Debug info
               "-O1",        -- Basic optimization
               "-fstack-check"
            );

         when "release" =>
            for Default_Switches ("Ada") use Common_Switches & (
               "-O3",        -- Full optimization
               "-gnatn",     -- Inline across units
               "-fdata-sections",
               "-ffunction-sections"
            );

         when "paranoid" =>
            for Default_Switches ("Ada") use Common_Switches & (
               "-O3",        -- Full optimization
               "-gnatn",     -- Inline across units
               "-gnateV",    -- Validity checking
               "-gnatVa",    -- All validity checks
               "-fstack-check"
            );
      end case;
   end Compiler;

   -- Binder configuration
   package Binder is
      for Default_Switches ("Ada") use ("-Es"); -- Static elaboration
   end Binder;

   -- Linker configuration
   package Linker is
      case Mode is
         when "release" | "paranoid" =>
            for Default_Switches ("Ada") use (
               "-Wl,--gc-sections",
               "-static"
            );
         when others =>
            null;
      end case;
   end Linker;

   -- Prove configuration (SPARK)
   package Prove is
      for Proof_Switches ("Ada") use (
         "--level=4",           -- Highest proof level
         "--prover=cvc5,z3,alt-ergo",
         "--timeout=60",
         "--memlimit=4000",
         "--steps=10000",
         "--counterexamples=on",
         "--proof-warnings=on"
      );
   end Prove;

   -- Documentation
   package Documentation is
      for Documentation_Dir use "doc";
   end Documentation;

end TERAS;
```

## 5.3 SPARK Configuration

```ada
-- gnatprove.adc
-- SPARK Prover Configuration

-- Enable all SPARK checks
pragma SPARK_Mode (On);

-- Assertion policy
pragma Assertion_Policy (Check);
pragma Assertion_Policy (Pre => Check);
pragma Assertion_Policy (Post => Check);
pragma Assertion_Policy (Contract_Cases => Check);
pragma Assertion_Policy (Loop_Invariant => Check);
pragma Assertion_Policy (Loop_Variant => Check);

-- Overflow checking
pragma Overflow_Mode (General => Strict, Assertions => Eliminated);

-- Initialize scalars for security
pragma Initialize_Scalars;

-- Restrictions for verification
pragma Restrictions (No_Abort_Statements);
pragma Restrictions (No_Asynchronous_Control);
pragma Restrictions (No_Dynamic_Attachment);
pragma Restrictions (No_Exception_Propagation);
pragma Restrictions (No_Task_Allocators);
pragma Restrictions (No_Task_Hierarchy);
pragma Restrictions (No_Unchecked_Deallocation);
pragma Restrictions (No_Implicit_Heap_Allocations);
pragma Restrictions (No_Secondary_Stack);
pragma Restrictions (Static_Storage_Size);
pragma Restrictions (Max_Asynchronous_Select_Nesting => 0);
pragma Restrictions (Max_Protected_Entries => 0);
pragma Restrictions (Max_Select_Alternatives => 0);
pragma Restrictions (Max_Task_Entries => 0);
pragma Restrictions (Max_Tasks => 0);
```

---

# 6. TERAS-LANG BUILD PIPELINE

## 6.1 Build Pipeline Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      TERAS-LANG BUILD PIPELINE                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌────────────────────────────────────────────────────────────────────┐    │
│  │                     STAGE 0: BOOTSTRAP                             │    │
│  │  ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌───────────┐      │    │
│  │  │   Rust    │  │   Rust    │  │   Rust    │  │   Rust    │      │    │
│  │  │   Lexer   │──│   Parser  │──│   Type    │──│  CodeGen  │      │    │
│  │  │           │  │           │  │  Checker  │  │   (LLVM)  │      │    │
│  │  └───────────┘  └───────────┘  └───────────┘  └───────────┘      │    │
│  │       │                                             │             │    │
│  │       └─────────────────────────────────────────────┘             │    │
│  │                           │                                        │    │
│  │                           ▼                                        │    │
│  │                  ┌─────────────────┐                              │    │
│  │                  │   terasc-stage0 │  (Rust binary)               │    │
│  │                  └─────────────────┘                              │    │
│  └────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│  ┌────────────────────────────────────────────────────────────────────┐    │
│  │                     STAGE 1: SELF-HOST                             │    │
│  │  ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌───────────┐      │    │
│  │  │  TERAS    │  │  TERAS    │  │  TERAS    │  │  TERAS    │      │    │
│  │  │   Lexer   │──│   Parser  │──│   Type    │──│  CodeGen  │      │    │
│  │  │   (.trs)  │  │   (.trs)  │  │  Checker  │  │   (.trs)  │      │    │
│  │  └───────────┘  └───────────┘  └───────────┘  └───────────┘      │    │
│  │       │              │              │              │              │    │
│  │       └──────────────┴──────────────┴──────────────┘              │    │
│  │                           │                                        │    │
│  │                    compiled by                                     │    │
│  │                    terasc-stage0                                   │    │
│  │                           │                                        │    │
│  │                           ▼                                        │    │
│  │                  ┌─────────────────┐                              │    │
│  │                  │   terasc-stage1 │                              │    │
│  │                  └─────────────────┘                              │    │
│  └────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│  ┌────────────────────────────────────────────────────────────────────┐    │
│  │                     STAGE 2: VERIFY                                │    │
│  │                                                                    │    │
│  │  Compile same source with terasc-stage1 → terasc-stage2           │    │
│  │                                                                    │    │
│  │  ┌─────────────────────────────────────────────────────────────┐  │    │
│  │  │                    VERIFICATION                              │  │    │
│  │  │  ├── Compare terasc-stage1 == terasc-stage2 (bit-for-bit)   │  │    │
│  │  │  ├── If match: terasc is verified self-hosting               │  │    │
│  │  │  └── If mismatch: HALT — bootstrap chain broken              │  │    │
│  │  └─────────────────────────────────────────────────────────────┘  │    │
│  └────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│                    ┌─────────────────┐                                     │
│                    │  terasc-verified │  (Production compiler)             │
│                    └─────────────────┘                                     │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## 6.2 Build Configuration

```toml
# teras-lang-build.toml
# TERAS-LANG compiler build configuration

[bootstrap]
# Stage 0: Rust bootstrap compiler
stage0_source = "crates/terasc"
stage0_output = "target/release/terasc-stage0"
stage0_verification = ["kani", "miri"]

[self_host]
# Stage 1: Self-hosted compiler
stage1_source = "teras-lang/compiler/"
stage1_output = "target/teras/terasc-stage1"
stage1_compiler = "terasc-stage0"
stage1_verification = ["type-check", "effect-check"]

[verify]
# Stage 2: Verification build
stage2_source = "teras-lang/compiler/"
stage2_output = "target/teras/terasc-stage2"
stage2_compiler = "terasc-stage1"
stage2_verification = ["bit-for-bit"]

[final]
# Production compiler
production_compiler = "terasc-stage1"  # After stage2 verification passes
production_output = "target/release/terasc"

[verification_levels]
level0 = ["syntax"]
level1 = ["syntax", "type-check"]
level2 = ["syntax", "type-check", "ifc-check"]
level3 = ["syntax", "type-check", "ifc-check", "effect-check"]
level4 = ["syntax", "type-check", "ifc-check", "effect-check", "capability-check"]
level5 = ["syntax", "type-check", "ifc-check", "effect-check", "capability-check", "proof-gen"]
level6 = ["syntax", "type-check", "ifc-check", "effect-check", "capability-check", "proof-gen", "proof-verify"]

default_level = "level4"
ci_level = "level5"
release_level = "level6"
```

---

# 7. HARDWARE BUILD INTEGRATION

## 7.1 HDL Build Structure

```
teras-hw/
├── teras-hw.toml              # Hardware build configuration
│
├── rtl/
│   ├── effect_gate/           # Effect Gate RTL
│   │   ├── effect_gate.sv     # Top module
│   │   ├── capability_checker.sv
│   │   ├── proof_verifier.sv
│   │   └── crypto_engine.sv
│   │
│   ├── crypto/                # Crypto accelerators
│   │   ├── aes_engine.sv
│   │   ├── sha3_engine.sv
│   │   ├── ml_kem_engine.sv
│   │   └── ml_dsa_engine.sv
│   │
│   └── common/                # Shared components
│       ├── fifos.sv
│       ├── arbiter.sv
│       └── sync.sv
│
├── constraints/
│   ├── timing.sdc             # Timing constraints
│   ├── pinout.lpf             # Pin assignments
│   └── power.upf              # Power constraints
│
├── testbench/
│   ├── tb_effect_gate.sv
│   ├── tb_crypto.sv
│   └── helpers/
│
├── formal/
│   ├── properties.sv          # SVA properties
│   ├── assume.sv              # Assumptions
│   └── cover.sv               # Cover properties
│
└── targets/
    ├── ecp5/                  # ECP5 FPGA target
    ├── ice40/                 # iCE40 FPGA target
    └── sim/                   # Simulation target
```

## 7.2 Hardware Build Configuration

```toml
# teras-hw.toml
# TERAS Hardware Build Configuration

[project]
name = "teras-hw"
version = "0.1.0"
top_module = "effect_gate"

[sources]
rtl = ["rtl/**/*.sv", "rtl/**/*.v"]
constraints = ["constraints/*.sdc", "constraints/*.lpf"]
testbench = ["testbench/**/*.sv"]
formal = ["formal/**/*.sv"]

[simulation]
tool = "verilator"
options = ["--timing", "--trace-fst", "--coverage"]
top = "tb_effect_gate"

[synthesis]
tool = "yosys"
target = "ecp5"
options = ["-json", "-abc9"]

[place_and_route]
tool = "nextpnr"
target = "ecp5"
device = "um5g-85k"
package = "CABGA381"
options = ["--timing-allow-fail"]

[formal_verification]
tool = "symbiyosys"
engine = ["smtbmc", "boolector"]
depth = 50
timeout = 3600

[verification_levels]
level0 = ["lint"]
level1 = ["lint", "simulate"]
level2 = ["lint", "simulate", "coverage"]
level3 = ["lint", "simulate", "coverage", "formal-bmc"]
level4 = ["lint", "simulate", "coverage", "formal-bmc", "formal-prove"]
level5 = ["lint", "simulate", "coverage", "formal-bmc", "formal-prove", "timing"]

default_level = "level2"
ci_level = "level4"
release_level = "level5"

[lint]
tool = "verilator"
options = ["--lint-only", "-Wall", "-Werror"]

[coverage]
types = ["line", "branch", "condition", "toggle"]
threshold = 95
```

---

# 8. REPRODUCIBLE BUILD SPECIFICATION

## 8.1 Reproducibility Requirements

```
REPRODUCIBLE BUILD REQUIREMENTS:

1. DETERMINISTIC COMPILATION
   ├── Same source → Same binary (bit-for-bit)
   ├── No timestamps in binaries
   ├── No random data in binaries
   ├── Deterministic ordering of operations
   └── Reproducible across machines

2. HERMETIC BUILDS
   ├── No network access during build
   ├── No access to system time
   ├── No access to random sources
   ├── All dependencies locked
   └── Environment fully specified

3. VERIFIABLE BUILDS
   ├── Build manifest includes all inputs
   ├── Output hashes recorded
   ├── Rebuild verification possible
   └── Third-party verification possible

4. AUDITABLE BUILDS
   ├── Complete log of all operations
   ├── All tools versioned
   ├── All dependencies hashed
   └── Chain of custody maintained
```

## 8.2 Build Manifest Format

```json
{
  "manifest_version": "1.0.0",
  "build_id": "build-2026-01-03-001",
  "timestamp": "2026-01-03T12:00:00Z",
  
  "inputs": {
    "source": {
      "commit": "abc123def456...",
      "tree_hash": "sha256:...",
      "files": [
        {
          "path": "src/main.rs",
          "hash": "sha256:..."
        }
      ]
    },
    "dependencies": [
      {
        "name": "rustc",
        "version": "1.84.0",
        "hash": "sha256:..."
      },
      {
        "name": "cargo",
        "version": "1.84.0",
        "hash": "sha256:..."
      }
    ],
    "environment": {
      "RUSTFLAGS": "-Cembed-bitcode=yes",
      "SOURCE_DATE_EPOCH": "0"
    }
  },
  
  "build": {
    "command": "cargo build --release --locked",
    "duration_seconds": 120,
    "success": true
  },
  
  "outputs": [
    {
      "path": "target/release/terasc",
      "hash": "sha256:...",
      "size": 12345678
    }
  ],
  
  "verification": {
    "reproducible": true,
    "rebuild_hash": "sha256:...",
    "verified_by": "teras-verify v1.0.0"
  },
  
  "signatures": [
    {
      "signer": "build-system",
      "algorithm": "ed25519",
      "signature": "base64:..."
    }
  ]
}
```

## 8.3 Reproducibility Verification Script

```bash
#!/bin/bash
# verify-reproducibility.sh
# Verifies that a build is reproducible

set -euo pipefail

BUILD_MANIFEST="$1"
REBUILD_DIR="$(mktemp -d)"

echo "=== TERAS Reproducibility Verification ==="
echo "Manifest: $BUILD_MANIFEST"
echo "Rebuild directory: $REBUILD_DIR"

# Extract source commit from manifest
COMMIT=$(jq -r '.inputs.source.commit' "$BUILD_MANIFEST")
echo "Source commit: $COMMIT"

# Clone source at exact commit
git clone --depth 1 --branch "$COMMIT" https://internal.teras.my/git/teras "$REBUILD_DIR/source"

# Set environment from manifest
export SOURCE_DATE_EPOCH=0
export CARGO_INCREMENTAL=0

# Rebuild
cd "$REBUILD_DIR/source"
cargo build --release --locked

# Compare hashes
ORIGINAL_HASH=$(jq -r '.outputs[0].hash' "$BUILD_MANIFEST")
REBUILD_HASH=$(sha256sum target/release/terasc | cut -d' ' -f1)

echo "Original hash: $ORIGINAL_HASH"
echo "Rebuild hash:  sha256:$REBUILD_HASH"

if [ "sha256:$REBUILD_HASH" = "$ORIGINAL_HASH" ]; then
    echo "✓ BUILD IS REPRODUCIBLE"
    exit 0
else
    echo "✗ BUILD IS NOT REPRODUCIBLE"
    exit 1
fi
```

---

# 9. BUILD SECURITY REQUIREMENTS

## 9.1 Security Controls

```
BUILD SECURITY CONTROLS:

1. ACCESS CONTROL
   ├── Role-based access to build systems
   ├── Multi-factor authentication required
   ├── Principle of least privilege
   ├── Separation of duties (build vs. deploy)
   └── Audit logging of all access

2. INPUT VALIDATION
   ├── All sources verified against expected hashes
   ├── All dependencies verified against lock files
   ├── No user-controlled paths in build
   ├── No arbitrary code execution in config
   └── Schema validation for all config files

3. ENVIRONMENT ISOLATION
   ├── Builds run in isolated containers
   ├── No network access during build
   ├── No persistent state between builds
   ├── Ephemeral build environments
   └── Resource limits enforced

4. OUTPUT VERIFICATION
   ├── All outputs hashed
   ├── All outputs signed
   ├── Provenance metadata attached
   ├── Tamper detection enabled
   └── Chain of custody maintained

5. SECRET MANAGEMENT
   ├── No secrets in source code
   ├── No secrets in build logs
   ├── Secrets injected at runtime only
   ├── Secrets rotated regularly
   └── Secrets access audited
```

## 9.2 Threat Model for Build System

```
THREAT MODEL:

THREAT 1: SOURCE TAMPERING
├── Attack: Attacker modifies source before build
├── Mitigation: 
│   ├── Signed commits required
│   ├── Source hash verification
│   └── Code review required
└── Detection: Hash mismatch

THREAT 2: DEPENDENCY POISONING
├── Attack: Attacker substitutes malicious dependency
├── Mitigation:
│   ├── Locked dependency versions
│   ├── Dependency hash verification
│   ├── No runtime third-party deps
│   └── Vendored dependencies
└── Detection: Hash mismatch, cargo-deny

THREAT 3: BUILD SYSTEM COMPROMISE
├── Attack: Attacker compromises build infrastructure
├── Mitigation:
│   ├── Ephemeral build environments
│   ├── Reproducible builds
│   ├── Multiple independent builds
│   └── Hardware-backed signing
└── Detection: Reproducibility verification failure

THREAT 4: COMPILER TROJAN
├── Attack: Attacker installs trojan in compiler
├── Mitigation:
│   ├── Diverse double-compilation
│   ├── Multiple compiler versions
│   ├── Binary comparison
│   └── Bootstrapping verification
└── Detection: Binary mismatch across compilers

THREAT 5: OUTPUT TAMPERING
├── Attack: Attacker modifies build outputs
├── Mitigation:
│   ├── Signed outputs
│   ├── Content-addressed storage
│   ├── Signature verification required
│   └── Provenance verification
└── Detection: Signature verification failure
```

---

# 10. HASH CHAIN TOOLING

## 10.1 Hash Chain Tool Specification

```
TOOL: teras-hash-chain
PURPOSE: Maintain cryptographic integrity chain for all TERAS documents

COMMANDS:
├── init         Initialize new hash chain
├── add          Add document to chain
├── verify       Verify chain integrity
├── show         Display chain status
├── export       Export chain to file
└── import       Import chain from file

USAGE:
├── teras-hash-chain init --chain-name <name>
├── teras-hash-chain add --file <path> [--predecessor <hash>]
├── teras-hash-chain verify [--deep]
├── teras-hash-chain show [--format <json|text>]
├── teras-hash-chain export --output <path>
└── teras-hash-chain import --input <path>

CHAIN ENTRY FORMAT:
{
  "document_id": "TRACK_F-TOOL-BUILD_v1_0_0.md",
  "sha256": "abc123...",
  "predecessor": "def456...",
  "timestamp": "2026-01-03T12:00:00Z",
  "author": "Track F",
  "signature": "base64:..."
}

CHAIN VERIFICATION:
├── Verify each entry's hash matches document
├── Verify predecessor chain is unbroken
├── Verify signatures are valid
├── Verify timestamps are monotonic
└── Verify no missing entries
```

## 10.2 Hash Chain Tool Implementation

```rust
// tools/hash-chain/src/main.rs
// TERAS Hash Chain Tool
// Version: 1.0.0

use std::fs;
use std::path::PathBuf;
use sha2::{Sha256, Digest};
use serde::{Serialize, Deserialize};
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "teras-hash-chain")]
#[command(about = "TERAS document hash chain management")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Initialize a new hash chain
    Init {
        #[arg(long)]
        chain_name: String,
    },
    /// Add a document to the chain
    Add {
        #[arg(long)]
        file: PathBuf,
        #[arg(long)]
        predecessor: Option<String>,
    },
    /// Verify chain integrity
    Verify {
        #[arg(long)]
        deep: bool,
    },
    /// Show chain status
    Show {
        #[arg(long, default_value = "text")]
        format: String,
    },
}

#[derive(Serialize, Deserialize, Clone)]
struct ChainEntry {
    document_id: String,
    sha256: String,
    predecessor: Option<String>,
    timestamp: String,
    author: String,
    signature: Option<String>,
}

#[derive(Serialize, Deserialize)]
struct HashChain {
    name: String,
    created: String,
    entries: Vec<ChainEntry>,
}

fn compute_sha256(path: &PathBuf) -> Result<String, std::io::Error> {
    let contents = fs::read(path)?;
    let mut hasher = Sha256::new();
    hasher.update(&contents);
    let result = hasher.finalize();
    Ok(format!("{:x}", result))
}

fn main() {
    let cli = Cli::parse();
    
    match cli.command {
        Commands::Init { chain_name } => {
            println!("Initializing hash chain: {}", chain_name);
            let chain = HashChain {
                name: chain_name,
                created: chrono::Utc::now().to_rfc3339(),
                entries: Vec::new(),
            };
            let json = serde_json::to_string_pretty(&chain).unwrap();
            fs::write("teras-hash-chain.json", json).unwrap();
            println!("Hash chain initialized successfully.");
        }
        Commands::Add { file, predecessor } => {
            println!("Adding document: {:?}", file);
            let hash = compute_sha256(&file).unwrap();
            let entry = ChainEntry {
                document_id: file.file_name().unwrap().to_string_lossy().to_string(),
                sha256: hash.clone(),
                predecessor,
                timestamp: chrono::Utc::now().to_rfc3339(),
                author: "Track F".to_string(),
                signature: None,
            };
            
            let mut chain: HashChain = serde_json::from_str(
                &fs::read_to_string("teras-hash-chain.json").unwrap()
            ).unwrap();
            chain.entries.push(entry);
            fs::write("teras-hash-chain.json", 
                serde_json::to_string_pretty(&chain).unwrap()
            ).unwrap();
            
            println!("Document added with hash: {}", hash);
        }
        Commands::Verify { deep } => {
            println!("Verifying hash chain integrity...");
            let chain: HashChain = serde_json::from_str(
                &fs::read_to_string("teras-hash-chain.json").unwrap()
            ).unwrap();
            
            let mut errors = 0;
            for entry in &chain.entries {
                if deep {
                    // Verify document hash matches
                    let path = PathBuf::from(&entry.document_id);
                    if path.exists() {
                        let computed = compute_sha256(&path).unwrap();
                        if computed != entry.sha256 {
                            println!("✗ Hash mismatch for {}", entry.document_id);
                            errors += 1;
                        } else {
                            println!("✓ {} verified", entry.document_id);
                        }
                    } else {
                        println!("⚠ File not found: {}", entry.document_id);
                    }
                }
            }
            
            if errors == 0 {
                println!("✓ Hash chain verified successfully");
            } else {
                println!("✗ {} errors found", errors);
                std::process::exit(1);
            }
        }
        Commands::Show { format } => {
            let chain: HashChain = serde_json::from_str(
                &fs::read_to_string("teras-hash-chain.json").unwrap()
            ).unwrap();
            
            if format == "json" {
                println!("{}", serde_json::to_string_pretty(&chain).unwrap());
            } else {
                println!("Hash Chain: {}", chain.name);
                println!("Created: {}", chain.created);
                println!("Entries: {}", chain.entries.len());
                println!();
                for entry in &chain.entries {
                    println!("  {} → {}", 
                        &entry.sha256[..16], 
                        entry.document_id
                    );
                }
            }
        }
    }
}
```

---

# 11. CI/CD FOUNDATION CONFIGURATION

## 11.1 CI/CD Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           TERAS CI/CD SYSTEM                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌────────────────────────────────────────────────────────────────────┐    │
│  │                        SOURCE CONTROL                               │    │
│  │  ├── Self-hosted Git server                                         │    │
│  │  ├── Signed commits required                                        │    │
│  │  ├── Protected branches (main, release/*)                          │    │
│  │  └── Pull request required for all changes                          │    │
│  └────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│               ┌──────────────┼──────────────┐                              │
│               │              │              │                               │
│               ▼              ▼              ▼                               │
│  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐               │
│  │   COMMIT       │  │   PULL         │  │   RELEASE      │               │
│  │   PIPELINE     │  │   REQUEST      │  │   PIPELINE     │               │
│  │                │  │   PIPELINE     │  │                │               │
│  │ ├── Build      │  │ ├── All of     │  │ ├── All of     │               │
│  │ ├── Unit test  │  │ │   commit     │  │ │   PR         │               │
│  │ ├── Lint       │  │ ├── Property   │  │ ├── Full       │               │
│  │ ├── Format     │  │ │   tests      │  │ │   verification│              │
│  │ └── Quick      │  │ ├── Verify     │  │ ├── Fuzzing    │               │
│  │    verify      │  │ │   level 4    │  │ ├── Mutation   │               │
│  │                │  │ ├── Security   │  │ ├── Sign       │               │
│  │                │  │ │   scan       │  │ ├── SBOM       │               │
│  │                │  │ └── Cross-     │  │ └── Deploy     │               │
│  │                │  │    track check │  │                │               │
│  └────────────────┘  └────────────────┘  └────────────────┘               │
│         │                    │                    │                         │
│         └────────────────────┼────────────────────┘                        │
│                              │                                              │
│                              ▼                                              │
│  ┌────────────────────────────────────────────────────────────────────┐    │
│  │                      BUILD RUNNERS                                  │    │
│  │  ├── Self-hosted (security requirement)                            │    │
│  │  ├── Ephemeral containers                                          │    │
│  │  ├── Network isolated                                              │    │
│  │  ├── Resource limited                                              │    │
│  │  └── Audit logged                                                  │    │
│  └────────────────────────────────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│  ┌────────────────────────────────────────────────────────────────────┐    │
│  │                      ARTIFACT STORAGE                               │    │
│  │  ├── Content-addressed                                              │    │
│  │  ├── Signed artifacts                                               │    │
│  │  ├── Immutable storage                                              │    │
│  │  └── Provenance metadata                                            │    │
│  └────────────────────────────────────────────────────────────────────┘    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## 11.2 CI Configuration

```yaml
# .teras-ci/pipeline.yaml
# TERAS CI/CD Pipeline Configuration

version: "1.0"

# Common configuration
common:
  image: teras-build:latest
  timeout: 60m
  retry: 2
  
  environment:
    SOURCE_DATE_EPOCH: "0"
    CARGO_INCREMENTAL: "0"
    RUSTFLAGS: "-Dwarnings"

# Trigger rules
triggers:
  commit:
    branches: ["*"]
    pipeline: commit-pipeline
    
  pull_request:
    branches: ["main", "release/*"]
    pipeline: pr-pipeline
    
  release:
    tags: ["v*"]
    pipeline: release-pipeline

# Pipeline definitions
pipelines:
  commit-pipeline:
    stages:
      - name: build
        jobs:
          - name: build-rust
            script:
              - cargo build --workspace --all-targets
              
          - name: build-ada
            script:
              - gprbuild -P teras.gpr -XTERAS_BUILD_MODE=dev
              
      - name: test
        depends_on: [build]
        jobs:
          - name: test-rust
            script:
              - cargo test --workspace
              
          - name: test-ada
            script:
              - gprbuild -P teras_tests.gpr
              - ./run_tests.sh
              
      - name: lint
        parallel: true
        jobs:
          - name: clippy
            script:
              - cargo clippy --workspace -- -D warnings
              
          - name: rustfmt
            script:
              - cargo fmt --check
              
          - name: gnatcheck
            script:
              - gnatcheck -P teras.gpr -rules -from=gnatcheck.rules
              
      - name: quick-verify
        depends_on: [test, lint]
        jobs:
          - name: miri
            script:
              - cargo +nightly miri test --workspace
              
  pr-pipeline:
    stages:
      - name: commit-checks
        include: commit-pipeline
        
      - name: property-tests
        depends_on: [commit-checks]
        jobs:
          - name: proptest
            script:
              - cargo test --workspace --features proptest
              
      - name: verification
        depends_on: [property-tests]
        jobs:
          - name: kani
            script:
              - cargo kani --workspace
              
          - name: gnatprove
            script:
              - gnatprove -P teras.gpr --level=4
              
      - name: security
        parallel: true
        jobs:
          - name: cargo-deny
            script:
              - cargo deny check
              
          - name: cargo-audit
            script:
              - cargo audit
              
      - name: cross-track
        depends_on: [verification, security]
        jobs:
          - name: validate-coordination
            script:
              - teras-hash-chain verify --deep
              
  release-pipeline:
    stages:
      - name: pr-checks
        include: pr-pipeline
        
      - name: full-verification
        depends_on: [pr-checks]
        timeout: 4h
        jobs:
          - name: verus
            script:
              - cargo verus --workspace
              
          - name: creusot
            script:
              - cargo creusot --workspace
              
          - name: prusti
            script:
              - cargo prusti --workspace
              
          - name: gnatprove-platinum
            script:
              - gnatprove -P teras.gpr --level=4 --prover=all
              
      - name: fuzzing
        depends_on: [full-verification]
        timeout: 2h
        jobs:
          - name: fuzz
            script:
              - cargo +nightly fuzz run --release -- -max_total_time=7200
              
      - name: mutation
        depends_on: [full-verification]
        jobs:
          - name: mutants
            script:
              - cargo mutants --workspace
              
      - name: package
        depends_on: [fuzzing, mutation]
        jobs:
          - name: build-release
            script:
              - cargo build --release --locked
              - gprbuild -P teras.gpr -XTERAS_BUILD_MODE=release
              
          - name: generate-sbom
            script:
              - cargo sbom --output=sbom.json
              
          - name: sign
            script:
              - teras-sign --input=target/release/* --output=artifacts/
              
          - name: manifest
            script:
              - teras-build-manifest generate --output=manifest.json
              
      - name: deploy
        depends_on: [package]
        manual: true
        jobs:
          - name: deploy-test
            script:
              - teras-deploy --env=test --artifacts=artifacts/
```

---

# 12. DEVELOPMENT ENVIRONMENT SETUP

## 12.1 Development Container

```dockerfile
# Dockerfile.dev
# TERAS Development Container
# Version: 1.0.0

FROM ubuntu:24.04

# Metadata
LABEL maintainer="TERAS Team <security@teras.my>"
LABEL version="1.0.0"
LABEL description="TERAS Development Environment"

# Environment
ENV DEBIAN_FRONTEND=noninteractive
ENV LANG=C.UTF-8
ENV LC_ALL=C.UTF-8
ENV RUSTUP_HOME=/usr/local/rustup
ENV CARGO_HOME=/usr/local/cargo
ENV PATH=/usr/local/cargo/bin:$PATH

# System packages
RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    git \
    pkg-config \
    libssl-dev \
    clang \
    lld \
    llvm \
    cmake \
    ninja-build \
    python3 \
    python3-pip \
    gnat \
    gprbuild \
    gnatprove \
    && rm -rf /var/lib/apt/lists/*

# Rust toolchain
RUN curl --proto '=https' --tlsv1.3 -sSf https://sh.rustup.rs | \
    sh -s -- -y --default-toolchain 1.84.0 --profile complete

# Rust components
RUN rustup component add \
    rustfmt \
    clippy \
    miri \
    rust-analyzer \
    rust-src \
    llvm-tools-preview

# Rust targets
RUN rustup target add \
    x86_64-unknown-linux-gnu \
    aarch64-unknown-linux-gnu \
    x86_64-unknown-linux-musl \
    aarch64-unknown-linux-musl

# Cargo tools
RUN cargo install --locked \
    cargo-deny \
    cargo-audit \
    cargo-outdated \
    cargo-bloat \
    cargo-udeps \
    cargo-llvm-cov \
    cargo-fuzz \
    cargo-mutants \
    kani-verifier

# Hardware tools (for Track E)
RUN apt-get update && apt-get install -y \
    verilator \
    yosys \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN useradd -m -s /bin/bash teras
USER teras
WORKDIR /home/teras/workspace

# Default command
CMD ["/bin/bash"]
```

## 12.2 VS Code Configuration

```json
// .vscode/settings.json
{
    "editor.formatOnSave": true,
    "editor.rulers": [100],
    "files.trimTrailingWhitespace": true,
    "files.insertFinalNewline": true,
    
    // Rust
    "rust-analyzer.check.command": "clippy",
    "rust-analyzer.cargo.features": "all",
    "rust-analyzer.procMacro.enable": true,
    "rust-analyzer.diagnostics.experimental.enable": true,
    
    // Ada
    "ada.projectFile": "teras.gpr",
    "ada.defaultCompiler": "gnat",
    
    // Extensions
    "[rust]": {
        "editor.defaultFormatter": "rust-lang.rust-analyzer"
    },
    "[ada]": {
        "editor.defaultFormatter": "adacore.ada"
    },
    "[toml]": {
        "editor.defaultFormatter": "tamasfe.even-better-toml"
    }
}
```

```json
// .vscode/extensions.json
{
    "recommendations": [
        "rust-lang.rust-analyzer",
        "tamasfe.even-better-toml",
        "serayuzgur.crates",
        "vadimcn.vscode-lldb",
        "adacore.ada",
        "ms-vscode.hexeditor",
        "mshr-h.veriloghdl"
    ]
}
```

---

# 13. BUILD VERIFICATION PROTOCOL

## 13.1 Verification Levels

```
VERIFICATION LEVEL MATRIX:

Level 0 - SYNTAX
├── Source compiles without errors
├── All dependencies resolve
└── Basic smoke test passes

Level 1 - STYLE
├── Level 0 +
├── Formatting correct (rustfmt, gnatcheck)
├── Lints pass (clippy, gnatcheck)
└── Documentation present

Level 2 - UNIT
├── Level 1 +
├── All unit tests pass
├── Unsafe code verified (miri)
└── Coverage >= 80%

Level 3 - PROPERTY
├── Level 2 +
├── Property-based tests pass (proptest)
├── Bounded model checking (kani)
└── SPARK flow analysis

Level 4 - INTEGRATION
├── Level 3 +
├── Integration tests pass
├── Cross-crate verification
├── SPARK proof (gold level)
└── Coverage >= 90%

Level 5 - FORMAL
├── Level 4 +
├── Full formal verification (verus, creusot, prusti)
├── SPARK proof (platinum level)
├── Hardware formal verification
└── Coverage >= 95%

Level 6 - PRODUCTION
├── Level 5 +
├── Reproducible build verified
├── Security audit passed
├── Penetration testing passed
├── Performance validated
└── Documentation complete
```

## 13.2 Verification Script

```bash
#!/bin/bash
# verify.sh
# TERAS Build Verification Script

set -euo pipefail

LEVEL="${1:-2}"
RESULT_FILE="verification-results.json"

echo "=== TERAS Build Verification ==="
echo "Verification Level: $LEVEL"
echo "Timestamp: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo

declare -A RESULTS
FAILURES=0

run_check() {
    local name="$1"
    local cmd="$2"
    
    echo -n "Running $name... "
    if eval "$cmd" > "/tmp/$name.log" 2>&1; then
        echo "✓ PASS"
        RESULTS["$name"]="pass"
    else
        echo "✗ FAIL"
        RESULTS["$name"]="fail"
        ((FAILURES++))
    fi
}

# Level 0 - Syntax
if [ "$LEVEL" -ge 0 ]; then
    echo "--- Level 0: Syntax ---"
    run_check "rust-build" "cargo build --workspace"
    run_check "ada-build" "gprbuild -P teras.gpr -XTERAS_BUILD_MODE=dev"
fi

# Level 1 - Style
if [ "$LEVEL" -ge 1 ]; then
    echo "--- Level 1: Style ---"
    run_check "rustfmt" "cargo fmt --check"
    run_check "clippy" "cargo clippy --workspace -- -D warnings"
    run_check "gnatcheck" "gnatcheck -P teras.gpr"
fi

# Level 2 - Unit
if [ "$LEVEL" -ge 2 ]; then
    echo "--- Level 2: Unit ---"
    run_check "rust-test" "cargo test --workspace"
    run_check "miri" "cargo +nightly miri test --workspace"
    run_check "coverage" "cargo llvm-cov --workspace --fail-under-lines 80"
fi

# Level 3 - Property
if [ "$LEVEL" -ge 3 ]; then
    echo "--- Level 3: Property ---"
    run_check "proptest" "cargo test --workspace --features proptest"
    run_check "kani" "cargo kani --workspace"
    run_check "spark-flow" "gnatprove -P teras.gpr --mode=flow"
fi

# Level 4 - Integration
if [ "$LEVEL" -ge 4 ]; then
    echo "--- Level 4: Integration ---"
    run_check "integration" "cargo test --workspace --test '*'"
    run_check "spark-gold" "gnatprove -P teras.gpr --level=2"
    run_check "coverage-90" "cargo llvm-cov --workspace --fail-under-lines 90"
fi

# Level 5 - Formal
if [ "$LEVEL" -ge 5 ]; then
    echo "--- Level 5: Formal ---"
    run_check "verus" "cargo verus --workspace"
    run_check "creusot" "cargo creusot --workspace"
    run_check "prusti" "cargo prusti --workspace"
    run_check "spark-platinum" "gnatprove -P teras.gpr --level=4"
fi

# Generate results
echo
echo "=== Results ==="
echo "Passed: $((${#RESULTS[@]} - FAILURES))/${#RESULTS[@]}"
echo "Failed: $FAILURES"

if [ "$FAILURES" -eq 0 ]; then
    echo "✓ ALL CHECKS PASSED"
    exit 0
else
    echo "✗ VERIFICATION FAILED"
    exit 1
fi
```

---

# 14. CROSS-TRACK BUILD SUPPORT

## 14.1 Track Dependencies

```
TRACK BUILD REQUIREMENTS:

TRACK A (Formal Foundations):
├── Coq 8.18+ with ssreflect, mathcomp
├── Lean 4.3+
├── Isabelle 2024
├── Z3 4.12+, CVC5 1.1+, Alt-Ergo 2.5+
└── Build: teras-build formal

TRACK B (Prototype Validation):
├── Rust 1.84+ with all verification tools
├── Ada/SPARK with GNAT 14+ and GNATprove
├── LLVM 18+
└── Build: teras-build proto

TRACK C (Specifications):
├── mdBook for documentation
├── rustdoc for API docs
├── PlantUML for diagrams
└── Build: teras-build docs

TRACK D (Adversarial Testing):
├── AFL++, libFuzzer for fuzzing
├── cargo-mutants for mutation testing
├── Valgrind, ASan, MSan for dynamic analysis
└── Build: teras-build security

TRACK E (Hardware):
├── Yosys for synthesis
├── nextpnr for place & route
├── Verilator for simulation
├── SymbiYosys for formal verification
└── Build: teras-build hardware

RESEARCH:
├── Python 3.12+ for scripts
├── Jupyter for notebooks
├── All formal prover tools
└── Build: teras-build research
```

## 14.2 Unified Build Command

```bash
# teras-build CLI
# Usage: teras-build <track> [options]

teras-build all          # Build everything
teras-build rust         # Rust crates only
teras-build ada          # Ada/SPARK only
teras-build teras-lang   # TERAS-LANG compiler
teras-build formal       # Track A formal proofs
teras-build proto        # Track B prototypes
teras-build docs         # Track C documentation
teras-build security     # Track D security tests
teras-build hardware     # Track E hardware
teras-build research     # Research tools

Options:
  --level <0-6>    Verification level (default: 2)
  --release        Release profile
  --paranoid       Paranoid profile
  --clean          Clean before build
  --verbose        Verbose output
  --parallel <n>   Parallel jobs
```

---

# 15. MONITORING AND ALERTING

## 15.1 Build Metrics

```
METRICS COLLECTED:

BUILD METRICS:
├── build_duration_seconds
├── build_success_total
├── build_failure_total
├── build_artifact_size_bytes
├── build_cache_hit_ratio
└── build_parallelism

VERIFICATION METRICS:
├── verification_duration_seconds
├── verification_pass_total
├── verification_fail_total
├── proof_obligation_count
├── proof_success_ratio
└── coverage_percentage

TEST METRICS:
├── test_duration_seconds
├── test_pass_total
├── test_fail_total
├── test_skip_total
├── mutation_kill_ratio
└── fuzz_coverage

INFRASTRUCTURE METRICS:
├── runner_utilization
├── runner_queue_depth
├── artifact_storage_bytes
├── cache_storage_bytes
└── pipeline_queue_time
```

## 15.2 Alert Rules

```yaml
# alerts.yaml
# TERAS Build System Alerts

alerts:
  - name: build_failure
    condition: build_success_total == 0 for 3 builds
    severity: critical
    notify: [track-f, track-leads]
    
  - name: verification_failure
    condition: verification_fail_total > 0
    severity: high
    notify: [track-f, track-a]
    
  - name: test_failure
    condition: test_fail_total > 0
    severity: high
    notify: [track-f, track-b]
    
  - name: coverage_drop
    condition: coverage_percentage < 90
    severity: medium
    notify: [track-f]
    
  - name: build_slow
    condition: build_duration_seconds > 3600
    severity: medium
    notify: [track-f]
    
  - name: queue_backup
    condition: pipeline_queue_time > 300
    severity: low
    notify: [track-f]
```

---

# 16. VALIDATION AND TESTING

## 16.1 Build System Tests

```
BUILD SYSTEM VALIDATION:

1. UNIT TESTS
   ├── Configuration parsing
   ├── Dependency resolution
   ├── Task scheduling
   ├── Result collection
   └── Manifest generation

2. INTEGRATION TESTS
   ├── End-to-end Rust build
   ├── End-to-end Ada build
   ├── End-to-end TERAS-LANG build
   ├── Cross-language build
   └── Verification integration

3. REPRODUCIBILITY TESTS
   ├── Same-machine reproducibility
   ├── Cross-machine reproducibility
   ├── Time-independence
   └── Environment-independence

4. SECURITY TESTS
   ├── Input validation
   ├── Sandbox isolation
   ├── Secret handling
   └── Output signing

5. PERFORMANCE TESTS
   ├── Incremental build time
   ├── Full build time
   ├── Cache effectiveness
   └── Parallel scaling
```

## 16.2 Validation Checklist

```
TRACK F BUILD SYSTEM VALIDATION CHECKLIST:

□ All Rust crates build successfully
□ All Ada/SPARK packages build successfully
□ TERAS-LANG bootstrap compiles
□ All unit tests pass
□ All integration tests pass
□ Miri finds no undefined behavior
□ Kani verification passes
□ SPARK proofs complete
□ Coverage >= 80%
□ Reproducible build verified
□ CI/CD pipeline functional
□ Hash chain tool operational
□ All tracks can build successfully
□ Documentation complete
□ No TODOs remaining
```

---

# APPENDIX A: QUICK START

## A.1 Initial Setup

```bash
# Clone repository
git clone https://internal.teras.my/git/teras.git
cd teras

# Setup development environment
./scripts/setup-dev.sh

# Verify setup
teras-build all --level=0

# Run verification
./scripts/verify.sh 2
```

## A.2 Common Commands

```bash
# Build all
teras-build all

# Build specific track
teras-build rust
teras-build ada
teras-build teras-lang

# Run tests
cargo test --workspace
gprbuild -P teras_tests.gpr && ./run_tests.sh

# Run verification
./scripts/verify.sh 4

# Update hash chain
teras-hash-chain add --file <document>
teras-hash-chain verify

# Generate documentation
teras-build docs
```

---

# APPENDIX B: TROUBLESHOOTING

## B.1 Common Issues

| Issue | Cause | Solution |
|-------|-------|----------|
| Rust build fails | Missing toolchain | `rustup default 1.84.0` |
| Ada build fails | Missing GNAT | Install `gnat` package |
| Verification timeout | Complex proof | Increase timeout in config |
| Hash mismatch | Modified file | Check for unauthorized changes |
| CI failure | Environment diff | Check runner configuration |

---

# APPENDIX C: DOCUMENT INTEGRITY

## C.1 Hash Chain Entry

```
DOCUMENT: TRACK_F-TOOL-BUILD_v1_0_0.md
VERSION: 1.0.0
CREATED: 2026-01-03
SHA-256: [COMPUTED AT FINALIZATION]
PREDECESSOR: TERAS_COORDINATION_LOG_v1_0_0.md
SIGNATURE: [SIGNED AT FINALIZATION]
```

## C.2 Change Log

| Version | Date | Author | Description |
|---------|------|--------|-------------|
| 1.0.0 | 2026-01-03 | Track F | Initial release |

---

*END OF DOCUMENT: TRACK_F-TOOL-BUILD_v1_0_0.md*
*Track F: Tooling — Building the Foundation for TERAS*
