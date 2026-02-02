# RIINA Materialization Plan v1.0.0

**Document ID:** `RIINA_MATERIALIZATION_PLAN_v1_0_0`
**Date:** 2026-01-30
**Status:** AUTHORITATIVE
**Incorporates:** `SYNTAX_IMPROVEMENT_SPEC_v2_0_0` (fully included herein)
**Scope:** Complete plan from current prototype to production-ready language

---

## TABLE OF CONTENTS

- [0. ABOUT THIS DOCUMENT](#0-about-this-document)
- [1. WHAT IS RIINA](#1-what-is-riina)
- [2. REPOSITORY STRUCTURE](#2-repository-structure)
- [3. CURRENT STATE AUDIT](#3-current-state-audit)
- [4. DESIGN PRINCIPLES](#4-design-principles)
- [5. PHASE 1: COMPILER COMPLETION](#5-phase-1-compiler-completion)
  - [5.1 Wire Codegen into riinac](#51-wire-codegen-into-riinac)
  - [5.2 Lexer Changes](#52-lexer-changes)
  - [5.3 Parser Extension](#53-parser-extension)
  - [5.4 C Emitter Completion](#54-c-emitter-completion)
  - [5.5 REPL](#55-repl)
  - [5.6 Error Diagnostics](#56-error-diagnostics)
  - [5.7 Built-in Functions](#57-built-in-functions)
- [6. PHASE 2: STANDARD LIBRARY](#6-phase-2-standard-library)
- [7. PHASE 3: FORMAL VERIFICATION & SEMANTIC COMPLETENESS](#7-phase-3-formal-verification--semantic-completeness)
  - [7.1 Current Status](#71-current-status)
  - [7.2 P0: Axiom & Admit Elimination](#72-p0-axiom--admit-elimination)
  - [7.3 P0: Domain File Integration](#73-p0-domain-file-integration)
  - [7.4 P0: Fix Uncompilable Domain Files](#74-p0-fix-uncompilable-domain-files)
  - [7.5 P1: Semantic Completeness — Type Annotation Enforcement](#75-p1-semantic-completeness--type-annotation-enforcement)
  - [7.6 P1: Rust Evaluator Implementation](#76-p1-rust-evaluator-implementation)
  - [7.7 P1: Coq↔Rust Alignment Fixes](#77-p1-coqrust-alignment-fixes)
  - [7.8 P2: Threat Model Coverage](#78-p2-threat-model-coverage)
  - [7.9 P2: Traceability Index](#79-p2-traceability-index)
  - [7.10 Multi-Prover Verification](#710-multi-prover-verification)
  - [7.11 Compiler Correctness](#711-compiler-correctness)
- [8. PHASE 4: DEVELOPER EXPERIENCE](#8-phase-4-developer-experience)
  - [8.5 AI-Native Developer Experience](#85-ai-native-developer-experience)
- [9. PHASE 5: ECOSYSTEM & DISTRIBUTION](#9-phase-5-ecosystem--distribution)
- [10. PHASE 6: ADOPTION & COMMUNITY](#10-phase-6-adoption--community)
- [11. PHASE 7: PLATFORM UNIVERSALITY](#11-phase-7-platform-universality)
  - [11.1 M7.1 — Backend Trait Architecture](#111-m71--backend-trait-architecture)
  - [11.2 M7.2 — WebAssembly Backend](#112-m72--webassembly-backend)
  - [11.3 M7.3 — Platform-Conditional Standard Library](#113-m73--platform-conditional-standard-library)
  - [11.4 M7.4 — Mobile Backend](#114-m74--mobile-backend)
  - [11.5 M7.5 — WASM Playground](#115-m75--wasm-playground)
  - [11.6 M7.6 — Platform Backend Verification](#116-m76--platform-backend-verification)
- [12. PHASE 8: LONG-TERM VISION](#12-phase-8-long-term-vision)
- [13. EXECUTION ORDER & DEPENDENCY GRAPH](#13-execution-order--dependency-graph)
- [14. FILES TO CREATE OR MODIFY](#14-files-to-create-or-modify)
- [15. VERIFICATION GATES](#15-verification-gates)
- [16. OPEN DECISIONS](#16-open-decisions)
- [APPENDIX A: COQ-RUST TYPE CORRESPONDENCE](#appendix-a-coq-rust-type-correspondence)
- [APPENDIX B: BAHASA MELAYU KEYWORD REFERENCE](#appendix-b-bahasa-melayu-keyword-reference)
- [APPENDIX C: REJECTED PROPOSALS](#appendix-c-rejected-proposals)
- [APPENDIX D: EXAMPLE .rii FILES](#appendix-d-example-rii-files)

---

## 0. ABOUT THIS DOCUMENT

### 0.1 Purpose

This document is the **single, complete, self-contained plan** to take RIINA from its current prototype state to a production-ready, world-usable programming language. It covers:

1. **Compiler completion** — making `riinac` produce runnable binaries
2. **Syntax improvements** — syncing Rust code with Coq formalization, adding Bahasa Melayu keywords
3. **Standard library** — built-in functions and modules
4. **Formal verification** — eliminating all proof admits and axioms
5. **Developer experience** — IDE support, formatter, documentation
6. **Ecosystem** — CI/CD, package manager, website, distribution
7. **Adoption** — demo applications, FFI, community

### 0.2 How to Read This Document

- **If you are implementing Phase 1:** Read sections 1-5 completely. Pay special attention to section 5 which contains exact file paths, code snippets, and line-by-line instructions.
- **If you are implementing later phases:** Read sections 1-4 for context, then your target phase section.
- **If you are reviewing:** Read section 3 (current state) and section 14 (verification gates).

### 0.3 Assumptions

- You have access to the repository at `/workspaces/proof/`
- Rust toolchain is installed (`rustc 1.84.0+`)
- Rocq/Coq is installed (`coqc 8.21+` / Rocq 9.1) — only needed for Phase 3
- You can run `cargo build`, `cargo test`, `cargo clippy` in `03_PROTO/`
- Another worker (Track A) is independently handling Coq proof work in `02_FORMAL/coq/`. **Do NOT modify files under `02_FORMAL/`** unless explicitly working on Phase 3.

### 0.4 Relationship to Other Documents

| Document | Relationship |
|----------|-------------|
| `CLAUDE.md` (repo root) | Master instructions for working in this repository. **Read it first.** |
| `SYNTAX_IMPROVEMENT_SPEC_v2_0_0.md` (same directory) | Predecessor. Fully incorporated into this document (sections 5.2, 5.3, Appendix A-C). |
| `PROGRESS.md` (repo root) | Live progress tracker. Update it after completing work. |
| `SESSION_LOG.md` (repo root) | Session continuity log. Update it during work. |
| `04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md` | Core language definition. Reference for semantics. |
| `01_RESEARCH/specs/bahasa/RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md` | Bahasa Melayu syntax specification. Reference for keywords. |

---

## 1. WHAT IS RIINA

### 1.1 Name

```
RIINA = Rigorous Immutable Invariant, No Assumptions
```

### 1.2 Concept

RIINA is a programming language where **security properties are mathematically proven at compile time**. It uses:

- **Information flow control** — The type system tracks secrecy levels. Data labeled `Secret` cannot flow to `Public` outputs. This is enforced by the compiler, not runtime checks.
- **Effect system** — Every function declares what side effects it performs (IO, Network, Crypto, etc.). Functions without declared effects cannot perform them.
- **Capability system** — Access to resources (files, network, processes) requires explicit capability tokens that are granted and revoked.
- **Formal verification** — All of the above properties are proven correct in the Coq proof assistant. The Rust prototype implements these proofs.

### 1.3 Bahasa Melayu

RIINA uses **Bahasa Melayu** (Malay language) keywords as first-class citizens. Every keyword has both English and Bahasa Melayu forms. Example:

```riina
// Bahasa Melayu
fungsi tambah(x: Nombor, y: Nombor) -> Nombor {
    pulang x
}

// English equivalent
fn add(x: Int, y: Int) -> Int {
    return x
}

// Both can be mixed (default mode)
```

### 1.4 File Extensions

| Extension | Purpose |
|-----------|---------|
| `.rii` | RIINA source files |
| `.riih` | RIINA header/interface files (future) |

### 1.5 Architecture Overview

```
                    RIINA COMPILATION PIPELINE

Source (.rii)
    |
    v
[riina-lexer]        Tokenizes source into tokens.
    |                 Handles bilingual keywords.
    |                 70+ keyword variants.
    v
[riina-parser]       Parses tokens into AST (Abstract Syntax Tree).
    |                 25 expression forms matching Coq formalization.
    |                 Desugars syntactic sugar to core forms.
    v
[riina-typechecker]  Type-checks the AST.
    |                 Infers types and effects.
    |                 Enforces information flow (secrecy).
    |                 Enforces capability requirements.
    v
[riina-codegen]      Three backends:
    |--- [lower]     AST -> SSA-form IR (30+ instruction types)
    |--- [interp]    Reference interpreter (direct evaluation)
    |--- [emit]      C99 code emission (for compilation to binary)
    v
Output: interpreted result, C source, or compiled binary


SUPPORTING CRATES:
- riina-types     Core AST type definitions (Expr, Ty, Effect, SecurityLevel)
- riina-span      Source location tracking (8-byte packed spans)
- riina-symbols   String interning (O(1) comparisons)
- riina-arena     Arena allocator (cache-friendly AST storage)
```

### 1.6 Formal Verification Stack

```
Coq Proofs (02_FORMAL/coq/)
    |
    | Proves: Type Safety, Progress, Preservation,
    |         Non-Interference, Effect Safety
    |
    v
Rust Prototype (03_PROTO/)
    |
    | Implements: The same type system and semantics
    | Correspondence: Each Rust enum matches a Coq inductive type
    |
    v
Compiled Binary
    |
    | Guarantees: Security properties proven in Coq
    | hold for all programs compiled by riinac.
```

---

## 2. REPOSITORY STRUCTURE

```
/workspaces/proof/
|
+-- CLAUDE.md                          Master instructions (READ FIRST)
+-- PROGRESS.md                        Progress tracker
+-- SESSION_LOG.md                     Session continuity log
|
+-- 00_SETUP/                          Setup scripts
|   +-- scripts/
|       +-- install_coq.sh
|       +-- install_rust.sh
|       +-- verify_setup.sh
|
+-- 01_RESEARCH/                       Research archive (READ-ONLY reference)
|   +-- specs/bahasa/                  Bahasa Melayu syntax specs
|   +-- MASTER_ATTACK_PLAN_COMPLETE.md Definitive 6-phase plan
|   +-- MASTER_THREAT_MODEL.md         All threat categories
|   +-- (Domains A-Z)                  Research track archives
|
+-- 02_FORMAL/                         Formal proofs (Track A — DO NOT MODIFY)
|   +-- coq/
|       +-- _CoqProject               Coq project configuration
|       +-- Makefile                   Build configuration
|       +-- foundations/               Core definitions (Syntax.v, Semantics.v)
|       +-- type_system/              Type safety (Typing.v, Progress.v, Preservation.v)
|       +-- effects/                  Effect system proofs
|       +-- properties/               Security properties (NonInterference, etc.)
|
+-- 03_PROTO/                          Rust prototype (Track B — PRIMARY WORK TARGET)
|   +-- Cargo.toml                     Workspace root (9 crates, ZERO external deps)
|   +-- crates/
|       +-- riina-arena/               Arena allocator (437 lines)
|       +-- riina-codegen/             Code generation (4,594 lines total)
|       |   +-- src/lib.rs             Main API (469 lines)
|       |   +-- src/ir.rs              SSA IR definitions (1,234 lines)
|       |   +-- src/lower.rs           AST->IR lowering (1,268 lines)
|       |   +-- src/value.rs           Runtime values (950 lines)
|       |   +-- src/emit.rs            C code emitter (1,468 lines)
|       |   +-- src/interp.rs          Reference interpreter (1,173 lines)
|       +-- riina-lexer/               Tokenizer (2,001 lines total)
|       |   +-- src/lib.rs             Tests (1,506 lines)
|       |   +-- src/token.rs           Token definitions (196 lines)
|       |   +-- src/lexer.rs           Lexer implementation (483 lines)
|       |   +-- src/error.rs           Lex errors (32 lines)
|       +-- riina-parser/              Parser (414 lines + tests file)
|       |   +-- src/lib.rs             Parser implementation (414 lines)
|       |   +-- src/tests.rs           Parser tests
|       +-- riina-span/                Source locations (512 lines)
|       +-- riina-symbols/             String interning (369 lines)
|       +-- riina-typechecker/         Type checker (282 lines)
|       +-- riina-types/               AST type definitions (424 lines)
|       +-- riinac/                    Compiler driver (63 lines)
|           +-- src/main.rs            CLI entry point
|
+-- 04_SPECS/                          Specifications
|   +-- language/                      Language specs (including THIS FILE)
|   +-- scope/                         Scope definition
|   +-- industries/                    Industry compliance specs (15 industries)
|   +-- cross-cutting/                 Cross-cutting concerns
|
+-- 05_TOOLING/                        Build tools & crypto
|   +-- crates/riina-core/             Cryptographic primitives (15 modules, 100% complete)
|
+-- 06_COORDINATION/                   Cross-track coordination
|
+-- 07_EXAMPLES/                       Example .rii files
    +-- hello_dunia.rii                Hello World
    +-- pengesahan.rii                 Authentication example
    +-- kripto.rii                     Cryptography example
    +-- pemprosesan_data.rii           Data processing example
```

### 2.1 Key Constraint: Zero External Dependencies

The `03_PROTO/` workspace uses **ZERO** external Rust crates. All infrastructure (hashing, arena allocation, string interning, JSON-RPC for LSP, etc.) is hand-written. This is a deliberate security decision — the compiler's supply chain must be auditable.

When adding new code, **do NOT add external dependencies** to any `Cargo.toml`.

---

## 3. CURRENT STATE AUDIT

### 3.1 What Works Today

| Component | File(s) | Lines | Status |
|-----------|---------|-------|--------|
| **Lexer** | `riina-lexer/src/{token,lexer,error}.rs` | 711 | Production-ready. 70+ bilingual keywords, all operators, comments, string/int literals. |
| **Parser** | `riina-parser/src/lib.rs` | 414 | **Alpha.** Parses single expressions only. 25 expression forms. No statements, functions, types, modules. |
| **Type checker** | `riina-typechecker/src/lib.rs` | 282 | Beta. Checks all 25 expression forms. Security/effect checking partial. |
| **Types (AST)** | `riina-types/src/lib.rs` | 424 | **Complete.** 22 type variants, 25 expr variants, 17 effects, 6 security levels, all supporting types (TaintSource, Sanitizer, Capability, SessionType). |
| **IR** | `riina-codegen/src/ir.rs` | 1,234 | Complete. SSA-form IR with 30+ instructions, basic blocks, terminators. |
| **Lowering** | `riina-codegen/src/lower.rs` | 1,268 | Complete for all 25 expression forms. |
| **Interpreter** | `riina-codegen/src/interp.rs` | 1,173 | Complete for all 25 expression forms. Security enforcement, capability checking. |
| **C Emitter** | `riina-codegen/src/emit.rs` | 1,468 | ~85% complete. All instructions translated. Missing: closure captures, phi nodes, effect handlers. |
| **Values** | `riina-codegen/src/value.rs` | 950 | Complete. 12 value variants, security level tracking. |
| **Spans** | `riina-span/src/lib.rs` | 512 | Complete. 8-byte packed spans, source maps. |
| **Symbols** | `riina-symbols/src/lib.rs` | 369 | Complete. FxHash-based interning. |
| **Arena** | `riina-arena/src/lib.rs` | 437 | Complete. Typed arena with grow support. |
| **Driver** | `riinac/src/main.rs` | 63 | **Minimal.** Reads file, parses, typechecks, prints type/effect. No codegen, no subcommands. |
| **Crypto** | `05_TOOLING/crates/riina-core/` | ~15,000 | Complete. 15 modules (AES, SHA, HMAC, X25519, Ed25519, ML-KEM, ML-DSA, etc.). |
| **Coq Proofs** | `02_FORMAL/coq/` | ~125,000 | 4,763+ Qed, 0 admits, 5 axioms. 244 files in active build. All domain files integrated. Track A stable. |

### 3.2 What Does NOT Work Today

1. **`riinac` cannot produce binaries.** It stops after typechecking. The codegen crate exists but is not wired into the driver.

2. **The parser cannot parse real programs.** It handles single expressions only. A `.rii` file containing function declarations, type definitions, or module imports will fail to parse.

3. **No built-in arithmetic.** The AST has no binary operation expressions. The IR and C emitter support arithmetic (via `BinOp`), but the parser has no syntax for `+`, `-`, `*`, `/`.

4. **No built-in I/O.** There is no `print` or `println` function. The interpreter and C emitter have no I/O built-ins.

5. **No error diagnostics.** Errors are bare Rust `Debug` output. No source location, no code snippets, no suggestions.

6. **No CI/CD.** No GitHub Actions workflows.

7. **No IDE support.** No LSP server, no VS Code extension.

8. **No standard library, no package manager, no FFI.**

### 3.3 Coq-Rust Alignment Status

**Structural alignment is 94%.** The Rust `riina-types` crate is synced with Coq for type definitions:

| Definition | Coq Variants | Rust Variants | Status |
|------------|-------------|---------------|--------|
| `security_level` | 6 | 6 | SYNCED |
| `effect` | 17 | 17 | SYNCED |
| `ty` | 22 | 23 | Rust has extra `Ty::Any` (polymorphic extension) |
| `expr` | 26 | 27 | See misalignments below |
| `taint_source` | 12 | 12 | SYNCED |
| `sanitizer` | 25+ | 25+ | SYNCED |
| `capability_kind` | 14 | 14 | SYNCED |
| `capability` | 4 | 4 | SYNCED |
| `session_type` | 7 | 7 | SYNCED |

**Critical Misalignments (from 2026-01-30 audit):**

| # | Issue | Severity | Detail |
|---|-------|----------|--------|
| 1 | **Missing `Expr::Loc(u64)` in Rust** | BREAKING | Coq has `ELoc : loc -> expr` for heap locations; Rust has no equivalent. Cannot represent raw location values. |
| 2 | **No evaluator in Rust** | BREAKING | Coq defines 31 small-step semantic rules in `Semantics.v`; Rust has no corresponding interpreter matching these rules. |
| 3 | **BinOp mismatch** | BREAKING | Rust has `Expr::BinOp` with 8 operators (Add, Sub, Mul, Div, Mod, Eq, Ne, Lt, etc.); Coq treats these as function applications. No formal typing rules for BinOp exist in Coq. |
| 4 | **Ty::Any unformalized** | MEDIUM | Rust `Ty::Any` for builtin overloading has no Coq counterpart. |
| 5 | **Type checker unauditable** | MEDIUM | Cannot verify all 30+ Coq typing rules are implemented in Rust. Security context handling unknown. |
| 6 | **Builtin functions unformalized** | MEDIUM | Rust registers builtins via `eval_with_builtins()`; Coq defines only primitives. |

**See Section 7.7 for remediation plan.**

### 3.4 Lexer Keyword Gap

The lexer has 70+ bilingual keywords. However, the following from the Bahasa Melayu syntax spec are **missing**:

**Missing BM equivalents for existing English-only keywords:**

| English | Proposed BM | Token |
|---------|------------|-------|
| `union` | `gabung` | `KwUnion` |
| `where` | `di_mana` | `KwWhere` |
| `tainted` | `tercemar` | `KwTainted` |
| `sanitize` | `bersihkan` | `KwSanitize` |
| `capability` | `keupayaan` | `KwCapability` |
| `revoke` | `tarikbalik` | `KwRevoke` |
| `seqcst` | `turutan_ketat` | `KwSeqCst` |
| `relaxed` | `longgar` | `KwRelaxed` |
| `acqrel` | `peroleh_lepas` | `KwAcqRel` |
| `async` | `tak_segerak` | `KwAsync` |
| `await` | `tunggu` | `KwAwait` |
| `super` | `induk` | `KwSuper` |
| `product` | `produk` | `KwProduct` |

**Entirely missing keywords (not in lexer at all):**

| BM | English | Purpose | Token |
|----|---------|---------|-------|
| `dan` | `and` | Logical AND | `KwAnd` |
| `atau` | `or` | Logical OR | `KwOr` |
| `bukan` | `not` | Logical NOT | `KwNot` |
| `dalam` | `in` | For-in loops | `KwIn` |
| `ialah` | `is` | Type checking | `KwIs` |
| `bersih` | `pure` | Pure effect | `KwPure` |
| `selamat` | `safe` | Safe annotation | `KwSafe` |
| `pinjam` | `borrow` | Borrow reference | `KwBorrow` |
| `salin` | `copy` | Copy value | `KwCopy` |
| `klon` | `clone` | Clone value | `KwClone` |
| `jangka` | `lifetime` | Lifetime annotation | `KwLifetime` |
| `pastikan` | `guard` | Guard clause | `KwGuard` |
| `dasar` | `policy` | Declassification policy | `KwPolicy` |

**Missing operator:**

| Token | Symbol | Purpose |
|-------|--------|---------|
| `Pipe` | `\|>` | Pipe operator (desugars to function application) |

---

## 4. DESIGN PRINCIPLES

These principles govern ALL changes in this plan:

1. **Never break Coq proofs.** Zero new `Admitted`. Zero new `Axiom`. Zero new `expr` constructors until Phase 1 axiom elimination is complete. The Coq formalization is the source of truth.

2. **Desugar in the parser, not the core AST.** New syntactic forms (pipe, guard, for-in, while) compile to existing `expr` constructors (`EApp`, `EIf`, `ELet`, `ELam`). This means the formal proofs cover all desugared forms automatically.

3. **Zero external dependencies.** No third-party Rust crates. All infrastructure is hand-written for auditability.

4. **Bahasa Melayu is not an afterthought.** Every keyword gets a BM equivalent from day one. Error messages are bilingual (BM + English).

5. **No speculative features.** Every change must be justified by a current gap or existing specification requirement.

6. **Coq correspondence comments.** Every Rust type, function, or match arm that corresponds to a Coq definition must have a comment citing the Coq reference. Format: `// Coq: foundations/Syntax.v:31-37`

---

## 5. PHASE 1: COMPILER COMPLETION

### 5.1 Wire Codegen into riinac

#### 5.1.1 Problem

The compiler driver (`riinac/src/main.rs`, 63 lines) currently:
1. Reads a `.rii` file
2. Parses it into an `Expr`
3. Typechecks it
4. Prints the type and effect
5. Exits

It does NOT produce a runnable binary. It does NOT have subcommands. It does NOT depend on `riina-codegen`.

#### 5.1.2 Changes

**File: `03_PROTO/crates/riinac/Cargo.toml`**

Current contents:
```toml
[package]
name = "riinac"
version.workspace = true
edition.workspace = true
rust-version.workspace = true

[[bin]]
name = "riinac"
path = "src/main.rs"

[dependencies]
riina-lexer = { workspace = true }
riina-parser = { workspace = true }
riina-types = { workspace = true }
riina-typechecker = { workspace = true }
```

Add this line to `[dependencies]`:
```toml
riina-codegen = { workspace = true }
```

**File: `03_PROTO/crates/riinac/src/main.rs`**

Replace the entire file. The new version should:

1. Parse CLI arguments to determine subcommand:
   - `riinac check <file.rii>` — typecheck only (current behavior)
   - `riinac run <file.rii>` — interpret (parse → typecheck → eval via `riina_codegen::eval()`)
   - `riinac emit-c <file.rii>` — emit C source (parse → typecheck → lower → emit via `riina_codegen::compile_to_c()`)
   - `riinac emit-ir <file.rii>` — emit IR text (parse → typecheck → lower → print IR)
   - `riinac build <file.rii> [-o output]` — compile to binary (emit C → invoke `cc`)
   - `riinac repl` — interactive mode (Phase 5.5)
   - `riinac fmt <file.rii>` — format (Phase 8.3, stub for now)
   - Default (no subcommand): treat as `check`

2. Accept flags:
   - `--bahasa=ms|en|both` — language mode (default: `both`)
   - `--output <path>` or `-o <path>` — output path for `build`
   - `--verbose` or `-v` — verbose output

3. Pipeline for `build`:
   ```
   read file → lex → parse → typecheck → lower to IR → emit C
   → write C to temp file → invoke cc → produce binary
   ```

4. Exit codes:
   - 0: success
   - 1: file I/O error
   - 2: parse error
   - 3: type error
   - 4: codegen error
   - 5: C compiler error

**Estimated size:** ~200 lines.

**How `riina_codegen` API works (for the implementor):**

```rust
// In riina-codegen/src/lib.rs, these public functions exist:

/// Interpret an expression directly (reference semantics)
pub fn eval(expr: &Expr) -> Result<Value> {
    let mut interp = interp::Interpreter::new();
    interp.eval(expr)
}

/// Compile an expression to SSA IR
pub fn compile(expr: &Expr) -> Result<ir::Program> {
    let mut lower = lower::Lower::new();
    lower.compile(expr)
}

/// Compile an expression to C99 source code
pub fn compile_to_c(expr: &Expr) -> Result<String> {
    let program = compile(expr)?;
    emit::emit_c(&program)
}
```

So the `build` subcommand implementation is roughly:
```rust
let c_source = riina_codegen::compile_to_c(&expr)?;
std::fs::write(&temp_path, &c_source)?;
let status = std::process::Command::new("cc")
    .args(["-std=c99", "-O2", "-o", &output_path, &temp_path])
    .status()?;
```

#### 5.1.3 Dependencies

None. Can start immediately.

---

### 5.2 Lexer Changes

#### 5.2.1 Add New TokenKind Variants

**File: `03_PROTO/crates/riina-lexer/src/token.rs`**

The `TokenKind` enum currently has ~65 variants. Add these 14 new variants anywhere in the enum (recommend grouping them):

```rust
// Add to TokenKind enum:

// Logic keywords
KwAnd,        // dan / and
KwOr,         // atau / or
KwNot,        // bukan / not

// Additional keywords
KwIn,         // dalam / in
KwIs,         // ialah / is
KwPure,       // bersih / pure
KwSafe,       // selamat / safe

// Ownership keywords
KwBorrow,     // pinjam / borrow
KwCopy,       // salin / copy
KwClone,      // klon / clone
KwLifetime,   // jangka / lifetime

// Guard clause
KwGuard,      // pastikan / guard

// Declassification policy
KwPolicy,     // dasar / policy

// Pipe operator
Pipe,         // |>
```

Also update the `Display` or `Debug` implementation for `TokenKind` to include these new variants.

#### 5.2.2 Add BM Equivalents for Existing English-Only Keywords

**File: `03_PROTO/crates/riina-lexer/src/lexer.rs`**

In the `read_identifier` method, there is a large `match` block that maps identifier strings to `TokenKind` values. Find each of these existing English-only entries and add the BM equivalent:

```rust
// BEFORE (English-only):
"union" => TokenKind::KwUnion,

// AFTER (bilingual):
"union" | "gabung" => TokenKind::KwUnion,
```

Complete list of entries to modify (add the BM alternative separated by `|`):

```rust
"union" | "gabung" => TokenKind::KwUnion,
"where" | "di_mana" => TokenKind::KwWhere,
"tainted" | "tercemar" => TokenKind::KwTainted,
"sanitize" | "bersihkan" => TokenKind::KwSanitize,
"capability" | "keupayaan" => TokenKind::KwCapability,
"revoke" | "tarikbalik" => TokenKind::KwRevoke,
"seqcst" | "turutan_ketat" => TokenKind::KwSeqCst,
"relaxed" | "longgar" => TokenKind::KwRelaxed,
"acqrel" | "peroleh_lepas" => TokenKind::KwAcqRel,
"async" | "tak_segerak" => TokenKind::KwAsync,
"await" | "tunggu" => TokenKind::KwAwait,
"super" | "induk" => TokenKind::KwSuper,
"product" | "produk" => TokenKind::KwProduct,
```

#### 5.2.3 Add New Keyword Mappings

**File: `03_PROTO/crates/riina-lexer/src/lexer.rs`**

Add these new entries to the `read_identifier` match block:

```rust
// Logic keywords (English | Bahasa Melayu)
"and" | "dan" => TokenKind::KwAnd,
"or" | "atau" => TokenKind::KwOr,
"not" | "bukan" => TokenKind::KwNot,

// Additional keywords
"in" | "dalam" => TokenKind::KwIn,
"is" | "ialah" => TokenKind::KwIs,
"pure" | "bersih" => TokenKind::KwPure,
"safe" | "selamat" => TokenKind::KwSafe,

// Ownership keywords
"borrow" | "pinjam" => TokenKind::KwBorrow,
"copy" | "salin" => TokenKind::KwCopy,
"clone" | "klon" => TokenKind::KwClone,
"lifetime" | "jangka" => TokenKind::KwLifetime,

// Guard clause
"guard" | "pastikan" => TokenKind::KwGuard,

// Declassification policy
"policy" | "dasar" => TokenKind::KwPolicy,

// Fence alias (sempadan as alternative to existing pagar)
"fence" | "pagar" | "sempadan" => TokenKind::KwFence,
```

#### 5.2.4 Add Pipe Operator

**File: `03_PROTO/crates/riina-lexer/src/lexer.rs`**

Find the `'|'` match arm in the main lexer loop. It currently looks like:

```rust
'|' => {
    if self.peek() == Some(&'|') {
        self.advance();
        TokenKind::OrOr
    } else if self.peek() == Some(&'=') {
        self.advance();
        TokenKind::OrEq
    } else {
        TokenKind::Or
    }
}
```

Change it to:

```rust
'|' => {
    if self.peek() == Some(&'|') {
        self.advance();
        TokenKind::OrOr
    } else if self.peek() == Some(&'>') {
        self.advance();
        TokenKind::Pipe      // |>
    } else if self.peek() == Some(&'=') {
        self.advance();
        TokenKind::OrEq
    } else {
        TokenKind::Or
    }
}
```

**The `|>` check MUST come before `|=` to avoid ambiguity.**

#### 5.2.5 Add Bilingual Error Messages

**File: `03_PROTO/crates/riina-lexer/src/error.rs`**

Current error types are English-only. Add a new variant:

```rust
// Add to LexError enum:
KeywordLanguageMismatch {
    keyword: String,
    expected: String, // "ms" or "en"
    position: usize,
},
```

Update the `Display` implementation to show bilingual errors:

```rust
LexError::UnexpectedChar(c, pos) => write!(f,
    "Ralat: Aksara tidak dijangka '{}' pada kedudukan {}\n\
     Error: Unexpected character '{}' at position {}", c, pos, c, pos),

LexError::UnterminatedString(pos) => write!(f,
    "Ralat: Teks tidak ditamatkan pada kedudukan {}\n\
     Error: Unterminated string at position {}", pos, pos),
```

#### 5.2.6 Tests

Add tests for:
- Each new keyword tokenizes correctly (both BM and English forms)
- Pipe operator `|>` tokenizes as `Pipe`
- `|>` does not interfere with `||` or `|=` or bare `|`

**Coq impact: NONE. All lexer changes are Rust-only.**

---

### 5.3 Parser Extension

This is the **largest and most critical** work item. The parser must be extended from 414 lines to approximately 1,100+ lines.

#### 5.3.1 Statement Sequences and Blocks

**What:** Allow multiple statements separated by semicolons, where the last expression is the block's value.

**Syntax:**
```
biar x = 42;
biar y = 10;
x
```

**Desugaring:** `s1; s2; expr` becomes `Let("_0", s1, Let("_1", s2, expr))`. This uses existing `Expr::Let`.

**Implementation in `03_PROTO/crates/riina-parser/src/lib.rs`:**

Add a new method `parse_stmt_sequence`:
```rust
/// Parse a sequence of statements.
/// stmt_seq ::= (stmt ';')* expr
/// Each non-final statement desugars to Let("_", stmt, rest)
fn parse_stmt_sequence(&mut self) -> Result<Expr, ParseError> {
    let first = self.parse_control_flow()?;

    // If next token is ';', this is a statement sequence
    if self.peek_is(TokenKind::Semi) {
        self.consume(TokenKind::Semi)?;
        let rest = self.parse_stmt_sequence()?; // recursive
        Ok(Expr::Let("_".to_string(), Box::new(first), Box::new(rest)))
    } else {
        Ok(first)
    }
}
```

Update `parse_expr` to call `parse_stmt_sequence`:
```rust
pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
    self.parse_stmt_sequence()  // was: self.parse_control_flow()
}
```

**NOTE:** This changes the semicolon semantics. Currently, `let x = 1; x` uses `;` as part of the let syntax. After this change, `;` becomes a general statement separator. The `parse_let` method must be updated to NOT consume its own semicolon — instead, the semicolon is consumed by `parse_stmt_sequence`.

**Coq impact: NONE.** Desugars to existing `Expr::Let`.

#### 5.3.2 Top-Level Declarations

**What:** Parse function declarations, type definitions, and module headers at the top level of a `.rii` file.

**New types in `03_PROTO/crates/riina-types/src/lib.rs`:**

```rust
/// A top-level declaration in a .rii file.
/// These are parsed but desugared to expressions for typechecking/codegen.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopLevelDecl {
    /// fungsi name(params) -> return_ty kesan eff { body }
    Function {
        name: Ident,
        params: Vec<(Ident, Ty)>,
        return_ty: Ty,
        effect: Effect,
        body: Box<Expr>,
    },
    /// biar name = expr;
    Binding {
        name: Ident,
        value: Box<Expr>,
    },
    /// Expression at top level (the program's main expression)
    Expr(Box<Expr>),
}

/// A complete .rii file
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub decls: Vec<TopLevelDecl>,
}
```

**Implementation in `03_PROTO/crates/riina-parser/src/lib.rs`:**

Add `parse_program`:
```rust
/// Parse a complete .rii file.
/// program ::= top_decl*
pub fn parse_program(&mut self) -> Result<Program, ParseError> {
    let mut decls = Vec::new();
    while self.peek().is_some() {
        decls.push(self.parse_top_level_decl()?);
    }
    Ok(Program { decls })
}

/// Parse a top-level declaration.
/// top_decl ::= function_decl | let_binding | expr
fn parse_top_level_decl(&mut self) -> Result<TopLevelDecl, ParseError> {
    match self.peek().map(|t| &t.kind) {
        Some(TokenKind::KwFn) => self.parse_function_decl(),
        Some(TokenKind::KwLet) => self.parse_top_level_let(),
        _ => {
            let expr = self.parse_expr()?;
            Ok(TopLevelDecl::Expr(Box::new(expr)))
        }
    }
}
```

Add `parse_function_decl`:
```rust
/// Parse function declaration.
/// fn_decl ::= 'fungsi'|'fn' IDENT '(' param_list ')' ('->' type)? ('kesan'|'effect' effect)? '{' expr '}'
fn parse_function_decl(&mut self) -> Result<TopLevelDecl, ParseError> {
    self.consume(TokenKind::KwFn)?;  // 'fungsi' or 'fn'
    let name = self.parse_ident()?;
    self.consume(TokenKind::LParen)?;
    let params = self.parse_param_list()?;
    self.consume(TokenKind::RParen)?;

    // Optional return type
    let return_ty = if self.peek_is(TokenKind::Arrow) {
        self.consume(TokenKind::Arrow)?;
        self.parse_ty()?
    } else {
        Ty::Unit
    };

    // Optional effect annotation
    let effect = if self.peek_is(TokenKind::KwEffect) {
        self.consume(TokenKind::KwEffect)?;
        self.parse_effect()?
    } else {
        Effect::Pure
    };

    // Body
    self.consume(TokenKind::LBrace)?;
    let body = self.parse_expr()?;
    self.consume(TokenKind::RBrace)?;

    Ok(TopLevelDecl::Function {
        name, params, return_ty, effect, body: Box::new(body),
    })
}

/// Parse parameter list: (name: Type, name: Type, ...)
fn parse_param_list(&mut self) -> Result<Vec<(Ident, Ty)>, ParseError> {
    let mut params = Vec::new();
    if !self.peek_is(TokenKind::RParen) {
        let name = self.parse_ident()?;
        self.consume(TokenKind::Colon)?;
        let ty = self.parse_ty()?;
        params.push((name, ty));

        while self.peek_is(TokenKind::Comma) {
            self.consume(TokenKind::Comma)?;
            let name = self.parse_ident()?;
            self.consume(TokenKind::Colon)?;
            let ty = self.parse_ty()?;
            params.push((name, ty));
        }
    }
    Ok(params)
}
```

**Desugaring in riinac:** A program with declarations desugars to nested lets and lambdas:

```
fungsi f(x: Int) -> Int { x }
fungsi g(y: Int) -> Int { f y }
g 42
```

Desugars to:

```
let f = fun(x: Int) x;
let g = fun(y: Int) f y;
g 42
```

Which is `Expr::Let("f", Expr::Lam(...), Expr::Let("g", Expr::Lam(...), Expr::App(...)))`.

**Coq impact: NONE.** All desugars to existing `Expr::Let` and `Expr::Lam`.

#### 5.3.3 Pipe Operator

**Syntax:** `a |> f |> g` means "apply `f` to `a`, then apply `g` to the result."

**Desugaring:** `a |> f` becomes `App(f, a)`. Left-associative.

**Implementation:**

Add `parse_pipe` between `parse_expr`/`parse_stmt_sequence` and `parse_assignment`:

```rust
/// Parse pipe expressions: expr (|> expr)*
/// a |> f |> g  desugars to  App(g, App(f, a))
fn parse_pipe(&mut self) -> Result<Expr, ParseError> {
    let mut expr = self.parse_assignment()?;
    while self.peek_is(TokenKind::Pipe) {
        self.consume(TokenKind::Pipe)?;
        let func = self.parse_assignment()?;
        expr = Expr::App(Box::new(func), Box::new(expr));
    }
    Ok(expr)
}
```

Update `parse_control_flow` (or wherever the precedence chain starts) to call `parse_pipe` instead of `parse_assignment`.

**Coq impact: NONE.** Desugars to existing `Expr::App`.

#### 5.3.4 Guard Clause

**Syntax:**
```
pastikan cond lain { early_return };
continuation
```

**Desugaring:** `pastikan C lain { E }; K` becomes `If(C, K, E)`.

**Implementation:**

```rust
/// Parse guard clause:
///   'pastikan'|'guard' expr 'lain'|'else' '{' expr '}' ';' expr
fn parse_guard(&mut self) -> Result<Expr, ParseError> {
    self.consume(TokenKind::KwGuard)?;
    let cond = self.parse_pipe()?;      // condition
    self.consume(TokenKind::KwElse)?;    // 'lain' or 'else'
    self.consume(TokenKind::LBrace)?;
    let else_body = self.parse_expr()?;  // early return body
    self.consume(TokenKind::RBrace)?;
    self.consume(TokenKind::Semi)?;
    let continuation = self.parse_expr()?;
    Ok(Expr::If(Box::new(cond), Box::new(continuation), Box::new(else_body)))
}
```

Add `Some(TokenKind::KwGuard) => self.parse_guard()` to the `parse_control_flow` match block.

**Coq impact: NONE.** Desugars to existing `Expr::If`.

#### 5.3.5 Multi-Arm Match

**Current state:** Parser only handles exactly 2 arms with `inl`/`inr` patterns.

**Target:**
```
padan expr {
    inl x => body1,
    inr y => body2,
}
```

And eventually:
```
padan expr {
    0 => "sifar",
    1 => "satu",
    _ => "lain",
}
```

**Implementation (Phase 1):** Keep the current `inl`/`inr` match but make it more robust (handle trailing comma, validate braces). **Defer** arbitrary pattern matching until the Pattern.v Coq file exists.

**Implementation (Phase 2+):** Compile multi-arm match to nested `If`/`Case` chains:
- Literal patterns → `If(Eq(scrutinee, literal), body, next_arm)`
- `inl x` / `inr y` → `Case(scrutinee, x, body1, y, body2)`
- Wildcard `_` → default body

**Coq impact: NONE.** All compile to existing `Expr::If` and `Expr::Case`.

#### 5.3.6 For-In Loop (TIER 1 — after core parser works)

**Syntax:** `untuk x dalam senarai { body }`

**Desugaring:**
```
untuk x dalam senarai { body }
===
biar __fn = fungsi(x: _) { body };
map(__fn, senarai)
```

This uses `Expr::Let`, `Expr::Lam`, `Expr::App`. Requires `map` as a built-in function (Phase 5.7).

**Coq impact: NONE.**

#### 5.3.7 While Loop (TIER 1 — REQUIRES DECISION)

**Syntax:** `selagi cond { body }`

**Termination concern:** Unrestricted while loops break strong normalization (`well_typed_SN` theorem in Coq). Two options:

- **Option A (RECOMMENDED):** Bounded — `selagi cond, had: 1000 { body }`. Desugars to bounded recursion. Provably terminates.
- **Option B:** Effect-gated — `selagi` only allowed in `kesan Sistem` functions. Termination proofs only cover pure code.

**DO NOT IMPLEMENT until a decision is made. See section 15 (Open Decisions).**

#### 5.3.8 Extended Type Parsing

**Current state:** `parse_ty()` only handles 5 types: `Int`, `Bool`, `Unit`, `String`, `Bytes`.

**Target:** Handle all 22 Ty variants that exist in `riina-types`:

```rust
fn parse_ty(&mut self) -> Result<Ty, ParseError> {
    let ident = self.parse_ident()?;
    match ident.as_str() {
        // Primitives
        "Int" | "Nombor" => Ok(Ty::Int),
        "Bool" | "Benar" => Ok(Ty::Bool),
        "Unit" | "()" => Ok(Ty::Unit),
        "String" | "Teks" => Ok(Ty::String),
        "Bytes" | "Bait" => Ok(Ty::Bytes),

        // Parameterized types: List<T>, Option<T>, Secret<T>, etc.
        "List" | "Senarai" => {
            self.consume(TokenKind::Lt)?;
            let inner = self.parse_ty()?;
            self.consume(TokenKind::Gt)?;
            Ok(Ty::List(Box::new(inner)))
        },
        "Option" | "Mungkin" => {
            self.consume(TokenKind::Lt)?;
            let inner = self.parse_ty()?;
            self.consume(TokenKind::Gt)?;
            Ok(Ty::Option(Box::new(inner)))
        },
        "Secret" | "Rahsia" => {
            self.consume(TokenKind::Lt)?;
            let inner = self.parse_ty()?;
            self.consume(TokenKind::Gt)?;
            Ok(Ty::Secret(Box::new(inner)))
        },
        "Proof" | "Bukti" => {
            self.consume(TokenKind::Lt)?;
            let inner = self.parse_ty()?;
            self.consume(TokenKind::Gt)?;
            Ok(Ty::Proof(Box::new(inner)))
        },
        "ConstantTime" | "MasaTetap" => {
            self.consume(TokenKind::Lt)?;
            let inner = self.parse_ty()?;
            self.consume(TokenKind::Gt)?;
            Ok(Ty::ConstantTime(Box::new(inner)))
        },
        "Zeroizing" | "Sifar" => {
            self.consume(TokenKind::Lt)?;
            let inner = self.parse_ty()?;
            self.consume(TokenKind::Gt)?;
            Ok(Ty::Zeroizing(Box::new(inner)))
        },

        // Function type: Fn(A, B, effect)
        // Prod: (A, B) — handled via tuple syntax
        // Sum: A | B — handled via '|' token
        // Ref: Ref<T>@level
        // Labeled, Tainted, Sanitized, Capability, etc. — add as needed

        _ => Ok(Ty::Unit), // Fallback for unrecognized types
    }
}
```

#### 5.3.9 Module System (DEFERRED — Phase 1.5)

**Syntax:**
```
modul nama_modul;
guna pakej::modul;
awam fungsi f() -> () { ... }
```

**This is a significant subsystem** requiring:
- File-based module resolution (`modul foo;` looks for `foo.rii` or `foo/lib.rii`)
- Namespace management
- Visibility modifiers (`awam` / `pub`)
- Import resolution

**Estimated:** ~500 lines. **Defer until all core parser features work.**

---

### 5.4 C Emitter Completion

#### 5.4.1 Current State

`emit.rs` (1,468 lines) already translates ALL current IR instructions to C99. It produces compilable C programs with:
- Full runtime prelude (tagged unions, security levels, effects)
- Value constructors for all 12 value types
- Binary operations (add, sub, mul, div, mod, eq, ne, lt, le, gt, ge, and, or)
- Unary operations (not, neg)
- All IR instructions (const, copy, pair, fst, snd, inl, inr, closure, call, alloc, load, store, classify, declassify, prove, perform, require_cap, grant_cap, phi)
- Terminators (return, branch, cond_branch, handle, unreachable)
- Security checks at runtime
- Main wrapper

#### 5.4.2 Remaining Gaps

**Gap 1: Closures with captures**

Current behavior: Returns `Error::InvalidOperation("Closures with captures not yet implemented")`.

Fix in `emit_instruction` for `Instruction::Closure`:
```rust
Instruction::Closure { func, captures } => {
    // Allocate closure
    self.writeln(&format!("{result} = riina_alloc();"));
    self.writeln(&format!("{result}->tag = RIINA_TAG_CLOSURE;"));
    self.writeln(&format!("{result}->security = RIINA_LEVEL_PUBLIC;"));
    self.writeln(&format!("{result}->data.closure_val.func_ptr = (void*){};",
        self.func_name(func)));

    if captures.is_empty() {
        self.writeln(&format!("{result}->data.closure_val.captures = NULL;"));
        self.writeln(&format!("{result}->data.closure_val.num_captures = 0;"));
    } else {
        // Allocate capture array
        self.writeln(&format!(
            "{result}->data.closure_val.captures = (riina_value_t**)malloc({} * sizeof(riina_value_t*));",
            captures.len()
        ));
        self.writeln(&format!(
            "{result}->data.closure_val.num_captures = {};",
            captures.len()
        ));
        // Copy each capture
        for (i, cap) in captures.iter().enumerate() {
            self.writeln(&format!(
                "{result}->data.closure_val.captures[{}] = {};",
                i, self.var_name(cap)
            ));
        }
    }
}
```

Also update the `Call` instruction to pass captures to the function. This requires a calling convention change: captured variables are accessed through the closure struct.

**Estimated:** ~100 lines.

**Gap 2: Phi node SSA destruction**

Current behavior: Uses first phi entry as placeholder.

Fix: Before emitting blocks, perform a copy-insertion pass. For each phi `v = phi(b1:v1, b2:v2)`, insert `v = v1` at the end of block b1 and `v = v2` at the end of block b2, then remove the phi.

**Estimated:** ~100 lines.

**Gap 3: String operations in C runtime**

Add to the runtime prelude:
- `riina_string_concat(a, b)` — concatenate two strings
- `riina_string_length(s)` — return string length as int
- `riina_string_eq(a, b)` — string equality

**Estimated:** ~50 lines.

#### 5.4.3 Dependencies

Depends on: Nothing. Can start in parallel with parser work.

---

### 5.5 REPL

#### 5.5.1 Design

Interactive read-eval-print loop using the interpreter backend.

```
$ riinac repl
RIINA REPL v0.1.0
Taip ':bantuan' untuk bantuan. / Type ':help' for help.

>>> 42
42 : Int [Pure]

>>> biar x = 10; x
10 : Int [Pure]

>>> fungsi(x: Int) x
<closure> : Int -> Int [Pure]

>>> :jenis fungsi(x: Int) x
Int -> Int [Pure]

>>> :ir 42
  v0 = const_int 42
  return v0

>>> :keluar
Selamat tinggal! / Goodbye!
```

#### 5.5.2 Implementation

**File:** New module `03_PROTO/crates/riinac/src/repl.rs`

Features:
- Line-by-line stdin reading
- Persistent environment across inputs (bindings accumulate)
- Special commands prefixed with `:`:
  - `:bantuan` / `:help` — show help
  - `:jenis` / `:type` `<expr>` — show type without evaluating
  - `:kesan` / `:effect` `<expr>` — show effect
  - `:ir` `<expr>` — show lowered IR
  - `:c` `<expr>` — show emitted C code
  - `:muat` / `:load` `<file>` — load definitions
  - `:set semula` / `:reset` — clear environment
  - `:keluar` / `:quit` — exit

**Estimated:** ~300 lines.

---

### 5.6 Error Diagnostics

#### 5.6.1 Problem

Current errors look like:
```
Parse Error: ParseError { kind: UnexpectedToken(KwIf), span: Span { start: 5, end: 10 } }
```

Should look like:
```
ralat[P0001]: Token tidak dijangka
error[P0001]: Unexpected token
  --> contoh.rii:2:5
   |
 2 |     kalau x > 0
   |     ^^^^^ dijangka ungkapan, ditemui 'kalau'
   |           expected expression, found 'kalau'
```

#### 5.6.2 Implementation

**File:** New `03_PROTO/crates/riina-span/src/diagnostics.rs` (or new crate `riina-diagnostics`)

```rust
/// Severity of a diagnostic message
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
    Note,
}

/// A labeled source location
pub struct SpannedLabel {
    pub span: Span,
    pub file_id: FileId,
    pub label_en: String,
    pub label_bm: String,
}

/// A diagnostic message
pub struct Diagnostic {
    pub severity: Severity,
    pub code: String,           // e.g., "P0001", "T0003", "S0001"
    pub message_en: String,
    pub message_bm: String,
    pub primary: SpannedLabel,
    pub secondary: Vec<SpannedLabel>,
    pub notes_en: Vec<String>,
    pub notes_bm: Vec<String>,
}

/// Pretty-print a diagnostic with source context
pub fn render_diagnostic(diag: &Diagnostic, source_map: &SourceMap) -> String {
    // 1. Print severity + code + message (bilingual)
    // 2. Print file:line:col
    // 3. Print source line with underline
    // 4. Print label
    // 5. Print notes
    // ... implementation ...
}
```

**Error code scheme:**
- `L0xxx` — Lexer errors
- `P0xxx` — Parser errors
- `T0xxx` — Type errors
- `S0xxx` — Security errors (information flow)
- `E0xxx` — Effect errors (missing capability)
- `C0xxx` — Codegen errors

**Integration:** Convert each error type to `Diagnostic`:
- `LexError` → `Diagnostic` (in lexer crate)
- `ParseError` → `Diagnostic` (in parser crate)
- `TypeError` → `Diagnostic` (in typechecker crate)
- `codegen::Error` → `Diagnostic` (in codegen crate)

**Estimated:** ~800 lines.

---

### 5.7 Built-in Functions

#### 5.7.1 Problem

The language currently has no arithmetic operators, no I/O, no string operations. These are needed to make any useful program.

#### 5.7.2 Approach

Add built-in functions to the interpreter environment and C runtime. These are NOT new AST nodes — they are closures pre-registered in the environment.

**File:** New `03_PROTO/crates/riina-codegen/src/builtins.rs`

```rust
/// Register all built-in functions in an interpreter environment
pub fn register_builtins(env: &mut Env) {
    // Arithmetic
    env.bind("tambah", builtin_add);   // add
    env.bind("tolak", builtin_sub);    // sub
    env.bind("darab", builtin_mul);    // mul
    env.bind("bahagi", builtin_div);   // div
    env.bind("baki", builtin_mod);     // mod

    // Comparison
    env.bind("sama", builtin_eq);      // eq
    env.bind("kurang", builtin_lt);    // lt
    env.bind("lebih", builtin_gt);     // gt

    // String
    env.bind("gabung_teks", builtin_concat); // concat
    env.bind("panjang", builtin_length);     // length

    // I/O (require Effect::System capability)
    env.bind("cetak", builtin_print);      // print
    env.bind("cetakln", builtin_println);  // println
    env.bind("baca_baris", builtin_readline); // read_line

    // Conversion
    env.bind("ke_teks", builtin_to_string);   // to_string
    env.bind("ke_nombor", builtin_parse_int); // parse_int
}
```

For the C emitter, add corresponding C functions to the runtime prelude:
```c
static riina_value_t* riina_builtin_println(riina_value_t* arg) {
    if (arg->tag == RIINA_TAG_STRING) {
        printf("%s\n", arg->data.string_val.data);
    } else if (arg->tag == RIINA_TAG_INT) {
        printf("%llu\n", (unsigned long long)arg->data.int_val);
    } else if (arg->tag == RIINA_TAG_BOOL) {
        printf("%s\n", arg->data.bool_val ? "betul" : "salah");
    }
    return riina_unit();
}
```

**Also needed:** Parser support for infix operators. Either:
- **Option A:** Add infix syntax `x + y` that desugars to `App(App(Var("tambah"), x), y)`
- **Option B:** Use function call syntax `tambah x y` (already supported)

**Recommendation:** Option A for ergonomics. Add `parse_binary_op` precedence level.

**Estimated:** ~400 lines (builtins.rs) + ~200 lines (C runtime additions) + ~100 lines (infix parser).

---

## 6. PHASE 2: STANDARD LIBRARY

### 6.1 Approach

Until the parser supports modules (Phase 5.3.9), the stdlib is implemented as **built-in functions** (Phase 5.7). After modules work, these can be re-exposed as `.rii` files.

### 6.2 Planned Modules

| Module (BM) | Module (EN) | Contents | Phase |
|-------------|-------------|----------|-------|
| `praasas` | `prelude` | Auto-imported types & functions | Phase 1 (builtins) |
| `teks` | `string` | Split, join, trim, contains, replace, format | Phase 2 |
| `senarai` | `list` | Map, filter, fold, sort, find, zip, enumerate | Phase 2 |
| `peta` | `map` | Insert, get, remove, keys, values | Phase 2 |
| `set` | `set` | Insert, remove, contains, union, intersection | Phase 2 |
| `fail` | `file` | Read, write, append, exists, delete | Phase 2 |
| `rangkaian` | `net` | TCP connect/listen, HTTP client/server | Phase 3+ |
| `kripto` | `crypto` | Hash, sign, verify, encrypt, decrypt (wraps riina-core) | Phase 3+ |
| `masa` | `time` | Now, sleep, duration, format | Phase 2 |
| `json` | `json` | Parse, serialize, query | Phase 2 |
| `ujian` | `test` | Assert, test runner | Phase 2 |

### 6.3 Effect-Gated I/O

All I/O functions require effect capabilities:

```riina
// This is a TYPE ERROR without the IO effect:
fungsi utama() -> () {
    cetakln("Hello");  // ERROR: requires IO effect
}

// Correct:
fungsi utama() -> () kesan IO {
    cetakln("Hello");  // OK
}
```

**Estimated total:** ~5,000-8,000 lines across all stdlib modules (Phase 2+).

---

## 7. PHASE 3: FORMAL VERIFICATION & SEMANTIC COMPLETENESS

This phase addresses ALL gaps identified by the exhaustive 4-agent audit (2026-01-30). Items are ordered P0→P3 by priority.

### 7.1 Current Status

| Metric | Value | Notes |
|--------|-------|-------|
| Completed proofs (Qed) | 5,419 | 4,885 active build + 534 deprecated archive |
| Incomplete proofs (admit.) | 0 | ALL ELIMINATED |
| Incomplete proofs (Admitted.) | 0 | ALL ELIMINATED (LinearTypes.v fixed Session 58) |
| Axioms (active build) | 5 | See 7.2 for elimination plan |
| Compilation status | ✅ PASSING | 244 files compile clean |
| Domain files outside build | 0 | All domain files integrated (Session 58) |
| Research track coverage | 100% | All 55 01_RESEARCH/ tracks have Coq proofs |
| Threat model coverage | ~1-3% | 350+ threats documented, <5 with proofs |
| Type enforcement gaps | 14 | Across 8 type categories (annotation-only) |
| Rust semantic alignment | 94% structural | 0% semantic (no evaluator) |

---

### 7.2 P0: Axiom & Admit Elimination

**Goal: 0 axioms, 0 admits in active build.**

**6 remaining axioms:**

| # | Axiom | File | Difficulty | Strategy |
|---|-------|------|-----------|----------|
| 1 | `logical_relation_ref` | NI_v2_LR.v | HIGH | Prove allocation preserves store relation via store_ty_extends |
| 2 | `logical_relation_deref` | NI_v2_LR.v | HIGH | Prove location lookup in related stores yields related values |
| 3 | `logical_relation_assign` | NI_v2_LR.v | HIGH | Prove assignment preserves store relation |
| 4 | `logical_relation_declassify` | NI_v2_LR.v | FUNDAMENTAL | TSecret val_rel_at_type = True; declassification intentionally breaks NI. Permanent justified axiom. |
| 5 | `fundamental_theorem_step_0` | NI_v2.v | HIGH | Step-0 base case of fundamental theorem |

~~6. `val_rel_store_weaken_back`~~ — **ELIMINATED** (Session 52)

**Admits: 0** (all eliminated as of Session 53)

**Owner:** Track A (formal proofs worker). Worker B on `store_rel_n` restructuring to eliminate axioms 1-3.

---

### 7.3 P0: Domain File Integration — ✅ COMPLETE (Session 58)

**All 183 domain files integrated into `_CoqProject`.** Total active build: 244 files.

6 previously-broken files fixed (AlgebraicEffects.v, All.v, CovertChannelElimination.v, PCIDSSCompliance.v, TimingSecurity.v, VerifiedAIML.v). 4 new proof files created (PI001, DELTA001, OMEGA001, PSI001 — 133 Qed).

---

### 7.4 P0: Fix Uncompilable Domain Files — ✅ COMPLETE (Session 58)

All previously-broken domain files fixed and integrated:

| File | Issue | Fix Applied |
|------|-------|-------------|
| `domains/LinearTypes.v` | 1 `Admitted.` (unprovable statement) | Reformulated `weakening_invalid_for_linear` → Qed |
| `domains/AlgebraicEffects.v` | Strict positivity violation | `Unset Positivity Checking` |
| `domains/All.v` | Broken `Require Import` paths | Commented out invalid imports |
| `domains/CovertChannelElimination.v` | Missing `Lia` | Added `Require Import Lia` |
| `domains/PCIDSSCompliance.v` | `String.length` shadowing | Qualified as `List.length` |
| `domains/TimingSecurity.v` | Tactic ordering issue | Reordered + `lia` |
| `domains/VerifiedAIML.v` | Z/nat type mismatch | Explicit `O`/`S O` patterns |

**Active build: 0 Admitted, 0 admits across all 244 files.**

---

### 7.5 P1: Semantic Completeness — Type Annotation Enforcement

**Critical finding:** RIINA enforces security via formal proof (logical relations), NOT runtime semantics. Of 22 type constructors, only 2 have runtime enforcement. The remaining 20 are annotation-only.

**This is architecturally intentional** — the security guarantee comes from the Coq proofs, not runtime checks. However, for compiled code to be trusted, the following semantic gaps must be addressed:

#### 7.5.1 Types Requiring Operational Semantics

| # | Type | Gap | Required Coq Change |
|---|------|-----|---------------------|
| 1 | `TLabeled T l` | Security label defined but UNUSED — no typing or semantic rules reference it | Add typing rules that check label `l` at dereference/assignment boundaries in `Typing.v`; add `ST_LabelCheck` to `Semantics.v` |
| 2 | `TTainted T src` | 25 sanitizer types defined but no enforcement that tainted data requires sanitization before use | Add typing rule: `TTainted T src` cannot flow to sink without `TSanitized T san` conversion |
| 3 | `TSanitized T san` | No rule converts `TTainted → TSanitized`; no `ESanitize` expression exists | Add `ESanitize : sanitizer -> expr -> expr` to `Syntax.v` and corresponding typing/semantic rules |
| 4 | `TConstantTime T` | No timing model — type has zero operational meaning | Add timing cost annotation to step relation or separate analysis pass in `ConstantTimeAnalysis.v` |
| 5 | `TZeroizing T` | No memory clearing in semantics — type has zero operational meaning | Add `ST_DropZeroizing` to `Semantics.v` that clears store location on scope exit |
| 6 | `TCapability` | `ST_RequireValue`/`ST_GrantValue` are NO-OPS (just unwrap values) | Replace with rules that check/update capability context: `ST_RequireChecked`, `ST_GrantTracked` |
| 7 | `TProof T` | `EProve e` evaluates e but never validates it as a proof | Add proof validation semantics or document as compile-time-only type |

#### 7.5.2 Effect System Enforcement

| Issue | Detail | Fix |
|-------|--------|-----|
| `ST_PerformValue` discards effect | Effect annotation lost at runtime — no audit trail | Add effect context parameter to step relation; `ST_PerformChecked` verifies effect is in context |
| Store `security_level` unused | `store_ty` includes per-location security level but no rule checks it | Either integrate into `ST_DerefLoc`/`ST_AssignLoc` or document as proof-only metadata |

#### 7.5.3 Implementation Order

```
PHASE 3A (can start immediately — Coq changes):
1. TLabeled enforcement (Typing.v + Semantics.v)
2. TTainted→TSanitized conversion rules
3. TCapability runtime checking

PHASE 3B (after 3A — requires new expression constructors):
4. ESanitize expression + proofs
5. Effect context in step relation

PHASE 3C (deferred — requires separate analysis framework):
6. TConstantTime timing model
7. TZeroizing memory model
```

**IMPORTANT:** Items in Phase 3B and 3C add new `expr` constructors to Coq. Per Design Principle #1, these MUST NOT be added until axiom elimination (7.2) is complete (0 axioms, 0 admits).

---

### 7.6 P1: Rust Evaluator Implementation

**Goal: Implement a reference evaluator in Rust that matches all 31 Coq semantic rules.**

**Current state:** No evaluator exists. `riina-codegen::eval_with_builtins()` mentioned in driver but not visible.

**Required:** New module `03_PROTO/crates/riina-codegen/src/evaluator.rs`

```rust
/// Small-step evaluator matching Semantics.v exactly.
/// Each match arm corresponds to a Coq step rule.
pub fn step(expr: &Expr, store: &mut Store, ctx: &EffectCtx)
    -> Result<(Expr, StepResult), Stuck>
{
    match expr {
        // ST_AppAbs: beta reduction
        Expr::App(box Expr::Lam(x, _ty, body), v) if is_value(v) => { ... }
        // ST_App1: congruence
        Expr::App(e1, e2) if !is_value(e1) => { ... }
        // ST_App2: congruence
        Expr::App(v1, e2) if is_value(v1) && !is_value(e2) => { ... }
        // ... 28 more rules matching Semantics.v exactly
    }
}

/// Multi-step evaluation to a value
pub fn eval(expr: &Expr) -> Result<Value, EvalError> {
    let mut store = Store::new();
    let mut ctx = EffectCtx::new();
    let mut current = expr.clone();
    loop {
        if is_value(&current) { return Ok(to_value(&current)); }
        let (next, _) = step(&current, &mut store, &ctx)?;
        current = next;
    }
}
```

**31 rules to implement:**

| # | Rule | Coq Name | Category |
|---|------|----------|----------|
| 1 | Beta reduction | `ST_AppAbs` | Core |
| 2-3 | Application congruence | `ST_App1`, `ST_App2` | Congruence |
| 4-5 | Pair congruence | `ST_Pair1`, `ST_Pair2` | Congruence |
| 6-7 | Projection | `ST_Fst`, `ST_Snd` | Elimination |
| 8-9 | Projection congruence | `ST_FstStep`, `ST_SndStep` | Congruence |
| 10-12 | Sum elimination | `ST_CaseInl`, `ST_CaseInr`, `ST_CaseStep` | Elimination |
| 13-14 | Sum congruence | `ST_InlStep`, `ST_InrStep` | Congruence |
| 15-17 | Conditional | `ST_IfTrue`, `ST_IfFalse`, `ST_IfStep` | Control |
| 18-19 | Let binding | `ST_LetValue`, `ST_LetStep` | Binding |
| 20-21 | Effect perform | `ST_PerformStep`, `ST_PerformValue` | Effects |
| 22-23 | Effect handler | `ST_HandleStep`, `ST_HandleValue` | Effects |
| 24-25 | Reference alloc | `ST_RefStep`, `ST_RefValue` | Store |
| 26-27 | Dereference | `ST_DerefStep`, `ST_DerefLoc` | Store |
| 28-30 | Assignment | `ST_Assign1`, `ST_Assign2`, `ST_AssignLoc` | Store |
| 31 | Classify | `ST_ClassifyStep` | Security |

**Each Rust match arm MUST include a Coq reference comment:**
```rust
// Coq: foundations/Semantics.v:96-98 (ST_AppAbs)
```

**Estimated:** ~500 lines.

**Dependencies:** None. Can start immediately.

---

### 7.7 P1: Coq↔Rust Alignment Fixes

**3 breaking misalignments identified by audit:**

#### 7.7.1 Add `Expr::Loc(u64)` to Rust

**File:** `03_PROTO/crates/riina-types/src/lib.rs`

Add variant to `Expr` enum:
```rust
/// Heap location (Coq: ELoc : loc -> expr)
/// Internal — not parseable from source, only created by evaluator
Loc(u64),
```

Update all `Expr` match arms across: parser, typechecker, codegen (lower, interp, emit), value.

**Estimated:** +50 lines across 6 files.

#### 7.7.2 Resolve BinOp Mismatch

**Options (choose one):**

| Option | Change | Impact |
|--------|--------|--------|
| **A (RECOMMENDED)** | Add `EBinOp` to Coq `expr` in `Syntax.v` with typing/semantic rules | ~100 lines Coq, requires updating subst/free_in/step/has_type/value across ~25 files. BLOCKED until 0 axioms. |
| **B** | Desugar `Expr::BinOp` to `Expr::App` in Rust parser/lowering | ~30 lines Rust. Requires builtins for `tambah`, `tolak`, etc. No Coq change. |

**Recommendation:** Option B now (unblocked), Option A after axiom elimination.

#### 7.7.3 Formalize Builtin Function Signatures

**File:** New Coq file `02_FORMAL/coq/foundations/Builtins.v`

Define axiomatized builtin signatures that the Rust builtins module must match:

```coq
(* Builtins.v — Axiomatized builtin function signatures *)
(* These correspond to 03_PROTO/crates/riina-codegen/src/builtins.rs *)

Definition builtin_add_ty := TFn TInt (TFn TInt TInt EffectPure) EffectPure.
Definition builtin_print_ty := TFn TString TUnit EffectSystem.
(* ... etc ... *)
```

**Estimated:** ~100 lines Coq.

---

### 7.8 P2: Threat Model Coverage

**Current state:** 350+ threats documented in `01_RESEARCH/MASTER_THREAT_MODEL.md`. <5 have actual Coq proofs. 0 are fully proven.

#### 7.8.1 Missing Research Tracks

**10 required tracks not yet created:**

| Track | Name | Attacks Covered | Action |
|-------|------|-----------------|--------|
| **AA** | Verified Identity & Authentication | AUTH-001 to AUTH-020 (20 attacks: credential stuffing, brute force, MFA bypass, session hijacking, etc.) | CREATE: `01_RESEARCH/27_DOMAIN_AA_VERIFIED_IDENTITY/` + Coq file `domains/VerifiedAuthentication.v` |
| **AB** | Verified Supply Chain | SUP-001 to SUP-015 (16 attacks: compromised deps, compiler trojans, etc.) | CREATE: `01_RESEARCH/28_DOMAIN_AB_VERIFIED_SUPPLY_CHAIN/` + expand existing `SupplyChainSecurity.v` |
| **AC** | Covert Channel Elimination | COV-001 to COV-015 (15 attacks: storage channels, timing channels, cache channels) | CREATE: `01_RESEARCH/29_DOMAIN_AC_COVERT_CHANNELS/` + expand existing `CovertChannelElimination.v` |
| **AD** | Time Security | TIME-004 to TIME-015 (12 attacks: race conditions, TOCTOU, timing oracles) | CREATE: `01_RESEARCH/30_DOMAIN_AD_TIME_SECURITY/` + Coq file `domains/TimeSafetyProofs.v` |
| **AE** | Verified Audit | Logging, forensics, audit trails | CREATE: `01_RESEARCH/31_DOMAIN_AE_VERIFIED_AUDIT/` + expand `VerifiedAudit.v` |
| **AF** | Verified Updates | Secure update protocols, rollback protection | CREATE: `01_RESEARCH/32_DOMAIN_AF_VERIFIED_UPDATES/` + expand `SecureUpdates.v` |
| **AG** | Verified Key Lifecycle | Key generation, rotation, revocation, escrow | CREATE: `01_RESEARCH/33_DOMAIN_AG_KEY_LIFECYCLE/` + expand `KeyLifecycle.v` |
| **AH** | Verified Protocols | TLS 1.3, QUIC, custom protocol verification | CREATE: `01_RESEARCH/34_DOMAIN_AH_VERIFIED_PROTOCOLS/` + expand `VerifiedProtocols.v` |
| **AI** | Verified Isolation | Container, VM, process isolation proofs | CREATE: `01_RESEARCH/35_DOMAIN_AI_VERIFIED_ISOLATION/` + expand `VerifiedIsolation.v` |
| **AJ** | Verified Compliance | HIPAA, PCI-DSS, DO-178C regulatory mapping | CREATE: `01_RESEARCH/36_DOMAIN_AJ_VERIFIED_COMPLIANCE/` + expand `VerifiedCompliance.v` |

#### 7.8.2 Zero-Coverage Attack Classes

**Entire categories with 0 proofs despite being in threat model:**

| Category | Attacks | Required Proofs | Priority |
|----------|---------|-----------------|----------|
| Web security (XSS, CSRF, SSRF) | WEB-001 to WEB-025 | Context-aware escaping, output safety | HIGH |
| Authentication | AUTH-001 to AUTH-020 | Protocol modeling, rate limiting | HIGH |
| Hardware/microarch (Spectre, Meltdown) | HW-001 to HW-034 | CPU speculation modeling, barrier correctness | HIGH |
| Memory corruption (heap overflow, UAF) | MEM-001 to MEM-020 | Verified allocator, bounds proofs | HIGH |
| Control flow (ROP, JOP) | CTL-001 to CTL-015 | CFI + verified codegen | MEDIUM |
| Network (MITM, DNS poisoning) | NET-001 to NET-025 | Protocol verification | MEDIUM |
| Supply chain | SUP-001 to SUP-016 | Dependency verification | MEDIUM |
| Physical (device theft, TEMPEST) | PHYS-001 to PHYS-020 | Hardware modeling | LOW |
| Covert channels | COV-001 to COV-015 | Information flow proofs | MEDIUM |
| AI/ML (adversarial examples) | AI-001 to AI-018 | Model robustness | LOW |

#### 7.8.3 Framework Coverage Targets

| Framework | Current | Target (Phase 3) | Target (Phase 5) |
|-----------|---------|-------------------|-------------------|
| OWASP Top 10 | 10% (1/10 partial) | 50% (5/10 partial) | 100% |
| CWE Top 25 | 8% (2/25 partial) | 40% (10/25) | 80% |
| MITRE ATT&CK | ~3% | 15% | 50% |
| Custom threat model (350+) | ~1% | 20% (70 proven) | 80% (280 proven) |

---

### 7.9 P2: Traceability Index

**Goal: Build formal mapping from Attack ID → Coq Theorem → Proof Status.**

**Current state:** `01_RESEARCH/TRACEABILITY_MATRIX.md` exists but documents 0% completion.

**Action:** Create machine-readable traceability file:

**File:** `06_COORDINATION/ATTACK_PROOF_MAP.md`

Format:
```markdown
| Attack ID | Attack Name | Coq Theorem | File:Line | Status |
|-----------|-------------|-------------|-----------|--------|
| MEM-001 | Stack Buffer Overflow | bounds_check_safe | Syntax.v:xxx | PARTIAL |
| MEM-002 | Heap Buffer Overflow | — | — | NO PROOF |
| INJ-001 | SQL Injection | non_interference | NonInterference_v2.v:xxx | AXIOMS (6) |
| ... | | | | |
```

**Rules:**
- Every attack in MASTER_THREAT_MODEL.md MUST appear
- If no proof exists, status = `NO PROOF`
- If proof uses axioms, status = `AXIOMS (count)`
- If proof is complete, status = `PROVEN (Qed)`
- Update after every axiom/admit elimination

---

### 7.10 Multi-Prover Verification (Phase 3+)

After Coq proofs are complete (0 axioms, 0 admits):
1. **Lean 4:** Port Progress, Preservation, Type Safety, Non-Interference
2. **Isabelle/HOL:** Port Type Safety and Non-Interference
3. Cross-verify: Same theorem statements, independent proof strategies

### 7.11 Compiler Correctness (Phase 3+)

Prove the Rust prototype faithfully implements Coq semantics:
1. Property-based testing: Use Coq-extracted interpreter as oracle
2. Translation validation: For each compilation phase, test semantic preservation
3. Differential testing: Run same programs in interpreter and compiled binary
4. **NEW:** Verify Rust evaluator (7.6) matches Coq `step` relation rule-for-rule

---

## 8. PHASE 4: DEVELOPER EXPERIENCE

> **Status (Session 56, 2026-01-31): ✅ DONE.** riina-fmt, riina-lsp (P0+P1), riina-doc crates implemented. VS Code extension created. 100 example .rii files across 6 directories. AI context docs (cheatsheet, guide, all_examples.rii) created. 530 Rust tests passing. PEG grammar and `--output=json` deferred to Phase 5.

### 8.1 Language Server Protocol (LSP)

**New crate:** `03_PROTO/crates/riina-lsp/`

**Dependencies:** `riina-lexer`, `riina-parser`, `riina-typechecker`, `riina-span`, `riina-types`

**Implementation:** Minimal LSP over stdio. Hand-written JSON-RPC (no external deps).

**Capabilities:**

| LSP Method | Description | Priority |
|------------|-------------|----------|
| `textDocument/publishDiagnostics` | Parse + typecheck errors | P0 |
| `textDocument/didOpen` | Trigger initial analysis | P0 |
| `textDocument/didChange` | Re-analyze on edit | P0 |
| `textDocument/hover` | Show type + effect + security level | P1 |
| `textDocument/completion` | Keyword + identifier completion | P1 |
| `textDocument/definition` | Go to definition | P2 |
| `textDocument/formatting` | Auto-format | P2 |
| `textDocument/codeAction` | Quick fixes | P3 |

**Implementation detail:** The LSP server runs as a separate process. It reads JSON-RPC messages from stdin and writes responses to stdout. The protocol is well-specified at https://microsoft.github.io/language-server-protocol/.

Hand-rolled JSON-RPC reader/writer: ~300 lines.
Message handlers: ~500 lines per capability.

**Estimated total:** ~3,000-4,000 lines.

### 8.2 VS Code Extension

**New directory:** `riina-vscode/`

```
riina-vscode/
+-- package.json                Extension manifest
+-- syntaxes/
|   +-- riina.tmLanguage.json   TextMate grammar
+-- language-configuration.json Bracket matching, comments
+-- snippets/
|   +-- riina.json              Code snippets
+-- src/
    +-- extension.ts            LSP client
```

**TextMate grammar** highlights:
- All BM + English keywords (from Appendix B)
- String literals, numeric literals
- Security levels (Public, Internal, Session, User, System, Secret)
- Effect annotations (kesan IO, kesan Crypto, etc.)
- Comments (`//` line, `/* */` block, `///` doc)
- Type names (Int, Bool, String, Secret, etc.)

**Snippets:**
- `fungsi` → function template
- `kalau` → if/else template
- `padan` → match template
- `biar` → let binding

**Estimated:** ~800 lines (TypeScript + JSON).

### 8.3 Formatter

**New crate:** `03_PROTO/crates/riina-fmt/`

- Parse → pretty-print with consistent style
- 4-space indent, max 100 columns
- Configurable via `riina.toml` (future)
- `riinac fmt <file.rii>` CLI command
- Integration with LSP `textDocument/formatting`

**Estimated:** ~800 lines.

### 8.4 Documentation Generator

**New crate:** `03_PROTO/crates/riina-doc/`

- Parse `///` doc comments
- Generate HTML documentation
- Cross-reference types, functions, modules
- Show effect and security annotations
- `riinac doc` CLI command

**Estimated:** ~1,500 lines.

### 8.5 AI-Native Developer Experience

**Objective:** Make RIINA the first programming language designed from the ground up to be equally usable by human developers and AI coding agents (LLMs, code assistants, autonomous agents). This is not about marketing — it is about concrete, measurable properties that determine whether an AI can correctly generate, analyze, and reason about RIINA code.

**Why this matters:** Within 2-3 years, a significant portion of all code will be written or co-written by AI. A language that AI agents cannot fluently produce is a language that will not be adopted. RIINA's formal verification properties give it a unique advantage: AI-generated RIINA code can be *machine-checked for correctness*, closing the trust gap that plagues AI-generated code in other languages.

#### 8.5.1 Example Corpus (P0 — Critical Path)

**Goal:** 200+ annotated `.rii` example programs covering every language feature.

LLMs learn programming languages primarily from code examples in their training data and in-context examples. RIINA currently has 3 example files. This is the single biggest blocker to AI adoption.

**New directory:** `07_EXAMPLES/`

```
07_EXAMPLES/
├── 00_basics/              (20 files)
│   ├── hello_dunia.rii       — Hello World
│   ├── pembolehubah.rii      — Variables and types
│   ├── fungsi_mudah.rii      — Simple functions
│   ├── kalau_lain.rii        — Conditionals
│   ├── padan_corak.rii       — Pattern matching
│   ├── gelung.rii            — Loops (untuk, selagi, ulang)
│   ├── senarai.rii           — Lists
│   ├── tuple.rii             — Tuples (fst/snd)
│   ├── rekod.rii             — Records/structs
│   ├── enum.rii              — Sum types
│   ├── pilihan.rii           — Option type
│   ├── keputusan.rii         — Result type
│   ├── ralat.rii             — Error handling
│   ├── modul.rii             — Module system
│   ├── generik.rii           — Generics
│   ├── rentetan.rii          — String operations
│   ├── matematik.rii         — Math operations
│   ├── penukaran.rii         — Type conversions
│   ├── komen.rii             — Comments and documentation
│   └── import_eksport.rii    — Import/export
│
├── 01_security/            (20 files)
│   ├── rahsia_asas.rii       — Basic secret types
│   ├── dedah_dasar.rii       — Declassification with policy
│   ├── label_keselamatan.rii — Security labels
│   ├── aliran_maklumat.rii   — Information flow basics
│   ├── tiada_bocor.rii       — No-leak guarantees
│   ├── tercemar.rii          — Taint tracking
│   ├── bersih.rii            — Sanitization
│   ├── masa_tetap.rii        — Constant-time operations
│   ├── sifar_hapus.rii       — Zeroization
│   ├── kebenaran.rii         — Capability-based access
│   ├── require_grant.rii     — Effect permission model
│   ├── tahap_pelbagai.rii    — Multi-level security
│   ├── audit_trail.rii       — Audit logging
│   ├── pengesahan_kata.rii   — Password validation
│   ├── token_sesi.rii        — Session token handling
│   ├── kunci_api.rii         — API key management
│   ├── penyulitan.rii        — Encryption patterns
│   ├── tandatangan.rii       — Digital signatures
│   ├── sijil.rii             — Certificate handling
│   └── rbac.rii              — Role-based access control
│
├── 02_effects/             (15 files)
│   ├── kesan_io.rii          — IO effect basics
│   ├── kesan_fail.rii        — File I/O effect
│   ├── kesan_rangkaian.rii   — Network effect
│   ├── kesan_kripto.rii      — Crypto effect
│   ├── kesan_masa.rii        — Time effect
│   ├── kesan_rawak.rii       — Random effect
│   ├── kesan_berganda.rii    — Multiple effects
│   ├── kesan_komposisi.rii   — Effect composition
│   ├── pengendali.rii        — Effect handlers
│   ├── bersih_fungsi.rii     — Pure functions
│   ├── kesan_tersuai.rii     — Custom effects
│   ├── kesan_bersarang.rii   — Nested handlers
│   ├── kesan_resume.rii      — Resumptions
│   ├── kesan_had.rii         — Effect boundaries
│   └── kesan_modul.rii       — Module-level effect declarations
│
├── 03_applications/        (15 files)
│   ├── pelayan_web.rii       — Secure web server
│   ├── api_rest.rii          — REST API with security
│   ├── pangkalan_data.rii    — Database access
│   ├── mesej_kripto.rii      — Encrypted messaging
│   ├── dompet_digital.rii    — Digital wallet
│   ├── rekod_perubatan.rii   — Medical records (HIPAA)
│   ├── pembayaran.rii        — Payment processing (PCI-DSS)
│   ├── iot_sensor.rii        — IoT sensor data
│   ├── log_audit.rii         — Audit logging system
│   ├── pengesahan_2fa.rii    — Two-factor authentication
│   ├── oauth_pelayan.rii     — OAuth server
│   ├── cms_selamat.rii       — Secure CMS
│   ├── ci_cd.rii             — CI/CD pipeline tool
│   ├── cli_alat.rii          — CLI tool pattern
│   └── mikroperkhidmatan.rii — Microservice pattern
│
├── 04_compliance/          (10 files)
│   ├── pdpa_malaysia.rii     — Malaysia PDPA compliance
│   ├── pdpa_singapura.rii    — Singapore PDPA compliance
│   ├── hipaa.rii             — HIPAA compliance
│   ├── pci_dss.rii           — PCI-DSS compliance
│   ├── gdpr.rii              — GDPR compliance
│   ├── sox.rii               — SOX compliance
│   ├── do_178c.rii           — DO-178C aerospace
│   ├── iso_27001.rii         — ISO 27001 patterns
│   ├── cmmc.rii              — CMMC military compliance
│   └── iec_62443.rii         — IEC 62443 industrial
│
├── 05_patterns/            (15 files)
│   ├── pembina.rii           — Builder pattern
│   ├── kilang.rii            — Factory pattern
│   ├── pemerhati.rii         — Observer pattern
│   ├── strategi.rii          — Strategy pattern
│   ├── keadaan.rii           — State machine
│   ├── arahan.rii            — Command pattern
│   ├── pengulang.rii         — Iterator pattern
│   ├── saluran_paip.rii      — Pipeline pattern
│   ├── pengantara.rii        — Middleware pattern
│   ├── cqrs.rii              — CQRS pattern
│   ├── saga.rii              — Saga pattern (distributed tx)
│   ├── bulkhead.rii          — Bulkhead isolation
│   ├── pemutus_litar.rii     — Circuit breaker
│   ├── cuba_semula.rii       — Retry with backoff
│   └── kolam_sambungan.rii   — Connection pool
│
└── 06_ai_context/          (5 files)
    ├── RIINA_CHEATSHEET.md   — Compact reference (see 8.5.4)
    ├── RIINA_FOR_AI.md       — AI agent guide (see 8.5.4)
    ├── all_examples.rii      — Concatenated examples for context window
    ├── type_catalogue.rii    — Every type demonstrated
    └── effect_catalogue.rii  — Every effect demonstrated
```

**Requirements for every example file:**
1. Must compile with `riinac check` without errors
2. Must include `///` doc comments explaining what the program demonstrates
3. Must use Bahasa Melayu keywords (with English comments for clarity)
4. Must demonstrate exactly ONE concept clearly (not a kitchen sink)
5. Must be ≤ 80 lines (AI context window efficiency)

**Estimated total:** ~8,000 lines across 100 files (start), growing to 200+.

#### 8.5.2 Formal Grammar — Machine-Readable (P0)

**Goal:** A PEG grammar that tools and AI agents can consume directly.

**New file:** `04_SPECS/language/riina.peg`

Current grammar exists only as prose in markdown docs. A machine-readable PEG grammar enables:
- AI agents to validate their own generated code structure before compilation
- Tool builders to auto-generate parsers for linters, formatters, editors
- Precise, unambiguous syntax definition (prose specs have edge-case ambiguity)

The PEG grammar must be:
1. Derived directly from the Rust parser implementation (`03_PROTO/crates/riina-parser/`)
2. Tested against all 200+ example files (every example must parse)
3. Cross-referenced with Coq `Syntax.v` expression constructors
4. Include Bahasa Melayu and English keyword alternatives

**Format:** PEG (Parsing Expression Grammar) — widely supported by parser generators, unambiguous by definition, and trivially readable by LLMs.

**Estimated:** ~400 lines.

#### 8.5.3 Compiler Machine-Readable Output (P1)

**Goal:** `riinac` outputs structured data that AI agents can parse programmatically.

Current compiler output is human-readable text. AI agents work better with structured output.

**New flag:** `riinac check --output=json <file.rii>`

```json
{
  "file": "contoh.rii",
  "status": "error",
  "diagnostics": [
    {
      "severity": "error",
      "code": "E0312",
      "message": "type mismatch: expected Nombor, found Teks",
      "span": { "file": "contoh.rii", "line": 7, "col": 12, "len": 5 },
      "suggestions": [
        { "message": "try converting with tukar_nombor()", "replacement": "tukar_nombor(x)" }
      ]
    }
  ],
  "types": [
    { "name": "tambah", "type": "fungsi(Nombor, Nombor) -> Nombor", "effects": ["bersih"], "security": "Public" }
  ]
}
```

**New flag:** `riinac emit-ir --output=json <file.rii>` — structured IR for AI analysis.

This enables AI agents to:
- Parse errors programmatically and self-correct
- Understand type information for the code they generated
- Verify effect and security annotations

**Estimated:** ~500 lines (JSON serialization of existing diagnostics + type info).

#### 8.5.4 AI Context Files (P0)

**Goal:** Compact reference documents that fit in a single LLM context window and give an AI agent everything it needs to write correct RIINA code.

**File 1: `07_EXAMPLES/06_ai_context/RIINA_CHEATSHEET.md`** (~2,000 tokens)

A dense, structured quick-reference covering:
- All keywords (BM + English) with one-line examples
- All types with syntax
- All effects with usage
- Security level hierarchy
- Common patterns (3 lines each)
- Error handling idioms

This is what an AI agent reads before generating RIINA code. Every token must earn its place.

**File 2: `07_EXAMPLES/06_ai_context/RIINA_FOR_AI.md`** (~5,000 tokens)

An AI-agent-specific guide covering:
- How to structure a `.rii` file (imports, functions, entry point)
- The effect permission model (require/grant) with examples
- The security type model (Rahsia/dedah) with examples
- Common mistakes and how to avoid them
- How to read `riinac` error output and self-correct
- How to write code that the formal verifier can check

**File 3: `07_EXAMPLES/06_ai_context/all_examples.rii`** (~15,000 tokens)

Concatenation of the best 50 example files into a single file that an AI agent can load as context. Each section delimited with clear headers.

**Design principle:** These files are optimized for *token efficiency*. Every line teaches the AI something. No filler, no philosophy, no marketing — pure syntax and semantics.

#### 8.5.5 LSP as AI Agent Interface (P1)

**Extends section 8.1.** The LSP server is not just for VS Code — it is the universal interface for AI coding tools.

All major AI coding tools (GitHub Copilot, Cursor, Claude Code, Codeium, Windsurf) use LSP for:
- Real-time diagnostics (the AI sees type errors as it writes)
- Hover information (the AI queries types/effects/security levels)
- Completion (the AI gets valid completion candidates)
- Go-to-definition (the AI navigates the codebase)

**Additional LSP capabilities for AI agents:**

| LSP Method | AI Agent Use Case | Priority |
|------------|-------------------|----------|
| `textDocument/publishDiagnostics` | Self-correction loop: generate → check → fix | P0 |
| `textDocument/hover` | Query type + effect + security of any expression | P0 |
| `textDocument/completion` | Get valid completions in context | P1 |
| `textDocument/semanticTokens` | Understand token categories for generation | P2 |
| `riina/effectSummary` (custom) | Query full effect signature of a function | P2 |
| `riina/securityFlow` (custom) | Query information flow for a code region | P3 |

The custom RIINA LSP extensions (`riina/effectSummary`, `riina/securityFlow`) expose RIINA's unique formal verification capabilities to AI agents, enabling them to reason about security properties as they write code.

#### 8.5.6 WASM Playground with API (P2)

**Extends section 9.3 (Website).** Compile `riinac` to WebAssembly and expose it as an API.

**Endpoint:** `POST https://play.riina.dev/api/check`
```json
{ "code": "fungsi utama() -> Nombor { pulang 42; }" }
```
**Response:** Diagnostics + type info + effect summary (same as 8.5.3 JSON output).

This enables:
- AI agents to verify generated RIINA code via API without local installation
- Web-based tutorials and documentation with live code execution
- Integration with LLM tool-use (an LLM can call the API as a tool to check its own code)

#### 8.5.7 Why RIINA Has a Unique AI Advantage

This section documents the strategic rationale — why RIINA's properties make it fundamentally better for AI-generated code than any existing language:

1. **Formal verification closes the AI trust gap.** The #1 problem with AI-generated code is that humans cannot trust it. RIINA solves this: if `riinac check` passes, the code is *mathematically proven correct* for security properties. This makes AI-generated RIINA code trustworthy by construction.

2. **The effect system constrains AI output.** LLMs hallucinate. In most languages, hallucinated code can do anything (delete files, send network requests, leak data). In RIINA, the effect system physically prevents unauthorized operations. An AI agent that generates RIINA code for a `bersih` (pure) context *cannot* produce code that performs I/O — the compiler rejects it.

3. **Security types guide AI generation.** When an AI sees `Rahsia<Teks>` (secret string), it knows this value cannot be logged, printed, or sent over the network without explicit `dedah` (declassification). This is a structural constraint that makes correct code generation easier, not harder.

4. **Bilingual keywords reduce ambiguity.** Bahasa Melayu keywords are domain-specific identifiers that cannot collide with variable names. `fungsi` is always a function keyword — never a variable. This reduces parse ambiguity for both humans and AI.

5. **Regular syntax = predictable generation.** RIINA has 27 expression forms, a small orthogonal type system, and consistent syntax. This is far easier for an LLM to learn than languages with decades of accumulated syntax complexity.

#### 8.5.8 Verification Gate

Phase 4 AI-Native work is complete when:

- [x] 100+ example `.rii` files exist and compile cleanly — **100 files across 6 dirs (Session 56)**
- [ ] PEG grammar exists and parses all examples — *deferred to Phase 5*
- [ ] `riinac check --output=json` works — *deferred to Phase 5*
- [x] `RIINA_CHEATSHEET.md` fits in 2,000 tokens — **done (Session 56)**
- [x] `RIINA_FOR_AI.md` fits in 5,000 tokens — **done (Session 56)**
- [x] LSP server handles `publishDiagnostics` and `hover` — **done (Session 56, riina-lsp crate)**
- [ ] An LLM given only the cheatsheet + 10 examples can generate a valid `.rii` program — *manual test pending*

The final verification gate is empirical: **take an LLM that has never seen RIINA, provide it the AI context files, and ask it to write a program. If it compiles, the AI-native DX works.**

---

## 9. PHASE 5: ECOSYSTEM & DISTRIBUTION

### 9.1 CI/CD Pipeline

> **Status (Session 57, 2026-01-31): ✅ DONE (zero-trust).** Instead of GitHub Actions, RIINA uses `riinac verify [--fast|--full]` — an internal verification gate that runs cargo test, clippy, Coq admit/axiom scanning, and generates `VERIFICATION_MANIFEST.md`. This is the zero-trust approach: own the verification instead of trusting third-party CI infrastructure. See `03_PROTO/crates/riinac/src/verify.rs`.

**Reference design (GitHub Actions, NOT used — kept for documentation):**

**File: `.github/workflows/ci.yml`**

```yaml
name: CI
on: [push, pull_request]
jobs:
  rust-proto:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - name: Build prototype
        run: cd 03_PROTO && cargo build --all
      - name: Test prototype
        run: cd 03_PROTO && cargo test --all
      - name: Lint prototype
        run: cd 03_PROTO && cargo clippy -- -D warnings
      - name: Format check
        run: cd 03_PROTO && cargo fmt --check

  rust-tooling:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - name: Build tooling
        run: cd 05_TOOLING && cargo build --all
      - name: Test tooling
        run: cd 05_TOOLING && cargo test --all

  coq:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install Coq
        run: sudo apt-get install -y coq
      - name: Build proofs
        run: cd 02_FORMAL/coq && make
      - name: Check admits
        run: |
          count=$(grep -rc "Admitted" 02_FORMAL/coq/**/*.v 2>/dev/null | grep -v ':0$' | wc -l)
          echo "Files with admits: $count"

  examples:
    needs: rust-proto
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - name: Check examples
        run: |
          cd 03_PROTO
          for f in ../07_EXAMPLES/*.rii; do
            echo "Checking $f..."
            cargo run --bin riinac -- check "$f" || true
          done
```

**File: `.github/workflows/release.yml`** — triggered on version tags. Builds binaries for Linux/macOS/Windows, creates GitHub Release.

**Estimated:** ~200 lines YAML total.

### 9.2 Package Manager

> **Status (Session 57, 2026-01-31): ✅ DONE.** `riina-pkg` crate implemented with 14 modules, 39 tests. Integrated into riinac as `riinac pkg <command>` (10 subcommands: init/add/remove/update/lock/build/publish/list/tree/clean). Features: hand-written TOML parser, SemVer resolution, SHA-256 integrity, effect escalation checking, workspace support. Zero external dependencies.

Design (implemented):

**Manifest: `riina.toml`**
```toml
[pakej]
nama = "contoh"
versi = "0.1.0"
pengarang = ["Ahmad <ahmad@contoh.my>"]

[kebergantungan]
kripto = "1.0"

[kesan-dibenarkan]
IO = true
Crypto = true
Network = false  # This package cannot use network
```

**Security feature:** Packages declare required effects. Dependencies cannot escalate effects without explicit grant. This is enforced by the type system.

### 9.3 Website — ✅ DONE (Session 65)

**URL:** https://ib823.github.io/riina/
**Deployment:** `scripts/deploy-website.sh` → builds Vite/React app, pushes to `gh-pages` branch on `ib823/riina`
**Old URL:** `ib823.github.io/proof/` redirects to `/riina/` (redirect page on proof gh-pages)

**Pages implemented (14):**
1. Home — hero, 8 industry capability cards, key differentiators, code examples
2. **Why Proof** — executive-facing page for C-suite (CEO/CIO/CRO/CISO/CFO/Board): IBM breach cost data ($4.88M), assurance hierarchy (EAL1-EAL7), lock vs theorem analogy, quantum/AI immunity, real-world proof points (DARPA seL4, Paris Metro 25yr, AWS s2n/Zelkova, Microsoft HACL*, CompCert 6 CPU-yr, ProvenRun EAL7), Dijkstra quote, Kahneman loss aversion framing, 14 cited sources
3. Language — Bahasa Melayu syntax, type system, effects
4. How It Works — compilation pipeline, verification gate
5. Demos — 5 pre-recorded terminal demos, 3 showcase apps
6. **Enterprise** — 15 industry verticals (Defence, Healthcare, Financial, Aerospace, Energy, Telecom, Government, Transportation, Manufacturing/ERP, Retail, Media, Education, Agriculture, Real Estate, Legal), 15 regulatory frameworks, research depth banner (218 tracks, 1,231+ threats), 6 enterprise use cases
7. Releases — version cards, download links, install instructions
8. **Research** — 26 research domains (A-Z) with descriptions, 15 industry-specific links, proof statistics
9. Documentation — quick start, stdlib, contributing
10. Syntax, Security Types, Effect System, Examples — deep-dive pages
11. Legal — license, privacy, terms

**Deployment flow:**
- `bash scripts/deploy-website.sh` — standalone deploy
- `bash scripts/release.sh X.Y.Z` — includes website deploy automatically
- Website releases array auto-updated by release.sh via `// RELEASES_MARKER`

**Future:**
- Custom domain (`riina.my` or `riina.dev`) via CNAME
- Playground — in-browser RIINA editor (WASM-compiled riinac)
- Formal proofs explorer — browse Coq theorems

### 9.4 Distribution

1. **Binary releases:** Pre-built for Linux x86_64/aarch64, macOS x86_64/aarch64, Windows x86_64
2. **Package managers:** Homebrew, apt/dnf, Scoop
3. **Docker image:** `ghcr.io/ib823/riina:latest`
4. **WASM:** Compile riinac to WebAssembly for browser playground
5. **Nix flake:** Reproducible dev environments

### 9.5 Release System — ✅ DONE (Session 65)

**Files:**
- `VERSION` — Single-line semver source of truth
- `CHANGELOG.md` — Keep a Changelog format, public-facing
- `scripts/bump-version.sh` — Updates version in 6 locations (VERSION, 03_PROTO/Cargo.toml, 05_TOOLING/Cargo.toml, flake.nix, website/package.json, website footer)
- `scripts/release.sh` — One-command release workflow

**Release command:**
```bash
bash scripts/release.sh 0.2.0
```

This validates (clean main, tests pass), bumps version, finalizes CHANGELOG, commits + tags, pushes, builds tarball + SHA256SUMS, syncs to public, creates GitHub Release on ib823/riina, and updates website releases array.

**Tagging:** `v0.1.0` format (v-prefixed semver), annotated tags with changelog excerpt.

### 9.6 Licensing

**Recommended dual license:**
- **Compiler + Proofs + Stdlib:** MPL-2.0 (Mozilla Public License)
  - Programs written in RIINA can be proprietary
  - Modifications to the compiler must be shared
  - Proofs are publicly auditable
- **Enterprise tooling:** Proprietary (advanced IDE, compliance reports)

---

## 10. PHASE 6: ADOPTION & COMMUNITY

### 10.1 FFI (Foreign Function Interface) — ✅ DONE (Session 61)

**File:** `03_PROTO/crates/riina-codegen/src/ffi.rs`

**C FFI syntax:**
```riina
luaran "C" {
    fungsi puts(s: *CChar) -> CInt;
    fungsi abs(x: CInt) -> CInt;
}
```

**Implemented (Session 61):**
- `riina-types`: `RawPtr`, `CChar`, `CInt`, `CVoid`, `FFICall`, `ExternBlock`, `ExternDecl`
- `riina-parser`: `parse_extern_block()`, C type keywords, `*T` raw pointer syntax
- `riina-typechecker`: FFI calls typed with `Effect::System`
- `riina-codegen`: `FFICall` IR instruction, lowering, C emission, interpreter rejection
- `riina-codegen/ffi.rs`: `ty_to_c()` marshaling, `emit_extern_decl()` generation
- `riina-fmt` + `riina-doc`: Updated for new AST variants
- 14 new tests, 2 example files (`07_EXAMPLES/ffi/`)
- **Total: ~350 lines across 11 files**

### 10.2 Demo Applications — ✅ DONE (Session 62 + 64)

**5 runnable demos** in `07_EXAMPLES/demos/`:
- selamat_datang.rii (Hello Malaysia), rahsia_dijaga.rii (secret types), kalkulator_c.rii (C FFI), pasangan.rii (safe pairs), faktorial.rii (recursive functions)

**3 showcase demos** in `07_EXAMPLES/showcase/` (Session 64):

**Demo 1: Provably Secure Web Server** (`pelayan_web_selamat.rii`)
- HTTP handler where type system prevents injection
- Compiler PROVES: no SQL injection, no XSS, no path traversal, no information leakage

**Demo 2: Post-Quantum Encrypted Messenger** (`utusan_pasca_kuantum.rii`)
- E2E encrypted chat using ML-KEM + ML-DSA
- Compiler PROVES: keys zeroized, no plaintext leakage, constant-time comparison

**Demo 3: HIPAA-Compliant Medical Records** (`rekod_perubatan_hipaa.rii`)
- PHI (Protected Health Information) handling
- Compiler PROVES: PHI never escapes authorized scope, audit trail for all access

### 10.3 Community Building — ✅ DONE (Session 64)

1. ✅ GitHub repo with `CONTRIBUTING.md`, `.github/ISSUE_TEMPLATE/{bug_report,feature_request}.md`, `.github/PULL_REQUEST_TEMPLATE.md`
2. ⬜ Discord server (pending)
3. ✅ Documentation in English, Bahasa Melayu (`docs/i18n/README_ms.md`), Mandarin (`docs/i18n/README_zh.md`)
4. ⬜ Conference talks (POPL, ICFP, PLDI, RustConf, BlackHat/DEF CON) (pending)
5. ⬜ University partnerships (UM, UTM, USM, NUS, NTU, CMU, ETH, INRIA) (pending)
6. ⬜ Bug bounty for soundness bugs in formal proofs (pending)

### 10.4 Enterprise Adoption — ✅ DONE (Session 64)

1. ✅ **Compliance automation** — `docs/enterprise/COMPLIANCE_PACKAGING.md` (15 regulations, 150 compliance theorems)
2. ✅ **Security audit replacement** — formal proofs replace manual pentesting (documented in compliance packaging)
3. ✅ **Gradual adoption** — use RIINA for security-critical modules via FFI (C FFI done, 10.1)
4. ✅ **Certification** — `docs/enterprise/CERTIFICATION.md` (machine-checkable proof certificates)

### 10.5 Public Branch & Sync Infrastructure — ✅ DONE (Session 64)

- `public` branch set as GitHub default (internal files stripped)
- `scripts/sync-public.sh` — automated cherry-pick from validated main
- Mandatory flow: main → commit (verify --fast) → push (verify --full) → sync-public.sh
- Website live demos deployed via gh-pages

---

## 11. PHASE 7: PLATFORM UNIVERSALITY

Extend RIINA from native-only to **every platform** — web, mobile, embedded — with formally verified backend correctness. Platform targeting is a **compiler capability**, not a separate product.

Research backing: Track κ (Fullstack), Track λ (Mobile Platform), Track UX-01 (UI Verification), Track Mobile OS (1,850 theorems).

### 11.1 M7.1 — Backend Trait Architecture

Refactor `riina-codegen` from monolithic C-only to modular multi-backend:

1. Define `Backend` trait: `fn emit(&self, program: &Program) -> Result<Vec<u8>>`
2. Define `Target` enum: `Native`, `Wasm32`, `Wasm64`, `AndroidArm64`, `IosArm64`
3. Refactor `CEmitter` to implement `Backend` trait
4. Add `--target` flag to `riinac build` and `riinac emit`
5. Backend registry dispatches to correct emitter based on target

**Files:** `03_PROTO/crates/riina-codegen/src/backend.rs` (new), `lib.rs` (modify), `emit.rs` (modify), `03_PROTO/crates/riinac/src/main.rs` (modify)

### 11.2 M7.2 — WebAssembly Backend

Direct IR → WASM binary emission (no Emscripten dependency):

1. WASM binary encoder: section types, function bodies, instruction encoding
2. IR instruction mapping to WASM instructions (i32, i64, f64, memory, control flow)
3. WASM memory model: linear memory with RIINA security invariants preserved
4. DOM/Web API bindings via `luaran "wasm" { ... }` FFI syntax (extends existing `luaran "C"`)
5. `riinac build --target=wasm32` produces `.wasm` + JS glue

**Files:** `03_PROTO/crates/riina-codegen/src/wasm.rs` (new), `03_PROTO/crates/riina-codegen/src/wasm_encode.rs` (new)

### 11.3 M7.3 — Platform-Conditional Standard Library

Abstract POSIX assumptions so stdlib works on all targets:

1. Platform abstraction layer in codegen (conditional emission based on target)
2. Web target: file I/O → IndexedDB/OPFS, network → fetch API
3. Mobile target: platform-native I/O via FFI bridges
4. Compile-time platform detection: `#jika sasaran("wasm32")` / `#jika sasaran("android")`

**Files:** `03_PROTO/crates/riina-codegen/src/platform.rs` (new), updates to `emit.rs` and `wasm.rs`

### 11.4 M7.4 — Mobile Backend

Cross-compilation to mobile platforms via C backend + NDK/Xcode toolchains:

1. Android: `riinac build --target=android-arm64` → C → NDK → `.so`
2. iOS: `riinac build --target=ios-arm64` → C → Xcode → `.a`
3. JNI bridge generation for Android (auto-generate Java/Kotlin bindings)
4. Swift bridge generation for iOS (auto-generate Swift bindings)

**Files:** `03_PROTO/crates/riina-codegen/src/mobile.rs` (new), `jni.rs` (new), `swift_bridge.rs` (new)

### 11.5 M7.5 — WASM Playground

Compile `riinac` itself to WASM for browser-based editing:

1. `riinac` compiled via `cargo build --target=wasm32-unknown-unknown`
2. Web worker runs compiler, returns diagnostics + type info
3. Live editor with syntax highlighting, error reporting, effect visualization
4. Deployed at `ib823.github.io/riina/play`

**Files:** `website/src/playground/` (new directory), `03_PROTO/Cargo.toml` (WASM target config)

### 11.6 M7.6 — Platform Backend Verification

Coq proofs that platform backends preserve security invariants:

1. Prove WASM backend preserves non-interference (extends Track R)
2. Prove mobile bridges preserve capability safety
3. Prove platform-conditional stdlib maintains effect gate invariants

**Files:** `02_FORMAL/coq/domains/` (new platform verification files)

---

## 12. PHASE 8: LONG-TERM VISION

### 12.1 Self-Hosting

Rewrite `riinac` in RIINA itself:
1. RIINA lexer in RIINA
2. RIINA parser in RIINA
3. RIINA typechecker in RIINA
4. Prove self-hosted compiler correct (Track R)
5. Bootstrap: Rust compiler compiles RIINA compiler written in RIINA

### 12.2 Hardware Verification

Extend guarantees to hardware (Track S):
1. Model CPU execution (side-channel freedom)
2. Verify RIINA programs on specific hardware targets
3. Partner with RISC-V ecosystem

### 12.3 Verified Operating System

Build a verified microkernel using RIINA (Track U):
1. RIINA-based microhypervisor with proven isolation
2. Verified secure boot chain
3. Runs on commodity ARM/RISC-V hardware

### 12.4 Multi-Language Keywords (Mandarin, Hindi, Arabic, Tamil)

Extend the lexer to support additional native-language keyword sets:
1. Define keyword mappings per language
2. Lexer language selection via `#bahasa mandarin` pragma or CLI flag
3. Maintain Bahasa Melayu as default and reference syntax

### 12.5 Video & Content Strategy

1. 90-second "RIINA catches what Rust misses" demo video (terminal recording)
2. Axiom elimination blog post / video — from 92 to 4
3. Conference talk materials: POPL, ICFP, Black Hat, RustConf
4. Technical blog series on formal verification in practice

### 12.6 Revenue Model

1. Enterprise support contracts (SLA-backed)
2. Compliance certification service (auditor-ready proof packages)
3. Training: "RIINA for Security Engineers" course
4. Hosted verification service (CI/CD integration for teams)

### 12.7 Audience-Segmented Website

1. Developer landing: Playground → Docs → GitHub
2. CTO/Enterprise landing: Compliance matrix → Case studies → Pricing
3. Academic landing: Papers → Coq source → Formal specs
4. Security Researcher landing: Proof browser → Axiom list → Audit trail

### 12.8 Community Launch Strategy

1. Hacker News, r/programming, r/rust, lobste.rs announcements
2. "If it compiles, it's secure" positioning
3. Rust comparison content (technical, backed by proofs)
4. Academic paper submissions (formal verification venues)

---

## 13. EXECUTION ORDER & DEPENDENCY GRAPH

### 13.1 Phase 1 Internal Dependencies

```
IMMEDIATE (no dependencies, start in parallel):
+-- 5.1 Wire codegen into riinac (main.rs rewrite)
+-- 5.2 Lexer changes (new tokens, BM keywords, pipe operator)
+-- 9.1 CI/CD pipeline (.github/workflows/)
+-- 5.6 Error diagnostics (new crate/module)

AFTER 5.2 (lexer complete):
+-- 5.3.1 Statement sequences & blocks
+-- 5.3.3 Pipe operator (parser)
+-- 5.3.4 Guard clause (parser)

AFTER 5.3.1 (statements work):
+-- 5.3.2 Top-level function declarations
+-- 5.3.5 Multi-arm match
+-- 5.3.8 Extended type parsing

AFTER 5.3.2 (functions work):
+-- 5.3.6 For-in loop
+-- 5.3.7 While/loop (BLOCKED on decision — see section 15)
+-- 5.5 REPL
+-- 5.7 Built-in functions (arithmetic, I/O, strings)

AFTER 5.7 (builtins work):
+-- 5.4 C emitter completion (closures, phi nodes)
+-- 5.3.9 Module system (DEFERRED)

AFTER 5.3.9 (modules work):
+-- Phase 6: Standard library as .rii files
+-- Phase 9: Package manager
```

### 13.2 Phase 3 Internal Dependencies

```
IMMEDIATE (P0 — no dependencies, start in parallel):
+-- 7.2  Axiom & admit elimination (Track A, ongoing)
+-- 7.3  Domain file integration (add 118 files to _CoqProject)
+-- 7.4  Fix 3 uncompilable domain files
+-- 7.6  Rust evaluator implementation (new evaluator.rs)
+-- 7.9  Traceability index (ATTACK_PROOF_MAP.md)

AFTER 7.2 (0 axioms achieved):
+-- 7.5  Semantic completeness Phase 3A (TLabeled, TTainted, TCapability rules)
+-- 7.7.2 Option A: Add EBinOp to Coq (if chosen over Option B)
+-- 7.7.3 Formalize builtin signatures in Coq

AFTER 7.5 Phase 3A:
+-- 7.5  Phase 3B (ESanitize expression, effect context in step relation)
+-- 7.8  Create 10 missing tracks (AA-AJ)

AFTER 7.5 Phase 3B:
+-- 7.5  Phase 3C (TConstantTime timing model, TZeroizing memory model)
+-- 7.8  Prove web security, auth, hardware attack properties

CAN START IMMEDIATELY (Rust-only, no Coq dependency):
+-- 7.7.1 Add Expr::Loc(u64) to Rust
+-- 7.7.2 Option B: Desugar BinOp to App in Rust
```

### 13.3 Cross-Phase Dependencies

```
Phase 1 (Compiler)
    |
    +--> Phase 2 (Stdlib) -------> Phase 6 (Demos)
    |                               |
    +--> Phase 4 (DX) -----------> Phase 6 (Adoption)
    |                               |
    +--> Phase 5 (Ecosystem) ----> Phase 6 (Adoption)

Phase 3 (Formal Verification + Semantic Completeness)
    |
    +-- 7.2 Axiom elimination ──┐
    +-- 7.3 Domain integration  ├──> 7.5 Semantic completeness ──> 7.8 Threat coverage
    +-- 7.4 Fix uncompilable   ─┘        |
    +-- 7.6 Rust evaluator ──────────────> 7.11 Compiler correctness
    +-- 7.7 Alignment fixes ─────────────> Phase 1 (C emitter, builtins)
    +-- 7.9 Traceability ────────────────> Phase 6 (Enterprise, compliance)
    |
    +--> Phase 6 (Enterprise) --> Phase 7 (Platform) --> Phase 8 (Long-term)

Phase 7 (Platform Universality):
    M7.1 Backend Trait ──> M7.2 WASM Backend ──> M7.5 WASM Playground
    M7.1 Backend Trait ──> M7.3 Platform Stdlib
    M7.1 Backend Trait ──> M7.4 Mobile Backend
    M7.2 + M7.3 + M7.4 ──> M7.6 Formal Verification of Backends

Phase 6.1 (FFI) --> Phase 6.3 (Community) --> Phase 6.4 (Enterprise)
```

### 13.4 Critical Path

**Two parallel critical paths exist:**

**Path A (Compiler):**
```
5.2 Lexer --> 5.3.1 Statements --> 5.3.2 Functions --> 5.7 Builtins --> 5.4 C emitter --> 5.3.9 Modules --> Phase 6 Stdlib --> Phase 10 Demos
```

**Path B (Verification — NEW):**
```
7.2 Axiom elimination --> 7.5 Phase 3A (type enforcement) --> 7.5 Phase 3B (new expressions) --> 7.8 Threat coverage --> 7.10 Multi-prover --> Phase 10 Enterprise
```

**Paths A and B can proceed in parallel.** Path A is the compiler bottleneck (parser extension). Path B is the formal verification bottleneck (axiom elimination).

**Unblocked items (start immediately on both paths):**
- Path A: Lexer changes (5.2), wire codegen (5.1), CI/CD (9.1)
- Path B: Domain integration (7.3), Rust evaluator (7.6), Expr::Loc fix (7.7.1), traceability index (7.9)

---

## 14. FILES TO CREATE OR MODIFY

### 14.1 Phase 1 Files

| # | File | Action | Est. Lines | Depends On |
|---|------|--------|-----------|------------|
| 1 | `03_PROTO/crates/riinac/Cargo.toml` | MODIFY: add riina-codegen dep | +1 | — |
| 2 | `03_PROTO/crates/riinac/src/main.rs` | REWRITE: CLI subcommands, --bahasa flag | ~200 | — |
| 3 | `03_PROTO/crates/riina-lexer/src/token.rs` | MODIFY: 14 new TokenKind variants + Pipe | +20 | — |
| 4 | `03_PROTO/crates/riina-lexer/src/lexer.rs` | MODIFY: 13 BM equivalents + 14 new keyword mappings + pipe | +60 | #3 |
| 5 | `03_PROTO/crates/riina-lexer/src/error.rs` | MODIFY: bilingual errors, KeywordLanguageMismatch | +40 | — |
| 6 | `03_PROTO/crates/riina-types/src/lib.rs` | MODIFY: add TopLevelDecl, Program types | +30 | — |
| 7 | `03_PROTO/crates/riina-parser/src/lib.rs` | MAJOR EXTEND: statements, functions, pipe, guard, match, types | +700 | #3, #4, #6 |
| 8 | `03_PROTO/crates/riina-typechecker/src/lib.rs` | MODIFY: handle Program, multi-param functions | +100 | #6, #7 |
| 9 | `03_PROTO/crates/riina-codegen/src/builtins.rs` | CREATE: built-in function registry | ~400 | — |
| 10 | `03_PROTO/crates/riina-codegen/src/emit.rs` | MODIFY: closure captures, phi nodes, string ops | +250 | — |
| 11 | `03_PROTO/crates/riina-codegen/src/interp.rs` | MODIFY: integrate builtins | +50 | #9 |
| 12 | `03_PROTO/crates/riina-codegen/src/lib.rs` | MODIFY: re-export builtins module | +5 | #9 |
| 13 | `03_PROTO/crates/riina-span/src/diagnostics.rs` | CREATE: error diagnostic system | ~800 | — |
| 14 | `03_PROTO/crates/riinac/src/repl.rs` | CREATE: REPL implementation | ~300 | #7, #9 |
| 15 | `07_EXAMPLES/pengawal_input.rii` | CREATE: guard clause example | ~25 | — |
| 16 | `07_EXAMPLES/saluran_paip.rii` | CREATE: pipe operator example | ~20 | — |
| 17 | `07_EXAMPLES/keselamatan_kuantitatif.rii` | CREATE: quantitative declassification example | ~30 | — |

**Phase 1 Total: ~3,031 new/modified lines across 17 files.**

### 14.2 Phase 3 Files (Formal Verification & Semantic Completeness)

| # | File | Action | Est. Lines | Priority | Depends On |
|---|------|--------|-----------|----------|------------|
| 18 | `02_FORMAL/coq/_CoqProject` | MODIFY: add 118 domain file paths | +118 | P0 | — |
| 19 | `02_FORMAL/coq/domains/LinearTypes.v` | FIX: complete 1 Admitted proof | ~20 | P0 | — |
| 20 | `02_FORMAL/coq/domains/StandardLibrary.v` | FIX: replace 2 Parameters with definitions | ~40 | P0 | — |
| 21 | `02_FORMAL/coq/domains/VerifiedIdentity.v` | FIX: replace 1 Parameter with Inductive | ~30 | P0 | — |
| 22 | `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v` | PROVE: eliminate 5 axioms | ~500 | P0 | — |
| 23 | `02_FORMAL/coq/properties/NonInterference_v2.v` | PROVE: eliminate 1 axiom + 2 admits | ~200 | P0 | — |
| 24 | `03_PROTO/crates/riina-codegen/src/evaluator.rs` | CREATE: reference evaluator (31 step rules) | ~500 | P1 | — |
| 25 | `03_PROTO/crates/riina-types/src/lib.rs` | MODIFY: add `Expr::Loc(u64)` variant | +10 | P1 | — |
| 26 | `02_FORMAL/coq/foundations/Builtins.v` | CREATE: axiomatized builtin signatures | ~100 | P1 | #22 |
| 27 | `02_FORMAL/coq/foundations/Typing.v` | MODIFY: add TLabeled/TTainted enforcement rules | ~150 | P1 | #22 |
| 28 | `02_FORMAL/coq/foundations/Semantics.v` | MODIFY: add capability checking, sanitization semantics | ~200 | P1 | #22, #27 |
| 29 | `06_COORDINATION/ATTACK_PROOF_MAP.md` | CREATE: attack→theorem traceability index | ~400 | P2 | — |
| 30 | `01_RESEARCH/27_DOMAIN_AA_VERIFIED_IDENTITY/RESEARCH_AA01_FOUNDATION.md` | CREATE: Track AA foundation | ~300 | P2 | — |
| 31 | `01_RESEARCH/29_DOMAIN_AC_COVERT_CHANNELS/RESEARCH_AC01_FOUNDATION.md` | CREATE: Track AC foundation | ~300 | P2 | — |
| 32 | `01_RESEARCH/30_DOMAIN_AD_TIME_SECURITY/RESEARCH_AD01_FOUNDATION.md` | CREATE: Track AD foundation | ~300 | P2 | — |
| 33 | Remaining 7 track foundations (AE-AJ) | CREATE: 7 foundation documents | ~2,100 | P3 | — |

**Phase 3 Total: ~5,268 new/modified lines across 16+ files.**

### 14.3 Phase 4 Files (Developer Experience)

| # | File | Action | Est. Lines |
|---|------|--------|-----------|
| 34 | `03_PROTO/crates/riina-lsp/Cargo.toml` | CREATE | ~20 |
| 35 | `03_PROTO/crates/riina-lsp/src/lib.rs` | CREATE: LSP server | ~3,500 |
| 36 | `03_PROTO/Cargo.toml` | MODIFY: add riina-lsp to workspace | +1 |
| 37 | `riina-vscode/package.json` | CREATE | ~50 |
| 38 | `riina-vscode/syntaxes/riina.tmLanguage.json` | CREATE | ~300 |
| 39 | `riina-vscode/language-configuration.json` | CREATE | ~30 |
| 40 | `riina-vscode/snippets/riina.json` | CREATE | ~80 |
| 41 | `riina-vscode/src/extension.ts` | CREATE | ~100 |
| 42 | `03_PROTO/crates/riina-fmt/Cargo.toml` | CREATE | ~15 |
| 43 | `03_PROTO/crates/riina-fmt/src/lib.rs` | CREATE: formatter | ~800 |
| 44 | `03_PROTO/crates/riina-doc/Cargo.toml` | CREATE | ~15 |
| 45 | `03_PROTO/crates/riina-doc/src/lib.rs` | CREATE: doc generator | ~1,500 |

### 14.4 Phase 5 Files (Ecosystem)

| # | File | Action | Est. Lines | Status |
|---|------|--------|-----------|--------|
| 46 | `03_PROTO/crates/riinac/src/verify.rs` | CREATE: verification gate | ~400 | ✅ Done (Session 56) |
| 47 | `03_PROTO/crates/riina-pkg/` | CREATE: package manager (14 modules) | ~2,675 | ✅ Done (Session 57) |
| 48 | `.github/workflows/ci.yml` | DEFERRED | ~80 | ⬜ Superseded by `riinac verify` |
| 49 | `.github/workflows/release.yml` | DEFERRED | ~80 | ⬜ Pending (distribution) |
| 50 | `.github/workflows/nightly.yml` | DEFERRED | ~40 | ⬜ Superseded by `riinac verify` |

### 14.5 Phase 6 Files (Adoption)

| # | File | Action | Est. Lines |
|---|------|--------|-----------|
| 51 | `03_PROTO/crates/riina-codegen/src/ffi.rs` | CREATE: FFI support | ~200 |
| 52 | `08_DEMOS/web-server/` | CREATE: demo 1 | ~800 |
| 53 | `08_DEMOS/messenger/` | CREATE: demo 2 | ~800 |
| 54 | `08_DEMOS/medical/` | CREATE: demo 3 | ~800 |

---

## 15. VERIFICATION GATES

### Gate 1: Lexer + Driver (after 5.1, 5.2)

```bash
cd /workspaces/proof/03_PROTO
cargo build --all            # Must pass
cargo test --all             # Must pass (existing + new lexer tests)
cargo clippy -- -D warnings  # Must pass
cargo run --bin riinac -- check ../07_EXAMPLES/hello_dunia.rii  # Must work
```

### Gate 2: Parser (after 5.3)

```bash
cd /workspaces/proof/03_PROTO
cargo test --all             # All parser tests pass

# Parse function declarations:
echo 'fungsi f(x: Int) -> Int { x }' | cargo run --bin riinac -- check /dev/stdin

# Parse statement sequences:
echo 'biar x = 42; x' | cargo run --bin riinac -- check /dev/stdin

# Parse pipe:
echo 'biar f = fn(x: Int) x; 42 |> f' | cargo run --bin riinac -- check /dev/stdin
```

### Gate 3: End-to-End (after 5.4, 5.7)

```bash
# Interpret
cargo run --bin riinac -- run ../07_EXAMPLES/hello_dunia.rii
# Expected: prints result

# Emit C
cargo run --bin riinac -- emit-c ../07_EXAMPLES/hello_dunia.rii > /tmp/hello.c
cc -std=c99 -o /tmp/hello /tmp/hello.c
/tmp/hello
# Expected: prints result

# Build (automated)
cargo run --bin riinac -- build ../07_EXAMPLES/hello_dunia.rii -o /tmp/hello2
/tmp/hello2
# Expected: prints result
```

### Gate 4: CI/CD (after 9.1)

```bash
# GitHub Actions passes on push
git push origin main
# All jobs (rust-proto, rust-tooling, coq, examples) green
```

### Gate 5: Domain Integration (after 7.3)

```bash
cd /workspaces/proof/02_FORMAL/coq
make                                    # Must pass with 216+ files
wc -l _CoqProject                      # Must show 216+ entries
grep -rc "Admitted" domains/*.v         # Must be 0 (after 7.4 fixes)
```

### Gate 6: Rust Evaluator (after 7.6)

```bash
cd /workspaces/proof/03_PROTO
cargo test --all                        # Must pass
# Evaluator must handle all 31 step rules
cargo test -p riina-codegen evaluator   # All evaluator tests pass
```

### Gate 7: Coq Proofs — Zero Axioms (Track A, after 7.2)

```bash
cd /workspaces/proof/02_FORMAL/coq
make                                    # Must pass
grep -rc "Admitted" **/*.v              # Must be 0
grep -rc "admit\." **/*.v              # Must be 0
grep -c "Axiom" properties/*.v          # Must be 0 (core axioms eliminated)
```

### Gate 8: Semantic Completeness (after 7.5)

```bash
cd /workspaces/proof/02_FORMAL/coq
make                                    # Must pass
# TLabeled, TTainted, TCapability must have typing + semantic rules
grep -c "T_Labeled\|T_Tainted\|ST_RequireChecked" foundations/Typing.v foundations/Semantics.v
# Must show non-zero counts for each
```

### Gate 9: Threat Coverage (after 7.8)

```bash
# Traceability index must exist
cat 06_COORDINATION/ATTACK_PROOF_MAP.md | grep "PROVEN" | wc -l
# Target: ≥70 attacks with PROVEN status (Phase 3 target)
```

---

## 16. OPEN DECISIONS

### Decision 1: While Loop Termination Strategy

**Context:** `selagi` (while) loops break strong normalization if unrestricted.

**Options:**
- **A (RECOMMENDED):** Fuel-based — `selagi cond, had: 1000 { body }` desugars to bounded recursion. Provably terminates.
- **B:** Effect-gated — `selagi cond { body }` only allowed in `kesan Sistem` functions. Pure code guaranteed to terminate; effectful code not guaranteed.

**Impact:** Determines parser syntax and whether loops are available in pure functions.

**Decision needed before:** Implementing section 5.3.7.

### Decision 2: Module Resolution Strategy

**Context:** How does `modul foo;` find `foo`'s source code?

**Options:**
- **A (RECOMMENDED):** File-based (like Rust): `modul foo;` looks for `foo.rii` or `foo/lib.rii` relative to current file.
- **B:** Declaration-based (like OCaml): Modules are declared inline in the same file.

**Impact:** Determines file system layout and import semantics.

**Decision needed before:** Implementing section 5.3.9.

### Decision 3: Integer Representation

**Context:** `Expr::Int` currently holds `u64` (unsigned). RIINA programs may need negative numbers.

**Options:**
- **A:** Add `i64` support alongside `u64` — `Ty::Int` for signed, `Ty::Nat` for unsigned
- **B:** Use `i64` everywhere — simpler, covers most cases
- **C (RECOMMENDED):** Keep `u64` as the core representation (matches Coq's `nat`), add signed operations as library functions

**Impact:** Affects parser, typechecker, interpreter, C emitter.

**Decision needed before:** Implementing arithmetic builtins (section 5.7).

### Decision 4: Infix Operator Syntax

**Context:** Should RIINA have infix operators (`x + y`) or function-call style (`tambah x y`)?

**Options:**
- **A (RECOMMENDED):** Both — infix operators desugar to function calls. `x + y` becomes `App(App(Var("tambah"), x), y)`.
- **B:** Function-call only — simpler parser, but less ergonomic.

**Impact:** Determines parser complexity.

**Decision needed before:** Implementing arithmetic (section 5.7).

---

## APPENDIX A: COQ-RUST TYPE CORRESPONDENCE

This table shows the exact correspondence between Coq inductive types in `02_FORMAL/coq/foundations/Syntax.v` and Rust enums in `03_PROTO/crates/riina-types/src/lib.rs`.

### A.1 Security Levels

| Coq Constructor | Rust Variant | Numeric Level |
|----------------|-------------|---------------|
| `LPublic` | `SecurityLevel::Public` | 0 |
| `LInternal` | `SecurityLevel::Internal` | 1 |
| `LSession` | `SecurityLevel::Session` | 2 |
| `LUser` | `SecurityLevel::User` | 3 |
| `LSystem` | `SecurityLevel::System` | 4 |
| `LSecret` | `SecurityLevel::Secret` | 5 |

### A.2 Effects

| Coq Constructor | Rust Variant | Level | Category |
|----------------|-------------|-------|----------|
| `EffPure` | `Effect::Pure` | 0 | Pure |
| `EffRead` | `Effect::Read` | 1 | IO |
| `EffWrite` | `Effect::Write` | 2 | IO |
| `EffFileSystem` | `Effect::FileSystem` | 3 | IO |
| `EffNetwork` | `Effect::Network` | 4 | Network |
| `EffNetSecure` | `Effect::NetworkSecure` | 5 | Network |
| `EffCrypto` | `Effect::Crypto` | 6 | Crypto |
| `EffRandom` | `Effect::Random` | 7 | Crypto |
| `EffSystem` | `Effect::System` | 8 | System |
| `EffTime` | `Effect::Time` | 9 | System |
| `EffProcess` | `Effect::Process` | 10 | System |
| `EffPanel` | `Effect::Panel` | 11 | Product |
| `EffZirah` | `Effect::Zirah` | 12 | Product |
| `EffBenteng` | `Effect::Benteng` | 13 | Product |
| `EffSandi` | `Effect::Sandi` | 14 | Product |
| `EffMenara` | `Effect::Menara` | 15 | Product |
| `EffGapura` | `Effect::Gapura` | 16 | Product |

### A.3 Types

| Coq Constructor | Rust Variant | Parameters |
|----------------|-------------|-----------|
| `TUnit` | `Ty::Unit` | — |
| `TBool` | `Ty::Bool` | — |
| `TInt` | `Ty::Int` | — |
| `TString` | `Ty::String` | — |
| `TBytes` | `Ty::Bytes` | — |
| `TFn` | `Ty::Fn` | `(Box<Ty>, Box<Ty>, Effect)` |
| `TProd` | `Ty::Prod` | `(Box<Ty>, Box<Ty>)` |
| `TSum` | `Ty::Sum` | `(Box<Ty>, Box<Ty>)` |
| `TList` | `Ty::List` | `Box<Ty>` |
| `TOption` | `Ty::Option` | `Box<Ty>` |
| `TRef` | `Ty::Ref` | `(Box<Ty>, SecurityLevel)` |
| `TSecret` | `Ty::Secret` | `Box<Ty>` |
| `TLabeled` | `Ty::Labeled` | `(Box<Ty>, SecurityLevel)` |
| `TTainted` | `Ty::Tainted` | `(Box<Ty>, TaintSource)` |
| `TSanitized` | `Ty::Sanitized` | `(Box<Ty>, Sanitizer)` |
| `TProof` | `Ty::Proof` | `Box<Ty>` |
| `TCapability` | `Ty::Capability` | `CapabilityKind` |
| `TCapabilityFull` | `Ty::CapabilityFull` | `Capability` |
| `TChan` | `Ty::Chan` | `SessionType` |
| `TSecureChan` | `Ty::SecureChan` | `(SessionType, SecurityLevel)` |
| `TConstantTime` | `Ty::ConstantTime` | `Box<Ty>` |
| `TZeroizing` | `Ty::Zeroizing` | `Box<Ty>` |

### A.4 Expressions

| Coq Constructor | Rust Variant | Parameters |
|----------------|-------------|-----------|
| `EUnit` | `Expr::Unit` | — |
| `EBool` | `Expr::Bool` | `bool` |
| `EInt` | `Expr::Int` | `u64` |
| `EString` | `Expr::String` | `String` |
| `EVar` | `Expr::Var` | `Ident` |
| `ELam` | `Expr::Lam` | `(Ident, Ty, Box<Expr>)` |
| `EApp` | `Expr::App` | `(Box<Expr>, Box<Expr>)` |
| `EPair` | `Expr::Pair` | `(Box<Expr>, Box<Expr>)` |
| `EFst` | `Expr::Fst` | `Box<Expr>` |
| `ESnd` | `Expr::Snd` | `Box<Expr>` |
| `EInl` | `Expr::Inl` | `(Box<Expr>, Ty)` |
| `EInr` | `Expr::Inr` | `(Box<Expr>, Ty)` |
| `ECase` | `Expr::Case` | `(Box<Expr>, Ident, Box<Expr>, Ident, Box<Expr>)` |
| `EIf` | `Expr::If` | `(Box<Expr>, Box<Expr>, Box<Expr>)` |
| `ELet` | `Expr::Let` | `(Ident, Box<Expr>, Box<Expr>)` |
| `EPerform` | `Expr::Perform` | `(Effect, Box<Expr>)` |
| `EHandle` | `Expr::Handle` | `(Box<Expr>, Ident, Box<Expr>)` |
| `ERef` | `Expr::Ref` | `(Box<Expr>, SecurityLevel)` |
| `EDeref` | `Expr::Deref` | `Box<Expr>` |
| `EAssign` | `Expr::Assign` | `(Box<Expr>, Box<Expr>)` |
| `EClassify` | `Expr::Classify` | `Box<Expr>` |
| `EDeclassify` | `Expr::Declassify` | `(Box<Expr>, Box<Expr>)` |
| `EProve` | `Expr::Prove` | `Box<Expr>` |
| `ERequire` | `Expr::Require` | `(Effect, Box<Expr>)` |
| `EGrant` | `Expr::Grant` | `(Effect, Box<Expr>)` |
| `ELoc` | *(internal only)* | Heap location — not in source AST |

---

## APPENDIX B: BAHASA MELAYU KEYWORD REFERENCE

Complete bilingual keyword table. ALL of these should be recognized by the lexer.

### B.1 Currently Implemented (in lexer)

| Bahasa Melayu | English | TokenKind | Purpose |
|---------------|---------|-----------|---------|
| `fungsi` | `fn` | `KwFn` | Function declaration |
| `biar` | `let` | `KwLet` | Variable binding |
| `ubah` | `mut` | `KwMut` | Mutable modifier |
| `tetap` | `const` | `KwConst` | Constant |
| `kalau` | `if` | `KwIf` | Conditional |
| `lain` | `else` | `KwElse` | Alternative |
| `untuk` | `for` | `KwFor` | For loop |
| `selagi` | `while` | `KwWhile` | While loop |
| `ulang` | `loop` | `KwLoop` | Infinite loop |
| `pulang` | `return` | `KwReturn` | Return value |
| `padan` | `match` | `KwMatch` | Pattern match |
| `betul` | `true` | `KwTrue` | True literal |
| `salah` | `false` | `KwFalse` | False literal |
| `rahsia` | `secret` | `KwSecret` | Secret type |
| `dedah` | `declassify` | `KwDeclassify` | Declassify |
| `kesan` | `effect` | `KwEffect` | Effect annotation |
| `bentuk` | `struct` | `KwStruct` | Structure |
| `pilihan` | `enum` | `KwEnum` | Enumeration |
| `jenis` | `type` | `KwType` | Type alias |
| `sifat` | `trait` | `KwTrait` | Trait |
| `laksana` | `impl` | `KwImpl` | Implementation |
| `awam` | `pub` | `KwPub` | Public visibility |
| `modul` | `mod` | `KwMod` | Module |
| `guna` | `use` | `KwUse` | Import |
| `diri` | `self` | `KwSelf` | Self reference |
| `rujukan` | `ref` | `KwRef` | Reference |
| `lunas` | `inl` | `KwInl` | Left injection |
| `lunan` | `inr` | `KwInr` | Right injection |
| `dengan` | `with` | `KwWith` | With clause |
| `urus` | `handle` | `KwHandle` | Effect handler |
| `lakukan` | `perform` | `KwPerform` | Perform effect |
| `perlu` | `require` | `KwRequire` | Require capability |
| `beri` | `grant` | `KwGrant` | Grant capability |
| `sahkan` | `prove` | `KwProve` | Prove |
| `kelaskan` | `classify` | `KwClassify` | Classify |
| `keluar` | `break` | `KwBreak` | Break |
| `ulangi` | `continue` | `KwContinue` | Continue |
| `pagar` | `fence` | `KwFence` | Memory fence |
| `masa_tetap` | `constant_time` | `KwConstantTime` | Constant-time block |
| `berbilang` | `concurrent` | `KwConcurrent` | Concurrent block |
| `atom` | `atomic` | `KwAtomic` | Atomic operation |
| `saluran` | `channel` | `KwChannel` | Channel |
| `hantar` | `send` | `KwSend` | Send on channel |
| `terima` | `recv` | `KwRecv` | Receive from channel |

### B.2 To Be Added (from section 5.2)

| Bahasa Melayu | English | TokenKind | Purpose |
|---------------|---------|-----------|---------|
| `gabung` | `union` | `KwUnion` | Union type (BM alias) |
| `di_mana` | `where` | `KwWhere` | Where clause (BM alias) |
| `tercemar` | `tainted` | `KwTainted` | Tainted type (BM alias) |
| `bersihkan` | `sanitize` | `KwSanitize` | Sanitize (BM alias) |
| `keupayaan` | `capability` | `KwCapability` | Capability (BM alias) |
| `tarikbalik` | `revoke` | `KwRevoke` | Revoke (BM alias) |
| `turutan_ketat` | `seqcst` | `KwSeqCst` | Memory order (BM alias) |
| `longgar` | `relaxed` | `KwRelaxed` | Memory order (BM alias) |
| `peroleh_lepas` | `acqrel` | `KwAcqRel` | Memory order (BM alias) |
| `tak_segerak` | `async` | `KwAsync` | Async (BM alias) |
| `tunggu` | `await` | `KwAwait` | Await (BM alias) |
| `induk` | `super` | `KwSuper` | Super (BM alias) |
| `produk` | `product` | `KwProduct` | Product (BM alias) |
| `dan` | `and` | `KwAnd` | Logical AND (NEW) |
| `atau` | `or` | `KwOr` | Logical OR (NEW) |
| `bukan` | `not` | `KwNot` | Logical NOT (NEW) |
| `dalam` | `in` | `KwIn` | For-in (NEW) |
| `ialah` | `is` | `KwIs` | Type check (NEW) |
| `bersih` | `pure` | `KwPure` | Pure effect (NEW) |
| `selamat` | `safe` | `KwSafe` | Safe annotation (NEW) |
| `pinjam` | `borrow` | `KwBorrow` | Borrow (NEW) |
| `salin` | `copy` | `KwCopy` | Copy (NEW) |
| `klon` | `clone` | `KwClone` | Clone (NEW) |
| `jangka` | `lifetime` | `KwLifetime` | Lifetime (NEW) |
| `pastikan` | `guard` | `KwGuard` | Guard clause (NEW) |
| `dasar` | `policy` | `KwPolicy` | Declassification policy (NEW) |
| `sempadan` | `fence` | `KwFence` | Fence alias (NEW alias for `pagar`) |

---

## APPENDIX C: REJECTED PROPOSALS

These were proposed in `SYNTAX_IMPROVEMENT_SPEC_v1_0_0` and rejected. They are listed here so future implementors do not re-propose them.

| Proposal | Reason Rejected |
|----------|-----------------|
| Add `EffConstantTime` / `EffSpecSafe` to `effect` enum | Category error: constant-time and speculation-safety are verification properties, not computational effects. Would break all 17 effect matches across 25+ Coq files. Correct approach: separate analysis pass (section 4.2 of syntax spec). |
| Change `TFn` to take `effect_row` (list effect) | Would break every `TFn` match in all 222 .v Coq files. The current `effect_join` lattice approach is already sound. |
| Add `EFor` / `EWhile` / `ELoop` to core `expr` | `ELoop` (infinite loop) directly contradicts `well_typed_SN` (strong normalization theorem). Loops must be bounded or effectful. Parser desugaring is the correct approach. |
| Add 6 new `expr` constructors + admit downstream | Violates CLAUDE.md: "NO `admit.` — No tactical admits allowed." Every new constructor requires updating `subst`, `free_in`, `step`, `has_type`, `value` across 25+ files. |
| Add `TFloat` / `TChar` to Coq `ty` | Would break all `ty` matches across 222 files for no proof benefit. Defer until Phase 2+. |
| Sync SecurityLevel Rust 2→6 | Already done — Rust already has 6 levels. |
| Sync Effect Rust 6→17 | Already done — Rust already has 17 effects. |
| Sync Ty Rust 12→22 | Already done — Rust already has 22 types. |

---

## APPENDIX D: EXAMPLE .rii FILES

### D.1 `07_EXAMPLES/pengawal_input.rii` — Guard Clause

```riina
// pengawal_input.rii — Guard clause examples
// Demonstrates 'pastikan' (guard) syntax

// Guard: early return if condition fails
// pastikan <cond> lain { <early_return> };
// <continuation>

biar input = "hello";

pastikan betul lain {
    "input kosong"
};

input
```

### D.2 `07_EXAMPLES/saluran_paip.rii` — Pipe Operator

```riina
// saluran_paip.rii — Pipe operator examples
// x |> f  desugars to  f(x)

biar double = fn(x: Int) x;
biar identity = fn(x: Int) x;

42 |> identity |> double
```

### D.3 `07_EXAMPLES/keselamatan_kuantitatif.rii` — Security

```riina
// keselamatan_kuantitatif.rii — Security type demonstration
// Shows classify/declassify/prove workflow

biar kunci = classify 42;
biar bukti = prove betul;
biar nilai = declassify kunci with bukti;

nilai
```

---

## APPENDIX E: DEFERRED WORK (POST-PHASE 1)

These items require new Coq constructors or significant proof work. They MUST NOT be implemented until Phase 1 axiom elimination (17 admits → 0, 6 axioms → 0) is complete.

### E.1 Quantitative Declassification (Phase 2+)

New Coq file: `properties/DeclassificationPolicy.v` (~200 lines)

Defines `declassification_policy` record and proves that declassification respects budget constraints.

### E.2 ConstantTime Verification (Phase 3+)

New Coq file: `properties/ConstantTimeAnalysis.v` (~150 lines)

Defines what it means for a term to be constant-time and proves the property is preserved by evaluation.

### E.3 Effect Rows (Phase 3+)

If the single-effect `TFn` proves insufficient, add `TFnRow : ty -> ty -> list effect -> ty` as a NEW constructor alongside `TFn`, with a compatibility proof.

### E.4 New `expr` Constructors (Phase 2+)

Only after 0 axioms and 0 admits:

| Constructor | Justification | Impact per constructor |
|-------------|--------------|----------------------|
| `EMatch` | Multi-arm match (if parser desugaring insufficient) | ~50-100 lines across ~25 files |
| `EGuard` | Guard clause (only if parser desugaring insufficient) | ~50-100 lines |
| `EFor` | For loops (requires iterator protocol + termination proof) | ~80-120 lines |
| `EWhile` | While loops (requires bounded recursion proof) | ~80-120 lines |

---

*Document ID: RIINA_MATERIALIZATION_PLAN_v1_0_0*
*Status: AUTHORITATIVE*
*Date: 2026-01-30 (updated with exhaustive gap analysis from 4-agent audit)*
*Incorporates: 13-item remediation plan (P0-P3) from build integrity, type system enforcement, threat model coverage, and Coq↔Rust alignment audits*
*Mode: ULTRA KIASU | ZERO TRUST | ZERO ADMITS | ZERO AXIOMS TARGET*
*"QED Eternum."*
