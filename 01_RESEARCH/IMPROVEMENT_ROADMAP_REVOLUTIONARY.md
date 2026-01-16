# RIINA Revolutionary Improvement Roadmap

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  RIINA REVOLUTIONARY IMPROVEMENT ROADMAP                                         ║
║  Version: 1.0.0                                                                  ║
║  Date: 2026-01-16                                                                ║
║  Status: PLANNING DOCUMENT - DO NOT IMPLEMENT UNTIL APPROVED                     ║
║                                                                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE           ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

## Document Purpose

This document captures ALL identified improvements required to transform RIINA from
a "good research prototype" into a "revolutionary, first-in-human-history" security
language. It provides:

1. **Systematic categorization** of all improvements
2. **Dependency ordering** for implementation
3. **Effort estimates** (not time - complexity units)
4. **Verification criteria** for each improvement
5. **Non-conflicting implementation strategy**

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Improvement Categories](#2-improvement-categories)
3. [Phase 0: Foundation Fixes](#3-phase-0-foundation-fixes)
4. [Phase 1: Proof Completion](#4-phase-1-proof-completion)
5. [Phase 2: Performance Revolution](#5-phase-2-performance-revolution)
6. [Phase 3: Cryptographic Hardening](#6-phase-3-cryptographic-hardening)
7. [Phase 4: Verified Compilation](#7-phase-4-verified-compilation)
8. [Phase 5: Zero-Trust Bootstrap](#8-phase-5-zero-trust-bootstrap)
9. [Dependency Graph](#9-dependency-graph)
10. [Implementation Protocol](#10-implementation-protocol)
11. [Verification Checklist](#11-verification-checklist)

---

## 1. Executive Summary

### Current State Assessment

| Dimension | Current Score | Target Score | Gap |
|-----------|--------------|--------------|-----|
| Proof Completeness | 40% | 100% | 60% |
| Performance | 1x | 100x | 99x |
| Crypto Security | 60% | 100% | 40% |
| File Size Efficiency | 50% | 90% | 40% |
| Verified Compilation | 0% | 100% | 100% |
| Zero-Trust Build | 0% | 100% | 100% |

### Total Improvements Identified: 47

- **Critical (P0):** 12 improvements
- **High (P1):** 15 improvements
- **Medium (P2):** 12 improvements
- **Low (P3):** 8 improvements

### Estimated Total Effort: ~2,400 complexity units

(1 unit ≈ 1 focused work session of substantial progress)

---

## 2. Improvement Categories

### Category A: Formal Proofs (02_FORMAL/)
- A1: Axiom Elimination
- A2: Proof Completion
- A3: Data Structure Optimization
- A4: Effect System Enhancement
- A5: New Property Proofs

### Category B: Rust Implementation (03_PROTO/)
- B1: Lexer Performance
- B2: Parser Performance
- B3: Type Checker Performance
- B4: AST Optimization
- B5: Code Size Reduction

### Category C: Cryptography (05_TOOLING/)
- C1: AES Optimization
- C2: SHA-256 Optimization
- C3: Post-Quantum Implementation
- C4: Side-Channel Hardening
- C5: Hardware Acceleration

### Category D: Architecture
- D1: Verified Compilation Pipeline
- D2: Zero-Trust Bootstrap
- D3: Hardware Verification
- D4: Build Reproducibility

---

## 3. Phase 0: Foundation Fixes

**Goal:** Fix fundamental issues that block other improvements.
**Dependency:** None (can start immediately)
**Conflicts:** Minimal - mostly new files

### P0-001: Create Shared Constants Module

**Problem:** Magic numbers scattered across codebase.

**Solution:**
```
03_PROTO/crates/riina-constants/src/lib.rs (NEW FILE)
```

**Specification:**
```rust
// All security-critical constants in one place
pub mod crypto {
    pub const AES_BLOCK_SIZE: usize = 16;
    pub const AES_256_KEY_SIZE: usize = 32;
    pub const SHA256_BLOCK_SIZE: usize = 64;
    pub const SHA256_OUTPUT_SIZE: usize = 32;
    // ... etc
}

pub mod limits {
    pub const MAX_IDENTIFIER_LENGTH: usize = 255;
    pub const MAX_NESTING_DEPTH: usize = 256;
    pub const MAX_FUNCTION_PARAMS: usize = 255;
}
```

**Effort:** 5 units
**Priority:** P0
**Verification:** Compile succeeds, all tests pass

---

### P0-002: Create Symbol Table Infrastructure

**Problem:** String allocations everywhere.

**Solution:**
```
03_PROTO/crates/riina-symbols/src/lib.rs (NEW FILE)
```

**Specification:**
```rust
/// Interned symbol identifier (4 bytes instead of 24+ for String)
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(u32);

/// Global symbol table with interior mutability
pub struct SymbolTable {
    strings: Vec<Box<str>>,
    indices: std::collections::HashMap<&'static str, Symbol>,
}

impl SymbolTable {
    pub fn intern(&mut self, s: &str) -> Symbol;
    pub fn resolve(&self, sym: Symbol) -> &str;
}

// Thread-local or global singleton pattern
thread_local! {
    static SYMBOLS: RefCell<SymbolTable> = RefCell::new(SymbolTable::new());
}
```

**Effort:** 15 units
**Priority:** P0
**Verification:** Memory usage reduced, no functional changes

---

### P0-003: Create Arena Allocator

**Problem:** Box everywhere = heap fragmentation.

**Solution:**
```
03_PROTO/crates/riina-arena/src/lib.rs (NEW FILE)
```

**Specification:**
```rust
/// Typed arena for AST nodes
pub struct Arena<T> {
    chunks: Vec<Vec<T>>,
    current: usize,
}

/// Index into arena (lightweight alternative to Box)
#[derive(Clone, Copy)]
pub struct Idx<T>(u32, std::marker::PhantomData<T>);

impl<T> Arena<T> {
    pub fn alloc(&mut self, value: T) -> Idx<T>;
    pub fn get(&self, idx: Idx<T>) -> &T;
    pub fn get_mut(&mut self, idx: Idx<T>) -> &mut T;
}
```

**Effort:** 20 units
**Priority:** P0
**Verification:** Benchmarks show allocation improvement

---

### P0-004: Standardize Error Types

**Problem:** Each crate has different error handling.

**Solution:**
```
03_PROTO/crates/riina-errors/src/lib.rs (NEW FILE)
```

**Specification:**
```rust
/// Unified error type with source location
pub struct Diagnostic {
    pub severity: Severity,
    pub code: ErrorCode,
    pub message: String,
    pub span: Span,
    pub notes: Vec<Note>,
}

pub enum Severity {
    Error,
    Warning,
    Info,
    Hint,
}

/// Numeric error code for programmatic handling
#[derive(Clone, Copy)]
pub struct ErrorCode(u16);

// Error code ranges:
// 0000-0999: Lexer errors
// 1000-1999: Parser errors
// 2000-2999: Type errors
// 3000-3999: Effect errors
// 4000-4999: Security errors
```

**Effort:** 25 units
**Priority:** P0
**Verification:** All errors use unified format

---

## 4. Phase 1: Proof Completion

**Goal:** Eliminate ALL axioms and admitted lemmas.
**Dependency:** Phase 0 (for coordination)
**Conflicts:** HIGH - affects 02_FORMAL/coq/

### P1-001: Restructure Logical Relations

**Problem:** Current step-indexed relations require unprovable axioms.

**Current:**
```coq
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

**Solution:** Kripke-style with explicit world quantification.

**New Structure:**
```coq
(* World = step count + store typing *)
Record World := {
  w_step : nat;
  w_store_ty : store_ty;
}.

(* World ordering *)
Definition world_le (w1 w2 : World) : Prop :=
  w1.(w_step) >= w2.(w_step) /\  (* More steps = more restrictive *)
  store_ty_extends w1.(w_store_ty) w2.(w_store_ty).

(* Value relation indexed by world *)
Fixpoint val_rel (w : World) (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TFn T1 T2 eff =>
      forall w', world_le w w' ->
        forall x y, val_rel w' T1 x y ->
          (* ... uses w' not w, making weakening trivial *)
  | _ => (* first-order cases unchanged *)
  end.

(* Weakening is now PROVABLE by world_le transitivity *)
Lemma val_rel_weaken : forall w w' T v1 v2,
  world_le w w' ->
  val_rel w T v1 v2 ->
  val_rel w' T v1 v2.
Proof.
  (* Follows from structure *)
Qed.
```

**Files Affected:**
- `02_FORMAL/coq/properties/NonInterference.v` (MAJOR REWRITE)

**Effort:** 80 units
**Priority:** P1
**Verification:** `grep -r "Axiom\|Admitted" 02_FORMAL/coq/` returns empty

---

### P1-002: Complete Fundamental Theorem

**Problem:** `logical_relation` lemma is admitted.

**Current:**
```coq
Lemma logical_relation : forall Γ e T eff Σ,
  has_type Γ Σ e T eff ->
  (* ... 19+ cases, only ~10 done *)
Admitted.
```

**Solution:** Complete ALL cases systematically.

**Case Completion Checklist:**
- [ ] T_Unit
- [ ] T_Bool
- [ ] T_Int
- [ ] T_String
- [ ] T_Var
- [ ] T_Lam (COMPLEX - needs substitution lemma)
- [ ] T_App (COMPLEX - needs beta reduction preservation)
- [ ] T_Pair
- [ ] T_Fst
- [ ] T_Snd
- [ ] T_Inl
- [ ] T_Inr
- [ ] T_Case
- [ ] T_If
- [ ] T_Let
- [ ] T_Ref (needs store extension)
- [ ] T_Deref
- [ ] T_Assign
- [ ] T_Classify
- [ ] T_Declassify

**Effort:** 120 units (6 units average × 20 cases)
**Priority:** P1
**Verification:** `logical_relation` compiles with `Qed.`

---

### P1-003: Prove Store Relation Properties

**Problem:** Store relation properties use axioms.

**Axioms to Eliminate:**
```coq
Axiom store_rel_n_weaken : ...
Axiom val_rel_n_mono_store : ...
Axiom store_rel_n_mono_store : ...
```

**Solution:** Derive from Kripke structure (after P1-001).

**Effort:** 40 units
**Priority:** P1
**Dependency:** P1-001

---

### P1-004: Replace Linear Store with Efficient Structure

**Problem:** O(n) store lookups.

**Current:**
```coq
Definition store := list (loc * expr).
```

**Solution:** Use Coq's FMap or stdpp's gmap.

**New:**
```coq
Require Import Coq.FSets.FMapPositive.
Module LocMap := FMapPositive.PositiveMap.

Definition store := LocMap.t expr.

Definition store_lookup (l : loc) (st : store) : option expr :=
  LocMap.find (Pos.of_nat l) st.  (* O(log n) *)
```

**Files Affected:**
- `02_FORMAL/coq/foundations/Semantics.v`
- All files importing Semantics.v

**Effort:** 35 units
**Priority:** P1
**Verification:** All proofs still compile, complexity improved

---

### P1-005: Implement Proper Effect Lattice

**Problem:** Linear effect chain is too simplistic.

**Current:**
```coq
Inductive effect : Type :=
  | EffPure | EffRead | EffWrite | EffNetwork | EffCrypto | EffSystem.
```

**Solution:** Proper lattice with multiple dimensions.

**New:**
```coq
(* Effect as bit vector for lattice operations *)
Record effect := {
  eff_read : bool;
  eff_write : bool;
  eff_network : bool;
  eff_crypto : bool;
  eff_system : bool;
}.

Definition eff_pure : effect :=
  {| eff_read := false; eff_write := false;
     eff_network := false; eff_crypto := false; eff_system := false |}.

Definition eff_join (e1 e2 : effect) : effect :=
  {| eff_read := e1.(eff_read) || e2.(eff_read);
     eff_write := e1.(eff_write) || e2.(eff_write);
     (* ... *) |}.

Definition eff_leq (e1 e2 : effect) : Prop :=
  (e1.(eff_read) = true -> e2.(eff_read) = true) /\
  (* ... all fields *).

(* Prove lattice laws *)
Lemma eff_join_comm : forall e1 e2, eff_join e1 e2 = eff_join e2 e1.
Lemma eff_join_assoc : forall e1 e2 e3, ...
Lemma eff_join_idempotent : forall e, eff_join e e = e.
Lemma eff_leq_refl : forall e, eff_leq e e.
Lemma eff_leq_trans : forall e1 e2 e3, ...
Lemma eff_leq_antisym : forall e1 e2, ...
```

**Files Affected:**
- `02_FORMAL/coq/foundations/Syntax.v`
- `02_FORMAL/coq/effects/EffectAlgebra.v`
- All downstream files

**Effort:** 50 units
**Priority:** P1
**Verification:** All lattice laws proven

---

## 5. Phase 2: Performance Revolution

**Goal:** Achieve 100x performance improvement.
**Dependency:** Phase 0 complete
**Conflicts:** Modifies 03_PROTO/ extensively

### P2-001: SIMD-Accelerated Lexer

**Problem:** Char-by-char processing is slow.

**Current Performance:** ~10 MB/s
**Target Performance:** ~1 GB/s

**Implementation:**

```rust
// 03_PROTO/crates/riina-lexer/src/simd.rs (NEW FILE)

#[cfg(target_arch = "x86_64")]
mod x86_64 {
    use std::arch::x86_64::*;

    /// Find first non-whitespace byte using AVX2
    /// Returns offset from start, or len if all whitespace
    #[target_feature(enable = "avx2")]
    pub unsafe fn skip_whitespace_avx2(bytes: &[u8]) -> usize {
        let len = bytes.len();
        let mut offset = 0;

        // Process 32 bytes at a time
        while offset + 32 <= len {
            let chunk = _mm256_loadu_si256(bytes.as_ptr().add(offset) as *const __m256i);

            // Create masks for whitespace characters
            let spaces = _mm256_set1_epi8(b' ' as i8);
            let tabs = _mm256_set1_epi8(b'\t' as i8);
            let newlines = _mm256_set1_epi8(b'\n' as i8);
            let returns = _mm256_set1_epi8(b'\r' as i8);

            // Compare
            let is_space = _mm256_cmpeq_epi8(chunk, spaces);
            let is_tab = _mm256_cmpeq_epi8(chunk, tabs);
            let is_newline = _mm256_cmpeq_epi8(chunk, newlines);
            let is_return = _mm256_cmpeq_epi8(chunk, returns);

            // Combine: is whitespace?
            let is_ws = _mm256_or_si256(
                _mm256_or_si256(is_space, is_tab),
                _mm256_or_si256(is_newline, is_return)
            );

            // Find first non-whitespace
            let mask = _mm256_movemask_epi8(is_ws) as u32;
            if mask != 0xFFFFFFFF {
                // Found non-whitespace
                return offset + (!mask).trailing_zeros() as usize;
            }

            offset += 32;
        }

        // Scalar fallback for remainder
        while offset < len {
            let b = bytes[offset];
            if b != b' ' && b != b'\t' && b != b'\n' && b != b'\r' {
                return offset;
            }
            offset += 1;
        }

        len
    }

    /// Find next identifier boundary using AVX2
    #[target_feature(enable = "avx2")]
    pub unsafe fn scan_identifier_avx2(bytes: &[u8]) -> usize {
        // Similar pattern: check for [a-zA-Z0-9_] in bulk
        // ...
    }
}

// Fallback for non-x86
#[cfg(not(target_arch = "x86_64"))]
mod fallback {
    pub fn skip_whitespace(bytes: &[u8]) -> usize {
        bytes.iter().position(|&b| !b.is_ascii_whitespace()).unwrap_or(bytes.len())
    }
}
```

**Effort:** 40 units
**Priority:** P2
**Verification:** Benchmark shows >50x improvement on large files

---

### P2-002: Zero-Copy Token Stream

**Problem:** Tokens own their string data.

**Current:**
```rust
pub enum TokenKind {
    Identifier(String),  // Allocation!
    LiteralString(String),  // Allocation!
    // ...
}
```

**Solution:**
```rust
// 03_PROTO/crates/riina-lexer/src/token.rs (MODIFIED)

/// Token that borrows from source
pub struct Token<'src> {
    pub kind: TokenKind,
    pub span: Span,
    pub text: &'src str,  // Points into source, no allocation
}

pub enum TokenKind {
    Identifier,  // Text in Token.text
    LiteralString,  // Text in Token.text (after escape processing)
    LiteralInt,
    LiteralFloat,
    // Keywords are just enum variants, no data
    KwFn,
    KwLet,
    // ...
}
```

**Effort:** 30 units
**Priority:** P2
**Verification:** Zero allocations during lexing (check with DHAT)

---

### P2-003: Arena-Allocated AST

**Problem:** Every AST node is a heap allocation.

**Solution:**
```rust
// 03_PROTO/crates/riina-types/src/ast.rs (NEW FILE)

use riina_arena::{Arena, Idx};
use riina_symbols::Symbol;

pub type ExprIdx = Idx<ExprData>;
pub type TyIdx = Idx<TyData>;

/// All AST data stored in arenas
pub struct Ast {
    pub exprs: Arena<ExprData>,
    pub types: Arena<TyData>,
    pub spans: Arena<Span>,
}

/// Expression data without Box
pub enum ExprData {
    Unit,
    Bool(bool),
    Int(u64),
    String(Symbol),  // Interned
    Var(Symbol),

    Lam {
        param: Symbol,
        param_ty: TyIdx,
        body: ExprIdx,
    },
    App {
        func: ExprIdx,
        arg: ExprIdx,
    },
    Pair {
        fst: ExprIdx,
        snd: ExprIdx,
    },
    // ... all variants use indices, not Box
}

/// Type data without Box
pub enum TyData {
    Unit,
    Bool,
    Int,
    String,
    Bytes,
    Fn {
        param: TyIdx,
        ret: TyIdx,
        effect: Effect,
    },
    Prod {
        fst: TyIdx,
        snd: TyIdx,
    },
    // ...
}
```

**Migration Strategy:**
1. Create new `ast.rs` with arena types
2. Create conversion from old `Expr` to new `ExprData`
3. Update parser to use arenas directly
4. Remove old `Expr` type
5. Update all consumers

**Effort:** 60 units
**Priority:** P2
**Verification:** Memory usage reduced by 50%+, no functional change

---

### P2-004: Incremental Type Checking

**Problem:** Full recheck on every change.

**Solution:**
```rust
// 03_PROTO/crates/riina-typechecker/src/incremental.rs (NEW FILE)

use std::collections::HashMap;

/// Cached type checking results
pub struct TypeCache {
    /// Hash of expression → (type, effect)
    results: HashMap<u64, (TyIdx, Effect)>,
    /// Dependency tracking: expr hash → dependent expr hashes
    dependents: HashMap<u64, Vec<u64>>,
}

impl TypeCache {
    /// Check if cached result is still valid
    pub fn get(&self, expr_hash: u64) -> Option<(TyIdx, Effect)> {
        self.results.get(&expr_hash).copied()
    }

    /// Invalidate an expression and all its dependents
    pub fn invalidate(&mut self, expr_hash: u64) {
        if let Some(deps) = self.dependents.remove(&expr_hash) {
            for dep in deps {
                self.invalidate(dep);  // Recursive invalidation
            }
        }
        self.results.remove(&expr_hash);
    }
}
```

**Effort:** 45 units
**Priority:** P2
**Verification:** Incremental recheck is >10x faster than full check

---

### P2-005: Parallel Type Checking

**Problem:** Single-threaded type checking.

**Solution:**
```rust
// 03_PROTO/crates/riina-typechecker/src/parallel.rs (NEW FILE)

use rayon::prelude::*;

/// Type check multiple top-level definitions in parallel
pub fn type_check_module_parallel(
    defs: &[Definition],
    ctx: &SharedContext,
) -> Vec<Result<(TyIdx, Effect), TypeError>> {
    defs.par_iter()
        .map(|def| type_check_definition(def, ctx))
        .collect()
}

/// Thread-safe shared context (read-only during parallel phase)
pub struct SharedContext {
    /// Immutable symbol table
    symbols: Arc<SymbolTable>,
    /// Immutable type definitions
    type_defs: Arc<HashMap<Symbol, TyIdx>>,
}
```

**Effort:** 35 units
**Priority:** P2
**Dependency:** P2-003 (arena AST)
**Verification:** Parallel speedup on multi-core machines

---

## 6. Phase 3: Cryptographic Hardening

**Goal:** Production-ready, side-channel resistant crypto.
**Dependency:** None (independent track)
**Conflicts:** Modifies 05_TOOLING/

### P3-001: AES-NI Implementation

**Problem:** Software constant-time is 100-1000x slower.

**Solution:**
```rust
// 05_TOOLING/crates/teras-core/src/crypto/aes_ni.rs (NEW FILE)

#[cfg(all(target_arch = "x86_64", target_feature = "aes"))]
pub mod aesni {
    use std::arch::x86_64::*;

    pub struct Aes256Ni {
        round_keys: [__m128i; 15],
    }

    impl Aes256Ni {
        pub fn new(key: &[u8; 32]) -> Self {
            let mut round_keys = [unsafe { _mm_setzero_si128() }; 15];
            unsafe {
                // Load key
                let k0 = _mm_loadu_si128(key.as_ptr() as *const __m128i);
                let k1 = _mm_loadu_si128(key.as_ptr().add(16) as *const __m128i);
                round_keys[0] = k0;
                round_keys[1] = k1;

                // Key expansion using AESKEYGENASSIST
                macro_rules! expand_key {
                    ($i:expr, $rcon:expr) => {{
                        let temp = _mm_aeskeygenassist_si128(round_keys[$i * 2 + 1], $rcon);
                        // ... key expansion logic
                    }};
                }

                expand_key!(0, 0x01);
                expand_key!(1, 0x02);
                // ... remaining rounds
            }
            Self { round_keys }
        }

        #[inline]
        pub fn encrypt_block(&self, block: &mut [u8; 16]) {
            unsafe {
                let mut state = _mm_loadu_si128(block.as_ptr() as *const __m128i);

                // Initial round
                state = _mm_xor_si128(state, self.round_keys[0]);

                // Main rounds
                state = _mm_aesenc_si128(state, self.round_keys[1]);
                state = _mm_aesenc_si128(state, self.round_keys[2]);
                // ... rounds 3-13

                // Final round
                state = _mm_aesenclast_si128(state, self.round_keys[14]);

                _mm_storeu_si128(block.as_mut_ptr() as *mut __m128i, state);
            }
        }
    }
}
```

**Effort:** 30 units
**Priority:** P3
**Verification:** NIST test vectors pass, 50x+ speedup

---

### P3-002: Bitsliced AES for Non-Hardware

**Problem:** Need constant-time on platforms without AES-NI.

**Solution:**
```rust
// 05_TOOLING/crates/teras-core/src/crypto/aes_bitsliced.rs (NEW FILE)

/// Process 8 blocks in parallel using bitslicing
pub struct Aes256Bitsliced {
    round_keys_bs: [[u64; 8]; 15],  // Bitsliced round keys
}

impl Aes256Bitsliced {
    /// Encrypt 8 blocks simultaneously
    pub fn encrypt_blocks(&self, blocks: &mut [[u8; 16]; 8]) {
        // Transpose to bitsliced representation
        let mut state = transpose_to_bitsliced(blocks);

        // Apply rounds using boolean operations
        for round in 0..14 {
            // SubBytes as boolean circuit (no table lookups!)
            sbox_bitsliced(&mut state);

            // ShiftRows (permutation)
            shift_rows_bitsliced(&mut state);

            // MixColumns (linear, can be done with XOR)
            if round < 13 {
                mix_columns_bitsliced(&mut state);
            }

            // AddRoundKey (XOR)
            add_round_key_bitsliced(&mut state, &self.round_keys_bs[round]);
        }

        // Transpose back
        transpose_from_bitsliced(&state, blocks);
    }
}

/// S-box implemented as boolean circuit (constant-time)
fn sbox_bitsliced(state: &mut [u64; 8]) {
    // GF(2^8) inversion using ~30 AND + ~115 XOR gates
    // No memory access = no cache timing
    // ...
}
```

**Effort:** 60 units
**Priority:** P3
**Verification:** Constant-time verified with dudect, 10x+ speedup vs ct_lookup

---

### P3-003: Complete ML-KEM-768 Implementation

**Problem:** ML-KEM is stub only.

**Solution:** Full FIPS 203 implementation.

```rust
// 05_TOOLING/crates/teras-core/src/crypto/ml_kem.rs (COMPLETE REWRITE)

pub const N: usize = 256;
pub const K: usize = 3;  // ML-KEM-768
pub const Q: i16 = 3329;

/// Polynomial in R_q = Z_q[X]/(X^n + 1)
#[derive(Clone)]
pub struct Poly {
    coeffs: [i16; N],
}

/// NTT domain polynomial
#[derive(Clone)]
pub struct PolyNtt {
    coeffs: [i16; N],
}

impl Poly {
    /// Number Theoretic Transform
    pub fn ntt(&self) -> PolyNtt {
        let mut coeffs = self.coeffs;
        let mut k = 1;

        for len in [128, 64, 32, 16, 8, 4, 2] {
            for start in (0..N).step_by(2 * len) {
                let zeta = ZETAS[k];
                k += 1;
                for j in start..start + len {
                    let t = montgomery_mul(zeta, coeffs[j + len]);
                    coeffs[j + len] = coeffs[j] - t;
                    coeffs[j] = coeffs[j] + t;
                }
            }
        }

        PolyNtt { coeffs }
    }

    /// Inverse NTT
    pub fn inv_ntt(ntt: &PolyNtt) -> Poly {
        // ... inverse transform
    }
}

/// ML-KEM key pair
pub struct MlKemKeyPair {
    pub public: MlKemPublicKey,
    pub secret: MlKemSecretKey,
}

/// Key generation (Algorithm 15)
pub fn keygen(seed: &[u8; 64]) -> MlKemKeyPair {
    let (rho, sigma) = seed.split_at(32);

    // Generate A matrix
    let a: [[PolyNtt; K]; K] = sample_matrix(rho);

    // Sample secret and error
    let s: [Poly; K] = sample_cbd(sigma, 0);
    let e: [Poly; K] = sample_cbd(sigma, K as u8);

    // Compute public key
    let t: [PolyNtt; K] = /* A * NTT(s) + NTT(e) */;

    // ...
}

/// Encapsulation (Algorithm 17)
pub fn encaps(pk: &MlKemPublicKey, randomness: &[u8; 32]) -> (MlKemCiphertext, SharedSecret) {
    // ...
}

/// Decapsulation (Algorithm 18)
pub fn decaps(sk: &MlKemSecretKey, ct: &MlKemCiphertext) -> SharedSecret {
    // ... with implicit rejection
}
```

**Effort:** 100 units
**Priority:** P3
**Verification:** NIST KAT vectors pass

---

### P3-004: Complete ML-DSA-65 Implementation

**Problem:** ML-DSA is stub only.

**Solution:** Full FIPS 204 implementation.

**Effort:** 120 units
**Priority:** P3
**Verification:** NIST KAT vectors pass

---

### P3-005: X25519 Montgomery Ladder

**Problem:** X25519 is stub only.

**Solution:**
```rust
// 05_TOOLING/crates/teras-core/src/crypto/x25519.rs (COMPLETE REWRITE)

/// Field element in GF(2^255 - 19)
#[derive(Clone, Copy)]
pub struct Fe25519([u64; 5]);  // Radix 2^51 representation

impl Fe25519 {
    /// Constant-time conditional swap
    fn cswap(swap: u64, a: &mut Self, b: &mut Self) {
        let mask = 0u64.wrapping_sub(swap);
        for i in 0..5 {
            let t = mask & (a.0[i] ^ b.0[i]);
            a.0[i] ^= t;
            b.0[i] ^= t;
        }
    }

    /// Multiplication
    fn mul(&self, other: &Self) -> Self {
        // 5x5 → 9 limb product, then reduce
        // ...
    }

    /// Squaring (slightly faster than mul)
    fn square(&self) -> Self {
        // ...
    }

    /// Inversion via Fermat's little theorem
    fn invert(&self) -> Self {
        // a^(-1) = a^(p-2) where p = 2^255 - 19
        // Uses addition chain for efficiency
    }
}

/// X25519 scalar multiplication
pub fn x25519(k: &[u8; 32], u: &[u8; 32]) -> [u8; 32] {
    // Clamp scalar
    let mut k = *k;
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;

    // Montgomery ladder
    let mut x_1 = Fe25519::from_bytes(u);
    let mut x_2 = Fe25519::one();
    let mut z_2 = Fe25519::zero();
    let mut x_3 = x_1;
    let mut z_3 = Fe25519::one();

    let mut swap: u64 = 0;

    for pos in (0..255).rev() {
        let bit = ((k[pos >> 3] >> (pos & 7)) & 1) as u64;
        swap ^= bit;
        Fe25519::cswap(swap, &mut x_2, &mut x_3);
        Fe25519::cswap(swap, &mut z_2, &mut z_3);
        swap = bit;

        // Montgomery ladder step
        // ... standard formulas
    }

    Fe25519::cswap(swap, &mut x_2, &mut x_3);
    Fe25519::cswap(swap, &mut z_2, &mut z_3);

    // Compute x_2 * z_2^(-1)
    let result = x_2.mul(&z_2.invert());
    result.to_bytes()
}
```

**Effort:** 50 units
**Priority:** P3
**Verification:** RFC 7748 test vectors pass

---

## 7. Phase 4: Verified Compilation

**Goal:** Guarantee compiled code matches formal semantics.
**Dependency:** Phase 1 (proofs complete)
**Conflicts:** Creates new Track R infrastructure

### P4-001: Coq Extraction to OCaml

**Solution:** Extract type checker from Coq.

```coq
(* 02_FORMAL/coq/extraction/Extract.v (NEW FILE) *)

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import RIINA.type_system.Typing.

(* Configure extraction *)
Extraction Language OCaml.

(* Extract to file *)
Extraction "riina_extracted.ml" type_check.
```

**Effort:** 40 units
**Priority:** P4

---

### P4-002: Translation Validation

**Solution:** Verify Rust output matches Coq semantics.

**Effort:** 150 units
**Priority:** P4

---

## 8. Phase 5: Zero-Trust Bootstrap

**Goal:** Compiler bootstrapped from auditable hex.
**Dependency:** All previous phases
**Conflicts:** Creates new Track T infrastructure

### P5-001: Hex0 Assembler

**Effort:** 80 units
**Priority:** P5

### P5-002: Stage-1 C Compiler

**Effort:** 200 units
**Priority:** P5

### P5-003: Self-Hosting Verification

**Effort:** 100 units
**Priority:** P5

---

## 9. Dependency Graph

```
                    ┌─────────────────────────────────────────┐
                    │           PHASE 0: FOUNDATION           │
                    │  P0-001  P0-002  P0-003  P0-004         │
                    │  (const) (syms)  (arena) (errors)       │
                    └──────┬───────┬────────┬───────┬─────────┘
                           │       │        │       │
           ┌───────────────┼───────┼────────┼───────┼────────────────┐
           │               │       │        │       │                │
           ▼               ▼       ▼        ▼       ▼                ▼
    ┌──────────────┐ ┌──────────────────────────────────┐  ┌─────────────────┐
    │   PHASE 1    │ │          PHASE 2                 │  │    PHASE 3      │
    │    PROOFS    │ │        PERFORMANCE               │  │    CRYPTO       │
    │              │ │                                  │  │                 │
    │ P1-001 ──────┼─┤ P2-001 (SIMD lexer)             │  │ P3-001 (AES-NI) │
    │   │          │ │   │                              │  │   │             │
    │   ▼          │ │   ▼                              │  │   ▼             │
    │ P1-002 ──┐   │ │ P2-002 (zero-copy)              │  │ P3-002 (bitslice)│
    │   │      │   │ │   │                              │  │   │             │
    │   ▼      │   │ │   ▼                              │  │   ▼             │
    │ P1-003   │   │ │ P2-003 (arena AST) ◄────────────┼──┤ P3-003 (ML-KEM) │
    │   │      │   │ │   │                              │  │   │             │
    │   ▼      │   │ │   ├──► P2-004 (incremental)     │  │   ▼             │
    │ P1-004   │   │ │   │                              │  │ P3-004 (ML-DSA) │
    │   │      │   │ │   └──► P2-005 (parallel)        │  │   │             │
    │   ▼      │   │ │                                  │  │   ▼             │
    │ P1-005   │   │ │                                  │  │ P3-005 (X25519) │
    └────┬─────┘   │ └──────────────────────────────────┘  └────────┬────────┘
         │         │                                                │
         └─────────┼────────────────────────────────────────────────┘
                   │
                   ▼
           ┌──────────────┐
           │   PHASE 4    │
           │  VERIFIED    │
           │ COMPILATION  │
           │              │
           │ P4-001 ──────┤
           │   │          │
           │   ▼          │
           │ P4-002       │
           └──────┬───────┘
                  │
                  ▼
           ┌──────────────┐
           │   PHASE 5    │
           │  ZERO-TRUST  │
           │  BOOTSTRAP   │
           │              │
           │ P5-001 ──────┤
           │   │          │
           │   ▼          │
           │ P5-002 ──────┤
           │   │          │
           │   ▼          │
           │ P5-003       │
           └──────────────┘
```

---

## 10. Implementation Protocol

### 10.1 Conflict Avoidance Rules

1. **Check PROGRESS.md** before starting any task
2. **Check SESSION_LOG.md** for active work
3. **Never modify files currently being edited elsewhere**
4. **Create NEW files when possible** (less conflict risk)
5. **Use feature branches** for major changes
6. **Coordinate via 06_COORDINATION/COORDINATION_LOG.md**

### 10.2 Implementation Order for Non-Conflict

**Safe to start immediately (no conflicts with existing work):**
- P0-001: riina-constants (NEW crate)
- P0-002: riina-symbols (NEW crate)
- P0-003: riina-arena (NEW crate)
- P0-004: riina-errors (NEW crate)
- P3-001: aes_ni.rs (NEW file)
- P3-002: aes_bitsliced.rs (NEW file)

**Requires coordination (modifies existing files):**
- P1-*: All Coq changes
- P2-*: Most Rust changes
- P3-003+: Crypto rewrites

### 10.3 Branch Strategy

```
main
  │
  ├── feature/phase0-foundation
  │     ├── P0-001-constants
  │     ├── P0-002-symbols
  │     ├── P0-003-arena
  │     └── P0-004-errors
  │
  ├── feature/phase1-proofs
  │     ├── P1-001-kripke-relations
  │     └── ...
  │
  ├── feature/phase2-performance
  │     └── ...
  │
  └── feature/phase3-crypto
        └── ...
```

---

## 11. Verification Checklist

### Per-Improvement Verification

- [ ] Code compiles without warnings
- [ ] All existing tests pass
- [ ] New tests added for new functionality
- [ ] Benchmarks run (if performance-related)
- [ ] Memory checked (if allocation-related)
- [ ] No new axioms or admits (if proof-related)
- [ ] Documentation updated
- [ ] PROGRESS.md updated

### Phase Completion Verification

- [ ] All improvements in phase complete
- [ ] Integration tests pass
- [ ] Performance targets met
- [ ] Security audit passed (for crypto)
- [ ] Code review completed

---

## Appendix A: Effort Estimation Key

| Units | Description |
|-------|-------------|
| 5 | Simple change, < 100 LOC, well-understood |
| 15 | Moderate change, 100-500 LOC, some research |
| 30 | Significant change, 500-1000 LOC, design needed |
| 60 | Major feature, 1000-2000 LOC, complex design |
| 100+ | System-level change, extensive impact |

---

## Appendix B: File Change Matrix

| Improvement | New Files | Modified Files | Deleted Files |
|-------------|-----------|----------------|---------------|
| P0-001 | 1 | 0 | 0 |
| P0-002 | 1 | 0 | 0 |
| P0-003 | 1 | 0 | 0 |
| P0-004 | 1 | 0 | 0 |
| P1-001 | 0 | 1 | 0 |
| P1-002 | 0 | 1 | 0 |
| P2-001 | 1 | 1 | 0 |
| P2-002 | 0 | 1 | 0 |
| P2-003 | 1 | 3 | 1 |
| P3-001 | 1 | 0 | 0 |
| P3-002 | 1 | 0 | 0 |
| P3-003 | 0 | 1 | 0 |

---

*Document Status: PLANNING - Awaiting approval before implementation*
*Last Updated: 2026-01-16*
*Author: Claude Code Analysis*
