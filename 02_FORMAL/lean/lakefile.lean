-- Copyright (c) 2026 The RIINA Authors. All rights reserved.

/-!
# RIINA Formal Proofs - Lean 4 Port

Multi-prover verification port from Coq 8.20.1 originals.
This provides independent verification of RIINA's core theorems.

Reference: 02_FORMAL/coq/ (authoritative Coq proofs)
-/

import Lake
open Lake DSL

package RIINA where
  version := v!"0.2.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib RIINA where
  roots := #[`RIINA]
  globs := #[.submodules `RIINA]

-- Mathlib dependency for advanced tactics
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.5.0"
