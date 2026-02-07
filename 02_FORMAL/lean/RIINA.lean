-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

/-!
# RIINA Formal Proofs - Main Library

Multi-prover verification port from Coq 8.20.1 originals.
Provides independent verification of RIINA's type safety and security properties.

## Structure

- `RIINA.Foundations.Syntax` - Core syntax definitions (port of Syntax.v)
- `RIINA.Foundations.Semantics` - Operational semantics (port of Semantics.v)
- `RIINA.TypeSystem.Typing` - Typing rules (port of Typing.v)
- `RIINA.TypeSystem.Progress` - Progress theorem
- `RIINA.TypeSystem.Preservation` - Preservation theorem
- `RIINA.Effects.EffectSystem` - Effect system
- `RIINA.Properties.TypeSafety` - Type safety composition
- `RIINA.Properties.NonInterference` - Security property

## Verification Status

| Module | Coq Qed | Lean Theorems | Status |
|--------|---------|---------------|--------|
| Syntax | 3 | 5 | ✅ Ported |
| Semantics | 13 | 12 | ✅ Ported |
| Typing | TBD | TBD | Planned |

Mode: ULTRA KIASU | ZERO TRUST | ABSOLUTE FIDELITY
-/

import RIINA.Foundations.Syntax
import RIINA.Foundations.Semantics
import RIINA.TypeSystem.Typing
import RIINA.TypeSystem.Progress
import RIINA.TypeSystem.Preservation
import RIINA.TypeSystem.TypeSafety
import RIINA.Effects.EffectAlgebra
import RIINA.Effects.EffectSystem
import RIINA.Effects.EffectGate
import RIINA.Properties.NonInterference
import RIINA.Domains
import RIINA.Industries
