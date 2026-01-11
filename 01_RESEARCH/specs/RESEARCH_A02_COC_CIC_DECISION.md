# RESEARCH A-02: COC/CIC — DECISION DOCUMENT

## Version: 1.0.0
## Date: 2026-01-03
## Session: A-02
## Domain: A (Type Theory)
## Document Type: DECISION
## Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE

---

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║              SESSION A-02: COC/CIC BINDING DECISIONS                         ║
║                                                                              ║
║  AUTHORITATIVE DECISIONS FOR TERAS-LANG REGARDING COC/CIC FEATURES          ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

# EXECUTIVE DECISION

## The Question

**What features from the Calculus of Constructions (CoC) and Calculus of Inductive Constructions (CIC) should TERAS-LANG adopt?**

## The Answer

**TERAS-LANG SHALL ADOPT CIC-STYLE INDUCTIVE TYPES BUT REJECT IMPREDICATIVITY.**

The foundation remains Intensional MLTT (per A-01). From CIC, we adopt the practical machinery for inductive types while maintaining a fully predicative system.

---

# PART 1: PRIMARY DECISIONS

## Decision A-02-001: Impredicativity

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║  DECISION A-02-001: IMPREDICATIVITY REJECTION                                ║
║                                                                              ║
║  TERAS-LANG SHALL NOT have an impredicative sort.                           ║
║                                                                              ║
║  Specifically:                                                               ║
║  - NO impredicative Prop                                                    ║
║  - NO impredicative Set                                                     ║
║  - NO Church encodings of data types                                        ║
║  - ALL universes are predicative                                            ║
║                                                                              ║
║  STATUS: APPROVED                                                            ║
║  AUTHORITY: Research Track                                                   ║
║  EFFECTIVE: Immediately                                                      ║
║  REVERSIBILITY: NONE — This is final                                        ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

**Rationale**:
1. Impredicativity complicates metatheory
2. Creates axiom incompatibilities (classical + choice)
3. Requires complex elimination restrictions
4. Not needed for security verification
5. Universe polymorphism provides sufficient expressiveness
6. Aligns with MLTT foundation (A-01)

## Decision A-02-002: Sort Structure

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║  DECISION A-02-002: UNIVERSE STRUCTURE                                       ║
║                                                                              ║
║  TERAS-LANG SHALL have a single predicative universe hierarchy:             ║
║                                                                              ║
║      Type₀ : Type₁ : Type₂ : ...                                            ║
║                                                                              ║
║  - NO separate Prop sort                                                    ║
║  - NO separate Set sort                                                     ║
║  - Propositions are types with at most one inhabitant (by convention)       ║
║  - Proof erasure handled by quantitative types (see A-04, A-06)            ║
║                                                                              ║
║  STATUS: APPROVED                                                            ║
║  AUTHORITY: Research Track                                                   ║
║  EFFECTIVE: Immediately                                                      ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

**Rationale**:
1. Simpler than Coq's Prop/Set/Type
2. No elimination restrictions needed
3. Proof irrelevance via erasure (QTT style) not segregation
4. Follows Agda's uniform approach
5. Cleaner implementation

## Decision A-02-003: Inductive Types

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║  DECISION A-02-003: PRIMITIVE INDUCTIVE TYPES                               ║
║                                                                              ║
║  TERAS-LANG SHALL have primitive inductive types with CIC-style machinery:  ║
║                                                                              ║
║  REQUIRED:                                                                   ║
║  ├── Simple inductive types                                                  ║
║  ├── Parameterized inductive types                                           ║
║  ├── Indexed inductive families                                              ║
║  ├── Mutual inductive definitions                                            ║
║  ├── Strict positivity checking                                              ║
║  ├── Generated eliminators/recursors                                         ║
║  └── Dependent pattern matching                                              ║
║                                                                              ║
║  DEFERRED (study in later sessions):                                         ║
║  ├── Nested inductive types                                                  ║
║  ├── Inductive-inductive definitions                                         ║
║  ├── Inductive-recursive definitions                                         ║
║  └── Coinductive types                                                       ║
║                                                                              ║
║  REJECTED:                                                                   ║
║  └── Higher inductive types (HoTT)                                          ║
║                                                                              ║
║  STATUS: APPROVED                                                            ║
║  AUTHORITY: Research Track                                                   ║
║  EFFECTIVE: Immediately                                                      ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

**Rationale**:
1. Native induction essential for verification
2. CIC machinery is well-understood and battle-tested
3. Pattern matching crucial for practical programming
4. Advanced features can be added incrementally

## Decision A-02-004: Universe Polymorphism

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║  DECISION A-02-004: UNIVERSE POLYMORPHISM                                    ║
║                                                                              ║
║  TERAS-LANG SHALL support universe polymorphism (Lean 4 style):             ║
║                                                                              ║
║  FEATURES:                                                                   ║
║  ├── Universe level variables (u, v, w, ...)                                ║
║  ├── Level operations: 0, succ, max, imax                                    ║
║  ├── Universe constraints in definitions                                     ║
║  ├── Automatic level inference where possible                                ║
║  └── Explicit level annotations when needed                                  ║
║                                                                              ║
║  NOT INCLUDED:                                                               ║
║  ├── Universe cumulativity (use explicit lifting)                           ║
║  └── Universe unification (keeps type checking simpler)                      ║
║                                                                              ║
║  STATUS: APPROVED                                                            ║
║  AUTHORITY: Research Track                                                   ║
║  EFFECTIVE: Immediately                                                      ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

**Rationale**:
1. Avoids universe duplication
2. Enables generic programming
3. Non-cumulative is simpler (Lean approach)
4. imax crucial for dependent elimination

## Decision A-02-005: Pattern Matching

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║  DECISION A-02-005: DEPENDENT PATTERN MATCHING                              ║
║                                                                              ║
║  TERAS-LANG SHALL support dependent pattern matching with:                   ║
║                                                                              ║
║  ├── Coverage checking (exhaustiveness)                                      ║
║  ├── Reachability checking (no dead code)                                   ║
║  ├── Dependent case splitting                                                ║
║  ├── With-abstraction (Agda style)                                          ║
║  ├── Dot patterns for forced patterns                                       ║
║  └── Inaccessible patterns                                                   ║
║                                                                              ║
║  COMPILATION:                                                                ║
║  └── Pattern matching compiles to eliminators                                ║
║                                                                              ║
║  STATUS: APPROVED                                                            ║
║  AUTHORITY: Research Track                                                   ║
║  EFFECTIVE: Immediately                                                      ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

# PART 2: SECONDARY DECISIONS

## Decision A-02-006: Positivity Checking

**TERAS-LANG SHALL enforce strict positivity for inductive definitions.**

Algorithm: Syntactic positivity checking following CIC rules.

## Decision A-02-007: Termination Checking

**TERAS-LANG SHALL enforce termination for recursive definitions.**

Methods:
- Structural recursion (size decreases)
- Well-founded recursion (with Acc proofs)
- Guardedness for corecursion (if adopted)

## Decision A-02-008: Quotient Types

**TERAS-LANG SHALL study quotient types for potential future inclusion.**

Not included in initial design; may be added if needed for:
- Abstract data types
- Setoid hell avoidance
- Equivalence class constructions

Decision deferred to Session A-05 or later.

## Decision A-02-009: Implementation Reference

**TERAS-LANG implementation SHALL reference Lean 4 for performance patterns.**

Specifically:
- Bidirectional type checking
- Lazy normalization
- Universe constraint solving
- Native code generation

---

# PART 3: DECISION RATIONALE SUMMARY

## 3.1 Why Not Impredicativity?

| Concern | Impact | Decision |
|---------|--------|----------|
| Metatheory complexity | High | REJECT |
| Axiom conflicts | High | REJECT |
| Elimination restrictions | High | REJECT |
| Church encoding limitations | Medium | REJECT |
| Concise logic? | Low benefit | REJECT |

## 3.2 Why Adopt Inductive Types from CIC?

| Benefit | Value | Decision |
|---------|-------|----------|
| Native induction | Critical | ADOPT |
| Pattern matching | Critical | ADOPT |
| Efficient computation | Critical | ADOPT |
| Well-tested design | High | ADOPT |
| Extensibility | High | ADOPT |

## 3.3 Feature Origin Table

| Feature | Origin | Status |
|---------|--------|--------|
| Dependent types | MLTT | Foundation |
| Identity types | MLTT | Foundation |
| Predicative universes | MLTT | Foundation |
| Universe polymorphism | Lean/Agda | ADOPT |
| Primitive inductives | CIC | ADOPT |
| Pattern matching | CIC/Agda | ADOPT |
| Eliminators | CIC | ADOPT |
| Positivity checking | CIC | ADOPT |
| Termination checking | Agda | ADOPT |
| Impredicativity | CoC | REJECT |
| Prop/Set/Type | CIC | REJECT |
| Large elim. restrictions | CIC | REJECT |

---

# PART 4: IMPLEMENTATION IMPLICATIONS

## 4.1 Type Checker Architecture

```
TERAS TYPE CHECKER ARCHITECTURE (informed by A-02):
───────────────────────────────────────────────────

                    ┌─────────────────────┐
                    │   Surface Syntax    │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │   Elaboration       │
                    │   (Pattern Match    │
                    │    Compilation)     │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │   Core Type Theory  │
                    │   (MLTT + Inductives│
                    │    + Universe Poly) │
                    └──────────┬──────────┘
                               │
         ┌─────────────────────┼─────────────────────┐
         │                     │                     │
┌────────▼────────┐ ┌──────────▼──────────┐ ┌───────▼────────┐
│ Type Checking   │ │ Normalization       │ │ Universe       │
│ (Bidirectional) │ │ (Lazy, call-by-need)│ │ Constraint     │
│                 │ │                     │ │ Solving        │
└─────────────────┘ └─────────────────────┘ └────────────────┘
```

## 4.2 Inductive Definition Pipeline

```
INDUCTIVE DEFINITION PIPELINE:
──────────────────────────────

User Definition
      │
      ▼
┌─────────────────┐
│ Positivity      │  ──▶ Reject if non-positive
│ Check           │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Universe Level  │  ──▶ Compute minimal level
│ Inference       │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Recursor        │  ──▶ Generate ind_rec, ind_rect
│ Generation      │
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│ Computation     │  ──▶ Add ι-reduction rules
│ Rules           │
└────────┬────────┘
         │
         ▼
  Environment Entry
```

---

# PART 5: CROSS-REFERENCE

## 5.1 Related Decisions

| Decision | Session | Relationship |
|----------|---------|--------------|
| A-01-001 | A-01 | Foundation: MLTT |
| A-01-002 | A-01 | Extensional rejected |
| A-01-003 | A-01 | CwF semantics |
| A-02-001 | A-02 | Impredicativity rejected |
| A-02-003 | A-02 | Inductives adopted |

## 5.2 Future Sessions Affected

| Session | Topic | Dependency |
|---------|-------|------------|
| A-03 | System F/Polymorphism | Uses universe poly (A-02-004) |
| A-04 | Linear Types | Extends core (needs inductives) |
| A-05 | Refinement Types | Uses inductive predicates |
| A-06 | QTT | Alternative to Prop (per A-02-002) |

---

# PART 6: COMPLIANCE VERIFICATION

## 6.1 Immutable Laws Compliance

| Law | Status | Verification |
|-----|--------|--------------|
| Law 1: Biometric locality | N/A | Type theory level |
| Law 2: Cryptographic minimums | N/A | Type theory level |
| Law 3: Constant-time | Pending | Needs CT types |
| Law 4: Zeroization | Pending | Needs linear types |
| Law 5: Defense in depth | Compliant | Dependent types enable |
| Law 6: Fail secure | Compliant | Termination checking |
| Law 7: Auditability | Compliant | Type proofs are evidence |
| Law 8: Zero third-party | Compliant | No external dependencies |
| Law 9: Effect gate | Pending | Needs effect system |
| Law 10: Hardware attestation | N/A | Type theory level |
| Law 11: Governance | Compliant | Decision tracking |

## 6.2 Effect Gate Doctrine Alignment

**"Tak Ada Bukti, Tak Jadi Kesan"**

- Decidable type checking ✓
- Termination guaranteed ✓
- Proofs are values ✓
- Pattern matching is total ✓

---

# APPENDIX A: DECISION RECORD

```
DECISION RECORD A-02
────────────────────
Date: 2026-01-03
Session: A-02
Topic: Calculus of Constructions and CIC

DECISIONS MADE:
├── A-02-001: REJECT impredicativity
├── A-02-002: Single predicative universe hierarchy
├── A-02-003: ADOPT CIC-style inductive types
├── A-02-004: ADOPT universe polymorphism (Lean style)
├── A-02-005: ADOPT dependent pattern matching
├── A-02-006: Enforce strict positivity
├── A-02-007: Enforce termination
├── A-02-008: DEFER quotient types
└── A-02-009: Reference Lean 4 for implementation

DOCUMENTS PRODUCED:
├── RESEARCH_A02_COC_CIC_SURVEY.md (~1,100 lines)
├── RESEARCH_A02_COC_CIC_COMPARISON.md (~550 lines)
└── RESEARCH_A02_COC_CIC_DECISION.md (~400 lines)

NEXT SESSION: A-03 (System F, Polymorphism, Type Operators)
```

---

# DOCUMENT METADATA

```
Document: RESEARCH_A02_COC_CIC_DECISION.md
Version: 1.0.0
Session: A-02
Domain: A (Type Theory)
Type: DECISION
Status: COMPLETE
Lines: ~400
Created: 2026-01-03
Author: TERAS Research Track
Precedent: RESEARCH_A02_COC_CIC_COMPARISON.md
Successor: RESEARCH_A03_*
SHA-256: [To be computed on finalization]
```

---

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║  SESSION A-02: COMPLETE                                                      ║
║                                                                              ║
║  Documents Produced:                                                         ║
║  1. RESEARCH_A02_COC_CIC_SURVEY.md     (~1,100 lines)                       ║
║  2. RESEARCH_A02_COC_CIC_COMPARISON.md (~550 lines)                         ║
║  3. RESEARCH_A02_COC_CIC_DECISION.md   (~400 lines)                         ║
║                                                                              ║
║  Key Decisions:                                                              ║
║  - REJECT impredicativity                                                   ║
║  - ADOPT CIC inductive type machinery                                       ║
║  - ADOPT universe polymorphism (Lean style)                                 ║
║  - Single predicative universe hierarchy                                     ║
║                                                                              ║
║  Status: APPROVED                                                            ║
║                                                                              ║
║  Next: SESSION A-03 — System F and Polymorphism                             ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

**END OF DECISION DOCUMENT**
