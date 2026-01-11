# RESEARCH A-02: COC/CIC — COMPARATIVE ANALYSIS

## Version: 1.0.0
## Date: 2026-01-03
## Session: A-02
## Domain: A (Type Theory)
## Document Type: COMPARISON
## Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE

---

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║              SESSION A-02: COC/CIC COMPARATIVE ANALYSIS                      ║
║                                                                              ║
║  SYSTEMATIC COMPARISON: MLTT vs CoC vs CIC vs LEAN vs TERAS NEEDS           ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

# EXECUTIVE SUMMARY

This comparison analyzes the Calculus of Constructions (CoC), Calculus of Inductive Constructions (CIC), and their variants against MLTT and TERAS requirements. The analysis reveals that while CIC provides practical benefits (inductive types, proof irrelevance), its impredicativity and complex sort structure conflict with TERAS's preference for clean, predicative foundations.

**Verdict**: MLTT remains the foundation; adopt CIC's inductive type machinery but avoid impredicativity.

---

# PART 1: FOUNDATION COMPARISON

## 1.1 MLTT vs CoC Matrix

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                        MLTT vs CoC COMPARISON MATRIX                              │
├────────────────────────┬───────────────────────────┬──────────────────────────────┤
│ Feature                │ MLTT (Intensional)        │ CoC (Pure)                   │
├────────────────────────┼───────────────────────────┼──────────────────────────────┤
│ Dependent Π-types      │ YES                       │ YES                          │
│ Dependent Σ-types      │ YES                       │ Encoded (impredicatively)    │
│ Identity types         │ YES (primitive)           │ Encoded (impredicatively)    │
│ Universes              │ Predicative hierarchy     │ Two sorts (* and □)          │
│ Polymorphism           │ Universe polymorphism     │ Impredicative                │
│ Inductive types        │ W-types or primitive      │ Encoded only                 │
│ Induction              │ YES                       │ NO (Church encodings)        │
│ Proof irrelevance      │ No (optional axiom)       │ No                           │
│ Decidability           │ YES                       │ YES                          │
│ Type:Type              │ NO (predicative)          │ NO (Prop : Type)             │
│ Normalization          │ Strong                    │ Strong                       │
├────────────────────────┴───────────────────────────┴──────────────────────────────┤
│ TERAS VERDICT: MLTT is simpler and more principled                               │
│                CoC adds impredicativity without clear benefit for security       │
└──────────────────────────────────────────────────────────────────────────────────┘
```

## 1.2 CIC Variants Comparison

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                        CIC VARIANTS COMPARISON MATRIX                             │
├─────────────────────┬─────────────┬─────────────┬─────────────┬──────────────────┤
│ Feature             │ CIC (orig)  │ pCIC        │ pCuIC       │ TERAS Need       │
├─────────────────────┼─────────────┼─────────────┼─────────────┼──────────────────┤
│ Prop sort           │ Impredicative│ Impredicative│ Impredicative│ Consider        │
│ Set sort            │ Impredicative│ PREDICATIVE │ Predicative │ Prefer pred.     │
│ Type hierarchy      │ Predicative │ Predicative │ Predicative │ YES              │
│ Cumulativity        │ Yes         │ Yes         │ Yes (+ ind) │ Optional         │
│ Inductive types     │ YES         │ YES         │ YES         │ YES              │
│ Large elimination   │ Restricted  │ Restricted  │ Restricted  │ Avoid            │
│ Classical logic     │ Breaks comp │ Compatible  │ Compatible  │ Prefer constr.   │
│ Axiom of choice     │ Inconsistent│ Compatible  │ Compatible  │ Avoid if poss.   │
├─────────────────────┴─────────────┴─────────────┴─────────────┴──────────────────┤
│ EVOLUTION: CIC → pCIC (Coq 8.0) → pCuIC (modern Coq/Rocq)                        │
│ TERAS VERDICT: If using CIC features, use pCIC predicative Set                   │
└──────────────────────────────────────────────────────────────────────────────────┘
```

## 1.3 PTS Instantiations

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                    PURE TYPE SYSTEMS COMPARISON                                   │
├─────────────┬─────────────────────────────────────────────────────────────────────┤
│ System      │ PTS Specification (S, A, R)                                         │
├─────────────┼─────────────────────────────────────────────────────────────────────┤
│ λ→ (STLC)  │ ({*,□}, {*:□}, {(*,*,*)})                                           │
│             │ Simply typed, no polymorphism, no dependencies                      │
├─────────────┼─────────────────────────────────────────────────────────────────────┤
│ λ2 (Sys F)  │ ({*,□}, {*:□}, {(*,*,*), (□,*,*)})                                 │
│             │ Polymorphism via (□,*,*) — types abstracted over                    │
├─────────────┼─────────────────────────────────────────────────────────────────────┤
│ λP          │ ({*,□}, {*:□}, {(*,*,*), (*,□,□)})                                 │
│             │ Dependent types via (*,□,□) — types depend on terms                 │
├─────────────┼─────────────────────────────────────────────────────────────────────┤
│ λC (CoC)    │ ({*,□}, {*:□}, {(*,*,*), (□,*,*), (*,□,□), (□,□,□)})              │
│             │ All four rules: polymorphism + dependency + type operators          │
├─────────────┼─────────────────────────────────────────────────────────────────────┤
│ MLTT-style  │ ({U₀,U₁,...,□}, {Uᵢ:Uᵢ₊₁}, {(Uᵢ,Uⱼ,U_{max(i,j)})})               │
│             │ Predicative universe hierarchy                                      │
├─────────────┴─────────────────────────────────────────────────────────────────────┤
│ ANALYSIS: CoC is "smaller" in sorts but "larger" in rules (impredicative)        │
│           MLTT is "larger" in sorts but "smaller" in rules (predicative)         │
│ TERAS: Prefer MLTT's predicative approach with bounded universe hierarchy        │
└──────────────────────────────────────────────────────────────────────────────────┘
```

---

# PART 2: IMPREDICATIVITY ANALYSIS

## 2.1 What Impredicativity Provides

```
BENEFITS OF IMPREDICATIVITY:
────────────────────────────
1. Concise logical encodings
   ∀P:Prop. P → P : Prop  (fits in Prop!)

2. Church encodings of data
   Nat := ∀X:Prop. X → (X→X) → X

3. Second-order quantification in logic
   ∀P. P ∨ ¬P  (LEM as single proposition)

4. Polymorphism without universe complications
   id : ∀A. A → A  (single definition)
```

## 2.2 What Impredicativity Costs

```
COSTS OF IMPREDICATIVITY:
─────────────────────────
1. Complex metatheory
   - Reducibility candidates required for SN proof
   - Set-theoretic models need special constructions

2. Axiom incompatibilities
   - Impredicative Set + Excluded Middle + Choice = INCONSISTENT
   - Required switch to predicative Set in Coq 8.0

3. Elimination restrictions
   - Cannot freely extract computational content from Prop
   - Singleton elimination rules are complex

4. No native induction for encodings
   - Church-encoded data lacks induction principle
   - Motivated CIC's primitive inductive types

5. Canonicity concerns
   - Closed terms may not compute to canonical form
   - Axioms can block computation
```

## 2.3 TERAS Impredicativity Decision

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                    IMPREDICATIVITY DECISION FOR TERAS                            │
├──────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│  DECISION: REJECT IMPREDICATIVITY FOR TERAS-LANG                                │
│                                                                                  │
│  RATIONALE:                                                                      │
│  1. Predicative universes are simpler and sufficient                            │
│  2. No axiom compatibility concerns                                             │
│  3. Cleaner metatheory (easier soundness proofs)                                │
│  4. No elimination restrictions needed                                          │
│  5. Universe polymorphism provides sufficient expressiveness                    │
│  6. Aligns with MLTT foundation (Session A-01)                                  │
│                                                                                  │
│  EXCEPTION: None. Impredicativity is not required for security verification.    │
│                                                                                  │
└──────────────────────────────────────────────────────────────────────────────────┘
```

---

# PART 3: INDUCTIVE TYPES COMPARISON

## 3.1 Approaches to Inductive Types

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                    INDUCTIVE TYPE APPROACHES                                      │
├─────────────────────┬────────────────────────────────────────────────────────────┤
│ Approach            │ Description                                                │
├─────────────────────┼────────────────────────────────────────────────────────────┤
│ Church Encodings    │ Impredicative encoding in pure CoC                         │
│ (CoC)               │ + Concise, no extension needed                             │
│                     │ - No induction, no large elimination                       │
├─────────────────────┼────────────────────────────────────────────────────────────┤
│ W-types             │ Single "well-founded tree" type in MLTT                    │
│ (MLTT)              │ + Minimal, all inductives encodable                        │
│                     │ - Verbose, poor computational behavior                     │
├─────────────────────┼────────────────────────────────────────────────────────────┤
│ Primitive Inductive │ First-class inductive definitions (CIC)                    │
│ (CIC)               │ + Native induction, good computation                       │
│                     │ + Flexible (indexed families, mutual, nested)              │
│                     │ - Requires positivity checking                             │
│                     │ - Extension to core theory                                 │
├─────────────────────┼────────────────────────────────────────────────────────────┤
│ Inductive Families  │ Indexed inductive types (Agda, Idris)                      │
│                     │ + Dependent pattern matching                               │
│                     │ + Expressive (vectors, red-black trees)                    │
│                     │ - Complex coverage checking                                │
├─────────────────────┴────────────────────────────────────────────────────────────┤
│ TERAS VERDICT: Adopt CIC-style primitive inductive types with inductive families │
│                This provides practical benefits without impredicativity          │
└──────────────────────────────────────────────────────────────────────────────────┘
```

## 3.2 Inductive Type Features

```
FEATURE COMPARISON:
───────────────────
                            │ CIC  │ Agda │ Lean │ TERAS
────────────────────────────┼──────┼──────┼──────┼───────
Simple inductive           │ YES  │ YES  │ YES  │ YES
Parameterized              │ YES  │ YES  │ YES  │ YES
Indexed (families)         │ YES  │ YES  │ YES  │ YES
Mutual inductive           │ YES  │ YES  │ YES  │ YES
Nested inductive           │ YES  │ YES  │ YES  │ YES
Inductive-inductive        │ NO   │ YES  │ NO   │ STUDY
Inductive-recursive        │ NO   │ YES  │ NO   │ STUDY
Higher inductive (HIT)     │ NO*  │ Cub. │ NO   │ NO
Coinductive                │ YES  │ YES  │ NO** │ STUDY
Quotient inductive (QIIT)  │ NO   │ Cub. │ Quot │ STUDY

* With axioms
** Lean uses explicit corecursion, not primitive coinduction
```

---

# PART 4: PROOF ASSISTANT COMPARISON

## 4.1 Coq/Rocq vs Lean vs Agda

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                    PROOF ASSISTANT COMPARISON                                     │
├─────────────────────┬─────────────────┬─────────────────┬─────────────────────────┤
│ Feature             │ Coq/Rocq        │ Lean 4          │ Agda                    │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Foundation          │ pCIC            │ CIC variant     │ MLTT-like               │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Prop sort           │ YES (impredicative)│ YES (impred) │ NO (optional)           │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Set sort            │ YES (predicative) │ NO            │ NO                      │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Cumulativity        │ YES             │ NO (use ulift)  │ YES                     │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Quotients           │ Setoid encoding │ Built-in axiom  │ Cubical (native)        │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Prop extensionality │ Axiom           │ Axiom           │ Axiom or Cubical        │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Func extensionality │ Axiom           │ From quotients  │ Axiom or Cubical        │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Proof irrelevance   │ Built-in (Prop) │ Built-in (Prop) │ Optional (--prop)       │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Tactics             │ Ltac2, SSReflect│ Lean DSL        │ Reflection              │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Code extraction     │ OCaml, Haskell  │ Native compile  │ Haskell, JS             │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Performance         │ Medium          │ HIGH            │ Medium                  │
├─────────────────────┼─────────────────┼─────────────────┼─────────────────────────┤
│ Math library        │ MathComp        │ Mathlib (huge)  │ agda-stdlib             │
├─────────────────────┴─────────────────┴─────────────────┴─────────────────────────┤
│ TERAS RELEVANCE:                                                                  │
│ - Coq: Reference for inductive types, tactics                                    │
│ - Lean: Reference for performance, metaprogramming                               │
│ - Agda: Reference for clean MLTT implementation                                  │
└──────────────────────────────────────────────────────────────────────────────────┘
```

## 4.2 Axiom Comparison

```
COMMON AXIOMS:
──────────────
                        │ Coq  │ Lean │ Agda │ TERAS
────────────────────────┼──────┼──────┼──────┼──────
Propositional Ext       │ Axiom│ Axiom│ Axiom│ AVOID*
Function Ext            │ Axiom│ Deriv│ Axiom│ STUDY
Excluded Middle         │ Axiom│ Axiom│ Axiom│ AVOID
Axiom of Choice         │ Axiom│ Axiom│ Axiom│ AVOID
Quotients               │ Axiom│ Axiom│ Cubic│ STUDY
Univalence              │ Axiom│ NO   │ Cubic│ NO

* TERAS prefers constructive foundations without axioms
```

---

# PART 5: ELIMINATION RULES COMPARISON

## 5.1 Elimination Restrictions

```
ELIMINATION INTO TYPE FROM PROP:
────────────────────────────────

COROCQ (pCIC):
├── Prop → Prop: Always allowed
├── Prop → Type: RESTRICTED (singleton/empty only)
├── Set → any: Always allowed
└── Type → any: Always allowed

LEAN 4:
├── Prop → Prop: Always allowed
├── Prop → Type: RESTRICTED (subsingleton only)
└── Type → any: Always allowed

AGDA (without --prop):
├── No Prop sort
└── All elimination allowed

TERAS CONSIDERATION:
├── Option A: No separate Prop (like Agda)
├── Option B: Prop with restrictions (like Lean)
└── Option C: Proof irrelevance via erasure (like QTT)
```

## 5.2 Subsingleton Elimination

```
SUBSINGLETON DEFINITION:
────────────────────────
A type T is a subsingleton if ∀(x y : T), x = y

SYNTACTIC APPROXIMATION (Lean):
├── At most one constructor
└── All constructor arguments are Prop

EXAMPLES:
├── Unit : Subsingleton ✓
├── Empty : Subsingleton ✓
├── True : Subsingleton ✓
├── a = b : Subsingleton ✓
├── Acc R x : Subsingleton ✓
└── ∃x, P x : NOT subsingleton ✗

TERAS: If using Prop, follow Lean's subsingleton approach
```

---

# PART 6: PERFORMANCE COMPARISON

## 6.1 Runtime Performance

```
EXTRACTION/COMPILATION:
───────────────────────
                        │ Method              │ Performance │ TERAS Relevance
────────────────────────┼─────────────────────┼─────────────┼────────────────
Coq → OCaml             │ Code extraction     │ Medium      │ Reference
Coq → Haskell           │ Code extraction     │ Lower       │ Not target
Lean 4 native           │ Direct compilation  │ HIGH        │ Model
Idris 2 → C/Scheme      │ Quantitative erasure│ HIGH        │ Model
Agda → Haskell          │ Code extraction     │ Medium      │ Reference

TERAS TARGET: Native compilation with >C performance (per Immutable Laws)
BEST REFERENCE: Lean 4 and Idris 2 approaches
```

## 6.2 Type Checking Performance

```
TYPE CHECKING FACTORS:
──────────────────────
1. Normalization strategy (lazy vs eager)
2. Conversion checking algorithm
3. Universe constraint solving
4. Tactic elaboration overhead

OBSERVED RANKINGS:
├── Lean 4: Fastest (optimized implementation)
├── Agda: Medium (intensive dependent matching)
├── Coq: Medium (Ltac overhead)
└── Idris 2: Medium (QTT overhead)

TERAS: Target Lean 4 performance level
```

---

# PART 7: SECURITY FEATURE ANALYSIS

## 7.1 Security-Relevant Features

```
SECURITY FEATURE MATRIX:
────────────────────────
                        │ CIC  │ Lean │ Agda │ TERAS Need
────────────────────────┼──────┼──────┼──────┼───────────
Dependent types         │ YES  │ YES  │ YES  │ MANDATORY
Linear types            │ NO   │ NO   │ NO*  │ MANDATORY
Effect tracking         │ NO   │ NO   │ NO   │ MANDATORY
Refinement types        │ NO   │ NO   │ NO   │ MANDATORY
Session types           │ NO   │ NO   │ NO   │ HIGH
Capability types        │ NO   │ NO   │ NO   │ HIGH
IFC labels              │ NO   │ NO   │ NO   │ CRITICAL
Constant-time types     │ NO   │ NO   │ NO   │ CRITICAL

* Agda has experimental --erasure feature
```

## 7.2 Gap Analysis

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                    CIC/COC SECURITY GAP ANALYSIS                                 │
├──────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│ CIC/CoC provides ~30% of TERAS security typing requirements:                     │
│                                                                                  │
│ PROVIDED:                                                                        │
│ ✓ Dependent types for invariants                                                │
│ ✓ Inductive types for data structure proofs                                     │
│ ✓ Strong normalization (termination)                                            │
│ ✓ Decidable type checking                                                       │
│                                                                                  │
│ MISSING:                                                                         │
│ ✗ Linear/affine types (memory safety)                                           │
│ ✗ Effect system (side effect control)                                           │
│ ✗ Refinement types (SMT-backed constraints)                                     │
│ ✗ Information flow control (confidentiality)                                    │
│ ✗ Session types (protocol verification)                                         │
│ ✗ Capability types (access control)                                             │
│ ✗ Constant-time types (timing side channels)                                    │
│                                                                                  │
│ CONCLUSION: CIC is insufficient alone; must be extended significantly           │
│                                                                                  │
└──────────────────────────────────────────────────────────────────────────────────┘
```

---

# PART 8: TERAS SYNTHESIS

## 8.1 Feature Adoption Matrix

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                    TERAS FEATURE ADOPTION FROM CIC                               │
├─────────────────────────────────────────────────────────────────────────────────┤
│                                                                                  │
│ ADOPT:                                                                          │
│ ┌────────────────────────────────────────────────────────────────────────────┐  │
│ │ ✓ Primitive inductive type machinery                                       │  │
│ │   - Positivity checking algorithm                                          │  │
│ │   - Recursor/eliminator generation                                         │  │
│ │   - Pattern matching compilation                                           │  │
│ │   - Inductive families (indexed types)                                     │  │
│ │                                                                            │  │
│ │ ✓ Universe polymorphism (Lean style)                                       │  │
│ │   - Level variables                                                        │  │
│ │   - max/imax operations                                                    │  │
│ │   - Universe constraints                                                   │  │
│ │                                                                            │  │
│ │ ✓ Guardedness checking (for recursive definitions)                         │  │
│ │                                                                            │  │
│ │ ✓ Decidable type checking architecture                                     │  │
│ └────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                  │
│ REJECT:                                                                          │
│ ┌────────────────────────────────────────────────────────────────────────────┐  │
│ │ ✗ Impredicative Prop                                                       │  │
│ │   Reason: Complicates metatheory, axiom conflicts                          │  │
│ │                                                                            │  │
│ │ ✗ Three-sort hierarchy (Prop/Set/Type)                                     │  │
│ │   Reason: Unnecessary complexity                                           │  │
│ │                                                                            │  │
│ │ ✗ Complex elimination restrictions                                         │  │
│ │   Reason: Follows from impredicativity we're rejecting                     │  │
│ │                                                                            │  │
│ │ ✗ Church encodings                                                         │  │
│ │   Reason: No benefits with primitive inductives                            │  │
│ └────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                  │
│ STUDY FURTHER:                                                                   │
│ ┌────────────────────────────────────────────────────────────────────────────┐  │
│ │ ? Coinductive types                                                        │  │
│ │   For infinite protocols, streams                                          │  │
│ │                                                                            │  │
│ │ ? Quotient types                                                           │  │
│ │   For abstract data types with equivalence                                 │  │
│ │                                                                            │  │
│ │ ? Proof irrelevance (via erasure, not Prop)                                │  │
│ │   For runtime performance                                                  │  │
│ └────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                  │
└──────────────────────────────────────────────────────────────────────────────────┘
```

## 8.2 Comparison Summary

| Criterion | Winner | Rationale |
|-----------|--------|-----------|
| Foundation simplicity | MLTT | Predicative, uniform |
| Inductive types | CIC | Well-engineered |
| Metatheory | MLTT | No impredicativity |
| Practical verification | CIC/Lean | Mature tooling |
| Performance model | Lean | Best compilation |
| Security extensions | Neither | Both need augmentation |

---

# APPENDIX: DECISION PREREQUISITES

This comparison provides input for the Session A-02 Decision Document.

**Key Questions Resolved**:
1. Impredicativity? → NO
2. Separate Prop sort? → STUDY FURTHER (consider erasure approach)
3. Inductive type scheme? → YES, adopt CIC style
4. Universe approach? → Predicative with universe polymorphism
5. Which implementation to study? → Lean 4 for performance, Agda for MLTT fidelity

---

# DOCUMENT METADATA

```
Document: RESEARCH_A02_COC_CIC_COMPARISON.md
Version: 1.0.0
Session: A-02
Domain: A (Type Theory)
Type: COMPARISON
Status: COMPLETE
Lines: ~550
Created: 2026-01-03
Author: TERAS Research Track
Precedent: RESEARCH_A02_COC_CIC_SURVEY.md
Successor: RESEARCH_A02_COC_CIC_DECISION.md
SHA-256: [To be computed on finalization]
```

---

**END OF COMPARISON DOCUMENT**
