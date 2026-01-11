# RESEARCH A-02: CALCULUS OF CONSTRUCTIONS AND CIC — COMPLETE SURVEY

## Version: 1.0.0
## Date: 2026-01-03
## Session: A-02
## Domain: A (Type Theory)
## Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE

---

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║          SESSION A-02: CALCULUS OF CONSTRUCTIONS AND CIC                     ║
║                                                                              ║
║  COMPLETE EXHAUSTIVE SURVEY OF COC, CIC, PURE TYPE SYSTEMS                   ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

# EXECUTIVE SUMMARY

The Calculus of Constructions (CoC) and its extension, the Calculus of Inductive Constructions (CIC), form the theoretical foundation for the Coq/Rocq proof assistant and significantly influence other systems including Lean. This survey provides exhaustive coverage of CoC/CIC including their relationship to Pure Type Systems (PTS) and Barendregt's lambda cube.

**Key Findings for TERAS**:
- CoC combines MLTT dependent types with System F impredicative polymorphism
- CIC adds primitive inductive types, essential for practical verification
- Impredicativity of Prop creates both power and complexity
- Predicative Set (pCIC) required for consistency with classical axioms
- Pure Type Systems provide elegant unifying framework for type system taxonomy
- CIC deviates from pure MLTT in ways requiring careful analysis for TERAS

---

# PART 1: HISTORICAL DEVELOPMENT

## 1.1 Origins and Influences

### 1.1.1 De Bruijn's Automath (1968)

The Automath project (N.G. de Bruijn, 1968) pioneered:
- Machine-checked mathematical proofs
- Lambda calculus as proof language
- Types as propositions (early Curry-Howard)
- Influenced both MLTT and CoC development

### 1.1.2 Girard's System F (1972)

Jean-Yves Girard introduced System F (second-order lambda calculus):

```
KEY FEATURES:
├── Polymorphic types: ∀α.τ
├── Type abstraction: Λα.t
├── Type application: t[τ]
├── Impredicative quantification
└── Strong normalization proven

EXAMPLE:
id : ∀α.α → α
id = Λα.λx:α.x
```

System F provides the polymorphism component of CoC.

### 1.1.3 Martin-Löf's MLTT (1972-1984)

From Session A-01, MLTT provides:
- Dependent types (Π, Σ)
- Predicative universes
- Identity types
- Propositions-as-types

CoC synthesizes System F's impredicativity with MLTT's dependent types.

## 1.2 The Calculus of Constructions

### 1.2.1 Coquand's Thesis (1985)

Thierry Coquand's PhD thesis at University of Paris VII introduced CoC as an extension of Automath with higher-order features.

Key innovation: Unifying dependent types and polymorphism in a single system.

### 1.2.2 The 1988 Paper

The seminal publication:
- **Authors**: Thierry Coquand and Gérard Huet
- **Title**: "The Calculus of Constructions"
- **Journal**: Information and Computation 76 (2-3), 1988, pp. 95-120
- **DOI**: 10.1016/0890-5401(88)90005-3

### 1.2.3 Evolution to CIC (1988-1990)

Christine Paulin-Mohring (then Paulin) extended CoC with inductive types:

**Key Papers**:
1. Coquand, T. and Paulin, C. (1988/1990). "Inductively defined types." COLOG-88, LNCS 417.
2. Pfenning, F. and Paulin-Mohring, C. (1990). "Inductively defined types in the Calculus of Constructions." MFPS 1989, LNCS 442.
3. Paulin-Mohring, C. (1993). "Inductive definitions in the system Coq." TLCA 1993, LNCS 664.

### 1.2.4 Modern pCIC (2004+)

Coq 8.0 (2004) introduced predicative Set:
- Set became predicative by default
- Prop remains impredicative
- Flag `-impredicative-set` preserves old behavior
- Required for consistency with classical axioms + choice

---

# PART 2: PURE TYPE SYSTEMS FRAMEWORK

## 2.1 The Pure Type Systems Formalism

Pure Type Systems (PTS) provide a uniform framework for specifying typed lambda calculi.

### 2.1.1 PTS Definition

A PTS is specified by a triple (S, A, R):

```
S = Set of SORTS
    Examples: {*, □}, {Prop, Set, Type}, {Type₀, Type₁, ...}

A ⊆ S × S = AXIOMS (specifying sort hierarchy)
    Examples: (* : □), (Prop : Type), (Type_i : Type_{i+1})

R ⊆ S × S × S = RULES (specifying product formation)
    Rule (s₁, s₂, s₃) means:
    If A : s₁ and B : s₂ then (Πx:A.B) : s₃
```

### 2.1.2 PTS Typing Rules

```
Γ ⊢ A : s₁    Γ, x:A ⊢ B : s₂    (s₁, s₂, s₃) ∈ R
─────────────────────────────────────────────────── (PRODUCT)
              Γ ⊢ (Πx:A.B) : s₃

Γ, x:A ⊢ b : B    Γ ⊢ (Πx:A.B) : s
────────────────────────────────── (ABSTRACTION)
     Γ ⊢ (λx:A.b) : (Πx:A.B)

Γ ⊢ f : (Πx:A.B)    Γ ⊢ a : A
────────────────────────────── (APPLICATION)
       Γ ⊢ (f a) : B[a/x]

      (s₁, s₂) ∈ A
────────────────────── (AXIOM)
      ⊢ s₁ : s₂

Γ ⊢ A : B    B =β B'    Γ ⊢ B' : s
─────────────────────────────────── (CONVERSION)
            Γ ⊢ A : B'
```

## 2.2 Barendregt's Lambda Cube

### 2.2.1 The Eight Systems

The lambda cube (λ-cube) organizes eight type systems along three dimensions:

```
                        λC (CoC)
                       /   |
                      /    |
                λP2 ─┼─ λPω
                |    |    |
                |    |    |
              λ2 ─┼─ λω
               |     |    |
               |     |    |
             λP ──┼── λω_
              |      |
              |      |
            λ→ ─────┘

DIMENSIONS:
├── Terms depending on Types (→): Polymorphism (λ2, System F)
├── Types depending on Terms (↑): Dependent Types (λP)
└── Types depending on Types (→): Type Operators (λω_)
```

### 2.2.2 System Specifications

| System | S | A | R | Features |
|--------|---|---|---|----------|
| λ→ | {*, □} | {*:□} | {(*,*,*)} | Simply typed |
| λ2 | {*, □} | {*:□} | {(*,*,*), (□,*,*)} | Polymorphism |
| λP | {*, □} | {*:□} | {(*,*,*), (*,□,□)} | Dependent types |
| λω_ | {*, □} | {*:□} | {(*,*,*), (□,□,□)} | Type operators |
| λP2 | {*, □} | {*:□} | {(*,*,*), (□,*,*), (*,□,□)} | Poly + Dep |
| λPω_ | {*, □} | {*:□} | {(*,*,*), (*,□,□), (□,□,□)} | Dep + Ops |
| λω | {*, □} | {*:□} | {(*,*,*), (□,*,*), (□,□,□)} | System Fω |
| λC | {*, □} | {*:□} | All four rules | CoC |

### 2.2.3 CoC as λC

CoC sits at the apex of the lambda cube:

```
CALCULUS OF CONSTRUCTIONS (λC)
──────────────────────────────
S = {*, □}           (* = Prop, □ = Type)
A = {* : □}
R = {(*,*,*),        Terms depending on terms
     (□,*,*),        Terms depending on types (polymorphism)
     (*,□,□),        Types depending on terms (dependent types)
     (□,□,□)}        Types depending on types (type operators)
```

## 2.3 Properties of Pure Type Systems

### 2.3.1 Strong Normalization

All systems in the lambda cube are strongly normalizing:
- Every well-typed term has a normal form
- All reduction sequences terminate
- Proven using Girard's reducibility candidates method

**Theorem (Barendregt)**: All lambda cube systems are strongly normalizing.

### 2.3.2 The Barendregt-Geuvers-Klop Conjecture

**Conjecture**: For all PTS, weak normalization implies strong normalization.

Status: Open problem, proven for certain subclasses.

### 2.3.3 Decidability

For strongly normalizing PTS:
- Type checking is decidable
- Type inference is decidable for some systems
- Crucial for implementation

---

# PART 3: CALCULUS OF CONSTRUCTIONS DETAIL

## 3.1 Syntax and Judgments

### 3.1.1 Terms

```
ABSTRACT SYNTAX:
t, u, A, B ::= x          (variable)
             | s          (sort: Prop or Type)
             | Πx:A.B     (dependent product)
             | λx:A.t     (abstraction)
             | t u        (application)
```

### 3.1.2 Judgments

CoC uses four forms of judgment:

```
1. Γ ctx         Γ is a well-formed context
2. Γ ⊢ A : s     A is a well-formed type of sort s in Γ
3. Γ ⊢ t : A     t has type A in context Γ
4. Γ ⊢ t ≡ u : A t and u are definitionally equal at type A
```

### 3.1.3 The Product Rule

The key rule that distinguishes CoC:

```
Γ ⊢ A : s₁    Γ, x:A ⊢ B : s₂
──────────────────────────────── (PROD)
      Γ ⊢ (Πx:A.B) : s₂

Where (s₁, s₂) ∈ {(Prop, Prop), (Prop, Type), (Type, Prop), (Type, Type)}
```

The rule `(Type, Prop)` enables quantification over all types into Prop — **impredicativity**.

## 3.2 Impredicativity

### 3.2.1 What is Impredicativity?

A definition is **impredicative** if it quantifies over a domain that includes the entity being defined.

```
IMPREDICATIVE EXAMPLE:
─────────────────────
∀P:Prop. P → P : Prop

This type quantifies over ALL propositions,
including itself!
```

### 3.2.2 Church Encodings

Impredicativity enables Church-style encodings of data types:

```
NATURAL NUMBERS (Church encoding):
──────────────────────────────────
Nat := ∀X:Prop. X → (X → X) → X

zero : Nat
zero = λX:Prop. λz:X. λs:(X→X). z

succ : Nat → Nat
succ = λn:Nat. λX:Prop. λz:X. λs:(X→X). s (n X z s)

BOOLEANS:
─────────
Bool := ∀X:Prop. X → X → X

true  = λX. λt. λf. t
false = λX. λt. λf. f
```

### 3.2.3 Limitations of Church Encodings

Church encodings lack native **induction principles**:

```
PROBLEM:
────────
We cannot prove: ∀n:Nat. P(n) by induction

The Church-encoded Nat has no structural recursion principle!
```

This limitation motivated the development of CIC.

## 3.3 Consistency of CoC

### 3.3.1 Girard's Paradox (Why Not Type:Type)

Recall from Session A-01: Type:Type leads to inconsistency via Girard's paradox (encoding of Burali-Forti).

CoC avoids this by:
- Having Prop : Type (not Prop : Prop)
- Having Type : □ (external kind, not in theory)

### 3.3.2 Consistency Proof

Strong normalization implies consistency:

**Theorem (Coquand 1985)**: CoC is strongly normalizing.

**Corollary**: CoC is consistent (cannot derive ⊥ : Prop).

Proof methods:
- Reducibility candidates (Girard's technique)
- Logical relations
- Set-theoretic models

---

# PART 4: CALCULUS OF INDUCTIVE CONSTRUCTIONS

## 4.1 Motivation for Inductive Types

### 4.1.1 Problems with Church Encodings

1. **No native induction**: Cannot prove P(zero) ∧ (∀n.P(n)→P(succ n)) → ∀n.P(n)
2. **No large elimination**: Cannot define functions Nat → Type
3. **Inefficient computation**: Numerals are huge lambda terms
4. **No discrimination**: Cannot prove zero ≠ succ n

### 4.1.2 Solution: Primitive Inductive Types

CIC adds inductive types as first-class citizens with:
- Introduction rules (constructors)
- Elimination rules (recursors/pattern matching)
- Computation rules (ι-reduction)

## 4.2 Inductive Type Definitions

### 4.2.1 General Schema

```
INDUCTIVE DEFINITION SCHEMA:
────────────────────────────
Inductive I (params) : arity :=
| C₁ : type₁
| C₂ : type₂
  ⋮
| Cₙ : typeₙ
```

### 4.2.2 Examples

```
(* Natural numbers *)
Inductive nat : Set :=
| O : nat
| S : nat → nat.

(* Lists *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A → list A → list A.

(* Equality *)
Inductive eq {A : Type} (x : A) : A → Prop :=
| eq_refl : eq x x.

(* Accessibility (for well-founded recursion) *)
Inductive Acc {A : Type} (R : A → A → Prop) (x : A) : Prop :=
| Acc_intro : (∀y, R y x → Acc R y) → Acc R x.
```

### 4.2.3 Positivity Constraint

Constructors must be **strictly positive** in the inductive type:

```
STRICT POSITIVITY:
──────────────────
I may appear in constructor types ONLY in:
1. The return type
2. Positive positions of function types

FORBIDDEN (non-strictly positive):
Inductive Bad :=
| bad : (Bad → Prop) → Bad.   (* Bad appears left of → *)

WHY: Non-positive occurrences enable paradoxes
```

## 4.3 Elimination and Computation

### 4.3.1 The Recursor

Each inductive type I generates a recursor `I_rect`:

```
nat_rect : ∀(P : nat → Type),
           P O →                      (* zero case *)
           (∀n, P n → P (S n)) →      (* successor case *)
           ∀n, P n                    (* conclusion *)
```

### 4.3.2 Pattern Matching

CIC supports dependent pattern matching:

```
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S m => m
  end.
```

### 4.3.3 ι-Reduction

Computation rules for inductive types:

```
ι-REDUCTION:
────────────
match (C args) with ... | C x₁...xₙ => body | ... end
  →ι  body[args/x₁...xₙ]

EXAMPLE:
pred (S 5) →ι 5
```

## 4.4 Universe Structure in CIC

### 4.4.1 Sorts and Universes

```
SORT HIERARCHY:
───────────────
Prop : Type₀ : Type₁ : Type₂ : ...

SPECIAL SORTS:
- Prop : impredicative, proof-irrelevant
- Set  : predicative (since Coq 8.0), computational
- Type : predicative hierarchy

ALIASES:
- Set = Type₀ (with special properties)
```

### 4.4.2 Impredicativity Rules

```
IMPREDICATIVE PROP:
───────────────────
Γ ⊢ A : Type    Γ, x:A ⊢ P : Prop
──────────────────────────────────
      Γ ⊢ (∀x:A, P) : Prop

The product lives in Prop even though A lives in Type!
This is impredicativity.

PREDICATIVE SET (pCIC):
───────────────────────
Γ ⊢ A : Set    Γ, x:A ⊢ B : Set
────────────────────────────────
     Γ ⊢ (∀x:A, B) : Set

Same level! This is predicativity.

PREDICATIVE TYPE:
─────────────────
Γ ⊢ A : Typeᵢ    Γ, x:A ⊢ B : Typeⱼ
────────────────────────────────────
    Γ ⊢ (∀x:A, B) : Type_{max(i,j)}

Level is maximum of arguments!
```

### 4.4.3 Cumulativity

CIC has cumulativity between universes:

```
CUMULATIVITY:
─────────────
Prop ≤ Set ≤ Type₀ ≤ Type₁ ≤ ...

If A : Typeᵢ and i ≤ j, then A : Typeⱼ
```

## 4.5 Elimination Restrictions

### 4.5.1 Large Elimination Problem

Large elimination: Eliminating from Prop into Type.

```
PROBLEM:
────────
Inductive ex (A : Type) (P : A → Prop) : Prop :=
| ex_intro : ∀x:A, P x → ex A P.

(* Cannot project the witness! *)
Definition witness {A} {P} (h : ex A P) : A := ???

This would violate proof irrelevance!
```

### 4.5.2 Singleton Elimination

Exception: Single-constructor inductives in Prop with Prop-only arguments:

```
(* Allowed: eq has one constructor with Prop arguments *)
Definition eq_rect :
  ∀(A:Type) (x:A) (P:A→Type), P x → ∀y, x = y → P y.

(* Allowed: True has one constructor with no arguments *)
Inductive True : Prop := I.
Definition True_rect : ∀(P:Type), P → True → P.

(* Forbidden: ex has witness *)
(* Cannot eliminate ex into Type! *)
```

## 4.6 Coinductive Types

CIC supports coinductive definitions for infinite structures:

```
CoInductive Stream (A : Type) : Type :=
| Cons : A → Stream A → Stream A.

(* Infinite stream of ones *)
CoFixpoint ones : Stream nat := Cons 1 ones.
```

Guardedness checking ensures productivity.

---

# PART 5: COMPARISON WITH MLTT

## 5.1 Key Differences

| Feature | MLTT | CoC/CIC |
|---------|------|---------|
| Prop sort | No separate | Yes (impredicative) |
| Set sort | No separate | Yes (predicative since 8.0) |
| Universes | Predicative hierarchy | Mixed: impred Prop + pred Type |
| Polymorphism | Universe polymorphism | Impredicative + universe poly |
| Induction | W-types or primitive | Primitive inductive types |
| Identity | Intensional (J) | Intensional (J) + pattern match |
| Proof irrelevance | No (optional axiom) | Built-in for Prop |
| Elimination | Uniform | Restricted for Prop |

## 5.2 Implications for TERAS

### 5.2.1 Advantages of CIC over pure MLTT

1. **Impredicative Prop**: Concise encoding of logical connectives
2. **Proof irrelevance**: Proofs erased at runtime
3. **Mature ecosystem**: Coq/Rocq has decades of development
4. **Large-scale verification**: CompCert, sel4, etc.

### 5.2.2 Disadvantages of CIC for TERAS

1. **Complexity**: Prop/Set/Type distinction adds complexity
2. **Elimination restrictions**: Complicates proof extraction
3. **Impredicativity**: Harder metatheory, potential axiom conflicts
4. **Not purely predicative**: Diverges from clean MLTT foundation

### 5.2.3 TERAS Recommendation

**Use MLTT as foundation (per A-01 decision), but study CIC for**:
- Inductive type scheme design
- Proof irrelevance patterns
- Universe polymorphism implementation
- Practical verification techniques

---

# PART 6: LEAN'S TYPE THEORY

## 6.1 Lean 4 Foundation

Lean 4 implements a variant of CIC with modifications:

### 6.1.1 Key Features

```
LEAN 4 TYPE THEORY:
───────────────────
- Sorts: Prop, Type u (universe polymorphic)
- Prop: impredicative, proof-irrelevant
- Type: predicative hierarchy (NOT cumulative)
- Quotient types: built-in (not encoded)
- Propositional extensionality: axiom
- Function extensionality: derived from quotients
```

### 6.1.2 Differences from Coq

| Feature | Coq/Rocq | Lean 4 |
|---------|----------|--------|
| Cumulativity | Yes | No (use ulift) |
| Set sort | Yes | No (just Prop + Type) |
| Coinductive | Built-in | Not primitive |
| Quotients | Encoded | Built-in axiom |
| Tactics | Ltac2 | Lean metaprogramming |

### 6.1.3 Subsingleton Elimination

Lean allows large elimination only for subsingletons:

```
SUBSINGLETON:
─────────────
A type with at most one inhabitant.

Examples: Unit, Empty, Prop (by proof irrelevance)

For Prop, elimination into Type requires:
- At most one constructor
- All constructor arguments are Prop
```

## 6.2 Quotient Types in Lean

### 6.2.1 Primitive Quotients

```
QUOTIENT AXIOMS:
────────────────
quot : (α → α → Prop) → Type
quot.mk : α → quot r
quot.lift : (f : α → β) → (∀a b, r a b → f a = f b) → quot r → β
quot.sound : r a b → quot.mk a = quot.mk b
```

### 6.2.2 Function Extensionality

Lean derives funext from quotients:

```
funext : (∀x, f x = g x) → f = g

Derived via quotient of function graphs.
```

---

# PART 7: IMPLEMENTATIONS AND ECOSYSTEM

## 7.1 Coq/Rocq

### 7.1.1 History

- 1984: First Coq implementation (Huet)
- 1988: CIC formalized
- 1991: Coq V5
- 2004: Coq 8.0 (predicative Set)
- 2024: Renamed to Rocq

### 7.1.2 Notable Verifications

- **CompCert**: Verified C compiler
- **sel4**: Verified microkernel (with Isabelle/HOL)
- **Fiat-Crypto**: Verified cryptographic primitives
- **Mathematical Components**: Formalized mathematics
- **Iris**: Higher-order concurrent separation logic

### 7.1.3 Libraries

- **Coq Standard Library**: Basic types, logic, arithmetic
- **Mathematical Components**: SSReflect, algebra
- **stdpp**: Std++ (Iris foundation)
- **Equations**: Dependent pattern matching
- **MetaCoq**: Coq in Coq

## 7.2 Lean

### 7.2.1 History

- 2013: Lean 1 (de Moura, Microsoft Research)
- 2015: Lean 2
- 2017: Lean 3 (community edition)
- 2021: Lean 4 (complete rewrite)

### 7.2.2 Notable Projects

- **Mathlib**: Massive unified mathematics library
- **Lean 4 itself**: Bootstrapped in Lean
- **LeanSAT**: Verified SAT solver

## 7.3 Other CIC-based Systems

- **Agda**: Closer to MLTT but inspired by Coq
- **Matita**: Italian Coq variant
- **LEGO**: Edinburgh implementation

---

# PART 8: TERAS RELEVANCE ANALYSIS

## 8.1 What to Adopt from CIC

### 8.1.1 Inductive Type Scheme

CIC's inductive definitions are well-engineered:

```
ADOPT FOR TERAS:
────────────────
✓ Strict positivity checking
✓ Generated eliminators/recursors
✓ Pattern matching compilation
✓ Guardedness for corecursion
```

### 8.1.2 Universe Polymorphism

```
ADOPT FOR TERAS:
────────────────
✓ Universe-polymorphic definitions
✓ Explicit universe constraints
✓ max/imax operations
```

### 8.1.3 Proof Irrelevance Pattern

```
CONSIDER FOR TERAS:
───────────────────
? Proof irrelevance for security properties
? Erasure of proofs at runtime
? Restricted elimination for propositions
```

## 8.2 What to Avoid from CIC

### 8.2.1 Impredicativity

```
AVOID FOR TERAS:
────────────────
✗ Impredicative Prop
✗ Church encodings
✗ Complex elimination restrictions

REASON: Predicativity is simpler and sufficient
        Impredicativity complicates metatheory
        Conflicts with some axioms
```

### 8.2.2 Prop/Set/Type Distinction

```
AVOID FOR TERAS:
────────────────
✗ Three-sort hierarchy
✗ Complex elimination rules
✗ Special cases for singleton types

PREFER: Clean predicative hierarchy (MLTT style)
```

## 8.3 Synthesis for TERAS-LANG

```
TERAS-LANG RECOMMENDATION:
──────────────────────────
Foundation: Intensional MLTT (per A-01)

FROM CIC ADOPT:
├── Inductive type schema (positivity, eliminators)
├── Universe polymorphism (Lean-style)
├── Pattern matching compilation
└── Guardedness for recursion

FROM CIC AVOID:
├── Impredicativity
├── Multiple sorts (Prop/Set/Type)
└── Complex elimination restrictions

ADDITIONAL (from other sessions):
├── Linear types (memory safety)
├── Effect system (side effects)
├── Refinement types (invariants)
└── IFC labels (security)
```

---

# PART 9: METATHEORY

## 9.1 Strong Normalization

### 9.1.1 Statement

**Theorem**: Every well-typed CIC term has a unique normal form, reachable in finitely many steps.

### 9.1.2 Proof Techniques

1. **Reducibility candidates** (Girard): Types interpreted as sets of strongly normalizing terms
2. **Logical relations**: Type-indexed relations preserving normalization
3. **Realizability models**: Computational interpretation

## 9.2 Consistency

### 9.2.1 Relative Consistency

CIC is consistent relative to:
- ZFC + inaccessible cardinals
- Higher-order arithmetic

### 9.2.2 Canonicity

**Canonicity Property**: Every closed term of type nat reduces to a numeral (S^n O).

Note: Canonicity can fail with certain axioms (e.g., classical axioms).

## 9.3 Subject Reduction

**Theorem**: If Γ ⊢ t : A and t →β t', then Γ ⊢ t' : A.

Typing is preserved under reduction.

## 9.4 Decidability

**Theorem**: Type-checking in CIC is decidable.

Algorithm: Bidirectional type-checking with:
- β-reduction for conversion checking
- Universe constraint solving

---

# PART 10: CATEGORICAL SEMANTICS

## 10.1 Models of CIC

### 10.1.1 Set-theoretic Models

- Werner (1994): Set-theoretic model with traces
- Lee and Werner (2011): pCIC model
- Timany and Sozeau (2018): pCuIC model

### 10.1.2 Categorical Models

- Locally cartesian closed categories (LCCCs)
- Categories with Families (CwF)
- Comprehension categories

### 10.1.3 Proof-Irrelevance Models

For impredicative Prop with proof irrelevance:
- Prop interpreted as 2-element set {⊤, ⊥}
- All proofs of same proposition identified

---

# APPENDIX A: BIBLIOGRAPHY

## Primary Sources

1. Coquand, T. and Huet, G. (1988). "The Calculus of Constructions." Information and Computation 76(2-3):95-120.

2. Coquand, T. (1985). "Une Théorie des Constructions." PhD Thesis, University of Paris VII.

3. Paulin-Mohring, C. (1993). "Inductive definitions in the system Coq." TLCA 1993, LNCS 664.

4. Barendregt, H. (1991). "Lambda Calculi with Types." Handbook of Logic in Computer Science, Vol. 2.

5. Girard, J.-Y. (1972). "Interprétation fonctionnelle et élimination des coupures." PhD Thesis.

## Secondary Sources

6. Paulin-Mohring, C. (2015). "Introduction to the Calculus of Inductive Constructions." All about Proofs.

7. Bertot, Y. and Castéran, P. (2004). "Interactive Theorem Proving and Program Development." Springer.

8. de Moura, L. et al. (2021). "The Lean 4 Theorem Prover and Programming Language." CADE-28.

9. Werner, B. (1994). "Une Théorie des Constructions Inductives." PhD Thesis.

10. Luo, Z. (1994). "Computation and Reasoning: A Type Theory for Computer Science." Oxford.

---

# APPENDIX B: GLOSSARY

| Term | Definition |
|------|------------|
| CoC | Calculus of Constructions |
| CIC | Calculus of Inductive Constructions |
| pCIC | Predicative CIC (Set predicative) |
| PTS | Pure Type System |
| Impredicative | Quantification includes defined entity |
| Predicative | Quantification excludes defined entity |
| Subsingleton | Type with at most one inhabitant |
| Large elimination | Eliminating Prop into Type |
| Positivity | Constraint on recursive occurrences |
| Guardedness | Constraint ensuring productivity |

---

# DOCUMENT METADATA

```
Document: RESEARCH_A02_COC_CIC_SURVEY.md
Version: 1.0.0
Session: A-02
Domain: A (Type Theory)
Type: SURVEY
Status: COMPLETE
Lines: ~1,100
Created: 2026-01-03
Author: TERAS Research Track
Precedent: RESEARCH_A01_MLTT_DECISION.md
Successor: RESEARCH_A02_COC_CIC_COMPARISON.md
SHA-256: [To be computed on finalization]
```

---

**END OF SURVEY DOCUMENT**
