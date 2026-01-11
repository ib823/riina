# RESEARCH A-02: COC/CIC â€” COMPARATIVE ANALYSIS

## Version: 1.0.0
## Date: 2026-01-03
## Session: A-02
## Domain: A (Type Theory)
## Document Type: COMPARISON
## Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE

---

```
â•”â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•—
â•‘                                                                              â•‘
â•‘              SESSION A-02: COC/CIC COMPARATIVE ANALYSIS                      â•‘
â•‘                                                                              â•‘
â•‘  SYSTEMATIC COMPARISON: MLTT vs CoC vs CIC vs LEAN vs TERAS NEEDS           â•‘
â•‘                                                                              â•‘
â•šâ•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•
```

---

# EXECUTIVE SUMMARY

This comparison analyzes the Calculus of Constructions (CoC), Calculus of Inductive Constructions (CIC), and their variants against MLTT and TERAS requirements. The analysis reveals that while CIC provides practical benefits (inductive types, proof irrelevance), its impredicativity and complex sort structure conflict with TERAS's preference for clean, predicative foundations.

**Verdict**: MLTT remains the foundation; adopt CIC's inductive type machinery but avoid impredicativity.

---

# PART 1: FOUNDATION COMPARISON

## 1.1 MLTT vs CoC Matrix

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                        MLTT vs CoC COMPARISON MATRIX                              â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Feature                â”‚ MLTT (Intensional)        â”‚ CoC (Pure)                   â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Dependent Î -types      â”‚ YES                       â”‚ YES                          â”‚
â”‚ Dependent Î£-types      â”‚ YES                       â”‚ Encoded (impredicatively)    â”‚
â”‚ Identity types         â”‚ YES (primitive)           â”‚ Encoded (impredicatively)    â”‚
â”‚ Universes              â”‚ Predicative hierarchy     â”‚ Two sorts (* and â–¡)          â”‚
â”‚ Polymorphism           â”‚ Universe polymorphism     â”‚ Impredicative                â”‚
â”‚ Inductive types        â”‚ W-types or primitive      â”‚ Encoded only                 â”‚
â”‚ Induction              â”‚ YES                       â”‚ NO (Church encodings)        â”‚
â”‚ Proof irrelevance      â”‚ No (optional axiom)       â”‚ No                           â”‚
â”‚ Decidability           â”‚ YES                       â”‚ YES                          â”‚
â”‚ Type:Type              â”‚ NO (predicative)          â”‚ NO (Prop : Type)             â”‚
â”‚ Normalization          â”‚ Strong                    â”‚ Strong                       â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ TERAS VERDICT: MLTT is simpler and more principled                               â”‚
â”‚                CoC adds impredicativity without clear benefit for security       â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 1.2 CIC Variants Comparison

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                        CIC VARIANTS COMPARISON MATRIX                             â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Feature             â”‚ CIC (orig)  â”‚ pCIC        â”‚ pCuIC       â”‚ TERAS Need       â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Prop sort           â”‚ Impredicativeâ”‚ Impredicativeâ”‚ Impredicativeâ”‚ Consider        â”‚
â”‚ Set sort            â”‚ Impredicativeâ”‚ PREDICATIVE â”‚ Predicative â”‚ Prefer pred.     â”‚
â”‚ Type hierarchy      â”‚ Predicative â”‚ Predicative â”‚ Predicative â”‚ YES              â”‚
â”‚ Cumulativity        â”‚ Yes         â”‚ Yes         â”‚ Yes (+ ind) â”‚ Optional         â”‚
â”‚ Inductive types     â”‚ YES         â”‚ YES         â”‚ YES         â”‚ YES              â”‚
â”‚ Large elimination   â”‚ Restricted  â”‚ Restricted  â”‚ Restricted  â”‚ Avoid            â”‚
â”‚ Classical logic     â”‚ Breaks comp â”‚ Compatible  â”‚ Compatible  â”‚ Prefer constr.   â”‚
â”‚ Axiom of choice     â”‚ Inconsistentâ”‚ Compatible  â”‚ Compatible  â”‚ Avoid if poss.   â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ EVOLUTION: CIC â†’ pCIC (Coq 8.0) â†’ pCuIC (modern Coq/Rocq)                        â”‚
â”‚ TERAS VERDICT: If using CIC features, use pCIC predicative Set                   â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 1.3 PTS Instantiations

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    PURE TYPE SYSTEMS COMPARISON                                   â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ System      â”‚ PTS Specification (S, A, R)                                         â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Î»â†’ (STLC)  â”‚ ({*,â–¡}, {*:â–¡}, {(*,*,*)})                                           â”‚
â”‚             â”‚ Simply typed, no polymorphism, no dependencies                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Î»2 (Sys F)  â”‚ ({*,â–¡}, {*:â–¡}, {(*,*,*), (â–¡,*,*)})                                 â”‚
â”‚             â”‚ Polymorphism via (â–¡,*,*) â€” types abstracted over                    â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Î»P          â”‚ ({*,â–¡}, {*:â–¡}, {(*,*,*), (*,â–¡,â–¡)})                                 â”‚
â”‚             â”‚ Dependent types via (*,â–¡,â–¡) â€” types depend on terms                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Î»C (CoC)    â”‚ ({*,â–¡}, {*:â–¡}, {(*,*,*), (â–¡,*,*), (*,â–¡,â–¡), (â–¡,â–¡,â–¡)})              â”‚
â”‚             â”‚ All four rules: polymorphism + dependency + type operators          â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ MLTT-style  â”‚ ({Uâ‚€,Uâ‚,...,â–¡}, {Uáµ¢:Uáµ¢â‚Šâ‚}, {(Uáµ¢,Uâ±¼,U_{max(i,j)})})               â”‚
â”‚             â”‚ Predicative universe hierarchy                                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ ANALYSIS: CoC is "smaller" in sorts but "larger" in rules (impredicative)        â”‚
â”‚           MLTT is "larger" in sorts but "smaller" in rules (predicative)         â”‚
â”‚ TERAS: Prefer MLTT's predicative approach with bounded universe hierarchy        â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

---

# PART 2: IMPREDICATIVITY ANALYSIS

## 2.1 What Impredicativity Provides

```
BENEFITS OF IMPREDICATIVITY:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
1. Concise logical encodings
   âˆ€P:Prop. P â†’ P : Prop  (fits in Prop!)

2. Church encodings of data
   Nat := âˆ€X:Prop. X â†’ (Xâ†’X) â†’ X

3. Second-order quantification in logic
   âˆ€P. P âˆ¨ Â¬P  (LEM as single proposition)

4. Polymorphism without universe complications
   id : âˆ€A. A â†’ A  (single definition)
```

## 2.2 What Impredicativity Costs

```
COSTS OF IMPREDICATIVITY:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    IMPREDICATIVITY DECISION FOR TERAS                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                                  â”‚
â”‚  DECISION: REJECT IMPREDICATIVITY FOR TERAS-LANG                                â”‚
â”‚                                                                                  â”‚
â”‚  RATIONALE:                                                                      â”‚
â”‚  1. Predicative universes are simpler and sufficient                            â”‚
â”‚  2. No axiom compatibility concerns                                             â”‚
â”‚  3. Cleaner metatheory (easier soundness proofs)                                â”‚
â”‚  4. No elimination restrictions needed                                          â”‚
â”‚  5. Universe polymorphism provides sufficient expressiveness                    â”‚
â”‚  6. Aligns with MLTT foundation (Session A-01)                                  â”‚
â”‚                                                                                  â”‚
â”‚  EXCEPTION: None. Impredicativity is not required for security verification.    â”‚
â”‚                                                                                  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

---

# PART 3: INDUCTIVE TYPES COMPARISON

## 3.1 Approaches to Inductive Types

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    INDUCTIVE TYPE APPROACHES                                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Approach            â”‚ Description                                                â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Church Encodings    â”‚ Impredicative encoding in pure CoC                         â”‚
â”‚ (CoC)               â”‚ + Concise, no extension needed                             â”‚
â”‚                     â”‚ - No induction, no large elimination                       â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ W-types             â”‚ Single "well-founded tree" type in MLTT                    â”‚
â”‚ (MLTT)              â”‚ + Minimal, all inductives encodable                        â”‚
â”‚                     â”‚ - Verbose, poor computational behavior                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Primitive Inductive â”‚ First-class inductive definitions (CIC)                    â”‚
â”‚ (CIC)               â”‚ + Native induction, good computation                       â”‚
â”‚                     â”‚ + Flexible (indexed families, mutual, nested)              â”‚
â”‚                     â”‚ - Requires positivity checking                             â”‚
â”‚                     â”‚ - Extension to core theory                                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Inductive Families  â”‚ Indexed inductive types (Agda, Idris)                      â”‚
â”‚                     â”‚ + Dependent pattern matching                               â”‚
â”‚                     â”‚ + Expressive (vectors, red-black trees)                    â”‚
â”‚                     â”‚ - Complex coverage checking                                â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ TERAS VERDICT: Adopt CIC-style primitive inductive types with inductive families â”‚
â”‚                This provides practical benefits without impredicativity          â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 3.2 Inductive Type Features

```
FEATURE COMPARISON:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                            â”‚ CIC  â”‚ Agda â”‚ Lean â”‚ TERAS
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€
Simple inductive           â”‚ YES  â”‚ YES  â”‚ YES  â”‚ YES
Parameterized              â”‚ YES  â”‚ YES  â”‚ YES  â”‚ YES
Indexed (families)         â”‚ YES  â”‚ YES  â”‚ YES  â”‚ YES
Mutual inductive           â”‚ YES  â”‚ YES  â”‚ YES  â”‚ YES
Nested inductive           â”‚ YES  â”‚ YES  â”‚ YES  â”‚ YES
Inductive-inductive        â”‚ NO   â”‚ YES  â”‚ NO   â”‚ STUDY
Inductive-recursive        â”‚ NO   â”‚ YES  â”‚ NO   â”‚ STUDY
Higher inductive (HIT)     â”‚ NO*  â”‚ Cub. â”‚ NO   â”‚ NO
Coinductive                â”‚ YES  â”‚ YES  â”‚ NO** â”‚ STUDY
Quotient inductive (QIIT)  â”‚ NO   â”‚ Cub. â”‚ Quot â”‚ STUDY

* With axioms
** Lean uses explicit corecursion, not primitive coinduction
```

---

# PART 4: PROOF ASSISTANT COMPARISON

## 4.1 Coq/Rocq vs Lean vs Agda

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    PROOF ASSISTANT COMPARISON                                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Feature             â”‚ Coq/Rocq        â”‚ Lean 4          â”‚ Agda                    â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Foundation          â”‚ pCIC            â”‚ CIC variant     â”‚ MLTT-like               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Prop sort           â”‚ YES (impredicative)â”‚ YES (impred) â”‚ NO (optional)           â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Set sort            â”‚ YES (predicative) â”‚ NO            â”‚ NO                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Cumulativity        â”‚ YES             â”‚ NO (use ulift)  â”‚ YES                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Quotients           â”‚ Setoid encoding â”‚ Built-in axiom  â”‚ Cubical (native)        â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Prop extensionality â”‚ Axiom           â”‚ Axiom           â”‚ Axiom or Cubical        â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Func extensionality â”‚ Axiom           â”‚ From quotients  â”‚ Axiom or Cubical        â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Proof irrelevance   â”‚ Built-in (Prop) â”‚ Built-in (Prop) â”‚ Optional (--prop)       â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Tactics             â”‚ Ltac2, SSReflectâ”‚ Lean DSL        â”‚ Reflection              â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Code extraction     â”‚ OCaml, Haskell  â”‚ Native compile  â”‚ Haskell, JS             â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Performance         â”‚ Medium          â”‚ HIGH            â”‚ Medium                  â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ Math library        â”‚ MathComp        â”‚ Mathlib (huge)  â”‚ agda-stdlib             â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ TERAS RELEVANCE:                                                                  â”‚
â”‚ - Coq: Reference for inductive types, tactics                                    â”‚
â”‚ - Lean: Reference for performance, metaprogramming                               â”‚
â”‚ - Agda: Reference for clean MLTT implementation                                  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 4.2 Axiom Comparison

```
COMMON AXIOMS:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                        â”‚ Coq  â”‚ Lean â”‚ Agda â”‚ TERAS
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€
Propositional Ext       â”‚ Axiomâ”‚ Axiomâ”‚ Axiomâ”‚ AVOID*
Function Ext            â”‚ Axiomâ”‚ Derivâ”‚ Axiomâ”‚ STUDY
Excluded Middle         â”‚ Axiomâ”‚ Axiomâ”‚ Axiomâ”‚ AVOID
Axiom of Choice         â”‚ Axiomâ”‚ Axiomâ”‚ Axiomâ”‚ AVOID
Quotients               â”‚ Axiomâ”‚ Axiomâ”‚ Cubicâ”‚ STUDY
Univalence              â”‚ Axiomâ”‚ NO   â”‚ Cubicâ”‚ NO

* TERAS prefers constructive foundations without axioms
```

---

# PART 5: ELIMINATION RULES COMPARISON

## 5.1 Elimination Restrictions

```
ELIMINATION INTO TYPE FROM PROP:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

COROCQ (pCIC):
â”œâ”€â”€ Prop â†’ Prop: Always allowed
â”œâ”€â”€ Prop â†’ Type: RESTRICTED (singleton/empty only)
â”œâ”€â”€ Set â†’ any: Always allowed
â””â”€â”€ Type â†’ any: Always allowed

LEAN 4:
â”œâ”€â”€ Prop â†’ Prop: Always allowed
â”œâ”€â”€ Prop â†’ Type: RESTRICTED (subsingleton only)
â””â”€â”€ Type â†’ any: Always allowed

AGDA (without --prop):
â”œâ”€â”€ No Prop sort
â””â”€â”€ All elimination allowed

TERAS CONSIDERATION:
â”œâ”€â”€ Option A: No separate Prop (like Agda)
â”œâ”€â”€ Option B: Prop with restrictions (like Lean)
â””â”€â”€ Option C: Proof irrelevance via erasure (like QTT)
```

## 5.2 Subsingleton Elimination

```
SUBSINGLETON DEFINITION:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
A type T is a subsingleton if âˆ€(x y : T), x = y

SYNTACTIC APPROXIMATION (Lean):
â”œâ”€â”€ At most one constructor
â””â”€â”€ All constructor arguments are Prop

EXAMPLES:
â”œâ”€â”€ Unit : Subsingleton âœ“
â”œâ”€â”€ Empty : Subsingleton âœ“
â”œâ”€â”€ True : Subsingleton âœ“
â”œâ”€â”€ a = b : Subsingleton âœ“
â”œâ”€â”€ Acc R x : Subsingleton âœ“
â””â”€â”€ âˆƒx, P x : NOT subsingleton âœ—

TERAS: If using Prop, follow Lean's subsingleton approach
```

---

# PART 6: PERFORMANCE COMPARISON

## 6.1 Runtime Performance

```
EXTRACTION/COMPILATION:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                        â”‚ Method              â”‚ Performance â”‚ TERAS Relevance
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Coq â†’ OCaml             â”‚ Code extraction     â”‚ Medium      â”‚ Reference
Coq â†’ Haskell           â”‚ Code extraction     â”‚ Lower       â”‚ Not target
Lean 4 native           â”‚ Direct compilation  â”‚ HIGH        â”‚ Model
Idris 2 â†’ C/Scheme      â”‚ Quantitative erasureâ”‚ HIGH        â”‚ Model
Agda â†’ Haskell          â”‚ Code extraction     â”‚ Medium      â”‚ Reference

TERAS TARGET: Native compilation with >C performance (per Immutable Laws)
BEST REFERENCE: Lean 4 and Idris 2 approaches
```

## 6.2 Type Checking Performance

```
TYPE CHECKING FACTORS:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
1. Normalization strategy (lazy vs eager)
2. Conversion checking algorithm
3. Universe constraint solving
4. Tactic elaboration overhead

OBSERVED RANKINGS:
â”œâ”€â”€ Lean 4: Fastest (optimized implementation)
â”œâ”€â”€ Agda: Medium (intensive dependent matching)
â”œâ”€â”€ Coq: Medium (Ltac overhead)
â””â”€â”€ Idris 2: Medium (QTT overhead)

TERAS: Target Lean 4 performance level
```

---

# PART 7: SECURITY FEATURE ANALYSIS

## 7.1 Security-Relevant Features

```
SECURITY FEATURE MATRIX:
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
                        â”‚ CIC  â”‚ Lean â”‚ Agda â”‚ TERAS Need
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Dependent types         â”‚ YES  â”‚ YES  â”‚ YES  â”‚ MANDATORY
Linear types            â”‚ NO   â”‚ NO   â”‚ NO*  â”‚ MANDATORY
Effect tracking         â”‚ NO   â”‚ NO   â”‚ NO   â”‚ MANDATORY
Refinement types        â”‚ NO   â”‚ NO   â”‚ NO   â”‚ MANDATORY
Session types           â”‚ NO   â”‚ NO   â”‚ NO   â”‚ HIGH
Capability types        â”‚ NO   â”‚ NO   â”‚ NO   â”‚ HIGH
IFC labels              â”‚ NO   â”‚ NO   â”‚ NO   â”‚ CRITICAL
Constant-time types     â”‚ NO   â”‚ NO   â”‚ NO   â”‚ CRITICAL

* Agda has experimental --erasure feature
```

## 7.2 Gap Analysis

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    CIC/COC SECURITY GAP ANALYSIS                                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                                  â”‚
â”‚ CIC/CoC provides ~30% of TERAS security typing requirements:                     â”‚
â”‚                                                                                  â”‚
â”‚ PROVIDED:                                                                        â”‚
â”‚ âœ“ Dependent types for invariants                                                â”‚
â”‚ âœ“ Inductive types for data structure proofs                                     â”‚
â”‚ âœ“ Strong normalization (termination)                                            â”‚
â”‚ âœ“ Decidable type checking                                                       â”‚
â”‚                                                                                  â”‚
â”‚ MISSING:                                                                         â”‚
â”‚ âœ— Linear/affine types (memory safety)                                           â”‚
â”‚ âœ— Effect system (side effect control)                                           â”‚
â”‚ âœ— Refinement types (SMT-backed constraints)                                     â”‚
â”‚ âœ— Information flow control (confidentiality)                                    â”‚
â”‚ âœ— Session types (protocol verification)                                         â”‚
â”‚ âœ— Capability types (access control)                                             â”‚
â”‚ âœ— Constant-time types (timing side channels)                                    â”‚
â”‚                                                                                  â”‚
â”‚ CONCLUSION: CIC is insufficient alone; must be extended significantly           â”‚
â”‚                                                                                  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

---

# PART 8: TERAS SYNTHESIS

## 8.1 Feature Adoption Matrix

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    TERAS FEATURE ADOPTION FROM CIC                               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                                  â”‚
â”‚ ADOPT:                                                                          â”‚
â”‚ â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚
â”‚ â”‚ âœ“ Primitive inductive type machinery                                       â”‚  â”‚
â”‚ â”‚   - Positivity checking algorithm                                          â”‚  â”‚
â”‚ â”‚   - Recursor/eliminator generation                                         â”‚  â”‚
â”‚ â”‚   - Pattern matching compilation                                           â”‚  â”‚
â”‚ â”‚   - Inductive families (indexed types)                                     â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ âœ“ Universe polymorphism (Lean style)                                       â”‚  â”‚
â”‚ â”‚   - Level variables                                                        â”‚  â”‚
â”‚ â”‚   - max/imax operations                                                    â”‚  â”‚
â”‚ â”‚   - Universe constraints                                                   â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ âœ“ Guardedness checking (for recursive definitions)                         â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ âœ“ Decidable type checking architecture                                     â”‚  â”‚
â”‚ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚
â”‚                                                                                  â”‚
â”‚ REJECT:                                                                          â”‚
â”‚ â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚
â”‚ â”‚ âœ— Impredicative Prop                                                       â”‚  â”‚
â”‚ â”‚   Reason: Complicates metatheory, axiom conflicts                          â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ âœ— Three-sort hierarchy (Prop/Set/Type)                                     â”‚  â”‚
â”‚ â”‚   Reason: Unnecessary complexity                                           â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ âœ— Complex elimination restrictions                                         â”‚  â”‚
â”‚ â”‚   Reason: Follows from impredicativity we're rejecting                     â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ âœ— Church encodings                                                         â”‚  â”‚
â”‚ â”‚   Reason: No benefits with primitive inductives                            â”‚  â”‚
â”‚ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚
â”‚                                                                                  â”‚
â”‚ STUDY FURTHER:                                                                   â”‚
â”‚ â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”  â”‚
â”‚ â”‚ ? Coinductive types                                                        â”‚  â”‚
â”‚ â”‚   For infinite protocols, streams                                          â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ ? Quotient types                                                           â”‚  â”‚
â”‚ â”‚   For abstract data types with equivalence                                 â”‚  â”‚
â”‚ â”‚                                                                            â”‚  â”‚
â”‚ â”‚ ? Proof irrelevance (via erasure, not Prop)                                â”‚  â”‚
â”‚ â”‚   For runtime performance                                                  â”‚  â”‚
â”‚ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜  â”‚
â”‚                                                                                  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
1. Impredicativity? â†’ NO
2. Separate Prop sort? â†’ STUDY FURTHER (consider erasure approach)
3. Inductive type scheme? â†’ YES, adopt CIC style
4. Universe approach? â†’ Predicative with universe polymorphism
5. Which implementation to study? â†’ Lean 4 for performance, Agda for MLTT fidelity

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
