# TERAS RESEARCH DOCUMENT A-03: COMPARATIVE ANALYSIS
## Homotopy Type Theory and Cubical Type Theory

### Document Metadata

| Field | Value |
|-------|-------|
| Document ID | RESEARCH_A03_HOTT_CUBICAL_COMPARISON |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | A-03 |
| Type | Comparative Analysis |

---

## 1. System Comparison Matrix

### 1.1 Core Type Theories Compared

| Feature | MLTT | CoC/CIC | Book HoTT | CCHM Cubical | Cartesian Cubical |
|---------|------|---------|-----------|--------------|-------------------|
| **Base** | Predicative | Impredicative | MLTT | MLTT | MLTT |
| **Identity Types** | J-eliminator | J-eliminator | Paths | Path types | Path types |
| **UIP** | Can assume | Can assume | Refuted | Refuted | Refuted |
| **Univalence** | â€” | â€” | Axiom | Provable | Provable |
| **Canonicity** | Yes | Yes | No | Yes | Yes |
| **HITs** | â€” | Inductives | Postulated | Definable | Definable |
| **Interval** | â€” | â€” | â€” | De Morgan | Cartesian |
| **Computation** | Full | Full | Limited | Full | Full |

### 1.2 Implementation Comparison

| System | Language | HITs | Univalence | Automation | Maturity |
|--------|----------|------|------------|------------|----------|
| Agda (cubical) | Haskell | Native | Provable | Limited | High |
| Arend | Kotlin | Native | Provable | Good | Medium |
| Coq HoTT | OCaml | Hack | Axiom | Ltac | High |
| cubicaltt | Haskell | Native | Provable | None | Low |
| Lean 4 | Lean | Quotients | No | Excellent | High |
| RedPRL/redtt | SML | Native | Provable | Limited | Low |

### 1.3 Interval Structures Compared

| Feature | CCHM | Cartesian | BCH |
|---------|------|-----------|-----|
| Endpoints | 0, 1 | 0, 1 | 0, 1 |
| Reversal | 1-i | â€” | â€” |
| Connections | âˆ§, âˆ¨ | â€” | â€” |
| Diagonals | Yes | Yes | No |
| Composition | comp | hcom + coe | â€” |
| Glue | Full | Full | Partial |

---

## 2. HoTT vs Classical Foundations

### 2.1 Structural Comparison

| Aspect | ZFC Set Theory | Classical Type Theory | HoTT |
|--------|----------------|----------------------|------|
| Basic entities | Sets | Types | Homotopy types |
| Equality | Global relation | Identity type | Path space |
| Isomorphism | Bijection | Type isomorphism | Equivalence = Equality |
| Quotients | Set quotient | Axiom/encoding | HITs |
| Proof objects | No | Yes | Yes (higher) |
| Constructive | No (typically) | Can be | Yes (typically) |
| Computation | No | Yes | Yes (cubical) |

### 2.2 Handling of Equality

| Scenario | Set Theory | CIC | HoTT |
|----------|------------|-----|------|
| x = x | Reflexivity axiom | refl | refl (path) |
| Symmetry | Axiom | sym proof | path inverse |
| Transitivity | Axiom | trans proof | path composition |
| Substitution | Axiom | transport | transport |
| Functional ext. | Axiom | Axiom | Follows from UA |
| Propositional ext. | Axiom | Axiom | Follows from UA |
| Structure identity | Fails | Fails | Automatic |

### 2.3 Proof Relevance

| Type | Set Theory | MLTT | HoTT |
|------|------------|------|------|
| Propositions | Proof-irrelevant | Proof-relevant | Can be either |
| Sets | N/A | N/A | 0-truncated |
| Higher types | N/A | May be trivial | Rich structure |
| Path between paths | N/A | May be unique | May be non-trivial |

---

## 3. Cubical Type Theory Variants

### 3.1 CCHM vs Cartesian

| Aspect | CCHM | Cartesian |
|--------|------|-----------|
| Cube category | De Morgan algebra | Cartesian product |
| Reversal | Built-in (1-i) | Derived/added |
| Connections | Built-in (âˆ§,âˆ¨) | Not present |
| Kan operation | comp | hcom + coe |
| Glue reduction | Direct | Via coercion |
| HITs | Well-supported | Well-supported |
| Canonicity | Proven (2018) | Proven |
| Complexity | Higher | Lower |
| Meta-theory | More developed | More recent |

### 3.2 Composition Operations

**CCHM Composition**:
```
comp^i A [Ï† â†¦ u] aâ‚€
-- Inputs: Line A, partial tube u, base aâ‚€
-- Output: Element of A(1) extending tube
```

**Cartesian (separate operations)**:
```
coe^i A a          -- coercion along line
hcom A [Ï† â†¦ u] aâ‚€  -- homogeneous composition
```

### 3.3 Glue Types

**CCHM Glue**:
```
Glue A [Ï† â†¦ (T, e)]
-- T : Type [Ï†]
-- e : T â‰ƒ A [Ï†]
-- Result: Type equal to T on Ï†, "connected" to A
```

**Cartesian V-types**:
```
V i A T e
-- Similar but using coercion-based structure
```

---

## 4. Higher Inductive Types Approaches

### 4.1 Implementation Strategies

| Approach | Description | Systems |
|----------|-------------|---------|
| Axioms/Postulates | Add HITs as axioms | Coq HoTT |
| Private inductives | Hack using private constructors | Coq HoTT |
| Interval-based | Define using interval type | Cubical systems |
| Special syntax | Built-in HIT syntax | Arend, Agda cubical |
| Schemas | General HIT signatures | Research systems |

### 4.2 Specific HIT Definitions Compared

**Circle SÂ¹**:

*Book HoTT (axiomatic)*:
```
postulate SÂ¹ : Type
postulate base : SÂ¹
postulate loop : base = base
postulate SÂ¹-elim : ...
```

*Cubical Agda*:
```agda
data SÂ¹ : Type where
  base : SÂ¹
  loop : base â‰¡ base
```

*Arend*:
```arend
\data S1 | base | loop : base = base
```

### 4.3 Quotient Type Implementations

| System | Method | Computation |
|--------|--------|-------------|
| Lean 4 | Primitive quotient | Reduces |
| Coq | Axiom + private | Doesn't reduce |
| Cubical | HIT | Reduces |
| Arend | HIT syntax | Reduces |

---

## 5. Expressiveness Comparison

### 5.1 What Can Be Expressed

| Concept | MLTT | CIC | Book HoTT | Cubical |
|---------|------|-----|-----------|---------|
| Dependent products | âœ“ | âœ“ | âœ“ | âœ“ |
| Dependent sums | âœ“ | âœ“ | âœ“ | âœ“ |
| Identity types | âœ“ | âœ“ | âœ“ | âœ“ (paths) |
| Inductive types | âœ“ | âœ“ | âœ“ | âœ“ |
| HITs | â€” | â€” | âœ“ (axiom) | âœ“ |
| Univalence | â€” | â€” | âœ“ (axiom) | âœ“ |
| Function ext. | Axiom | Axiom | âœ“ | âœ“ |
| Quotients | â€” | â€” | âœ“ | âœ“ |
| n-types | â€” | â€” | âœ“ | âœ“ |

### 5.2 Proof Methods Available

| Method | Classical | CIC | HoTT |
|--------|-----------|-----|------|
| Induction | âœ“ | âœ“ | âœ“ |
| Path induction | â€” | âœ“ | âœ“ |
| Transport | â€” | âœ“ | âœ“ (fundamental) |
| Univalent transport | â€” | â€” | âœ“ |
| Higher path induction | â€” | â€” | âœ“ |
| Encode-decode | â€” | â€” | âœ“ |

---

## 6. Computational Properties

### 6.1 Reduction Rules

| Operation | MLTT | CIC | HoTT (axiom) | Cubical |
|-----------|------|-----|--------------|---------|
| Î²-reduction | âœ“ | âœ“ | âœ“ | âœ“ |
| Î·-reduction | Optional | âœ“ | âœ“ | âœ“ |
| Î¹-reduction | âœ“ | âœ“ | âœ“ | âœ“ |
| Path reduction | â€” | â€” | â€” | âœ“ |
| Comp reduction | â€” | â€” | â€” | âœ“ |
| Glue reduction | â€” | â€” | â€” | âœ“ |

### 6.2 Canonicity

| System | Canonicity | Method |
|--------|------------|--------|
| MLTT | Yes | Normalization |
| CIC | Yes | Strong normalization |
| HoTT + UA (axiom) | No | UA blocks |
| CCHM | Yes | Computability argument |
| Cartesian | Yes | Normalization proof |

### 6.3 Decidability

| Property | MLTT | CIC | Book HoTT | Cubical |
|----------|------|-----|-----------|---------|
| Type checking | Decidable | Decidable | Decidable | Decidable |
| Type inference | Partial | Partial | Partial | Partial |
| Definitional equality | Decidable | Decidable | Semi-decidable | Decidable |
| Propositional equality | Undecidable | Undecidable | Undecidable | Undecidable |

---

## 7. Performance Characteristics

### 7.1 Type Checking Complexity

| System | Complexity | Main Bottleneck |
|--------|------------|-----------------|
| MLTT | Moderate | Unification |
| CIC | Moderate | Universe constraints |
| HoTT (axiom) | Low overhead | Axioms are free |
| Cubical | High | Composition operations |

### 7.2 Proof Size

| Theorem | CIC | HoTT (axiom) | Cubical |
|---------|-----|--------------|---------|
| Function extensionality | Axiom | Follows | Direct |
| Ï€â‚(SÂ¹) = â„¤ | Cannot state | Medium | Medium |
| Univalence | â€” | Axiom | Proof term |
| Basic HITs | Encoding | Axiom | Definition |

### 7.3 Runtime Overhead

| Feature | Extracted Code Impact |
|---------|----------------------|
| Paths | Erased (typically) |
| Transport | May remain |
| Composition | May be expensive |
| HITs | Point constructors remain |
| Truncation | Erased |

---

## 8. Use Case Analysis

### 8.1 Mathematics Formalization

| Task | Best System | Reason |
|------|-------------|--------|
| Classical algebra | CIC (Coq/Lean) | Mature, automation |
| Synthetic homotopy | Cubical Agda | Native HITs |
| Category theory | HoTT | Univalence natural |
| Set-level math | Any | All adequate |

### 8.2 Programming Languages

| Use Case | Best Approach | Reason |
|----------|---------------|--------|
| Verified compilers | CIC | Mature extraction |
| Proof-carrying code | MLTT | Simple, efficient |
| Extensional reasoning | HoTT | Univalence helps |
| Quotient types | Cubical/Lean | Native support |

### 8.3 Security Applications

| Security Need | Relevant Features | Best Choice |
|---------------|-------------------|-------------|
| Access control | Basic types | MLTT/CIC |
| Policy equivalence | Quotients | Cubical/HoTT |
| Information flow | Refinement types | Neither (need extension) |
| Proof irrelevance | Truncation | HoTT |
| Representation independence | Univalence | HoTT |

---

## 9. Migration and Compatibility

### 9.1 Theory Embeddings

```
MLTT âŠ‚ CIC âŠ‚ pCIC

MLTT â†’ HoTT (not full embedding)
MLTT âŠ‚ Cubical (conservative)
HoTT â†’ Cubical (interpretation)
```

### 9.2 Code Portability

| From | To | Difficulty |
|------|-----|------------|
| Coq standard | Coq HoTT | Moderate (UIP issues) |
| Agda standard | Cubical Agda | Low-Moderate |
| HoTT Coq | Cubical Agda | Moderate |
| Any | Arend | Moderate |

### 9.3 Interoperability

Most systems are not directly interoperable. Translation requires:
- Rechecking all proofs
- Adapting to different universes
- Handling different primitive operations

---

## 10. Recommendations Summary

### 10.1 For General Theorem Proving

**Recommendation**: Lean 4 or Coq
- Mature ecosystems
- Good automation
- Large libraries

### 10.2 For Homotopical Mathematics

**Recommendation**: Cubical Agda
- Native HITs
- Computational univalence
- Active development

### 10.3 For TERAS-LANG

**Recommendation**: Selective incorporation

| HoTT Feature | TERAS Inclusion | Rationale |
|--------------|-----------------|-----------|
| Set quotients | Yes (primitive) | Security policies |
| Prop truncation | Yes | Proof irrelevance |
| Full univalence | No | Unnecessary complexity |
| General HITs | Limited | Case-by-case basis |
| Cubical paths | No | Performance concerns |
| n-types | Awareness only | For decidability analysis |

---

## 11. Conclusion

### 11.1 Key Differentiators

1. **Univalence** distinguishes HoTT from classical type theories
2. **Cubical** distinguishes computational HoTT from axiomatic
3. **HITs** enable quotients and topological reasoning
4. **Truncation levels** classify type complexity

### 11.2 Trade-offs Summary

| Choosing For | Accept Trade-off |
|--------------|------------------|
| Computation | More complex type theory |
| Simplicity | Loss of univalence |
| Full HoTT | Performance overhead |
| Classical reasoning | May break canonicity |

### 11.3 TERAS Position

TERAS-LANG should position itself as:
- **Beyond MLTT**: Support quotients, proof irrelevance
- **Below full HoTT**: No full univalence or cubical operations
- **Security-focused**: Extensions for IFC, capabilities, effects
- **Practical**: Emphasize decidability and performance

---

*End of Comparative Analysis Document*
