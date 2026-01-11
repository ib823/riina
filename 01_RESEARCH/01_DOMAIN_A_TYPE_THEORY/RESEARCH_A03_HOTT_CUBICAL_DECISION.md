# TERAS RESEARCH DOCUMENT A-03: DECISION DOCUMENT
## Homotopy Type Theory and Cubical Type Theory Integration Decisions

### Document Metadata

| Field | Value |
|-------|-------|
| Document ID | RESEARCH_A03_HOTT_CUBICAL_DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | A-03 |
| Type | Architecture Decision |
| Status | APPROVED |

---

## 1. Executive Decision Summary

### Primary Decision

**TERAS-LANG will NOT implement full Homotopy Type Theory or Cubical Type Theory.**

Instead, TERAS-LANG will selectively incorporate specific HoTT concepts that directly benefit security verification:

| Feature | Decision | Priority |
|---------|----------|----------|
| Full Univalence | ❌ REJECT | — |
| Cubical Path Types | ❌ REJECT | — |
| Set Quotients | ✅ ADOPT | HIGH |
| Propositional Truncation | ✅ ADOPT | HIGH |
| General HITs | ⚠️ DEFER | LOW |
| n-Truncation Levels | ⚠️ CONSIDER | MEDIUM |

### Rationale Summary

1. **Complexity vs Benefit**: Full HoTT adds significant implementation complexity with limited security benefit
2. **Performance**: Cubical operations have computational overhead unsuitable for security-critical code
3. **Security Focus**: Most security properties are propositions (proof-irrelevant) or sets (0-truncated)
4. **Practical Quotients**: Set quotients provide direct value for security policy modeling
5. **Proof Irrelevance**: Propositional truncation enables clean extraction of security predicates

---

## 2. Detailed Feature Decisions

### 2.1 DECISION A03-001: Reject Full Univalence Axiom

**Decision**: TERAS-LANG will NOT include the full univalence axiom.

**Status**: REJECTED

**Rationale**:

1. **Unnecessary Power**: Univalence provides that equivalent types are equal. For security:
   - Security policies are typically propositional (have at most one proof)
   - Policy equivalence can be handled with simpler mechanisms
   - Structure identity principle rarely needed

2. **Implementation Burden**: Full univalence requires either:
   - Cubical type theory (complex, performance overhead)
   - Axiom (breaks canonicity)

3. **Alternative**: For cases where type equivalence matters:
   - Use explicit isomorphism witnesses
   - Provide targeted propositional/set extensionality

**Trade-off Accepted**: 
- Cannot automatically transport proofs across equivalent types
- Must manually handle representation changes
- Isomorphic types remain distinct

### 2.2 DECISION A03-002: Reject Cubical Path Types

**Decision**: TERAS-LANG will NOT use cubical path types as the primitive identity type.

**Status**: REJECTED

**Rationale**:

1. **Complexity**: Cubical interval, faces, composition operations add significant complexity to:
   - Type checker implementation
   - User mental model
   - Runtime behavior

2. **Performance**: Cubical operations:
   - comp, hcom, coe involve non-trivial computation
   - Glue type reductions can be expensive
   - Not suitable for performance-critical security code

3. **Overkill**: Most security reasoning:
   - Uses simple equality (definitional or propositional)
   - Doesn't need higher path structure
   - Benefits more from SMT integration than path computation

**Alternative Adopted**:
- Standard Martin-Löf identity types with J-eliminator
- Function extensionality as postulate (if needed)
- Explicit equality proofs where required

### 2.3 DECISION A03-003: Adopt Set Quotient Types

**Decision**: TERAS-LANG WILL include primitive set quotient types.

**Status**: ADOPTED

**Priority**: HIGH

**Specification**:

```
-- Set Quotient Type Formation
quotient : (A : Type) → (R : A → A → Prop) → Type

-- Constructors
[_] : A → A / R

-- Equality constructor
eq/ : (a b : A) → R a b → [a] =_{A/R} [b]

-- Elimination (into sets only)
quotient_elim : 
  (P : A / R → Type)
  → (∀ q. isSet (P q))
  → (f : (a : A) → P [a])
  → (∀ a b (r : R a b). transport P (eq/ a b r) (f a) = f b)
  → (q : A / R) → P q
```

**Rationale**:

1. **Security Policy Modeling**:
   ```
   -- Security labels modulo equivalence
   SecurityLabel = LabelRep / label_equiv
   
   -- Access control policies
   Policy = PolicyRep / policy_equiv
   
   -- Cryptographic key equivalence
   Key = KeyRep / key_rotation_equiv
   ```

2. **Declassification Policies**:
   ```
   -- Equivalent declassification paths should be equal
   DeclassPath = RawPath / path_equiv
   ```

3. **Computational**: Set quotients compute properly (reduce to [_] cases)

**Implementation Approach**:
- Primitive type former (not HIT encoding)
- Built-in computation rules
- Integration with equality checker

### 2.4 DECISION A03-004: Adopt Propositional Truncation

**Decision**: TERAS-LANG WILL include propositional truncation.

**Status**: ADOPTED

**Priority**: HIGH

**Specification**:

```
-- Propositional Truncation Type
∥_∥ : Type → Type

-- Constructor
|_| : A → ∥A∥

-- Truncation property
trunc : (x y : ∥A∥) → x = y

-- Elimination (into propositions only)
∥∥-elim : 
  (P : ∥A∥ → Type)
  → (∀ t. isProp (P t))
  → ((a : A) → P |a|)
  → (t : ∥A∥) → P t
```

**Rationale**:

1. **Proof Irrelevance**: Security claims often need only existence, not witness:
   ```
   -- "User has valid credential" without revealing which one
   hasCredential : User → ∥Credential × valid(User, Credential)∥
   
   -- "Some declassification path exists" 
   canDeclassify : Secret → Public → ∥DeclassProof∥
   ```

2. **Efficient Extraction**: Truncated values can be erased:
   ```
   -- Runtime code doesn't carry proof objects
   extracted_hasCredential : User → Bool
   ```

3. **Non-Constructive Properties**: Enables classical-ish reasoning:
   ```
   -- "Either authorized or not" without decidability
   authorization : User → Resource → ∥Authorized ∨ ¬Authorized∥
   ```

### 2.5 DECISION A03-005: Defer General Higher Inductive Types

**Decision**: TERAS-LANG will NOT initially support arbitrary HITs, but may add specific ones.

**Status**: DEFERRED

**Priority**: LOW

**Rationale**:

1. **Set Quotients Sufficient**: Most practical needs covered by quotients + truncation
2. **Complexity**: General HIT schemes are complex to implement and use
3. **Research Status**: General HIT theory still developing

**Future Consideration**:
- May add specific HITs (e.g., interval, pushout) if clear use case emerges
- Will monitor research on HIT schemas
- Could add as extension/pragma if needed

### 2.6 DECISION A03-006: Consider Truncation Level Tracking

**Decision**: TERAS-LANG MAY track truncation levels for decidability guarantees.

**Status**: UNDER CONSIDERATION

**Priority**: MEDIUM

**Potential Specification**:

```
-- Truncation level annotations
@isProp  -- (-1)-truncated, at most one element
@isSet   -- 0-truncated, set-level equality  
@isGroupoid  -- 1-truncated

-- Compiler can use these for:
-- 1. Optimization (erase proof-irrelevant data)
-- 2. Decidability (set equality may be decidable)
-- 3. Documentation
```

**Benefits**:
- Automatic proof erasure for @isProp types
- Equality decidability hints for @isSet types
- Type system documentation

**Concerns**:
- Annotation burden on users
- May complicate type checking
- Not strictly necessary for core security features

---

## 3. Integration Architecture

### 3.1 Type System Extensions

```
TERAS Type Hierarchy
├── Type (standard types)
├── Prop (propositions, proof-irrelevant)  -- ≡ ∥Type∥ with isProp
├── Set (sets, decidable equality target)  -- 0-truncated
├── Quotient A R (set quotients)
├── ∥A∥ (propositional truncation)
└── [existing: Refined, Linear, Effect, IFC types]
```

### 3.2 Syntax Additions

```
-- Quotient type
type Label = LabelRep / label_equiv

-- Quotient constructor
let l : Label = [raw_label]

-- Quotient pattern matching (for sets)
match q : A/R returning Set with
  | [a] => f a
end

-- Propositional truncation
type HasKey = ∥Σ(k: Key). valid(k)∥

-- Truncation introduction
let proof : HasKey = |witness|

-- Truncation elimination (into Prop only)
match t : ∥A∥ returning Prop with
  | |a| => p a
end
```

### 3.3 Interaction with Other Features

**With Refinement Types**:
```
-- Refinement over quotient
type PositiveLabel = { l : Label | positive(l) }

-- Quotient of refined type
type NonzeroRational = { (n,d) : Int × Int | d ≠ 0 } / rational_equiv
```

**With Linear Types**:
```
-- Linear quotient (each element used once)
type LinearToken = TokenRep / token_equiv  -- with linear usage

-- Truncation preserves linearity
type HasLinearResource = ∥Linear(Resource)∥
```

**With IFC Types**:
```
-- Security level quotient
type SecLevel = LevelRep / level_equiv

-- Labeled truncation
type HasSecret[L] = ∥Secret[L]∥  -- existence at level L
```

---

## 4. Implementation Roadmap

### Phase 1: Core Quotients (Priority: HIGH)
1. Add Quotient type former to AST
2. Implement quotient formation rules
3. Add [_] constructor and eq/ equality
4. Implement set-restricted elimination
5. Add reduction rules for quotient elimination

### Phase 2: Propositional Truncation (Priority: HIGH)
1. Add ∥_∥ type former
2. Implement truncation formation rules
3. Add |_| constructor and trunc equality
4. Implement prop-restricted elimination
5. Optimize for proof erasure during extraction

### Phase 3: Integration (Priority: MEDIUM)
1. Integrate quotients with refinement types
2. Integrate with linear types
3. Integrate with IFC types
4. Add convenience syntax

### Phase 4: Optional Extensions (Priority: LOW)
1. Consider truncation level annotations
2. Evaluate specific HITs if needed
3. Research function extensionality needs

---

## 5. Risk Analysis

### 5.1 Risks of Adoption

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Quotient implementation complexity | Medium | Medium | Incremental development |
| Performance of quotient elimination | Low | Medium | Optimize computation rules |
| User confusion with truncation | Medium | Low | Good documentation |
| Integration complexity | Medium | Medium | Clear type system design |

### 5.2 Risks of Rejection (Full HoTT)

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Missing needed feature | Low | Low | Can add specific features later |
| Academic perception | Low | Very Low | Focus on practical security |
| Limited research collaboration | Low | Low | Different research community |

---

## 6. Validation Criteria

### 6.1 Quotient Types Success Criteria

- [ ] Security policy equivalence expressible as quotient
- [ ] Quotient elimination computes correctly
- [ ] Integration with refinement types works
- [ ] No performance regression for non-quotient code

### 6.2 Propositional Truncation Success Criteria

- [ ] Proof irrelevance achieved for truncated types
- [ ] Extraction erases truncated proofs
- [ ] Integration with security predicates clean
- [ ] Classical reasoning patterns available

---

## 7. Related Decisions

| Decision | Reference | Relationship |
|----------|-----------|--------------|
| A01-001 (MLTT Base) | RESEARCH_A01 | Foundation for extensions |
| A02-003 (CIC Inductive) | RESEARCH_A02 | Quotients extend inductives |
| A04-XXX (Linear Types) | RESEARCH_A04 | Must integrate with quotients |
| A08-XXX (Refinement) | RESEARCH_A08 | Must integrate with quotients |

---

## 8. Approval and Sign-off

### Decision Authority

These decisions are made under the TERAS Research Track authority and align with:
- TERAS Master Architecture requirements
- Effect Gate Doctrine compliance
- Security-first design philosophy

### Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2026-01-03 | Initial decision document |

---

## 9. Appendix: Rejected Alternatives

### A. Full Cubical Implementation

**Rejected because**:
- 10x implementation complexity estimate
- Ongoing performance research
- Security use cases don't require full power

### B. Axiomatic Univalence

**Rejected because**:
- Breaks canonicity
- Complicates extraction
- Limited practical benefit for security

### C. No HoTT Features

**Rejected because**:
- Quotients genuinely useful for security policies
- Proof irrelevance valuable for extraction
- Missing these would require awkward encodings

---

*End of Decision Document*

**Document Hash**: To be computed
**Next Session**: A-04 (Linear Logic and Linear Types)
