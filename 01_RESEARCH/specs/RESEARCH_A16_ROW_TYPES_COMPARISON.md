# TERAS-LANG Research Track
# Session A-16: Row Types and Row Polymorphism
# Document Type: Comparative Analysis

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  COMPARATIVE ANALYSIS: ROW TYPE SYSTEMS                                      ║
║                                                                              ║
║  Comparing: Wand, Rémy, OCaml, PureScript, TypeScript, Effect Rows           ║
║  Criteria: Expressiveness, Inference, Extensibility, Security Fit            ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

## 1. System Overview Matrix

| System | Year | Base Language | Row Application | Inference | Labels |
|--------|------|---------------|-----------------|-----------|--------|
| Wand | 1987 | Theory | Records | Partial | Unique |
| Rémy | 1989 | ML | Records | Complete | Flags |
| OCaml Variants | 1996 | OCaml | Variants | Complete | Bounded |
| PureScript | 2012 | Haskell-like | Records + Effects | Complete | First-class |
| TypeScript | 2016 | JavaScript | Objects | Limited | Computed |
| Koka/Frank | 2019 | FP | Effects | Complete | Scoped |

---

## 2. Expressiveness Comparison

### 2.1 Core Operations

| Operation | Wand | Rémy | OCaml | PureScript | TypeScript | Effect Rows |
|-----------|------|------|-------|------------|------------|-------------|
| Field Access | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Field Extension | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| Field Removal | ✗ | ✓ | ✗ | ✓ | ✓ | ✓ |
| Concatenation | Limited | ✓ | ✗ | Partial | ✓ | ✗ |
| Row Polymorphism | ✓ | ✓ | ✓ | ✓ | Limited | ✓ |
| Duplicate Labels | ✗ | ✗ | ✗ | ✗ | ✗ | ✓ (scoped) |
| Row Constraints | ✗ | ✓ | ✓ | ✓ | ✓ | ✓ |

### 2.2 Type-Level Features

| Feature | Wand | Rémy | OCaml | PureScript | TypeScript |
|---------|------|------|-------|------------|------------|
| Row Variables | ✓ | ✓ | ✓ | ✓ | Partial |
| Row Kinds | ✗ | ✗ | ✗ | ✓ | ✗ |
| Higher-Kinded Rows | ✗ | ✗ | ✗ | ✓ | ✗ |
| Mapped Types | ✗ | ✗ | ✗ | Via HKT | ✓ |
| Conditional Types | ✗ | ✗ | ✗ | Partial | ✓ |
| Label Computation | ✗ | ✗ | ✗ | ✗ | ✓ |

### 2.3 Expressiveness Score

```
Expressiveness Ranking (1-10):

PureScript:  ████████░░ 8/10  (First-class rows, HKT, kinds)
TypeScript:  ███████░░░ 7/10  (Mapped types, conditionals)
Rémy:        ██████░░░░ 6/10  (Flags, removal, concatenation)
Effect Rows: ██████░░░░ 6/10  (Scoped labels, handlers)
OCaml:       █████░░░░░ 5/10  (Variants only, bounded)
Wand:        ████░░░░░░ 4/10  (Original, limited operations)
```

---

## 3. Type Inference Comparison

### 3.1 Inference Capabilities

| System | Inference Method | Completeness | Principal Types | Decidability |
|--------|------------------|--------------|-----------------|--------------|
| Wand | Extension of HM | Partial | No | Yes |
| Rémy | ML + Flags | Complete | Yes | Yes |
| OCaml Variants | HM + Bounds | Complete | Yes | Yes |
| PureScript | Qualified Types | Complete | Yes | Yes |
| TypeScript | Structural Flow | Partial | No | Undecidable* |
| Effect Rows | Row Unification | Complete | Yes | Yes |

*TypeScript has edge cases; practical decidability for typical code.

### 3.2 Annotation Requirements

```
Annotation Burden:

Rémy:       █░░░░░░░░░ Minimal (automatic inference)
OCaml:      ██░░░░░░░░ Low (variance annotations for APIs)
PureScript: ███░░░░░░░ Moderate (row kinds explicit)
Effect Rows:███░░░░░░░ Moderate (effect declarations)
TypeScript: ████░░░░░░ Moderate (generic constraints)
Wand:       █████░░░░░ Higher (lacks constraints)
```

### 3.3 Unification Complexity

| System | Algorithm | Time Complexity | Space Complexity |
|--------|-----------|-----------------|------------------|
| Wand | Row extension | O(n²) | O(n) |
| Rémy | Flag-based | O(n log n) | O(n) |
| OCaml | Bounds propagation | O(n) | O(n) |
| PureScript | Qualified unification | O(n²) | O(n) |
| TypeScript | Structural | O(n³) worst | O(n²) |
| Effect Rows | Row with scopes | O(n log n) | O(n) |

---

## 4. Record vs Variant Row Types

### 4.1 Duality

```
Record Rows (Wand/Rémy/PureScript):
─────────────────────────────────────
  {x : Int ; y : String}        -- Has fields x, y
  {x : Int | r}                  -- Has at least x
  
Variant Rows (OCaml):
─────────────────────────────────────
  [> `A of Int | `B of String]  -- Has at least A, B
  [< `A of Int | `B of String]  -- Has at most A, B
  
Effect Rows (Koka/Frank):
─────────────────────────────────────
  <console, state | e>          -- Has effects console, state
```

### 4.2 Subtyping Behavior

| Row Kind | Width Subtyping | Depth Subtyping |
|----------|-----------------|-----------------|
| Records | More fields ≤ Fewer | Covariant |
| Variants | Fewer cases ≤ More | Contravariant* |
| Effects | More effects ≤ Fewer | Covariant |

*Variant input positions are contravariant

### 4.3 Application Fit

| Use Case | Best Row Type |
|----------|---------------|
| Configuration objects | Record rows (PureScript) |
| Error handling | Variant rows (OCaml) |
| Effect tracking | Effect rows (Koka) |
| Web APIs | Record rows + Mapped (TypeScript) |
| Database queries | Record rows (Ur/Web) |

---

## 5. Extensibility Mechanisms

### 5.1 Row Extension Syntax

**PureScript**:
```purescript
type Extended = { newField :: Int | BaseRow }
```

**TypeScript**:
```typescript
type Extended = BaseType & { newField: number }
```

**OCaml**:
```ocaml
type extended = [ base | `NewCase of int ]
```

**Effect Rows**:
```koka
type extended = <newEffect | baseEffects>
```

### 5.2 Row Restriction

| System | Restriction Syntax | Static Guarantee |
|--------|-------------------|------------------|
| Rémy | `r \ ℓ` | ✓ Compile-time |
| PureScript | Via constraint solving | ✓ Compile-time |
| TypeScript | `Omit<T, K>` | ✓ Compile-time |
| OCaml | Not supported | N/A |
| Effect Rows | Handler masking | ✓ Compile-time |

### 5.3 Extensibility Score

```
Extensibility Ranking:

TypeScript:  █████████░ 9/10  (Intersection, mapped, conditionals)
PureScript:  ████████░░ 8/10  (First-class, constraints)
Effect Rows: ███████░░░ 7/10  (Handlers, masking)
Rémy:        ██████░░░░ 6/10  (Flags, removal)
OCaml:       ████░░░░░░ 4/10  (Bounded only)
Wand:        ███░░░░░░░ 3/10  (Extension only)
```

---

## 6. Security Feature Comparison

### 6.1 Capability Modeling

| System | Capability Rows | Attenuation | Revocation |
|--------|-----------------|-------------|------------|
| PureScript | ✓ Via constraints | ✓ Row restriction | Manual |
| Effect Rows | ✓ Native | ✓ Handler masking | ✓ Via handlers |
| TypeScript | Partial | ✓ Omit | Manual |
| Rémy | ✓ Via flags | ✓ Field removal | Manual |
| OCaml | Limited | ✗ | ✗ |

### 6.2 Information Flow

| System | Label Tracking | Lattice Support | Declassification |
|--------|----------------|-----------------|------------------|
| Effect Rows | ✓ Effect labels | Via row ordering | ✓ Effect handlers |
| PureScript | Via type classes | Custom | Via constraints |
| TypeScript | Branded types | Manual | Type assertions |
| Rémy | Via presence flags | Limited | Flag change |
| OCaml | Via variants | Limited | Pattern match |

### 6.3 Taint Tracking

| System | Per-Field Taint | Propagation | Sanitization |
|--------|-----------------|-------------|--------------|
| Effect Rows | ✓ Effect per field | ✓ Effect composition | ✓ Handler |
| TypeScript | ✓ Branded types | ✓ Via mapped types | ✓ Type guards |
| PureScript | ✓ Row fields | ✓ Row operations | ✓ Constraints |
| Rémy | Partial | Manual | Flag manipulation |

### 6.4 Security Score

```
Security Fit Ranking:

Effect Rows: █████████░ 9/10  (Native capability/effect model)
PureScript:  ████████░░ 8/10  (Constraints, kinds)
TypeScript:  ██████░░░░ 6/10  (Mapped types, guards)
Rémy:        █████░░░░░ 5/10  (Flags for presence)
OCaml:       ████░░░░░░ 4/10  (Variants for errors)
Wand:        ███░░░░░░░ 3/10  (Limited security features)
```

---

## 7. Integration with Substructural Types

### 7.1 Linear/Affine Row Fields

| System | Linear Fields | Affine Fields | Field Consumption |
|--------|---------------|---------------|-------------------|
| Effect Rows | Via effect | Via effect | Handler-based |
| PureScript | Manual | Manual | Not native |
| Rémy | Not native | Not native | Not native |
| TypeScript | Not supported | Not supported | N/A |
| OCaml | Not supported | Not supported | N/A |

### 7.2 Ownership-Aware Rows

| System | Owned Fields | Borrowed Fields | Move Semantics |
|--------|--------------|-----------------|----------------|
| Effect Rows | Via effect | Via effect | Not native |
| PureScript | Manual | Manual | Not native |
| All others | Not supported | Not supported | N/A |

### 7.3 Substructural Integration Feasibility

```
Integration Feasibility:

Effect Rows:     Good  (Effects can encode linearity)
PureScript:      Medium (Manual encoding possible)
TypeScript:      Poor  (No substructural support)
Rémy/OCaml/Wand: Poor  (Requires extension)
```

---

## 8. Performance Characteristics

### 8.1 Compile-Time Overhead

| System | Type Checking | Inference | Constraint Solving |
|--------|---------------|-----------|-------------------|
| OCaml | Fast | Fast | Minimal |
| Rémy | Fast | Fast | Moderate |
| PureScript | Moderate | Moderate | Moderate |
| TypeScript | Slow | Slow | Complex |
| Effect Rows | Moderate | Moderate | Moderate |

### 8.2 Runtime Overhead

| System | Record Access | Field Operations | Memory |
|--------|---------------|------------------|--------|
| OCaml | Zero (monomorphized) | Zero | Optimal |
| PureScript | Dictionary passing | Pointer chase | Extra dict |
| TypeScript | Zero (erased) | Zero | Standard JS |
| Effect Rows | Handler overhead | Handler lookup | Handler stack |

### 8.3 Performance Score

```
Performance Ranking:

OCaml:       █████████░ 9/10  (Monomorphization, zero overhead)
TypeScript:  ████████░░ 8/10  (Erased at runtime)
Rémy:        ███████░░░ 7/10  (Efficient, some dict passing)
PureScript:  ██████░░░░ 6/10  (Dictionary passing overhead)
Effect Rows: █████░░░░░ 5/10  (Handler runtime cost)
```

---

## 9. Ecosystem and Tooling

### 9.1 Language Support

| System | Native Language | Library Support | IDE Integration |
|--------|-----------------|-----------------|-----------------|
| TypeScript | TypeScript | Excellent | Excellent |
| OCaml | OCaml | Good | Good |
| PureScript | PureScript | Good | Good |
| Effect Rows | Koka/Frank | Limited | Limited |
| Rémy | Academic | None | None |

### 9.2 Documentation and Community

| System | Documentation | Community | Learning Resources |
|--------|---------------|-----------|-------------------|
| TypeScript | Excellent | Large | Abundant |
| OCaml | Good | Medium | Good |
| PureScript | Good | Small | Moderate |
| Effect Rows | Research papers | Minimal | Academic |
| Rémy/Wand | Research papers | Academic | Papers only |

---

## 10. TERAS Alignment Assessment

### 10.1 Requirement Mapping

| TERAS Requirement | Best Fit System | Alignment Score |
|-------------------|-----------------|-----------------|
| Capability rows | Effect Rows | 9/10 |
| Taint tracking | TypeScript / PureScript | 7/10 |
| Permission modeling | PureScript | 8/10 |
| Protocol state | Effect Rows | 8/10 |
| Effect composition | Effect Rows | 9/10 |
| Type inference | Rémy / PureScript | 8/10 |
| Zero runtime overhead | OCaml | 9/10 |
| Security labels | Effect Rows | 8/10 |

### 10.2 Integration Complexity

| Integration | Complexity | Risk | Benefit |
|-------------|------------|------|---------|
| Row + Linear | Medium | Low | High (resource rows) |
| Row + Effects | Low | Low | High (native fit) |
| Row + Refinement | Medium | Medium | High (refined rows) |
| Row + Ownership | Medium | Medium | High (owned fields) |
| Row + Regions | Medium | Low | Medium (regional rows) |

### 10.3 Overall TERAS Fit

```
TERAS Alignment Ranking:

Effect Rows (Koka-style): █████████░ 9/10
  + Native capability/effect model
  + Scoped labels for security
  + Handler-based masking
  - Research maturity
  
PureScript-style:         ████████░░ 8/10
  + First-class row kinds
  + Excellent inference
  + Good expressiveness
  - Dictionary passing overhead
  
Rémy-style:               ███████░░░ 7/10
  + Proven inference algorithm
  + Presence/absence flags
  + Good for records
  - Limited security features
  
TypeScript-style:         ██████░░░░ 6/10
  + Mapped types powerful
  + Practical ecosystem
  - Undecidable in edge cases
  - No substructural support
  
OCaml-style:              █████░░░░░ 5/10
  + Zero overhead
  + Variants useful
  - Record rows limited
  - No row operations
```

---

## 11. Hybrid Approach Analysis

### 11.1 Rémy + Effect Rows

Combining Rémy's inference with effect row features:

**Strengths**:
- Complete inference for records
- Scoped labels for effects
- Handler-based effect masking

**Challenges**:
- Two row systems to unify
- Interaction complexity

### 11.2 PureScript + Substructural

Adding linear/affine modalities to PureScript rows:

**Strengths**:
- First-class row polymorphism
- Row kinds for abstraction
- Linear field consumption

**Challenges**:
- Inference complexity
- New implementation

### 11.3 Recommended Hybrid

```
TERAS Row Type Design:

Base:       Rémy-style presence/absence flags
Extension:  Effect row integration (A-05, A-11)
Kinds:      PureScript-style row kinds
Substructural: Linear/Affine field annotations
Security:   Row-level security labels

Syntax Example:
  type SecureRequest<ρ : Row> = {
    lin auth : AuthToken ;           -- Linear field
    headers : Headers ;              -- Normal field
    body : Tainted Body ;            -- Security-labeled
    | ρ                              -- Row extension
  }
```

---

## 12. Comparative Summary

### 12.1 Strengths and Weaknesses

| System | Primary Strength | Primary Weakness |
|--------|------------------|------------------|
| Wand | Original formulation | Limited operations |
| Rémy | Complete inference | Security gaps |
| OCaml | Variants + performance | No record rows |
| PureScript | Expressiveness + kinds | Runtime overhead |
| TypeScript | Practical + ecosystem | Inference limits |
| Effect Rows | Security model | Research maturity |

### 12.2 Final Recommendation

**For TERAS-LANG**: Hybrid approach combining:

1. **Rémy-style inference** for record rows with presence flags
2. **Effect row semantics** for capability and effect tracking
3. **PureScript-style kinds** for row abstraction
4. **Substructural annotations** for linear/affine fields
5. **Security labels** integrated into row structure

This provides the expressiveness needed for security properties while maintaining decidable inference.

---

## Document Metadata

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  Document ID: TERAS-RESEARCH-A16-COMPARISON                                  ║
║  Version: 1.0.0                                                              ║
║  Status: COMPLETE                                                            ║
║  Next: A-16 Decision Document                                                ║
╚══════════════════════════════════════════════════════════════════════════════╝
```
