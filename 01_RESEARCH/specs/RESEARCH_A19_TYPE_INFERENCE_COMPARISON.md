# TERAS-LANG Research Comparison A-19: Type Inference Algorithms

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A19-COMPARISON |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## 1. Systems Compared

| System | Approach | Language/Context |
|--------|----------|------------------|
| Algorithm W | Classic Damas-Milner | ML, Haskell 98 |
| Algorithm J | Optimized HM | SML/NJ, OCaml |
| Bidirectional | Check/Synth modes | Agda, GHC |
| OutsideIn(X) | Constraint-based | GHC (modern) |
| Complete and Easy | Bidir + polymorphism | Research, Idris |
| Local Type Inference | Minimal annotations | Scala, Kotlin |
| Flow | Union types + inference | JavaScript |

---

## 2. Feature Comparison Matrix

### 2.1 Core Capabilities

| Feature | W | J | Bidir | OutsideIn | C&E | Local | Flow |
|---------|---|---|-------|-----------|-----|-------|------|
| Let-polymorphism | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ | â— |
| Higher-rank | âœ— | âœ— | âœ“ | âœ“ | âœ“ | â— | âœ— |
| GADTs | âœ— | âœ— | âœ“ | âœ“ | âœ“ | âœ— | âœ— |
| Type families | âœ— | âœ— | â— | âœ“ | â— | âœ— | âœ— |
| Type classes | ext | ext | ext | âœ“ | ext | ext | âœ— |
| Subtyping | âœ— | âœ— | âœ“ | â— | âœ“ | âœ“ | âœ“ |
| Refinement | âœ— | âœ— | ext | ext | âœ“ | âœ— | âœ— |

### 2.2 Inference Quality

| Property | W | J | Bidir | OutsideIn | C&E | Local | Flow |
|----------|---|---|-------|-----------|-----|-------|------|
| Principal types | âœ“ | âœ“ | â— | âœ“ | âœ“ | â— | âœ— |
| Complete | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ | â— | âœ— |
| Sound | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ | â— |
| Decidable | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ |
| Predictable | â— | â— | âœ“ | â— | âœ“ | âœ“ | â— |

### 2.3 Error Quality

| Property | W | J | Bidir | OutsideIn | C&E | Local | Flow |
|----------|---|---|-------|-----------|-----|-------|------|
| Localized errors | â— | â— | âœ“ | â— | âœ“ | âœ“ | â— |
| Clear messages | â— | â— | âœ“ | â— | âœ“ | âœ“ | â— |
| Suggestions | âœ— | âœ— | â— | âœ“ | â— | âœ“ | âœ“ |
| Type holes | âœ— | âœ— | âœ“ | âœ“ | âœ“ | â— | âœ— |

---

## 3. Detailed Algorithm Analysis

### 3.1 Algorithm W (Damas-Milner)

**Approach:** Recursive descent with substitution composition

**Pseudocode:**
```
W(Î“, e) returns (Substitution, Type)

W(Î“, x) = (âˆ…, inst(Î“(x)))
W(Î“, Î»x.e) = let (S, Ï„) = W(Î“ âˆª {x:Î±}, e) in (S, SÎ± â†’ Ï„)
W(Î“, eâ‚ eâ‚‚) = let (Sâ‚, Ï„â‚) = W(Î“, eâ‚)
              let (Sâ‚‚, Ï„â‚‚) = W(Sâ‚Î“, eâ‚‚)
              let Sâ‚ƒ = unify(Sâ‚‚Ï„â‚, Ï„â‚‚ â†’ Î±)
              in (Sâ‚ƒâˆ˜Sâ‚‚âˆ˜Sâ‚, Sâ‚ƒÎ±)
W(Î“, let x = eâ‚ in eâ‚‚) = let (Sâ‚, Ï„â‚) = W(Î“, eâ‚)
                          let Ïƒ = gen(Sâ‚Î“, Ï„â‚)
                          let (Sâ‚‚, Ï„â‚‚) = W(Sâ‚Î“ âˆª {x:Ïƒ}, eâ‚‚)
                          in (Sâ‚‚âˆ˜Sâ‚, Ï„â‚‚)
```

**Strengths:**
- Simple to implement
- Well-understood theory
- Principal types guaranteed
- Complete for HM

**Weaknesses:**
- Quadratic complexity (substitution composition)
- Poor error messages
- No subtyping
- Limited feature support

### 3.2 Algorithm J (Optimized HM)

**Approach:** Mutable references instead of substitution

**Key Optimization:**
```
Type variable: Ref<Option<Type>>
- None: unsolved
- Some(Ï„): solved to Ï„

Union-find for equivalence:
- Near-constant time unification
- Path compression
- Rank-based union
```

**Strengths:**
- Near-linear complexity
- Same coverage as W
- More efficient for large programs
- Standard in production compilers

**Weaknesses:**
- Mutable state complicates reasoning
- Same feature limitations as W
- Error messages still difficult
- Backtracking harder

### 3.3 Bidirectional Type Checking

**Approach:** Two judgment forms (check vs synthesize)

**Core Judgments:**
```
Î“ âŠ¢ e â‡’ A  (synthesize A from e)
Î“ âŠ¢ e â‡ A  (check e against A)
```

**Key Rules:**
```
Var:    (x : A) âˆˆ Î“
        â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
        Î“ âŠ¢ x â‡’ A

App:    Î“ âŠ¢ eâ‚ â‡’ A â†’ B    Î“ âŠ¢ eâ‚‚ â‡ A
        â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
        Î“ âŠ¢ eâ‚ eâ‚‚ â‡’ B

Lam:    Î“, x : A âŠ¢ e â‡ B
        â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
        Î“ âŠ¢ Î»x. e â‡ A â†’ B

Anno:   Î“ âŠ¢ e â‡ A
        â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
        Î“ âŠ¢ (e : A) â‡’ A

Sub:    Î“ âŠ¢ e â‡’ A    A <: B
        â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
        Î“ âŠ¢ e â‡ B
```

**Strengths:**
- Predictable type flow
- Localized errors
- Natural for subtyping
- Higher-rank types
- Modular rules

**Weaknesses:**
- Needs annotations at mode switches
- Less inference than HM in some cases
- Design choices for subsumption

### 3.4 OutsideIn(X)

**Approach:** Implication constraints with modular solving

**Constraint Language:**
```
C ::= Ï„â‚ ~ Ï„â‚‚           (equality)
    | Câ‚ âˆ§ Câ‚‚           (conjunction)
    | âˆƒÎ±. C             (existential)
    | Q âŠƒ C             (implication: given Q, wanted C)
    | D Ï„               (type class: instance of D at Ï„)
```

**Solving Strategy:**
```
1. Generate constraints for whole program
2. Simplify: flatten conjunctions, reduce type families
3. Solve: unify equalities, resolve instances
4. Check: verify implications satisfied
5. Generalize: create polymorphic types
```

**Strengths:**
- Handles type families
- Type classes native
- GADTs supported
- Modular (separate compilation)
- Touchable variables prevent escape

**Weaknesses:**
- Complex implementation
- Can produce confusing errors
- Defaulting rules tricky
- Ambiguous types need resolution

### 3.5 Complete and Easy Bidirectional

**Approach:** Bidirectional + existential variables + subtyping

**Context Extension:**
```
Î“ ::= Â· | Î“, x : A | Î“, Î± | Î“, Î±Ì‚ | Î“, Î±Ì‚ = Ï„ | Î“, â–¸Î±Ì‚

Î±Ì‚ = existential variable (to be solved)
â–¸Î±Ì‚ = marker (for scoping)
```

**Key Innovation:**
```
âˆ€-Application:
    Î“ âŠ¢ e â‡’ âˆ€Î±. A
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“, Î±Ì‚ âŠ¢ e â‡’ [Î± â†¦ Î±Ì‚]A

Existential solving:
    During checking, Î±Ì‚ may be solved to concrete type
    Solution must respect context ordering
```

**Strengths:**
- Higher-rank polymorphism
- Subtyping integration
- Complete for predicative fragment
- Elegant metatheory
- Good error properties

**Weaknesses:**
- Context threading complex
- Requires careful implementation
- Impredicativity limited

### 3.6 Local Type Inference

**Approach:** Minimal annotations, local type propagation

**Principles:**
```
1. Propagate types from annotations downward
2. Synthesize types from leaves upward
3. Meet in the middle at mode switches
4. Require annotations at polymorphic recursion
```

**Example (Scala):**
```scala
val f: Int => Int = x => x + 1  // x inferred as Int
val g = (x: Int) => x + 1       // Return type inferred
val xs = List(1, 2, 3)          // Element type inferred
```

**Strengths:**
- Minimal annotations
- Good for OO languages
- Practical for real codebases
- Familiar to developers

**Weaknesses:**
- Not complete
- May fail to infer
- Different from HM behavior
- Less predictable

### 3.7 Flow Type Inference

**Approach:** Union/intersection types, widening

**Key Ideas:**
```
1. Types can be unions: string | number
2. Narrowing via control flow: if (typeof x === "string") ...
3. Widening to prevent infinite types
4. Soundness sacrificed for practicality
```

**Strengths:**
- Handles JavaScript idioms
- Gradual typing
- Practical for dynamic code
- Good tooling integration

**Weaknesses:**
- Unsound
- Complex union reasoning
- Performance issues
- Unpredictable inference

---

## 4. Performance Comparison

### 4.1 Time Complexity

| Algorithm | Best Case | Worst Case | Typical |
|-----------|-----------|------------|---------|
| W | O(n) | O(nÂ²) | O(n log n) |
| J | O(n Î±(n)) | O(n Î±(n)) | O(n Î±(n)) |
| Bidir | O(n) | O(nÂ²) | O(n) |
| OutsideIn | O(n) | O(nÂ²) | O(n log n) |
| C&E | O(n) | O(nÂ²) | O(n) |
| Local | O(n) | O(nÂ²) | O(n) |
| Flow | O(n) | O(nÂ³) | O(nÂ²) |

### 4.2 Space Complexity

| Algorithm | Space | Notes |
|-----------|-------|-------|
| W | O(n) | Substitution chains |
| J | O(n) | Union-find structure |
| Bidir | O(n) | Context stack |
| OutsideIn | O(nÂ²) | Constraint store |
| C&E | O(n) | Context with markers |
| Local | O(n) | Propagation info |
| Flow | O(nÂ²) | Type graph |

### 4.3 Practical Performance

| Algorithm | Small Programs | Large Programs | Incremental |
|-----------|----------------|----------------|-------------|
| W | Fast | Slow | Poor |
| J | Fast | Fast | Poor |
| Bidir | Fast | Fast | Good |
| OutsideIn | Medium | Medium | Good |
| C&E | Fast | Fast | Good |
| Local | Fast | Medium | Good |
| Flow | Slow | Slow | Medium |

---

## 5. Error Message Quality

### 5.1 Error Localization

| Algorithm | Localization | Why |
|-----------|--------------|-----|
| W | Poor | Constraint far from source |
| J | Poor | Same as W |
| Bidir | Excellent | Error at mode switch |
| OutsideIn | Medium | Constraint solving order |
| C&E | Excellent | Scoped existentials |
| Local | Good | Local propagation |
| Flow | Medium | Union widening hides source |

### 5.2 Example Error Messages

**Algorithm W/J:**
```
Error: Cannot unify Int with String
  In the application: f x
  
(May be far from actual error)
```

**Bidirectional:**
```
Error: Type mismatch in argument
  Expected: Int
  Got: String
  
  In: f "hello"
       ^^^^^^^
```

**OutsideIn:**
```
Error: Could not deduce (Show a) arising from use of 'show'
  Possible fix: add (Show a) to the context of the type signature
  
  In: show x
```

**Complete and Easy:**
```
Error: Cannot check Î»x. x against Int â†’ String
  The function returns: x
  But expected: String
  
  In: (Î»x. x) : Int â†’ String
          ^
```

---

## 6. Security Feature Support

### 6.1 Information Flow

| Algorithm | IFC Support | Approach |
|-----------|-------------|----------|
| W | âœ— | N/A |
| J | âœ— | N/A |
| Bidir | âœ“ | Check labels in subtyping |
| OutsideIn | â— | Constraints on labels |
| C&E | âœ“ | Label in subtyping lattice |
| Local | â— | Propagate labels |
| Flow | â— | Union of labels |

### 6.2 Capability Inference

| Algorithm | Capability Support | Approach |
|-----------|-------------------|----------|
| W | ext | Add effect variables |
| J | ext | Add effect variables |
| Bidir | âœ“ | Track in context |
| OutsideIn | âœ“ | Constraints on effects |
| C&E | âœ“ | Effects in checking |
| Local | â— | Local propagation |
| Flow | âœ— | N/A |

### 6.3 Linear Type Support

| Algorithm | Linear Support | Approach |
|-----------|---------------|----------|
| W | âœ— | Context not split |
| J | âœ— | Context not split |
| Bidir | âœ“ | Split context in rules |
| OutsideIn | â— | Multiplicity constraints |
| C&E | âœ“ | Usage in context |
| Local | â— | Usage tracking |
| Flow | âœ— | N/A |

---

## 7. Comparative Code Examples

### 7.1 Simple Polymorphic Function

**All algorithms infer:** `id : âˆ€Î±. Î± â†’ Î±`
```
let id = Î»x. x
```

### 7.2 Higher-Rank Type

**Need annotation for higher-rank:**
```
// Only bidir, OutsideIn, C&E handle this
let apply : (âˆ€Î±. Î± â†’ Î±) â†’ Int â†’ Int
let apply = Î»f. Î»x. f x
```

| Algorithm | Infers? | Notes |
|-----------|---------|-------|
| W | âœ— | No higher-rank |
| J | âœ— | No higher-rank |
| Bidir | âœ“ | Checks against annotation |
| OutsideIn | âœ“ | Instantiates at use |
| C&E | âœ“ | Scoped existentials |

### 7.3 GADT Pattern Match

```haskell
data Expr a where
    LitInt :: Int â†’ Expr Int
    Add :: Expr Int â†’ Expr Int â†’ Expr Int

eval :: Expr a â†’ a
eval (LitInt n) = n      -- needs: a ~ Int
eval (Add x y) = eval x + eval y
```

| Algorithm | Handles? | Notes |
|-----------|----------|-------|
| W | âœ— | No refinement |
| J | âœ— | No refinement |
| Bidir | âœ“ | Pattern refines type |
| OutsideIn | âœ“ | Local assumptions |
| C&E | âœ“ | Pattern matching |

### 7.4 Effect Inference

```
let f = Î»x. do
    print(x)
    return (x + 1)
// Should infer: Int -[IO]â†’ Int
```

| Algorithm | Infers? | Notes |
|-----------|---------|-------|
| W | ext | With effect extension |
| J | ext | With effect extension |
| Bidir | âœ“ | Effects in judgment |
| OutsideIn | âœ“ | Effect constraints |
| C&E | âœ“ | Effect rows |

---

## 8. TERAS-LANG Suitability Analysis

### 8.1 Evaluation Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| Security support | 25% | IFC, caps, linear |
| Error quality | 20% | Localization, clarity |
| Feature coverage | 20% | HKT, GADTs, effects |
| Performance | 15% | Compile time |
| Predictability | 10% | Developer experience |
| Implementation | 10% | Complexity |

### 8.2 Weighted Scores

| Algorithm | Security | Errors | Features | Perf | Predict | Impl | **Total** |
|-----------|----------|--------|----------|------|---------|------|-----------|
| W | 3 | 4 | 3 | 7 | 5 | 9 | **4.35** |
| J | 3 | 4 | 3 | 9 | 5 | 8 | **4.55** |
| Bidir | 9 | 9 | 8 | 8 | 9 | 6 | **8.35** |
| OutsideIn | 7 | 6 | 9 | 7 | 6 | 4 | **6.85** |
| C&E | 9 | 9 | 8 | 8 | 9 | 5 | **8.20** |
| Local | 5 | 7 | 5 | 8 | 8 | 7 | **6.30** |
| Flow | 2 | 5 | 4 | 4 | 4 | 6 | **3.85** |

### 8.3 Recommendation

**Primary: Bidirectional type checking** with constraint solving for advanced features.

**Rationale:**
1. Best error localization for security failures
2. Natural fit for substructural types
3. Handles higher-rank and GADTs
4. Predictable for developers
5. Extensible to security features

---

## 9. Hybrid Approach for TERAS-LANG

### 9.1 Proposed Architecture

```
TERAS-LANG Inference = Bidirectional + Constraints
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
Core:
â”œâ”€â”€ Bidirectional checking for all terms
â”œâ”€â”€ Mode switch at annotations and applications
â””â”€â”€ Subtyping in subsumption rule

Extensions:
â”œâ”€â”€ Constraint generation for type classes
â”œâ”€â”€ Effect row inference with constraints
â”œâ”€â”€ Capability set collection
â”œâ”€â”€ Linear usage tracking
â””â”€â”€ Security label inference

Solving:
â”œâ”€â”€ Unification with union-find (from J)
â”œâ”€â”€ Constraint simplification
â”œâ”€â”€ Implication checking (from OutsideIn)
â””â”€â”€ Defaulting for ambiguous types
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

### 9.2 Security-Specific Extensions

```
Security Inference Components:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
Label Inference:
    - Generate label variables for unknown labels
    - Collect flow constraints from operations
    - Solve: minimal consistent labeling
    - Report: declassification requirements

Capability Inference:
    - Track required capabilities per function
    - Collect from primitive operations
    - Report: manifest of required capabilities
    - Verify: capability subset constraints

Linear Tracking:
    - Count usage of each variable
    - Split contexts in application
    - Report: unused or overused linear variables
    - Integrate: with capability consumption
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

---

## 10. Summary

### 10.1 Key Differentiators

| Approach | Best For | Avoid For |
|----------|----------|-----------|
| W/J | Simple HM languages | Advanced features |
| Bidir | Modern typed langs | Pure inference |
| OutsideIn | GHC-like languages | Simple languages |
| C&E | Research/new langs | Production (complexity) |
| Local | OO languages | Functional langs |
| Flow | Dynamic languages | Static guarantees |

### 10.2 TERAS-LANG Direction

TERAS-LANG should adopt **bidirectional type checking** as the foundation, extended with:
- Constraint solving for type classes and families
- Usage tracking for linear types
- Label inference for information flow
- Capability collection for permissions
- Excellent error messages with blame tracking

This combination provides the best balance of expressiveness, security support, error quality, and implementation tractability.

---

*Comparison document for TERAS-LANG research track. Analysis of type inference algorithms for security-focused language design.*
