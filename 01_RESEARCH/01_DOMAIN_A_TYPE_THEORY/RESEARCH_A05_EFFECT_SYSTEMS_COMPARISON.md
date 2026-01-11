# RESEARCH_A05_EFFECT_SYSTEMS_COMPARISON.md

## TERAS Research Track: Session A-05
## Effect Systems - Comparative Analysis

**Document Version:** 1.0.0
**Created:** 2026-01-03
**Session:** A-05 of 47
**Track:** Foundational Type Theory

---

## 1. Comparison Overview

This document compares approaches to tracking and managing computational effects, evaluating their suitability for TERAS-LANG's security-focused type system.

### Approaches Compared

| Approach | Representative | Era | Key Innovation |
|----------|---------------|-----|----------------|
| Monadic | Haskell | 1990s | Encapsulated effects via type |
| Effect Systems | FX, Java | 1988-2000 | Effect annotations on types |
| Row-Polymorphic | Koka | 2014+ | Effect rows with polymorphism |
| Algebraic Effects | Eff, OCaml 5 | 2009+ | Operations + handlers |
| Dependent Effects | F* | 2011+ | Effects + refinements + SMT |

---

## 2. Monadic Effects vs. Effect Systems

### 2.1 Monadic Approach (Haskell-style)

**Mechanism:**
```haskell
-- Effects encoded in type constructor
readFile :: FilePath -> IO String
pure :: a -> m a
(>>=) :: m a -> (a -> m b) -> m b
```

**Strengths:**
- Well-understood theory (Kleisli categories)
- Explicit sequencing via bind
- Type-safe effect boundaries
- Mature ecosystem (mtl, transformers)

**Weaknesses:**
- Transformer stacks cumbersome
- Effect ordering fixed by stack
- No effect polymorphism without transformers
- Colored functions (monadic vs. pure)

**Example Problem:**
```haskell
-- Need to know full monad stack
type App a = ExceptT Error (StateT Config (ReaderT Env IO)) a

-- Adding new effect requires changing everywhere
addLogging :: App a -> LoggingT App a  -- invasive change
```

### 2.2 Effect System Approach (Koka-style)

**Mechanism:**
```koka
// Effects as row types
fun readFile(path: string) : ⟨io, exn | ε⟩ string
```

**Strengths:**
- Effect polymorphism built-in
- No transformer boilerplate
- Effects compose automatically
- Inference-friendly

**Weaknesses:**
- Newer, less ecosystem
- Implementation complexity
- Debugging challenges

**Example Advantage:**
```koka
// Effect polymorphism is natural
fun map(f, xs) : e list<b>   // e inferred from f
  match xs
    Nil -> Nil
    Cons(x, xx) -> Cons(f(x), map(f, xx))
```

### 2.3 Comparison Matrix

| Criterion | Monads | Effect Systems |
|-----------|--------|----------------|
| Effect Polymorphism | Requires transformers | Built-in |
| Composability | Manual lifting | Automatic |
| Learning Curve | Moderate | Lower |
| Ecosystem Maturity | High | Growing |
| Type Inference | Good | Excellent |
| Performance | Good | Variable |
| Debugging | Familiar | Challenging |

**TERAS Verdict:** Effect systems preferred for ergonomics and polymorphism.

---

## 3. Row Polymorphism vs. Subtyping

### 3.1 Subtyping Approach

**Mechanism:**
```
Effect subtyping: ε₁ ⊆ ε₂ implies (τ →^ε₁ σ) ≤ (τ →^ε₂ σ)
```

**Example:**
```
// f has fewer effects than expected
f : Int →^{read} Int
g : (Int →^{read,write} Int) → Int
g(f)  // OK: {read} ⊆ {read,write}
```

**Strengths:**
- Intuitive subset relationship
- Flexible effect widening
- Familiar from OO subtyping

**Weaknesses:**
- Inference can be undecidable
- Principal types may not exist
- Complex constraint solving

### 3.2 Row Polymorphism Approach

**Mechanism:**
```
Effect rows: ⟨l₁ | ⟨l₂ | ε⟩⟩ where ε is variable
```

**Example:**
```koka
// Effect variable captures "other effects"
fun foo(f : () -> ⟨exn | ε⟩ int) : ⟨exn | ε⟩ int
  f()
```

**Strengths:**
- Decidable inference
- Principal types exist
- Clean unification-based algorithm
- No subtyping complexity

**Weaknesses:**
- Effect order in rows can confuse
- Duplicate labels need care
- Less intuitive than subsets

### 3.3 Comparison Matrix

| Criterion | Subtyping | Row Polymorphism |
|-----------|-----------|------------------|
| Decidability | Often undecidable | Decidable |
| Principal Types | May not exist | Exist |
| Inference Algorithm | Complex | Unification-based |
| Expressiveness | More flexible | Slightly restricted |
| Implementation | Complex | Manageable |
| User Mental Model | Subset intuition | Row extension |

**TERAS Verdict:** Row polymorphism preferred for decidability and implementation simplicity.

---

## 4. Algebraic Effects vs. Monads

### 4.1 Conceptual Comparison

**Monads:**
- Effects as types: `IO a`, `State s a`
- Fixed semantics per monad
- Combination via transformers
- One "handler" per monad

**Algebraic Effects:**
- Effects as operations: `effect Get : s`, `effect Put : s -> ()`
- Semantics via handlers (multiple possible)
- Combination via effect rows
- Handlers are first-class, composable

### 4.2 Expressiveness

**Monads Cannot Easily Express:**
- Backtracking with state rollback
- Multi-shot continuations
- Cooperative threading

**Algebraic Effects Handle These:**
```
effect Choose : unit -> bool
effect Fail : unit -> nothing

// Backtracking handler
all_results = handler
  | Choose((), k) -> concat [k True, k False]
  | Fail((), k) -> []
  | return x -> [x]
```

### 4.3 Modularity

**Monad Transformers:**
```haskell
-- Order matters: StateT over ExceptT vs ExceptT over StateT
runExceptT . runStateT m s  -- exception doesn't restore state
runStateT (runExceptT m) s  -- exception restores state
```

**Effect Handlers:**
```
// Same effect, different handlers give different semantics
handle m with state_handler
handle m with transactional_handler
// Semantics determined by handler, not effect order
```

### 4.4 Comparison Matrix

| Criterion | Monads | Algebraic Effects |
|-----------|--------|-------------------|
| Theoretical Foundation | Category theory | Universal algebra |
| Modularity | Limited (transformers) | High (handlers) |
| Multi-shot Continuations | Difficult | Natural |
| Semantics Flexibility | Fixed per monad | Handler-defined |
| Implementation | Well-understood | Active research |
| Performance | Good | Improving |
| Mainstream Adoption | Haskell dominates | Growing |

**TERAS Verdict:** Algebraic effects preferred for modularity and flexibility.

---

## 5. Verification-Oriented Effects (F*)

### 5.1 F* Approach

**Key Features:**
- Dependent types + effects + refinements
- Dijkstra monads for WP semantics
- SMT-automated verification
- Multi-monadic effect system

**Effect Definition:**
```fstar
effect ST (a:Type) 
         (pre: heap -> Type) 
         (post: heap -> a -> heap -> Type) =
  STATE a (fun p h -> pre h /\ (forall x h'. post h x h' ==> p x h'))
```

### 5.2 Comparison with Pure Effect Systems

| Aspect | Koka/OCaml 5 | F* |
|--------|--------------|-----|
| Primary Goal | Practical programming | Verification |
| Effect Semantics | Handlers | WP transformers |
| Verification | Limited | SMT-integrated |
| Dependent Types | No | Yes |
| Learning Curve | Moderate | Steep |
| Use Cases | General | Security-critical |

### 5.3 TERAS Relevance

**F*-style Benefits:**
- Proven for cryptographic verification
- Refinement types + effects
- Strong correctness guarantees

**F*-style Challenges:**
- Complexity for general programming
- Annotation burden
- External dependency (Z3)

**TERAS Approach:** Adopt F* concepts (verified effects, WP) but with better ergonomics and zero external dependencies.

---

## 6. Implementation Strategy Comparison

### 6.1 CPS Transformation

**Approach:** Transform effectful code to continuation-passing style.

```
// Before
let x = op(); e
// After
op(λx. ⟦e⟧)
```

**Pros:**
- Well-understood
- Works for all effects
- Good for multi-shot continuations

**Cons:**
- Code bloat
- Optimization challenges
- Debugging difficulty

### 6.2 Evidence Passing

**Approach:** Pass effect capabilities explicitly.

```
// Handler evidence passed as argument
fun f(h: Handler⟨State⟩) -> ...
```

**Pros:**
- No control flow transformation
- Good performance
- Clear operational semantics

**Cons:**
- Syntactic overhead
- Less flexible than CPS

### 6.3 Segmented Stacks (OCaml 5)

**Approach:** Copy/restore stack segments for continuations.

**Pros:**
- Natural direct style
- Good performance for common cases
- One-shot continuations efficient

**Cons:**
- Multi-shot expensive
- Runtime complexity
- Platform-specific

### 6.4 Strategy Selection for TERAS

| Strategy | Suitability | Rationale |
|----------|-------------|-----------|
| CPS | Medium | Proven but overhead |
| Evidence Passing | High | Good performance, explicit |
| Segmented Stacks | Medium | Requires runtime support |
| **Hybrid** | **Best** | CPS for multi-shot, evidence for common |

---

## 7. Effect System + Linear Types Integration

### 7.1 Approaches

**Separate Concerns (Rust + Effects):**
```rust
// Linearity and effects orthogonal
fn process(handle: FileHandle) -> Result<Data, Error> { ... }
// Linearity: handle consumed
// Effect: may throw Error
```

**Unified (ATS):**
```ats
// Linear views in effectful computation
fn read {l:addr} (pf: !file_v(l)) -> (option string)
```

**Graded (Granule):**
```granule
// Multiplicity + effects combined
read : File [1] -> {IO} String
```

### 7.2 Comparison for TERAS

| Approach | Pros | Cons |
|----------|------|------|
| Separate | Simpler mental model | Less integrated |
| Unified | Maximum expressiveness | Complex types |
| Graded | Elegant theory | Implementation challenge |

**TERAS Recommendation:** Start with separate concerns, evolve toward graded as maturity increases.

---

## 8. Security Effect Patterns

### 8.1 Information Flow Control

**Option A: Dedicated IFC Types (FlowCaml)**
```
// Explicit security labels in types
x : int^{secret}
y : int^{public}
```

**Option B: IFC as Effects (Koka-style)**
```
effect Read<L>  : unit -> data
effect Write<L> : data -> unit
```

**Option C: Refinement-Based (Liquid)**
```
{x:int | level(x) = Secret}
```

| Option | Expressiveness | Ergonomics | Verification |
|--------|---------------|------------|--------------|
| Dedicated | High | Medium | Type-based |
| Effect-based | Medium | High | Handler-based |
| Refinement | High | Medium | SMT-based |

**TERAS Choice:** Combine effect-based (for tracking) with refinement (for properties).

### 8.2 Capability Safety

**Effect-Based Capabilities:**
```teras
effect FileOp : Path -> Data
effect NetOp : Host -> Connection

// Sandbox removes capabilities
sandbox : Eff ⟨FileOp, NetOp | ε⟩ α → Eff ε (Option α)
```

**Linear Capabilities (from A-04):**
```teras
type Capability<R> = lin { cap: Token | authorized(cap) }
use_cap : Capability<R> ⊸ R → (Result, Option<Capability<R>>)
```

**Combined:**
```teras
effect UseCapability<R> : Capability<R> -> (R -> Eff ε α) -> α
```

---

## 9. Performance Considerations

### 9.1 Overhead Sources

| Source | Impact | Mitigation |
|--------|--------|------------|
| Handler dispatch | Medium | Specialization |
| Continuation capture | High | Avoid when possible |
| Effect row checking | Low | Compile-time only |
| Evidence passing | Low | Inlining |

### 9.2 Benchmarks (from Literature)

**Koka vs Haskell mtl:**
- Simple effects: ~comparable
- Complex stacks: Koka ~2x faster
- Multi-shot: Koka significantly faster

**OCaml 5 Effects:**
- One-shot: Near-native performance
- Multi-shot: ~10x overhead

**F* Extraction:**
- Compiles to efficient OCaml/C
- No runtime effect overhead

### 9.3 TERAS Performance Requirements

Law 8 mandates: Performance must exceed hand-written C.

**Strategy:**
1. Compile-time effect checking only (zero runtime cost)
2. Evidence passing for single-shot handlers
3. CPS transformation only when multi-shot needed
4. Aggressive handler specialization

---

## 10. Decision Matrix

### 10.1 Scoring Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| Security Fit | 25% | How well does it support security patterns? |
| Type Integration | 20% | Integration with dependent/linear/refinement |
| Decidability | 15% | Is type/effect inference decidable? |
| Performance | 15% | Can it meet TERAS performance requirements? |
| Ergonomics | 15% | Developer experience and learning curve |
| Implementation | 10% | Feasibility of implementation |

### 10.2 Scores

| Approach | Security | Integration | Decidable | Performance | Ergonomics | Impl | **Total** |
|----------|----------|-------------|-----------|-------------|------------|------|-----------|
| Pure Monads | 6 | 7 | 9 | 8 | 5 | 9 | **6.85** |
| Subtyping Effects | 7 | 6 | 4 | 7 | 7 | 6 | **6.25** |
| Row Effects | 8 | 8 | 9 | 8 | 8 | 7 | **8.05** |
| Algebraic + Handlers | 9 | 7 | 8 | 7 | 8 | 6 | **7.80** |
| F*-style Dependent | 10 | 9 | 7 | 8 | 5 | 5 | **7.80** |
| **Hybrid Row + Handlers** | 9 | 9 | 8 | 8 | 8 | 6 | **8.35** |

### 10.3 Recommendation

**Primary Choice:** Hybrid system combining:
1. **Row-polymorphic effect tracking** (Koka-style) for inference and polymorphism
2. **Algebraic handlers** for flexible effect implementation
3. **Refinement integration** (F*-inspired) for security properties

**Rationale:**
- Row polymorphism ensures decidable inference
- Handlers provide modularity for security patterns
- Refinements enable verified effects
- Combined score: 8.35/10

---

## 11. Integration Recommendations

### 11.1 With A-04 (Linear Types)

**Effect-Linear Integration:**
```teras
// Effect on linear resource
effect Use<R> : (lin R) -> Result

// Handler consumes resource
handle_use : Handler⟨Use⟩ → (lin R) → Eff ε Result
```

### 11.2 With A-03 (Refinement Types)

**Refined Effects:**
```teras
// Effect with refined parameter
effect Read : (path: {p:Path | valid(p)}) -> String

// Effect with refined result
effect Encrypt : Plaintext -> {c:Ciphertext | length(c) = length(p) + 16}
```

### 11.3 With A-01/A-02 (Dependent Types)

**Dependent Effect Indices:**
```teras
// Effect indexed by security level
effect Read<L: Level> : Unit -> Data<L>
effect Write<L: Level> : Data<L> -> Unit
```

---

## 12. Summary

### Key Decisions

1. **Row-polymorphic effects** over subtyping (decidability)
2. **Algebraic handlers** for effect implementation (modularity)
3. **Separate but integrated** with linear types (pragmatism)
4. **Refinement-enriched** effects for security (verification)
5. **Evidence passing** default, CPS when needed (performance)

### TERAS Alignment

| TERAS Principle | Effect System Support |
|-----------------|----------------------|
| Zero dependencies | Custom implementation |
| Formal verification | Decidable type checking |
| Performance | Compile-time effects |
| Security | IFC + capability effects |
| Memory safety | Integrates with linear |

---

## Document Metadata

**Research Track:** A (Theoretical Foundations)
**Session:** A-05
**Document Type:** Comparative Analysis
**Preceding Document:** RESEARCH_A05_EFFECT_SYSTEMS_SURVEY.md
**Following Document:** RESEARCH_A05_EFFECT_SYSTEMS_DECISION.md

---

*This comparison establishes row-polymorphic algebraic effects with handlers as the foundation for TERAS-LANG's effect system.*
