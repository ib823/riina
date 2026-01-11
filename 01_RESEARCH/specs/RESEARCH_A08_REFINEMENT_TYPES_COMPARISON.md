# RESEARCH_A08_REFINEMENT_TYPES_COMPARISON.md
## TERAS-LANG Research Track A - Session 08
## Comparative Analysis: Refinement Type Systems

**Document Version**: 1.0.0
**Created**: 2026-01-03
**Purpose**: Compare refinement type approaches for TERAS-LANG design decisions

---

## 1. SYSTEM COMPARISON MATRIX

### 1.1 Core Features

| Feature | Liquid Haskell | F* | DML | Flux | Stardust |
|---------|---------------|-----|-----|------|----------|
| Base Language | Haskell | F*/OCaml | SML | Rust | SML |
| Refinement Logic | First-order + measures | Dependent | Linear arithmetic | First-order | Restricted |
| SMT Backend | Z3 | Z3 | None (LP) | Z3 | None |
| Automation Level | High | Medium | High | High | High |
| Effect Tracking | Partial | Full monadic | None | Ownership | None |
| Extraction | Native Haskell | C, OCaml, F#, JS | Native SML | Native Rust | â€” |

### 1.2 Type System Power

| Capability | Liquid Haskell | F* | DML | Flux |
|------------|---------------|-----|-----|------|
| Predicate subtypes | âœ“ | âœ“ | âœ“ (index) | âœ“ |
| Dependent functions | âœ“ | âœ“ | âœ“ | âœ“ |
| Abstract refinements | âœ“ | âœ“ | â€” | âœ“ |
| Measures | âœ“ | âœ“ | Built-in | âœ“ |
| Refinement reflection | âœ“ | â€” | â€” | â€” |
| Higher-order refinements | Limited | âœ“ | â€” | Limited |
| Existential refinements | âœ“ | âœ“ | â€” | âœ“ |

### 1.3 Decidability and Automation

| Aspect | Liquid Haskell | F* | DML | Flux |
|--------|---------------|-----|-----|------|
| Type inference | Liquid inference | Bidirectional | Full | Liquid inference |
| Constraint solving | SMT | SMT + tactics | ILP | SMT |
| Loop invariants | Inferred | Manual/auto | Manual | Inferred |
| Termination | Checked (optional) | Checked | Assumed | Rust guarantees |
| Decidability | Decidable (restricted) | Semi-decidable | Decidable | Decidable |

---

## 2. REFINEMENT LOGIC COMPARISON

### 2.1 Liquid Types (Liquid Haskell, Flux)

**Core Principle**: Restrict refinements to conjunctions of logical qualifiers

```
Îº ::= qâ‚ âˆ§ qâ‚‚ âˆ§ ... âˆ§ qâ‚™   where qáµ¢ âˆˆ Q*
```

**Qualifiers Q***:
- Provided by user or derived from program syntax
- Typically include: `v > 0`, `v < x`, `len v = n`, etc.
- Finite set ensures decidable inference

**Pros**:
- Fully automatic inference via fixed-point
- Decidable type checking
- Minimal annotation burden

**Cons**:
- Limited to qualifier vocabulary
- May miss properties outside Q*
- Quantified properties challenging

### 2.2 Index Refinements (DML)

**Core Principle**: Separate index domain from value domain

```
type List(n:int) = ...
val append : {m,n:int} List(m) -> List(n) -> List(m+n)
```

**Index Domain**:
- Linear arithmetic over integers
- Constraint satisfaction via integer linear programming
- Decidable and efficient

**Pros**:
- Very efficient constraint solving
- Clean phase separation
- No SMT dependency

**Cons**:
- Limited to linear arithmetic
- No general predicates
- Index language is separate syntax

### 2.3 Full Dependent Types (F*)

**Core Principle**: Refinements in full dependent type theory

```fstar
val sort : l:list int -> l':list int{sorted l' âˆ§ permutation l l'}
```

**Logic**:
- Full first-order logic with dependent types
- SMT for decidable fragments
- Manual tactics for complex proofs

**Pros**:
- Maximum expressiveness
- Can encode any property
- Theorem proving when needed

**Cons**:
- Type checking semi-decidable
- May require manual proofs
- Steeper learning curve

---

## 3. EFFECT HANDLING COMPARISON

### 3.1 Liquid Haskell (Lazy Effects)

**Challenge**: Lazy evaluation breaks standard refinement soundness

**Solution**: Stratified types
```haskell
Ï„â‡“  -- Terminating values (refinements hold)
Ï„â†“  -- May diverge (refinements conditional)
Ï„   -- Arbitrary (no refinement guarantees)
```

**Termination Checking**:
- Optional but recommended
- Well-founded metrics on recursive calls
- 96% of functions verified terminating

### 3.2 F* (Monadic Effects)

**Challenge**: Track effects precisely for verification

**Solution**: Effect system with monads
```fstar
Tot a      -- Total, always terminates
Pure a     -- Pure but may diverge
ST a       -- Stateful with heap
ML a       -- Full ML effects
```

**Key Insight**: Effects are indexed by pre/postconditions
```fstar
ST (requires P) (ensures Q)
```

### 3.3 Flux (Ownership Effects)

**Challenge**: Verify imperative Rust code

**Solution**: Leverage Rust ownership for effect handling
```rust
#[spec(fn(x: &mut i32[@n]) ensures x: &mut i32[@n+1])]
fn incr(x: &mut i32) { *x += 1 }
```

**Key Insight**: 
- Ownership handles aliasing
- Refinements handle functional properties
- Strong references enable strong updates

---

## 4. VERIFICATION WORKFLOW COMPARISON

### 4.1 Liquid Haskell Workflow

```
1. Write Haskell code
2. Add {-@ ... @-} annotations
3. Run liquid checker
4. SMT solver checks VCs
5. Fix errors or add qualifiers
6. Native Haskell execution
```

**Iteration Cycle**: Fast (seconds to minutes)
**Annotation Burden**: Low (~10-20% of code lines)

### 4.2 F* Workflow

```
1. Write F* code with specs
2. Type check (generates VCs)
3. Z3 attempts automatic proof
4. Add tactics/lemmas if needed
5. Extract to target language
6. Compile and execute
```

**Iteration Cycle**: Medium (minutes)
**Annotation Burden**: Medium (~20-40% for complex code)

### 4.3 Flux Workflow

```
1. Write Rust code
2. Add #[spec(...)] attributes
3. Run flux checker (rustc plugin)
4. SMT solver verifies
5. Native Rust compilation
```

**Iteration Cycle**: Fast (integrates with cargo)
**Annotation Burden**: Low (~10-15% based on benchmarks)

---

## 5. REAL-WORLD DEPLOYMENT

### 5.1 Liquid Haskell Applications

**Verified Libraries**:
- containers (Data.Map, Data.Set)
- bytestring
- text
- vector-algorithms
- xmonad

**Scale**: 10,000+ lines verified
**Integration**: GHC plugin, IDE support

### 5.2 F* Applications

**Major Projects**:
- HACL*: Verified cryptographic library (deployed in Firefox, Linux)
- miTLS: Verified TLS implementation
- EverCrypt: Cross-platform crypto provider
- Vale: Verified assembly language

**Scale**: 100,000+ lines
**Integration**: Compiler to C/OCaml/F#/JS

### 5.3 Flux Applications

**Verified Systems**:
- Tock OS process isolation
- WaVe WebAssembly sandbox
- Various vector-manipulating programs

**Scale**: Growing (thousands of lines)
**Integration**: Rustc plugin, cargo integration

---

## 6. SECURITY PROPERTIES

### 6.1 Memory Safety

| System | Array Bounds | Buffer Overflow | Use-After-Free |
|--------|-------------|-----------------|----------------|
| Liquid Haskell | âœ“ (via length) | N/A (GC) | N/A (GC) |
| F*/Low* | âœ“ (via preconditions) | âœ“ | âœ“ |
| DML | âœ“ (via indexes) | N/A | N/A |
| Flux | âœ“ (via ownership + refinement) | âœ“ (Rust) | âœ“ (Rust) |

### 6.2 Information Flow

| System | Label Tracking | Non-Interference | Declassification |
|--------|---------------|------------------|------------------|
| Liquid Haskell | Encodable | Encodable | Manual |
| F* | âœ“ (native) | âœ“ | âœ“ |
| DML | â€” | â€” | â€” |
| Flux | Encodable | Limited | â€” |

### 6.3 Side-Channel Resistance

| System | Timing Independence | Secret Independence |
|--------|-------------------|---------------------|
| Liquid Haskell | â€” | â€” |
| F*/HACL* | âœ“ | âœ“ (via secure integers) |
| DML | â€” | â€” |
| Flux | â€” | â€” |

---

## 7. PERFORMANCE CHARACTERISTICS

### 7.1 Verification Time

| System | Small (<1K LOC) | Medium (1-10K) | Large (>10K) |
|--------|----------------|----------------|--------------|
| Liquid Haskell | Seconds | Minutes | Minutes-Hours |
| F* | Seconds-Minutes | Minutes-Hours | Hours |
| DML | Seconds | Seconds | Minutes |
| Flux | Seconds | Seconds-Minutes | Minutes |

### 7.2 Runtime Overhead

All systems compile to native code with no runtime overhead for verified properties:
- Liquid Haskell â†’ Native Haskell (GHC)
- F* â†’ C/OCaml (native performance)
- DML â†’ Native SML
- Flux â†’ Native Rust

---

## 8. TERAS-LANG APPLICABILITY ANALYSIS

### 8.1 Alignment with TERAS Goals

| Goal | Liquid Haskell | F* | DML | Flux |
|------|---------------|-----|-----|------|
| Formal Verification | High | Very High | Medium | High |
| Zero Runtime Overhead | âœ“ | âœ“ | âœ“ | âœ“ |
| Security Properties | Medium | Very High | Low | High |
| Decidable Checking | âœ“ | Partial | âœ“ | âœ“ |
| Low-Level Control | â€” | High (Low*) | â€” | High |
| Effect Tracking | Partial | âœ“ | â€” | Via ownership |

### 8.2 Integration with TERAS Type System

**Linear Types (A-04)**:
- F*: Explicit effect tracking complements linearity
- Flux: Ownership = linearity, refinements = properties
- Liquid Haskell: Would need extension

**Session Types (A-07)**:
- F*: Full dependent types can encode session types with refinements
- Liquid Haskell: Abstract refinements could encode protocols
- Flux: Linear endpoints natural, refinements on messages

**Uniqueness Types (A-06)**:
- Flux: Natural fit (Rust ownership)
- F*: Encodable via effects
- Liquid Haskell: Limited support

### 8.3 Recommended Approach for TERAS

**Primary Inspiration**: Flux/Liquid Types approach
- Automatic inference via predicate abstraction
- SMT backend (Z3) for verification
- Integration with linear/ownership types

**Secondary Inspiration**: F* features
- Effect-aware refinements
- Extraction to verified C
- Security-oriented type system

**Hybrid Design**:
```teras
// Liquid-style refinements
type Nat = {v: Int | v >= 0}

// Effect-aware refinements (F*-style)
fn read_file(path: Path) -> IO<{data: Bytes | len(data) <= MAX_SIZE}>

// Ownership + refinements (Flux-style)
fn process(buf: lin &mut [u8; @n]) -> lin &mut [u8; @n]
```

---

## 9. COMPARISON SUMMARY

### 9.1 Best For Each Use Case

| Use Case | Recommended System | Reason |
|----------|-------------------|--------|
| Functional correctness | Liquid Haskell | High automation, mature |
| Cryptographic verification | F*/HACL* | Security properties, C extraction |
| Systems programming | Flux | Rust integration, ownership |
| Array bounds | DML or Liquid | Efficient, decidable |
| Protocol verification | F* | Full dependent types |
| Low annotation burden | Liquid/Flux | Automatic inference |

### 9.2 Key Trade-offs

| Trade-off | Liquid Style | F* Style |
|-----------|-------------|----------|
| Automation vs Power | Higher automation | Higher power |
| Decidability vs Expressiveness | Decidable | Semi-decidable |
| Learning Curve | Lower | Higher |
| Annotation Burden | Lower | Higher |
| Proof Control | Less | More |

---

## 10. CONCLUSION

For TERAS-LANG, a hybrid approach combining:

1. **Liquid Types inference** for automatic refinement discovery
2. **SMT-decidable refinement logic** for practical verification
3. **Integration with linear types** leveraging ownership for aliasing
4. **Effect-aware refinements** for tracking computational effects
5. **Security-oriented predicates** for TERAS product requirements

This provides the best balance of automation, expressiveness, and security guarantees aligned with TERAS's formal verification mandate.

---

*Document generated as part of TERAS-LANG Research Track A*
*Session A-08: Refinement Types Comparison*
