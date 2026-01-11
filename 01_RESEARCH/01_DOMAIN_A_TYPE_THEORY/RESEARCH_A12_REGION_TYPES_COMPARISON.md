# RESEARCH_A12_REGION_TYPES_COMPARISON.md

## TERAS Research Track — Domain A: Type Theory
### Session A-12: Region Types — Comparative Analysis

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research

---

# PART I: SYSTEM COMPARISON MATRIX

## 1.1 Feature Matrix

| Feature | MLKit | Cyclone | RTSJ | Vault | Rust | Linear Regions |
|---------|-------|---------|------|-------|------|----------------|
| **Static Safety** | ✓ Full | ✓ Full | ✗ Runtime | ✓ Full | ✓ Full | ✓ Full |
| **Region Inference** | ✓ Full | ✗ Manual | ✗ None | Partial | Partial | ✓ Full |
| **Effect Tracking** | ✓ | Partial | ✗ | ✓ | ✗ | ✓ |
| **Region Polymorphism** | ✓ | ✓ | ✗ | ✓ | ✓ | ✓ |
| **Unique Pointers** | ✗ | ✓ | ✗ | ✓ | ✓ | ✓ |
| **Adoption/Focus** | ✗ | ✗ | ✗ | ✓ | ✗ | ✗ |
| **GC Integration** | ✓ | ✗ | ✓ | ✗ | ✗ | ✗ |
| **Bounds Checking** | Separate | ✓ | Runtime | ✓ | ✓ | Separate |
| **C Compatibility** | ✗ | ✓ High | N/A | ✓ | Via FFI | ✗ |
| **Production Use** | ✓ | ✗ Ended | ✓ | ✗ Research | ✓ | ✗ Research |

## 1.2 Safety Guarantees

| Property | MLKit | Cyclone | RTSJ | Vault | Rust |
|----------|-------|---------|------|-------|------|
| No dangling pointers | Static | Static | Runtime | Static | Static |
| No double free | By design | By design | Runtime | Static | Static |
| No memory leaks | Partial* | Partial* | Runtime | Partial* | Partial* |
| No buffer overflow | Separate | Static | Runtime | Static | Static |
| No use-after-free | Static | Static | Runtime | Static | Static |
| No data races | N/A | ✗ | Runtime | Static | Static |

*Partial: Can still have logical leaks if regions too long-lived

## 1.3 Expressiveness Comparison

```
Expressiveness vs. Ease of Use:

                  EASE OF USE
                      ^
                      |
           MLKit *    |
    (full inference)  |
                      |    * Rust (partial inference,
                      |      familiar ownership)
                      |
                      |           * Cyclone
                      |             (manual, C-like)
                      |
                      |                 * Vault
                      |                   (adoption, focus)
    ──────────────────┼────────────────────────────────> EXPRESSIVENESS
                      |
                      |
                      
MLKit: Simple model, full inference, limited expressiveness
Cyclone: Rich features, manual annotations, C compatible
Rust: Ownership subsumes regions, practical balance
Vault: Most expressive (adoption), research complexity
```

---

# PART II: DETAILED COMPARISONS

## 2.1 MLKit vs Cyclone

### 2.1.1 Design Philosophy

| Aspect | MLKit | Cyclone |
|--------|-------|---------|
| Base Language | Standard ML | C dialect |
| Primary Goal | Safe FP | Safe systems |
| Annotation Burden | None (inferred) | High (manual) |
| Target Users | ML programmers | C programmers |
| Memory Model | GC + regions | Regions only |

### 2.1.2 Technical Differences

```
MLKit Approach:
  - Region inference from types
  - Polymorphism everywhere
  - Storage mode optimization
  - Effect masking at boundaries
  
  Strengths:
    + No manual annotations
    + Proven type safety
    + Efficient for FP patterns
    
  Weaknesses:
    - Sometimes inefficient inference
    - Regions can be too coarse
    - No fine-grained control

Cyclone Approach:
  - Explicit region annotations
  - Multiple pointer kinds
  - Existential types for abstraction
  - Runtime checks where needed
  
  Strengths:
    + C compatibility
    + Fine-grained control
    + Rich pointer taxonomy
    
  Weaknesses:
    - High annotation burden
    - Learning curve
    - Project discontinued
```

### 2.1.3 Code Comparison

```ml
(* MLKit: Region-polymorphic map *)
fun map f [] = []
  | map f (x::xs) = f x :: map f xs

(* Inferred type:
   ∀α,β,ρ₁,ρ₂,ε.
   (α →^ε β) → list(α,ρ₁) →^{ε,put(ρ₂)} list(β,ρ₂)
*)
```

```c
// Cyclone: Explicit region annotations
struct List<`a,`r::R> {
    `a hd;
    struct List<`a,`r> *`r tl;
};

struct List<`b,`r2> *`r2 
map<`a,`b,`r1,`r2>(
    `b (*f)(`a), 
    struct List<`a,`r1> *`r1 lst,
    region_t<`r2> rgn
) {
    if (lst == NULL) return NULL;
    return rnew(rgn) List{f(lst->hd), map(f, lst->tl, rgn)};
}
```

## 2.2 Cyclone vs Rust

### 2.2.1 Lifetime vs Region

| Concept | Cyclone | Rust |
|---------|---------|------|
| Stack regions | `foo scope | `'a` lifetime |
| Heap region | `H | `'static` |
| Unique pointer | `*`U | `Box<T>` |
| Region param | `<`r>` | `<'a>` |
| Outlives | Implicit | `'a: 'b` |

### 2.2.2 Feature Evolution

```
Cyclone → Rust Evolution:

Cyclone Feature         Rust Equivalent
─────────────────────   ─────────────────────
`*`r ptr               &'a T
`*`U unique            Box<T>
`*@fat arr             &[T] / Vec<T>
region r { }           { } scope
existential `r         impl Trait
NULL checks            Option<T>

Key Differences:
- Rust: Ownership replaces explicit regions
- Rust: Borrowing is the primary mechanism
- Rust: No runtime region handles needed
- Rust: More ergonomic syntax
```

### 2.2.3 Safety Comparison

```rust
// Rust: Ownership + borrowing achieves region safety
fn process<'a>(data: &'a [u8]) -> &'a u8 {
    &data[0]  // Lifetime tied to input
}

// Cannot return dangling reference
fn bad<'a>() -> &'a u8 {
    let x = 42u8;
    &x  // ERROR: x does not live long enough
}
```

```c
// Cyclone: Explicit region ensures same safety
int *`r process<`r>(int *`r @fat data, region_t<`r> r) {
    return &data[0];  // In region r
}

// Cannot return pointer to dead region
int *`r bad<`r>() {
    region local {
        int x = 42;
        return &x;  // ERROR: would escape local region
    }
}
```

## 2.3 MLKit vs Rust Lifetimes

### 2.3.1 Inference Comparison

| Aspect | MLKit | Rust |
|--------|-------|------|
| Full inference | Yes | No |
| Annotation need | Never | Sometimes |
| Polymorphism | Implicit | Explicit |
| Effect tracking | Yes | Via borrow checker |

### 2.3.2 Expressiveness

```
MLKit Inference:
  All region annotations inferred
  Effect polymorphism automatic
  But: Less control when needed

Rust Lifetime Elision:
  Common patterns inferred:
    fn f(&self) -> &T       // self lifetime propagated
    fn f(&T) -> &T          // input-output same lifetime
    fn f(&T, &U) -> V       // no inference for output
  
  Manual for complex cases:
    fn f<'a, 'b>(&'a T, &'b U) -> &'a V where 'b: 'a
```

## 2.4 RTSJ vs Static Systems

### 2.4.1 Static vs Dynamic Trade-offs

| Aspect | Static (MLKit/Cyclone) | Dynamic (RTSJ) |
|--------|------------------------|----------------|
| Safety checking | Compile time | Runtime |
| Performance overhead | None at runtime | Runtime checks |
| Flexibility | Less | More |
| Error detection | Early (compile) | Late (runtime) |
| Certification | Easier | Harder |

### 2.4.2 Real-Time Suitability

```
Real-Time Requirements:

RTSJ Approach:
  + Designed for real-time
  + Explicit control over allocation
  + No GC pauses in scoped memory
  - Runtime check overhead
  - Potential runtime errors

Static Approach (MLKit/Cyclone):
  + Zero runtime overhead
  + Errors caught at compile time
  + Easier to certify
  - Less flexible
  - May require program restructuring
```

---

# PART III: INTEGRATION ANALYSIS

## 3.1 Integration with Linear Types

### 3.1.1 Comparison

| System | Linear Integration | Approach |
|--------|-------------------|----------|
| MLKit | No built-in | Can encode |
| Cyclone | Unique pointers | Special kind |
| Rust | Ownership | Move semantics |
| Linear Regions | Native | Capabilities |

### 3.1.2 Synergy Analysis

```
Linear Types + Regions:

Option 1: Orthogonal (MLKit style)
  Regions: lexical scoping
  Linear: separate dimension
  Interaction: lin (τ at ρ)

Option 2: Unified (Fluet-Morrisett)
  Capabilities are linear
  Region access requires capability
  Deallocation consumes capability

Option 3: Ownership Subsumes (Rust)
  Ownership provides linearity
  Lifetimes provide region-like scoping
  Borrow checker enforces both

For TERAS-LANG: Option 1 (orthogonal) recommended
  - Cleaner semantics
  - Separate concerns
  - Proven sound
```

## 3.2 Integration with Effects

### 3.2.1 Effect Systems Comparison

| System | Effect Tracking | Granularity |
|--------|-----------------|-------------|
| MLKit | get(ρ), put(ρ) | Per region |
| Cyclone | Implicit | Per access |
| Rust | None explicit | Via borrow rules |
| TERAS (proposed) | Read<ρ>, Write<ρ>, Alloc<ρ> | Per region |

### 3.2.2 Recommended Effect Design

```
TERAS Region Effects:

Read<ρ>   -- read from region ρ
Write<ρ>  -- write to region ρ
Alloc<ρ>  -- allocate in region ρ
Free<ρ>   -- deallocate region ρ

Effect composition:
  fn f(x: &τ at ρ) -> τ' ! {Read<ρ>}
  fn g(x: &mut τ at ρ) -> () ! {Write<ρ>}
  fn h() -> τ at ρ ! {Alloc<ρ>}

Effect masking at region boundary:
  letregion ρ in e end : τ ! ε \ {Read<ρ>, Write<ρ>, Alloc<ρ>}
```

## 3.3 Integration with Security Types

### 3.3.1 Security Region Attributes

```
Combining Regions + Security:

Security Attributes:
  letregion ρ [secret] in ...     -- secret data region
  letregion ρ [tainted] in ...    -- untrusted data region
  letregion ρ [ct] in ...         -- constant-time region

Type Integration:
  Secret<τ> at ρ[secret]          -- secret in secret region
  Tainted<τ> at ρ[tainted]        -- tainted in tainted region

Interaction Rules:
  Cannot flow: ρ[secret] → ρ[public]
  Must sanitize: ρ[tainted] → ρ[clean]
  Constant-time: ρ[ct] requires CT operations
```

---

# PART IV: PERFORMANCE ANALYSIS

## 4.1 Allocation Performance

| System | Allocation | Deallocation | Fragmentation |
|--------|------------|--------------|---------------|
| MLKit ATTOP | O(1) bump | O(1) pop | None |
| MLKit ATBOT | O(1) bump | O(pages) | Per-region |
| Cyclone | O(1) bump | O(pages) | Per-region |
| RTSJ | O(1) bump | O(1) reset | None |
| Rust Stack | O(1) | O(1) | None |
| Rust Heap | O(log n) | O(log n) | Global |

## 4.2 Space Overhead

```
Memory Overhead Analysis:

MLKit:
  - Region header: ~24 bytes per region
  - Page overhead: ~16 bytes per page
  - No per-object overhead
  
Cyclone:
  - Region descriptor: ~32 bytes
  - Fat pointer: 2× pointer size
  - Tagged unions: 1 word tag
  
Rust:
  - No region overhead (static)
  - slice: 2× pointer (ptr + len)
  - Box: pointer only
  
RTSJ:
  - MemoryArea object: ~64 bytes
  - Runtime reference checks
  - Per-object reference tracking
```

## 4.3 Inference Complexity

| System | Type Inference | Region Inference | Overall |
|--------|----------------|------------------|---------|
| MLKit | O(n) HM | O(n²) worst | O(n²) |
| Cyclone | None | Manual | O(n) checking |
| Rust | O(n) | Local | O(n) |

---

# PART V: EVALUATION CRITERIA FOR TERAS-LANG

## 5.1 Criteria Weights

| Criterion | Weight | Rationale |
|-----------|--------|-----------|
| Safety Guarantees | 25% | Core TERAS requirement |
| Performance | 20% | D38 mandate |
| Inference Quality | 15% | Usability |
| Linear Integration | 15% | A-04 compatibility |
| Security Integration | 15% | IFC requirements |
| Simplicity | 10% | Learnability |

## 5.2 Scored Comparison

| System | Safety | Perf | Infer | Linear | Security | Simple | **Total** |
|--------|--------|------|-------|--------|----------|--------|-----------|
| MLKit | 23/25 | 18/20 | 15/15 | 10/15 | 8/15 | 8/10 | **82/100** |
| Cyclone | 25/25 | 16/20 | 5/15 | 13/15 | 10/15 | 5/10 | **74/100** |
| Rust | 25/25 | 20/20 | 12/15 | 15/15 | 8/15 | 7/10 | **87/100** |
| Linear Regions | 25/25 | 18/20 | 14/15 | 15/15 | 12/15 | 6/10 | **90/100** |
| RTSJ | 15/25 | 14/20 | 0/15 | 5/15 | 5/15 | 6/10 | **45/100** |

## 5.3 Recommendation Justification

```
Linear Regions scores highest because:
  + Full static safety (25/25)
  + Good performance via bump allocation (18/20)
  + Full inference like MLKit (14/15)
  + Native linear type integration (15/15)
  + Natural security region support (12/15)
  - Somewhat complex model (6/10)

Rust is close second (87/100):
  + Proven in practice
  + Excellent performance
  + Good tooling
  - Security integration needs extension
  - Not designed for region effects

MLKit provides inference model (82/100):
  + Best inference algorithm
  + Proven sound
  - Limited linear integration
  - Weak security features

For TERAS-LANG: Combine Linear Regions theory
                with MLKit inference approach
                and Rust ergonomics
```

---

# PART VI: SUMMARY

## 6.1 Key Findings

1. **Static safety is mandatory** — Runtime approaches (RTSJ) rejected for TERAS
2. **Inference is valuable** — MLKit approach reduces annotation burden
3. **Linear integration critical** — Fluet-Morrisett capability model ideal
4. **Security features needed** — Region attributes for confidentiality
5. **Rust validates approach** — Ownership/lifetimes prove practical viability

## 6.2 Design Direction

```
TERAS-LANG Region Design:

Theoretical Foundation: Linear Regions (Fluet-Morrisett)
Inference Algorithm: MLKit-style (Tofte-Birkedal)
Surface Syntax: Rust-inspired ergonomics
Security Extension: Attributed regions

Type: lin τ at ρ[attrs]
Effect: Read<ρ>, Write<ρ>, Alloc<ρ>
Inference: Full region inference
Safety: Compile-time only
```

---

**END OF COMPARISON DOCUMENT**

**Next Document:** RESEARCH_A12_REGION_TYPES_DECISION.md
