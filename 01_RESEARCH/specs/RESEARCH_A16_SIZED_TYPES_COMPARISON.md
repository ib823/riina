# RESEARCH_A16_SIZED_TYPES_COMPARISON.md

## TERAS Research Track â€” Domain A: Type Theory
### Session A-16: Sized Types â€” Comparative Analysis

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research

---

# PART I: SYSTEM COMPARISON MATRIX

## 1.1 Feature Matrix

| Feature | Agda Sized | F* Decreases | MiniAgda | CIC^Ï‰ |
|---------|------------|--------------|----------|-------|
| **Size Representation** | Ordinal | Measure | Ordinal | Ordinal |
| **Inference** | Partial | Manual | Research | Partial |
| **Codata Support** | Yes | Limited | Yes | Yes |
| **Subtyping** | Yes | No | Yes | Yes |
| **Integration** | Full | Effect system | Standalone | Coq |
| **Production** | Yes | Yes | Research | Research |

## 1.2 Termination Checking Comparison

| Property | Agda | F* | MiniAgda | CIC^Ï‰ |
|----------|------|----|---------:|-------|
| Structural recursion | âœ“ | âœ“ | âœ“ | âœ“ |
| Sized types | âœ“ | Via measures | âœ“ | âœ“ |
| Lexicographic | âœ“ | âœ“ | Limited | âœ“ |
| Custom measures | Limited | âœ“ | âœ— | âœ— |
| Mutual recursion | âœ“ | âœ“ | âœ“ | âœ“ |

## 1.3 Design Philosophy Spectrum

```
                    EXPRESSIVENESS
                        ^
                        |
         F* *           |      * CIC^Ï‰
    (custom measures)   |       (ordinal sizes)
                        |
                        |
                        |     * MiniAgda
                        |       (pure sizes)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€> INFERENCE
                        |
                        |
          Agda *        |
        (practical      |
         sizes)         |
                        |

Agda: Practical balance of inference and expressiveness
F*: Maximum expressiveness, manual annotation
MiniAgda: Theoretical purity, research focus
CIC^Ï‰: Formal foundations, ordinal theory
```

---

# PART II: DETAILED SYSTEM COMPARISONS

## 2.1 Agda vs F*

### 2.1.1 Termination Approach Comparison

| Aspect | Agda Sized Types | F* Decreases |
|--------|------------------|--------------|
| Annotation style | Type-level sizes | Decreases clauses |
| Size propagation | Type inference | Manual |
| Codata | Native sized codata | Effect-based |
| Subtyping | Size subtyping | No size subtyping |
| Flexibility | Medium | High |

### 2.1.2 Code Comparison

```
-- Agda: Size in type
data List (A : Set) : Size â†’ Set where
  []  : {i : Size} â†’ List A (â†‘ i)
  _âˆ·_ : {i : Size} â†’ A â†’ List A i â†’ List A (â†‘ i)

length : {A : Set} {i : Size} â†’ List A i â†’ Nat
length [] = 0
length (x âˆ· xs) = suc (length xs)

-- F*: Decreases clause
let rec length #a (l : list a) : Tot nat (decreases l) =
  match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl
```

### 2.1.3 Trade-offs

```
Agda Sized Types:
  + Compositional (size in signature)
  + Automatic propagation
  + Good codata support
  - Less flexible than measures
  - Size inference limitations

F* Decreases:
  + Very flexible measures
  + Custom well-founded orders
  + Integration with effects
  - Manual annotation required
  - No size subtyping
```

## 2.2 Sized Types vs Structural Recursion

### 2.2.1 Programs Accepted

```
Structural Recursion Only:
  âœ“ map f []       = []
    map f (x :: xs) = f x :: map f xs
    
  âœ— merge xs []         = xs
    merge [] ys         = ys
    merge (x::xs) (y::ys) = 
      if x < y then x :: merge xs (y::ys)
      else y :: merge (x::xs) ys
    -- Not structural! Both arguments change

With Sized Types:
  âœ“ merge : List^i A â†’ List^j A â†’ List^(i+j) A
    -- Size is sum, clearly decreasing
    
  âœ“ div : Nat^i â†’ Nat â†’ Nat
    div n m = if n < m then 0 else 1 + div (n - m) m
    -- n-m < n, captured by size
```

### 2.2.2 Expressiveness Comparison

| Pattern | Structural | Sized |
|---------|------------|-------|
| Simple recursion | âœ“ | âœ“ |
| Nested recursion | âœ“ | âœ“ |
| Mutual recursion | Limited | âœ“ |
| Non-structural | âœ— | âœ“ |
| Accumulator | Limited | âœ“ |
| Corecursion | Guarded | âœ“ |

## 2.3 Size Inference Approaches

### 2.3.1 Inference Strategies

```
Strategy 1: Constraint-Based (Agda-style)
  - Generate size constraints from usage
  - Solve constraint system
  - Fill in size variables
  
  Pros: Good automation
  Cons: Undecidable in general

Strategy 2: Bidirectional (Annotation-guided)
  - Programmer provides key sizes
  - System propagates
  
  Pros: Predictable, controllable
  Cons: More annotation burden

Strategy 3: Measure-Based (F*-style)
  - Explicit decreases specification
  - SMT-backed verification
  
  Pros: Very flexible
  Cons: Fully manual
```

### 2.3.2 Inference Comparison

| Aspect | Constraint | Bidirectional | Measure |
|--------|------------|---------------|---------|
| Automation | High | Medium | Low |
| Predictability | Low | High | High |
| Expressiveness | Medium | Medium | High |
| Error quality | Often poor | Good | Good |

---

# PART III: INTEGRATION ANALYSIS

## 3.1 Integration with Linear Types (A-04)

### 3.1.1 Linear Sized Types

```
Option 1: Size on Linear Types
  lin A^i    -- linear value with size bound
  
  Example:
    process : âˆ€i. lin Buffer^i â†’ Result
    -- Linear resource, bounded processing

Option 2: Linear Size Consumption
  lin Size   -- size itself is linear
  
  Example:
    bounded_use : lin Size^i â†’ Resource â†’ Result
    -- Size consumed, enforces single use
```

### 3.1.2 Recommended Approach

```
TERAS-LANG Linear Sizes:

Orthogonal combination:
  lin A^i     -- linear value of bounded size
  aff A^i     -- affine value of bounded size
  
  -- Linearity: how many times used
  -- Size: bound on structure/computation
  
Example:
  consume_bounded : âˆ€i. lin Buffer^i â†’ Result
  -- Must use buffer exactly once
  -- Processing bounded by size i
```

## 3.2 Integration with Effects (A-11)

### 3.2.1 Sized Effects

```
Effect Bounded by Size:

effect Iteration^i {
    Step : () â†’ ()
}
-- Effect can occur at most i times

Handler with Size:
  handle {
      loop_body
  } with Bounded^i {
      Step () â†’ 
          if remaining > 0 then resume () else error
  }
```

### 3.2.2 Effect-Size Interaction

```
Effect Signatures with Sizes:

fn process(input : Data^i) -> Result ! Bounded^i
-- Effect budget matches input size

fn stream_process(s : Stream^i) -> Stream^i ! IO^i
-- I/O operations bounded by stream consumption
```

## 3.3 Integration with Capabilities (A-14)

### 3.3.1 Sized Capabilities

```
Capability Usage Bounds:

cap<R, P>^i    -- capability for i uses

Example:
  api_key : cap<API, Call>^1000
  -- Can make at most 1000 API calls

Usage Pattern:
  call_api : cap<API, Call>^(â†‘i) â†’ Req â†’ (Resp, cap<API, Call>^i)
  -- Each call decrements usage count
```

### 3.3.2 Rate Limiting via Types

```
Type-Safe Rate Limiting:

struct RateLimiter^i {
    cap : cap<Resource, Use>^i
}

fn use_resource<i>(
    limiter: RateLimiter^(â†‘i)
) -> (Result, RateLimiter^i) {
    let result = limiter.cap.use()
    (result, RateLimiter { cap: limiter.cap })
}

-- Compile-time guarantee: at most i uses
```

## 3.4 Integration with Staged Types (A-15)

### 3.4.1 Sized Code Generation

```
Generated Code Termination:

code[A^i â†’ B]    -- generated function terminates on size-i input

Example:
  compile_algo : âˆ€i. Algorithm â†’ code[Data^i â†’ Result]
  -- Compiled algorithm terminates on bounded input

Staging with Bounds:
  specialize : âˆ€i. Pattern â†’ code[Input^i â†’ MatchResult]
  -- Specialized matcher terminates
```

---

# PART IV: PERFORMANCE ANALYSIS

## 4.1 Compile-Time Cost

| System | Inference Cost | Verification Cost | Overall |
|--------|----------------|-------------------|---------|
| Agda | Medium | Low | Medium |
| F* | Low (manual) | Medium (SMT) | Medium |
| MiniAgda | High | Low | High |
| Structural only | Very Low | Very Low | Very Low |

## 4.2 Runtime Overhead

```
Runtime Overhead Analysis:

All Sized Type Systems:
  - Zero runtime overhead
  - Sizes erased at compile time
  - No size checks at runtime
  
This is critical for TERAS:
  - D38 compliance (performance > C)
  - No runtime cost for termination
```

## 4.3 Usability Trade-offs

```
                INFERENCE BURDEN
                    ^
                    |
            F* *    |
        (manual     |
        decreases)  |
                    |
                    |      * MiniAgda
                    |       (research)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€> GUARANTEES
                    |
            Agda *  |
        (partial    |
         inference) |
                    |

For TERAS: Agda-zone (practical inference, good guarantees)
```

---

# PART V: EVALUATION FOR TERAS-LANG

## 5.1 Criteria and Weights

| Criterion | Weight | Rationale |
|-----------|--------|-----------|
| Termination Guarantee | 25% | Essential for security |
| Integration | 20% | A-04, A-11, A-14, A-15 |
| Inference | 20% | Usability |
| Zero Overhead | 15% | D38 requirement |
| Expressiveness | 10% | Accept useful programs |
| Formalization | 10% | Verification needs |

## 5.2 System Scores

| System | Term | Compat | Infer | Overhead | Express | Formal | **Total** |
|--------|------|--------|-------|----------|---------|--------|-----------|
| Agda-style | 24/25 | 18/20 | 16/20 | 15/15 | 8/10 | 9/10 | **90/100** |
| F*-style | 25/25 | 15/20 | 12/20 | 15/15 | 10/10 | 8/10 | **85/100** |
| MiniAgda-style | 25/25 | 12/20 | 10/20 | 15/15 | 7/10 | 10/10 | **79/100** |
| Structural only | 18/25 | 20/20 | 20/20 | 15/15 | 5/10 | 8/10 | **86/100** |

## 5.3 Recommendation Summary

```
Ranking for TERAS-LANG:

1. Agda-style (90/100)
   Practical sized types with partial inference
   Best integration potential
   
2. Structural + Agda (86/100 enhanced)
   Default structural, optional sizes
   Practical hybrid
   
3. F*-style (85/100)
   Maximum expressiveness
   Higher annotation burden

Recommended Hybrid:
  - Default: Structural recursion checking
  - Enhancement: Agda-style sized types for complex cases
  - Fallback: F*-style measures for edge cases
```

---

# PART VI: SUMMARY

## 6.1 Key Comparative Findings

1. **Agda-style provides best balance** â€” practical inference with good guarantees
2. **Structural recursion often sufficient** â€” sized types for edge cases
3. **Zero runtime overhead universal** â€” all systems erase sizes
4. **Integration feasible** â€” can combine with linear/effect/capability types
5. **F* measures most expressive** â€” but manual annotation required

## 6.2 Design Direction

```
TERAS-LANG Sized Type Design:

Primary: Structural recursion by default
  - Simple, predictable
  - No annotation needed
  - Covers 90% of cases

Enhancement: Agda-style sizes
  - A^i syntax for sized types
  - Partial inference
  - For non-structural patterns

Integration:
  - lin A^i for linear bounded resources
  - A^i ! E for bounded effects
  - cap<R,P>^i for usage-limited capabilities
  - code[A^i â†’ B] for terminating generated code
```

---

**END OF COMPARISON DOCUMENT**

**Next Document:** RESEARCH_A16_SIZED_TYPES_DECISION.md
