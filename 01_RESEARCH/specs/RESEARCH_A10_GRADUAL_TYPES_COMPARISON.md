# TERAS RESEARCH COMPARISON: GRADUAL TYPES
## Session A-10: Comparative Analysis of Gradual Typing Approaches

**Document ID:** RESEARCH_A10_GRADUAL_TYPES_COMPARISON  
**Version:** 1.0.0  
**Date:** 2026-01-03  
**Status:** COMPLETE  
**Classification:** TERAS Research Track - Domain A (Type Theory)

---

## 1. EXECUTIVE SUMMARY

This document compares gradual typing approaches for TERAS-LANG, evaluating their suitability for a security-focused language. The comparison covers theoretical foundations, practical implementations, and security implications.

**Key Finding:** Sound gradual typing with blame tracking (Typed Racket model) is essential for TERAS security requirements, but must be integrated strategically to avoid performance penalties. Gradual typing should be an optional feature for FFI and plugin boundaries, not a universal language feature.

---

## 2. COMPARISON DIMENSIONS

### 2.1 Theoretical Soundness

| Approach | Gradual Guarantee | Blame Theorem | Type Safety |
|----------|-------------------|---------------|-------------|
| **Typed Racket** | Yes | Yes | Sound |
| **TypeScript** | No | No | Unsound |
| **Flow** | Partial | No | Unsound |
| **Mypy** | No | No | Unsound |
| **Reticulated Python** | Yes | Yes | Sound |
| **Gradualtalk** | Yes | Yes | Sound |

**Analysis for TERAS:**
- TERAS requires soundness (violations lead to security breaches)
- Must satisfy gradual guarantee (safe type migration)
- Must have blame tracking (security attribution)

### 2.2 Performance Characteristics

| Approach | Boundary Overhead | Cast Strategy | Space Efficiency |
|----------|-------------------|---------------|------------------|
| **Typed Racket** | 10-100x | Contracts | Moderate |
| **TypeScript** | 0% (no checks) | Erasure | Excellent |
| **Monotonic Refs** | 2-5x | Single-direction | Excellent |
| **Threesomes** | 2-3x | Composed | Excellent |
| **Transient** | 1.5-2x | Shallow checks | Good |

**Analysis for TERAS:**
- TypeScript's approach unacceptable (no soundness)
- Typed Racket's overhead too high for security systems
- Monotonic or threesome approach preferred for TERAS

### 2.3 Cast Semantics

**Type-Directed (Typed Racket):**
```
âŸ¨Int â†’ Int â‡ ? â†’ ?âŸ© f = 
  Î»x. âŸ¨Int â‡ ?âŸ©(f (âŸ¨? â‡ IntâŸ© x))
```
- Full structural checking
- High overhead
- Maximum blame precision

**Transient (Vitousek et al.):**
```
-- Only check top-level type tag
âŸ¨Int â‡ ?âŸ© v = if tag(v) == INT then v else error
```
- Shallow checks only
- Low overhead
- Less precise blame

**Monotonic (Siek et al. 2015):**
```
-- Values can only become more precisely typed
ref<Int> r := ?
r := 42       -- r's type refined to Int
r := "hello"  -- ERROR: would weaken type
```
- Amortized O(1)
- Space efficient
- Limited flexibility

---

## 3. IMPLEMENTATION COMPARISON

### 3.1 Typed Racket (Sound, Full)

**Strengths:**
- Fully sound gradual typing
- Comprehensive blame tracking
- Mature implementation (15+ years)
- Good tooling

**Weaknesses:**
- Significant performance overhead
- Complex implementation
- Scheme-specific design

**Code Example:**
```racket
#lang typed/racket
(: safe-div (-> Integer Integer (Option Integer)))
(define (safe-div x y)
  (if (= y 0) #f (quotient x y)))

; In untyped module
(safe-div 10 "oops")  ; Runtime blame error
```

### 3.2 TypeScript (Unsound, Pragmatic)

**Strengths:**
- Zero runtime overhead
- Excellent tooling
- Wide adoption
- Great developer experience

**Weaknesses:**
- Not sound (any escapes type system)
- No runtime type checks
- Types erased at compile time
- Can't guarantee security properties

**Code Example:**
```typescript
function process(x: number): number {
    return x * 2;
}
const val: any = "hello";
process(val);  // No error! Returns NaN
```

**Analysis:** Completely unsuitable for security-critical code.

### 3.3 Reticulated Python (Sound, Research)

**Strengths:**
- Sound gradual typing for Python
- Blame tracking
- Gradual guarantee proven
- AGT-based design

**Weaknesses:**
- Research prototype
- Significant overhead
- Limited adoption
- Python-specific

### 3.4 Transient Approach (Vitousek)

**Strengths:**
- Low overhead (shallow checks)
- Sound for first-order types
- Good performance/safety trade-off

**Weaknesses:**
- No blame tracking
- Doesn't catch all errors early
- Higher-order issues

**Code Example:**
```
-- Transient: only checks top-level
âŸ¨Int â†’ Int â‡ ? â†’ ?âŸ© f
-- Only checks that f is a function
-- Doesn't wrap to check argument/result types
```

---

## 4. SECURITY-SPECIFIC COMPARISON

### 4.1 Trust Boundary Modeling

| Approach | Trust Modeling | Attack Surface |
|----------|---------------|----------------|
| Sound + Blame | Explicit boundaries | Visible |
| Unsound | No modeling | Hidden |
| Transient | Partial | Partially visible |

**TERAS Requirement:** Trust boundaries must be explicit and enforced.

### 4.2 Blame for Security Attribution

**With Blame (Typed Racket style):**
```
Typed Code                  Untyped Plugin
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
api : Int â†’ Int            plugin_fn = Î»x. "bad"

-- When plugin_fn called through api:
-- Error: "plugin boundary violated contract"
-- Blame: plugin_fn (untyped side)
```

**Without Blame (TypeScript style):**
```
// No way to know who violated contract
// Silent data corruption possible
```

**Analysis:** Blame is essential for security auditing and incident response.

### 4.3 Information Flow with Gradual Types

**Challenge:** Gradual typing must preserve IFC properties.

| Scenario | Sound Approach | Unsound Approach |
|----------|----------------|------------------|
| Secret â†’ ? | Runtime label check | Label lost |
| ? â†’ Public | Runtime verification | No check |
| ? â†’ ? | Propagate dynamically | Unknown |

**TERAS Requirement:** Gradual IFC must preserve non-interference at boundaries.

### 4.4 Linear Types with Gradual Typing

**Challenge:** How does `?` interact with linearity?

| Combination | Meaning | Safety |
|-------------|---------|--------|
| `1 : ?` | Linear unknown | Tricky |
| `? : A` | Unknown quantity | Dangerous |
| `1 : A` | Linear known | Safe |

**Proposed Solution:**
```
-- Quantity is always known (not gradual)
-- Only base type can be unknown
(1 x: ?) â†’ ?    -- OK: linear unknown
(? x: Int) â†’ ?  -- ERROR: quantity must be explicit
```

---

## 5. INTEGRATION WITH TERAS TYPE SYSTEM

### 5.1 Integration with A-04 Linear Types

**Option A: Unknown is unrestricted**
```
? : Type  (implicitly Ï‰ quantity)
-- All ? values are unrestricted
-- Converting linear to ? loses linearity
```
**Pros:** Simple
**Cons:** Can't have linear unknown

**Option B: Graded unknown**
```
?_q : Type  where q âˆˆ {0, 1, Ï‰}
-- Unknown with explicit quantity
```
**Pros:** Preserves linearity
**Cons:** More complex

**Recommendation:** Option B (security requires linear tracking)

### 5.2 Integration with A-05 Effects

**Effect Graduality:**
```
eff[?] A     -- Unknown effects
eff[E] ?     -- Known effects, unknown result
eff[?] ?     -- Fully unknown

-- Cast semantics
âŸ¨eff[IO] Int â‡ eff[?] ?âŸ© e
= handle e with
    runtime_effect_check(IO)
    result_cast(Int)
```

**Recommendation:** Allow gradual effects but prefer explicit effects.

### 5.3 Integration with A-09 Dependent Types

**Dependent Graduality:**
```
-- Unknown dependent type
(x: Int) â†’ ?{x}    -- Result depends on x somehow

-- Gradual vector
Vec<?>(?)          -- Unknown element type, unknown length
Vec<Int>(?)        -- Int elements, unknown length
Vec<?>(5)          -- Unknown elements, length 5
```

**Challenge:** Dependent types require computation; `?` blocks computation.

**Recommendation:** Limited dependent graduality (only in argument position).

### 5.4 Integration with A-08 Refinement Types

**Gradual Refinements:**
```
{x: Int | ?}       -- Unknown predicate
{x: ? | x > 0}     -- Unknown type, known predicate (odd)
{x: ? | ?}         -- Fully unknown

-- Runtime checking
âŸ¨{x: Int | x > 0} â‡ {x: Int | ?}âŸ© v
= if v > 0 then v else blame p
```

**Recommendation:** Support gradual refinements for FFI boundaries.

---

## 6. DESIGN ALTERNATIVES

### 6.1 Alternative A: No Gradual Typing

**Description:** TERAS-LANG is fully statically typed, no `?` type.

**Pros:**
- Maximum security guarantees
- No runtime overhead
- Simpler implementation

**Cons:**
- Difficult FFI with untyped code
- No plugin extensibility
- Rigid

### 6.2 Alternative B: Boundary-Only Gradual

**Description:** `?` type only at module boundaries.

**Pros:**
- Clear trust boundaries
- Limited attack surface
- Good security model

**Cons:**
- Less flexible than full gradual
- Requires careful boundary design

### 6.3 Alternative C: Full Gradual

**Description:** `?` type anywhere in the language.

**Pros:**
- Maximum flexibility
- Easy migration
- Standard gradual semantics

**Cons:**
- Security risks from internal `?`
- Performance unpredictable
- Complex implementation

### 6.4 Recommendation: Alternative B (Boundary-Only)

For TERAS security requirements:
- Gradual typing only at defined boundaries
- Core language remains fully typed
- Clear trust model
- Acceptable performance

---

## 7. EVALUATION MATRIX

### 7.1 Weighted Scoring

| Criterion | Weight | Typed Racket | TypeScript | Boundary-Only |
|-----------|--------|--------------|------------|---------------|
| Soundness | 20 | 10 | 0 | 10 |
| Gradual Guarantee | 15 | 10 | 0 | 10 |
| Blame Tracking | 15 | 10 | 0 | 10 |
| Performance | 15 | 4 | 10 | 8 |
| Security Integration | 15 | 8 | 2 | 10 |
| Linear Type Integration | 10 | 5 | 0 | 9 |
| Implementation Complexity | 10 | 4 | 8 | 7 |

**Weighted Scores:**
- **Typed Racket Model:** 7.25/10
- **TypeScript Model:** 2.75/10 (disqualified for security)
- **Boundary-Only (TERAS):** 9.15/10

### 7.2 Interpretation

1. **TypeScript model disqualified:** No soundness = no security
2. **Typed Racket model has merit:** But performance concerns for hot paths
3. **Boundary-only approach optimal:** Combines benefits, minimizes risks

---

## 8. DETAILED DESIGN FOR TERAS

### 8.1 Boundary Definition Syntax

```teras
-- Define external boundary
extern boundary untrusted_plugin {
  fn transform(data: ?) -> ?;
  fn validate(input: ?) -> { valid: Bool, error: ? };
}

-- Define typed interface
interface PluginAPI {
  fn transform(data: Public<Data>) -> Result<Public<Data>, Error>;
  fn validate(input: Input) -> ValidationResult;
}

-- Connect boundary to interface
impl PluginAPI for untrusted_plugin {
  fn transform(data: Public<Data>) -> Result<Public<Data>, Error> {
    // Automatic casts inserted with blame
    âŸ¨Public<Data> â‡^untrusted_plugin ?âŸ© 
      untrusted_plugin.transform(
        âŸ¨? â‡^untrusted_plugin Public<Data>âŸ© data
      )
  }
}
```

### 8.2 Cast Semantics

```teras
-- Cast failure produces blame
data BlameError {
  boundary: BoundaryId,
  expected_type: Type,
  actual_type: Type,
  value: DebugInfo,
}

-- Cast behavior
cast<T>(value: ?, boundary: BoundaryId) -> Result<T, BlameError> {
  if runtime_type_check(value, T) {
    Ok(unsafe_coerce(value))
  } else {
    Err(BlameError {
      boundary: boundary,
      expected_type: type_of<T>(),
      actual_type: runtime_type_of(value),
      value: debug_repr(value),
    })
  }
}
```

### 8.3 Performance Optimization

```teras
-- Declare hot path (no gradual typing allowed)
#[hot_path]
fn critical_crypto(key: lin uniq Key, data: Bytes) -> Encrypted {
  // Compiler error if any ? types reach here
  ...
}

-- Declare cold boundary (gradual allowed)
#[cold_boundary]
extern boundary slow_plugin { ... }
```

---

## 9. RISK ANALYSIS

### 9.1 Risks of Each Approach

| Risk | Full Gradual | Boundary-Only | No Gradual |
|------|--------------|---------------|------------|
| Security holes | High | Low | None |
| Performance issues | High | Medium | None |
| Implementation bugs | High | Medium | Low |
| FFI difficulties | None | Low | High |
| Plugin limitations | None | Low | High |

### 9.2 Mitigation Strategies

**For Boundary-Only Approach:**

1. **Boundary Audit:** All boundaries explicitly marked, reviewable
2. **Blame Logging:** All type errors logged with full context
3. **Hot Path Protection:** Compiler prevents gradual types in critical code
4. **Testing:** Boundary fuzzing to find type mismatches

---

## 10. CONCLUSION

### 10.1 Primary Recommendation

**Adopt Boundary-Only Gradual Typing:**
- `?` type only at designated boundaries
- Full blame tracking with security attribution
- Monotonic/threesome cast representation for performance
- Integration with linear types (graded unknown)

### 10.2 Key Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Soundness | Required | Security fundamental |
| Gradual Guarantee | Required | Safe migration |
| Blame | Full tracking | Security attribution |
| Scope | Boundary-only | Minimize risk |
| Performance | Monotonic casts | Balance safety/speed |
| Linear integration | Graded unknown | Preserve linearity |

### 10.3 What We Reject

1. **TypeScript-style erasure:** Unsound, unacceptable for security
2. **Universal `?`:** Too risky for security-critical code
3. **No gradual typing:** Too rigid for practical FFI needs

---

**END OF COMPARISON DOCUMENT**

*Document generated for TERAS Research Track - Session A-10*
*Next: RESEARCH_A10_GRADUAL_TYPES_DECISION.md*
