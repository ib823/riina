# TERAS RESEARCH SURVEY: GRADUAL TYPES
## Session A-10: Gradual Typing, The Gradual Guarantee, and Blame Tracking

**Document ID:** RESEARCH_A10_GRADUAL_TYPES_SURVEY  
**Version:** 1.0.0  
**Date:** 2026-01-03  
**Status:** COMPLETE  
**Classification:** TERAS Research Track - Domain A (Type Theory)

---

## PART I: FOUNDATIONS OF GRADUAL TYPING

### 1.1 What Is Gradual Typing?

Gradual typing enables mixing statically typed and dynamically typed code within a single program, providing a spectrum between full static typing and full dynamic typing.

**Core Insight:** Introduce a special type `?` (or `Dyn`, `Any`, `*`) that is compatible with all other types, deferring type checking to runtime.

```
Static Typing          Gradual Typing         Dynamic Typing
────────────────────────────────────────────────────────────
All types known        Some types known       No static types
at compile time        at compile time        Type checking
                                              at runtime only
```

**Key Properties:**
1. **Static-Dynamic Spectrum:** Code can be partially typed
2. **Gradual Migration:** Incrementally add types to untyped code
3. **Runtime Checking:** Type errors detected at runtime for dynamic portions
4. **Blame Tracking:** Identify source of type errors across boundaries

### 1.2 Historical Development

| Year | Development | Contributor |
|------|-------------|-------------|
| 2006 | Gradual typing for functional languages | Siek & Taha |
| 2009 | Gradual typing for objects | Siek & Taha |
| 2010 | Blame calculus | Wadler & Findler |
| 2011 | Threesomes | Siek & Wadler |
| 2014 | TypeScript | Microsoft |
| 2015 | Gradual guarantee formalized | Siek et al. |
| 2016 | Gradual parametricity | Igarashi et al. |
| 2017 | Abstracting Gradual Typing (AGT) | Garcia et al. |
| 2019 | Gradual effects | Bañados Schwerter et al. |
| 2021 | Gradual liquid types | Vazou et al. |

### 1.3 The Unknown Type

**The Dynamic/Unknown Type `?`:**
```
? ∼ τ  for all types τ    (? is consistent with everything)
```

**Type Consistency (≁ is not the same as equality):**
```
Consistency Rules:
────────────────────
? ∼ τ           -- Unknown is consistent with any type
τ ∼ ?           -- Any type is consistent with unknown
τ ∼ τ           -- Reflexivity
─────────────
τ₁ → τ₂ ∼ τ₁' → τ₂'    if τ₁ ∼ τ₁' and τ₂ ∼ τ₂'
(τ₁, τ₂) ∼ (τ₁', τ₂')  if τ₁ ∼ τ₁' and τ₂ ∼ τ₂'
```

**Key Distinction:**
- **Type Equality:** `Int = Int`, `Int ≠ Bool`
- **Type Consistency:** `? ∼ Int`, `? ∼ Bool`, `Int ∼ Int`
- Consistency is symmetric but NOT transitive:
  `Int ∼ ?` and `? ∼ Bool` but `Int ≁ Bool`

---

## PART II: THE GRADUAL GUARANTEE

### 2.1 Definition

The **Gradual Guarantee** (Siek et al. 2015) formalizes that adding type annotations should not change program behavior:

**Informal Statement:**
> If a well-typed program is modified by adding type annotations (making it more precisely typed), the program continues to behave the same way (or produces a type error at compile time).

**Formal Statement:**

Let `e ⊑ e'` mean "e is less precisely typed than e'" (e has more `?` types).

1. **Soundness Preservation:** 
   If `Γ ⊢ e : τ` and `e ⊑ e'` and `Γ' ⊢ e' : τ'` then `τ ⊑ τ'`

2. **Behavior Preservation:**
   If `Γ ⊢ e : τ` and `e ⊑ e'` and `Γ' ⊢ e' : τ'` then:
   - If `e ⟶* v` then `e' ⟶* v'` where `v ⊑ v'`, OR
   - If `e ⟶* error` then `e' ⟶* error` OR `e'` fails to type check

### 2.2 Precision Ordering

**Type Precision (⊑):**
```
? ⊑ τ           -- Unknown is less precise than any type
τ ⊑ τ           -- Reflexivity
Int ⊑ Int       -- Base types are equally precise

τ₁ → τ₂ ⊑ τ₁' → τ₂'    if τ₁' ⊑ τ₁ and τ₂ ⊑ τ₂'  (contravariant in input)
```

**Term Precision:**
```
x ⊑ x                   -- Variables
λx:τ.e ⊑ λx:τ'.e'      if τ ⊑ τ' and e ⊑ e'
e₁ e₂ ⊑ e₁' e₂'        if e₁ ⊑ e₁' and e₂ ⊑ e₂'
```

### 2.3 Why the Gradual Guarantee Matters

1. **Safe Migration:** Adding types to untyped code won't break it
2. **Incremental Adoption:** Type gradually, get benefits incrementally  
3. **Predictability:** Programmers understand how types affect behavior
4. **Refactoring Safety:** Type annotations are purely informational

**Counter-example (languages that violate the guarantee):**
```python
# Python with mypy (no gradual guarantee)
def f(x):
    return x + 1

f("hello")  # Runs, produces runtime error

# Adding type
def f(x: int) -> int:
    return x + 1

f("hello")  # Still runs! Mypy only warns, doesn't prevent
```

---

## PART III: BLAME CALCULUS

### 3.1 The Blame Problem

When static and dynamic code interact, who's responsible for type errors?

```
Typed Code                      Untyped Code
──────────────────────────────────────────────
def increment(x: Int) -> Int:   def broken(f):
    return x + 1                    return f("hello")

# broken(increment)  -- Runtime error
# Whose fault? The untyped code passed a string!
```

**Blame Tracking:** Assign responsibility labels to code boundaries.

### 3.2 Casts and Blame Labels

**Cast Syntax:** `⟨τ₁ ⇐^p τ₂⟩ e`
- Cast expression `e` from type `τ₂` to type `τ₁`
- Blame label `p` identifies the boundary
- Label can be positive (`+p`) or negative (`-p`)

**Cast Semantics:**
```
⟨Int ⇐^p Int⟩ n  ⟶  n                    -- Identity
⟨Int ⇐^p ?⟩ n    ⟶  n                    -- Unbox from ?
⟨? ⇐^p Int⟩ n    ⟶  n                    -- Box into ?
⟨Int ⇐^p Bool⟩ true  ⟶  blame p         -- Type mismatch

-- Function casts (domain contravariant, codomain covariant)
⟨τ₁ → τ₂ ⇐^p τ₁' → τ₂'⟩ f  ⟶  
    λx. ⟨τ₂ ⇐^p τ₂'⟩ (f (⟨τ₁' ⇐^~p τ₁⟩ x))
```

### 3.3 The Blame Theorem

**Blame Theorem (Wadler & Findler 2009):**
> Well-typed programs can't be blamed.

If a program consists of typed and untyped code, and a cast error occurs, the blame label will always point to untyped code.

**Formal Statement:**
If `∅ ⊢ e : τ` and `e ⟶* blame p`, then `p` labels untyped code.

**Intuition:** Typed code fulfills its contract. Only untyped code can violate expectations.

### 3.4 Positive and Negative Blame

**Polarity Rules:**
- **Positive blame (+p):** The blamed code produced a wrong value
- **Negative blame (-p):** The blamed code used a value incorrectly

```
-- Function boundary example
typed_f : Int → Int          -- Type promise
untyped_call(f) = f("hi")    -- Untyped calls typed

⟨Int → Int ⇐^p ? → ?⟩ typed_f
  = λx. ⟨Int ⇐^p ?⟩ (typed_f (⟨? ⇐^~p Int⟩ x))

-- When called with "hi":
⟨? ⇐^~p Int⟩ "hi"  ⟶  blame ~p  -- Negative: caller's fault
```

---

## PART IV: IMPLEMENTATION STRATEGIES

### 4.1 Cast Representation

**Three Main Approaches:**

1. **Type-Tagged Values (Traditional):**
   ```
   data DynValue = DInt Int | DBool Bool | DFun (DynValue → DynValue)
   
   cast : DynValue → Type → Maybe DynValue
   cast (DInt n) IntT = Just (DInt n)
   cast (DInt n) BoolT = Nothing  -- Type error
   ```

2. **Coercions (Henglein 1994):**
   ```
   data Coercion = Id | Fail | Fun Coercion Coercion | Seq Coercion Coercion
   
   -- Composable: c₁ ; c₂ can be composed
   compose : Coercion → Coercion → Coercion
   ```

3. **Threesomes (Siek & Wadler 2010):**
   ```
   ⟨τ, G, τ'⟩ e
   -- τ = source type
   -- G = ground type (mediator)
   -- τ' = target type
   
   -- Enables space-efficient cast composition
   ```

### 4.2 Space Efficiency

**The Space Efficiency Problem:**
```
-- Naive casts accumulate
let rec loop n =
  if n = 0 then 0
  else ⟨Int ⇐ ?⟩(⟨? ⇐ Int⟩(loop (n-1)))

-- After n iterations: n nested casts!
```

**Solutions:**
1. **Coercion Composition:** Compose adjacent casts
2. **Threesomes:** Represent casts as triples, compose naturally
3. **Space-Efficient Semantics:** Prove O(1) cast overhead

### 4.3 Performance Considerations

| Strategy | Cast Time | Space | Composition |
|----------|-----------|-------|-------------|
| Tagged Values | O(1) | O(n) runtime type | No |
| Coercions | O(n) compose | O(1) per cast | Yes |
| Threesomes | O(1) | O(1) | Yes |
| Monotonic (Siek 2015) | O(1) amortized | O(1) | Yes |

---

## PART V: GRADUAL TYPING IN PRACTICE

### 5.1 TypeScript

**TypeScript's Approach:**
- `any` type represents unknown
- Type erasure at runtime (no runtime checks!)
- Structural subtyping
- Does NOT satisfy the gradual guarantee

```typescript
// TypeScript
function greet(name: string): string {
    return "Hello, " + name;
}

let x: any = 42;
greet(x);  // No compile error (any compatible with string)
           // No runtime error (types erased)
           // Returns "Hello, 42"
```

**Analysis:** TypeScript prioritizes migration ease over soundness.

### 5.2 Typed Racket

**Typed Racket's Approach:**
- Full blame tracking
- Runtime contracts at boundaries
- Satisfies gradual guarantee (with some exceptions)
- Sound gradual typing

```racket
#lang typed/racket

(: add1 (-> Integer Integer))
(define (add1 x)
  (+ x 1))

; In untyped Racket module:
(add1 "hello")  ; Runtime error with clear blame
```

**Analysis:** Typed Racket is the gold standard for sound gradual typing.

### 5.3 Flow

**Flow's Approach:**
- Type inference for JavaScript
- Tracks `mixed` and `any` types
- No runtime enforcement
- Focus on developer experience

### 5.4 Mypy (Python)

**Mypy's Approach:**
- Optional static type checking
- `Any` type is universal
- No runtime enforcement (unless using runtime checkers)
- Gradual by default

### 5.5 Comparison

| Language | Sound | Gradual Guarantee | Runtime Checks | Performance |
|----------|-------|-------------------|----------------|-------------|
| TypeScript | No | No | No | Excellent |
| Typed Racket | Yes | Mostly | Yes | Overhead |
| Flow | No | No | No | Excellent |
| Mypy | No | No | Optional | Excellent |
| Reticulated Python | Yes | Yes | Yes | Significant overhead |

---

## PART VI: ADVANCED TOPICS

### 6.1 Gradual Parametricity

**The Problem:** How do generic types interact with `?`?

```
id : ∀a. a → a
id_dyn : ? → ?

-- Are these compatible?
⟨∀a.a→a ⇐ ?→?⟩ id_dyn  -- Can we cast?
```

**Gradual Parametricity (Igarashi et al. 2017):**
- Extend gradual typing to polymorphic types
- Preserve parametricity when types are known
- Allow violation when types are unknown

```
id_dyn : ? → ?
id_dyn x = if is_int(x) then 0 else x

-- This violates parametricity for id : ∀a.a→a
-- But is acceptable at type ? → ?
```

### 6.2 Gradual Effects

**Gradual Effect Systems (Bañados Schwerter et al. 2019):**
- Unknown effect `!` compatible with any effect
- Gradual migration of effect annotations
- Runtime effect checking at boundaries

```
-- Fully typed
read_file : String → IO String

-- Gradual (unknown effect)
process : String → ! String

-- Boundary inserts check
⟨IO String ⇐^p ! String⟩ (process path)
-- Checks that process actually performs IO
```

### 6.3 Gradual Refinement Types

**Gradual Liquid Types (Vazou et al. 2021):**
- Unknown refinement `{?}` compatible with any predicate
- Runtime checking of refinement violations

```
-- Precise type
positive : {x : Int | x > 0}

-- Gradual type
unknown_sign : {x : Int | ?}

-- Cast checks predicate at runtime
⟨{x | x > 0} ⇐ {x | ?}⟩ (unknown_sign)
```

### 6.4 Abstracting Gradual Typing (AGT)

**AGT Framework (Garcia et al. 2016):**
Systematic method to derive gradual type systems from static ones:

1. **Start with static type system**
2. **Replace types with sets of types (gradual types)**
3. **Lift operations to sets**
4. **Derive consistency and precision from sets**

```
-- Static type
Int

-- Gradual type (set interpretation)
? = { Int, Bool, String, ... }  -- All types
Int = { Int }                    -- Singleton set

-- Consistency
τ₁ ∼ τ₂  iff  τ₁ ∩ τ₂ ≠ ∅
```

---

## PART VII: GRADUAL TYPING FOR SECURITY

### 7.1 Gradual Security Types

**Gradual Information Flow (Fennell & Thiemann 2013):**
- Unknown security label `⊤?`
- Gradual migration from untyped to security-typed
- Runtime enforcement of information flow

```
-- Static IFC
secret : Secret<Int, High>
public : Secret<Int, Low>

-- Gradual IFC
unknown_sensitivity : Secret<Int, ?>

-- Flow check at runtime
⟨Secret<Int, Low> ⇐ Secret<Int, ?>⟩ unknown_sensitivity
-- Checks that actual sensitivity ≤ Low
```

### 7.2 Gradual Capabilities

```
-- Unknown capability
dyn_cap : ?<Capability>

-- Gradual check
⟨Capability<Read, Write> ⇐ ?<Capability>⟩ dyn_cap
-- Runtime: verify dyn_cap has Read and Write
```

### 7.3 Gradual Session Types

**Gradual Sessions (Igarashi et al. 2019):**
```
-- Static session
auth_session : !Credentials.?{Accept:!Token.end, Reject:end}

-- Gradual session (unknown protocol)
dyn_session : ?Session

-- Runtime protocol monitoring
⟨AuthSession ⇐ ?Session⟩ dyn_session
-- Checks protocol compliance dynamically
```

### 7.4 Trust Boundaries

Gradual typing naturally models trust boundaries:

```
┌─────────────────┐         ┌──────────────────┐
│   Typed Core    │  ⟷ casts │  Untyped Plugins │
│   (trusted)     │         │   (untrusted)    │
└─────────────────┘         └──────────────────┘

-- All interactions through typed interfaces
plugin_api : (? → ?) → ...

-- Plugin operations cast with blame
⟨Int → Int ⇐^plugin ?→?⟩ plugin_fn
-- If plugin_fn fails, blame points to plugin
```

---

## PART VIII: PERFORMANCE ANALYSIS

### 8.1 Cast Overhead

**Benchmarks from Typed Racket:**
- Fully typed: 0% overhead
- Boundary-heavy: 10-100x slowdown
- Typical mixed code: 2-10x overhead

**Optimization Techniques:**
1. **Type-based specialization:** Compile typed code without checks
2. **Cast coalescing:** Merge adjacent casts
3. **Tracing JIT:** Optimize hot paths
4. **Monotonic references:** Casts only in one direction

### 8.2 Memory Overhead

| Representation | Per-Value | Per-Cast | Total |
|----------------|-----------|----------|-------|
| Tagged | Type tag | None | Low |
| Wrapped | Wrapper | Wrapper chain | High |
| Monotonic | Type slot | None | Low |

### 8.3 Practical Guidelines

1. **Type boundaries, not interiors:** Put typed/untyped boundaries at module edges
2. **Avoid hot-path casts:** Type hot code paths fully
3. **Use precise types:** More precise = fewer runtime checks
4. **Profile carefully:** Identify cast-heavy code

---

## PART IX: TERAS-LANG RELEVANCE

### 9.1 Why Gradual Typing for TERAS?

**Use Cases:**

1. **Legacy Integration:** Interface with untyped code (Python libraries, etc.)
2. **Plugin Systems:** Allow plugins without full type information
3. **Rapid Prototyping:** Develop without types, add later
4. **FFI Boundaries:** Safe interaction with C/unsafe code

### 9.2 Gradual Security Properties

```teras
-- Core typed (full guarantees)
fn process_secret(
  secret: Secret<Data, High>,
  key: lin uniq Key
) -> eff[Crypto] Encrypted { ... }

-- External plugin (gradual)
fn plugin_transform(data: ?) -> ? { ... }

-- Boundary enforces security
fn call_plugin(
  data: Public<Data>
) -> eff[Plugin] Result<Public<Data>, Error>
{
  // Cast ensures result is actually public
  let result = ⟨Public ⇐^plugin ?⟩ plugin_transform(data);
  result
}
```

### 9.3 Integration with TERAS Type System

```
-- Gradual + Linear
(1 x: ?) → ?      -- Linear unknown
? → (1 _: Int)    -- Return linear Int

-- Gradual + Effects
fn dyn_op(x: ?) -> eff[?] ?  -- Unknown effects
fn call() -> eff[IO] Int {
  ⟨eff[IO] Int ⇐^p eff[?] ?⟩ dyn_op(42)
}

-- Gradual + Refinements
{x: ? | x > 0}    -- Unknown base type, known predicate
{x: Int | ?}      -- Known type, unknown predicate
```

### 9.4 Blame for Security

```teras
-- Trust boundaries with blame tracking
boundary untrusted_plugin : ? → ? {
  // All casts blame "untrusted_plugin"
  // Security violations traceable to plugin
}

-- Usage
fn use_plugin(data: Public<Data>) -> Result<Public<Data>, Blamed>
{
  match ⟨Public ⇐^untrusted_plugin ?⟩ untrusted_plugin(data) {
    Ok(v) => Ok(v),
    Err(blame) => {
      // blame identifies untrusted_plugin as source
      log_security_violation(blame);
      Err(blame)
    }
  }
}
```

---

## PART X: KEY INSIGHTS AND RECOMMENDATIONS

### 10.1 Key Insights

1. **Gradual Guarantee is Crucial:** Without it, adding types can break code—unacceptable for TERAS
2. **Blame is Essential:** Security requires knowing who violated contracts
3. **Performance Trade-offs:** Sound gradual typing has overhead; optimize boundaries
4. **Security Integration:** Gradual types can model trust boundaries naturally
5. **Not All-or-Nothing:** Use gradual typing strategically, not universally

### 10.2 Recommendations for TERAS-LANG

| Aspect | Recommendation | Rationale |
|--------|----------------|-----------|
| **Gradual Guarantee** | MUST satisfy | Safe type migration |
| **Blame Tracking** | MUST implement | Security attribution |
| **Unknown Type** | Limited `?` | Not universal escape hatch |
| **Runtime Checks** | At boundaries only | Performance |
| **Default Mode** | Fully typed | Security-first |
| **Gradual Security** | Optional extension | For plugin systems |

### 10.3 When to Use Gradual Typing in TERAS

**APPROPRIATE:**
- FFI boundaries with C code
- Plugin/extension interfaces
- Migration of legacy code
- Prototyping (with intent to type later)

**NOT APPROPRIATE:**
- Security-critical core
- Cryptographic operations
- Memory-safety critical code
- Performance-critical hot paths

---

## PART XI: REFERENCES

### Academic Papers
1. Siek, J. & Taha, W. (2006). "Gradual Typing for Functional Languages"
2. Wadler, P. & Findler, R. (2009). "Well-Typed Programs Can't Be Blamed"
3. Siek, J. et al. (2015). "Refined Criteria for Gradual Typing"
4. Garcia, R. et al. (2016). "Abstracting Gradual Typing"
5. Bañados Schwerter, F. et al. (2019). "Gradual Effect Checking"

### Implementations
- Typed Racket: https://docs.racket-lang.org/ts-guide/
- TypeScript: https://www.typescriptlang.org/
- Reticulated Python: https://github.com/mvitousek/reticulated

### Books/Tutorials
- "Practical Foundations for Programming Languages" - Harper (Chapter on gradual types)
- "Types and Programming Languages" - Pierce (foundations)

---

**END OF SURVEY DOCUMENT**

*Document generated for TERAS Research Track - Session A-10*
*Next: RESEARCH_A10_GRADUAL_TYPES_COMPARISON.md*
