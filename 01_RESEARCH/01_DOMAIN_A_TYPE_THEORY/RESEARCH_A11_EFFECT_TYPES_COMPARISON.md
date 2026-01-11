# RESEARCH_A11_EFFECT_TYPES_COMPARISON.md

## TERAS-LANG Research Track
### Session A-11: Effect Types — Comparative Analysis

---

**Document ID:** RESEARCH_A11_EFFECT_TYPES_COMPARISON  
**Version:** 1.0.0  
**Created:** 2026-01-03  
**Domain:** A (Type Theory Foundations)  
**Session:** A-11  
**Status:** COMPLETE

---

## 1. COMPARATIVE FRAMEWORK

This document provides a systematic comparison of effect type systems for TERAS-LANG integration, evaluating each approach against TERAS requirements for security, performance, and formal verification.

### 1.1 Evaluation Criteria

| Criterion | Weight | Description |
|-----------|--------|-------------|
| Effect Safety | 25% | Compile-time effect tracking guarantees |
| Inference Quality | 15% | Automatic effect inference capability |
| Polymorphism | 15% | Effect-polymorphic function support |
| Performance | 20% | Runtime overhead of effect system |
| Security Fit | 15% | Applicability to security properties |
| Integration | 10% | Compatibility with linear/session types |

---

## 2. EFFECT TYPING APPROACHES

### 2.1 Row-Polymorphic Effects (Koka)

**Mechanism:** Effects represented as row types with scoped labels

**Strengths:**
- Full effect inference with principal types
- Flexible effect composition and extension
- Established row polymorphism theory
- Evidence-passing compilation for efficiency

**Weaknesses:**
- Row unification can be O(n³) in worst case
- Effect types can become verbose
- Scoped labels add complexity

**TERAS Alignment:**
```
Security Tracking:    ████████░░ 80%
Performance:          █████████░ 90%
Formal Verification:  ████████░░ 80%
```

### 2.2 Boolean Unification Effects (Flix)

**Mechanism:** Effect constraints as Boolean formulas solved by unification

**Strengths:**
- Efficient purity tracking (pure vs impure)
- Principal types with minimal effects
- Integrates well with Hindley-Milner
- Clear separation of pure/impure code

**Weaknesses:**
- Boolean unification is NP-complete
- Less granular effect distinctions
- Limited to effect presence/absence

**TERAS Alignment:**
```
Security Tracking:    ███████░░░ 70%
Performance:          █████████░ 90%
Formal Verification:  ██████░░░░ 60%
```

### 2.3 Capability-Based Effects (Effekt)

**Mechanism:** Effects as capabilities required from context

**Strengths:**
- Simple contextual effect polymorphism
- Second-class functions ensure safety
- Lexical scoping enables zero-cost compilation
- No explicit effect variables needed

**Weaknesses:**
- Second-class functions limit expressivity
- Cannot store effectful functions in data
- Different mental model from traditional FP

**TERAS Alignment:**
```
Security Tracking:    █████████░ 90%
Performance:          █████████░ 90%
Formal Verification:  ███████░░░ 70%
```

### 2.4 Bidirectional Effects (Frank)

**Mechanism:** Bidirectional typing with invisible effect variables

**Strengths:**
- Minimal annotation burden
- Natural multihandler syntax
- Ambient effects simplify polymorphism
- Elegant unification of functions and handlers

**Weaknesses:**
- Research language maturity
- Limited tooling ecosystem
- Multihandler complexity for complex protocols

**TERAS Alignment:**
```
Security Tracking:    ███████░░░ 70%
Performance:          ███████░░░ 70%
Formal Verification:  ████████░░ 80%
```

### 2.5 First-Class Effects (Eff)

**Mechanism:** Effect instances as first-class values with handlers

**Strengths:**
- Maximum expressivity
- Dynamic effect instances
- Clean theoretical foundation
- Effect subtyping for modularity

**Weaknesses:**
- Complex type system
- Performance overhead from dynamism
- Steeper learning curve

**TERAS Alignment:**
```
Security Tracking:    ██████░░░░ 60%
Performance:          █████░░░░░ 50%
Formal Verification:  █████████░ 90%
```

### 2.6 Untyped Effects (OCaml 5)

**Mechanism:** Effect handlers without type-level effect tracking

**Strengths:**
- Simple integration with existing code
- Backward compatible
- Efficient fiber implementation
- Practical for concurrency

**Weaknesses:**
- No static effect tracking
- Cannot verify effect usage at compile time
- Effects as runtime failures

**TERAS Alignment:**
```
Security Tracking:    ██░░░░░░░░ 20%
Performance:          ████████░░ 80%
Formal Verification:  █░░░░░░░░░ 10%
```

---

## 3. HANDLER SEMANTICS COMPARISON

### 3.1 Deep vs Shallow Handlers

| Aspect | Deep Handlers | Shallow Handlers |
|--------|--------------|------------------|
| Continuation scope | Entire handled computation | Single effect occurrence |
| Re-handling | Automatic | Must re-install explicitly |
| Implementation | Simpler user code | More control |
| Use case | Most common | Fine-grained control |
| Languages | Koka, Eff, Frank | OCaml 5 (optional) |

### 3.2 Lexical vs Dynamic Handlers

| Aspect | Lexical Handlers | Dynamic Handlers |
|--------|-----------------|------------------|
| Binding | Compile-time known | Runtime lookup |
| Optimization | Zero-cost possible | Runtime overhead |
| Modularity | Local reasoning | Global effects |
| Examples | Effekt, Koka | Eff, early systems |

### 3.3 One-Shot vs Multi-Shot Continuations

| Aspect | One-Shot | Multi-Shot |
|--------|----------|------------|
| Memory | No copying needed | Must copy continuation |
| Linear types | Compatible | Requires special handling |
| Use cases | Most effects | Backtracking, search |
| Languages | OCaml 5, Effekt | Koka, Eff |
| TERAS fit | Preferred | Controlled usage |

---

## 4. COMPILATION STRATEGY COMPARISON

### 4.1 Evidence Passing (Koka)

```
// Source
handle action() with
  | effect Get() resume k -> k(state)

// Compiled (evidence passing)
fn action(ev: Evidence) {
  ev.handler.get(continuation)
}
```

**Performance:** Near-C for most effects, CPS for control effects only

### 4.2 CPS Transformation

```
// Source
handle action() with
  | effect Get() resume k -> k(state)

// Compiled (CPS)
fn action_cps(k: Continuation) {
  k_get = fn(v) { k(v) }
  handler.get(k_get)
}
```

**Performance:** Overhead from closure allocation

### 4.3 Fiber-Based (OCaml 5)

```
// Stack layout
[main fiber] <- [handler fiber] <- [effect fiber]

// Effect: capture fiber, invoke handler
// Resume: restore fiber, continue
```

**Performance:** Good for concurrency, stack allocation overhead

### 4.4 Region-Based (Effekt)

```
// Lexical effects compile to direct calls
// No continuation capture for local effects
```

**Performance:** Zero-cost for lexical effects

---

## 5. EFFECT POLYMORPHISM COMPARISON

### 5.1 Explicit Effect Variables (Koka, Flix)

```koka
// Koka: explicit effect variable e
fun map(f : a -> <e> b, xs : list<a>) : <e> list<b>
```

**Trade-offs:**
- Clear effect propagation
- Verbose for complex effects
- Good inference support

### 5.2 Implicit Effect Variables (Frank)

```frank
// Frank: implicit ambient effects
map : {X -> Y} -> List X -> List Y
```

**Trade-offs:**
- Minimal annotation
- Effects propagate automatically
- Less explicit documentation

### 5.3 Contextual Polymorphism (Effekt)

```effekt
// Effekt: block captures ambient
def map[A, B](l: List[A]) { f: A => B / {} }: List[B] / {}
```

**Trade-offs:**
- Simple model
- Second-class limitation
- Zero-cost compilation

---

## 6. SECURITY FEATURE COMPARISON

### 6.1 Information Flow Tracking

| System | Capability | Mechanism |
|--------|-----------|-----------|
| Koka | Can encode IFC | Effect annotations |
| Effekt | Natural capability model | Second-class enforces boundary |
| Flix | Purity distinction | Boolean pure/impure |
| Eff | Effect instances | Dynamic tracking possible |

### 6.2 Capability-Based Security

| System | Native Support | Implementation |
|--------|---------------|----------------|
| Effekt | Full | Second-class capabilities |
| Koka | Partial | Effect handlers as capabilities |
| Flix | No | Would need extension |
| OCaml 5 | No | Runtime only |

### 6.3 Resource Safety

| System | Linear Integration | Mechanism |
|--------|-------------------|-----------|
| Koka | Planned | Perceus + effects |
| Effekt | Partial | Regions + lexical |
| Flix | No | Separate feature |
| Eff | No | Pure functional |

---

## 7. TERAS REQUIREMENTS MATRIX

### 7.1 Effect Types for TERAS Products

| Product | Required Effects | Best Fit |
|---------|-----------------|----------|
| MENARA (Mobile) | IO, Crypto, Network | Koka/Effekt |
| GAPURA (WAF) | Network, State, Time | Koka |
| ZIRAH (EDR) | System, File, Process | Koka |
| BENTENG (eKYC) | Crypto, Bio, Network | Koka/Effekt |
| SANDI (Sig) | Crypto, Time, HSM | Koka |

### 7.2 Integration Requirements

| Requirement | Row-Based | Boolean | Capability |
|-------------|-----------|---------|------------|
| Linear types | ████████░░ | ██████░░░░ | █████████░ |
| Session types | ████████░░ | █████░░░░░ | ████████░░ |
| Refinement types | ███████░░░ | ██████░░░░ | ███████░░░ |
| Formal proofs | ████████░░ | ██████░░░░ | ███████░░░ |

### 7.3 Performance Requirements

| Scenario | Row-Based | Boolean | Capability |
|----------|-----------|---------|------------|
| No effects (pure) | Zero cost | Zero cost | Zero cost |
| Local effects | Near-zero | Near-zero | Zero cost |
| Control effects | CPS overhead | N/A | CPS overhead |
| Nested handlers | Log(n) lookup | N/A | Direct call |

---

## 8. SYNTHESIS

### 8.1 Overall Scores

| System | Security | Performance | Integration | Theory | Total |
|--------|----------|-------------|-------------|--------|-------|
| Koka (Row) | 80% | 90% | 85% | 90% | **86%** |
| Effekt (Cap) | 90% | 90% | 75% | 80% | **84%** |
| Flix (Bool) | 70% | 90% | 60% | 75% | **74%** |
| Frank (Bi) | 70% | 70% | 75% | 85% | **75%** |
| Eff (FC) | 60% | 50% | 70% | 95% | **69%** |
| OCaml 5 | 20% | 80% | 50% | 40% | **48%** |

### 8.2 Recommended Approach

**Primary:** Row-polymorphic effects (Koka-style)
- Best balance of expressivity, performance, and theory
- Evidence passing enables efficient compilation
- Well-established row polymorphism foundation

**Secondary Influence:** Capability-based insights (Effekt)
- Second-class functions for security-critical code
- Lexical scoping for zero-cost effects
- Capability model for access control

**Tertiary:** Purity tracking (Flix)
- Boolean pure/impure distinction
- Enables parallelization of pure code
- Simplifies verification

### 8.3 Hybrid Design

```teras
// Row-polymorphic effects with purity tracking
fn process<e: Effect>(x: Data) -> Result / <e | IO> where Pure(e)
  // e must be pure, can use IO

// Capability-based for security effects
fn secure_op(cap: lin Capability<Crypto>) -> Hash / { }
  // Capability consumed, no lingering effects

// Effect masking for encapsulation
fn public_api() -> Result / { }
  internal_with_effects() masked { State, Log }
```

---

## 9. CONCLUSION

For TERAS-LANG, a hybrid approach combining:

1. **Row-polymorphic core** for general effect tracking
2. **Capability semantics** for security-critical effects
3. **Purity distinction** for optimization and verification
4. **Linear integration** for resource management

This combination achieves:
- Compile-time effect safety
- Zero-cost for common patterns
- Security property encoding
- Formal verification support

---

**Document Checksum (SHA-256):** To be computed on final version  
**Related Documents:** A-11 Survey, A-11 Decision  
**Next Session:** A-12 (Region Types)
