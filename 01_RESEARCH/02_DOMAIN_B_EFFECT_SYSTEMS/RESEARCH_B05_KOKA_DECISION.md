# TERAS-LANG Architecture Decision B-05: Koka-Inspired Design

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B05-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-05 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL ADOPT** Koka's effect system design as the primary foundation, specifically:

1. **Row-polymorphic effect types** with row variables
2. **Evidence passing compilation** for tail-resumptive handlers
3. **Effect inference algorithm** for ergonomic programming
4. **Named effect instances** for multiple contexts
5. **Scoped handlers** with controlled continuation scope

**TERAS-LANG SHALL EXTEND** Koka's design with:
1. Linear type integration (A-04)
2. Coeffect system (B-03)
3. Built-in security effects
4. Refinement type integration (A-08)

### 1.2 Architecture Decision ID

`TERAS-ARCH-B05-KOKA-001`

### 1.3 Status

**APPROVED** — Ratified for TERAS-LANG implementation

---

## 2. Rationale

### 2.1 Why Koka as Foundation

| Koka Strength | TERAS Benefit |
|---------------|---------------|
| Row polymorphism | Flexible effect composition |
| Evidence passing | Near-zero overhead |
| Effect inference | Developer productivity |
| Proven design | Reduced research risk |
| Active development | Learning from ongoing work |

### 2.2 Why Extensions Needed

| Gap | TERAS Need | Solution |
|-----|------------|----------|
| No linear types | Resource safety | Integrate A-04 |
| No coeffects | Context tracking | Integrate B-03 |
| Manual security | Security ergonomics | Built-in effects |
| No refinements | Input validation | Integrate A-08 |

---

## 3. Design Adoption

### 3.1 Effect Row Syntax (from Koka)

```rust
// TERAS adopts Koka-style row syntax
fn foo() -[State<i32>, Exn | ε]-> i32 {
    //      ^^^^^^^^^^^^^^^^^^
    //      effect row with variable ε
}

// Row polymorphism
fn map<A, B, E>(f: A -[E]-> B, xs: List<A>) -[E]-> List<B> {
    // E is effect row variable
}
```

### 3.2 Evidence Passing (from Koka)

```rust
// Tail-resumptive compiled to direct calls
// Non-tail-resumptive uses selective CPS

// TERAS follows Koka's evidence passing strategy
handler state_handler<S>(init: S) for State<S> {
    get() resume => resume(current)  // Direct call
}
```

### 3.3 Extensions Beyond Koka

```rust
// Linear effects (not in Koka)
effect LinearFile {
    fn open(path: &str) -> lin File;
    fn close(file: lin File) -> ();  // Must be called
}

// Coeffects (not in Koka)
fn secure_op() -[Audit]-> Result @ {Clearance::Secret} {
    //                            ^^^^^^^^^^^^^^^^^^^^
    //                            coeffect (from B-03)
}

// Built-in security effects (manual in Koka)
effect Capability<C: Cap> {  // First-class in TERAS
    fn require() -> Token<C>;
}
```

---

## 4. Implementation Strategy

### 4.1 Phase 1: Core Koka Features

| Component | Duration | Source |
|-----------|----------|--------|
| Row types | 3 weeks | Koka design |
| Effect inference | 4 weeks | Koka algorithm |
| Evidence passing | 4 weeks | Koka compilation |
| Basic handlers | 3 weeks | Koka semantics |

### 4.2 Phase 2: TERAS Extensions

| Component | Duration | Source |
|-----------|----------|--------|
| Linear integration | 3 weeks | A-04 |
| Coeffect integration | 3 weeks | B-03 |
| Security effects | 4 weeks | TERAS design |
| Refinement integration | 3 weeks | A-08 |

---

## 5. References

1. Leijen, D. (2017). "Type Directed Compilation of Row-typed Algebraic Effects"
2. Koka Language: https://koka-lang.github.io/
3. TERAS Architecture Decisions A-04, A-08, B-03

---

*Architecture Decision Record for TERAS-LANG Koka-inspired effect system.*
