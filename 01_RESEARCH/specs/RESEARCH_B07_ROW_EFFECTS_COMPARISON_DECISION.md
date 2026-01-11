# TERAS-LANG Research Comparison B-07: Row-Polymorphic Effects

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B07-COMPARISON |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-07 |
| Domain | B: Effect Systems |
| Status | Complete |

---

## 1. Comparison Matrix

| Feature | Koka Rows | Links Rows | Set-Based | TERAS Target |
|---------|-----------|------------|-----------|--------------|
| Row variables | ✓ | ✓ | ✗ | ✓ |
| Presence/absence | Implicit | Explicit | N/A | Explicit |
| Scoped labels | ✓ | ✗ | ✗ | ✓ |
| Row kinds | ✓ | ✗ | ✗ | ✓ |
| Unification | Full | Full | Simple | Full |
| Performance | Good | Moderate | Good | Target: Good |

---

## 2. Decision

**ADOPT Koka-style row polymorphism** with:
1. Explicit row variables with `| ε` syntax
2. Scoped labels for handler matching
3. Row kind system for duplicate prevention
4. Evidence-based compilation

---

# TERAS-LANG Architecture Decision B-07: Row-Polymorphic Effects

## Decision Statement

**TERAS-LANG SHALL IMPLEMENT** row-polymorphic effect types following Koka's design:

1. **Row variables** for effect polymorphism
2. **Scoped labels** for effect instance identity
3. **Row kinds** for sound typing
4. **Presence/absence** tracking where needed
5. **Evidence passing** compilation strategy

### Architecture Decision ID: `TERAS-ARCH-B07-ROW-001`

### Status: **APPROVED**

---

## Design

```rust
// Effect row with variable
fn polymorphic<ε>(f: () -[State<i32> | ε]-> A) -[State<i32> | ε]-> A

// Closed row
fn pure_state() -[State<i32>]-> i32

// Empty row (pure)
fn completely_pure() -[]-> i32
```

---

*Architecture Decision Record for TERAS-LANG row-polymorphic effects.*
