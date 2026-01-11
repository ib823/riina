# TERAS-LANG Research Comparison & Decision B-09: Effect Subtyping

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B09-COMPARISON-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-09 |
| Domain | B: Effect Systems |
| Status | **APPROVED** |

---

## 1. Decision

### Decision Statement

**TERAS-LANG SHALL IMPLEMENT:**

1. **Row-based effect subtyping** with covariance
2. **Handler-based masking** to remove effects
3. **Effect tunneling** for unhandled effects
4. **Named instance masking** for multiple same-effect
5. **Effect lattice** with pure as bottom

### Architecture Decision ID: `TERAS-ARCH-B09-SUB-001`

### Status: **APPROVED**

---

## 2. Subtyping Rules

```rust
// Subtyping: fewer effects <: more effects
Pure <: [E | ε]                    // Pure is bottom
[E1 | ε] <: [E1, E2 | ε]          // Extension
[E | ε1] <: [E | ε2] if ε1 <: ε2  // Depth
```

## 3. Masking Semantics

```rust
// Handler masks its effect
handle state_handler(0) {
    body  // : A ! [State<i32> | ε]
}
// Result: A ! [ε]  (State masked)
```

---

*Architecture Decision Record for TERAS-LANG effect subtyping.*
