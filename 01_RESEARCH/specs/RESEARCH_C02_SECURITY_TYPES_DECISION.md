# TERAS-LANG Architecture Decision C-02: Security Type Systems

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C02-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-02 |
| Domain | C: Information Flow Control |
| Status | **APPROVED** |

---

## 1. Decision

### Decision Statement

**TERAS-LANG SHALL IMPLEMENT:**

1. **Labeled types** with syntax `T @ L` or `Labeled<L, T>`
2. **PC tracking** for implicit flow prevention
3. **Label polymorphism** with `âˆ€L. ...` quantification
4. **Label inference** for internal code
5. **Combined confidentiality + integrity** labels
6. **Subtyping** covariant in labels
7. **Integration** with effect system (B-01)

### Architecture Decision ID: `TERAS-ARCH-C02-STY-001`

### Status: **APPROVED**

---

## 2. Type Syntax

```rust
// Labeled type
type Secret<T> = T @ SecretLevel;

// Function with flow annotations
fn process(x: int @ High) -> int @ High { x }

// Label polymorphism
fn id<L: Label>(x: int @ L) -> int @ L { x }

// Combined labels
fn trusted_secret() -> int @ (Secret, Trusted) { 42 }
```

---

## 3. PC Tracking

```rust
// Implicit in control flow
if secret_bool {  // pc raised to Secret
    // All assignments here must be to Secret or higher
    public = 1;  // ERROR: implicit flow!
}
```

---

*Architecture Decision Record for TERAS-LANG security types.*
