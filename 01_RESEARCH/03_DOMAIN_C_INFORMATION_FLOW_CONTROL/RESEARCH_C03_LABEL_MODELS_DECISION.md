# TERAS-LANG Architecture Decision C-03: Label Models

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C03-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-03 |
| Domain | C: Information Flow Control |
| Status | **APPROVED** |

---

## 1. Decision

### Decision Statement

**TERAS-LANG SHALL IMPLEMENT:**

1. **Five-level security lattice** (Public → TopSecret)
2. **Compartments** as sets for need-to-know
3. **DLM features** (owners, readers) where needed
4. **Combined confidentiality + integrity**
5. **Product-specific label presets**
6. **Label inference** with explicit boundaries

### Architecture Decision ID: `TERAS-ARCH-C03-LBL-001`

### Status: **APPROVED**

---

## 2. Label Structure

```rust
pub struct Label {
    level: SecurityLevel,        // 5-level lattice
    compartments: Set<String>,   // Compartmentalization
    integrity: IntegrityLevel,   // Trust level
    owner: Option<Principal>,    // DLM owner
    readers: Option<Set<Principal>>, // DLM readers
}
```

---

## 3. Rationale

| Feature | Rationale |
|---------|-----------|
| 5 levels | Matches common classification schemes |
| Compartments | Need-to-know isolation |
| Integrity | Prevent taint propagation |
| DLM | Decentralized authority |

---

*Architecture Decision Record for TERAS-LANG label models.*
