# TERAS-LANG Research Comparison & Decision C-01: IFC Foundations

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C01-COMPARISON-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-01 |
| Domain | C: Information Flow Control |
| Status | **APPROVED** |

---

## 1. IFC Approach Comparison

| Approach | Precision | Usability | Performance | TERAS Fit |
|----------|-----------|-----------|-------------|-----------|
| Static IFC | High | Medium | Excellent | ✓✓ |
| Dynamic IFC | Medium | High | Medium | ✓ |
| Hybrid | High | High | Good | ✓✓ |
| DLM | Excellent | Medium | Good | ✓✓ |

---

## 2. Language Comparison

| Language | Label Model | Inference | Production | TERAS Lessons |
|----------|-------------|-----------|------------|---------------|
| Jif | DLM | Partial | Research | Principals model |
| FlowCaml | Simple | Full | Research | ML integration |
| LIO | Simple | N/A | Production | Monadic approach |
| Paragon | DLM | Full | Research | Parallelism |

---

## 3. Decision

### Decision Statement

**TERAS-LANG SHALL IMPLEMENT:**

1. **Static IFC** as primary enforcement mechanism
2. **DLM-style labels** with principals and readers
3. **Label inference** for internal code
4. **Explicit labels** at API boundaries
5. **Noninterference guarantee** (termination-insensitive)
6. **Integration with effect system** (IFC as coeffect)

### Architecture Decision ID: `TERAS-ARCH-C01-IFC-001`

### Status: **APPROVED**

---

## 4. TERAS Security Lattice

```rust
// Five-level lattice with compartments
enum SecurityLevel {
    Public,       // ⊥
    Internal,
    Confidential,
    Secret,
    TopSecret,    // ⊤
}

// Label with DLM features
struct Label {
    level: SecurityLevel,
    owner: Principal,
    readers: Set<Principal>,
    compartments: Set<Compartment>,
}
```

---

## 5. Integration with Effects

IFC integrates as coeffect (B-03 decision):
- Clearance as coeffect requirement
- Security level checking at compile time
- Effect handlers can declassify with authority

---

*Architecture Decision Record for TERAS-LANG IFC foundations.*
