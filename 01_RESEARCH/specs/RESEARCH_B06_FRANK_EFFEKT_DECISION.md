# TERAS-LANG Architecture Decision B-06: Frank/Effekt Synthesis

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B06-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-06 |
| Domain | B: Effect Systems |
| Status | **APPROVED** |

---

## 1. Decision

**TERAS-LANG SHALL:**

1. **Adopt Effekt's lexical scoping** for effect capabilities
2. **Adopt Effekt's second-class continuations** for resource safety
3. **Adopt Frank's operator-as-interface** syntax style
4. **Support bidirectional effects** for protocol modeling (Frank-inspired)
5. **NOT adopt** Frank's full first-class continuations (security risk)

### 1.1 Architecture Decision ID

`TERAS-ARCH-B06-FRE-001`

---

## 2. Key Adoptions

### 2.1 Scoped Handlers (from Effekt)

```rust
// Capabilities lexically scoped - cannot escape
scoped handler secret_handler for SecretAccess {
    // Continuation bound to this scope
}
```

### 2.2 Bidirectional Effects (from Frank)

```rust
// Protocol effects flow both directions
effect Protocol {
    send: Message -> (),  // Outgoing
    recv: () -> Message   // Incoming
}
```

---

## 3. References

1. Lindley et al. (2017). "Do Be Do Be Do"
2. BrachthÃ¤user et al. (2020). "Effects as Capabilities"

---

*Architecture Decision Record for TERAS-LANG Frank/Effekt synthesis.*
