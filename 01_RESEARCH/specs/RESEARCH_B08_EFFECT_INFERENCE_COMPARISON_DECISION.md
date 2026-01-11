# TERAS-LANG Research Comparison & Decision B-08: Effect Inference

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B08-COMPARISON-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-08 |
| Domain | B: Effect Systems |
| Status | **APPROVED** |

---

## 1. Comparison

| System | Full Inference | Row Support | Complexity | Errors |
|--------|---------------|-------------|------------|--------|
| Koka | âœ“âœ“ | Full rows | Near-linear | Good |
| Links | âœ“ | Rows | Linear | Fair |
| Eff | âœ“ | Sets | Linear | Good |
| Frank | âœ“ | Implicit | Higher | Fair |
| Effekt | âœ“ | Partial | Linear | Good |

---

## 2. Decision

### Decision Statement

**TERAS-LANG SHALL IMPLEMENT** effect inference with:

1. **Full row-polymorphic inference** (Koka-style)
2. **Bidirectional checking** for annotated code
3. **Modular inference** for separate compilation
4. **Blame tracking** for error messages
5. **Incremental solving** for IDE integration

### Architecture Decision ID: `TERAS-ARCH-B08-INF-001`

### Status: **APPROVED**

---

## 3. Implementation

```rust
// Inference entry point
fn infer_function(func: &Function) -> Result<EffectSignature, InferError> {
    // 1. Generate constraints
    let (ty, eff, constraints) = infer_effects(&func.body, &func.context);
    
    // 2. Solve constraints
    let subst = solve_constraints(constraints)?;
    
    // 3. Apply substitution
    let final_ty = subst.apply(ty);
    let final_eff = subst.apply(eff);
    
    // 4. Generalize
    let generalized = generalize(final_ty, final_eff, &func.context);
    
    Ok(generalized)
}
```

---

## 4. Error Messages

```
// Example error
error[E0401]: unhandled effect `FileWrite`
  --> src/main.rs:42:5
   |
42 |     write_file(path, data);
   |     ^^^^^^^^^^^^^^^^^^^^^ `FileWrite` effect not handled
   |
   = note: effect originates from `std::fs::write_file`
   = help: add handler: `handle file_handler { ... }`
```

---

*Architecture Decision Record for TERAS-LANG effect inference.*
