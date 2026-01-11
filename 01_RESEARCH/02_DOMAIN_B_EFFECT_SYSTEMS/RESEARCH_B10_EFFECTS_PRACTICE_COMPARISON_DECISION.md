# TERAS-LANG Research Comparison & Decision B-10: Effects in Practice

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B10-COMPARISON-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-10 |
| Domain | B: Effect Systems |
| Status | **APPROVED** |

---

## 1. Production Systems Comparison

| System | Maturity | Performance | Ecosystem | Typing |
|--------|----------|-------------|-----------|--------|
| Koka | Research+ | Excellent | Small | Full |
| OCaml 5 | Production | Good | Large | None |
| effectful | Production | Excellent | Medium | Partial |
| polysemy | Production | Fair | Medium | Full |
| Eff | Research | Poor | Tiny | Full |

---

## 2. Decision

### Decision Statement

**TERAS-LANG SHALL:**

1. **Prioritize production-readiness** from day one
2. **Invest heavily in tooling** (IDE, profiler, debugger)
3. **Provide standard handlers** for common effects
4. **Support gradual adoption** via interop
5. **Optimize common patterns** to zero/near-zero cost
6. **Create comprehensive documentation** with examples

### Architecture Decision ID: `TERAS-ARCH-B10-PRA-001`

### Status: **APPROVED**

---

## 3. Standard Effects Library

```rust
// TERAS standard effects (built-in)

// I/O Effects
effect Console { print, println, read_line }
effect FileRead { read_file, read_dir }
effect FileWrite { write_file, create_dir }
effect Network { connect, listen, request }

// State Effects  
effect State<S> { get, put, modify }
effect Reader<R> { ask, local }
effect Writer<W: Monoid> { tell, listen }

// Control Effects
effect Exception<E> { throw, catch }
effect Async { spawn, await_, yield_ }
effect Choice { choose, fail }

// Security Effects (TERAS-specific)
effect Audit { log, with_context }
effect Capability<C> { require, attenuate }
effect Taint<S> { mark, check, propagate }
effect Crypto { sign, verify, encrypt, decrypt }
```

---

## 4. Production Handler Library

```rust
// Standard production handlers

// File I/O with sandboxing
handler sandboxed_file_handler(root: Path) for FileRead + FileWrite

// Async with Tokio backend
handler tokio_async_handler for Async

// Database with connection pooling
handler postgres_handler(pool: PgPool) for Database

// Audit with blockchain backend
handler secure_audit_handler(chain: AuditChain, hsm: HSM) for Audit

// Capability with HSM-backed tokens
handler hsm_capability_handler(hsm: HSM) for Capability<_>
```

---

## 5. Tooling Requirements

| Tool | Priority | Purpose |
|------|----------|---------|
| LSP extension | Critical | Effect type display |
| Effect profiler | High | Performance analysis |
| Handler debugger | High | Step through handlers |
| Migration tool | Medium | Legacy code conversion |
| Documentation gen | Medium | Effect docs from code |

---

## 6. Adoption Strategy

```
TERAS Effect Adoption Path:

Week 1-2: Learn
├── Read effect tutorial
├── Complete exercises
└── Build simple handler

Week 3-4: Apply
├── Add effects to one module
├── Write test handlers
└── Measure performance

Month 2: Expand
├── Migrate more code
├── Create custom effects
└── Optimize hot paths

Month 3+: Master
├── Full codebase coverage
├── Advanced patterns
└── Contribute handlers
```

---

*Architecture Decision Record for TERAS-LANG effects in practice.*
