# TERAS-LANG Architecture Decision B-04: Effect Handlers

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B04-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-04 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL IMPLEMENT** effect handlers with:

1. **Deep handlers by default** with shallow available
2. **Evidence passing compilation** for tail-resumptive operations
3. **Multi-shot continuations** via opt-in annotation
4. **Scoped handlers** for security-critical effects
5. **Linear continuation mode** for resource safety
6. **First-class handlers** as values
7. **Parameterized handlers** with local state
8. **Named effect instances** for multiple same-effect contexts

### 1.2 Architecture Decision ID

`TERAS-ARCH-B04-HDL-001`

### 1.3 Status

**APPROVED** — Ratified for TERAS-LANG implementation

---

## 2. Handler Design

### 2.1 Handler Syntax

```rust
// Basic handler
handler state_handler<S>(init: S) for State<S> -> (A, S) {
    var current: S = init;
    
    return(x) => (x, current),
    
    get() resume => resume(current),
    
    put(s) resume => {
        current = s;
        resume(())
    }
}

// Scoped handler (continuation cannot escape)
scoped handler resource_handler for FileResource {
    open(path) resume => {
        let file = File::open(path)?;
        let result = resume(file);
        file.close();
        result
    }
}

// Multi-shot handler
multishot handler choice_handler for Choice -> List<A> {
    return(x) => vec![x],
    
    choose() resume => {
        let trues = resume(true);
        let falses = resume(false);
        trues.concat(falses)
    }
}
```

### 2.2 Handler Application

```rust
// Using handlers
fn example() -> (i32, i32) {
    handle state_handler(0) {
        let x = State::get();
        State::put(x + 1);
        State::get()
    }
}

// Nested handlers
fn nested() -> Result<(i32, i32), Error> {
    handle error_handler {
        handle state_handler(0) {
            // Both State and Error available
        }
    }
}

// Named instances
fn multi_state() -> (i32, String) {
    handle["counter"] state_handler(0) {
        handle["name"] state_handler("".to_string()) {
            State["counter"]::put(42);
            State["name"]::put("Alice".to_string());
            (State["counter"]::get(), State["name"]::get())
        }
    }
}
```

### 2.3 Continuation Modes

```rust
// Default: one-shot, optimized
handler default_handler for E {
    op(x) resume => resume(result)  // resume called once
}

// Linear: enforced one-shot
handler linear_handler for E {
    op(x) resume: lin => resume(result)  // MUST call exactly once
}

// Multi-shot: explicit opt-in
multishot handler multi_handler for E {
    op(x) resume => {
        resume(a);  // First call
        resume(b);  // Second call OK
    }
}
```

---

## 3. Compilation Strategy

### 3.1 Tail-Resumptive Optimization

```rust
// Source
handler state(init) for State<S> {
    get() resume => resume(current)    // Tail-resumptive
    put(s) resume => { current = s; resume(()) }  // Tail-resumptive
}

// Compiled (evidence passing)
struct StateEvidence<S> {
    current: Cell<S>,
}

impl<S> StateOps<S> for StateEvidence<S> {
    fn get(&self) -> S {
        self.current.get()  // Direct call, no continuation
    }
    
    fn put(&self, s: S) {
        self.current.set(s);  // Direct call
    }
}
```

### 3.2 Non-Tail-Resumptive

```rust
// Source (multi-shot)
multishot handler choice for Choice -> List<A> {
    choose() resume => resume(true).concat(resume(false))
}

// Compiled (CPS)
fn choice_handler<A>(body: impl FnOnce(&ChoiceOps) -> A) -> Vec<A> {
    // Capture continuation, invoke multiple times
    // Full CPS transformation
}
```

---

## 4. Security Handlers

### 4.1 Audit Handler

```rust
scoped handler audit_handler(sink: AuditSink) for Audit {
    return(x) => { sink.flush(); x },
    
    log(level, event) resume => {
        sink.write(AuditEntry::new(level, event));
        resume(())
    }
}
```

### 4.2 Capability Handler

```rust
scoped handler capability_handler(caps: CapSet) for Capability {
    require(cap) resume => {
        if caps.contains(cap) {
            resume(Token::new(cap))
        } else {
            panic!("Capability denied: {:?}", cap)
        }
    }
}
```

---

## 5. Implementation Roadmap

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Basic handlers | 4 weeks | Deep handlers, return clause |
| 2. Evidence passing | 4 weeks | Tail-resumptive optimization |
| 3. Scoped handlers | 2 weeks | Linear continuations |
| 4. Multi-shot | 3 weeks | CPS fallback |
| 5. Named instances | 2 weeks | Multiple same-effect |
| **Total** | **15 weeks** | Complete handler system |

---

## 6. What We're NOT Using

### 6.1 Rejected: Shallow-Only (OCaml 5 style)

**Reason**: Deep handlers more ergonomic for most use cases.

### 6.2 Rejected: CPS-Only Compilation

**Reason**: Too slow; evidence passing critical for performance.

### 6.3 Rejected: Unscoped Handlers

**Reason**: Security requires preventing continuation escape.

---

## 7. References

1. Plotkin & Pretnar (2009). "Handlers of Algebraic Effects"
2. Leijen (2017). "Type Directed Compilation of Row-typed Algebraic Effects"
3. TERAS Architecture Decisions B-01, B-03

---

*Architecture Decision Record for TERAS-LANG effect handlers.*
