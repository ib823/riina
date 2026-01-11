# TERAS-LANG Architecture Decision B-01: Algebraic Effects

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B01-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-01 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL ADOPT** algebraic effects with handlers as the primary abstraction for computational effects, implementing:

1. **Row-polymorphic effect types** (Koka-style)
2. **Evidence passing compilation** for near-zero overhead
3. **Deep handlers by default** with shallow available
4. **First-class handlers** as values
5. **Scoped effect instances** for security isolation
6. **Built-in security effects** (Audit, Capability, Taint, Crypto)
7. **Linear effect integration** for resource-safe effects

### 1.2 Architecture Decision ID

`TERAS-ARCH-B01-AEF-001`

### 1.3 Status

**APPROVED** â€” Ratified for TERAS-LANG implementation

---

## 2. Context and Requirements

### 2.1 Why Algebraic Effects for TERAS

| Challenge | Algebraic Effect Solution |
|-----------|--------------------------|
| Side effect tracking | Effect types make effects explicit |
| Security auditing | Audit effect captures all operations |
| Capability control | Capability effects enforce permissions |
| Testability | Handlers mock effects for testing |
| Modularity | Effects compose independently |
| Performance | Evidence passing eliminates overhead |

### 2.2 Requirements

| ID | Requirement | Priority |
|----|-------------|----------|
| AEF-01 | Compile-time effect safety | Critical |
| AEF-02 | Zero-cost for common patterns | Critical |
| AEF-03 | Row-polymorphic effect types | Critical |
| AEF-04 | Effect inference | High |
| AEF-05 | Handler composition | High |
| AEF-06 | Security effect integration | Critical |
| AEF-07 | Linear effect tracking | High |
| AEF-08 | Scoped effect instances | High |

---

## 3. Decision Details

### 3.1 Effect Syntax

```rust
// Effect declaration
effect State<S> {
    fn get() -> S;
    fn put(s: S) -> ();
}

effect Exn<E> {
    fn raise(e: E) -> !;  // ! = never returns normally
}

effect Async {
    fn spawn<A>(f: () -[Async]-> A) -> Task<A>;
    fn await<A>(t: Task<A>) -> A;
}

// Using effects
fn counter() -[State<i32>]-> i32 {
    let x = State::get();
    State::put(x + 1);
    x
}
```

### 3.2 Effect Type System

```
Effect Row Syntax:
    Îµ ::= âŸ¨âŸ©                    // empty
        | âŸ¨Eâ‚, Eâ‚‚, ... | ÏâŸ©     // effects + row variable
        | Ï                      // row variable

Function Type:
    A -[Îµ]-> B                   // function with effects Îµ

Effect Typing Rules:

    Î“ âŠ¢ e : A    A pure
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e : A ! âŸ¨âŸ©

    E.op : A â†’ B âˆˆ E
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ E::op : A -[âŸ¨E | ÏâŸ©]-> B

    Î“ âŠ¢ e : A -[Îµâ‚]-> B    Î“ âŠ¢ v : A
    Îµâ‚ âŠ† Îµâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e(v) : B ! Îµâ‚‚
```

### 3.3 Handler Syntax

```rust
// Basic handler
handler state_handler<S>(initial: S) for State<S> -> (A, S) {
    var current = initial;
    
    return(x) => (x, current),
    
    get() resume => {
        resume(current)
    },
    
    put(s) resume => {
        current = s;
        resume(())
    }
}

// Using handlers
fn main() -> (i32, i32) {
    handle state_handler(0) {
        counter();
        counter();
        counter();
        State::get()
    }
    // Returns: (2, 3)
}
```

### 3.4 Effect Row Polymorphism

```rust
// Polymorphic over effects
fn map<A, B, E>(f: A -[E]-> B, xs: List<A>) -[E]-> List<B> {
    match xs {
        Nil => Nil,
        Cons(x, rest) => Cons(f(x), map(f, rest))
    }
}

// Effect composition
fn logged_counter() -[State<i32>, Log]-> i32 {
    Log::info("incrementing counter");
    counter()
}

// Effect row extension (subtyping)
fn use_state<E>(f: () -[State<i32>]-> i32) -[State<i32> | E]-> i32 {
    f()
}
```

### 3.5 Evidence Passing Compilation

```rust
// Source
fn foo() -[State<i32>]-> i32 {
    State::get() + 1
}

// Compiled (tail-resumptive optimization)
fn foo_compiled(ev: &Evidence<State<i32>>) -> i32 {
    ev.get() + 1  // Direct call, no continuation
}

// Source (non-tail-resumptive)
fn bar() -[Choose]-> i32 {
    let x = Choose::flip();
    let y = Choose::flip();
    if x { 1 } else { 0 } + if y { 2 } else { 0 }
}

// Compiled (continuation-passing)
fn bar_compiled(ev: &Evidence<Choose>, k: Continuation<i32>) {
    ev.flip(|x| {
        ev.flip(|y| {
            let result = if x { 1 } else { 0 } + if y { 2 } else { 0 };
            k.resume(result)
        })
    })
}
```

### 3.6 Deep vs Shallow Handlers

```rust
// Deep handler (default) - recursive handling
handler all_choices for Choose -> List<A> {
    return(x) => vec![x],
    flip() resume => {
        // resume is ALSO handled by this handler
        let trues = resume(true);
        let falses = resume(false);
        trues.concat(falses)
    }
}

// Shallow handler - one-shot
shallow_handler first_choice for Choose -> Option<A> {
    return(x) => Some(x),
    flip() resume => {
        // resume is NOT handled - must re-handle manually
        resume(true)  // Just pick true, don't recurse
    }
}
```

### 3.7 Scoped Effect Instances

```rust
// Effect instances with identity
effect Resource<R> instance {
    fn acquire() -> R;
    fn release(r: R) -> ();
}

// Scoped handling
fn with_file<A>(path: &str, f: () -[Resource<File>]-> A) -> A {
    let instance = Resource::new_instance();
    handle instance {
        return(x) => x,
        acquire() resume => {
            let file = File::open(path);
            let result = resume(file);
            file.close();
            result
        },
        release(file) resume => {
            file.close();
            resume(())
        }
    } {
        f()
    }
}

// Cannot leak across instance boundaries
fn bad_leak() {
    let leaked: File;
    with_file("a.txt", || {
        leaked = Resource::acquire();  // ERROR: leaked escapes scope
    });
}
```

---

## 4. Security Effects

### 4.1 Audit Effect

```rust
// Built-in audit effect
effect Audit {
    fn log(level: Level, event: AuditEvent) -> ();
    fn get_context() -> AuditContext;
    fn with_context<A>(ctx: AuditContext, f: () -[Audit]-> A) -> A;
}

// Secure audit handler
handler secure_audit_handler(sink: AuditSink) for Audit {
    thread_local context: AuditContext = AuditContext::default();
    
    return(x) => x,
    
    log(level, event) resume => {
        let entry = AuditEntry {
            timestamp: Time::now_monotonic(),
            context: context.clone(),
            level,
            event,
        };
        sink.write_tamper_evident(entry);
        resume(())
    },
    
    get_context() resume => {
        resume(context.clone())
    },
    
    with_context(new_ctx, f) resume => {
        let old = context;
        context = new_ctx;
        let result = f();
        context = old;
        resume(result)
    }
}
```

### 4.2 Capability Effect

```rust
// Capability-gated operations
effect Capability<C: Cap> {
    fn require() -> Token<C>;
}

// Usage
fn read_file(path: &str) -[Capability<FileRead>]-> Bytes {
    let _token = Capability::<FileRead>::require();
    // Now allowed to read
    fs::read(path)
}

// Handler checks permissions
handler capability_handler<C: Cap>(perms: CapabilitySet) for Capability<C> {
    return(x) => x,
    require() resume => {
        if perms.contains(C) {
            resume(Token::new())
        } else {
            raise CapabilityDenied(C)
        }
    }
}
```

### 4.3 Taint Effect

```rust
// Information flow tracking
effect Taint<S: Source> {
    fn taint<A>(value: A) -> Tainted<S, A>;
    fn check<A>(value: A) -> Option<S>;
}

// Handler with taint map
handler taint_handler for Taint<S> {
    taint_map: Map<ObjectId, Set<Source>> = Map::new();
    
    return(x) => x,
    
    taint(value) resume => {
        let id = object_id(&value);
        taint_map.insert(id, Set::singleton(S));
        resume(Tainted::new(value))
    },
    
    check(value) resume => {
        let id = object_id(&value);
        resume(taint_map.get(&id))
    }
}
```

### 4.4 Crypto Effect

```rust
// Cryptographic operations (HSM-backed)
effect Crypto {
    fn random_bytes(n: usize) -> Bytes;
    fn encrypt(key: KeyHandle, plaintext: Bytes) -> Ciphertext;
    fn decrypt(key: KeyHandle, ciphertext: Ciphertext) -> Result<Bytes, CryptoError>;
    fn sign(key: SigningKeyHandle, message: Bytes) -> Signature;
    fn verify(key: VerifyKeyHandle, message: Bytes, sig: Signature) -> bool;
}

// HSM handler - keys never leave hardware
handler hsm_handler(hsm: HsmConnection) for Crypto {
    return(x) => x,
    
    random_bytes(n) resume => {
        resume(hsm.generate_random(n))
    },
    
    encrypt(key, plaintext) resume => {
        resume(hsm.encrypt(key, plaintext))
    },
    
    decrypt(key, ciphertext) resume => {
        resume(hsm.decrypt(key, ciphertext))
    },
    
    sign(key, message) resume => {
        resume(hsm.sign(key, message))
    },
    
    verify(key, message, sig) resume => {
        resume(hsm.verify(key, message, sig))
    }
}
```

---

## 5. Integration with Type System

### 5.1 Linear Effects

```rust
// Linear resources in effects
effect LinearFile {
    fn open(path: &str) -> lin File;
    fn read(file: &lin File) -> Bytes;
    fn close(file: lin File) -> ();
}

// Handler tracks linear usage
handler linear_file_handler for LinearFile {
    return(x) => x,
    
    open(path) resume => {
        let file = lin File::open_raw(path);
        resume(file)
    },
    
    read(file) resume => {
        resume(file.read_bytes())
    },
    
    close(file) resume => {
        drop(file);  // Linear resource consumed
        resume(())
    }
}
```

### 5.2 Refined Effects

```rust
// Effects with refinements
effect BoundedState<S: Ord, lo: S, hi: S> {
    fn get() -> { x: S | lo <= x && x <= hi };
    fn put(s: { x: S | lo <= x && x <= hi }) -> ();
}

// Refinements propagate through handlers
handler bounded_state_handler<S, lo, hi>(init: { x: S | lo <= x && x <= hi }) 
    for BoundedState<S, lo, hi> 
{
    var current: { x: S | lo <= x && x <= hi } = init;
    
    return(x) => x,
    get() resume => resume(current),
    put(s) resume => { current = s; resume(()) }
}
```

### 5.3 Effect with Session Types

```rust
// Protocol-following effects
effect Session<P: Protocol> {
    fn send<A>(a: A) -> () where P: Sends<A>;
    fn recv<A>() -> A where P: Receives<A>;
    fn choose<L>() -> () where P: Offers<L>;
    fn branch() -> BranchChoice<P::Branches>;
}

// Handler ensures protocol compliance
handler session_handler<P: Protocol>(channel: Channel) for Session<P> {
    // Type system ensures operations match protocol P
    ...
}
```

---

## 6. Performance Guarantees

### 6.1 Compilation Tiers

| Pattern | Compilation | Overhead |
|---------|-------------|----------|
| Tail-resumptive | Direct call | 0% |
| Single resumption | Inline | ~5% |
| Multi-shot | CPS transform | 20-50% |
| Nested handlers | Evidence chain | 5-10% |

### 6.2 Optimization Passes

```
Effect Optimization Pipeline:
1. Effect inference (fill row variables)
2. Handler inlining (small handlers)
3. Tail-resumptive detection
4. Evidence specialization (monomorphize)
5. Continuation elimination (when possible)
6. Dead effect elimination
7. Effect fusion (combine adjacent)
```

### 6.3 Benchmarks Targets

| Operation | Target |
|-----------|--------|
| Tail-resumptive effect | 0 cycles overhead |
| Handler installation | < 50 cycles |
| Continuation capture | < 500 cycles |
| Evidence lookup | < 10 cycles |

---

## 7. Integration with Previous Decisions

### 7.1 Effect Rows (A-11)

This decision implements the effect row system decided in A-11:
- Row polymorphism with presence/absence
- Effect subtyping via row extension
- Row variables for polymorphic effects

### 7.2 Linear Types (A-04)

Effects integrate with linearity:
- Linear effects (must be handled exactly once)
- Affine effects (at most once)
- Linear resources in effect operations

### 7.3 Type-Level Computation (A-18)

Effect types participate in type-level computation:
- Effect composition at type level
- Effect difference/subtraction
- Type-level effect predicates

---

## 8. Implementation Roadmap

### 8.1 Phases

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Core effects | 6 weeks | Basic effects, handlers |
| 2. Row types | 4 weeks | Row polymorphism |
| 3. Inference | 4 weeks | Effect inference |
| 4. Evidence passing | 6 weeks | Compilation |
| 5. Optimization | 4 weeks | Performance opts |
| 6. Security effects | 4 weeks | Built-in effects |
| **Total** | **28 weeks** | Complete effect system |

### 8.2 Milestones

| Milestone | Week | Deliverable |
|-----------|------|-------------|
| M1 | 6 | Basic effects working |
| M2 | 10 | Row polymorphism |
| M3 | 14 | Full inference |
| M4 | 20 | Evidence compilation |
| M5 | 28 | Production ready |

---

## 9. Validation Criteria

### 9.1 Correctness

- [ ] Effect safety theorem proved
- [ ] Handler typing sound
- [ ] Evidence passing correct
- [ ] All security effects verified

### 9.2 Performance

- [ ] Tail-resumptive: 0 overhead
- [ ] Handler install: < 50 cycles
- [ ] Benchmark suite passes

### 9.3 Usability

- [ ] Clear error messages
- [ ] Effect inference works
- [ ] Security effects documented

---

## 10. What We're NOT Using

### 10.1 Rejected: Untyped Effects (OCaml 5 style)

**Reason**: No compile-time effect safety. Critical for TERAS security.

### 10.2 Rejected: Monads Only

**Reason**: Monad transformers too cumbersome. Effect composition natural with algebraic effects.

### 10.3 Rejected: Exception-based

**Reason**: Cannot resume after exception. Limits handler flexibility.

### 10.4 Rejected: Set-based Effects (Eff style)

**Reason**: No effect polymorphism. Row types more expressive.

---

## 11. References

1. Plotkin, G., & Pretnar, M. (2009). "Handlers of Algebraic Effects"
2. Leijen, D. (2017). "Type Directed Compilation of Row-typed Algebraic Effects"
3. BrachthÃ¤user, J., et al. (2020). "Effects as Capabilities"
4. TERAS Architecture Decisions A-04, A-11, A-18

---

## 12. Approval

| Role | Name | Date | Signature |
|------|------|------|-----------|
| TERAS Architect | [Pending] | | |
| Language Lead | [Pending] | | |
| Security Lead | [Pending] | | |

---

*Architecture Decision Record for TERAS-LANG algebraic effects.*
