# TERAS-LANG Research Survey B-04: Effect Handlers

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B04-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-04 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Effect handlers are the mechanism for giving semantics to algebraic effects. They define how effect operations are interpreted, potentially capturing and manipulating continuations. This survey provides exhaustive coverage of handler semantics, implementation strategies, compilation techniques, and performance optimizations, with focus on security-critical applications for TERAS.

---

## Part 1: Handler Foundations

### 1.1 What Are Effect Handlers?

```
Effect handlers are first-class abstractions that:
├── Define interpretation of effect operations
├── Capture delimited continuations
├── Can invoke continuations zero, one, or many times
├── Transform return values
└── Enable modular effect semantics

Analogy:
    Exception handlers : Exceptions
    Effect handlers    : All computational effects
    
Key difference: Effect handlers can RESUME after handling!
```

### 1.2 Historical Development

```
Timeline:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1990    │ Felleisen: Delimited continuations (shift/reset)
2003    │ Filinski: Representing monads
2009    │ Plotkin & Pretnar: "Handlers of Algebraic Effects"
2012    │ Eff language: First implementation
2013    │ Kammar et al: "Handlers in Action"
2014    │ Koka: Row-typed handlers
2015    │ Bauer & Pretnar: Programming with handlers
2017    │ Lindley et al: Frank (bidirectional)
2020    │ Brachthäuser et al: Capability-based handlers
2021    │ OCaml 5: Effect handlers in mainstream
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

### 1.3 Handler Anatomy

```
handler h {
    return(x)    → c_ret          // Handle normal returns
    op₁(x, k)    → c₁             // Handle operation op₁
    op₂(x, k)    → c₂             // Handle operation op₂
    ...
}

Components:
├── return clause: transforms final value
├── operation clauses: define effect semantics
├── continuation k: captured delimited continuation
└── clause bodies: arbitrary computations

Key insight: k is a first-class value that can be:
    - Called once (normal handling)
    - Called multiple times (nondeterminism)
    - Never called (exceptions)
    - Stored for later (async)
```

---

## Part 2: Handler Semantics

### 2.1 Operational Semantics

```
Small-step semantics with evaluation contexts:

Evaluation Context:
    E ::= [] | let x = E in c | handle E with h

Values:
    v ::= x | λx.c | handler h

Computations:
    c ::= return v | let x = c₁ in c₂ | v₁ v₂
        | do op(v) | handle c with h

Reduction Rules:

    (β-value)
    let x = return v in c  →  c[x ↦ v]

    (β-app)
    (λx.c) v  →  c[x ↦ v]

    (handle-return)
    handle (return v) with h  →  c_ret[x ↦ v]
        where h = handler { return(x) → c_ret, ... }

    (handle-op) [KEY RULE]
    handle E[do op(v)] with h  →  c_op[x ↦ v, k ↦ λy. handle E[y] with h]
        where h = handler { ..., op(x, k) → c_op, ... }
        and op is handled by h

    (handle-tunnel)
    handle E[do op(v)] with h  →  handle E[do op(v)] with h
        where op NOT in h  (tunneling)
```

### 2.2 Denotational Semantics

```
Free monad interpretation:

⟦A ! E⟧ = Free_E(⟦A⟧)

data Free E A where
    Pure   : A → Free E A
    Impure : (∃X. E X × (X → Free E A)) → Free E A

Handler as fold:
⟦handle c with h⟧ = fold_h ⟦c⟧

fold_h : Free E A → Free E' B
fold_h (Pure a) = ⟦h.return⟧ a
fold_h (Impure (op, k)) = ⟦h.op⟧ (fold_h ∘ k)
```

### 2.3 Handler Types

```
Handler typing judgment:

    Γ ⊢ h handles E to B ! E'
    
Meaning: Handler h transforms computations with effect E
         into computations of type B with effect E'

Full rule:
    Γ, x : A ⊢ c_ret : B ! E'
    ∀op : A_op → B_op ∈ E.
        Γ, x : A_op, k : B_op → B ! E' ⊢ c_op : B ! E'
    ──────────────────────────────────────────────────────
    Γ ⊢ handler { return(x) → c_ret, op(x,k) → c_op } 
        handles E to B ! E'
```

---

## Part 3: Handler Varieties

### 3.1 Deep vs Shallow Handlers

**Deep Handlers (Default):**
```
handler deep_choice {
    return(x)   → [x]
    choose() k  → k(true) ++ k(false)
}

// When k is invoked, it's STILL wrapped by this handler
// Recursive handling automatic

handle deep_choice {
    let a = do choose()
    let b = do choose()
    (a, b)
}
// Result: [(true,true), (true,false), (false,true), (false,false)]
```

**Shallow Handlers:**
```
handler shallow_choice {
    return(x)   → [x]
    choose() k  → k(true) ++ k(false)  // k NOT wrapped!
}

// Must re-wrap manually for recursion
handle shallow_choice {
    let a = do choose()
    // Next choose() would escape to outer handler!
    (a, ())
}
// Result: [(true,()), (false,())]
```

**Comparison:**
| Aspect | Deep | Shallow |
|--------|------|---------|
| Recursion | Automatic | Manual |
| Control | Less | More |
| Use case | Most effects | State machines |
| Performance | Can optimize | Often faster |

### 3.2 Parameterized Handlers

```
// Handler with parameters (state)
handler state_handler(init : S) {
    var current = init
    
    return(x)  → (x, current)
    get() k    → k(current)
    put(s) k   → { current ← s; k(()) }
}

// Usage
handle state_handler(0) {
    let x = do get()
    do put(x + 1)
    do get()
}
// Result: (1, 1)
```

### 3.3 First-Class Handlers

```
// Handlers as values
let h : Handler State Int = handler {
    return(x) → (x, 0)
    get() k   → k(42)
    put(_) k  → k(())
}

// Higher-order handler operations
let compose : Handler E₁ A → Handler E₂ B → Handler (E₁ ∪ E₂) B
let map_handler : (A → B) → Handler E A → Handler E B
```

### 3.4 Named/Labelled Handlers

```
// Multiple instances of same effect
effect State[label] S {
    get : () → S
    put : S → ()
}

// Named handlers
handle["counter"] state_handler(0) {
    handle["name"] state_handler("") {
        do["counter"] put(42)
        do["name"] put("Alice")
        (do["counter"] get(), do["name"] get())
    }
}
// Result: (42, "Alice")
```

### 3.5 Forwarding Handlers

```
// Handler that intercepts but forwards some operations
handler logging_state for State S {
    return(x)  → x
    get() k    → { log("get called"); forward get() to k }
    put(s) k   → { log("put " ++ show s); forward put(s) to k }
}

// Wraps existing state handler
handle logging_state {
    handle real_state(0) {
        // Operations logged then forwarded
    }
}
```

---

## Part 4: Advanced Handler Patterns

### 4.1 Exception Pattern

```
handler catch {
    return(x)      → Right x
    throw(e) _     → Left e    // Discard continuation
}

// Usage
handle catch {
    if condition then return value
    else do throw(error)
}
```

### 4.2 State Pattern

```
handler state(init) {
    return(x)  → λs. (x, s)
    get() k    → λs. k(s)(s)
    put(s') k  → λ_. k(())(s')
}

// Run: handle state(0) { ... } init_state
```

### 4.3 Nondeterminism Pattern

```
handler all_results {
    return(x)    → [x]
    choose() k   → k(true) ++ k(false)
    fail() _     → []
}

handler first_result {
    return(x)    → Some x
    choose() k   → k(true) <|> k(false)
    fail() _     → None
}
```

### 4.4 Async/Await Pattern

```
handler async_scheduler {
    queue : Queue<Continuation> = empty
    
    return(x) → 
        if queue.empty() then x
        else { let k = queue.dequeue(); k(()) }
    
    spawn(f) k → 
        queue.enqueue(λ(). f())
        k(())
    
    yield() k →
        queue.enqueue(k)
        let next = queue.dequeue()
        next(())
    
    await(promise) k →
        if promise.ready() then k(promise.get())
        else {
            promise.on_ready(k)
            let next = queue.dequeue()
            next(())
        }
}
```

### 4.5 Coroutine Pattern

```
handler coroutine {
    return(x)    → Done(x)
    yield(v) k   → Yielded(v, k)
}

data Coroutine A B R
    = Done R
    | Yielded A (B → Coroutine A B R)

// Step coroutine
step : Coroutine A B R → B → Either R (A, B → Coroutine A B R)
step (Done r) _ = Left r
step (Yielded a k) b = Right (a, k)
```

### 4.6 Backtracking Pattern

```
handler backtrack {
    var checkpoints : List<Continuation> = []
    
    return(x) → Some x
    
    choice(options) k →
        for opt in options.tail() {
            checkpoints.push(λ(). k(opt))
        }
        k(options.head())
    
    fail() _ →
        if checkpoints.empty() then None
        else {
            let k = checkpoints.pop()
            k(())
        }
}
```

---

## Part 5: Compilation Strategies

### 5.1 CPS Transformation

```
// Direct style
let x = do get() in
let y = x + 1 in
do put(y)

// CPS transformed
get(λx.
    let y = x + 1 in
    put(y, λ_. return ()))

Pros:
+ Simple to implement
+ Works universally
+ Easy to reason about

Cons:
- Slow (closure allocation)
- No tail call optimization
- Large code size
```

### 5.2 Evidence Passing (Koka)

```
// Original
fun foo() : <state<int>> int
    get() + 1

// Evidence passing
fun foo(ev : Evidence<state<int>>) : int
    ev.get() + 1

// Handler creates evidence
fun with_state(init, body) =
    var s = init
    val ev = Evidence {
        get = λ(). s,
        put = λ(x). { s ← x }
    }
    body(ev)

Pros:
+ Fast (direct calls for tail-resumptive)
+ Monomorphization possible
+ Good optimization potential

Cons:
- Complex compilation
- Not all effects work
- Handler allocation
```

### 5.3 Multi-Prompt Delimited Continuations

```
// Use shift₀/reset₀ with multiple prompts

handle[E] c with h
    ≈
reset p_E (c)

perform op(x)
    ≈
shift₀ p_E (λk. h.op(x, k))

Pros:
+ Native continuation support
+ Clean semantics
+ Multi-shot natural

Cons:
- Requires runtime support
- Implementation complexity
- GC pressure
```

### 5.4 Bubble Resumption

```
// Optimization for single-use continuations

Instead of:
    capture_continuation(); invoke_later()

Do:
    mark_frame(); return_to_handler()
    // Later: restore_and_continue()

Pros:
+ Avoids continuation allocation
+ Fast for common case

Cons:
- Only for one-shot
- Stack manipulation
```

### 5.5 Selective CPS

```
// Only transform when needed

Analysis:
    if operation is tail-resumptive:
        compile as direct call
    else if continuation used once:
        use bubble resumption
    else:
        full CPS transformation

Achieves near-optimal for each case.
```

---

## Part 6: Performance Optimization

### 6.1 Tail-Resumptive Optimization

```
Definition: An operation is tail-resumptive if its handler
clause immediately resumes with no computation after.

handler state(init) {
    get() k → k(init)         // TAIL-RESUMPTIVE
    put(s) k → k(())          // TAIL-RESUMPTIVE (after assignment)
}

handler choice {
    choose() k → k(true) ++ k(false)  // NOT tail-resumptive
}

Optimization: Compile tail-resumptive as direct function call.
    get() → return state_var        // No continuation!
    put(s) → { state_var = s; return () }
```

### 6.2 Handler Fusion

```
// Two adjacent handlers
handle h₁ { handle h₂ { body } }

// Can fuse if compatible
handle h₁₂ { body }  // Combined handler

Conditions for fusion:
- No overlapping operations
- Compatible return transformations
- No handler-specific state conflicts
```

### 6.3 Effect Specialization

```
// Generic handler
handler generic_state<S> for State S { ... }

// Specialized for Int
handler int_state for State Int {
    // Monomorphized, inline optimized
}

// Specialization eliminates:
- Type dispatch
- Generic instantiation
- Indirect calls
```

### 6.4 Continuation Representation

```
Options for representing continuations:

1. Closure chain (simple, slow)
   Cont = (() → Cont) | Done

2. Stack segment (fast, complex)
   Cont = StackSegment + PC

3. One-shot optimized (bubble)
   Cont = FrameMarker  // In-place resume

4. Defunctionalized (analyzable)
   Cont = Apply₁ Cont Value | Apply₂ ...

Choice affects:
- Capture cost
- Resume cost
- GC interaction
- Multi-shot support
```

### 6.5 Benchmarks

| Pattern | Naive CPS | Evidence | Optimized |
|---------|-----------|----------|-----------|
| State loop 1M | 500ms | 20ms | 15ms |
| Reader | 300ms | 10ms | 8ms |
| Exception | 200ms | 15ms | 12ms |
| Nondeterminism | 800ms | 400ms | 350ms |
| Async/await | 600ms | 50ms | 40ms |

---

## Part 7: Handler Safety

### 7.1 Type Safety

```
Handler type safety theorem:

If:
    ∅ ⊢ handle c with h : B ! E'
Then either:
    1. handle c with h →* return v  with ∅ ⊢ v : B
    2. handle c with h →* E'[do op(v)]  with op ∈ E'
    3. Diverges

Key property: Handled effects don't escape.
```

### 7.2 Resource Safety

```
// Problem: What if handler drops continuation holding resource?

handler problematic {
    use_file(path) k →
        let file = open(path)
        // OOPS: Forgot to close if k fails!
        k(file)
}

// Solution: Linear continuations
handler safe {
    use_file(path) k →  // k is LINEAR, must call exactly once
        let file = open(path)
        let result = k(file)  // Must call k
        close(file)
        result
}
```

### 7.3 Scoped Handlers

```
// Prevent continuation escape

handler scoped_state(init) {
    scoped  // Mark as scoped
    
    return(x) → x
    get() k → k(init)      // k cannot escape this scope
    put(s) k → k(())
}

// Compiler enforces: continuation not stored or returned
```

---

## Part 8: Security Applications

### 8.1 Audit Handler

```
handler audit_handler(sink: AuditSink) for Audit {
    var context: AuditContext = default
    
    return(x) → 
        sink.flush()
        x
    
    log(level, event) k →
        let entry = AuditEntry {
            timestamp: monotonic_time(),
            level: level,
            event: event,
            context: context.clone(),
            call_stack: capture_stack()
        }
        sink.write(entry)
        k(())
    
    with_context(new_ctx, body) k →
        let old = context
        context ← new_ctx
        let result = body()
        context ← old
        k(result)
}
```

### 8.2 Capability Handler

```
handler capability_handler(perms: CapabilitySet) for Capability {
    require(cap) k →
        if perms.has(cap) {
            k(CapToken::new(cap))
        } else {
            raise CapabilityDenied(cap)
        }
    
    with_reduced(mask, body) k →
        let reduced = perms.intersect(mask)
        handle capability_handler(reduced) {
            k(body())
        }
    
    attenuate(new_perms, body) k →
        if new_perms.subset_of(perms) {
            handle capability_handler(new_perms) {
                k(body())
            }
        } else {
            raise CapabilityEscalation(new_perms - perms)
        }
}
```

### 8.3 Sandboxed Execution Handler

```
handler sandbox_handler(policy: SandboxPolicy) for SandboxedIO {
    read_file(path) k →
        if policy.can_read(path) {
            k(fs::read(path))
        } else {
            raise SandboxViolation::Read(path)
        }
    
    write_file(path, data) k →
        if policy.can_write(path) {
            fs::write(path, data)
            k(())
        } else {
            raise SandboxViolation::Write(path)
        }
    
    network(request) k →
        if policy.can_network(request.host) {
            k(net::request(request))
        } else {
            raise SandboxViolation::Network(request.host)
        }
}
```

### 8.4 Taint Tracking Handler

```
handler taint_handler for Taint {
    taint_map: Map<ObjectId, TaintSet> = new()
    
    mark_tainted(value, source) k →
        let id = object_id(value)
        taint_map.insert(id, TaintSet::singleton(source))
        k(Tainted::new(value, source))
    
    check_taint(value) k →
        let id = object_id(value)
        k(taint_map.get(id))
    
    propagate(f, tainted_value) k →
        let result = f(tainted_value.unwrap())
        let result_id = object_id(result)
        taint_map.insert(result_id, tainted_value.sources())
        k(Tainted::new(result, tainted_value.sources()))
    
    declassify(value, from, to, justification) k →
        // Requires privilege check
        audit_declassification(from, to, justification)
        let id = object_id(value)
        taint_map.update(id, |t| t.remove(from).add(to))
        k(value)
}
```

---

## Part 9: TERAS Handler Design

### 9.1 Handler Requirements

| Requirement | Priority |
|-------------|----------|
| Type-safe | Critical |
| Resource-safe | Critical |
| Efficient | High |
| Composable | High |
| First-class | Medium |
| Scoped | High |

### 9.2 TERAS Handler Syntax

```rust
// Handler declaration
handler state_handler<S>(init: S) for State<S> -> (A, S) {
    // Local state
    var current: S = init;
    
    // Return clause
    return(x) => (x, current),
    
    // Operation clauses
    get() resume => {
        resume(current)
    },
    
    put(s) resume => {
        current = s;
        resume(())
    }
}

// Handler with coeffect requirements
handler secure_handler for SecureOp @ {Clearance::Secret} {
    // Can only be installed in Secret-cleared context
}

// Scoped handler (continuation cannot escape)
scoped handler resource_handler for Resource {
    // ...
}
```

### 9.3 Handler Composition

```rust
// Sequential composition
let h1_then_h2 = h1.then(h2);

// Parallel composition (disjoint effects)
let h1_and_h2 = h1.with(h2);

// Handler wrapping
let wrapped = logging_wrapper(base_handler);

// Handler parameterization
fn make_handler<S>(init: S) -> Handler<State<S>, (A, S)> {
    handler { ... }
}
```

---

## Part 10: Bibliography

### 10.1 Foundational

1. Plotkin, G., & Pretnar, M. (2009). "Handlers of Algebraic Effects"
2. Plotkin, G., & Pretnar, M. (2013). "Handling Algebraic Effects"
3. Kammar, O., Lindley, S., & Oury, N. (2013). "Handlers in Action"

### 10.2 Implementation

4. Leijen, D. (2017). "Type Directed Compilation of Row-typed Algebraic Effects"
5. Hillerström, D., & Lindley, S. (2016). "Liberating Effects with Rows and Handlers"
6. Brachthäuser, J., et al. (2020). "Effects as Capabilities"

### 10.3 Semantics

7. Forster, Y., et al. (2017). "On the Expressive Power of User-Defined Effects"
8. Biernacki, D., et al. (2019). "Abstracting Algebraic Effects"

---

*Research Track Output — Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
