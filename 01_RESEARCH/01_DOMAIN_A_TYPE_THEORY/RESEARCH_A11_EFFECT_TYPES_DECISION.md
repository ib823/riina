# RESEARCH_A11_EFFECT_TYPES_DECISION.md

## TERAS-LANG Research Track
### Session A-11: Effect Types — Architecture Decision

---

**Document ID:** RESEARCH_A11_EFFECT_TYPES_DECISION  
**Version:** 1.0.0  
**Created:** 2026-01-03  
**Domain:** A (Type Theory Foundations)  
**Session:** A-11  
**Status:** APPROVED

---

## 1. DECISION SUMMARY

### 1.1 Decision Statement

**ADOPT row-polymorphic effect types with Koka-style evidence passing as the core effect type mechanism for TERAS-LANG, enhanced with capability-based semantics for security-critical effects and integrated purity tracking for optimization.**

### 1.2 Decision Rationale

Row-polymorphic effects provide the optimal balance of:
- Expressivity for complex effect combinations
- Efficient compilation via evidence passing
- Strong theoretical foundations
- Compatibility with linear and session types

Capability-based enhancements ensure:
- Security effects cannot be accidentally propagated
- Second-class treatment for sensitive operations
- Zero-cost lexical effect scoping

---

## 2. DETAILED SPECIFICATION

### 2.1 Effect Type Syntax

```teras
// Effect declaration
effect State<S> {
    fn get() -> S
    fn put(s: S) -> ()
}

effect IO {
    fn read_file(path: Path) -> Bytes
    fn write_file(path: Path, data: Bytes) -> ()
    fn network(addr: Address) -> Connection
}

effect Crypto {
    fn random(n: usize) -> Bytes
    fn encrypt(key: Key, data: Bytes) -> Ciphertext
    fn decrypt(key: Key, ct: Ciphertext) -> Option<Bytes>
}

// Function with effect annotation
fn increment() -> () / <State<Int>>
    let x = get()
    put(x + 1)

// Effect-polymorphic function
fn map<A, B, e: Effect>(f: A -> B / e, xs: List<A>) -> List<B> / e
    match xs
        Nil -> Nil
        Cons(x, rest) -> Cons(f(x), map(f, rest))

// Effect row extension
fn process() -> Result / <State<S>, IO | e>
    // Uses State and IO, plus any effects in e
```

### 2.2 Effect Row Semantics

**Row Types:**
```
ε ::= <e₁, e₂, ... | ρ>   (effect row)
ρ ::= <>                   (empty row / pure)
    | α                    (row variable)
    | <e | ρ>             (row extension)
```

**Row Operations:**
```
// Row extension
<State | <IO | ε>> = <State, IO | ε>

// Row unification
<e₁ | ρ₁> ~ <e₂ | ρ₂>  ⟹  e₁ = e₂ ∧ ρ₁ ~ ρ₂
                        ∨  ∃ρ'. ρ₁ = <e₂ | ρ'> ∧ <e₁ | ρ'> ~ ρ₂
                        ∨  ∃ρ'. ρ₂ = <e₁ | ρ'> ∧ ρ₁ ~ <e₂ | ρ'>

// Empty row (purity)
<> denotes pure computation
```

### 2.3 Effect Handler Syntax

```teras
// Deep handler (default)
handle action() with
    return x -> x
    effect Get() resume k -> k(state)
    effect Put(s) resume k ->
        state = s
        k(())

// Named handler for scoped effects
handler state_handler<S>(init: S) for State<S> {
    var current = init
    
    return x -> (current, x)
    effect Get() resume k -> k(current)
    effect Put(s) resume k ->
        current = s
        k(())
}

// Using named handler
fn run_state<S, A, e>(init: S, action: () -> A / <State<S> | e>) -> (S, A) / e
    with state_handler(init)
        action()
```

### 2.4 Evidence Passing Compilation

```teras
// Source
fn increment() -> () / <State<Int>>
    let x = get()
    put(x + 1)

// Compiled (evidence passing)
fn increment(ev: Evidence<State<Int>>) -> ()
    let x = ev.get()
    ev.put(x + 1)

// Handler installation
fn with_state(ev: Evidence<State<Int>>, action: () -> A) -> A
    let state = ref 0
    let new_ev = Evidence {
        get: () -> *state,
        put: (x) -> *state = x
    }
    action(new_ev)
```

---

## 3. PURITY TRACKING

### 3.1 Pure/Impure Distinction

```teras
// Pure function (no effects)
pure fn add(x: Int, y: Int) -> Int
    x + y

// Equivalent to empty effect row
fn add(x: Int, y: Int) -> Int / <>
    x + y

// Impure function (has effects)
fn greet(name: String) -> () / <IO>
    println("Hello, " + name)

// Effect-polymorphic with purity constraint
fn map_pure<A, B>(f: pure A -> B, xs: List<A>) -> List<B>
    // f is guaranteed pure, map is pure
```

### 3.2 Purity Inference

```teras
// Purity is inferred from effect row
fn factorial(n: Int) -> Int
    if n <= 1 then 1 else n * factorial(n - 1)
// Inferred: factorial : Int -> Int / <>  (pure)

fn read_config() -> Config
    let bytes = read_file("/etc/config")
    parse(bytes)
// Inferred: read_config : () -> Config / <IO>  (impure)
```

### 3.3 Purity Benefits

```teras
// Pure functions can be:
// 1. Memoized
@memoize
pure fn fib(n: Int) -> Int
    if n <= 1 then n else fib(n-1) + fib(n-2)

// 2. Parallelized
fn parallel_map<A, B>(f: pure A -> B, xs: List<A>) -> List<B>
    // Safe to run f in parallel

// 3. Constant-time verified
@constant_time
pure fn compare_secret(a: Bytes, b: Bytes) -> bool
    // Compiler verifies no timing side channels
```

---

## 4. CAPABILITY-BASED SECURITY EFFECTS

### 4.1 Security Effect Declarations

```teras
// Security effects require explicit capability
secure effect Crypto {
    fn random(n: usize) -> Bytes
    fn encrypt(alg: Algorithm, key: Key, data: Bytes) -> Ciphertext
    fn sign(key: PrivateKey, data: Bytes) -> Signature
}

secure effect HSM {
    fn generate_key(params: KeyParams) -> KeyHandle
    fn sign_with_key(handle: KeyHandle, data: Bytes) -> Signature
}

// Capability type (linear)
type Cap<E: SecureEffect> = lin Capability<E>
```

### 4.2 Capability-Passing Style

```teras
// Secure functions require capability
fn sign_document(
    cap: lin Cap<Crypto>,
    doc: Document
) -> Signature / <>
    // Capability consumed, cannot escape
    cap.sign(get_key(), doc.hash())

// Capability provisioning
fn with_crypto<A>(action: (lin Cap<Crypto>) -> A / <>) -> A / <IO>
    let cap = acquire_crypto_capability()
    action(cap)
    // cap consumed by action
```

### 4.3 Effect Masking

```teras
// Internal implementation uses effects
fn internal_process() -> Result / <State<S>, Log, Crypto>
    ...

// Public API masks effects
fn public_api() -> Result / <>
    handle internal_process() with
        // State handler
        return x -> x
        effect Get() resume k -> k(default_state())
        effect Put(s) resume k -> k(())
    mask Log with
        effect Log(msg) resume k -> k(())  // discard logs
    // Crypto effect requires capability, provided internally
```

---

## 5. INTEGRATION WITH OTHER TYPE FEATURES

### 5.1 Linear Types Integration

```teras
// Linear resources with effects
fn with_file<A>(
    path: Path,
    action: (lin File) -> A / <IO>
) -> A / <IO, FileError>
    let file = open(path)?
    let result = action(file)
    // file consumed by action
    result

// Effect handlers can consume linear values
handle action(lin resource) with
    return x -> x
    effect UseResource() resume k using resource ->
        let (result, resource') = use_resource(resource)
        k(result) using resource'
```

### 5.2 Session Types Integration

```teras
// Protocol as effect
effect Protocol<P: Session> {
    fn send<T>(msg: T) where P = !T.P'
    fn recv<T>() -> T where P = ?T.P'
}

session AuthProtocol = !Credentials.?AuthResult.end

fn authenticate(
    chan: lin Chan<AuthProtocol>
) -> AuthResult / <Protocol<AuthProtocol>>
    send(credentials)
    recv()

// Handler connects to actual channel
fn run_protocol<P, A>(
    chan: lin Chan<P>,
    action: () -> A / <Protocol<P>>
) -> A / <IO>
    handle action() with
        return x -> x
        effect Send(msg) resume k using chan ->
            let chan' = channel_send(chan, msg)
            k(()) using chan'
        effect Recv() resume k using chan ->
            let (msg, chan') = channel_recv(chan)
            k(msg) using chan'
```

### 5.3 Refinement Types Integration

```teras
// Effects with refinement predicates
effect BoundedAlloc<R, const N: usize> {
    fn alloc<T>(x: T) -> Ref<R, T> where size_of::<T>() <= N
}

// Effect-refined functions
fn process_buffer(
    buf: &[u8; n] where n <= 4096
) -> Result / <BoundedAlloc<Heap, 1024>>
    // Can only allocate up to 1024 bytes
```

---

## 6. EFFECT INFERENCE ALGORITHM

### 6.1 Type Inference with Effects

```
Input: Expression e, Environment Γ
Output: (Type τ, Effect ε, Substitution θ)

infer(Γ, e) = match e with
    | x -> 
        let τ = Γ(x)
        (instantiate(τ), <>, id)
    
    | λx. e' ->
        let α, β, ρ = fresh_vars()
        let (τ, ε, θ) = infer(Γ[x ↦ α], e')
        (θ(α) -> τ / ε, <>, θ)
    
    | e₁ e₂ ->
        let (τ₁, ε₁, θ₁) = infer(Γ, e₁)
        let (τ₂, ε₂, θ₂) = infer(θ₁(Γ), e₂)
        let α, ρ = fresh_vars()
        let θ₃ = unify(θ₂(τ₁), τ₂ -> α / ρ)
        (θ₃(α), θ₃(ε₁) ∪ θ₃(ε₂) ∪ θ₃(ρ), θ₃ ∘ θ₂ ∘ θ₁)
    
    | perform op(e') ->
        let E = effect_of(op)
        let (τ_arg, τ_ret) = signature_of(op)
        let (τ', ε, θ) = infer(Γ, e')
        let θ' = unify(τ', τ_arg)
        (θ'(τ_ret), θ'(ε) ∪ <E>, θ' ∘ θ)
    
    | handle e' with h ->
        let E = handled_effect(h)
        let (τ, ε, θ) = infer(Γ, e')
        let ε' = remove_effect(E, θ(ε))
        let τ' = handler_return_type(h, τ)
        (τ', ε', θ)
```

### 6.2 Row Unification

```
unify_row(ρ₁, ρ₂) = match (ρ₁, ρ₂) with
    | (<>, <>) -> id
    | (α, ρ) -> [α ↦ ρ] if α ∉ fv(ρ)
    | (ρ, α) -> [α ↦ ρ] if α ∉ fv(ρ)
    | (<e | ρ₁'>, <e | ρ₂'>) -> unify_row(ρ₁', ρ₂')
    | (<e₁ | ρ₁'>, <e₂ | ρ₂'>) when e₁ ≠ e₂ ->
        let β = fresh_var()
        let θ₁ = unify_row(ρ₁', <e₂ | β>)
        let θ₂ = unify_row(θ₁(ρ₂'), <e₁ | θ₁(β)>)
        θ₂ ∘ θ₁
```

---

## 7. IMPLEMENTATION ROADMAP

### 7.1 Phase 1: Core Effect Types (Weeks 1-6)

**Deliverables:**
- Effect declaration syntax
- Effect annotation on functions
- Basic row type representation
- Effect presence checking

**Validation:**
- Type safety proof sketch
- Basic test suite

### 7.2 Phase 2: Effect Inference (Weeks 7-12)

**Deliverables:**
- Row unification algorithm
- Effect inference in type checker
- Principal type computation
- Effect simplification

**Validation:**
- Inference completeness tests
- Performance benchmarks

### 7.3 Phase 3: Effect Handlers (Weeks 13-20)

**Deliverables:**
- Handler syntax and typing
- Deep handler semantics
- Evidence passing compilation
- Handler optimization

**Validation:**
- Handler correctness proofs
- Runtime performance tests

### 7.4 Phase 4: Security Effects (Weeks 21-28)

**Deliverables:**
- Secure effect declarations
- Capability types integration
- Effect masking
- Security verification

**Validation:**
- Security property proofs
- Penetration testing

### 7.5 Phase 5: Integration (Weeks 29-36)

**Deliverables:**
- Linear type integration
- Session type integration
- Refinement integration
- Full optimization passes

**Validation:**
- Integration tests
- End-to-end product tests

---

## 8. RISK ANALYSIS

### 8.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Row unification complexity | Medium | High | Implement optimizations from Koka |
| Evidence passing overhead | Low | Medium | Selective CPS, inlining |
| Integration conflicts | Medium | Medium | Careful interface design |
| Handler optimization | Medium | Medium | Study Effekt/Koka approaches |

### 8.2 Compatibility Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Linear type interaction | Low | High | Follow established patterns |
| Session type interaction | Low | Medium | Unified effect+session model |
| Refinement interaction | Medium | Medium | SMT effect constraints |

---

## 9. ALIGNMENT ASSESSMENT

### 9.1 TERAS Law Compliance

| Law | Compliance | Notes |
|-----|------------|-------|
| Self-sufficiency | ✓ | No external dependencies |
| Formal verification | ✓ | Row types well-understood |
| Performance mandate | ✓ | Evidence passing efficient |
| Security guarantees | ✓ | Capability-based security effects |

### 9.2 Product Alignment

| Product | Effect Usage | Alignment |
|---------|--------------|-----------|
| MENARA | Network, Crypto, UI | 95% |
| GAPURA | Network, State, Log | 90% |
| ZIRAH | System, File, Process | 90% |
| BENTENG | Crypto, Bio, Network | 95% |
| SANDI | Crypto, HSM, Time | 95% |

### 9.3 Overall Alignment Score

**Score: 8.8 / 10**

Strengths:
- Excellent theoretical foundation
- Efficient compilation strategy
- Strong security model
- Good integration path

Areas for attention:
- Row unification optimization
- Handler performance tuning
- Learning curve for developers

---

## 10. DECISION RECORD

### 10.1 Decision

**APPROVED:** Row-polymorphic effect types with Koka-style evidence passing, enhanced with capability-based security effects.

### 10.2 Alternatives Rejected

1. **Boolean unification (Flix):** Insufficient granularity for security tracking
2. **Untyped effects (OCaml 5):** No compile-time guarantees
3. **Pure capability model (Effekt):** Second-class function limitation

### 10.3 Dependencies

- A-04: Linear Types (for capability integration)
- A-05: Effect Systems (theoretical foundation)
- A-07: Session Types (protocol effects)

### 10.4 Successor Sessions

- A-12: Region Types (memory region effects)
- B-01: Algebraic Effects (implementation details)

---

**Document Checksum (SHA-256):** To be computed on final version  
**Approved By:** TERAS Architecture Council  
**Approval Date:** 2026-01-03
