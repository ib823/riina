# TERAS-LANG Architecture Decision A-18: Type-Level Computation

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A18-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL ADOPT** a unified type-level computation system combining:

1. **Dependent type foundation** (Idris-style) where types and values share syntax
2. **Closed type families** for predictable security computations
3. **Automatic singleton generation** for type-value bridging
4. **Stratified termination checking** to ensure decidability
5. **Security-specific type-level primitives** (labels, capabilities, states)
6. **Aggressive erasure** for zero runtime overhead

### 1.2 Architecture Decision ID

`TERAS-ARCH-A18-TLC-001`

### 1.3 Status

**APPROVED** - Ratified for TERAS-LANG implementation

---

## 2. Context and Requirements

### 2.1 Security Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| SEC-TLC-01 | Compile-time security policy enforcement | Critical |
| SEC-TLC-02 | Type-level information flow checking | Critical |
| SEC-TLC-03 | Capability set computation at compile time | Critical |
| SEC-TLC-04 | Protocol state machine verification | High |
| SEC-TLC-05 | Permission inheritance computation | High |
| SEC-TLC-06 | Zero runtime overhead for type-level code | Critical |

### 2.2 Integration Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| INT-TLC-01 | Integrate with linear type system (A-04) | Critical |
| INT-TLC-02 | Integrate with effect rows (A-05, A-11) | Critical |
| INT-TLC-03 | Integrate with refinement types (A-08) | High |
| INT-TLC-04 | Integrate with row types (A-16) | High |
| INT-TLC-05 | Integrate with HKT (A-17) | High |
| INT-TLC-06 | Support singleton pattern for bridging | High |

### 2.3 Usability Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| USE-TLC-01 | Clear error messages for type-level failures | High |
| USE-TLC-02 | Reasonable compilation times | Medium |
| USE-TLC-03 | Minimal boilerplate | Medium |
| USE-TLC-04 | Familiar syntax where possible | Medium |

---

## 3. Decision Details

### 3.1 Unified Type-Value Syntax

TERAS-LANG eliminates the artificial distinction between type-level and value-level code:

```
// Same function definition works at both levels
fn add(n: Nat, m: Nat) -> Nat {
    match n {
        Zero => m,
        Succ(pred) => Succ(add(pred, m))
    }
}

// Used at value level:
let five: Nat = add(two, three);

// Used at type level:
type FiveType = add(Two, Three);  // evaluates to Succ(Succ(Succ(Succ(Succ(Zero)))))

// In dependent position:
fn replicate<n: Nat, T>(value: T) -> Vec<add(n, Zero), T> {
    // add(n, Zero) is evaluated at compile time
    ...
}
```

**Syntax rules:**
- Lowercase identifiers can be types when in type position
- Type annotations required at boundaries
- Universe hierarchy: `Type : Typeâ‚ : Typeâ‚‚ : ...`

### 3.2 Closed Type-Level Functions

For predictable security semantics, core security computations use closed definitions:

```
// Closed function - all cases defined here, matched top-to-bottom
#[closed]
fn label_join(l1: Label, l2: Label) -> Label {
    match (l1, l2) {
        (Public, l) => l,
        (l, Public) => l,
        (Secret, Secret) => Secret,
        (Secret, TopSecret) => TopSecret,
        (TopSecret, _) => TopSecret,
        (_, TopSecret) => TopSecret,
        (Confidential, Confidential) => Confidential,
        (Confidential, Secret) => Secret,
        (Secret, Confidential) => Secret,
    }
}

// Properties of closed functions:
// - All patterns visible at definition site
// - Overlapping patterns allowed (first match wins)
// - Cannot be extended later
// - Guaranteed confluence
```

### 3.3 Security Label Computation

```
// Security label lattice as type-level computation
enum Label {
    Public,
    Internal,
    Confidential,
    Secret,
    TopSecret,
}

#[closed]
fn flows(from: Label, to: Label) -> Bool {
    match (from, to) {
        (Public, _) => True,
        (Internal, Public) => False,
        (Internal, _) => True,
        (Confidential, Public | Internal) => False,
        (Confidential, _) => True,
        (Secret, TopSecret | Secret) => True,
        (Secret, _) => False,
        (TopSecret, TopSecret) => True,
        (TopSecret, _) => False,
    }
}

// Compile-time checked information flow
fn declassify<from: Label, to: Label, T>(
    value: Labeled<from, T>
) -> Labeled<to, T>
where
    flows(from, to) == True  // Compile-time constraint
{
    Labeled(value.0)
}
```

### 3.4 Capability Set Operations

```
// Type-level capability set as list
type CapSet = List<Cap>;

enum Cap {
    FileRead,
    FileWrite,
    NetConnect,
    ProcessSpawn,
    CryptoSign,
    // ...
}

#[closed]
fn has_cap(c: Cap, cs: CapSet) -> Bool {
    match cs {
        Nil => False,
        Cons(head, tail) if c == head => True,
        Cons(_, tail) => has_cap(c, tail),
    }
}

#[closed]
fn cap_subset(sub: CapSet, super: CapSet) -> Bool {
    match sub {
        Nil => True,
        Cons(c, rest) => has_cap(c, super) && cap_subset(rest, super),
    }
}

// Capability-gated operation
fn read_file<caps: CapSet>(path: Path) -> IO<ByteString>
where
    has_cap(FileRead, caps) == True
{
    // ...
}

// Attenuation
fn attenuate<sub: CapSet, super: CapSet, T>(
    action: Secure<super, T>
) -> Secure<sub, T>
where
    cap_subset(sub, super) == True
{
    // Safe: sub is a subset of super
    unsafe_cast(action)
}
```

### 3.5 Protocol State Machines

```
// Protocol states as type-level data
enum TLSState {
    Initial,
    HelloSent,
    KeyExchanged,
    Established,
    Closed,
}

#[closed]
fn valid_transition(from: TLSState, to: TLSState) -> Bool {
    match (from, to) {
        (Initial, HelloSent) => True,
        (HelloSent, KeyExchanged) => True,
        (KeyExchanged, Established) => True,
        (Established, Closed) => True,
        (_, Closed) => True,  // Can always close
        _ => False,
    }
}

// State-indexed connection
struct TLSConnection<state: TLSState> {
    handle: Handle,
    _state: PhantomData<state>,
}

impl TLSConnection<Initial> {
    fn send_hello(self) -> TLSConnection<HelloSent>
    where
        valid_transition(Initial, HelloSent) == True
    {
        // Type system verifies this is a valid transition
        ...
    }
}

impl TLSConnection<Established> {
    fn send(self, data: ByteString) -> IO<()> {
        // Only available when established
        ...
    }
}
```

### 3.6 Automatic Singleton Generation

```
// #[singleton] generates type-value bridging automatically
#[singleton]
enum Nat {
    Zero,
    Succ(Nat),
}

// Generates:
// - SNat<n: Nat> singleton type
// - SZero: SNat<Zero>
// - SSucc: SNat<n> -> SNat<Succ(n)>
// - ToSing trait for lifting values
// - FromSing trait for lowering singletons

// Usage:
fn replicate<n: Nat, T>(sing: SNat<n>, value: T) -> Vec<n, T> {
    match sing {
        SZero => Vec::nil(),
        SSucc(pred) => Vec::cons(value.clone(), replicate(pred, value)),
    }
}

// With implicit singletons:
fn replicate_implicit<n: Nat, T>(value: T) -> Vec<n, T>
where
    Singleton<n>  // Constraint that singleton exists implicitly
{
    replicate(the_singleton::<n>(), value)
}
```

### 3.7 Termination Checking

```
// Stratified termination: recursive calls must decrease on some measure
#[terminating(on = n)]
fn add(n: Nat, m: Nat) -> Nat {
    match n {
        Zero => m,
        Succ(pred) => Succ(add(pred, m)),  // pred < n, OK
    }
}

// Fuel-based computation for complex recursion
#[fuel(1000)]
fn complex_compute<n: Nat>() -> Result<Computed<n>, OutOfFuel> {
    // Will terminate after 1000 reduction steps
    ...
}

// Explicit totality annotations
#[total]  // Must cover all cases and terminate
fn security_check<l: Label>() -> Bool { ... }

#[partial]  // May not cover all cases
fn user_function<T>() -> T { ... }
```

### 3.8 Error Messages

```
// Custom error messages for type-level failures
#[closed]
fn require_cap(c: Cap, cs: CapSet) -> ()
where
    has_cap(c, cs) == True
        or_else error("Missing capability: {c}. Available: {cs}")
{
    ()
}

// Usage generates clear errors:
fn example() {
    let caps: CapSet = [FileRead];
    require_cap(FileWrite, caps);
    // Error: Missing capability: FileWrite. Available: [FileRead]
}
```

---

## 4. Integration with Previous Decisions

### 4.1 Linear Types (A-04)

```
// Type-level computation with linear types
fn consume_linear<T: Linear, n: Nat>(
    resources: Vec<n, T>
) -> Consumed<n>
where
    n > Zero  // Type-level constraint
{
    // Each element consumed exactly once
    resources.into_iter().for_each(|r| r.consume());
    Consumed::new()
}
```

### 4.2 Effect Rows (A-05, A-11)

```
// Type-level effect computation
#[closed]
fn effect_union<e1: EffectRow, e2: EffectRow>() -> EffectRow {
    // Merge two effect rows
    ...
}

fn compose<A, B, C, e1: EffectRow, e2: EffectRow>(
    f: fn(A) -> Eff<e1, B>,
    g: fn(B) -> Eff<e2, C>,
) -> fn(A) -> Eff<effect_union(e1, e2), C> {
    |a| g(f(a)?)
}
```

### 4.3 Refinement Types (A-08)

```
// Type-level computation in refinements
type BoundedInt<lo: Int, hi: Int> = { x: Int | lo <= x && x <= hi };

fn clamp<lo: Int, hi: Int>(x: Int) -> BoundedInt<lo, hi>
where
    lo <= hi  // Type-level constraint
{
    if x < lo { lo }
    else if x > hi { hi }
    else { x }
}
```

### 4.4 Row Types (A-16)

```
// Type-level row operations
#[closed]
fn row_has<label: Symbol, row: Row>() -> Bool { ... }

#[closed]
fn row_get<label: Symbol, row: Row>() -> Type
where
    row_has(label, row) == True
{ ... }

fn get_field<label: Symbol, row: Row, T>(
    record: Record<row>
) -> T
where
    row_has(label, row) == True,
    row_get(label, row) == T
{
    // Type-safe field access
    ...
}
```

### 4.5 Higher-Kinded Types (A-17)

```
// Type-level computation with HKT
trait Functor<F: Type -> Type> {
    fn map<A, B>(fa: F<A>, f: fn(A) -> B) -> F<B>;
}

// Type-level functor composition
#[closed]
fn composed_kind<F: Type -> Type, G: Type -> Type>() -> (Type -> Type) {
    |A| F<G<A>>
}

impl<F: Functor, G: Functor> Functor<composed_kind(F, G)> {
    fn map<A, B>(fga: F<G<A>>, f: fn(A) -> B) -> F<G<B>> {
        F::map(fga, |ga| G::map(ga, f))
    }
}
```

---

## 5. Implementation Strategy

### 5.1 Compiler Phases

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                 Type-Level Computation Pipeline              â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                              â”‚
â”‚  Source â†’ Parse â†’ Elaborate â†’ TL-Eval â†’ Check â†’ Erase â†’ Gen â”‚
â”‚                        â”‚          â”‚        â”‚                 â”‚
â”‚                        â–¼          â–¼        â–¼                 â”‚
â”‚                   Universe    Normalize  Verify              â”‚
â”‚                   Inference   Types      Terms               â”‚
â”‚                        â”‚          â”‚        â”‚                 â”‚
â”‚                        â–¼          â–¼        â–¼                 â”‚
â”‚                   Implicit    Term.      Proof               â”‚
â”‚                   Resolution  Check      Erase               â”‚
â”‚                                                              â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 5.2 Type-Level Evaluation

| Phase | Action |
|-------|--------|
| 1. Collect | Gather type-level function definitions |
| 2. Stratify | Build call graph, detect cycles |
| 3. Termination | Verify termination (structural or fuel) |
| 4. Normalize | Reduce type-level terms to normal form |
| 5. Unify | Solve type equations after normalization |
| 6. Verify | Check constraints after normalization |

### 5.3 Erasure Strategy

```
Erasure Rules:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
Types:
    - All type parameters â†’ erased (exist only at compile time)
    
Proofs:
    - Equality proofs â†’ erased (Refl has no runtime rep)
    - Constraint witnesses â†’ erased if not used
    
Singletons:
    - SNat<n> â†’ erased (type determines value)
    - Exception: if singleton value used at runtime, keep
    
PhantomData:
    - PhantomData<T> â†’ zero-sized (no runtime rep)
    
Result:
    - Type-level computation â†’ zero runtime cost
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

### 5.4 Performance Optimizations

| Optimization | Description |
|--------------|-------------|
| Memoization | Cache normalized types to avoid re-computation |
| Incremental | Reuse type-level results across compilation units |
| Specialization | Generate specialized code for common type arguments |
| Inlining | Inline small type-level functions |
| Sharing | Share identical normalized types in memory |

---

## 6. TERAS Product Integration

### 6.1 Security Computations by Product

| Product | Type-Level Computation Use |
|---------|---------------------------|
| MENARA | Permission flags, trust levels, app state transitions |
| GAPURA | HTTP method constraints, rate limit encoding, taint propagation |
| ZIRAH | Process capability sets, threat severity ordering, scan state |
| BENTENG | Verification levels, identity attribute constraints, workflow states |
| SANDI | Key algorithm parameters, certificate chain validation, key states |

### 6.2 Example: MENARA Mobile Permissions

```
// Mobile permissions as type-level data
enum Permission {
    Camera,
    Microphone,
    Location,
    Storage,
    Network,
    Contacts,
}

#[singleton]
type PermSet = List<Permission>;

// Permission-gated API calls
fn access_camera<perms: PermSet>() -> IO<Camera>
where
    has_cap(Camera, perms) == True
{
    ...
}

fn access_location<perms: PermSet>() -> IO<Location>
where
    has_cap(Location, perms) == True
{
    ...
}

// App with declared permissions
struct App<perms: PermSet> {
    // Only operations matching perms are available
}

impl<perms: PermSet> App<perms>
where
    has_cap(Camera, perms) == True,
    has_cap(Location, perms) == True
{
    // This implementation only available if app has Camera and Location
    fn take_geotagged_photo(&self) -> IO<Photo> {
        let camera = access_camera::<perms>()?;
        let location = access_location::<perms>()?;
        camera.capture_with_location(location)
    }
}
```

### 6.3 Example: GAPURA Rate Limiting

```
// Type-level rate limit configuration
struct RateLimit<
    requests: Nat,
    period_seconds: Nat,
    burst: Nat,
> { ... }

// Compile-time rate limit validation
#[closed]
fn valid_rate_limit<r: Nat, p: Nat, b: Nat>() -> Bool {
    r > Zero && p > Zero && b >= r
}

fn create_limiter<r: Nat, p: Nat, b: Nat>() -> RateLimiter
where
    valid_rate_limit(r, p, b) == True
{
    ...
}

// Type-level rate limit composition
#[closed]
fn stricter<r1: Nat, p1: Nat, b1: Nat, r2: Nat, p2: Nat, b2: Nat>()
    -> (Nat, Nat, Nat)
{
    // Returns the stricter of two rate limits
    let rate_per_sec_1 = r1 / p1;
    let rate_per_sec_2 = r2 / p2;
    if rate_per_sec_1 < rate_per_sec_2 {
        (r1, p1, b1)
    } else {
        (r2, p2, b2)
    }
}
```

---

## 7. Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Compilation time explosion | Medium | High | Memoization, incremental, fuel limits |
| Complex error messages | High | Medium | Custom error annotations, examples |
| Non-termination | Low | High | Stratified termination checking |
| Learning curve | Medium | Medium | Documentation, familiar syntax |
| Integration complexity | Medium | Medium | Clear interface boundaries |

---

## 8. Implementation Roadmap

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Core TLC | 4 weeks | Unified syntax, basic type families |
| 2. Singletons | 3 weeks | Automatic generation, bridging |
| 3. Termination | 3 weeks | Stratified checking, fuel system |
| 4. Security Prims | 4 weeks | Labels, capabilities, states |
| 5. Integration | 4 weeks | Linear, effect, row integration |
| 6. Erasure | 3 weeks | Full erasure, zero-cost verification |
| 7. Optimization | 3 weeks | Memoization, specialization |
| **Total** | **24 weeks** | Complete TLC system |

---

## 9. Validation Criteria

### 9.1 Correctness

- [ ] Type-level functions reduce correctly
- [ ] Termination checking catches non-terminating functions
- [ ] Security computations produce correct results
- [ ] Integration with other type system features works

### 9.2 Performance

- [ ] Simple type-level ops: < 1ms
- [ ] Complex security checks: < 100ms
- [ ] Large capability sets: < 500ms
- [ ] Full program: < 2x base compile time

### 9.3 Security

- [ ] Security labels correctly computed
- [ ] Capability checks cannot be bypassed
- [ ] State machine transitions validated
- [ ] No runtime overhead from type-level code

---

## 10. References

1. Brady, E. (2013). "Idris, a general-purpose dependently typed programming language"
2. Eisenberg, R. A. (2016). "Dependent Types in Haskell: Theory and Practice"
3. Chakravarty, M., et al. (2005). "Associated Types with Class"
4. McBride, C. (2002). "Faking It: Simulating Dependent Types in Haskell"
5. TERAS Architecture Decisions A-01 through A-17

---

## 11. Approval

| Role | Name | Date | Signature |
|------|------|------|-----------|
| TERAS Architect | [Pending] | | |
| Security Lead | [Pending] | | |
| Compiler Lead | [Pending] | | |

---

*Architecture Decision Record for TERAS-LANG type-level computation system.*
