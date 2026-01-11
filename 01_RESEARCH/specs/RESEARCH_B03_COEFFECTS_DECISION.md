# TERAS-LANG Architecture Decision B-03: Coeffects

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B03-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-03 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL ADOPT** coeffects integrated with the algebraic effect system, implementing:

1. **Graded coeffect types** using semiring structure
2. **Capability coeffects** for permission requirements
3. **Clearance coeffects** for security level tracking
4. **Resource budget coeffects** for consumption limits
5. **Provenance coeffects** for data origin tracking
6. **Unified effect/coeffect syntax** in function types
7. **Coeffect inference** with explicit annotation support

### 1.2 Architecture Decision ID

`TERAS-ARCH-B03-COE-001`

### 1.3 Status

**APPROVED** â€” Ratified for TERAS-LANG implementation

---

## 2. Rationale

### 2.1 Why Coeffects for TERAS

| Security Need | Coeffect Solution |
|---------------|-------------------|
| Capability enforcement | Capability coeffects track required permissions |
| Security clearance | Clearance coeffects ensure proper authorization |
| Resource limiting | Budget coeffects prevent resource exhaustion |
| Taint tracking | Provenance coeffects track data origins |
| Context requirements | General coeffects encode any context dependency |

### 2.2 Requirements Addressed

| ID | Requirement | How Addressed |
|----|-------------|---------------|
| COE-01 | Compile-time capability checking | Capability coeffects |
| COE-02 | Security level propagation | Clearance lattice coeffects |
| COE-03 | Resource budget enforcement | Budget semiring coeffects |
| COE-04 | Data provenance tracking | Provenance set coeffects |
| COE-05 | Integration with effects | Unified A -[Îµ]-> B @ r syntax |

---

## 3. Design Details

### 3.1 Coeffect Syntax

```rust
// Function with effects AND coeffects
fn operation() -[Effect]-> Result @ {Coeffect} {
    // ...
}

// Full type signature
fn secure_read(path: &str) 
    -[IO, Log]->           // Effects produced
    Result<Bytes, Error>
    @ {FileRead, Secret}   // Coeffects required
{
    // Requires FileRead capability and Secret clearance
}
```

### 3.2 Coeffect Dimensions

```rust
// Built-in coeffect dimensions

// 1. Capabilities (set union)
coeffect Capability: Set<Cap> {
    combine = union;
    empty = {};
}

// 2. Security Clearance (lattice join)
coeffect Clearance: SecurityLevel {
    combine = join;  // âŠ”
    empty = Public;
}

// 3. Resource Budget (addition)
coeffect Budget: Resources {
    combine = add;
    empty = zero;
}

// 4. Data Provenance (set union)
coeffect Provenance: Set<Source> {
    combine = union;
    empty = {};
}

// 5. Usage Count (natural numbers)
coeffect Usage: Nat {
    combine = add;
    empty = 0;
}
```

### 3.3 Coeffect Typing Rules

```
Coeffect Judgment: Î“ âŠ¢ e : A ! Îµ @ r

Rules:

    x : A @ r âˆˆ Î“
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€    (Var)
    Î“ âŠ¢ x : A ! âŸ¨âŸ© @ r

    Î“ âŠ¢ eâ‚ : A â†’[Îµ] B @ râ‚    Î“ âŠ¢ eâ‚‚ : A ! Îµ' @ râ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€    (App)
    Î“ âŠ¢ eâ‚ eâ‚‚ : B ! Îµ âˆª Îµ' @ râ‚ âŠ• râ‚‚

    Î“, x : A @ s âŠ¢ e : B ! Îµ @ r
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€    (Abs)
    Î“ âŠ¢ Î»x. e : A â†’[Îµ] B @ r @ (r - s)

    râ‚ â‰¤ râ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€    (Weaken)
    Î“ âŠ¢ e : A ! Îµ @ râ‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e : A ! Îµ @ râ‚‚
```

### 3.4 Capability Coeffects

```rust
// Capability declaration
cap FileRead;
cap FileWrite;
cap NetworkAccess;
cap CryptoOps;

// Function requiring capabilities
fn read_file(path: &str) -> Bytes @ {FileRead} {
    fs::read(path)
}

fn write_file(path: &str, data: Bytes) -> () @ {FileWrite} {
    fs::write(path, data)
}

fn copy_file(src: &str, dst: &str) -> () @ {FileRead, FileWrite} {
    // Coeffects combine: {FileRead} âˆª {FileWrite}
    let data = read_file(src);
    write_file(dst, data)
}

// Capability checking at entry points
#[entry(capabilities = {FileRead, FileWrite})]
fn main() {
    copy_file("a.txt", "b.txt");  // OK: has required caps
}
```

### 3.5 Clearance Coeffects

```rust
// Security level hierarchy
level Public < Internal < Confidential < Secret < TopSecret;

// Clearance-graded functions
fn read_public() -> Data @ Clearance::Public {
    // Anyone can call
}

fn read_secret() -> Data @ Clearance::Secret {
    // Requires Secret clearance
}

fn process_mixed() -> Result @ Clearance::Secret {
    // Clearance is join: Public âŠ” Secret = Secret
    let pub_data = read_public();
    let sec_data = read_secret();
    combine(pub_data, sec_data)
}

// Clearance boundary checking
#[clearance(Secret)]
fn secure_context() {
    process_mixed();  // OK: context has Secret
}

#[clearance(Public)]
fn public_context() {
    process_mixed();  // ERROR: insufficient clearance
}
```

### 3.6 Budget Coeffects

```rust
// Resource budget structure
struct Budget {
    time: Duration,
    memory: Bytes,
    api_calls: u32,
}

// Budget-graded computations
fn expensive_query() -> Result @ Budget { 
    time: 100.ms, 
    memory: 10.MB, 
    api_calls: 5 
} {
    // Uses specified resources
}

fn cheap_check() -> bool @ Budget { 
    time: 1.ms, 
    memory: 1.KB, 
    api_calls: 0 
} {
    // Minimal resources
}

fn combined() -> Result @ Budget { 
    time: 101.ms,      // 100 + 1
    memory: 10.MB + 1.KB,
    api_calls: 5       // 5 + 0
} {
    if cheap_check() {
        expensive_query()
    } else {
        default_result()
    }
}

// Budget enforcement
fn with_budget<R>(budget: Budget, f: () -> R @ B) -> Option<R>
where
    B <= budget  // Compile-time check
{
    Some(f())
}
```

### 3.7 Provenance Coeffects

```rust
// Data sources
source UserInput;
source ConfigFile;
source Database;
source Network;

// Provenance-tracked functions
fn get_user_input() -> String @ Provenance::{UserInput} {
    stdin.read_line()
}

fn load_config() -> Config @ Provenance::{ConfigFile} {
    parse_config(read_file("config.toml"))
}

fn query_db(q: Query) -> Records @ Provenance::{Database} {
    db.execute(q)
}

// Provenance propagation
fn process_request() -> Response @ Provenance::{UserInput, Database} {
    // Provenance union: {UserInput} âˆª {Database}
    let input = get_user_input();
    let records = query_db(parse_query(input));
    format_response(records)
}

// Provenance-based security policy
fn sensitive_operation<P>(data: Data @ Provenance::P) -> Result
where
    UserInput âˆ‰ P  // No user input allowed!
{
    // Type-safe: only data without user input provenance
}
```

---

## 4. Integration with Effects

### 4.1 Combined Syntax

```rust
// Full effect + coeffect annotation
fn secure_transfer(
    from: Account,
    to: Account,
    amount: Money
) -[Transaction, Log, Audit]->    // Effects
  Result<Receipt, Error>
  @ {                              // Coeffects
      Capability::{AccountAccess, TransferAuth},
      Clearance::Confidential,
      Budget { time: 500.ms, api_calls: 3 }
  }
{
    // Implementation
}
```

### 4.2 Handler Coeffect Requirements

```rust
// Effect handlers can have coeffect requirements
handler audit_handler for Audit @ {AuditCapability} {
    // Handler requires AuditCapability to operate
    return(x) => x,
    log(level, event) resume => {
        write_audit_log(level, event);  // Needs capability
        resume(())
    }
}

// Installing handler satisfies effect, propagates coeffect
fn audited<A>(f: () -[Audit]-> A) -> A @ {AuditCapability} {
    handle audit_handler { f() }
}
```

### 4.3 Coeffect Polymorphism

```rust
// Polymorphic over coeffects
fn map<A, B, E, R>(
    f: A -[E]-> B @ R,
    xs: List<A>
) -[E]-> List<B> @ R {
    match xs {
        Nil => Nil,
        Cons(x, rest) => Cons(f(x), map(f, rest))
    }
}

// Coeffect bounds
fn restricted<R>(f: () -> A @ R) -> A
where
    R: HasCapability<FileRead>,
    R: HasClearance<Confidential>,
{
    f()
}
```

---

## 5. Coeffect Inference

### 5.1 Inference Algorithm

```
Coeffect Inference:

1. Generate constraints from syntax
2. Solve coeffect constraints using semiring operations
3. Propagate through function calls
4. Check at boundaries

Example:
    fn foo(x) = bar(x) + baz(x)
    
    Given:
        bar : A -> B @ râ‚
        baz : A -> C @ râ‚‚
    
    Inferred:
        foo : A -> D @ (râ‚ âŠ• râ‚‚)
```

### 5.2 Explicit Annotation

```rust
// Coeffects can be inferred or explicit

// Inferred
fn example1(path: &str) -> Bytes {
    read_file(path)  // Infers @ {FileRead}
}

// Explicit (for documentation/enforcement)
fn example2(path: &str) -> Bytes @ {FileRead} {
    read_file(path)
}

// Explicit restriction
fn example3(path: &str) -> Bytes @ {FileRead, FileWrite} {
    // Allowed to have MORE coeffects than needed
    read_file(path)
}
```

---

## 6. Implementation Roadmap

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Core coeffects | 3 weeks | Basic coeffect tracking |
| 2. Capability coeffects | 2 weeks | Capability system |
| 3. Clearance coeffects | 2 weeks | Security levels |
| 4. Budget coeffects | 2 weeks | Resource tracking |
| 5. Provenance coeffects | 2 weeks | Origin tracking |
| 6. Inference | 3 weeks | Coeffect inference |
| 7. Integration | 2 weeks | Effect+coeffect unification |
| **Total** | **16 weeks** | Complete coeffect system |

---

## 7. Validation Criteria

- [ ] Capability enforcement at compile time
- [ ] Clearance propagation correct
- [ ] Budget addition verified
- [ ] Provenance tracking complete
- [ ] Inference sound and complete
- [ ] Integration with effects seamless

---

## 8. References

1. Petricek, T., Orchard, D. (2014). "Coeffects: A Calculus of Context-dependent Computation"
2. Orchard, D., Liepelt, V. (2019). "Quantitative Program Reasoning with Graded Modal Types"
3. TERAS Architecture Decision B-01

---

*Architecture Decision Record for TERAS-LANG coeffects.*
