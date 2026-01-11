# TERAS-LANG Research C-06 through C-10: Remaining IFC Topics

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C06-C10-COMBINED |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | C-06 through C-10 |
| Domain | C: Information Flow Control |
| Status | Complete |

---

# C-06: Taint Analysis

## Executive Summary

Taint analysis tracks potentially malicious data through programs, a specialized form of IFC for security vulnerabilities.

## Key Concepts

### Taint Sources and Sinks

```rust
// Sources: Where tainted data enters
#[taint_source(UserInput)]
fn read_user_input() -> String { ... }

#[taint_source(NetworkData)]
fn recv_network() -> Bytes { ... }

// Sinks: Where taint must be checked
#[taint_sink(SqlQuery)]
fn execute_sql(query: String) { ... }

#[taint_sink(HtmlOutput)]
fn render_html(content: String) { ... }
```

### Taint Propagation

```rust
// Taint flows through operations
let user_input = read_user_input();  // Tainted: {UserInput}
let modified = user_input + " suffix"; // Still tainted: {UserInput}
let combined = modified + network_data; // Tainted: {UserInput, NetworkData}
```

### Sanitization

```rust
// Sanitizers remove specific taints
#[sanitizer(removes: UserInput, for: SqlQuery)]
fn escape_sql(input: String) -> String { ... }

#[sanitizer(removes: UserInput, for: HtmlOutput)]
fn escape_html(input: String) -> String { ... }

// Usage
let safe = escape_sql(user_input);  // Taint removed for SQL context
execute_sql(safe);  // OK: sanitized
```

## TERAS Decision C-06

**ADOPT** taint analysis integrated with IFC:
1. Taint as integrity labels
2. Product-specific sources/sinks
3. Sanitizer annotations
4. Static taint inference

### Architecture Decision ID: `TERAS-ARCH-C06-TNT-001`

---

# C-07: Language-Based IFC Survey

## Languages Surveyed

| Language | Type | Labels | Inference | Production |
|----------|------|--------|-----------|------------|
| Jif | Static | DLM | Partial | Research |
| FlowCaml | Static | Lattice | Full | Research |
| Paragon | Static | DLM | Full | Research |
| LIO | Dynamic | Lattice | N/A | Production |
| JSFlow | Dynamic | Lattice | N/A | Research |
| Jeeves | Hybrid | Policies | Full | Research |

## Lessons for TERAS

1. **Full inference critical** - Manual annotation burden too high
2. **DLM valuable** - Decentralized authority needed
3. **Hybrid best** - Static where possible, dynamic for flexibility
4. **Integration essential** - Must work with rest of type system

## TERAS Decision C-07

**ADOPT hybrid approach** with:
- Static IFC as default
- Dynamic IFC for runtime-determined labels
- Full label inference
- DLM for authority

### Architecture Decision ID: `TERAS-ARCH-C07-LNG-001`

---

# C-08: IFC for Concurrent Programs

## Challenges

```
Concurrency introduces new channels:

1. Timing channels
   if secret then long_computation() else short_computation()
   // Observable via timing

2. Resource contention
   lock(mutex)  // Contention reveals information
   
3. Scheduling
   Thread execution order may depend on secrets
```

## Solutions

### 1. Deterministic Parallelism

```rust
// Parallel but deterministic
fn parallel_map<F>(data: Vec<T @ L>, f: F) -> Vec<U @ L>
where F: Fn(T) -> U + Sync
{
    // Deterministic scheduling, no timing leaks
    data.par_iter().map(f).collect()
}
```

### 2. Noninterference-Preserving Concurrency

```rust
// Spawn at same label
fn spawn_at_label<L: Label>(f: impl FnOnce() -> () @ L) -> JoinHandle<()> {
    // Thread inherits caller's label
    // Cannot communicate with different-label threads
}
```

### 3. Isolation

```rust
// Separate security domains
fn isolated_execution<A>(
    secret_task: impl FnOnce() -> A @ Secret,
    public_task: impl FnOnce() -> B @ Public
) -> (A, B) {
    // Run in separate isolated contexts
    // No timing correlation possible
}
```

## TERAS Decision C-08

**ADOPT**:
1. Deterministic parallel primitives
2. Label-aware thread spawning
3. Isolation for security domains
4. Conservative timing channel treatment

### Architecture Decision ID: `TERAS-ARCH-C08-CON-001`

---

# C-09: IFC and Effects

## Integration with Effect System

```rust
// IFC as effect
effect IFC<L: Label> {
    fn label<T>(value: T) -> T @ L;
    fn unlabel<T>(labeled: T @ L) -> T;  // Raises PC
}

// IFC as coeffect
fn secure_operation() -[IO]-> Result 
    @ {Clearance::Secret}  // Coeffect requirement
{
    // Can access Secret data
}
```

## Handler-Based IFC

```rust
// IFC handler tracks PC
handler ifc_handler<L: Label>(clearance: L) for IFC<L> {
    var pc: Label = Public;
    
    unlabel(labeled) resume => {
        assert!(labeled.label.can_flow_to(&clearance));
        pc = pc.join(&labeled.label);
        resume(labeled.value)
    }
    
    // Write operations check PC
    // ...
}
```

## TERAS Decision C-09

**INTEGRATE** IFC with effect system (B-01):
1. Clearance as coeffect
2. PC tracking in handlers
3. Security effects for label operations
4. Unified typing judgment

### Architecture Decision ID: `TERAS-ARCH-C09-EFF-001`

---

# C-10: IFC in Practice

## Real-World Challenges

```
Production IFC challenges:

1. Legacy integration
   - Gradual adoption needed
   - Interop with unlabeled code

2. Performance
   - Dynamic checks overhead
   - Label storage costs

3. Usability
   - Error message clarity
   - Developer training

4. Policy management
   - Defining correct policies
   - Policy evolution
```

## Deployment Patterns

### Gradual Adoption

```rust
// Start with boundaries
#[ifc_boundary]
mod secure_module {
    // Full IFC enforcement inside
}

// Legacy code treated as Public/Untrusted
fn legacy_function() -> String @ (Public, Untrusted) { ... }
```

### Security Wrappers

```rust
// Wrap legacy APIs
fn safe_database_query(
    query: String @ Trusted  // Must be trusted
) -> Vec<Row> @ Confidential {
    let result = legacy_db_query(&query);  // Legacy code
    label(result, Confidential)
}
```

## TERAS IFC Summary

### Final Design

```rust
// Security label
pub struct Label {
    level: SecurityLevel,       // 5 levels
    compartments: Set<String>,  // Need-to-know
    integrity: IntegrityLevel,  // Trust
    owner: Option<Principal>,   // DLM
    readers: Option<Set<Principal>>,
}

// Labeled type
type Labeled<L, T> = T @ L;

// IFC operations
fn label<L, T>(value: T, label: L) -> T @ L;
fn unlabel<L, T>(labeled: T @ L) -> T;  // Raises PC
fn declassify<L1, L2, T>(value: T @ L1) -> T @ L2;  // Policy-controlled
fn endorse<T>(value: T @ Untrusted) -> T @ Trusted;  // After validation

// Integration
// - Effects: Security operations as effects
// - Coeffects: Clearance requirements
// - Inference: Full label inference
// - Audit: All operations logged
```

## TERAS Decision C-10

**FINALIZE** IFC design:
1. Full integration with TERAS type system
2. Gradual adoption support
3. Legacy interop patterns
4. Comprehensive documentation

### Architecture Decision ID: `TERAS-ARCH-C10-PRA-001`

---

# Domain C Summary

## Completed Sessions

| Session | Topic | Decision ID |
|---------|-------|-------------|
| C-01 | IFC Foundations | TERAS-ARCH-C01-IFC-001 |
| C-02 | Security Types | TERAS-ARCH-C02-STY-001 |
| C-03 | Label Models | TERAS-ARCH-C03-LBL-001 |
| C-04 | Declassification | TERAS-ARCH-C04-DCL-001 |
| C-05 | Dynamic IFC | TERAS-ARCH-C05-DYN-001 |
| C-06 | Taint Analysis | TERAS-ARCH-C06-TNT-001 |
| C-07 | Language Survey | TERAS-ARCH-C07-LNG-001 |
| C-08 | Concurrency | TERAS-ARCH-C08-CON-001 |
| C-09 | Effects Integration | TERAS-ARCH-C09-EFF-001 |
| C-10 | Practice | TERAS-ARCH-C10-PRA-001 |

## Key Decisions

1. **Static IFC** with dynamic fallback
2. **DLM-style labels** with inference
3. **Robust declassification** with audit
4. **Integration** with effects and coeffects
5. **Gradual adoption** for legacy systems

---

## Domain C: COMPLETE

**Total Documents: 15**
- 10 surveys (combined in larger files)
- 10 decisions

Ready for Domain D: Capability-Based Security

---

*Research Track Output — Domain C: Information Flow Control*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
