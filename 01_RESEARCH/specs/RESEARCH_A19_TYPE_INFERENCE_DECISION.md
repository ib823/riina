# TERAS-LANG Architecture Decision A-19: Type Inference Algorithms

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A19-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL ADOPT** a hybrid inference system combining:

1. **Bidirectional type checking** as the core algorithm
2. **Constraint-based solving** for type classes and families
3. **Union-find unification** for efficient type variable handling
4. **Usage-annotated contexts** for linear/affine type tracking
5. **Label inference** for information flow security
6. **Capability inference** for permission manifests
7. **Blame tracking** for security-focused error messages

### 1.2 Architecture Decision ID

`TERAS-ARCH-A19-INF-001`

### 1.3 Status

**APPROVED** - Ratified for TERAS-LANG implementation

---

## 2. Context and Requirements

### 2.1 Functional Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| INF-01 | Infer types without excessive annotations | Critical |
| INF-02 | Support let-polymorphism | Critical |
| INF-03 | Support higher-rank polymorphism | High |
| INF-04 | Support GADTs and type families | High |
| INF-05 | Support type classes | Critical |
| INF-06 | Infer effect rows | High |
| INF-07 | Infer security labels | Critical |
| INF-08 | Infer capability requirements | Critical |

### 2.2 Quality Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| QUA-INF-01 | Produce clear, localized errors | Critical |
| QUA-INF-02 | Complete type inference in < 1s/KLOC | High |
| QUA-INF-03 | Support incremental re-inference | Medium |
| QUA-INF-04 | Provide type holes for IDE support | Medium |
| QUA-INF-05 | Generate readable inferred types | High |

### 2.3 Security Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| SEC-INF-01 | Infer minimal security labels | Critical |
| SEC-INF-02 | Detect unauthorized declassification | Critical |
| SEC-INF-03 | Generate complete capability manifests | Critical |
| SEC-INF-04 | Track linear resource consumption | High |
| SEC-INF-05 | Verify state machine transitions | High |

---

## 3. Decision Details

### 3.1 Bidirectional Core

The core inference uses two judgment forms:

```
Synthesis (â‡’): Compute type from expression
    Î“ âŠ¢ e â‡’ A âŠ£ Î”
    
Checking (â‡): Verify expression has type
    Î“ âŠ¢ e â‡ A âŠ£ Î”

Where:
    Î“ = input context
    Î” = output context (with solved variables)
```

**Core Rules:**

```
Variable (synthesis):
    (x : A) âˆˆ Î“
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ x â‡’ A âŠ£ Î“

Annotation (synthesis):
    Î“ âŠ¢ e â‡ A âŠ£ Î”
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ (e : A) â‡’ A âŠ£ Î”

Application (synthesis):
    Î“ âŠ¢ eâ‚ â‡’ A âŠ£ Î˜
    Î˜ âŠ¢ A â€¢ eâ‚‚ âŠ£â‡’ C âŠ£ Î”
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ eâ‚ eâ‚‚ â‡’ C âŠ£ Î”

Lambda (checking):
    Î“, x : A âŠ¢ e â‡ B âŠ£ Î”, x : A
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ Î»x. e â‡ A â†’ B âŠ£ Î”

Subsumption (checking):
    Î“ âŠ¢ e â‡’ A âŠ£ Î˜
    Î˜ âŠ¢ A <: B âŠ£ Î”
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e â‡ B âŠ£ Î”
```

### 3.2 Context Structure

```
Context:
    Î“ ::= Â·                    (empty)
        | Î“, x : A             (term variable)
        | Î“, Î±                 (type variable)
        | Î“, Î±Ì‚                 (existential variable)
        | Î“, Î±Ì‚ = Ï„             (solved existential)
        | Î“, â–¸Î±Ì‚                (marker)
        | Î“, x :â‚˜ A            (usage-annotated: m âˆˆ {1, Ï‰})
        | Î“, [cap âˆˆ C]         (capability bound)
        | Î“, [label â‰¤ L]       (label bound)

Context ordering:
    - Variables solved left-to-right
    - Solutions can only refer to earlier bindings
    - Markers delimit scopes for generalization
```

### 3.3 Polymorphism Handling

```
Universal introduction (checking):
    Î“, Î± âŠ¢ e â‡ A âŠ£ Î”, Î±, Î˜
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e â‡ âˆ€Î±. A âŠ£ Î”

Universal elimination (application):
    Î“, â–¸Î±Ì‚, Î±Ì‚ âŠ¢ [Î± â†¦ Î±Ì‚]A â€¢ e âŠ£â‡’ C âŠ£ Î”
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ âˆ€Î±. A â€¢ e âŠ£â‡’ C âŠ£ Î”

Let-polymorphism:
    Î“ âŠ¢ eâ‚ â‡’ A âŠ£ Î˜
    Ïƒ = gen(Î˜, A)              (generalize unsolved existentials)
    Î˜, x : Ïƒ âŠ¢ eâ‚‚ â‡’ B âŠ£ Î”
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ let x = eâ‚ in eâ‚‚ â‡’ B âŠ£ Î”
```

### 3.4 Linear Type Tracking

```
Usage-annotated context:
    Î“ = xâ‚ :_{mâ‚} Aâ‚, ..., xâ‚™ :_{mâ‚™} Aâ‚™
    where m âˆˆ {0, 1, Ï‰} (unused, once, many)

Linear application:
    Î“â‚ âŠ¢ eâ‚ â‡’ A âŠ¸ B âŠ£ Î˜â‚
    Î˜â‚‚ âŠ¢ eâ‚‚ â‡ A âŠ£ Î”
    Î“â‚ âˆ© Î˜â‚‚ = âˆ…                (disjoint usage)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“â‚ âˆª Î˜â‚‚ âŠ¢ eâ‚ eâ‚‚ â‡’ B âŠ£ Î˜â‚ âˆª Î”

Usage checking at scope exit:
    - Linear variables (m=1) must have usage count exactly 1
    - Affine variables (mâ‰¤1) must have usage count 0 or 1
    - Relevant variables (mâ‰¥1) must have usage count â‰¥1
```

### 3.5 Effect Row Inference

```
Effect-annotated function type:
    A -[Îµ]â†’ B    (function with effects Îµ)

Effect row:
    Îµ ::= âŸ¨âŸ© | âŸ¨Eâ‚, Eâ‚‚, ... | ÏâŸ©    (row with tail variable)

Effect inference rule:
    Î“, x : A âŠ¢ e â‡’ B âŠ£ Î”
    Îµ = collectEffects(e)           (effects used in body)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ Î»x. e â‡’ A -[Îµ]â†’ B âŠ£ Î”

Effect polymorphism:
    Î“ âŠ¢ e â‡ âˆ€Ï. A -[Ï]â†’ B âŠ£ Î”     (effect-polymorphic)
```

### 3.6 Security Label Inference

```
Label-annotated type:
    A @ L    (type A at security level L)

Label lattice:
    L ::= Public | Internal | Confidential | Secret | TopSecret
    âŠ‘ : label ordering (flows-to)

Label inference:
    Î“ âŠ¢ e â‡’ A @ L âŠ£ Î”

Join rule:
    Î“ âŠ¢ eâ‚ â‡’ A @ Lâ‚ âŠ£ Î˜
    Î˜ âŠ¢ eâ‚‚ â‡’ B @ Lâ‚‚ âŠ£ Î”
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ (eâ‚, eâ‚‚) â‡’ (A, B) @ (Lâ‚ âŠ” Lâ‚‚) âŠ£ Î”

Declassification checking:
    Î“ âŠ¢ e â‡’ A @ Lâ‚ âŠ£ Î˜
    Lâ‚ âŠ‘ Lâ‚‚                        (flow allowed)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e â‡ A @ Lâ‚‚ âŠ£ Î˜
    
    (If Lâ‚ â‹¢ Lâ‚‚, error: unauthorized declassification)
```

### 3.7 Capability Inference

```
Capability set:
    C = {capâ‚, capâ‚‚, ...}

Capability-annotated function:
    A -[C]â†’ B    (function requiring capabilities C)

Capability collection:
    Î“ âŠ¢ e â‡’ A âŠ£ Î”; C    (C = capabilities required by e)

Primitive operation:
    read_file : Path -[{FileRead}]â†’ ByteString
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ read_file â‡’ Path -[{FileRead}]â†’ ByteString âŠ£ Î“; {FileRead}

Capability composition:
    Î“ âŠ¢ eâ‚ â‡’ A â†’ B âŠ£ Î˜; Câ‚
    Î˜ âŠ¢ eâ‚‚ â‡’ A âŠ£ Î”; Câ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ eâ‚ eâ‚‚ â‡’ B âŠ£ Î”; Câ‚ âˆª Câ‚‚

Capability manifest:
    For each exported function, emit required capability set
```

### 3.8 Constraint Solving

```
Constraint language:
    C ::= Ï„â‚ ~ Ï„â‚‚              (type equality)
        | Ï„â‚ <: Ï„â‚‚             (subtyping)
        | Lâ‚ âŠ‘ Lâ‚‚              (label ordering)
        | cap âˆˆ C              (capability member)
        | D Ï„                  (type class instance)
        | Câ‚ âˆ§ Câ‚‚              (conjunction)
        | âˆƒÎ±. C                (existential)

Solving phases:
    1. Simplify: flatten, reduce type families
    2. Unify: solve equalities with union-find
    3. Entail: check type class instances
    4. Order: verify label constraints
    5. Collect: gather capability requirements
    6. Default: resolve ambiguous variables
```

### 3.9 Unification Implementation

```rust
// Union-find based unification
struct TypeVar {
    id: usize,
    kind: Kind,
    level: Level,  // for generalization
}

struct UnifyState {
    parent: Vec<usize>,
    rank: Vec<u8>,
    types: Vec<TypeRepr>,
}

enum TypeRepr {
    Var,                          // unsolved
    Solved(Type),                 // solved to concrete type
}

impl UnifyState {
    fn unify(&mut self, t1: Type, t2: Type) -> Result<(), TypeError> {
        let t1 = self.find(t1);
        let t2 = self.find(t2);
        
        match (self.repr(t1), self.repr(t2)) {
            (TypeRepr::Var, _) => self.union(t1, t2),
            (_, TypeRepr::Var) => self.union(t2, t1),
            (TypeRepr::Solved(a), TypeRepr::Solved(b)) => {
                self.unify_types(a, b)
            }
        }
    }
    
    fn unify_types(&mut self, t1: Type, t2: Type) -> Result<(), TypeError> {
        match (t1, t2) {
            (Type::Arrow(a1, b1), Type::Arrow(a2, b2)) => {
                self.unify(a1, a2)?;
                self.unify(b1, b2)
            }
            (Type::Con(c1, args1), Type::Con(c2, args2)) if c1 == c2 => {
                for (a, b) in args1.iter().zip(args2.iter()) {
                    self.unify(*a, *b)?;
                }
                Ok(())
            }
            _ => Err(TypeError::Mismatch(t1, t2))
        }
    }
}
```

### 3.10 Error Reporting

```
Error structure:
    TypeError {
        kind: ErrorKind,
        location: Span,
        expected: Type,
        actual: Type,
        context: Vec<ContextFrame>,
        suggestions: Vec<Suggestion>,
    }

Blame tracking:
    - Each constraint carries origin location
    - On failure, trace back to source
    - Present minimal relevant context

Security-specific errors:
    LabelFlowViolation {
        from_label: Label,
        to_label: Label,
        location: Span,
        declassify_hint: Option<String>,
    }
    
    MissingCapability {
        required: CapabilitySet,
        available: CapabilitySet,
        location: Span,
        suggest_annotation: Option<String>,
    }
    
    LinearityViolation {
        variable: String,
        expected_usage: Usage,
        actual_usage: Usage,
        locations: Vec<Span>,
    }
```

---

## 4. Integration with Previous Decisions

### 4.1 Type-Level Computation (A-18)

```
// Type-level functions integrated into inference
fn replicate<n: Nat, T>(value: T) -> Vec<n, T> {
    // n is a type-level natural number
    // Inference solves for n from context
    ...
}

// Type family reduction during constraint solving
type family Add(n: Nat, m: Nat) -> Nat

fn append<n: Nat, m: Nat, T>(
    v1: Vec<n, T>, 
    v2: Vec<m, T>
) -> Vec<Add(n, m), T> {
    // Add(n, m) is reduced during type checking
    ...
}
```

### 4.2 Higher-Kinded Types (A-17)

```
// HKT with bidirectional checking
trait Functor[F: Type -> Type] {
    fn map[A, B](fa: F[A], f: A -> B) -> F[B];
}

// Instance resolution via constraints
fn double_map<F: Functor, G: Functor, A, B>(
    fga: F[G[A]], 
    f: A -> B
) -> F[G[B]] {
    // Inference finds Functor[F] and Functor[G] instances
    F::map(fga, |ga| G::map(ga, f))
}
```

### 4.3 Row Types (A-16)

```
// Row polymorphism with inference
fn get_name<r: Row>(record: { name: String | r }) -> String {
    record.name
}

// r is inferred from context
let person = { name: "Alice", age: 30 };
get_name(person)  // r inferred as { age: Int }
```

### 4.4 Linear Types (A-04)

```
// Linear tracking in bidirectional system
fn consume<T: Linear>(resource: T) -> () {
    drop(resource)  // usage count = 1, OK
}

fn error_example<T: Linear>(resource: T) -> () {
    let x = resource;
    let y = resource;  // ERROR: used twice
    drop(x);
    drop(y);
}
// Error: Linear variable 'resource' used 2 times (expected 1)
//   First use at line 2
//   Second use at line 3
```

### 4.5 Effect Types (A-05, A-11)

```
// Effect inference with rows
fn example() {
    print("hello");  // effect: IO
    throw Error;     // effect: Exn
    // Inferred: <IO, Exn>
}

// Effect polymorphism
fn compose<A, B, C, e1, e2>(
    f: A -[e1]-> B,
    g: B -[e2]-> C
) -> A -[e1 âˆª e2]-> C {
    // Effect union inferred
    |a| g(f(a))
}
```

---

## 5. Implementation Strategy

### 5.1 Inference Pipeline

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                  TERAS-LANG Inference Pipeline                   â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                  â”‚
â”‚  Parse â†’ Desugar â†’ Elaborate â†’ Solve â†’ Zonk â†’ Verify â†’ Lower    â”‚
â”‚              â”‚          â”‚         â”‚        â”‚                     â”‚
â”‚              â–¼          â–¼         â–¼        â–¼                     â”‚
â”‚          Name Res   Generate   Unify    Substitute               â”‚
â”‚          Macro Exp  Context    Classes  Solutions                â”‚
â”‚              â”‚          â”‚         â”‚        â”‚                     â”‚
â”‚              â–¼          â–¼         â–¼        â–¼                     â”‚
â”‚          Module     Bidir     Labels   Check                     â”‚
â”‚          Resolve    Check     Caps     Totality                  â”‚
â”‚                                                                  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 5.2 Phase Details

| Phase | Input | Output | Key Actions |
|-------|-------|--------|-------------|
| Parse | Source | CST | Lexing, parsing |
| Desugar | CST | AST | Expand syntax sugar |
| Elaborate | AST | Core + Constraints | Bidirectional, generate constraints |
| Solve | Constraints | Substitution | Unify, resolve instances |
| Zonk | Core + Subst | Core | Apply substitution |
| Verify | Core | Verified Core | Check linearity, labels, caps |
| Lower | Verified Core | IR | Erase types, optimize |

### 5.3 Data Structures

```rust
// Core inference state
struct InferState {
    // Context management
    context: Context,
    
    // Unification
    unify_state: UnifyState,
    
    // Constraints
    constraints: Vec<Constraint>,
    
    // Security tracking
    label_constraints: Vec<LabelConstraint>,
    capability_sets: HashMap<FnId, CapabilitySet>,
    
    // Linear tracking
    usage_counts: HashMap<VarId, usize>,
    
    // Error collection
    errors: Vec<TypeError>,
    
    // Blame tracking
    constraint_origins: HashMap<ConstraintId, Span>,
}

// Context entry
enum ContextEntry {
    TermVar { name: Name, ty: Type, usage: Usage },
    TypeVar { name: Name, kind: Kind },
    Existential { id: ExistId, kind: Kind },
    Solved { id: ExistId, solution: Type },
    Marker { id: MarkerId },
    LabelBound { var: LabelVar, bound: Label },
    CapBound { var: CapVar, caps: CapabilitySet },
}
```

### 5.4 Incremental Inference

```
Incremental strategy:
1. Cache: Store inferred types per declaration
2. Invalidate: Mark affected declarations on edit
3. Dependency: Track which declarations depend on which
4. Re-infer: Only re-check invalidated declarations
5. Propagate: Update dependents if signature changes

Data structures:
- Declaration graph (dependencies)
- Type cache (declaration â†’ inferred type)
- Dirty set (declarations needing re-inference)
```

---

## 6. TERAS Product Integration

### 6.1 Security Inference by Product

| Product | Inference Focus |
|---------|-----------------|
| MENARA | Permission manifest, trust levels |
| GAPURA | Request/response types, effect rows, taint labels |
| ZIRAH | Process capabilities, scan result types |
| BENTENG | Identity attribute types, verification workflow |
| SANDI | Key algorithm parameters, certificate types |

### 6.2 Example: GAPURA Request Handler

```
// Handler with inferred effects and labels
fn handle_request(req: Request) -> Response {
    let user_input = req.body;           // label: Tainted
    let sanitized = sanitize(user_input); // label: Sanitized
    let result = db_query(sanitized);    // effect: DB
    log_access(req.ip);                  // effect: Log
    Response::ok(result)
}

// Inferred signature:
// handle_request : Request -[DB, Log]-> Response
// with label flow: Tainted â†’ Sanitized â†’ Public

// Capability manifest generated:
// { DatabaseRead, LogWrite }
```

### 6.3 Example: BENTENG Verification Flow

```
// Verification workflow with inferred states
fn verify_identity(docs: Documents) -> Verified<Identity> {
    let extracted = extract_info(docs);     // state: Extracted
    let validated = validate_format(extracted); // state: Validated  
    let verified = cross_check(validated);  // state: Verified
    verified
}

// State transitions inferred and verified:
// Documents â†’ Extracted â†’ Validated â†’ Verified

// Missing transition would be caught:
// fn bad_verify(docs: Documents) -> Verified<Identity> {
//     let extracted = extract_info(docs);
//     verify(extracted)  // ERROR: Cannot transition Extracted â†’ Verified
// }
```

---

## 7. Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Inference too slow | Medium | High | Incremental, caching, parallelization |
| Poor error messages | Medium | High | Blame tracking, constraint origins |
| Incomplete inference | Low | Medium | Clear annotation requirements |
| Security inference unsound | Low | Critical | Formal verification of label rules |
| Complex implementation | High | Medium | Modular design, extensive testing |

---

## 8. Implementation Roadmap

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Core Bidir | 4 weeks | Basic bidirectional checking |
| 2. Unification | 3 weeks | Union-find, constraint solving |
| 3. Polymorphism | 4 weeks | Let-poly, higher-rank |
| 4. Type Classes | 4 weeks | Instance resolution |
| 5. Effects | 3 weeks | Effect row inference |
| 6. Linear | 3 weeks | Usage tracking |
| 7. Security | 4 weeks | Labels, capabilities |
| 8. Errors | 3 weeks | Blame tracking, messages |
| 9. Incremental | 3 weeks | Caching, invalidation |
| **Total** | **31 weeks** | Complete inference system |

---

## 9. Validation Criteria

### 9.1 Correctness

- [ ] Sound: well-typed programs don't go wrong
- [ ] Complete: typeable programs are accepted
- [ ] Principal: inferred types are most general

### 9.2 Performance

- [ ] < 100ms for 1 KLOC file
- [ ] < 1s for 10 KLOC file
- [ ] Incremental re-check < 50ms for single-function edit

### 9.3 Error Quality

- [ ] Errors localized to relevant expression
- [ ] Clear expected vs actual types
- [ ] Security errors explain flow violation
- [ ] Capability errors list missing permissions

### 9.4 Security

- [ ] No false negatives for label violations
- [ ] Complete capability manifest
- [ ] Correct linear usage tracking
- [ ] Valid state machine transitions only

---

## 10. References

1. Dunfield, J., & Krishnaswami, N. (2021). "Bidirectional Typing" (TOPLAS survey)
2. Vytiniotis, D., et al. (2011). "OutsideIn(X)"
3. Damas, L., & Milner, R. (1982). "Principal type-schemes for functional programs"
4. Pottier, F., & RÃ©my, D. (2005). "The Essence of ML Type Inference"
5. TERAS Architecture Decisions A-01 through A-18

---

## 11. Approval

| Role | Name | Date | Signature |
|------|------|------|-----------|
| TERAS Architect | [Pending] | | |
| Language Lead | [Pending] | | |
| Security Lead | [Pending] | | |

---

*Architecture Decision Record for TERAS-LANG type inference system.*
