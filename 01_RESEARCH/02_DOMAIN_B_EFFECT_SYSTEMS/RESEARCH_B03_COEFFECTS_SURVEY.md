# TERAS-LANG Research Survey B-03: Coeffects

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B03-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-03 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Coeffects are the dual of effects, tracking contextual requirements rather than computational side effects. While effects describe what a computation produces (state changes, I/O), coeffects describe what a computation requires (resources, capabilities, environment). This survey covers coeffect theory, graded comonads, and applications to resource tracking, with emphasis on security applications for TERAS.

---

## Part 1: Foundations

### 1.1 Effects vs Coeffects

```
Effects (what computation PRODUCES):
├── State modification
├── I/O operations  
├── Exceptions thrown
├── Nondeterminism
└── Resource allocation

Coeffects (what computation REQUIRES):
├── Variables in scope
├── Implicit parameters
├── Capabilities needed
├── Resources consumed
├── Context dependencies
```

### 1.2 Categorical Duality

```
Effect:     Monad     (T, η, μ)
Coeffect:   Comonad   (D, ε, δ)

Monad:
    return :: a → T a           (unit)
    join   :: T (T a) → T a     (multiplication)
    
Comonad:
    extract   :: D a → a        (counit)
    duplicate :: D a → D (D a)  (comultiplication)

Graded versions:
    Graded Monad:   T_r with r ∈ Monoid
    Graded Comonad: D_r with r ∈ Monoid (coeffects!)
```

### 1.3 Historical Development

```
Timeline:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
2010    │ Uustalu, Vene: Comonads in Haskell
2012    │ Petricek et al: "Coeffects" paper (ICALP)
2013    │ Orchard, Petricek: Coeffects for F#
2014    │ Brunel et al: Bounded Linear Logic connection
2016    │ Gaboardi et al: Granule language
2017    │ Petricek: Coeffects thesis
2018    │ Orchard, Liepelt: Granule refinements
2020    │ Granule language v0.8+
2022    │ Continued research applications
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## Part 2: Coeffect Theory

### 2.1 Graded Comonads

```
Definition (Graded Comonad):
A graded comonad over a monoid (R, ·, 1) consists of:
- Type constructor D_r : Type → Type for each r ∈ R
- extract : D_1 a → a
- duplicate : D_r a → D_s (D_{r·s⁻¹} a)  [for appropriate s]

Or using indexed comonads:
- extract : D_1 a → a
- extend : (D_s a → b) → D_{r·s} a → D_r b
```

### 2.2 Coeffect Typing Rules

```
Coeffect Typing Judgment:
    Γ ⊢_r e : A
    
Meaning: Under context Γ with coeffect requirement r,
         expression e has type A.

Rules:

    ──────────────────────────     (Variable)
    x : A ⊢_1 x : A

    Γ ⊢_r e : A    Δ ⊢_s f : A → B
    ─────────────────────────────────     (Application)
    Γ, Δ ⊢_{r·s} f e : B

    Γ, x : A ⊢_r e : B
    ─────────────────────────     (Abstraction)
    Γ ⊢_r λx. e : A →_r B        (r annotates arrow!)

Coeffect-annotated function type:
    A →_r B  means: function requires coeffect r
```

### 2.3 Common Coeffect Structures

**2.3.1 Natural Numbers (Resource Counting)**

```
R = (ℕ, +, 0)

Interpretation:
    r = n means "uses variable n times"
    
Rules:
    x : A ⊢_1 x : A              (one use)
    Γ ⊢_n e : A    n ≥ 1
    ────────────────────────     (contraction)
    Γ ⊢_1 e : A
```

**2.3.2 Bounded Natural Numbers (Bounded Usage)**

```
R = (ℕ_∞, max, 0)  where ℕ_∞ = ℕ ∪ {∞}

Interpretation:
    r = n means "uses variable at most n times"
    r = ∞ means "unlimited use"
```

**2.3.3 Capability Sets**

```
R = (𝒫(Cap), ∪, ∅)

Interpretation:
    r = {read, write} means "requires read and write capabilities"
    
Typing:
    read_file : String →_{read} ByteString
    write_file : String → ByteString →_{write} ()
```

**2.3.4 Security Levels**

```
R = (SecurityLevel, ⊔, ⊥)

Levels: Public ⊏ Internal ⊏ Confidential ⊏ Secret

Interpretation:
    r = Confidential means "requires Confidential clearance"
```

### 2.4 Contextual Modal Type Theory

```
Nanevski et al: Contextual Modal Type Theory (2008)

□_Γ A = type of code with free variables from Γ

Formation:
    Γ ⊢ A type
    ────────────────
    · ⊢ □_Γ A type

Introduction:
    Γ ⊢ e : A
    ────────────────────
    · ⊢ box e : □_Γ A

Elimination:
    · ⊢ e₁ : □_Γ A    Γ, u : A ⊢ e₂ : B
    ─────────────────────────────────────────
    Γ ⊢ letbox u = e₁ in e₂ : B
```

---

## Part 3: Implementations

### 3.1 Granule Language

```granule
-- Granule: coeffects for resource tracking

-- Linear function (uses argument exactly once)
id : a -> a
id x = x

-- Graded function (uses argument r times)
double : Int -> Int [2]  -- uses input twice
double x = x + x

-- Capability coeffects
readFile : String -> String [read]
writeFile : String -> String -> () [write]

-- Combining coeffects
copyFile : String -> String -> () [read, write]
copyFile src dst = writeFile dst (readFile src)
```

**Granule Type System:**

```
Types:
    A ::= α | A → B | A →_r B | □_r A | ...

Grading:
    r ::= 0 | 1 | n | r + s | r * s | ...

Key Rules:
    Γ ⊢_r e : A    r ≤ s
    ────────────────────────     (Weakening)
    Γ ⊢_s e : A

    Γ ⊢_r e : □_s A
    ────────────────────────     (Unbox)
    Γ ⊢_{r*s} unbox e : A
```

### 3.2 Coeffects in F#

```fsharp
// Petricek's coeffect tracking for F#

// Implicit parameters (reader coeffect)
let greet (implicit name : string) = "Hello, " + name

// Dataflow (past values)
let movingAvg (past 3) (stream : float seq) =
    stream |> Seq.windowed 3 |> Seq.map Seq.average

// Resource tracking
let readFile [requires: FileSystem] path = 
    System.IO.File.ReadAllText(path)
```

### 3.3 Context-Aware Programming

```
Coeffect applications:

1. Implicit Parameters:
   - Track what implicit values are needed
   - Similar to Scala implicits
   
2. Dataflow Dependencies:
   - Track how much history is needed
   - Stream processing optimization

3. Platform Requirements:
   - Track what APIs/features are required
   - Cross-platform code safety

4. Resource Usage:
   - Track bounded resource consumption
   - Memory/time budgets
```

### 3.4 Comonadic Coeffects in Haskell

```haskell
-- Comonad class
class Functor w => Comonad w where
    extract :: w a -> a
    duplicate :: w a -> w (w a)
    extend :: (w a -> b) -> w a -> w b
    extend f = fmap f . duplicate

-- Environment comonad (reader coeffect)
data Env e a = Env e a

instance Comonad (Env e) where
    extract (Env _ a) = a
    duplicate (Env e a) = Env e (Env e a)

-- Using comonads for contextual computation
ask :: Env e a -> e
ask (Env e _) = e

local :: (e -> e') -> Env e a -> Env e' a
local f (Env e a) = Env (f e) a

-- Traced comonad (writer coeffect dual)
data Traced m a = Traced (m -> a)

instance Monoid m => Comonad (Traced m) where
    extract (Traced f) = f mempty
    duplicate (Traced f) = Traced $ \m -> Traced $ \m' -> f (m <> m')
```

---

## Part 4: Coeffects for Security

### 4.1 Capability Coeffects

```
effect Capability<C: Cap> coeffect {
    // Coeffect: computation REQUIRES capability C
}

// Type-level capability tracking
fn read_secret() -[requires: SecretAccess]-> Secret {
    // Can only be called in contexts with SecretAccess
}

// Capability propagation
fn process_data() -[requires: {FileRead, NetworkAccess}]-> Result {
    let data = read_file("input.txt");  // requires FileRead
    let result = fetch_url("...");       // requires NetworkAccess
    process(data, result)
}

// Capability attenuation
fn attenuate<C1, C2>(f: () -[requires: C1]-> A) -[requires: C2]-> A
where
    C1 ⊆ C2  // C2 has at least C1's capabilities
{
    f()
}
```

### 4.2 Security Clearance Coeffects

```
// Security levels as coeffect grades
type ClearanceLevel = Public | Internal | Confidential | Secret | TopSecret;

// Clearance-graded functions
fn read_public_data() -[clearance: Public]-> Data { ... }
fn read_secret_data() -[clearance: Secret]-> Data { ... }

// Clearance propagation (join)
fn combine_data() -[clearance: Secret]-> CombinedData {
    // Requires Secret because calls read_secret_data
    let public = read_public_data();
    let secret = read_secret_data();
    combine(public, secret)
}

// Clearance checking at boundaries
fn api_endpoint(request: Request) -[clearance: ?]-> Response {
    match authenticate(request) {
        Clearance::Public => handle_public(request),
        Clearance::Secret => handle_secret(request),  // compile-time safe
    }
}
```

### 4.3 Resource Budget Coeffects

```
// Resource consumption tracking
type Budget = { time: Duration, memory: Bytes, calls: u32 };

// Budget-graded functions
fn expensive_computation() -[budget: { time: 100ms, memory: 1MB }]-> Result { ... }

fn cheap_computation() -[budget: { time: 1ms, memory: 1KB }]-> Result { ... }

// Budget composition (addition)
fn combined() -[budget: { time: 101ms, memory: 1MB + 1KB }]-> (Result, Result) {
    let r1 = expensive_computation();  // 100ms, 1MB
    let r2 = cheap_computation();      // 1ms, 1KB
    (r1, r2)
}

// Budget checking
fn within_budget<R, B: Budget>(
    f: () -[budget: B]-> R,
    available: B
) -> Option<R>
where
    B <= available  // Compile-time budget check
{
    Some(f())
}
```

### 4.4 Provenance Coeffects

```
// Track data provenance as coeffect
type Provenance = Set<Source>;

// Provenance-graded data
fn user_input() -[provenance: {UserInput}]-> String { ... }
fn config_file() -[provenance: {ConfigFile}]-> Config { ... }
fn database() -[provenance: {Database}]-> Record { ... }

// Provenance propagation
fn process_request() -[provenance: {UserInput, Database}]-> Response {
    let input = user_input();      // provenance: {UserInput}
    let record = database();       // provenance: {Database}
    process(input, record)         // provenance: {UserInput, Database}
}

// Provenance-based security policy
fn sensitive_operation(data: Data) -[provenance: P]-> Result
where
    {UserInput} ∩ P = ∅  // No user input in sensitive op
{
    // Type system ensures no tainted data
}
```

---

## Part 5: Coeffects + Effects

### 5.1 Combined System

```
Full effect/coeffect typing:

    Γ ⊢ e : A ! ε @ r
    
Where:
    ε = effect (what computation produces)
    r = coeffect (what computation requires)

Example:
    read_file : Path →_{FileRead} ByteString ! IO @ {fs_capability}
                       ^^^^^^^^^^             ^^   ^^^^^^^^^^^^^^^^
                       coeffect grade         effect   coeffect
```

### 5.2 Effect-Coeffect Interaction

```rust
// Effect with coeffect requirements
effect Log coeffect Audit {
    fn log(level: Level, msg: &str) -> ()
        requires: AuditCapability;
}

// Handler must satisfy coeffect
handler audit_handler for Log @ {AuditCapability} {
    // Has AuditCapability, can handle Log
    return(x) => x,
    log(level, msg) resume => {
        write_audit_log(level, msg);
        resume(())
    }
}

// Computation with both
fn secure_operation() -[Log]-> Result @ {AuditCapability, SecretAccess} {
    Log::log(Info, "Starting operation");
    let secret = read_secret();  // requires SecretAccess
    process(secret)
}
```

### 5.3 Graded Modal Types

```
Graded necessity (coeffect):
    □_r A = computation of A requiring r
    
Graded possibility (effect):
    ◇_r A = computation of A producing r
    
Combined:
    □_r ◇_s A = requires r, produces s, returns A
```

---

## Part 6: Technical Deep Dive

### 6.1 Coeffect Inference

```
Constraint Generation:
    Γ ⊢ e : A ⇒ (τ, C)
    
Where:
    τ = inferred type
    C = coeffect constraints

Example:
    f x y = x + y
    
Inference:
    x : Int @ r₁
    y : Int @ r₂
    (+) : Int → Int → Int @ {1, 1}
    
    Constraints: r₁ ≥ 1, r₂ ≥ 1
    Result: f : Int →₁ Int →₁ Int
```

### 6.2 Coeffect Polymorphism

```granule
-- Polymorphic over coeffect grade
map : forall r a b. (a -> b) [r] -> List a -> List b [r]
map f []        = []
map f (x :: xs) = f x :: map f xs

-- Usage
double : Int -> Int [1]
double x = x + x

-- Inferred: map double : List Int -> List Int [1]
```

### 6.3 Coeffect Subtyping

```
Coeffect ordering (when r ≤ s means "s has at least r"):

    r ≤ s
    ─────────────────────
    A →_s B <: A →_r B    (contravariant in coeffect)

Example:
    FileRead ⊆ {FileRead, FileWrite}
    
    f : A →_{FileRead, FileWrite} B
    g : A →_{FileRead} B → C
    
    g f : A → C   ✓ (f provides more than needed)
```

---

## Part 7: Applications to TERAS

### 7.1 TERAS Coeffect System

```rust
// Core coeffect dimensions for TERAS

coeffect Clearance: SecurityLevel {
    Public < Internal < Confidential < Secret < TopSecret
}

coeffect Capability: Set<Cap> {
    combine: union
    empty: {}
}

coeffect Budget: ResourceBudget {
    combine: add
    empty: zero
}

coeffect Provenance: Set<Source> {
    combine: union
    empty: {}
}
```

### 7.2 Product-Specific Coeffects

```rust
// MENARA: Mobile security
coeffect MobileContext {
    network: NetworkType,      // WiFi, Cellular, None
    battery: BatteryLevel,     // High, Medium, Low, Critical
    location: LocationAccess,  // Precise, Coarse, None
}

// GAPURA: WAF
coeffect RequestContext {
    client_ip: IPAddress,
    rate_limit: RateBucket,
    auth_level: AuthLevel,
}

// ZIRAH: EDR
coeffect ScanContext {
    privilege: PrivilegeLevel,  // User, Admin, Kernel
    isolation: IsolationLevel,  // None, Sandbox, VM
    time_budget: Duration,
}

// BENTENG: Identity
coeffect VerificationContext {
    documents: Set<DocumentType>,
    confidence: ConfidenceLevel,
    jurisdiction: Jurisdiction,
}

// SANDI: Digital signatures
coeffect CryptoContext {
    key_access: Set<KeyHandle>,
    algorithm_approval: Set<Algorithm>,
    hsm_session: Option<HSMSession>,
}
```

### 7.3 Coeffect Checking at Boundaries

```rust
// API boundary coeffect checking
#[coeffect(requires = {Clearance::Secret, Capability::{FileRead}})]
fn secure_api_endpoint(request: Request) -> Response {
    // Compiler ensures caller has required coeffects
}

// Dynamic coeffect checking for untrusted contexts
fn handle_external_request(
    request: Request,
    context: DynamicCoeffect
) -> Result<Response, CoeffectError> {
    // Runtime check of dynamic coeffects
    context.require(Clearance::Secret)?;
    context.require(Capability::FileRead)?;
    
    // Proceed with checked context
    secure_api_endpoint(request)
}
```

---

## Part 8: Summary

### 8.1 Key Insights

1. **Coeffects complement effects**: Effects track outputs, coeffects track inputs/requirements
2. **Graded types enable fine-grained tracking**: Usage counts, capability sets, security levels
3. **Comonads provide semantic foundation**: Clean categorical structure
4. **Security is natural fit**: Capabilities, clearances, provenance all model as coeffects

### 8.2 TERAS Relevance

| Coeffect Type | TERAS Application |
|---------------|-------------------|
| Capability | Permission enforcement |
| Clearance | Security level tracking |
| Provenance | Taint/origin tracking |
| Budget | Resource limiting |
| Context | Environment requirements |

### 8.3 Recommendations

1. **Integrate coeffects with effect system** (B-01)
2. **Use capability coeffects for permissions** 
3. **Use clearance coeffects for IFC**
4. **Implement coeffect inference for usability**

---

## Part 9: Bibliography

1. Petricek, T., Orchard, D., Mycroft, A. (2014). "Coeffects: A Calculus of Context-dependent Computation"
2. Brunel, A., Gaboardi, M., et al. (2014). "Coeffects for Fuzz"
3. Orchard, D., Liepelt, V., Eades, H. (2019). "Quantitative Program Reasoning with Graded Modal Types"
4. Gaboardi, M., et al. (2016). "Combining Effects and Coeffects via Grading"
5. Uustalu, T., Vene, V. (2008). "Comonadic Notions of Computation"
6. Granule Language Documentation

---

*Research Track Output — Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
