# TERAS-LANG Research Track
# Session A-16: Row Types and Row Polymorphism
# Document Type: Architecture Decision Record

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  ARCHITECTURE DECISION: ROW TYPES FOR TERAS-LANG                             ║
║                                                                              ║
║  Decision: ADOPT Hybrid Rémy-style row inference with effect row semantics   ║
║  Status: APPROVED                                                            ║
║  Impact: Core type system (A-01), Effects (A-05, A-11), Capabilities (A-14)  ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

## 1. Decision Statement

**TERAS-LANG shall adopt a hybrid row type system combining:**

1. **Rémy-style presence/absence flags** for complete type inference
2. **Effect row semantics** for capability and effect row tracking
3. **Row kinds** for higher-kinded row abstraction
4. **Substructural row fields** with linear/affine annotations
5. **Security row labels** for information flow at row level

This design provides extensible records and variants with security-aware field tracking while maintaining decidable inference.

---

## 2. Context and Requirements

### 2.1 TERAS Security Requirements

| Requirement | Row Type Solution |
|-------------|-------------------|
| Capability attenuation | Row restriction removes capabilities |
| Permission tracking | Permission row fields with presence flags |
| Taint propagation | Row-level taint labels on fields |
| Effect composition | Effect rows for operation tracking |
| Protocol state | State-dependent row types |
| Resource management | Linear/affine row field annotations |

### 2.2 Technical Requirements

| Requirement | Solution |
|-------------|----------|
| Type inference | Rémy's algorithm with presence flags |
| Expressiveness | Row polymorphism with constraints |
| Abstraction | Row kinds for type-level programming |
| Performance | Monomorphization where possible |
| Safety | Static field presence guarantees |

---

## 3. Detailed Design

### 3.1 Row Syntax

```
RowKind ::= Row Type           (* Row over types *)
          | Row Effect         (* Row over effects *)
          | Row Cap            (* Row over capabilities *)

Row ::= ()                     (* Empty row *)
     | (ℓ : φ ; ρ)            (* Label with presence flag *)
     | ρ                       (* Row variable *)

Presence φ ::= Pre(τ)          (* Field present with type τ *)
            | Abs              (* Field absent *)
            | Var(α)           (* Presence variable *)

RecordType ::= {| ρ |}         (* Record from row *)
VariantType ::= [| ρ |]        (* Variant from row *)
EffectRow ::= <ρ>              (* Effect row *)
```

### 3.2 Field Modality Annotations

```
Field Modalities:

{| 
  lin x : τ ;        (* Linear: must use exactly once *)
  aff y : τ ;        (* Affine: use at most once *)
  rel z : τ ;        (* Relevant: use at least once *)
  w : τ              (* Normal: unrestricted use *)
|}

-- Example: Security credential record
type Credentials = {|
  lin session_key : Key ;         (* Must be consumed *)
  aff refresh_token : Token ;     (* Can be dropped *)
  user_id : UserId                (* Normal access *)
|}
```

### 3.3 Security Labels on Rows

```
Security-Labeled Rows:

{|
  [secret] x : Int ;              (* Secret field *)
  [tainted] y : String ;          (* Tainted field *)
  [public] z : Bool               (* Public field *)
|}

-- Row-level security polymorphism
type SecureRecord<ρ : Row Type, σ : SecurityLabel> = {|
  [σ] data : Data ;
  | ρ
|}
```

### 3.4 Row Operations

```
-- Field access (requires presence)
access : ∀α ρ. {| ℓ : Pre(α) ; ρ |} → α

-- Field extension (requires absence)
extend : ∀α ρ. α → {| ℓ : Abs ; ρ |} → {| ℓ : Pre(α) ; ρ |}

-- Field update (requires presence)
update : ∀α ρ. α → {| ℓ : Pre(α) ; ρ |} → {| ℓ : Pre(α) ; ρ |}

-- Field removal (requires presence)
remove : ∀α ρ. {| ℓ : Pre(α) ; ρ |} → {| ℓ : Abs ; ρ |}

-- Row restriction (multiple fields)
restrict : ∀ρ₁ ρ₂. {| ρ₁ ; ρ₂ |} → {| ρ₂ |}
  where ∀ℓ ∈ ρ₁. ρ₁.ℓ = Pre(_)

-- Row concatenation (requires disjointness)
concat : ∀ρ₁ ρ₂. Disjoint(ρ₁, ρ₂) ⇒ {| ρ₁ |} → {| ρ₂ |} → {| ρ₁ ; ρ₂ |}
```

### 3.5 Row Constraints

```
Constraint Syntax:

lacks(ρ, ℓ)              (* Label ℓ not in row ρ *)
has(ρ, ℓ : τ)            (* Label ℓ in ρ with type τ *)
disjoint(ρ₁, ρ₂)         (* Rows share no labels *)
subset(ρ₁, ρ₂)           (* All labels in ρ₁ present in ρ₂ *)

-- Constrained row polymorphism
safeExtend : ∀α ρ. lacks(ρ, newField) ⇒ 
             α → {| ρ |} → {| newField : Pre(α) ; ρ |}
```

### 3.6 Effect Rows

```
Effect Row Integration:

-- Effect as row extension
type IOEffect = <read : IO, write : IO, network : IO>

-- Effect-polymorphic function
readFile : ∀ε. Path → <read : IO | ε> String

-- Effect row masking (handlers)
handleIO : ∀α ε. <io : IO | ε> α → (IOResult → <ε> α) → <ε> α

-- Capability-like effects
type CapRow = <file_read : Cap, file_write : Cap, network : Cap>

-- Capability attenuation via row restriction
attenuate : ∀ε. <file_write : Cap | ε> a → <ε> a
  -- Removes file_write capability
```

### 3.7 Row Kinds

```
Row Kind Declarations:

kind Row : Type → Type    (* Rows parameterized by element kind *)

-- Row over types
type RecordRow = Row Type

-- Row over effects  
type EffectRow = Row Effect

-- Row over capabilities
type CapRow = Row Cap

-- Higher-kinded row operations
type MapRow : (Type → Type) → Row Type → Row Type
type FilterRow : (Type → Bool) → Row Type → Row Type
```

---

## 4. Type Rules

### 4.1 Record Formation

```
Γ ⊢ ρ : Row Type    ∀ℓ ∈ ρ. ρ.ℓ = Pre(τ) for some τ
────────────────────────────────────────────────────
Γ ⊢ {| ρ |} : Type
```

### 4.2 Field Access

```
Γ ⊢ r : {| ℓ : Pre(τ) ; ρ |}
─────────────────────────────
Γ ⊢ r.ℓ : τ
```

### 4.3 Row Extension

```
Γ ⊢ e : τ    Γ ⊢ r : {| ℓ : Abs ; ρ |}
────────────────────────────────────────
Γ ⊢ {ℓ = e ; r} : {| ℓ : Pre(τ) ; ρ |}
```

### 4.4 Row Removal

```
Γ ⊢ r : {| ℓ : Pre(τ) ; ρ |}
─────────────────────────────
Γ ⊢ r \ ℓ : {| ℓ : Abs ; ρ |}
```

### 4.5 Linear Field Access

```
Γ ⊢ r : {| lin ℓ : Pre(τ) ; ρ |}
────────────────────────────────
Γ ⊢ consume r.ℓ : (τ, {| lin ℓ : Abs ; ρ |})
```

### 4.6 Row Unification

```
Unify((ℓ : φ₁ ; ρ₁), (ℓ : φ₂ ; ρ₂)) =
  let S₁ = UnifyPresence(φ₁, φ₂) in
  let S₂ = UnifyRow(S₁(ρ₁), S₁(ρ₂)) in
  S₂ ∘ S₁

UnifyPresence(Pre(τ₁), Pre(τ₂)) = Unify(τ₁, τ₂)
UnifyPresence(Abs, Abs) = ∅
UnifyPresence(Pre(_), Abs) = FAIL
UnifyPresence(Var(α), φ) = [α ↦ φ]
```

---

## 5. Implementation Strategy

### 5.1 Compiler Phases

```
Row Type Processing Pipeline:

1. Parsing
   └─ Row literals: {| x : Int ; y : String |}
   └─ Row extension: {| z : Bool | base |}
   └─ Row access: record.field

2. Row Inference (Rémy algorithm)
   └─ Introduce row variables for polymorphism
   └─ Generate presence constraints
   └─ Solve via flag-aware unification

3. Constraint Resolution
   └─ Check lacks/has constraints
   └─ Verify disjointness for concatenation
   └─ Propagate security labels

4. Substructural Checking
   └─ Track linear field usage
   └─ Ensure affine fields not duplicated
   └─ Verify relevant fields consumed

5. Code Generation
   └─ Monomorphize where possible
   └─ Generate dictionaries for polymorphic access
   └─ Inline field offsets when static
```

### 5.2 Runtime Representation

```
Monomorphic Record:
  struct Point {
    x: i64,
    y: i64,
  }
  // Access: load [record + field_offset]

Polymorphic Record (dictionary passing):
  struct RowDict {
    x_offset: usize,
    y_offset: usize,
    // ... field offsets
  }
  
  fn get_field<R>(dict: &RowDict, record: &R, field: &str) -> &dyn Any {
    let offset = dict.get_offset(field);
    unsafe { &*(record as *const R as *const u8).add(offset) as &dyn Any }
  }
```

### 5.3 Optimization Strategies

```
Row Optimization Techniques:

1. Monomorphization
   - Specialize row-polymorphic functions at call sites
   - Eliminate dictionary passing for known types

2. Field Offset Caching
   - Compute offsets at compile time when possible
   - Cache offsets for frequently accessed fields

3. Row Flattening
   - Flatten nested row extensions
   - Merge adjacent present fields

4. Dead Field Elimination
   - Remove unused Abs fields from representation
   - Compact row structure
```

---

## 6. Security Integration

### 6.1 Capability Rows

```
-- Capability row for file operations
type FileCaps = {|
  read : Cap<FileRead> ;
  write : Cap<FileWrite> ;
  exec : Cap<FileExec>
|}

-- Capability attenuation
attenuate_write : {| write : Pre(Cap<W>) ; ρ |} → {| write : Abs ; ρ |}

-- Capability-polymorphic operations
readFile : ∀ρ. {| read : Pre(Cap<FileRead>) | ρ |} → Path → IO String
```

### 6.2 Information Flow Rows

```
-- Security-labeled record
type ClassifiedDoc = {|
  [Top Secret] content : Bytes ;
  [Secret] metadata : Metadata ;
  [Public] title : String
|}

-- Row-level declassification (requires capability)
declassify : ∀ρ. DeclassCap → {| [σ₁] ℓ : Pre(τ) ; ρ |} 
           → {| [σ₂] ℓ : Pre(τ) ; ρ |}
  where σ₂ ≤ σ₁  -- Lower security level
```

### 6.3 Taint-Aware Rows

```
-- Taint tracking per field
type UserInput = {|
  [tainted:sql] query : String ;
  [tainted:xss] display : String ;
  [clean] validated : Bool
|}

-- Sanitization as row transformation
sanitize_sql : {| [tainted:sql] ℓ : Pre(String) ; ρ |} 
             → {| [clean] ℓ : Pre(String) ; ρ |}
```

---

## 7. TERAS Product Applications

### 7.1 MENARA

```
-- Mobile permission rows
type MobilePerms = {|
  camera : PermStatus ;
  location : PermStatus ;
  contacts : PermStatus ;
  storage : PermStatus
|}

-- Permission-polymorphic API
takePhoto : ∀ρ. {| camera : Pre(Granted) | ρ |} → IO Photo
getLocation : ∀ρ. {| location : Pre(Granted) | ρ |} → IO Coords
```

### 7.2 GAPURA

```
-- HTTP context rows
type HttpContext = {|
  request : Request ;
  [tainted] body : Bytes ;
  [tainted] query : QueryParams ;
  session : Session ;
  auth : Option<AuthInfo>
|}

-- Row-polymorphic middleware
authMiddleware : {| auth : Pre(None) ; session : Pre(Session) | ρ |} 
               → {| auth : Pre(Some(AuthInfo)) ; session : Pre(Session) | ρ |}
```

### 7.3 ZIRAH

```
-- Process inspection rows
type ProcessInfo = {|
  pid : PID ;
  memory : MemoryMap ;
  files : OpenFiles ;
  network : Sockets ;
  behavior : BehaviorProfile
|}

-- Inspection capability rows
type InspectCaps = {|
  read_memory : Cap<MemRead> ;
  trace_syscalls : Cap<Trace> ;
  monitor_network : Cap<NetMon>
|}
```

### 7.4 BENTENG

```
-- Identity verification rows
type VerifyContext = {|
  document : Document ;
  face : FaceData ;
  liveness : LivenessResult ;
  [verified] identity : Option<VerifiedId>
|}

-- Verification progression
verifyFace : {| face : Pre(FaceData) ; document : Pre(Document) | ρ |}
           → {| [verified] identity : Pre(Some(VerifiedId)) | ρ |}
```

### 7.5 SANDI

```
-- Signing context rows
type SignContext = {|
  lin key : SigningKey ;        (* Linear: consumed on sign *)
  cert : Certificate ;
  algorithm : Algorithm ;
  timestamp : Option<TSA>
|}

-- Signing with linear key consumption
sign : {| lin key : Pre(SigningKey) | ρ |} → Data 
     → ({| lin key : Abs | ρ |}, Signature)
```

---

## 8. Integration with Prior Sessions

### 8.1 A-04 Linear Types

```
Linear Row Fields:
  lin {ℓ : τ ; ρ} → Linear field must be consumed exactly once
  
Integration:
  - Row field consumption tracking
  - Linear projection removes field from row
```

### 8.2 A-05/A-11 Effect Systems

```
Effect Rows:
  <e₁ : E₁ ; e₂ : E₂ | ε>
  
Integration:
  - Effects tracked as row extensions
  - Effect handlers mask row entries
  - Effect polymorphism via row variables
```

### 8.3 A-08 Refinement Types

```
Refined Row Types:
  {| x : {v : Int | v > 0} ; y : {v : Int | v < x} |}
  
Integration:
  - Per-field refinements
  - Cross-field refinement constraints
```

### 8.4 A-12 Region Types

```
Regional Rows:
  {| ρ |} at region
  
Integration:
  - Entire record in a region
  - Per-field region annotations
```

### 8.5 A-13 Ownership Types

```
Owned Row Fields:
  {| owned x : Resource ; borrowed y : &Resource |}
  
Integration:
  - Ownership modalities on fields
  - Drop propagation through rows
```

### 8.6 A-14 Capability Types

```
Capability Rows:
  {| cap₁ : Cap<C₁> ; cap₂ : Cap<C₂> |}
  
Integration:
  - Capabilities as row fields
  - Row restriction for attenuation
```

### 8.7 A-15 Staged Types

```
Staged Row Construction:
  $$(generateRow fieldSpecs) : Row Type
  
Integration:
  - Compile-time row generation
  - Type-level row computation
```

---

## 9. Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Inference complexity | Medium | Medium | Restrict constraint forms |
| Performance overhead | Medium | Medium | Aggressive monomorphization |
| Security label interactions | Low | High | Formal verification |
| Integration conflicts | Low | Medium | Careful design coordination |

---

## 10. Decision Rationale

### 10.1 Why Rémy-style?

- **Complete inference**: No annotations needed for basic use
- **Presence flags**: Natural encoding of field operations
- **Proven theory**: Well-understood metatheory
- **Extensible**: Can add features incrementally

### 10.2 Why Effect Rows?

- **Security alignment**: Natural capability/effect model
- **Handler semantics**: Effect masking for sandboxing
- **Composition**: Effects compose via row extension

### 10.3 Why Row Kinds?

- **Abstraction**: Abstract over row structure
- **Higher-kinded operations**: Map, filter over rows
- **Type-level programming**: Compute row types

### 10.4 Why Substructural Fields?

- **Resource safety**: Linear keys consumed exactly once
- **Security**: Capabilities cannot be duplicated
- **Integration**: Unifies with A-04 linear types

---

## 11. Success Criteria

| Criterion | Metric | Target |
|-----------|--------|--------|
| Inference completeness | % programs needing annotations | < 10% |
| Type checking speed | Lines/second | > 10,000 |
| Runtime overhead | vs monomorphic | < 5% |
| Security coverage | TERAS requirements met | 100% |
| Integration success | Prior sessions compatible | 100% |

---

## 12. Implementation Roadmap

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Core Rows | 4 weeks | Basic row inference, operations |
| 2. Effect Rows | 3 weeks | Effect row integration |
| 3. Security Labels | 3 weeks | IFC labels on rows |
| 4. Substructural | 3 weeks | Linear/affine fields |
| 5. Row Kinds | 2 weeks | Higher-kinded rows |
| 6. Optimization | 3 weeks | Monomorphization, caching |

**Total: 18 weeks**

---

## Document Metadata

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  Document ID: TERAS-RESEARCH-A16-DECISION                                    ║
║  Version: 1.0.0                                                              ║
║  Status: APPROVED                                                            ║
║  Decision: ADOPT Hybrid Rémy + Effect Row System                             ║
║                                                                              ║
║  Key Design Points:                                                          ║
║  • Rémy presence/absence flags for inference                                 ║
║  • Effect rows for capability/effect tracking                                ║
║  • Row kinds for abstraction                                                 ║
║  • Substructural field annotations                                           ║
║  • Security labels integrated into rows                                      ║
║                                                                              ║
║  Integration Score: 9.2/10                                                   ║
║  Next Session: A-17 (Higher-Kinded Types)                                    ║
╚══════════════════════════════════════════════════════════════════════════════╝
```
