# TERAS RESEARCH DECISION: GRADUAL TYPES
## Session A-10: Boundary-Based Gradual Typing for TERAS-LANG

**Document ID:** RESEARCH_A10_GRADUAL_TYPES_DECISION  
**Version:** 1.0.0  
**Date:** 2026-01-03  
**Status:** APPROVED  
**Classification:** TERAS Research Track - Domain A (Type Theory)

---

## DECISION SUMMARY

| Field | Value |
|-------|-------|
| **Decision ID** | A-10-DEC |
| **Decision Title** | Boundary-Based Gradual Typing |
| **Status** | APPROVED |
| **Date** | 2026-01-03 |

**DECISION STATEMENT:**

ADOPT boundary-based gradual typing for TERAS-LANG with full blame tracking and the gradual guarantee. The unknown type (`?`) is restricted to explicitly marked trust boundaries (FFI, plugins), preserving full static typing for security-critical core code while enabling safe interoperation with untyped external systems.

---

## 1. CONTEXT AND MOTIVATION

### 1.1 Why Gradual Typing for TERAS

TERAS must interact with external systems that lack TERAS-LANG's type guarantees:
- **C Libraries:** FFI to system libraries, hardware interfaces
- **Legacy Code:** Integration with existing untyped systems
- **Plugins:** Third-party extensions without full type info
- **Network Protocols:** Data from untrusted sources

### 1.2 Security Constraints

| Constraint | Requirement |
|------------|-------------|
| Core Security | Full static typing, no escape hatches |
| FFI Safety | Type-checked boundaries with blame |
| Plugin Isolation | Untrusted code cannot bypass types |
| Audit Trail | All type violations traceable |
| Performance | Minimal overhead on hot paths |

### 1.3 What We Reject

1. **Universal `?` Type:** Would undermine security guarantees
2. **Type Erasure:** No runtime checks = no security at boundaries
3. **No Gradual Typing:** Too rigid for practical interoperation

---

## 2. ARCHITECTURE DECISION

### 2.1 Boundary-Based Model

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    TERAS-LANG CORE                          â”‚
â”‚                  (Fully Statically Typed)                   â”‚
â”‚                                                             â”‚
â”‚  - All security properties verified at compile time         â”‚
â”‚  - No `?` type allowed in core code                        â”‚
â”‚  - Linear types, effects, refinements all static           â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
                          â”‚
              â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
              â”‚    TRUST BOUNDARY     â”‚
              â”‚    (Gradual Casts)    â”‚
              â”‚  - Blame tracking     â”‚
              â”‚  - Runtime checks     â”‚
              â”‚  - Security logging   â”‚
              â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
                          â”‚
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                  EXTERNAL SYSTEMS                           â”‚
â”‚                     (Untyped)                               â”‚
â”‚                                                             â”‚
â”‚  - C libraries, plugins, FFI, network data                 â”‚
â”‚  - No type guarantees from TERAS perspective               â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 Type System Extension

**Unknown Type (Restricted):**
```
-- Unknown type only at boundaries
? : BoundaryType    -- Not Type!

-- Cannot appear in core code
fn core_function(x: Int) -> Int { ... }  -- OK
fn bad_function(x: ?) -> ? { ... }       -- ERROR: ? not allowed here

-- Must be in boundary context
boundary ffi {
  fn external(x: ?) -> ?;  -- OK: in boundary
}
```

**Graded Unknown:**
```
-- Unknown with quantity (from A-04)
?_0 : BoundaryType    -- Erased unknown
?_1 : BoundaryType    -- Linear unknown  
?_Ï‰ : BoundaryType    -- Unrestricted unknown (default)

-- Preserves linearity at boundaries
boundary resource_ffi {
  fn acquire() -> ?_1;           -- Returns linear unknown
  fn release(r: ?_1) -> ();      -- Consumes linear unknown
}
```

### 2.3 Boundary Declaration

```teras
-- Declare a trust boundary
#[trust_level(Untrusted)]
boundary crypto_lib {
  // External C library interface
  fn encrypt(key: ?_1, data: ?, len: ?) -> ?;
  fn decrypt(key: ?_1, data: ?, len: ?) -> ?;
  fn free_key(key: ?_1) -> ();
}

-- Typed adapter (what TERAS code sees)
module CryptoLib {
  // Internal: calls boundary with casts
  pub fn encrypt(key: lin uniq Key, data: Bytes) 
    -> Result<Encrypted, CryptoError>
  {
    // Casts insert runtime checks with blame
    let raw_result = boundary_call! {
      crypto_lib.encrypt(
        cast_to_unknown(key),
        cast_to_unknown(data),
        cast_to_unknown(data.len())
      )
    };
    
    // Cast result back with type check
    cast_from_unknown::<Bytes>(raw_result)
      .map(|b| Encrypted::from_bytes(b))
      .map_err(|blame| CryptoError::TypeViolation(blame))
  }
}
```

### 2.4 Blame Tracking System

```teras
-- Blame identifier
type BlameId = struct {
  boundary: BoundaryName,
  function: FunctionName,
  direction: BlameDirection,  // Positive or Negative
  location: SourceLocation,
}

enum BlameDirection {
  Positive,  // Boundary provided wrong value
  Negative,  // Boundary used value incorrectly
}

-- Runtime blame error
type BlameError = struct {
  blame: BlameId,
  expected: TypeDescriptor,
  actual: TypeDescriptor,
  value_repr: String,
  timestamp: Timestamp,
}

-- All blame errors logged for security audit
effect BlameLog {
  fn log_blame(error: BlameError) -> ();
}
```

### 2.5 Cast Semantics

**Cast Operations:**
```teras
-- Cast to unknown (always succeeds)
fn cast_to_unknown<T>(value: T) -> ? {
  // Type information erased but value preserved
  unsafe_erase_type(value)
}

-- Cast from unknown (may fail with blame)
fn cast_from_unknown<T>(value: ?, blame: BlameId) 
  -> eff[BlameLog] Result<T, BlameError>
{
  if runtime_type_check::<T>(value) {
    Ok(unsafe_assume_type::<T>(value))
  } else {
    let error = BlameError {
      blame: blame,
      expected: type_descriptor::<T>(),
      actual: runtime_type_of(value),
      value_repr: debug_repr(value),
      timestamp: now(),
    };
    perform log_blame(error);
    Err(error)
  }
}

-- Function cast (wraps with checks)
fn cast_function<A, B>(
  f: ? -> ?,
  blame: BlameId
) -> (A -> eff[BlameLog] Result<B, BlameError>)
{
  fn wrapper(x: A) -> eff[BlameLog] Result<B, BlameError> {
    let x_unknown = cast_to_unknown(x);
    let result_unknown = f(x_unknown);
    cast_from_unknown::<B>(result_unknown, blame)
  }
  wrapper
}
```

### 2.6 Gradual Guarantee Enforcement

**Precision Ordering:**
```
? âŠ‘ Ï„           -- Unknown is less precise than any type
Ï„ âŠ‘ Ï„           -- Reflexivity
Int âŠ‘ Int       -- Same type equally precise

-- Function types (contravariant in input)
(Ï„â‚ â†’ Ï„â‚‚) âŠ‘ (Ï„â‚' â†’ Ï„â‚‚')  iff  Ï„â‚' âŠ‘ Ï„â‚  and  Ï„â‚‚ âŠ‘ Ï„â‚‚'
```

**Guarantee Statement:**
> If typed boundary code eâ‚ is refined to more precise types eâ‚‚ (eâ‚ âŠ‘ eâ‚‚),
> and both type check, then:
> - eâ‚‚ produces the same results as eâ‚, OR
> - eâ‚‚ fails at compile time (more restrictive), OR  
> - eâ‚‚ produces a blame error earlier than eâ‚

---

## 3. INTEGRATION WITH PRIOR DECISIONS

### 3.1 Integration with A-04 Linear Types

**Linear Unknown:**
```teras
-- Linear boundary values
boundary resource_api {
  fn open_resource(name: ?) -> ?_1;   -- Returns linear
  fn use_resource(r: ?_1) -> ?;       -- Consumes linear
  fn close_resource(r: ?_1) -> ();    -- Consumes linear
}

-- Typed wrapper
module ResourceAPI {
  type Resource = lin uniq Handle;
  
  pub fn open(name: String) -> Result<Resource, Error> {
    let raw = boundary_call! { 
      resource_api.open_resource(cast_to_unknown(name)) 
    };
    // ?_1 cast to lin uniq Handle
    cast_linear_from_unknown::<Handle>(raw)
      .map(|h| Resource::from_handle(h))
  }
  
  pub fn use(r: &Resource) -> Result<Data, Error> {
    // Borrow doesn't consume linearity at boundary
    ...
  }
  
  pub fn close(r: lin Resource) -> () {
    boundary_call! {
      resource_api.close_resource(cast_to_unknown(r))
    };
  }
}
```

### 3.2 Integration with A-05 Effects

**Gradual Effects:**
```teras
-- Unknown effects at boundary
boundary effect_lib {
  fn unknown_effect_fn(x: ?) -> eff[?] ?;  -- Unknown effects
}

-- Must specify expected effects in wrapper
module EffectLib {
  pub fn known_effect(x: Input) -> eff[IO, Error] Output {
    // Cast verifies only declared effects occur
    let result = boundary_call! {
      effect_lib.unknown_effect_fn(cast_to_unknown(x))
    };
    cast_from_unknown_with_effects::<Output, [IO, Error]>(result)
  }
}
```

**Effect Verification:**
```teras
-- Runtime effect checking (optional, for debugging)
fn verify_effects<E: EffectSet>(
  computation: eff[?] ?,
  blame: BlameId
) -> eff[E, BlameLog] Result<?, BlameError>
{
  // Track actual effects during execution
  // Compare with declared effect set E
  // Blame if undeclared effect detected
}
```

### 3.3 Integration with A-09 Dependent Types

**Limited Dependent Graduality:**
```teras
-- Dependent types NOT gradual in core
Vec<Int, n>     -- n must be statically known
Vec<Int, ?>     -- ERROR: length cannot be unknown

-- At boundaries: dynamic length
boundary array_lib {
  fn get_array() -> DynArray;  // Unknown length
}

-- Wrapper must verify length
module ArrayLib {
  pub fn get_vec<const N: Nat>() -> Result<Vec<Int, N>, Error> {
    let dyn_arr = boundary_call! { array_lib.get_array() };
    if dyn_arr.len() == N {
      Ok(unsafe_assume_length::<N>(dyn_arr))
    } else {
      Err(Error::LengthMismatch(expected: N, actual: dyn_arr.len()))
    }
  }
}
```

### 3.4 Integration with A-08 Refinement Types

**Gradual Refinements:**
```teras
-- Refinement unknown
{x: Int | ?}    -- Known type, unknown predicate
{x: ? | ?}      -- Fully unknown (at boundary)

-- Runtime refinement checking
fn cast_refined<T, P: Predicate<T>>(
  value: ?,
  blame: BlameId
) -> eff[BlameLog] Result<{x: T | P(x)}, BlameError>
{
  let typed = cast_from_unknown::<T>(value, blame)?;
  if P(typed) {
    Ok(refined(typed))
  } else {
    Err(BlameError::RefinementViolation(blame, P, typed))
  }
}
```

### 3.5 Integration with A-07 Session Types

**Gradual Sessions (Limited):**
```teras
-- Session types NOT gradual
-- But can interface with untyped protocols via boundaries

boundary network_lib {
  fn send(socket: ?, data: ?) -> ();
  fn recv(socket: ?) -> ?;
}

-- Typed protocol wrapper
module Protocol {
  type AuthChannel<S: SessionState> = lin uniq Chan<S>;
  
  pub fn send_credentials(
    chan: AuthChannel<!Credentials.S>,
    creds: Credentials
  ) -> Result<AuthChannel<S>, Error>
  {
    let raw_socket = chan.raw_socket();
    boundary_call! {
      network_lib.send(raw_socket, serialize(creds))
    };
    Ok(advance_session_state(chan))
  }
}
```

---

## 4. SECURITY PROPERTIES

### 4.1 Blame Theorem for TERAS

**Theorem:** Well-typed TERAS-LANG core code cannot be blamed.

If:
- `Î“ âŠ¢_core e : Ï„` (e is well-typed core code)
- `e` interacts with boundary code through proper casts
- Execution produces `blame(b)`

Then:
- `b` is a boundary identifier (not core code)

**Implication:** Security violations always traceable to untrusted boundaries.

### 4.2 Information Flow Preservation

```teras
-- IFC labels preserved through gradual boundaries
boundary classified_lib {
  fn process(data: ?) -> ?;  -- Unknown labels
}

-- Wrapper enforces label checking
module ClassifiedLib {
  pub fn process_secret<L: SecurityLevel>(
    data: Secret<Data, L>
  ) -> eff[BlameLog] Result<Secret<Output, L>, BlameError>
  {
    // Cast to unknown strips label
    let raw = boundary_call! {
      classified_lib.process(cast_to_unknown(data.value))
    };
    
    // Cast back adds label (conservative: same or higher)
    cast_from_unknown::<Output>(raw)
      .map(|v| Secret::new(v, L))
  }
  
  // ALTERNATIVE: More conservative (disallow)
  // Don't allow secrets through untyped boundaries at all
}
```

### 4.3 Memory Safety at Boundaries

```teras
-- Buffer safety through typed wrappers
boundary c_lib {
  fn memcpy(dst: ?, src: ?, len: ?) -> ();
}

module SafeMemcpy {
  // Safe wrapper with bounds checking
  pub fn copy<const N: Nat, const M: Nat>(
    dst: &mut Buffer<N>,
    src: &Buffer<M>,
    len: {n: Nat | n <= N && n <= M}
  ) -> ()
  {
    boundary_call! {
      c_lib.memcpy(
        dst.as_ptr(),
        src.as_ptr(),
        len
      )
    };
  }
}
```

---

## 5. IMPLEMENTATION ROADMAP

### 5.1 Phased Implementation

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| **Phase 1** | Weeks 1-4 | Boundary declaration syntax |
| **Phase 2** | Weeks 5-8 | Unknown type and casts |
| **Phase 3** | Weeks 9-12 | Blame tracking system |
| **Phase 4** | Weeks 13-16 | Runtime type checking |
| **Phase 5** | Weeks 17-20 | Integration with linear/effects |
| **Phase 6** | Weeks 21-24 | Optimization and testing |

### 5.2 Phase 1: Boundary Declarations

**Deliverables:**
1. `boundary` keyword syntax
2. Trust level annotations
3. Scope restriction (`?` only in boundaries)
4. Wrapper generation scaffolding

### 5.3 Phase 3: Blame Tracking

**Deliverables:**
1. BlameId generation
2. Positive/negative blame
3. Security audit logging
4. Error message formatting

### 5.4 Performance Optimization

**Strategies:**
1. **Cast coalescing:** Merge adjacent casts
2. **Hot path exclusion:** Compiler error if `?` reaches hot code
3. **Monotonic casts:** One-direction refinement
4. **JIT specialization:** Specialize on observed types

---

## 6. ALIGNMENT WITH TERAS PRODUCTS

### 6.1 MENARA (Mobile Security)

```teras
-- Interface with native Android/iOS APIs
boundary android_api {
  fn get_device_id() -> ?;
  fn check_root() -> ?;
  fn get_keystore() -> ?;
}

module AndroidDevice {
  pub fn get_attestation() -> Result<DeviceAttestation, Error> {
    let device_id = boundary_call! { android_api.get_device_id() };
    let root_status = boundary_call! { android_api.check_root() };
    
    // Type-check all external data
    let id = cast_from_unknown::<DeviceId>(device_id)?;
    let rooted = cast_from_unknown::<Bool>(root_status)?;
    
    if rooted {
      Err(Error::DeviceCompromised)
    } else {
      Ok(DeviceAttestation::new(id))
    }
  }
}
```

### 6.2 GAPURA (WAF)

```teras
-- Interface with HTTP parser
boundary http_parser {
  fn parse_request(raw: ?) -> ?;
}

module WAF {
  pub fn process_request(raw: Bytes) 
    -> eff[BlameLog] Result<ValidatedRequest, Error>
  {
    let parsed = boundary_call! {
      http_parser.parse_request(cast_to_unknown(raw))
    };
    
    // Gradual â†’ fully typed
    let request = cast_from_unknown::<RawRequest>(parsed)?;
    
    // Now in typed world: apply rules
    validate_request(request)
  }
}
```

### 6.3 ZIRAH (EDR)

```teras
-- Interface with kernel modules
boundary kernel_api {
  fn register_callback(cb: ?) -> ?;
  fn get_process_info(pid: ?) -> ?;
}

module ProcessMonitor {
  pub fn monitor(callback: fn(ProcessEvent) -> ()) 
    -> Result<MonitorHandle, Error>
  {
    // Wrap typed callback for kernel
    let raw_cb = |raw_event: ?| -> () {
      match cast_from_unknown::<ProcessEvent>(raw_event) {
        Ok(event) => callback(event),
        Err(blame) => log_boundary_error(blame),
      }
    };
    
    let handle = boundary_call! {
      kernel_api.register_callback(cast_to_unknown(raw_cb))
    };
    
    cast_from_unknown::<Handle>(handle).map(MonitorHandle::new)
  }
}
```

---

## 7. DECISION RATIONALE

### 7.1 Why Boundary-Based

1. **Security First:** Core code fully typed, maximum guarantees
2. **Practical:** Still enables FFI and plugins
3. **Auditable:** All boundaries explicitly marked
4. **Performant:** No overhead in typed code

### 7.2 Why Full Blame

1. **Security Attribution:** Know exactly what violated types
2. **Audit Trail:** Complete record for incident response
3. **Gradual Guarantee:** Safe type migration
4. **Trust Modeling:** Clear untrusted boundaries

### 7.3 Why Not Simpler

**TypeScript-style erasure rejected:** No runtime checks = security holes

**Transient checking rejected:** Too weak for security (shallow checks only)

**Full gradual rejected:** `?` anywhere undermines security

---

## 8. RISKS AND MITIGATIONS

| Risk | Severity | Mitigation |
|------|----------|------------|
| Boundary overhead | Medium | Cast coalescing, hot path exclusion |
| Implementation complexity | Medium | Phased rollout, extensive testing |
| Blame information leak | Low | Redact sensitive data in blame |
| Incomplete type checking | High | Comprehensive test suite, fuzzing |
| Performance regressions | Medium | Benchmarks, profiling |

---

## 9. SUCCESS CRITERIA

1. **Soundness:** No type violations bypass boundaries
2. **Blame Accuracy:** All errors traced to correct boundary
3. **Performance:** <2% overhead on boundary-heavy code
4. **Security:** All external data type-checked before use
5. **Usability:** Clean syntax for boundary definitions

---

## 10. APPROVAL AND SIGN-OFF

| Role | Status | Date |
|------|--------|------|
| Type Theory Lead | APPROVED | 2026-01-03 |
| Security Architect | APPROVED | 2026-01-03 |
| TERAS-LANG Lead | APPROVED | 2026-01-03 |

---

## 11. ALIGNMENT SCORE

**Overall Alignment: 8.8/10**

| Dimension | Score | Notes |
|-----------|-------|-------|
| Security | 10/10 | Core fully typed, boundaries protected |
| Practicality | 9/10 | FFI and plugins supported |
| Performance | 8/10 | Overhead only at boundaries |
| A-04 Integration | 9/10 | Linear unknown types work |
| A-05 Integration | 8/10 | Gradual effects supported |
| A-09 Integration | 7/10 | Limited dependent graduality |
| Implementation | 9/10 | Clear phased approach |

---

**END OF DECISION DOCUMENT**

*Document generated for TERAS Research Track - Session A-10*
*Session A-10 COMPLETE*
