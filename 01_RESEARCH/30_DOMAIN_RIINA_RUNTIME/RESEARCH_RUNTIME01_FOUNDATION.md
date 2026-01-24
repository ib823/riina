# RIINA-RUNTIME: Verified Execution Environment

## Track Identifier: RUNTIME-01
## Version: 1.0.0
## Status: FOUNDATIONAL SPECIFICATION
## Date: 2026-01-24
## Layer: L5 (Runtime)

---

## 1. PURPOSE

RIINA-RUNTIME is a **formally verified execution environment** that provides memory management, garbage collection, and runtime services with mathematical correctness guarantees. It bridges the gap between verified application code and the verified operating system.

**Core Guarantee:** Runtime services cannot be exploited. Heap corruption, GC attacks, and sandbox escapes are proven impossible.

---

## 2. ARCHITECTURE

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      RIINA APPLICATION CODE                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│                      RIINA-RUNTIME                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ RUNTIME API                                                          │   │
│  │ • Memory allocation    • Exception handling   • Reflection (limited)│   │
│  │ • Type information     • Stack management     • Debug support        │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐            │
│  │ MEMORY MANAGER  │  │ GARBAGE         │  │ SANDBOX         │            │
│  │                 │  │ COLLECTOR       │  │ MANAGER         │            │
│  │ ────────────    │  │ ────────────    │  │ ────────────    │            │
│  │ • Bump alloc    │  │ • Tracing GC    │  │ • Capability    │            │
│  │ • Region alloc  │  │ • Incremental   │  │   isolation     │            │
│  │ • Pool alloc    │  │ • Concurrent    │  │ • Memory limits │            │
│  │ • Free verified │  │ • Verified roots│  │ • CPU limits    │            │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘            │
│                                                                             │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐            │
│  │ STACK MANAGER   │  │ FFI BOUNDARY    │  │ CRYPTO RUNTIME  │            │
│  │                 │  │                 │  │                 │            │
│  │ ────────────    │  │ ────────────    │  │ ────────────    │            │
│  │ • Stack probes  │  │ • Type marshaling│ │ • Constant-time │            │
│  │ • Unwinding     │  │ • Safety checks │  │ • Key handling  │            │
│  │ • Bound checks  │  │ • Capability req│  │ • Zeroization   │            │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘            │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ EXECUTION MODES                                                      │   │
│  │ • Normal mode: Full runtime services                                 │   │
│  │ • Constant-time mode: No branching on secrets, no GC                │   │
│  │ • Real-time mode: Bounded latency, no GC pauses                     │   │
│  │ • Minimal mode: Embedded systems, static allocation only            │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                      RIINA-OS KERNEL                                        │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 3. THREAT MODEL

### 3.1 Threats Eliminated by Construction

| Threat ID | Threat | Elimination Mechanism |
|-----------|--------|----------------------|
| RT-001 | Heap overflow | Allocation bounds proofs |
| RT-002 | Use-after-free | Ownership + GC proofs |
| RT-003 | Double-free | Linear type proofs |
| RT-004 | GC exploitation | GC invariant proofs |
| RT-005 | Type confusion | Runtime type proofs |
| RT-006 | Stack overflow | Stack bound proofs |
| RT-007 | Sandbox escape | Capability isolation proofs |
| RT-008 | FFI type confusion | Marshaling proofs |
| RT-009 | Timing leaks | Constant-time mode proofs |
| RT-010 | Memory exhaustion | Resource accounting proofs |
| RT-011 | Finalizer attacks | Finalizer safety proofs |
| RT-012 | Reflection exploits | Reflection restriction proofs |
| RT-013 | JIT spraying | No JIT (AOT only) |
| RT-014 | Exception handler hijack | Exception safety proofs |
| RT-015 | Secret key leakage | Zeroization proofs |

---

## 4. CORE THEOREMS

### 4.1 Memory Allocator (~80 theorems)

```coq
(* Allocation safety *)
Theorem alloc_safe : forall heap size,
  sufficient_space heap size ->
  exists ptr heap',
    alloc heap size = (ptr, heap') /\
    valid_ptr heap' ptr /\
    accessible_size heap' ptr >= size.

(* No overlap *)
Theorem alloc_no_overlap : forall heap ptr1 ptr2 size1 size2,
  alloc heap size1 = (ptr1, heap1) ->
  alloc heap1 size2 = (ptr2, heap2) ->
  disjoint (ptr1, size1) (ptr2, size2).

(* Free correctness *)
Theorem free_correct : forall heap ptr,
  valid_ptr heap ptr ->
  exists heap',
    free heap ptr = heap' /\
    ~ valid_ptr heap' ptr /\
    preserves_other_ptrs heap heap' ptr.

(* No use-after-free *)
Theorem no_uaf : forall heap ptr,
  freed heap ptr ->
  forall op, ~ can_access heap ptr op.

(* Allocation determinism *)
Theorem alloc_deterministic : forall heap size,
  alloc heap size = alloc heap size.
```

### 4.2 Garbage Collector (~80 theorems)

```coq
(* GC safety - live objects preserved *)
Theorem gc_preserves_live : forall heap roots,
  let heap' := gc heap roots in
  forall obj,
    reachable roots obj ->
    preserved heap heap' obj.

(* GC completeness - dead objects collected *)
Theorem gc_collects_dead : forall heap roots,
  let heap' := gc heap roots in
  forall obj,
    ~ reachable roots obj ->
    ~ in_heap heap' obj.

(* GC root correctness *)
Theorem gc_roots_complete : forall stack registers globals,
  gc_roots stack registers globals = all_live_roots.

(* GC pause bound (incremental) *)
Theorem gc_pause_bound : forall heap,
  incremental_gc_enabled ->
  gc_pause_time heap <= MAX_GC_PAUSE.

(* GC progress *)
Theorem gc_progress : forall heap,
  needs_gc heap ->
  eventually (~ needs_gc (gc_cycle heap)).

(* GC memory bound *)
Theorem gc_memory_bound : forall heap,
  heap_size (after_gc heap) <= MAX_HEAP_SIZE.

(* Finalizer safety *)
Theorem finalizer_safe : forall obj finalizer,
  has_finalizer obj finalizer ->
  runs_exactly_once finalizer obj /\
  no_resurrection finalizer obj.
```

### 4.3 Stack Management (~40 theorems)

```coq
(* Stack bounds *)
Theorem stack_bounded : forall thread,
  stack_size thread <= stack_limit thread.

(* Stack probes *)
Theorem stack_probe_safe : forall frame_size,
  frame_size > PAGE_SIZE ->
  probe_required frame_size.

(* Unwinding correctness *)
Theorem unwind_correct : forall stack exception handler,
  throws stack exception ->
  finds_handler stack exception handler ->
  unwinds_to stack handler /\
  cleans_up_frames stack handler.

(* No stack overflow *)
Theorem no_stack_overflow : forall thread call,
  stack_space_required call <= available_stack thread ->
  safe_to_call thread call.
```

### 4.4 Sandbox Isolation (~50 theorems)

```coq
(* Sandbox memory isolation *)
Theorem sandbox_memory_isolated : forall sandbox1 sandbox2 addr,
  sandbox1 <> sandbox2 ->
  accessible sandbox1 addr ->
  ~ accessible sandbox2 addr.

(* Sandbox capability isolation *)
Theorem sandbox_cap_isolated : forall sandbox cap,
  ~ granted sandbox cap ->
  ~ can_use sandbox cap.

(* Sandbox resource limits *)
Theorem sandbox_resource_limited : forall sandbox resource,
  usage sandbox resource <= limit sandbox resource.

(* Sandbox termination *)
Theorem sandbox_terminable : forall sandbox,
  can_terminate sandbox.

(* Sandbox communication *)
Theorem sandbox_comm_controlled : forall s1 s2 msg,
  sends s1 s2 msg ->
  has_channel s1 s2 /\
  allowed_message_type msg.
```

### 4.5 Constant-Time Execution (~30 theorems)

```coq
(* Constant-time guarantee *)
Theorem constant_time_exec : forall code secret1 secret2,
  constant_time_annotated code ->
  execution_time code secret1 = execution_time code secret2.

(* No secret-dependent branching *)
Theorem no_secret_branch : forall code secret,
  constant_time_annotated code ->
  control_flow code secret = control_flow code (zero_secret secret).

(* No secret-dependent memory access *)
Theorem no_secret_access : forall code secret,
  constant_time_annotated code ->
  access_pattern code secret = access_pattern code (zero_secret secret).

(* Crypto key handling *)
Theorem key_zeroized : forall key scope,
  crypto_key key ->
  exits scope key ->
  zeroized key.
```

### 4.6 FFI Safety (~20 theorems)

```coq
(* FFI type safety *)
Theorem ffi_type_safe : forall riina_val foreign_type,
  marshal riina_val foreign_type ->
  unmarshal (marshaled riina_val) = riina_val.

(* FFI capability requirement *)
Theorem ffi_requires_cap : forall ffi_call,
  can_call ffi_call ->
  has_ffi_cap ffi_call.

(* FFI memory safety *)
Theorem ffi_memory_safe : forall ffi_call,
  ffi_call_safe ffi_call ->
  no_buffer_overflow ffi_call /\
  no_use_after_free ffi_call.
```

---

## 5. EXECUTION MODES

### 5.1 Normal Mode
- Full GC, dynamic allocation
- Suitable for most applications

### 5.2 Constant-Time Mode
```riina
kesan KriptoMod {
    // All operations constant-time
    // GC disabled during crypto ops
    // Stack-only allocation
}

fungsi encrypt(kunci: Rahsia<Kunci>, data: &[u8]) -> Vec<u8>
    kesan KriptoMod
{
    // Compiler enforces constant-time
}
```

### 5.3 Real-Time Mode
```riina
kesan MasaNyata(max_latency: Masa) {
    // Bounded GC pauses
    // Preemption points
    // WCET analysis enabled
}

fungsi kawalan_motor(input: Sensor) -> Output
    kesan MasaNyata(10.ms)
{
    // Guaranteed to complete in 10ms
}
```

### 5.4 Minimal Mode
- No GC, static allocation only
- For embedded systems
- Smallest runtime footprint

---

## 6. DEPENDENCIES

| Dependency | Track | Status |
|------------|-------|--------|
| RIINA type system | Track A | In Progress |
| Ownership types | Track W | Defined |
| RIINA-OS memory | Track OS-01 | Spec |
| Constant-time ops | Track F | Complete |
| WCET analysis | Track V | Defined |

---

## 7. DELIVERABLES

1. **RT-SPEC-001:** Runtime formal specification
2. **RT-PROOF-001:** Memory allocator proofs (80 theorems)
3. **RT-PROOF-002:** Garbage collector proofs (80 theorems)
4. **RT-PROOF-003:** Stack management proofs (40 theorems)
5. **RT-PROOF-004:** Sandbox isolation proofs (50 theorems)
6. **RT-PROOF-005:** Constant-time proofs (30 theorems)
7. **RT-PROOF-006:** FFI safety proofs (20 theorems)
8. **RT-IMPL-001:** RIINA runtime source
9. **RT-TEST-001:** Runtime test suite

**Total: ~300 theorems**

---

## 8. REFERENCES

1. CakeML Verified Runtime
2. Bedrock (verified low-level programming)
3. Cogent (verified systems programming)
4. CompCert runtime model

---

*RIINA-RUNTIME: Where Memory Safety Meets Mathematical Proof*

*"Segfault is not in our vocabulary."*
