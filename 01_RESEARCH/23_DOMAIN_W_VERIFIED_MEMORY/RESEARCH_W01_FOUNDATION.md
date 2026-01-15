# TERAS-LANG Research Domain W: Verified Memory Management

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-W-VERIFIED-MEMORY |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | W: Verified Memory Management |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# W-01: The "Memory Corruption" Problem & The TERAS Solution

## 1. The Existential Threat

**Context:**
Memory corruption vulnerabilities have been the #1 class of security bugs for 50 years:
- Buffer overflows (Morris Worm, 1988)
- Use-after-free (still ~70% of Chrome/Windows CVEs in 2024)
- Double-free
- Heap spraying
- Type confusion via memory corruption

**The TERAS Reality:**
Our type system prevents logical type errors. But the RUNTIME memory allocator is a separate component. If the allocator is buggy:
- It could return overlapping memory regions
- It could allow access to freed memory
- It could corrupt internal metadata

A buggy allocator can **bypass all type-system guarantees**.

**The Goal:**
Formally verify the memory allocator. Prove it is IMPOSSIBLE for memory corruption to occur at the implementation level.

## 2. The Solution: Verified Allocator with Separation Logic

We will implement a memory allocator that is **proven correct** using separation logic, following the methodology of seL4 and CertiKOS.

### 2.1 The Core Properties

The allocator must satisfy:

#### Property 1: Non-Overlapping Allocations
$$
\forall p_1, p_2. \text{allocated}(p_1) \land \text{allocated}(p_2) \land p_1 \neq p_2 \implies \text{disjoint}(p_1, p_2)
$$

#### Property 2: Freshness
$$
\forall p. \text{allocate}() = p \implies \neg\text{previously\_accessible}(p)
$$

#### Property 3: Use-After-Free Prevention
$$
\forall p. \text{free}(p) \implies \neg\text{accessible}(p) \text{ until reallocated}
$$

#### Property 4: Double-Free Prevention
$$
\forall p. \text{free}(p) \implies \neg\text{freeable}(p) \text{ until reallocated}
$$

#### Property 5: Bounded Fragmentation
$$
\text{fragmentation\_ratio} \leq k \cdot \text{optimal}
$$

### 2.2 The Allocator Design

We implement a **formally verified buddy allocator**:

```
Structure:
- Memory divided into power-of-2 blocks
- Free lists for each size class
- Bitmap tracking allocation status
- Invariants maintained across all operations
```

Why buddy allocator:
- Simple enough to verify completely
- O(log n) allocation/deallocation
- Bounded fragmentation (factor of 2)
- No external fragmentation for aligned allocations

### 2.3 Separation Logic Specification

```coq
(* Allocation specification *)
Theorem allocate_spec : forall sz,
  {{ emp }}
  allocate(sz)
  {{ p, p |--> block(sz) * precise_size(p, sz) }}.

(* Free specification *)
Theorem free_spec : forall p sz,
  {{ p |--> block(sz) }}
  free(p)
  {{ emp }}.

(* Key separation property *)
Theorem disjoint_allocations : forall p1 p2 sz1 sz2,
  p1 |--> block(sz1) * p2 |--> block(sz2) ->
  p1 <> p2 ->
  disjoint(p1, sz1, p2, sz2).
```

## 3. Architecture of Domain W

### 3.1 The Verified Allocator Stack

```
┌─────────────────────────────────────────┐
│         TERAS Runtime                    │
├─────────────────────────────────────────┤
│    Verified Allocator API                │
│    (alloc, free, realloc)               │
├─────────────────────────────────────────┤
│    Buddy Allocator Core                  │
│    (Coq-verified, extracted to Rust)    │
├─────────────────────────────────────────┤
│    Page Allocator                        │
│    (seL4 / Track U integration)         │
├─────────────────────────────────────────┤
│    Physical Memory (Hardware)            │
└─────────────────────────────────────────┘
```

### 3.2 Integration with Type System

The type system tracks allocation:

```coq
(* Extended type for heap references *)
Inductive heap_ty : Type :=
  | HRef : ty -> region -> ownership -> heap_ty.

(* Ownership states *)
Inductive ownership : Type :=
  | Owned     : ownership      (* Unique owner, can free *)
  | Borrowed  : lifetime -> ownership  (* Temporary access *)
  | Shared    : ownership.     (* Read-only sharing *)
```

### 3.3 Region-Based Memory Management

For predictable deallocation without GC:

```
region r {
  let x = alloc_in(r, data);
  let y = alloc_in(r, more_data);
  // All allocations freed when region ends
}
// x, y automatically deallocated here
```

Regions provide:
- Deterministic deallocation (no GC pauses)
- Bulk freeing (efficient)
- Provable memory bounds

### 3.4 Optional Verified GC

For long-running applications, a verified garbage collector:

```coq
(* GC correctness theorem *)
Theorem gc_preserves_reachability : forall heap roots,
  reachable(roots, heap) = reachable(roots, gc(heap)).

(* GC safety theorem *)
Theorem gc_no_dangling : forall heap roots p,
  In p (gc(heap)) -> reachable_from(roots, p, heap).
```

## 4. Implementation Strategy (Infinite Timeline)

1. **Step 1: Formalize Memory Model**
   - Define heap as partial map: `loc -> option value`
   - Define separation logic in Coq
   - Prove frame rule and structural rules

2. **Step 2: Implement Buddy Allocator in Coq**
   - Define data structures (free lists, bitmaps)
   - Implement alloc/free
   - Prove all invariants preserved

3. **Step 3: Extract to Rust**
   - Use Coq extraction to generate Rust code
   - Or: manually implement and use VST/RefinedC to verify

4. **Step 4: Integrate with Track U**
   - Allocator runs under Runtime Guardian supervision
   - Hardware memory protection enforces region boundaries

5. **Step 5: Verification Against Physical Memory**
   - Prove allocator correctness assuming correct page tables
   - Integrate with Track S hardware model

## 5. Obsolescence of Threats

- **Buffer Overflow:** OBSOLETE. Allocator returns exact sizes; bounds checking is type-enforced.
- **Use-After-Free:** OBSOLETE. Freed memory is provably inaccessible.
- **Double-Free:** OBSOLETE. Free is idempotent or rejected on already-freed memory.
- **Heap Overflow:** OBSOLETE. Heap metadata is separate and protected.
- **Type Confusion via Corruption:** OBSOLETE. Memory layout is type-determined and verified.
- **Memory Leaks:** OBSOLETE. Region-based management or verified GC ensures reclamation.

## 6. Dependencies

| Dependency | Direction | Nature |
|------------|-----------|--------|
| Track A (Formal) | W depends on A | Heap typing rules |
| Track U (Guardian) | W integrates with U | Memory protection enforcement |
| Track S (Hardware) | W depends on S | Physical memory model |
| Track V (Termination) | W coordinates with V | Bounded allocation in loops |

## 7. Verification Targets

| Component | Verification Method | Tool |
|-----------|---------------------|------|
| Allocator logic | Separation logic | Coq + Iris |
| Rust implementation | Refinement proof | RefinedC / Verus |
| Integration | End-to-end | Combined proofs |

---

**"Memory is not managed. Memory is PROVEN."**
