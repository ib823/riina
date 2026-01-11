# RESEARCH_A12_REGION_TYPES_DECISION.md

## TERAS Research Track — Domain A: Type Theory
### Session A-12: Region Types — Architecture Decision

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Architecture Decision Record
**Status:** APPROVED

---

# DECISION SUMMARY

## Primary Decision

**ADOPT** Linear Regions (Fluet-Morrisett capability model) as the theoretical foundation for TERAS-LANG's region-based memory management, combined with MLKit-style inference for automatic region annotation.

## Secondary Decisions

1. **Region inference** via Tofte-Birkedal algorithm
2. **Capability-based access** with linear capabilities
3. **Security attributes** on regions for IFC integration
4. **Effect tracking** for region operations

---

# PART I: DECISION RATIONALE

## 1.1 Why Linear Regions

### 1.1.1 Alignment with A-04 (Linear Types)

The A-04 decision adopted graded linear types. Linear Regions naturally extends this:

```
A-04 Decision: Graded linear types with multiplicities
  lin T     -- linear (exactly once)
  aff T     -- affine (at most once)
  rel T     -- relevant (at least once)
  
Linear Regions Extension:
  lin Cap<ρ>  -- linear capability for region ρ
  
  Capability is linear:
    - Must use exactly once
    - Cannot duplicate
    - Can be consumed by deallocation
```

### 1.1.2 Security Foundation

Linear capabilities provide strong security guarantees:

```
Security Properties:

1. EXCLUSIVE ACCESS
   lin Cap<ρ> cannot be duplicated
   Only one code path can access ρ
   
2. DETERMINISTIC DEALLOCATION
   Consuming capability deallocates region
   No dangling references possible
   
3. CONFIDENTIALITY
   Data in ρ cannot escape
   Capability controls all access
   
4. INTEGRITY
   Only capability holder can write
   Tamper-evident by construction
```

### 1.1.3 Performance Benefits

```
Performance Analysis:

Linear capabilities enable:
  - Zero runtime reference counting
  - Static deallocation points
  - Optimal allocation strategy selection
  - No GC pauses

Compared to alternatives:
  MLKit: Similar performance, but no linearity guarantees
  Cyclone: More runtime checks
  RTSJ: Runtime checks everywhere
  Rust: Similar, different formulation
```

## 1.2 Why MLKit Inference

### 1.2.1 Annotation Burden Elimination

```
Inference Benefits:

Without inference (Cyclone):
  struct Buffer<`r> *`r createBuffer<`r>(
    region_t<`r> r, int size
  ) { ... }

With inference (MLKit):
  fun createBuffer size = ...
  (* Inferred: ∀ρ. int → Buffer at ρ ! Alloc<ρ> *)

TERAS-LANG target:
  fn createBuffer(size: int) -> Buffer
  // Inferred: ∀ρ. int → Buffer at ρ ! Alloc<ρ>
```

### 1.2.2 Proven Soundness

MLKit's inference algorithm has:
- 30 years of research refinement
- Formal soundness proofs
- Production implementation experience
- Well-understood complexity bounds

## 1.3 Why Security Attributes

### 1.3.1 IFC Integration

```
Security Attributes on Regions:

letregion ρ [secret] in
  // All data in ρ is secret
  // Cannot flow to public regions
  
letregion ρ [tainted] in
  // All data in ρ is untrusted
  // Must sanitize before use

letregion ρ [ct] in
  // Constant-time access only
  // No data-dependent branching
```

### 1.3.2 TERAS Product Requirements

| Product | Region Attribute Needs |
|---------|----------------------|
| MENARA | `[secret]` for credentials |
| GAPURA | `[tainted]` for input |
| ZIRAH | `[ct]` for analysis |
| BENTENG | `[secret]` for biometrics |
| SANDI | `[secret, ct]` for keys |

---

# PART II: TECHNICAL SPECIFICATION

## 2.1 Region Type Syntax

```
Region Types:

Types:
  τ ::= ...                           -- existing types
      | τ at ρ                        -- value in region ρ
      | &'ρ τ                         -- reference to τ in ρ
      | &'ρ mut τ                     -- mutable reference

Region Expressions:
  ρ ::= 'static                       -- global region
      | 'ρ                            -- region variable
      | 'heap                         -- heap region

Region Capabilities:
  Cap<ρ>                              -- capability type
  lin Cap<ρ>                          -- linear capability

Region Attributes:
  [attrs] ::= [secret]                -- confidential data
            | [tainted]               -- untrusted data
            | [ct]                    -- constant-time
            | [wipe]                  -- secure wipe
            | [attr₁, attr₂]          -- multiple
```

## 2.2 Region Operations

```
Operations with Capabilities:

Region Creation:
  letregion ρ [attrs] with cap in e end
  
  Typing:
    Γ, ρ, cap: lin Cap<ρ> ⊢ e : τ ; Δ
    ρ ∉ fv(τ)    cap ∉ fv(Δ)
    ─────────────────────────────────────────
    Γ ⊢ letregion ρ [attrs] with cap in e end : τ ; Δ

Allocation:
  alloc<ρ>(cap, value) : τ at ρ
  
  Typing:
    Γ ⊢ cap : &lin Cap<ρ>    Γ ⊢ value : τ
    ─────────────────────────────────────────
    Γ ⊢ alloc<ρ>(cap, value) : τ at ρ ; Alloc<ρ>

Read Access:
  read<ρ>(cap, ptr) : τ
  
  Typing:
    Γ ⊢ cap : &lin Cap<ρ>    Γ ⊢ ptr : &'ρ τ
    ─────────────────────────────────────────
    Γ ⊢ read<ρ>(cap, ptr) : τ ; Read<ρ>

Write Access:
  write<ρ>(cap, ptr, value) : ()
  
  Typing:
    Γ ⊢ cap : &lin Cap<ρ>    Γ ⊢ ptr : &'ρ mut τ    Γ ⊢ value : τ
    ──────────────────────────────────────────────────────────────
    Γ ⊢ write<ρ>(cap, ptr, value) : () ; Write<ρ>

Deallocation:
  freeregion(cap)
  
  Typing:
    Γ ⊢ cap : lin Cap<ρ>
    ───────────────────────────
    Γ ⊢ freeregion(cap) : () ; Free<ρ>
```

## 2.3 Region Effects

```
Effect Types for Regions:

Effect Constructors:
  Read<ρ>    -- read from region ρ
  Write<ρ>   -- write to region ρ
  Alloc<ρ>   -- allocate in region ρ
  Free<ρ>    -- deallocate region ρ

Effect Composition:
  ε ::= ∅                  -- no effect
      | ε₁ ∪ ε₂            -- union
      | Read<ρ>            -- region read
      | Write<ρ>           -- region write
      | Alloc<ρ>           -- region allocation
      | Free<ρ>            -- region deallocation

Effect Masking:
  letregion ρ with cap in e end
  masks effects: Read<ρ>, Write<ρ>, Alloc<ρ>, Free<ρ>
  
  Result effect: ε \ {Read<ρ>, Write<ρ>, Alloc<ρ>, Free<ρ>}

Effect Bounds:
  fn f<'ρ>(x: τ at 'ρ) -> τ' ! {Read<'ρ>}
```

## 2.4 Region Inference

```
Inference Algorithm:

PHASE 1: Type Reconstruction
  Standard HM type inference
  Introduce region variables at allocation points

PHASE 2: Constraint Collection
  For each allocation: fresh ρ, constraint {Alloc<ρ>} ⊆ ε
  For each read: constraint {Read<ρ>} ⊆ ε
  For each write: constraint {Write<ρ>} ⊆ ε
  
PHASE 3: Constraint Solving
  Unify regions with same lifetime
  Compute effect closure
  Determine capability usage

PHASE 4: Storage Mode Analysis
  For each region ρ:
    If contents escape → HEAP allocation
    If contents local → STACK allocation
    
PHASE 5: Capability Insertion
  Insert capability creation at region boundaries
  Insert capability usage at access points
  Insert capability consumption at deallocation
```

## 2.5 Security Attribute Semantics

```
Attribute Semantics:

[secret]:
  - Data cannot flow to non-secret regions
  - Comparison results are secret
  - Must declassify explicitly
  
  Rules:
    τ at ρ[secret] ≤ τ at ρ'[secret]    (OK: secret to secret)
    τ at ρ[secret] ≤ τ at ρ'            (ERROR: secret to public)

[tainted]:
  - Data from untrusted sources
  - Cannot use in security-sensitive operations
  - Must sanitize before use
  
  Rules:
    τ at ρ[tainted] → sanitizer → τ at ρ'    (OK with sanitizer)
    τ at ρ[tainted] → security_op            (ERROR: unsanitized)

[ct]:
  - Constant-time access only
  - No branching on data values
  - No data-dependent memory access
  
  Rules:
    if (x at ρ[ct]) { ... }                   (ERROR: branch on CT)
    arr[(x at ρ[ct])]                         (ERROR: CT-dependent index)
    ct_select(cond at ρ[ct], a, b)            (OK: CT operation)

[wipe]:
  - Secure memory clearing on deallocation
  - Prevents cold boot attacks
  - Zero memory before free
  
  Implementation:
    volatile memset + memory barrier before free
```

---

# PART III: INTEGRATION WITH PRIOR DECISIONS

## 3.1 A-04 Integration (Linear Types)

```
Combined Linear Types + Regions:

Linear on region values:
  lin τ at ρ
  
  Properties:
    - Value must be used exactly once (linear)
    - Value valid while ρ is live (region)
    - Combining constraints checked statically

Linear capabilities:
  lin Cap<ρ>
  
  Properties:
    - Capability cannot be duplicated
    - Must be consumed (deallocation) or passed
    - Statically tracked

Affine on region values:
  aff τ at ρ
  
  Properties:
    - Can be discarded (region deallocation)
    - Cannot be duplicated
    - Default for allocated values
```

## 3.2 A-05 Integration (Effects)

```
Effect System + Region Effects:

Combining A-05 effects with regions:

  fn process(x: τ at ρ) -> τ' ! {Read<ρ>, IO, State<s>}
  
  Effect ordering:
    Region effects compose with other effects
    All effects tracked in same system
    
  Effect handlers:
    handle { ... } with region_handler
    
    Region effects can be handled locally
    Masking at region boundaries
```

## 3.3 A-06 Integration (Uniqueness)

```
Uniqueness + Regions:

Unique values in regions:
  uniq τ at ρ
  
  Enables:
    - In-place update (uniqueness)
    - Region-bounded lifetime (region)
    - Safe destructive operations

Region transfer via uniqueness:
  fn transfer<'a, 'b>(
    x: uniq τ at 'a,
    target_cap: &lin Cap<'b>
  ) -> uniq τ at 'b ! {Free<'a>, Alloc<'b>}
  
  Uniqueness enables moving between regions
```

## 3.4 A-07 Integration (Session Types)

```
Session Types + Regions:

Session in region:
  session S at ρ = !{msg: τ at ρ}.?{ack: τ' at ρ}.end
  
  Channel endpoint:
    Chan<S> at ρ
  
  Message lifetime bounded by region:
    Messages allocated in session's region
    Protocol completion can free region
    
Cross-region sessions:
  session S at (ρ_local, ρ_remote) = 
    !{msg: τ at ρ_local}.
    ?{response: τ' at ρ_remote}.
    end
```

---

# PART IV: IMPLEMENTATION ROADMAP

## 4.1 Phase 1: Core Regions (Weeks 1-6)

```
Deliverables:
  □ Region syntax in parser
  □ Region type representation
  □ Basic region checking
  □ Capability type
  □ Region scope validation

Acceptance Criteria:
  □ Simple region examples type-check
  □ Escape analysis detects violations
  □ Capability tracking works
```

## 4.2 Phase 2: Region Inference (Weeks 7-12)

```
Deliverables:
  □ Constraint generation
  □ Region unification
  □ Effect collection
  □ Storage mode analysis
  □ Capability insertion

Acceptance Criteria:
  □ Programs type-check without annotations
  □ Inference matches manual annotations
  □ Storage modes correctly determined
```

## 4.3 Phase 3: Security Attributes (Weeks 13-16)

```
Deliverables:
  □ Attribute syntax
  □ Attribute propagation
  □ IFC rules for regions
  □ CT checking for regions
  □ Secure wipe implementation

Acceptance Criteria:
  □ Secret data confined to secret regions
  □ Tainted data requires sanitization
  □ CT violations rejected
  □ Wipe correctly clears memory
```

## 4.4 Phase 4: Optimization (Weeks 17-20)

```
Deliverables:
  □ Region coalescing
  □ Storage mode optimization
  □ Effect simplification
  □ Capability elision
  □ Performance validation

Acceptance Criteria:
  □ Performance matches or exceeds C
  □ No unnecessary regions created
  □ Optimal allocation strategies selected
```

---

# PART V: VALIDATION

## 5.1 Soundness Criteria

```
Region Type Soundness:

Property 1: No dangling pointers
  If Γ ⊢ e : τ at ρ and e →* v
  then ρ is live when v is accessed
  
Property 2: Capability linearity
  If Γ ⊢ e : () and cap: lin Cap<ρ> ∈ Γ
  then cap is used exactly once in e
  
Property 3: Effect soundness
  If Γ ⊢ e : τ ! ε and e →* v
  then all memory operations are in ε
  
Property 4: Attribute enforcement
  If ρ has [secret] and e : τ at ρ
  then e cannot flow to non-secret regions
```

## 5.2 Performance Criteria

```
Performance Requirements (D38 Mandate):

Allocation:
  ATTOP: O(1) bump allocation
  ATBOT: O(1) bump allocation
  Target: < 10 cycles average

Deallocation:
  Single region: O(1) page reset
  Nested regions: O(depth) pop
  Target: < 100 cycles average

Space Overhead:
  Per region: < 64 bytes metadata
  Per object: 0 bytes (no headers)
  Target: < 5% space overhead
```

## 5.3 TERAS Alignment Score

| Criterion | Score | Notes |
|-----------|-------|-------|
| Law 1 (Self-Sufficiency) | 10/10 | No external region runtime |
| Law 2 (Formal Verification) | 9/10 | Proven sound model |
| Law 3 (Zero Runtime) | 10/10 | Static checking only |
| Law 4 (Performance) | 9/10 | O(1) operations |
| Law 5 (Nation-State) | 9/10 | Security attributes |
| A-04 Compatibility | 10/10 | Linear capabilities |
| A-05 Compatibility | 10/10 | Effect integration |
| A-06 Compatibility | 9/10 | Uniqueness + regions |
| A-07 Compatibility | 9/10 | Session + regions |
| **Overall** | **9.4/10** | Strong alignment |

---

# PART VI: RISKS AND MITIGATIONS

## 6.1 Identified Risks

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Inference complexity | Medium | High | Incremental algorithm |
| Annotation burden | Low | Medium | Good defaults |
| Performance regression | Low | High | Benchmark suite |
| Security attribute interaction | Medium | Medium | Formal model |

## 6.2 Mitigation Strategies

```
Inference Complexity:
  - Start with local inference
  - Expand to cross-function incrementally
  - Allow manual override annotations
  
Annotation Burden:
  - Default region for temporaries
  - Elision rules for common patterns
  - IDE support for annotations
  
Performance:
  - Continuous benchmarking
  - Comparison with hand-written C
  - Profile-guided optimization
  
Security Interaction:
  - Formal model in Coq
  - Exhaustive attribute combination testing
  - Security-focused code review
```

---

# PART VII: DECISION RECORD

## 7.1 Decision Statement

```
DECISION A-12: Region Types

ADOPT Linear Regions (Fluet-Morrisett) with:
  1. Linear capabilities for region access
  2. MLKit-style inference for annotations
  3. Security attributes for IFC integration
  4. Effect tracking for region operations

Rationale:
  - Best fit for linear type system (A-04)
  - Proven inference algorithm
  - Security-first design
  - Zero runtime overhead

Alternatives Rejected:
  - MLKit (no linear integration)
  - Cyclone (too manual, discontinued)
  - RTSJ (runtime checks)
  - Rust lifetimes (different formulation)
```

## 7.2 Approval

```
Decision Status: APPROVED
Approval Date: 2026-01-03
Review Cycle: 6 months

Integration Points:
  - A-04: Linear types (capability linearity)
  - A-05: Effects (region effects)
  - A-06: Uniqueness (region transfer)
  - A-07: Sessions (bounded messages)
```

---

**END OF DECISION DOCUMENT**

**Document Statistics:**
- Decision: Linear Regions with MLKit inference
- Alignment Score: 9.4/10
- Implementation Phases: 4 (20 weeks)
- Risk Level: Low-Medium

**Next Session:** A-13 (Ownership Types)
