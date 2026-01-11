# RESEARCH_A14_CAPABILITY_TYPES_COMPARISON.md

## TERAS Research Track â€” Domain A: Type Theory
### Session A-14: Capability Types â€” Comparative Analysis

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research

---

# PART I: SYSTEM COMPARISON MATRIX

## 1.1 Feature Matrix

| Feature | E Language | Pony | Wyvern | Austral | seL4 |
|---------|------------|------|--------|---------|------|
| **Level** | Language | Language | Language | Language | Kernel |
| **Capability Model** | Object-cap | Ref-cap | Effect-cap | Linear-cap | Kernel-cap |
| **Static Verification** | Partial | Full | Full | Full | Formal |
| **Unforgeability** | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ |
| **Attenuation** | âœ“ | Limited | âœ“ | âœ“ | âœ“ |
| **Revocation** | Proxy | N/A | N/A | Linear | Derivation |
| **Concurrency Safe** | Actors | âœ“ Native | Partial | Manual | âœ“ |
| **Systems Programming** | âœ— | Limited | âœ— | âœ“ | N/A |
| **Linear Types** | âœ— | âœ— | âœ— | âœ“ | N/A |
| **Effect System** | âœ— | âœ— | âœ“ | âœ— | N/A |
| **Production Ready** | âœ“ | âœ“ | Research | âœ“ | âœ“ |

## 1.2 Security Guarantees

| Property | E | Pony | Wyvern | Austral | seL4 |
|----------|---|------|--------|---------|------|
| Confused deputy prevention | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ |
| No ambient authority | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ |
| Authority confinement | âœ“ | âœ“ | âœ“ | âœ“ | âœ“ |
| Static POLA | Partial | âœ“ | âœ“ | âœ“ | âœ“ |
| Information flow | Partial | âœ“ | Partial | âœ“ | âœ“ |
| Data race freedom | Actors | âœ“ | Partial | Manual | âœ“ |

## 1.3 Design Philosophy Comparison

```
Design Philosophy Spectrum:

                    FLEXIBILITY
                        ^
                        |
            E *         |         * Pony
      (object-cap,      |       (ref-cap,
       dynamic)         |        static)
                        |
                        |
                        |     * Wyvern
                        |       (effect-cap)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€> SAFETY
                        |
                        |
            seL4 *      |         * Austral
         (kernel-cap,   |       (linear-cap,
          verified)     |        systems)
                        |

E: Maximum flexibility, dynamic capability patterns
Pony: Reference capabilities for safe concurrency
Wyvern: Capability effects for modular reasoning
Austral: Linear capabilities for systems programming
seL4: Formally verified kernel capabilities
```

---

# PART II: DETAILED SYSTEM COMPARISONS

## 2.1 E vs Pony

### 2.1.1 Capability Model Comparison

| Aspect | E Language | Pony |
|--------|------------|------|
| Capability unit | Object reference | Reference type |
| Sharing model | Eventual send | Ref capabilities |
| Mutation control | Encapsulation | Type system |
| Concurrency | Actor model | Actor + rcaps |
| Distribution | Native | Not built-in |

### 2.1.2 Concurrency Approach

```
E Concurrency Model:
  - Actors communicate via eventual sends
  - Promise pipelining reduces latency
  - No shared mutable state
  - Vat = single-threaded actor group
  
  // E eventual send
  def result := remoteActor <- computeAsync()
  when (result) -> {
      // Handle result
  }

Pony Concurrency Model:
  - Actors communicate via messages
  - Reference capabilities prevent data races
  - iso for transferring mutable state
  - val for sharing immutable data
  
  // Pony actor send
  actor Worker
    be compute(data: Array[U32] iso) =>
      // data is isolated, safe to mutate
      process(consume data)
```

### 2.1.3 Capability Patterns Comparison

```
Sealer/Unsealer:
  E: Built-in makeBrand() function
  Pony: Must implement manually with tags
  
Caretaker (Revocation):
  E: First-class pattern with proxies
  Pony: Not standard, requires wrapper types
  
Membrane:
  E: Complete boundary wrapping
  Pony: Actor boundaries provide natural membranes
```

## 2.2 Pony vs Wyvern

### 2.2.1 Capability Type Comparison

```
Pony Reference Capabilities:
  iso -- isolated (unique, mutable)
  trn -- transition (write-unique)
  ref -- reference (aliased, mutable)
  val -- value (immutable, shareable)
  box -- box (locally immutable)
  tag -- tag (identity only)
  
  // Capability is property of reference
  class Data
    var value: U64
    
  actor Main
    new create(env: Env) =>
      let d: Data iso = Data  // d is isolated

Wyvern Effect Capabilities:
  resource type File
    def read(): String with {file.Read}
    def write(s: String): Unit with {file.Write}
  
  // Capability is effect requirement
  def process(f: File): String with {file.Read}
    f.read()
```

### 2.2.2 Modularity Comparison

| Aspect | Pony | Wyvern |
|--------|------|--------|
| Capability scope | Type annotations | Effect signatures |
| Abstraction | Ref cap variables | Effect polymorphism |
| Composition | Viewpoint adaptation | Effect composition |
| Hierarchy | Subtyping lattice | Effect inclusion |

### 2.2.3 Use Case Suitability

```
Pony Best For:
  - High-performance concurrent systems
  - Actor-based architectures
  - Memory-safe systems programming
  - Real-time systems (no GC pauses)

Wyvern Best For:
  - Effect-based reasoning
  - Modular security policies
  - Research and experimentation
  - Effect abstraction patterns
```

## 2.3 Austral vs Others

### 2.3.1 Linear Capability Unique Features

```
Austral's Linear Capabilities:

1. Linear by Default
   linear type File: Linear;
   // Must be consumed (cannot be dropped silently)

2. Explicit Capability Parameters
   function process(fs: &Filesystem): Result;
   // All authority from parameters

3. No Ambient Authority
   // Cannot access global state
   // Entry point receives all initial capabilities

4. Systems Programming Focus
   // Raw memory access via capabilities
   // Zero-cost abstractions
   // C FFI support
```

### 2.3.2 Comparison with Rust-like Ownership

| Aspect | Austral | Rust + Caps |
|--------|---------|-------------|
| Default linearity | Linear | Affine |
| Capability encoding | Explicit types | Via traits |
| Entry capabilities | Function params | Static refs |
| Drop behavior | Must consume | Auto-drop |
| Standard library | Minimal | Rich |

## 2.4 seL4 vs Language Capabilities

### 2.4.1 Level of Abstraction

```
seL4 (Kernel Level):
  - Capabilities managed by kernel
  - Hardware-enforced boundaries
  - Capability derivation tree
  - Formal verification (Isabelle/HOL)
  
Language Capabilities:
  - Capabilities in type system
  - Compile-time enforcement
  - No runtime overhead
  - Type-level verification

Complementary Approaches:
  seL4 protects OS-level resources
  Language caps protect app-level resources
  Both can be used together
```

### 2.4.2 Revocation Comparison

| Mechanism | seL4 | E | Pony | Austral |
|-----------|------|---|------|---------|
| Strategy | Derivation tree | Proxy | N/A | Linearity |
| Granularity | Single cap | Per proxy | N/A | Per value |
| Bulk revoke | âœ“ (subtree) | Membrane | N/A | Region end |
| Cost | O(tree) | O(1) | N/A | O(1) |

---

# PART III: INTEGRATION ANALYSIS

## 3.1 Integration with Linear Types (A-04)

### 3.1.1 Capability Linearity Options

```
Option 1: All Capabilities Linear (Austral-style)
  lin cap<R>   -- every capability linear
  
  Pros: Strongest resource guarantees
  Cons: Restrictive, frequent borrowing needed

Option 2: Optional Linearity
  cap<R>       -- default (affine)
  lin cap<R>   -- linear when needed
  
  Pros: Flexible, matches ownership
  Cons: Less uniform

Option 3: Linearity via Mode (A-04 integration)
  [m] cap<R>   -- mode-polymorphic capability
  
  Pros: Maximum flexibility
  Cons: More complex
```

### 3.1.2 Recommended Integration

```
TERAS-LANG Capability Linearity:

Default: Affine capabilities (can drop)
  cap<Resource>              -- affine
  
Linear when critical:
  lin cap<Transaction>       -- must commit/abort
  lin cap<Connection>        -- must close
  
Sharing via borrowing:
  &cap<Resource>             -- shared borrow
  &mut cap<Resource>         -- exclusive borrow
```

## 3.2 Integration with Ownership (A-13)

### 3.2.1 Ownership-Capability Interaction

```
Capability Ownership:

owned cap<R>   -- capability with ownership semantics
  - Move on assignment
  - Drop on scope exit
  - Borrow for temporary use

Pattern:
  fn process(c: owned cap<File>) -> Result {
      let content = read(&c)?;  // borrow
      close(c)                   // move (consume)
  }
  
  fn helper(c: &cap<File>) -> String {
      c.read()  // borrow, doesn't consume
  }
```

### 3.2.2 Permission Borrowing

```
Permission Attenuation via Borrowing:

Full capability:
  owned cap<File, Full>
  
Attenuated borrow:
  &cap<File, Read>    -- read-only view
  
Type rule:
  c : owned cap<R, P>    P' âŠ† P
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  &c : &cap<R, P'>
```

## 3.3 Integration with Effects (A-11)

### 3.3.1 Capability Effects (Wyvern-style)

```
Effect-Based Capability Tracking:

Effect Declaration:
  effect FileCapability {
    Open : Path â†’ cap<File>,
    Read : cap<File> â†’ String,
    Write : (cap<File>, String) â†’ (),
    Close : cap<File> â†’ (),
  }

Function Signature:
  fn process_file(path: Path) -> String
    ! {FileCapability.Open, FileCapability.Read, 
       FileCapability.Close}
```

### 3.3.2 Effect Masking at Capability Boundaries

```
Capability-Scoped Effects:

withcap c : cap<File> = open(path) in
  let content = read(c);
  close(c);
  content
end
// File effects masked outside scope
// Only pure result escapes

Type Rule:
  Î“ âŠ¢ e : cap<R>    Î”, x:cap<R> âŠ¢ e' : Ï„ ! E âˆª {Use<R>}
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  Î“, Î” âŠ¢ withcap x = e in e' : Ï„ ! E
  // Use<R> effects masked
```

## 3.4 Integration with Regions (A-12)

### 3.4.1 Region-Scoped Capabilities

```
Capability Lifetime via Regions:

letregion Ï in
  letcap c : cap<File> at Ï = open(path) in
    use(c)
  end
end
// Capability lifetime bounded by region

Benefits:
  - Bulk revocation (region end)
  - Resource cleanup guarantee
  - Effect masking at boundary
```

### 3.4.2 Capability Region Interaction

```
Type System Integration:

cap<R> at Ï    -- capability in region Ï
&'Ï cap<R>     -- borrow from region

Rules:
  - cap<R> at Ï cannot escape region Ï
  - Borrows bounded by region lifetime
  - Region end = bulk capability revocation
```

---

# PART IV: PERFORMANCE ANALYSIS

## 4.1 Runtime Overhead

| System | Capability Check | Indirection | Memory |
|--------|------------------|-------------|--------|
| E | Dynamic dispatch | Proxy layer | High |
| Pony | Zero (static) | None | Zero |
| Wyvern | Zero (static) | None | Zero |
| Austral | Zero (static) | None | Zero |
| seL4 | Kernel trap | CNode lookup | Medium |

## 4.2 Compile-Time Cost

```
Compilation Complexity:

E Language:
  - No static capability checking
  - Fast compilation
  - Runtime checks only
  
Pony:
  - Reference capability checking
  - Viewpoint adaptation
  - O(n) typical
  
Wyvern:
  - Effect inference
  - Capability subtyping
  - O(nÂ²) worst case
  
Austral:
  - Linear type checking
  - Simple capability rules
  - O(n) typical
```

## 4.3 Trade-off Summary

```
Performance vs Safety Trade-offs:

                    RUNTIME COST
                        ^
                        |
             E *        |
        (dynamic        |
         proxies)       |
                        |
    seL4 *              |
    (kernel             |
     traps)             |
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€> FLEXIBILITY
                        |
                        |
           Pony *  Austral *  Wyvern *
        (zero overhead, static checking)
                        |

For TERAS: Austral-zone (zero overhead, static)
```

---

# PART V: EVALUATION FOR TERAS-LANG

## 5.1 Criteria and Weights

| Criterion | Weight | Rationale |
|-----------|--------|-----------|
| Security Completeness | 25% | Core TERAS requirement |
| Zero Overhead | 20% | D38 performance mandate |
| Integration | 20% | A-04, A-11, A-12, A-13 |
| POLA Support | 15% | Security principle |
| Usability | 10% | Developer adoption |
| Formal Foundation | 10% | Verification needs |

## 5.2 System Scores

| System | Security | Overhead | Compat | POLA | Usable | Formal | **Total** |
|--------|----------|----------|--------|------|--------|--------|-----------|
| Austral-style | 24/25 | 20/20 | 18/20 | 15/15 | 7/10 | 8/10 | **92/100** |
| Pony-style | 22/25 | 20/20 | 12/20 | 12/15 | 9/10 | 8/10 | **83/100** |
| Wyvern-style | 23/25 | 20/20 | 18/20 | 14/15 | 6/10 | 8/10 | **89/100** |
| E-style | 20/25 | 10/20 | 8/20 | 14/15 | 8/10 | 6/10 | **66/100** |
| seL4-style | 25/25 | 15/20 | 5/20 | 15/15 | 5/10 | 10/10 | **75/100** |

## 5.3 Recommendation Summary

```
Ranking for TERAS-LANG:

1. Austral-style (92/100)
   Linear capabilities + zero overhead
   Best integration with A-04, A-13
   
2. Wyvern-style (89/100)
   Effect-based capabilities
   Best integration with A-11
   
3. Pony-style (83/100)
   Reference capabilities
   Great for concurrency

Recommended Hybrid:
  - Core: Austral-style linear capabilities
  - Enhancement: Wyvern-style effect integration
  - Concurrency: Pony-style deny capabilities (optional)
```

---

# PART VI: SUMMARY

## 6.1 Key Comparative Findings

1. **Linear capabilities optimal for TERAS** â€” Austral demonstrates viable approach
2. **Effect integration valuable** â€” Wyvern shows capability-effect synergy
3. **Reference capabilities for concurrency** â€” Pony model proven
4. **Zero overhead achievable** â€” Static checking eliminates runtime cost
5. **seL4 complementary** â€” Kernel + language caps work together

## 6.2 Design Direction

```
TERAS-LANG Capability Design:

Primary: Austral-style linear capabilities
  - cap<R, P> as first-class types
  - Linear by default for critical resources
  - No ambient authority
  
Effect Integration: Wyvern-style
  - Capabilities as effect requirements
  - Effect masking at capability boundaries
  
Ownership: Integrated (A-13)
  - owned cap<R> for exclusive ownership
  - &cap<R> for borrowed access
  
Region: Integrated (A-12)
  - cap<R> at Ï for lifetime bounding
  - Bulk revocation via region end
```

---

**END OF COMPARISON DOCUMENT**

**Next Document:** RESEARCH_A14_CAPABILITY_TYPES_DECISION.md
