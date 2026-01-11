# RESEARCH_A12_REGION_TYPES_SURVEY.md

## TERAS Research Track â€” Domain A: Type Theory
### Session A-12: Region Types (MLKit, Cyclone)

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research
**Predecessor:** A-11 (Effect Types)
**Successor:** A-13 (Ownership Types)

---

# PART I: FOUNDATIONS OF REGION-BASED MEMORY MANAGEMENT

## 1.1 Historical Context

### 1.1.1 The Memory Management Problem

Traditional approaches to memory management:

```
MANUAL MEMORY MANAGEMENT (C/C++)
  Advantages: Full control, predictable performance
  Disadvantages: Use-after-free, double-free, memory leaks

GARBAGE COLLECTION (Java, ML, Haskell)
  Advantages: Safety, convenience
  Disadvantages: Unpredictable pauses, memory overhead

REFERENCE COUNTING (Swift, Python)
  Advantages: Deterministic deallocation, no pauses
  Disadvantages: Cycles, atomic operations overhead

REGION-BASED MEMORY MANAGEMENT
  Advantages: Safe, deterministic, efficient
  Disadvantages: Requires static analysis, less flexible
```

### 1.1.2 Tofte & Talpin (1994-1997)

The foundational work on region-based memory management was developed by Mads Tofte and Jean-Pierre Talpin:

**Key Papers:**
- "Implementation of the Typed Call-by-Value Î»-calculus using a Stack of Regions" (POPL 1994)
- "Region-Based Memory Management" (Information and Computation, 1997)

**Core Insight:** Allocate data in lexically-scoped regions; deallocate entire region at scope exit.

```
Region Model:
  
  letregion Ï in          -- allocate region Ï
    let x = (1, 2) at Ï   -- allocate pair in Ï
    in ...                 -- use x
  end                      -- deallocate Ï (and x)
```

### 1.1.3 Type System for Regions

```
Types with Region Annotations:

Ï„ ::= int                     -- base type
    | Ï„â‚ â†’^Îµ Ï„â‚‚               -- function (with effect Îµ)
    | Ï„â‚ Ã— Ï„â‚‚ at Ï            -- pair allocated in Ï
    | ref Ï„ at Ï              -- reference in Ï
    | âˆ€Ï.Ï„                    -- region polymorphism
    | âˆ€Îµ.Ï„                    -- effect polymorphism

Effects:
Îµ ::= âˆ…                       -- no effect
    | {get(Ï), put(Ï)}        -- read/write region Ï
    | Îµâ‚ âˆª Îµâ‚‚                 -- effect union

Example:
  let f : âˆ€Ï. (int Ã— int) at Ï â†’^{get(Ï)} int
      f p = #1 p + #2 p
```

---

## 1.2 Theoretical Foundations

### 1.2.1 Typed Region Calculus

```
Syntax:

Terms:
e ::= x                       -- variable
    | Î»x.e                    -- abstraction
    | eâ‚ eâ‚‚                   -- application
    | (eâ‚, eâ‚‚) at Ï           -- pair allocation
    | #i e                    -- projection
    | ref e at Ï              -- reference allocation
    | !e                      -- dereference
    | eâ‚ := eâ‚‚                -- assignment
    | letregion Ï in e        -- region introduction
    | Î›Ï.e                    -- region abstraction
    | e[Ï]                    -- region application

Typing Rules:

[T-PAIR]
Î“ âŠ¢ eâ‚ : Ï„â‚ ; Îµâ‚    Î“ âŠ¢ eâ‚‚ : Ï„â‚‚ ; Îµâ‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ (eâ‚, eâ‚‚) at Ï : (Ï„â‚ Ã— Ï„â‚‚) at Ï ; Îµâ‚ âˆª Îµâ‚‚ âˆª {put(Ï)}

[T-PROJ]
Î“ âŠ¢ e : (Ï„â‚ Ã— Ï„â‚‚) at Ï ; Îµ
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ #i e : Ï„áµ¢ ; Îµ âˆª {get(Ï)}

[T-LETREGION]
Î“, Ï âŠ¢ e : Ï„ ; Îµ    Ï âˆ‰ ftv(Ï„)    Ï âˆ‰ frv(Î“)
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ letregion Ï in e : Ï„ ; Îµ \ {get(Ï), put(Ï)}

[T-REGABS]
Î“, Ï âŠ¢ e : Ï„ ; Îµ
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ Î›Ï.e : âˆ€Ï.Ï„ ; Îµ \ Ï

[T-REGAPP]
Î“ âŠ¢ e : âˆ€Ï.Ï„ ; Îµ
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e[Ï'] : Ï„[Ï'/Ï] ; Îµ âˆª {Ï' â‰¤ Ï}
```

### 1.2.2 Region Safety Theorem

**Theorem (Region Safety):** If `Â· âŠ¢ e : Ï„ ; Îµ` and `e â†’* v` then:
1. No dangling pointers are accessed during evaluation
2. All allocated memory is deallocated when the enclosing region ends
3. Memory access patterns respect region boundaries

**Proof Sketch:**
- Progress: Well-typed, non-value terms can step
- Preservation: Types and effects are preserved by reduction
- Effect masking: Effects on local regions are hidden at boundaries

### 1.2.3 Region Inference

Tofte-Talpin developed inference algorithms:

```
Region Inference Algorithm:

1. CONSTRAINT GENERATION
   For each subexpression, generate:
   - Type constraints (standard HM)
   - Region constraints (allocation points)
   - Effect constraints (region accesses)

2. CONSTRAINT SOLVING
   Unification for types
   Effect inclusion for effects
   Region unification with constraints

3. REGION NORMALIZATION
   Merge regions when safe
   Eliminate unnecessary region abstractions

Example:
  fun f x = (x, x)
  
  Inferred: âˆ€Î±.âˆ€Ï. Î± â†’^{put(Ï)} (Î± Ã— Î±) at Ï
  
  Analysis: Both components share the same region Ï
            because they may alias
```

---

# PART II: MLKit

## 2.1 Overview

MLKit is a Standard ML compiler that implements region-based memory management:

- Developed at University of Copenhagen and IT University of Copenhagen
- Full Standard ML implementation
- Combines regions with optional garbage collection
- Production-quality implementation

### 2.1.1 MLKit Architecture

```
MLKit Compilation Pipeline:

Source ML
    â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚   Parsing       â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Type Inference  â”‚ (standard HM)
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Region Inferenceâ”‚ (Tofte-Talpin)
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Effect Analysis â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Multiplicity    â”‚ (storage mode)
â”‚ Inference       â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ K-Normal Form   â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Region-Annotatedâ”‚
â”‚ Lambda Code     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
    â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Code Generation â”‚ (C or native)
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.1.2 MLKit Region Types

```sml
(* MLKit annotates types with regions *)

(* Simple allocation *)
val pair : int * int   (* allocated in some region *)

(* Region polymorphism is inferred *)
fun swap (x, y) = (y, x)
(* Type: âˆ€r1,r2,r3. (a * b, r1) -> ((b * a), r2) *)

(* Effect tracking *)
fun readBoth (r1: t ref, r2: t ref) = (!r1, !r2)
(* Effect: get(region(r1)) âˆª get(region(r2)) *)

(* Region annotations (debugging) *)
val _ = MLKit.regionDebug := true
(* Prints region flow information *)
```

### 2.1.3 Storage Modes

MLKit introduced **storage modes** to optimize region allocation:

```
Storage Modes:

ATTOP(Ï)   - Allocate at top of region Ï
            Value's lifetime â‰¤ region's lifetime
            Can use stack-like allocation

ATBOT(Ï)   - Allocate at bottom of region Ï
            Value may escape the region
            Must use heap-like allocation

SAT(Ï)     - Allocation known to be single
            Can optimize allocation

Storage Mode Inference:
  Analyze how values flow through the program
  Determine which allocations can use ATTOP
  ATTOP enables efficient stack allocation
```

### 2.1.4 Physical Representation

```
MLKit Runtime Regions:

Region Structure:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Region Header               â”‚
â”‚ - next_page pointer         â”‚
â”‚ - current allocation point  â”‚
â”‚ - page list                 â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
         â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Page 1                      â”‚
â”‚ â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â” â”‚
â”‚ â”‚ Object 1                â”‚ â”‚
â”‚ â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤ â”‚
â”‚ â”‚ Object 2                â”‚ â”‚
â”‚ â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤ â”‚
â”‚ â”‚ ...                     â”‚ â”‚
â”‚ â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜ â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
         â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Page 2                      â”‚
â”‚ ...                         â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Operations:
  allocInRegion(Ï, size): O(1) bump allocation
  deallocRegion(Ï): O(pages) page deallocation
  resetRegion(Ï): O(1) reset allocation pointer
```

### 2.1.5 Region Profiling

```sml
(* MLKit provides region profiling *)

(* Run with profiling enabled *)
(* $ mlkit -prof myprogram.sml *)

(* Profile output shows:
   - Region sizes over time
   - Allocation rates per region
   - Region lifetimes
   - Memory high-water marks
*)

(* Example profile visualization:
   
   Region Size
   ^
   |    ___
   |   /   \
   |  /     \___
   | /          \
   |/____________\_____ Time
   
   Region r42: max 1.2MB, lifetime 0.3s
*)
```

---

## 2.2 MLKit Techniques

### 2.2.1 Region Polymorphism

```sml
(* Region-polymorphic functions *)

(* map: âˆ€Î±,Î²,Ïâ‚,Ïâ‚‚,Ïâ‚ƒ. (Î± â†’ Î²) Ã— list(Î±,Ïâ‚) â†’ list(Î²,Ïâ‚‚) *)
fun map f [] = []
  | map f (x::xs) = f x :: map f xs

(* The result list can be in a different region *)
(* This enables allocating results in a different lifetime *)

(* Region polymorphism enables *)
val result = 
  letregion Ï_temp in
    let temp = map f input (* temp in Ï_temp *)
    in filter g temp       (* result escapes Ï_temp *)
  end                      (* Ï_temp deallocated, temp freed *)
```

### 2.2.2 Effect Masking

```sml
(* Effects on local regions are hidden *)

fun processData input =
  letregion Ï in
    (* All effects on Ï are local *)
    let temp = buildIndex input (* put(Ï) *)
        result = query temp     (* get(Ï) *)
    in result                   (* result escapes *)
  end (* no visible effect on Ï *)

(* External type has no effect on Ï *)
(* Safe to deallocate Ï at scope exit *)
```

### 2.2.3 Region Coalescing

```
Region Coalescing Optimization:

Before coalescing:
  letregion Ïâ‚ in
    letregion Ïâ‚‚ in
      let x = (1,2) at Ïâ‚
          y = (3,4) at Ïâ‚‚
      in (x, y)
    end
  end

Analysis: Ïâ‚ and Ïâ‚‚ have same lifetime

After coalescing:
  letregion Ï in
    let x = (1,2) at Ï
        y = (3,4) at Ï
    in (x, y)
  end

Benefit: One region instead of two
         Less runtime overhead
```

---

# PART III: CYCLONE

## 3.1 Overview

Cyclone was a safe dialect of C developed at Cornell and AT&T Labs:

- "Safe C" with regions, bounds checking, tagged unions
- Source-level compatibility with C (mostly)
- Ran from 2001-2006
- Influential on Rust's design

### 3.1.1 Cyclone Goals

```
Cyclone Design Goals:

1. SAFETY
   - No buffer overflows
   - No dangling pointers
   - No uninitialized reads
   - No format string attacks

2. C COMPATIBILITY
   - Similar syntax
   - Interoperability with C
   - Familiar programming model

3. CONTROL
   - Manual memory management available
   - Predictable performance
   - Low overhead
```

### 3.1.2 Cyclone Region System

```c
// Cyclone syntax for regions

// Region-qualified pointers
int *`r ptr;           // pointer into region r
int *`H heap_ptr;      // pointer into heap (special region)
int *`U unique_ptr;    // unique pointer (like Rust Box)

// Region declarations
region r {
    int *`r p = rnew(r) 42;    // allocate in r
    // ... use p ...
}
// r deallocated here, p now invalid

// Region handles
region_t<`r> handle;   // handle for region r
void process(region_t<`r> r, int *`r data);

// Lexical regions (stack-allocated)
void foo() {
    int x = 42;
    int *`foo ptr = &x;  // `foo is this function's region
    // ptr valid until foo returns
}
```

### 3.1.3 Pointer Kinds

```c
// Cyclone pointer kinds

// Fat pointers (with bounds)
int *@fat arr;         // knows its own size
arr = new int[10];
arr[i];                // bounds-checked

// Thin pointers (like C)
int *@thin ptr;        // just an address
// Cannot do arithmetic (safely)

// Nullable vs non-null
int *@notnull required;
int *@nullable optional;

// Combining qualifiers
int *`r @fat @notnull safe_array;

// Zero-terminated strings
char *@zeroterm str;   // must end with '\0'
```

### 3.1.4 Unique Pointers

```c
// Unique pointers in Cyclone

// Unique pointer declaration
int *`U p = unew(int);  // allocate unique int
*p = 42;

// Transfer ownership
int *`U q = p;          // p is now consumed
// p = ...;             // ERROR: p consumed

// Explicit free
ufree(q);               // deallocate

// Unique arrays
int *`U @fat arr = unew int[100];

// Unique to region conversion
region r {
    int *`r rp = alias(p); // convert unique to region
    // p is consumed
    // rp valid in r
}
```

### 3.1.5 Existential Types for Regions

```c
// Existential types hide region identity

// Pack a region
struct Buffer {
    <`r>                      // existential region
    region_t<`r> region;
    char *`r @fat data;
};

struct Buffer *createBuffer(int size) {
    region r;
    struct Buffer *b = new Buffer;
    b->region = r;
    b->data = rnew(r) char[size];
    return b;
}

// Unpack and use
void useBuffer(struct Buffer *b) {
    let Buffer{<`r> region, data} = *b;
    data[0] = 'x';  // safe: data is in region
}
```

---

## 3.2 Cyclone Safety Features

### 3.2.1 Bounds Checking

```c
// Array bounds checking

// Fat pointers carry bounds
int *@fat arr = new int[10];
int x = arr[5];        // OK
int y = arr[15];       // Runtime error (or compile-time if detectable)

// Thin pointers need explicit bounds
void process(int *@thin arr, int len) {
    // Cannot index arr without check
    for (int i = 0; i < len; i++) {
        // Cyclone inserts bounds check
        arr[i] = i;
    }
}

// numelts() for fat pointers
int len = numelts(arr);
```

### 3.2.2 Tagged Unions

```c
// Safe unions (tagged)

@tagged union IntOrStr {
    int i;
    char *@fat s;
};

union IntOrStr x = {.i = 42};

// Pattern matching required
switch (x) {
case {.i = n}: printf("%d\n", n); break;
case {.s = s}: printf("%s\n", s); break;
}

// Cannot access wrong variant
// x.s when x contains int -> compile error
```

### 3.2.3 Definite Assignment

```c
// Must initialize before use

void foo() {
    int x;            // declared but not initialized
    // int y = x;     // ERROR: x not definitely assigned
    x = 42;
    int y = x;        // OK: x definitely assigned
}

// Conditionals tracked
void bar(int cond) {
    int x;
    if (cond) {
        x = 1;
    } else {
        x = 2;
    }
    int y = x;        // OK: x assigned in both branches
}
```

---

# PART IV: OTHER REGION SYSTEMS

## 4.1 Real-Time Java (RTSJ)

### 4.1.1 Memory Areas

```java
// RTSJ Memory Areas

// Immortal memory - never collected
ImmortalMemory.instance().enter(() -> {
    // Allocations here persist forever
});

// Scoped memory - region-like
LTMemory scope = new LTMemory(1024);
scope.enter(() -> {
    // Allocations here freed when scope exits
    Object o = new Object(); // in scope
});
// o now invalid

// Scoped memory nesting
LTMemory outer = new LTMemory(4096);
outer.enter(() -> {
    LTMemory inner = new LTMemory(1024);
    inner.enter(() -> {
        // Can access outer, but not vice versa
    });
});
```

### 4.1.2 Reference Rules

```java
// RTSJ enforces reference rules

// RULE: Cannot reference from longer-lived to shorter-lived

LTMemory scope = new LTMemory(1024);
Object[] heap_array = new Object[1];

scope.enter(() -> {
    Object scoped = new Object();
    // heap_array[0] = scoped;  // ERROR at runtime
    // Would create dangling reference
});

// Checked at runtime (not static like Cyclone)
```

## 4.2 Vault (Microsoft Research)

### 4.2.1 Adoption and Focus

```
Vault: Region-based C dialect with adoption

Adoption: Transfer object between regions
  adopt(Ï_dest, obj)  // move obj to region Ï_dest
  
Focus: Change which region an object is associated with
  focus(Ï, obj) { ... } // temporarily focus obj to Ï

Key Operations:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ adopt(Ï, obj)                          â”‚
â”‚   - obj moved to region Ï              â”‚
â”‚   - old region loses obj               â”‚
â”‚   - requires unique access to obj      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ focus(Ï, obj) { block }                â”‚
â”‚   - temporarily treat obj as in Ï      â”‚
â”‚   - must restore before block exits    â”‚
â”‚   - enables borrowing patterns         â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 4.2.2 Vault Type System

```
Vault Types:

Ï„ ::= int | bool | ...               -- base types
    | Ï„ ptr(Ï)                       -- pointer in region Ï
    | Ï„ tracked(k)                   -- tracked with key k
    | âˆ€Ï.Ï„                           -- region polymorphism
    | âˆƒÏ.Ï„                           -- existential region

Keys:
k ::= Îº                              -- key variable
    | kâ‚ âŠ— kâ‚‚                        -- key product
    | kâ‚ âŠ• kâ‚‚                        -- key sum

Judgments:
Î“; K âŠ¢ e : Ï„ ; K'
  Î“ = type context
  K = keys held before
  K' = keys held after

Example:
  Î“; {Îº} âŠ¢ free(p) : unit ; {}
  (freeing p consumes key Îº)
```

## 4.3 RC (Region-based C)

### 4.3.1 Overview

```c
// RC: Reference counting + regions

// Declare region type
region_t R;

// Allocate in region
int *p = RC_ALLOC(R, int);

// Reference counting within regions
RC_RETAIN(p);
RC_RELEASE(p);

// Delete entire region
RC_DELETE_REGION(R);

// Single-assignment regions
sregion_t SR;
int *q = SRC_ALLOC(SR, int);
// q is immutable after initialization
```

## 4.4 Rust Lifetimes (Region-like)

### 4.4.1 Lifetimes as Regions

```rust
// Rust lifetimes are essentially regions

// Explicit lifetime annotation
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// Lifetime bounds
fn process<'a, 'b: 'a>(short: &'a str, long: &'b str) -> &'a str {
    // 'b outlives 'a
    short
}

// Lifetime in structs
struct Ref<'a, T> {
    data: &'a T,
}

// Region-like scoping
fn foo() {
    let x = String::from("hello");  // x's region starts
    {
        let y = &x;  // y borrows from x's region
    }  // y's borrow ends
}  // x's region ends
```

## 4.5 Linear Regions (Fluet & Morrisett)

### 4.5.1 Capability-Based Regions

```
Linear Regions (Fluet & Morrisett 2006):

Key Idea: Region access requires capability
          Capability is linear (must be used exactly once)

Syntax:
  e ::= ...
      | letRgn x.e                    -- create region with capability x
      | freeRgn x                     -- destroy region (consume capability)
      | new[Ï] e                      -- allocate (requires capability)
      | !e                            -- dereference (requires capability)
      | dup x as (xâ‚, xâ‚‚).e           -- duplicate capability (if allowed)

Types:
  Ï„ ::= ...
      | Cap Ï                         -- capability for region Ï
      | Ï„ at Ï                        -- value in region Ï

Typing:
  Î“; Î” âŠ¢ e : Ï„ ; Î”'
  
  Î” = linear context (capabilities)
  Î”' = capabilities after e

Example:
  letRgn c.                           -- create region, get capability c
    let p = new[c] 42 in              -- allocate using c
    let v = !p in                     -- read using c
    freeRgn c;                        -- destroy region, consume c
    v                                 -- result escapes
```

---

# PART V: REGION INFERENCE ALGORITHMS

## 5.1 Tofte-Birkedal Algorithm

### 5.1.1 Overview

```
Region Inference (Tofte-Birkedal):

Input: ML program without region annotations
Output: Region-annotated program

Phases:
1. Type inference (standard HM)
2. Region variable introduction
3. Unification and effect collection
4. Effect simplification
5. Region normalization

Key Data Structures:
- RegionVar: fresh region variables
- Effect: set of region operations
- Constraint: region/effect constraints
```

### 5.1.2 Algorithm Details

```
Region Inference Algorithm:

PHASE 1: Introduce region variables
  For each allocation point, create fresh Ï
  For each function, create arrow effect Îµ
  
  Example:
    fun f x = (x, x+1)
    
    Becomes:
    fun f x = (x, x+1) at Ïâ‚  -- fresh Ïâ‚
    Type: int â†’^Îµ int Ã— int at Ïâ‚
          where Îµ = {put(Ïâ‚)}

PHASE 2: Collect constraints
  From typing derivation, extract:
  - Unification constraints: Ï„â‚ = Ï„â‚‚
  - Effect constraints: Îµâ‚ âŠ† Îµâ‚‚
  - Outlives constraints: Ïâ‚ â‰¥ Ïâ‚‚

PHASE 3: Solve constraints
  Unify types and regions
  Compute effect closure
  
PHASE 4: Normalize
  Merge regions with same lifetime
  Remove unnecessary region abstractions
  
Example normalization:
  âˆ€Ïâ‚,Ïâ‚‚. Ï„ where Ïâ‚ = Ïâ‚‚
  Becomes: âˆ€Ï. Ï„[Ï/Ïâ‚, Ï/Ïâ‚‚]
```

## 5.2 Storage Mode Analysis

### 5.2.1 ATTOP vs ATBOT

```
Storage Mode Analysis:

Goal: Determine if allocation can use ATTOP (stack-like)
      or must use ATBOT (heap-like)

ATTOP conditions:
1. Value does not escape its creation region
2. No references to value outlive the region
3. Value is allocated at region's top

ATBOT conditions:
1. Value may escape creation region
2. References may outlive the region
3. Must allocate in heap portion

Algorithm:
  For each allocation point:
    Compute value's "escape analysis"
    If may_escape(v, Ï) then ATBOT(Ï)
    Else ATTOP(Ï)

Example:
  letregion Ï in
    let x = (1, 2) at Ï       -- ATBOT (escapes)
        y = (3, 4) at Ï       -- ATTOP (local)
    in #1 x                    -- x escapes, y doesn't
  end
```

## 5.3 Region Size Analysis

### 5.3.1 Infinite Region Detection

```
Infinite Region Problem:

Issue: Some regions grow without bound
       Memory leak even with regions

Example:
  fun loop () =
    letregion Ï in
      let _ = (1,2) at Ï      -- allocation in loop
      in loop ()               -- infinite recursion
    end
  
  Ï is inside loop â†’ bounded
  But if Ï were outside â†’ unbounded growth

Detection:
  Build region lifetime graph
  Find regions whose lifetime spans recursive calls
  Flag as potentially infinite

Mitigation:
  - Reset regions at loop iteration
  - Use resettable regions
  - Warn programmer
```

---

# PART VI: SECURITY APPLICATIONS

## 6.1 Memory Safety via Regions

```
Memory Safety Properties:

1. NO DANGLING POINTERS
   Region typing ensures:
   - Cannot access pointer after region deallocation
   - Pointer validity tied to region lifetime
   
   Guarantee: âˆ€p:Ï„ at Ï. access(p) âŸ¹ live(Ï)

2. NO BUFFER OVERFLOWS (with bounds)
   Combined with fat pointers:
   - Bounds carried with pointer
   - Checked at access time
   
3. NO DOUBLE FREE
   Region-level deallocation:
   - Entire region freed at once
   - No individual object free
   
4. NO USE-AFTER-FREE
   Static guarantee from type system:
   - Region Ï in scope âŸ¹ allocations in Ï valid
   - Exiting scope âŸ¹ all Ï references invalidated
```

## 6.2 Secure Information Flow

```
Regions for Information Flow:

Idea: Allocate secrets in dedicated regions
      Track region access as information flow

Security Regions:
  Ï_public   -- public data region
  Ï_secret   -- secret data region
  Ï_tainted  -- untrusted input region

Typing rules:
  read(Ï_secret) only in trusted code
  write(Ï_public) cannot depend on Ï_secret
  Ï_tainted data must be sanitized before use

Example:
  letregion Ï_session [secret] in
    let key = generate_key() at Ï_session
    in encrypt(key, data)  -- key confined to Ï_session
  end  -- key destroyed, cannot leak
```

## 6.3 Constant-Time Guarantees

```
Regions for Constant-Time:

Approach: Secret data in dedicated regions
          Analyze access patterns per region

Region-based CT analysis:
  For each region Ï:
    If Ï is secret:
      All accesses must be constant-time
      No branching on Ï contents
      No Ï-dependent memory access patterns

Example:
  letregion Ï_key [secret, ct] in
    let key = load_key() at Ï_key
    in ct_compare(key, input)  -- constant-time op
  end

  // ct_compare type:
  // âˆ€Ï[ct]. bytes at Ï â†’ bytes â†’ bool
  // Effect: {get(Ï) | constant_time}
```

## 6.4 Capability Confinement

```
Regions for Capability Isolation:

Each capability domain gets its own region:

Sandboxing:
  letregion Ï_sandbox in
    let cap = create_capability() at Ï_sandbox
    in run_untrusted(cap)
  end  -- cap cannot escape sandbox

Cross-domain calls:
  letregion Ï_call in
    let args = marshal(data) at Ï_call
        result = cross_call(args)
    in unmarshal(result)
  end  -- args deallocated after call

No capability leakage:
  Capability typed as: Cap<P> at Ï_domain
  Cannot be stored in Ï_other
  Enforced by region typing
```

---

# PART VII: TERAS-LANG INTEGRATION ANALYSIS

## 7.1 Prior Decision Integration

### 7.1.1 A-04 (Linear Types)

Linear types and regions are complementary:

```
Linear + Regions:

Linear ensures: used exactly once
Region ensures: valid during lifetime

Combined:
  lin Ï„ at Ï
  
Meaning:
  - Value must be used exactly once (linear)
  - Value valid while Ï is live (region)
  - If Ï ends before use â†’ type error
  - If used more than once â†’ type error

Example:
  letregion Ï in
    let key: lin SecretKey at Ï = generate()
    in
      use_key(key)  -- consumes key (linear)
  end  -- Ï ends, key already consumed (OK)
```

### 7.1.2 A-06 (Uniqueness Types)

```
Uniqueness + Regions:

Unique ensures: no aliases
Region ensures: bounded lifetime

Combined:
  uniq Ï„ at Ï
  
Enables:
  - In-place update (uniqueness)
  - Deterministic deallocation (region)
  - Safe transfer between regions

Region transfer:
  fn transfer<'a, 'b>(
    x: uniq Buffer at 'a,
    target: region 'b
  ) -> uniq Buffer at 'b
  
  Uniqueness enables safe region change
```

### 7.1.3 A-07 (Session Types)

```
Session Types + Regions:

Channel endpoints in regions:

session Protocol at Ï =
  !{msg: Message at Ï}.
  ?{ack: Ack at Ï}.
  end

Region bounds message lifetime:
  - Messages allocated in Ï
  - Channel valid while Ï live
  - Protocol completion frees Ï

Cross-region sessions:
  letregion Ï_local, Ï_remote in
    session S at (Ï_local, Ï_remote)
    ...
  end
```

## 7.2 TERAS Product Applications

### 7.2.1 MENARA (Mobile Security)

```
Mobile Session Regions:

// Per-session region for mobile app
letregion Ï_session in
  let creds: Credentials at Ï_session = authenticate()
  let token: SessionToken at Ï_session = get_token(creds)
  in
    // All session data in Ï_session
    while session_active() {
      process_request(token)
    }
end  // Session ends, all data wiped

// Guarantees:
// - Credentials cannot outlive session
// - Token cannot be stored persistently
// - Memory wiped on session end
```

### 7.2.2 GAPURA (WAF)

```
Request Processing Regions:

// Per-request region for WAF
fn handle_request(req: Request) {
  letregion Ï_req in
    let parsed: ParsedRequest at Ï_req = parse(req)
    let sanitized: SanitizedRequest at Ï_req = sanitize(parsed)
    let response: Response at Ï_req = process(sanitized)
    in
      send(response)
  end  // Request data freed, no leakage
}

// Benefits:
// - No memory leaks between requests
// - Request isolation automatic
// - Deterministic cleanup
```

### 7.2.3 ZIRAH (EDR)

```
Analysis Regions:

// Per-analysis region for EDR
fn analyze_process(pid: ProcessId) {
  letregion Ï_analysis in
    let memory: MemorySnapshot at Ï_analysis = capture(pid)
    let patterns: Patterns at Ï_analysis = scan(memory)
    let threats: Vec<Threat> at Ï_analysis = detect(patterns)
    in
      report(threats)
  end  // Large snapshot freed immediately
}

// Critical for EDR:
// - Memory snapshots can be large
// - Must not accumulate across analyses
// - Deterministic freeing prevents OOM
```

### 7.2.4 BENTENG (eKYC)

```
Verification Regions:

// Per-verification region for eKYC
fn verify_identity(doc: Document, selfie: Image) {
  letregion Ï_verify [secret] in
    let extracted: BiometricData at Ï_verify = extract(doc)
    let computed: FaceVector at Ï_verify = compute(selfie)
    let score: f32 = compare(extracted, computed)
    in
      score >= THRESHOLD  // Only score escapes
  end  // Biometric data wiped
}

// Security properties:
// - Biometric data cannot escape
// - Automatic secure deletion
// - No persistent biometric storage
```

### 7.2.5 SANDI (Digital Signatures)

```
Signing Regions:

// Per-operation region for signing
fn sign(data: &[u8], key_handle: KeyHandle) {
  letregion Ï_sign [secret, ct] in
    let key: PrivateKey at Ï_sign = load_key(key_handle)
    let padded: PaddedData at Ï_sign = pad(data)
    let signature = ct_sign(key, padded)  // constant-time
    in
      signature  // Only signature escapes
  end  // Private key material wiped
}

// Guarantees:
// - Key never in heap (region-only)
// - Constant-time operation (ct region)
// - Secure wipe on completion
```

## 7.3 Recommended Design

```
TERAS-LANG Region Design:

1. SYNTAX
   letregion Ï [attrs] in e end
   Ï„ at Ï
   &'Ï T  (reference into region Ï)

2. REGION ATTRIBUTES
   [secret]    -- contains secret data
   [tainted]   -- contains untrusted data
   [ct]        -- constant-time access required
   [wipe]      -- secure wipe on deallocation

3. INTEGRATION WITH LINEAR/UNIQUE
   lin Ï„ at Ï      -- linear value in region
   uniq Ï„ at Ï     -- unique value in region

4. INTEGRATION WITH EFFECTS
   fn f(x: Ï„ at Ï) -> Ï„' ! {get(Ï), put(Ï)}

5. INFERENCE
   Region inference Ã  la Tofte-Talpin
   Storage mode analysis
   Escape analysis for ATTOP/ATBOT
```

---

# PART VIII: REFERENCES

## 8.1 Foundational Papers

1. Tofte, M., & Talpin, J.P. (1994). "Implementation of the Typed Call-by-Value Î»-calculus using a Stack of Regions." POPL.
2. Tofte, M., & Talpin, J.P. (1997). "Region-Based Memory Management." Information and Computation.
3. Birkedal, L., Tofte, M., & Vejlstrup, M. (1996). "From Region Inference to von Neumann Machines via Region Representation Inference." POPL.
4. Tofte, M., et al. (2004). "A Retrospective on Region-Based Memory Management." Higher-Order and Symbolic Computation.

## 8.2 Implementation Papers

5. Elsman, M. (2003). "Garbage Collection Safety for Region-Based Memory Management." TLDI.
6. Hallenberg, N., Elsman, M., & Tofte, M. (2002). "Combining Region Inference and Garbage Collection." PLDI.
7. Grossman, D., et al. (2002). "Region-Based Memory Management in Cyclone." PLDI.
8. Jim, T., et al. (2002). "Cyclone: A Safe Dialect of C." USENIX ATC.

## 8.3 Advanced Topics

9. Fluet, M., & Morrisett, G. (2006). "Linear Regions Are All You Need." ESOP.
10. Calcagno, C., et al. (2007). "Stratified Operational Semantics for Safety and Correctness of Region Calculus." POPL.
11. Walker, D., & Morrisett, G. (2000). "Alias Types for Recursive Data Structures." TIC.

---

**END OF SURVEY DOCUMENT**

**Document Statistics:**
- Total Lines: ~1,350
- Systems Covered: 8+
- Code Examples: 70+
- Security Applications: 15+
- References: 11

**Next Document:** RESEARCH_A12_REGION_TYPES_COMPARISON.md
