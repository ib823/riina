# RESEARCH_A15_STAGED_TYPES_COMPARISON.md

## TERAS Research Track â€” Domain A: Type Theory
### Session A-15: Staged Types â€” Comparative Analysis

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research

---

# PART I: SYSTEM COMPARISON MATRIX

## 1.1 Feature Matrix

| Feature | MetaOCaml | Template Haskell | Scala 3 Macros | Rust proc_macro | Zig comptime |
|---------|-----------|------------------|----------------|-----------------|--------------|
| **Staging Model** | MSP | Compile-time | Compile-time | Compile-time | Compile-time |
| **Type Safety** | Full | Partial/Full | Full | Limited | Limited |
| **Scope Safety** | Yes | Yes | Yes | Manual | Yes |
| **N-Stage** | Arbitrary | 2-stage | 2-stage | 2-stage | 2-stage |
| **Cross-Stage Persistence** | Yes | Yes | Yes | Manual | Yes |
| **Hygiene** | Automatic | Semi-auto | Automatic | Manual | Automatic |
| **Runtime Overhead** | Zero | Zero | Zero | Zero | Zero |
| **Production Ready** | Yes | Yes | Yes | Yes | Yes |

## 1.2 Type Safety Comparison

| Property | MetaOCaml | Template Haskell | Scala 3 | Rust | Zig |
|----------|-----------|------------------|---------|------|-----|
| Well-typed generation | âœ“ Full | TExp only | âœ“ Full | âœ— | Limited |
| Scope extrusion prevention | âœ“ | âœ“ | âœ“ | Manual | âœ“ |
| Phase distinction | âœ“ Full | Partial | âœ“ Full | âœ— | âœ“ |
| Variable capture | Prevented | Hygienic | Prevented | Manual | Prevented |

## 1.3 Design Philosophy Spectrum

```
                    TYPE SAFETY
                        ^
                        |
       MetaOCaml *      |      * Scala 3
        (full MSP)      |       (typed quotes)
                        |
                        |
         TH *           |
     (semi-typed)       |
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€> PRACTICALITY
                        |
           Zig *        |
        (comptime)      |      * Rust
                        |       (proc_macro)
                        |
```

---

# PART II: DETAILED SYSTEM COMPARISONS

## 2.1 MetaOCaml vs Template Haskell

### 2.1.1 Staging Model Comparison

| Aspect | MetaOCaml | Template Haskell |
|--------|-----------|------------------|
| Stage levels | Arbitrary (n-stage) | 2 stages (compile/run) |
| Code type | `'a code` | `Q Exp` / `TExp a` |
| Quotation | `.<e>.` | `[| e |]` / `[|| e ||]` |
| Splice | `.~e` | `$(...)` / `$$(...)` |
| Run | `!.e` | Compile-time only |

### 2.1.2 Type Safety Comparison

```
MetaOCaml Type Safety:
  - Full typed staging
  - Environment classifiers track scope
  - Cross-stage persistence safe
  
  .<fun x -> .~(f .<x>.)>.  // x safely in scope
  
Template Haskell Type Safety:
  - Untyped: Q Exp (any expression)
  - Typed: TExp a (type-indexed)
  
  [|| \x -> $$(f [|| x ||]) ||]  // TExp is safe
  [| \x -> $(f [| x |]) |]        // Q Exp less safe
```

### 2.1.3 Use Case Suitability

```
MetaOCaml Best For:
  - Multi-stage computation
  - Runtime code generation
  - Partial evaluation
  - Interpreter specialization

Template Haskell Best For:
  - Compile-time metaprogramming
  - Deriving instances
  - Quasi-quotation (DSLs)
  - Boilerplate elimination
```

## 2.2 Scala 3 vs MetaOCaml

### 2.2.1 Quote/Splice Comparison

```
Scala 3 Quotes:
  '{e}           -- quote expression
  ${e}           -- splice expression
  '[T]           -- quote type
  Type.of[T]     -- type reflection
  
  def power(n: Int)(x: Expr[Double])(using Quotes): Expr[Double] =
    if n == 0 then '{1.0}
    else '{ $x * ${power(n-1)(x)} }

MetaOCaml Brackets:
  .<e>.          -- bracket (quote)
  .~e            -- escape (splice)
  !.e            -- run
  
  let rec power n x =
    if n = 0 then .<1.0>.
    else .<.~x *. .~(power (n-1) x)>.
```

### 2.2.2 Feature Comparison

| Feature | Scala 3 | MetaOCaml |
|---------|---------|-----------|
| Type quotation | Yes `'[T]` | No |
| Multi-stage | 2-stage | N-stage |
| Runtime execution | Via reflection | Direct `!.` |
| Macro system | Integrated | Separate |
| IDE support | Good | Limited |

## 2.3 Rust proc_macro vs Zig comptime

### 2.3.1 Model Comparison

```
Rust Procedural Macros:
  - Token stream transformation
  - No type information during expansion
  - Must parse/generate tokens manually
  
  #[proc_macro]
  pub fn my_macro(input: TokenStream) -> TokenStream {
      // Transform tokens
  }
  
Zig comptime:
  - Regular code executed at compile time
  - Full type information available
  - Same syntax as runtime code
  
  fn power(comptime n: u32, x: f64) f64 {
      comptime var result: f64 = 1.0;
      inline for (0..n) |_| {
          result *= x;
      }
      return result;
  }
```

### 2.3.2 Type Safety Comparison

| Property | Rust proc_macro | Zig comptime |
|----------|-----------------|--------------|
| Input types | TokenStream | Full types |
| Output types | TokenStream | Full types |
| Type checking | Post-expansion | During comptime |
| Error location | Often opaque | Precise |

## 2.4 Cross-Stage Persistence

### 2.4.1 Comparison of Approaches

```
MetaOCaml CSP:
  - Values automatically lifted
  - Serialization/deserialization
  - Works for most types
  
  let n = 5 in .<n + 1>.  // n persists into code

Template Haskell CSP:
  - Lift type class
  - Manual for complex types
  
  let n = 5 in [| n + 1 |]  -- uses Lift instance

Scala 3 CSP:
  - ToExpr type class
  - Automatic for primitives
  
  val n = 5; '{ ${Expr(n)} + 1 }

Rust/Zig:
  - Compile-time constants
  - No runtime code generation
```

---

# PART III: INTEGRATION ANALYSIS

## 3.1 Integration with Linear Types (A-04)

### 3.1.1 Linear Staging Options

```
Option 1: Linear Code Types (MetaOCaml-style)
  lin code[Ï„]    -- linear staged code
  
  Must execute exactly once:
    let c : lin code[Unit] = .<close_connection conn>.
    run c  // Must run exactly once

Option 2: Staged Linear Values
  code[lin Ï„]    -- code producing linear value
  
  Generated code produces linear:
    let c : code[lin Connection] = .<open_connection()>.
    let conn : lin Connection = run c
    // conn must be used linearly
```

### 3.1.2 Recommended Approach

```
TERAS-LANG Linear Staging:

Both code linearity and result linearity:

lin code[Ï„]     -- code itself is linear (run once)
code[lin Ï„]     -- code produces linear result
lin code[lin Ï„] -- both

Example:
  fn critical() -> lin code[lin Transaction] {
    .<begin_transaction()>.
  }
  // Code must be run once
  // Transaction must be used linearly
```

## 3.2 Integration with Effects (A-11)

### 3.2.1 Effect Staging Options

```
Option 1: Effectful Code (Wyvern-style)
  code[Ï„ ! E]    -- code with effect E when run
  
  let c : code[String ! IO] = .<read_file "x">.
  run c : String ! IO

Option 2: Effect During Staging
  (code[Ï„]) ! E  -- effect during code construction
  
  let c : code[Int] ! IO = 
    let n = read_config() in  // IO during staging
    .<n + 1>.
```

### 3.2.2 Recommended Approach

```
TERAS-LANG Staged Effects:

Both staging and runtime effects:

code[Ï„ ! E]       -- runtime effect E
(code[Ï„]) ! F     -- staging-time effect F
(code[Ï„ ! E]) ! F -- both

Handler-based:
  handle { run c } 
  with EffectHandler {
    Read(file) => ...
  }
```

## 3.3 Integration with Capabilities (A-14)

### 3.3.1 Capability Staging

```
Staged Capability Authority:

code[cap<R, P>]   -- code that produces capability

Example:
  let cap_code : code[cap<File, Read>] = 
    .<open_file path>.
  
  let cap : cap<File, Read> = run cap_code
  // Now have file capability

Capability During Staging:
  fn build_code(fs: cap<FS, Read>) -> code[Data] {
    let config = fs.read_config()  // uses cap during staging
    .<process ~config>.           // embed in code
  }
```

### 3.3.2 Security Considerations

```
Staging Security:

1. Capability at Staging Time
   - Code construction may require capabilities
   - Different from runtime capabilities
   
2. Capability in Generated Code
   - Generated code may use capabilities
   - Must track capability requirements
   
3. Principle of Least Authority
   - Don't embed capabilities in code
   - Pass capabilities at runtime when needed
```

## 3.4 Integration with Regions (A-12)

### 3.4.1 Region-Staged Code

```
Region-Scoped Staging:

code[Ï„] at Ï     -- code valid in region Ï

letregion Ï in
  let c : code[Data] at Ï = .<compute()>.
  let result = run c
end
// Code and result in region

Cross-Stage Region Safety:
  .<letregion Ï in
      let x : Data at Ï = alloc()
      .~(escape x)   // ERROR: x escapes region
    end>.
```

---

# PART IV: PERFORMANCE ANALYSIS

## 4.1 Staging Overhead

| System | Compile Overhead | Runtime Overhead | Code Size |
|--------|------------------|------------------|-----------|
| MetaOCaml | Medium | Zero (specialized) | Smaller |
| Template Haskell | Medium-High | Zero | Variable |
| Scala 3 | Medium | Zero | Similar |
| Rust proc_macro | Low-Medium | Zero | Similar |
| Zig comptime | Low | Zero | Smaller |

## 4.2 Specialization Benefits

```
Performance Benefits from Staging:

1. Constant Folding
   power 4 x  â†’  x * x * x * x
   
2. Loop Unrolling
   for comptime i in 0..4: ...
   â†’  inline expansion
   
3. Dead Code Elimination
   if comptime cond then A else B
   â†’  only A or B compiled
   
4. Type Specialization
   generic<T>(x)  â†’  specialized_int(x)
```

## 4.3 Trade-off Summary

```
                COMPILE TIME
                    ^
                    |
          TH *      |
   (heavy macro     |
    expansion)      |
                    |
        Scala 3 *   |      * MetaOCaml
                    |         (n-stage)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€> RUNTIME BENEFIT
                    |
                    |
           Zig *    |      * Rust
        (simple     |       proc_macro
         comptime)  |
                    |

For TERAS: MetaOCaml/Scala 3 zone (typed staging, high benefit)
```

---

# PART V: EVALUATION FOR TERAS-LANG

## 5.1 Criteria and Weights

| Criterion | Weight | Rationale |
|-----------|--------|-----------|
| Type Safety | 25% | Generated code must be well-typed |
| Integration | 20% | A-04, A-11, A-14 compatibility |
| Security | 20% | No code injection risks |
| Performance | 15% | Zero overhead, good specialization |
| Usability | 10% | Developer productivity |
| Expressiveness | 10% | Can express needed patterns |

## 5.2 System Scores

| System | Type | Compat | Security | Perf | Usable | Express | **Total** |
|--------|------|--------|----------|------|--------|---------|-----------|
| MetaOCaml-style | 25/25 | 18/20 | 18/20 | 13/15 | 7/10 | 10/10 | **91/100** |
| Scala 3-style | 24/25 | 17/20 | 18/20 | 14/15 | 8/10 | 9/10 | **90/100** |
| TH-style | 20/25 | 14/20 | 15/20 | 13/15 | 8/10 | 9/10 | **79/100** |
| Zig-style | 15/25 | 10/20 | 18/20 | 15/15 | 9/10 | 7/10 | **74/100** |
| Rust-style | 12/25 | 8/20 | 14/20 | 14/15 | 7/10 | 8/10 | **63/100** |

## 5.3 Recommendation Summary

```
Ranking for TERAS-LANG:

1. MetaOCaml-style (91/100)
   Full typed MSP with environment classifiers
   Best type safety, good integration potential
   
2. Scala 3-style (90/100)
   Typed quotes with macro integration
   Good type safety, practical approach
   
3. TH-style (79/100)
   Compile-time with typed template Haskell
   Mixed safety, good ecosystem

Recommended Hybrid:
  - Core: MetaOCaml-style typed MSP
  - Enhancement: Scala 3-style type quotation
  - Practicality: Compile-time evaluation (Zig-style comptime)
```

---

# PART VI: SUMMARY

## 6.1 Key Comparative Findings

1. **MetaOCaml provides strongest type safety** â€” environment classifiers and scope safety
2. **Scala 3 offers good balance** â€” typed quotes with practical macro system
3. **Compile-time evaluation valuable** â€” Zig comptime for simple cases
4. **Rust proc_macro insufficient** â€” lacks type safety for security-critical code
5. **Integration feasible** â€” can combine with linear types, effects, capabilities

## 6.2 Design Direction

```
TERAS-LANG Staging Design:

Primary: MetaOCaml-style typed MSP
  - code[Ï„] as first-class type
  - Environment classifiers for scope safety
  - N-stage support for complex specialization
  
Compile-time: Zig-style comptime for constants
  - comptime keyword for compile-time evaluation
  - Type-level computation
  
Integration:
  - lin code[Ï„] for linear staged code
  - code[Ï„ ! E] for effectful generated code
  - code[cap<R,P>] for capability-producing code
```

---

**END OF COMPARISON DOCUMENT**

**Next Document:** RESEARCH_A15_STAGED_TYPES_DECISION.md
