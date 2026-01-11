# RESEARCH_A15_STAGED_TYPES_SURVEY.md

## TERAS Research Track â€” Domain A: Type Theory
### Session A-15: Staged Types (Multi-Stage Programming)

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Foundational Research
**Predecessor:** A-14 (Capability Types)
**Successor:** A-16 (Sized Types)

---

# PART I: FOUNDATIONS OF STAGED COMPUTATION

## 1.1 Historical Development

### 1.1.1 Origins: Partial Evaluation

Multi-stage programming evolved from partial evaluation research:

```
Partial Evaluation Timeline:

1971: Futamura Projections
      - First specializer = first Futamura projection
      - Compiler generation = second Futamura projection
      - Compiler generator generation = third projection

1988: Jones, Gomard, Sestoft
      - Binding-time analysis
      - Online vs offline specialization
      - Mix self-application

1993: Consel & Danvy
      - Two-level lambda calculus
      - Type-based binding-time analysis
      - Foundations of staging
```

### 1.1.2 Multi-Stage Programming

```
Multi-Stage Programming (MSP):

1997: Taha & Sheard
      - MetaML: first typed MSP language
      - Brackets, escape, run primitives
      - Type safety for code generation
      
1999: Davies & Pfenning
      - Modal type theory connection
      - â–¡A (necessity) = code type
      - Soundness via modality

2000: Calcagno et al.
      - Environment classifiers
      - Open code typing
      - Scope safety

2003: MetaOCaml
      - Practical MSP in OCaml
      - BER MetaOCaml (2014+)
      - Cross-stage persistence
```

### 1.1.3 Compile-Time Computation

```
Template and Macro Systems:

1986: Common Lisp Macros
      - Hygienic via gensym
      - eval-when for staging
      
1998: Scheme R5RS Macros
      - syntax-rules (hygienic)
      - syntax-case (flexible)
      
2002: Template Haskell
      - Typed splices
      - Reification
      - Quasi-quotation

2007: Scala Macros
      - Def macros
      - Blackbox vs whitebox
      
2015: Rust Procedural Macros
      - Token stream manipulation
      - Derive macros
```

## 1.2 Core Concepts

### 1.2.1 What is Staging?

```
Staging Definition:

Staging = explicit separation of computation phases

Phase 0 (now):     Current execution
Phase 1 (later):   Generated code execution
Phase n (later^n): n-th stage execution

Key Operations:
  <e>     -- bracket: delay computation to next stage
  ~e      -- escape: execute in current stage within bracket
  !e      -- run: execute generated code
  
Example:
  <1 + 2>           -- code that computes 3 (not yet run)
  !<1 + 2>          -- 3 (code generated and run)
  <1 + ~(compute())> -- splice computed value into code
```

### 1.2.2 Type Safety for Staging

```
Staged Type System:

Code Types:
  <Ï„>   -- code of type Ï„ (to be executed later)
  
Typing Rules:
  Î“ âŠ¢ e : Ï„
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (bracket)
  Î“ âŠ¢ <e> : <Ï„>
  
  Î“ âŠ¢ e : <Ï„>
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (run)
  Î“ âŠ¢ !e : Ï„
  
  Î“â‚€ âŠ¢ e : Ï„     (in code context Î“â‚)
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (escape)
  Î“â‚€, Î“â‚ âŠ¢ ~e : Ï„  (splice into code)
  
Safety Properties:
  - Well-typed code generates well-typed code
  - No unbound variables in generated code
  - No scope extrusion
```

### 1.2.3 Binding-Time Analysis

```
Binding-Time Classification:

Static (S): Known at compile time
  - Constants
  - Static function arguments
  - Compile-time computations

Dynamic (D): Known only at runtime
  - Runtime inputs
  - Dynamic function arguments
  - Computed values

Binding-Time Analysis (BTA):
  Input: Program + static/dynamic annotations
  Output: Staged program
  
  Example:
    power(n, x) = if n = 0 then 1 else x * power(n-1, x)
    
    With n:S, x:D:
    power_staged(n) = <Î»x. ~(if n = 0 
                              then <1> 
                              else <x * ~(power_staged(n-1) x)>)>
```

---

# PART II: DETAILED SYSTEM ANALYSIS

## 2.1 MetaML

### 2.1.1 Language Design

MetaML (Taha & Sheard, 1997) pioneered typed multi-stage programming:

```
MetaML Primitives:

Brackets: Delay computation
  <e>    : code Ï„  (if e : Ï„)
  
Escape: Splice into bracket
  ~e     : Ï„       (if e : code Ï„, inside bracket)
  
Run: Execute code
  !e     : Ï„       (if e : code Ï„)
  
Lift: Convert value to code
  lift e : code Ï„  (if e : Ï„, Ï„ liftable)

Example - Staged Power:
  let rec power n =
    if n = 0 then <1>
    else <~(power (n-1)) * x>
    
  // power 3 = <1 * x * x * x>
  // No runtime recursion!
```

### 2.1.2 Type System

```
MetaML Type System:

Types:
  Ï„ ::= int | bool | Ï„ â†’ Ï„ | code Ï„ | ...

Contexts:
  Î“ ::= Â· | Î“, x:Ï„
  
Level Annotation:
  Î“^n denotes context at level n
  
Rules:
  Î“^n âŠ¢ e : Ï„
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (bracket)
  Î“^(n-1) âŠ¢ <e> : code Ï„
  
  Î“^(n-1) âŠ¢ e : code Ï„
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (escape)
  Î“^n âŠ¢ ~e : Ï„
  
  Î“^0 âŠ¢ e : code Ï„
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (run)
  Î“^0 âŠ¢ !e : Ï„
```

### 2.1.3 Cross-Stage Persistence

```
Cross-Stage Persistence (CSP):

Problem: How to use stage-0 values in stage-1 code?

Solution: Lift values into code
  lift : Ï„ â†’ code Ï„  (for liftable Ï„)
  
Liftable Types:
  - Base types (int, bool, etc.)
  - Pairs of liftable types
  - NOT functions (in general)

Example:
  let x = 42 in <~(lift x) + 1>
  // Produces: <42 + 1>
  
CSP vs Escape:
  ~e    -- evaluates e, splices code
  lift  -- converts value to code literal
```

## 2.2 MetaOCaml

### 2.2.1 BER MetaOCaml

BER MetaOCaml is the modern implementation for OCaml:

```
BER MetaOCaml Syntax:

Brackets (quotation):
  .<e>.   : e code   (if e : t, then .<e>. : t code)
  
Escape (antiquotation):
  .~e     : t        (if e : t code, inside bracket)
  
Run:
  Runcode.run : 'a code -> 'a
  
Example:
  let rec power n x =
    if n = 0 then .<1>.
    else .<.~x * .~(power (n-1) x)>.
    
  // power 3 .<x>. = .<x * x * x * 1>.
```

### 2.2.2 Code Types in MetaOCaml

```
MetaOCaml Type System:

Code Type Constructor:
  'a code   -- code that produces 'a when run
  
Level Polymorphism (implicit):
  - Code types track generation level
  - Prevents scope extrusion
  
Example Types:
  power : int -> int code -> int code
  
  let square = .<fun x -> x * x>.
  // square : (int -> int) code
  
  let apply_square = fun c -> .<.~square .~c>.
  // apply_square : int code -> int code
```

### 2.2.3 Practical Features

```
BER MetaOCaml Features:

1. Offshoring (Code Extraction)
   - Generate C code from OCaml
   - Print_code for inspection
   - Compilation to native
   
2. Let-Insertion
   - Automatic binding hoisting
   - CSP-free programming style
   
3. Genlet
   genlet : 'a code -> 'a code
   - Generates let binding if beneficial
   - Avoids code duplication

Example - Matrix Multiply:
  let mmult a b =
    .<fun i j ->
      let sum = ref 0 in
      for k = 0 to n-1 do
        sum := !sum + .~a.(i).(k) * .~b.(k).(j)
      done;
      !sum>.
```

## 2.3 Template Haskell

### 2.3.1 Overview

Template Haskell provides compile-time metaprogramming:

```
Template Haskell Primitives:

Quotation:
  [| e |]      : Q Exp       (expression quote)
  [d| ... |]   : Q [Dec]     (declaration quote)
  [t| Ï„ |]     : Q Type      (type quote)
  [p| pat |]   : Q Pat       (pattern quote)
  
Splice:
  $(e)         : Ï„           (if e : Q Exp, result : Ï„)
  
Reification:
  reify ''T    : Q Info      (get type info)
  reify 'f     : Q Info      (get function info)

Example - Printf:
  printf :: String -> Q Exp
  printf fmt = ...
  
  -- Usage:
  $(printf "x = %d, y = %s") 42 "hello"
  -- Expands to type-safe code at compile time
```

### 2.3.2 Typed Template Haskell

```
Typed Template Haskell:

Typed Quotation:
  [|| e ||]    : Q (TExp Ï„)  (typed expression quote)
  
Typed Splice:
  $$(e)        : Ï„           (if e : Q (TExp Ï„))

Advantages:
  - Type errors at quote site, not splice site
  - Better error messages
  - Type-safe code generation

Example:
  power :: Int -> Q (TExp (Int -> Int))
  power 0 = [|| \_ -> 1 ||]
  power n = [|| \x -> x * $$(power (n-1)) x ||]
  
  -- $$(power 3) : Int -> Int
  -- Generates: \x -> x * x * x * 1
```

### 2.3.3 Reification and Deriving

```
Template Haskell Reification:

Get Type Information:
  reify ''Maybe   -- Info about Maybe type
  reify 'show     -- Info about show function
  
Derive Instances:
  $(deriveJSON defaultOptions ''MyType)
  
  -- Generates JSON instances at compile time
  
Generic Programming:
  $(makeLenses ''Person)
  
  -- Generates lens accessors

Code Generation Pattern:
  genInstance :: Name -> Q [Dec]
  genInstance name = do
    info <- reify name
    case info of
      TyConI (DataD _ _ _ _ cons _) ->
        -- Generate code based on constructors
```

## 2.4 Rust Procedural Macros

### 2.4.1 Macro Types

```
Rust Procedural Macros:

Function-like Macros:
  #[proc_macro]
  pub fn my_macro(input: TokenStream) -> TokenStream
  
  // Usage: my_macro!(...)

Derive Macros:
  #[proc_macro_derive(MyTrait)]
  pub fn derive_my_trait(input: TokenStream) -> TokenStream
  
  // Usage: #[derive(MyTrait)]

Attribute Macros:
  #[proc_macro_attribute]
  pub fn my_attr(attr: TokenStream, item: TokenStream) -> TokenStream
  
  // Usage: #[my_attr(...)] struct Foo { ... }
```

### 2.4.2 Quote and Syn

```
Rust Macro Libraries:

syn: Parse Rust code
  let input: DeriveInput = syn::parse(input)?;
  
quote: Generate Rust code
  let expanded = quote! {
      impl #name {
          pub fn new() -> Self {
              Self { #(#field_names: Default::default()),* }
          }
      }
  };

Example - Derive Debug:
  #[proc_macro_derive(MyDebug)]
  pub fn derive_debug(input: TokenStream) -> TokenStream {
      let input = parse_macro_input!(input as DeriveInput);
      let name = &input.ident;
      
      let expanded = quote! {
          impl std::fmt::Debug for #name {
              fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                  write!(f, stringify!(#name))
              }
          }
      };
      
      TokenStream::from(expanded)
  }
```

## 2.5 Other Staging Systems

### 2.5.1 Scala Macros

```
Scala 3 Macros (Quotes/Splices):

Quotes:
  '{ expr }    : Expr[T]     (quote expression)
  '[ Type ]    : Type[T]     (quote type)
  
Splices:
  ${ expr }    : T           (splice expression)
  
Inline:
  inline def power(inline n: Int, x: Double): Double =
    inline if n == 0 then 1.0
    else x * power(n - 1, x)
    
  // Fully expanded at compile time

Macro Definition:
  inline def assert(inline cond: Boolean): Unit =
    ${ assertImpl('cond) }
    
  def assertImpl(cond: Expr[Boolean])(using Quotes): Expr[Unit] =
    '{ if !$cond then throw AssertionError("Assertion failed") }
```

### 2.5.2 Terra

```
Terra Language:

Multi-stage with Lua as meta-language:

terra power(n: int, x: double): double
  if n == 0 then return 1.0 end
  return x * power(n-1, x)
end

-- Generate specialized version
local pow3 = terralib.specialize(power, {3})
-- pow3 has no runtime recursion

-- Lua generates Terra code
function genStruct(fields)
  local struct S {}
  for name, typ in pairs(fields) do
    S.entries:insert({name, typ})
  end
  return S
end

local Point = genStruct{x=double, y=double}
```

### 2.5.3 Zig Comptime

```
Zig Comptime:

Compile-time Execution:
  fn power(comptime n: i32, x: i32) i32 {
      if (n == 0) return 1;
      return x * power(n - 1, x);  // Unrolled at compile time
  }
  
  const result = power(3, 5);  // Computed at compile time

Comptime Types:
  fn Vector(comptime T: type, comptime size: usize) type {
      return struct {
          data: [size]T,
          
          fn get(self: *@This(), i: usize) T {
              return self.data[i];
          }
      };
  }
  
  var v: Vector(f32, 3) = undefined;
```

---

# PART III: TYPE THEORY FOUNDATIONS

## 3.1 Modal Logic Connection

### 3.1.1 Davies-Pfenning Framework

```
Modal Type Theory for Staging:

S4 Modal Logic:
  â–¡A    -- "necessarily A" = code of type A
  â—‡A    -- "possibly A" = (not typically used)
  
Inference Rules:
  Î“ âŠ¢ A
  â”€â”€â”€â”€â”€â”€â”€â”€  (â–¡I: Bracket)
  Î“ âŠ¢ â–¡A
  
  Î“ âŠ¢ â–¡A    Î”, x:A âŠ¢ B
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (â–¡E: Run/Bind)
  Î“, Î” âŠ¢ B
  
Modal Validity:
  Î“; Î” âŠ¢ A
  
  Î“ = valid hypotheses (usable at any stage)
  Î” = hypotheses at current stage only
```

### 3.1.2 Environment Classifiers

```
Environment Classifiers (Calcagno et al.):

Problem: Open code (code with free variables)

Solution: Track environment in type
  <A>^Ï   -- code of type A, valid in environment Ï
  
Classifiers:
  Ï ::= Îµ          -- empty (closed code)
       | Ï, x:A    -- extended environment
       
Typing Rules:
  Î“; Î” âŠ¢^Ï e : A
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (bracket)
  Î“; Î” âŠ¢^Ï' <e> : <A>^Ï
  
  Î“; Î” âŠ¢^Ï e : <A>^Ï
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (escape)
  Î“; Î” âŠ¢^Ï ~e : A
```

### 3.1.3 Levels and Worlds

```
Multi-Level Typing:

Level Annotation:
  Î“^n âŠ¢ e : A    -- judgment at level n
  
  Level 0: current execution
  Level 1: generated code (one stage delayed)
  Level n: n stages delayed

Consistency Rules:
  - Variables at level n can only be used at level â‰¥ n
  - Brackets increase level by 1
  - Escapes decrease level by 1
  - Run requires level 0
  
Example:
  Î“^0 âŠ¢ x : int                    -- x at level 0
  Î“^0 âŠ¢ <x + 1> : <int>            -- code at level 0
  Î“^1 âŠ¢ x + 1 : int                -- inside bracket
  Î“^0 âŠ¢ !<x + 1> : int             -- run at level 0
```

## 3.2 Safety Properties

### 3.2.1 Type Preservation

```
Type Preservation for Staging:

Theorem (Type Preservation):
  If Î“ âŠ¢ e : Ï„ and e â†’ e'
  then Î“ âŠ¢ e' : Ï„
  
Includes reduction rules:
  !<e> â†’ e                (run bracket)
  <~e> â†’ e                (bracket escape, if e : <Ï„>)
  
Code Reduction:
  <eâ‚> âŠ• <eâ‚‚> â†’ <eâ‚ âŠ• eâ‚‚>  (combine code)
```

### 3.2.2 Scope Safety

```
Scope Safety (No Extrusion):

Problem: Free variables escaping their scope

  let x = <y>         -- y is free!
  in !x               -- Runtime error: y unbound

Solution: Level checking
  
  Î“^n âŠ¢ y : Ï„ requires y âˆˆ Î“^m for some m â‰¤ n
  
  - Variables must be bound at level â‰¤ use level
  - Prevents capturing unbound variables
```

### 3.2.3 Progress

```
Progress for Staged Languages:

Theorem (Progress):
  If Â· âŠ¢^0 e : Ï„ (closed, level 0)
  then either:
    - e is a value, or
    - e â†’ e' for some e'
    
Values at level 0:
  - Base values (integers, etc.)
  - Functions
  - Code values <e> where e is a value
```

---

# PART IV: APPLICATIONS

## 4.1 High-Performance Code Generation

### 4.1.1 Domain-Specific Optimization

```
DSL with Staging:

Example: Linear Algebra
  type Vector n = <Array n Double>
  
  dot :: Vector n -> Vector n -> <Double>
  dot v1 v2 = 
    let rec loop i acc =
      if i >= n then acc
      else loop (i+1) <~acc + ~v1[i] * ~v2[i]>
    in loop 0 <0.0>
    
  -- dot for n=3 generates:
  -- <v1[0]*v2[0] + v1[1]*v2[1] + v1[2]*v2[2]>
```

### 4.1.2 Specialization

```
Program Specialization:

Generic Interpreter:
  eval :: Expr -> Env -> Value
  eval (Const n) env = n
  eval (Var x) env = lookup x env
  eval (Add e1 e2) env = eval e1 env + eval e2 env
  
Staged Interpreter (First Futamura):
  evalS :: Expr -> <Env -> Value>
  evalS (Const n) = <\env -> n>
  evalS (Var x) = <\env -> lookup x env>
  evalS (Add e1 e2) = 
    <\env -> ~(evalS e1) env + ~(evalS e2) env>
    
-- evalS compiles Expr to efficient code
-- No interpretation overhead at runtime
```

### 4.1.3 Parser Generation

```
Staged Parser Combinators:

Basic Parser:
  type Parser a = String -> Maybe (a, String)
  
Staged Parser:
  type SParser a = <String -> Maybe (a, String)>
  
  char :: Char -> SParser Char
  char c = <\s -> 
    if s[0] == c then Just (c, tail s) else Nothing>
    
  seq :: SParser a -> SParser b -> SParser (a,b)
  seq p1 p2 = <\s ->
    case ~p1 s of
      Just (a, s') -> case ~p2 s' of
        Just (b, s'') -> Just ((a,b), s'')
        Nothing -> Nothing
      Nothing -> Nothing>
      
-- Generates specialized, efficient parser code
```

## 4.2 Type-Safe Code Generation

### 4.2.1 Printf Example

```
Type-Safe Printf:

format :: String -> Q (TExp a)  -- TH typed splice

format "%d" = [|| \(x::Int) -> show x ||]
format "%s" = [|| \(x::String) -> x ||]
format (c:rest) = [|| $(format rest) . (c:) ||]

-- Usage:
$$(format "%d + %d = %d") 1 2 3
-- Type: Int -> Int -> Int -> String
-- Generates: \x y z -> show x ++ " + " ++ show y ++ " = " ++ show z
```

### 4.2.2 SQL Query Generation

```
Type-Safe SQL:

-- Schema as types
data Person = Person { name :: Text, age :: Int }

-- Staged query builder
select :: Table a -> <Query a>
where_ :: <Bool> -> <Query a> -> <Query a>
from :: <Query a> -> <SQL>

-- Usage
query = $$(from (where_ [|| age > 18 ||] (select persons)))

-- Generates: SELECT * FROM persons WHERE age > 18
-- Type-checked at compile time
```

## 4.3 Security Applications

### 4.3.1 Staged Information Flow

```
Staged Security Types:

Secret Data in Staging:
  type Secret a = <a>  -- Secret = delayed computation
  
  -- Cannot inspect secret at stage 0
  -- Can only process and return as code
  
declassify :: <a> -> a  -- Controlled interface
declassify = run

-- Pattern: Process secrets without revealing
processSecret :: Secret Int -> <Int>
processSecret s = <~s * 2>  -- Never runs secret directly
```

### 4.3.2 Capability at Compile Time

```
Compile-Time Capability Checking:

-- Capability encoded as type-level staging
type Cap r p = <r -> p>

-- Attenuation
attenuate :: Cap r Full -> Cap r Read
attenuate cap = <\r -> readonly (~cap r)>

-- Compile-time capability verification
checkCap :: Cap File Read -> <File -> String>
checkCap cap = <\f -> read (~cap f)>
```

---

# PART V: SECURITY APPLICATIONS FOR TERAS

## 5.1 MENARA (Mobile Security)

```
Staged Security for Mobile:

// Protocol code generation
protocol_handler :: Protocol -> <Message -> Response>
protocol_handler TLS = <\msg -> handle_tls msg>
protocol_handler HTTPS = <\msg -> handle_https msg>

// Specialized at compile time for known protocols

// Crypto operation staging
crypto_staged :: CryptoParams -> <Data -> Ciphertext>
crypto_staged params = 
  let key = derive_key params in
  <\data -> encrypt key data>
  
// Key derivation happens at staging time
// Only encryption remains at runtime
```

## 5.2 GAPURA (WAF)

```
Staged WAF Rules:

// Rule compilation
compile_rule :: Rule -> <Request -> Decision>
compile_rule (Match pattern action) =
  let regex = compile_regex pattern in
  <\req -> if matches regex req.path then action else Pass>
  
// WAF ruleset generation
compile_rules :: [Rule] -> <Request -> Decision>
compile_rules rules = 
  let compiled = map compile_rule rules in
  <\req -> fold_decisions (~compiled) req>
  
// Regex compilation at staging time
// Only matching at runtime
```

## 5.3 ZIRAH (EDR)

```
Staged Detection Signatures:

// Signature compilation
compile_signature :: Signature -> <Process -> Bool>
compile_signature (Pattern bytes mask) =
  let matcher = build_matcher bytes mask in
  <\proc -> match_memory proc matcher>
  
// Behavior rule compilation
compile_behavior :: BehaviorRule -> <Events -> Alert>
compile_behavior rule =
  let automaton = build_automaton rule in
  <\events -> run_automaton events automaton>
  
// Detection logic specialized at compile time
```

## 5.4 BENTENG (eKYC)

```
Staged Verification:

// Document verification logic
compile_verification :: DocType -> <Image -> Result>
compile_verification Passport =
  <\img -> verify_passport img>
compile_verification NationalID =
  <\img -> verify_national_id img>
  
// Biometric matching
compile_matcher :: BiometricType -> <Template -> Template -> Score>
compile_matcher Face =
  let model = load_face_model () in
  <\t1 t2 -> face_match model t1 t2>
  
// Model loading at staging time
```

## 5.5 SANDI (Digital Signatures)

```
Staged Cryptography:

// Algorithm specialization
compile_sign :: SignatureAlgorithm -> <Key -> Message -> Signature>
compile_sign RSA =
  let rsa_impl = build_rsa_impl () in
  <\key msg -> rsa_sign rsa_impl key msg>
compile_sign ECDSA =
  let ecdsa_impl = build_ecdsa_impl () in
  <\key msg -> ecdsa_sign ecdsa_impl key msg>
  
// Verification
compile_verify :: SignatureAlgorithm -> <PublicKey -> Message -> Signature -> Bool>
compile_verify alg = ...

// Algorithm implementation built at staging time
// Only actual crypto ops at runtime
```

---

# PART VI: INTEGRATION WITH TYPE SYSTEM

## 6.1 Integration with Linear Types (A-04)

```
Linear Staged Types:

lin <Ï„>    -- linear code (must be run exactly once)

Example:
  let code : lin <Connection -> ()> = 
    <\conn -> close conn>
  in !code connection  -- Must use code exactly once

Typing:
  Î“ âŠ¢ e : lin <Ï„>
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  Î“ âŠ— Â· âŠ¢ !e : Ï„
```

## 6.2 Integration with Effects (A-11)

```
Staged Effects:

<Ï„ ! E>    -- code with effect E when run

Example:
  let code : <String ! IO> = <readFile "data.txt">
  
  // Running introduces effect
  !code : String ! IO

Effect Staging:
  Î“ âŠ¢ e : Ï„ ! E
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  Î“ âŠ¢ <e> : <Ï„ ! E>
```

## 6.3 Integration with Capabilities (A-14)

```
Staged Capabilities:

<cap<R, P>>   -- code that produces capability

Example:
  let cap_code : <cap<File, Read>> = <open_file "data.txt">
  let cap : cap<File, Read> = !cap_code
  
Staged Authority:
  -- Capability usage can be staged
  let read_code : cap<File, Read> -> <String> = 
    \c -> <read_file c>
```

---

# PART VII: SUMMARY

## 7.1 Key Systems Surveyed

| System | Approach | Type Safety | Production |
|--------|----------|-------------|------------|
| MetaML | Typed MSP | Full | Research |
| MetaOCaml | OCaml MSP | Full | Yes |
| Template Haskell | Compile-time | Partial/Full | Yes |
| Rust proc_macro | Token streams | Partial | Yes |
| Scala 3 Macros | Quotes/splices | Full | Yes |
| Zig comptime | Compile execution | Limited | Yes |

## 7.2 Core Staging Properties

```
Essential Staging Properties:

1. Type Safety
   Generated code is well-typed
   
2. Scope Safety
   No unbound variables in generated code
   
3. Phase Separation
   Clear stage boundaries
   
4. Efficiency
   Staging overhead eliminated at runtime
   
5. Expressiveness
   Can express useful metaprograms
```

## 7.3 Design Considerations for TERAS-LANG

```
TERAS-LANG Staging Design Questions:

1. Staging Model
   - Full MSP (MetaML/MetaOCaml style)?
   - Compile-time only (Template Haskell style)?
   - Inline expansion (Zig comptime style)?
   
2. Type Safety Level
   - Untyped quotation?
   - Typed quotation (TH TExp)?
   - Full typed MSP?
   
3. Integration Priorities
   - With linear types: lin <Ï„>
   - With effects: <Ï„ ! E>
   - With capabilities: <cap<R, P>>
   
4. Security Applications
   - Code generation for crypto?
   - Protocol specialization?
   - Rule compilation?
```

---

**END OF SURVEY DOCUMENT**

**Next Document:** RESEARCH_A15_STAGED_TYPES_COMPARISON.md
