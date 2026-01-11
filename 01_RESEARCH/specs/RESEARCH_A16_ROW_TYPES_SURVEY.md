# TERAS-LANG Research Track
# Session A-16: Row Types and Row Polymorphism
# Document Type: Comprehensive Survey

```
â•”â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•—
â•‘  RESEARCH SESSION A-16: ROW TYPES AND ROW POLYMORPHISM                       â•‘
â•‘                                                                               â•‘
â•‘  Date: 2026-01-03                                                            â•‘
â•‘  Domain: A (Type Theory Foundations)                                         â•‘
â•‘  Session: 16 of 20                                                           â•‘
â•‘  Predecessor: A-15 (Staged Types and Multi-Stage Programming)                â•‘
â•‘  Successor: A-17 (Higher-Kinded Types)                                       â•‘
â•‘                                                                              â•‘
â•‘  Research Coverage:                                                          â•‘
â•‘  â€¢ Wand's Row Polymorphism (1987-1991)                                       â•‘
â•‘  â€¢ RÃ©my's ML Record Extension (1989-1994)                                    â•‘
â•‘  â€¢ OCaml Polymorphic Variants                                                â•‘
â•‘  â€¢ PureScript Row Types                                                      â•‘
â•‘  â€¢ Extensible Records (Elm, Ur/Web)                                          â•‘
â•‘  â€¢ TypeScript Mapped Types                                                   â•‘
â•‘  â€¢ Row-Based Effect Systems                                                  â•‘
â•‘  â€¢ Scoped Labels and Qualified Types                                         â•‘
â•šâ•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•
```

---

## Table of Contents

1. [Foundations and Historical Context](#1-foundations-and-historical-context)
2. [Wand's Row Polymorphism](#2-wands-row-polymorphism)
3. [RÃ©my's ML Extension](#3-rÃ©mys-ml-extension)
4. [OCaml Polymorphic Variants](#4-ocaml-polymorphic-variants)
5. [PureScript Row Types](#5-purescript-row-types)
6. [Extensible Records in Practice](#6-extensible-records-in-practice)
7. [Row-Based Effect Systems](#7-row-based-effect-systems)
8. [TypeScript Mapped and Conditional Types](#8-typescript-mapped-and-conditional-types)
9. [Advanced Row Theories](#9-advanced-row-theories)
10. [Security Applications](#10-security-applications)
11. [Implementation Strategies](#11-implementation-strategies)
12. [TERAS Product Applications](#12-teras-product-applications)
13. [Integration with Prior Sessions](#13-integration-with-prior-sessions)
14. [Bibliography](#14-bibliography)

---

## 1. Foundations and Historical Context

### 1.1 The Record Problem

Traditional ML-style type systems treat records nominally or with fixed structure:

```ml
(* Fixed record type *)
type point = { x: float; y: float }

(* Function only works with 'point' *)
let get_x (p: point) = p.x
```

**Limitation**: Cannot write functions polymorphic over record structure.

Desired capability:
```ml
(* Function works with ANY record containing 'x' field *)
let get_x r = r.x  (* Type: {x: Î± | Ï} â†’ Î± *)
```

### 1.2 The Variance Challenge

Records and variants have opposite variance:

| Construct | Subtyping Direction | Covariance |
|-----------|---------------------|------------|
| Records | More fields â‰¤ Fewer fields | Width subtyping (subsumption) |
| Variants | Fewer cases â‰¤ More cases | Opposite to records |

This duality suggests a unified treatment via row types.

### 1.3 Historical Development

```
Timeline of Row Polymorphism:
                                                                    
1987 â”€â”¬â”€ Wand: Row Variables (POPL)                               
      â”‚  First formal treatment of record polymorphism             
      â”‚                                                            
1989 â”€â”¼â”€ RÃ©my: Record Extension (POPL)                            
      â”‚  Presence/absence flags, ML-style inference                
      â”‚                                                            
1994 â”€â”¼â”€ RÃ©my: Typing Record Concatenation (POPL)                 
      â”‚  Safe record concatenation with row types                  
      â”‚                                                            
1996 â”€â”¼â”€ OCaml Polymorphic Variants                               
      â”‚  Row types for sum types (variants)                        
      â”‚                                                            
2006 â”€â”¼â”€ Leijen: Extensible Records with Scoped Labels            
      â”‚  Duplicate labels, scoped resolution                       
      â”‚                                                            
2012 â”€â”¼â”€ PureScript                                               
      â”‚  First-class row polymorphism in production                
      â”‚                                                            
2016 â”€â”¼â”€ TypeScript Mapped Types                                  
      â”‚  Practical row-like manipulation                           
      â”‚                                                            
2019 â”€â”´â”€ Row Polymorphism in Effect Systems                       
        Koka, Frank, Eff                                           
```

---

## 2. Wand's Row Polymorphism

### 2.1 Core Insight (1987)

Mitchell Wand introduced row variables to type record operations polymorphically.

**Key Type Forms**:
```
Row ::= âˆ…                    (* Empty row *)
     |  (â„“ : Ï„ ; Ï)         (* Label extension *)
     |  Ï                    (* Row variable *)

Record ::= {Ï}               (* Record from row *)
```

**Row Variable**: Ï ranges over sets of labeled types.

### 2.2 Type Rules

**Record Construction**:
```
Î“ âŠ¢ e : Ï„    Î“ âŠ¢ r : {Ï}    â„“ âˆ‰ Ï
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ {â„“ = e ; r} : {â„“ : Ï„ ; Ï}
```

**Field Selection**:
```
Î“ âŠ¢ r : {â„“ : Ï„ ; Ï}
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ r.â„“ : Ï„
```

**Polymorphic Projection**:
```
get_x : âˆ€Î± Ï. {x : Î± ; Ï} â†’ Î±
get_x = Î»r. r.x
```

### 2.3 Example Derivation

```
get_x {x = 1; y = 2; z = 3}
â”‚
â”œâ”€ r : {x : int ; y : int ; z : int ; âˆ…}
â”‚
â”œâ”€ Unify: {x : Î± ; Ï} ~ {x : int ; y : int ; z : int ; âˆ…}
â”‚  Î± := int
â”‚  Ï := (y : int ; z : int ; âˆ…)
â”‚
â””â”€ Result: int
```

### 2.4 Limitations of Original Formulation

1. **Row commutativity**: Order-dependent (â„“â‚ : Ï„â‚ ; â„“â‚‚ : Ï„â‚‚) â‰  (â„“â‚‚ : Ï„â‚‚ ; â„“â‚ : Ï„â‚)
2. **No duplicate labels**: Each label appears at most once
3. **Lacks row constraints**: Cannot express "â„“ âˆ‰ Ï" in types directly

---

## 3. RÃ©my's ML Extension

### 3.1 Presence/Absence Flags (1989)

Didier RÃ©my extended row types with explicit presence annotations:

```
Flag ::= Pre(Ï„)    (* Field present with type Ï„ *)
      |  Abs       (* Field absent *)

Row ::= âˆ…
     |  (â„“ : Flag ; Ï)
     |  Ï

Record ::= {| Ï |}
```

### 3.2 The Key Innovation

Every label has a status (present or absent) for every row:

```
{| x : Pre(int) ; y : Pre(string) ; z : Abs ; Ï |}
```

This row has `x` and `y` present, `z` absent, and Ï determines remaining labels.

### 3.3 Type Rules with Flags

**Field Access**:
```
Î“ âŠ¢ r : {| â„“ : Pre(Ï„) ; Ï |}
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ r.â„“ : Ï„
```

**Record Extension**:
```
Î“ âŠ¢ e : Ï„    Î“ âŠ¢ r : {| â„“ : Abs ; Ï |}
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ {â„“ = e ; r} : {| â„“ : Pre(Ï„) ; Ï |}
```

**Field Removal**:
```
Î“ âŠ¢ r : {| â„“ : Pre(Ï„) ; Ï |}
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ r \ â„“ : {| â„“ : Abs ; Ï |}
```

### 3.4 Row Unification

RÃ©my's algorithm handles row unification with flags:

```
Unify((â„“ : fâ‚ ; Ïâ‚), (â„“ : fâ‚‚ ; Ïâ‚‚)) =
  Unify(fâ‚, fâ‚‚) âˆ˜ Unify(Ïâ‚, Ïâ‚‚)

Unify(Pre(Ï„â‚), Pre(Ï„â‚‚)) = Unify(Ï„â‚, Ï„â‚‚)
Unify(Abs, Abs) = id
Unify(Pre(_), Abs) = FAIL
Unify(Ï, row) = [Ï â†¦ row]  (* Row variable substitution *)
```

### 3.5 Record Concatenation (1994)

RÃ©my solved safe record concatenation:

```
concat : âˆ€Ïâ‚ Ïâ‚‚ Ïâ‚ƒ. 
         {| Ïâ‚ |} â†’ {| Ïâ‚‚ |} â†’ {| Ïâ‚ƒ |}
         where Ïâ‚ âŠ• Ïâ‚‚ = Ïâ‚ƒ
```

The constraint `Ïâ‚ âŠ• Ïâ‚‚ = Ïâ‚ƒ` ensures:
- Labels in Ïâ‚ and Ïâ‚‚ are disjoint
- Ïâ‚ƒ contains exactly labels from both

---

## 4. OCaml Polymorphic Variants

### 4.1 Row Types for Sum Types

OCaml applies row polymorphism to variants (sums), not just records:

```ocaml
(* Polymorphic variant value *)
`Foo 42  (* Type: [> `Foo of int ] *)

(* Closed variant *)
type color = [ `Red | `Green | `Blue ]

(* Open variant *)
type color_or_more = [> `Red | `Green | `Blue ]
```

### 4.2 Variance Annotations

```ocaml
[> `A | `B ]   (* At least these constructors *)
[< `A | `B ]   (* At most these constructors *)
[= `A | `B ]   (* Exactly these constructors *)
```

**Type Relationships**:
```
[= `A | `B ] <: [> `A | `B ]     (* Exact is subtype of "at least" *)
[< `A | `B ] <: [= `A | `B ]     (* "At most" is subtype of exact *)
```

### 4.3 Row Variable in OCaml

```ocaml
let f x = match x with
  | `A -> 1
  | `B -> 2

(* Inferred type: [< `A | `B ] -> int *)
(* The [< ...] indicates upper bound on variants *)
```

### 4.4 Combining Variants

```ocaml
type ab = [ `A | `B ]
type bc = [ `B | `C ]
type abc = [ ab | bc ]  (* [ `A | `B | `C ] *)

let handle_ab : ab -> int = function
  | `A -> 1
  | `B -> 2

let handle_abc : abc -> int = function
  | #ab as x -> handle_ab x  (* Coercion via row inclusion *)
  | `C -> 3
```

### 4.5 Pattern Matching Exhaustiveness

```ocaml
let complete : [< `A | `B | `C ] -> int = function
  | `A -> 1
  | `B -> 2
  | `C -> 3
  (* Exhaustive: handles all cases in upper bound *)

let partial : [> `A | `B ] -> int = function
  | `A -> 1
  | `B -> 2
  | _ -> 0  (* Need catch-all: row variable may have more cases *)
```

---

## 5. PureScript Row Types

### 5.1 First-Class Row Polymorphism

PureScript (2012+) provides the most explicit row type system:

```purescript
-- Explicit row type
type Point = { x :: Number, y :: Number }

-- Row-polymorphic function
getX :: forall r. { x :: Number | r } -> Number
getX rec = rec.x
```

### 5.2 Row Syntax

```purescript
-- Row kind
Row :: Type -> Type

-- Empty row
()

-- Row extension
(label :: Type | row)

-- Record from row
Record row  or  { row }
```

### 5.3 Operations on Rows

**Field Access**:
```purescript
_.x :: forall r. { x :: a | r } -> a
```

**Record Update**:
```purescript
_ { x = 5 } :: forall r. { x :: Int | r } -> { x :: Int | r }
```

**Record Construction**:
```purescript
{ x: 1, y: "hello" } :: { x :: Int, y :: String }
```

### 5.4 Row Constraints

PureScript uses row constraints for effects and other purposes:

```purescript
-- Effect row
type Effect eff = Eff (eff :: Effect)

-- Console effect
log :: forall eff. String -> Eff (console :: CONSOLE | eff) Unit

-- Combining effects
program :: forall eff. 
  Eff (console :: CONSOLE, random :: RANDOM | eff) Number
program = do
  log "Generating random number"
  random
```

### 5.5 Row Unification in PureScript

```purescript
-- These unify:
{ x :: Int | r } ~ { x :: Int, y :: String }
-- r := (y :: String)

-- These fail to unify:
{ x :: Int | r } ~ { x :: String, y :: Int }
-- Int â‰ String
```

---

## 6. Extensible Records in Practice

### 6.1 Elm Extensible Records

Elm (2012-2016 era) had extensible records:

```elm
-- Extensible record type
type alias Positioned a = { a | x : Float, y : Float }

-- Works with any record having x, y
moveRight : Positioned a -> Positioned a
moveRight obj = { obj | x = obj.x + 1 }

-- Apply to different record types
point = { x = 0, y = 0 }
player = { x = 0, y = 0, health = 100, name = "Hero" }

moveRight point   -- { x = 1, y = 0 }
moveRight player  -- { x = 1, y = 0, health = 100, name = "Hero" }
```

### 6.2 Ur/Web Row Types

Ur/Web provides sophisticated row types for web programming:

```urweb
(* Row type for HTML form *)
type form_row = [Name = string, Age = int, Email = string]

(* Generic form processor *)
val process : r ::: {Type} -> $(r) -> transaction unit

(* Field iteration via row polymorphism *)
val map_record : r ::: {Type} -> 
                 (f :: Type -> Type) ->
                 (a ::: Type -> a -> f a) ->
                 $(r) -> $(map f r)
```

### 6.3 Haskell Row Types Libraries

Several Haskell libraries implement row types:

**vinyl** (Anonymous Records):
```haskell
type Person = '[ "name" ::: String, "age" ::: Int ]

getPerson :: Record Person
getPerson = #name =: "Alice" :& #age =: 30 :& RNil

getName :: Record r -> String
getName rec = rec ^. rlens #name
-- Requires: "name" ::: String âˆˆ r
```

**row-types** package:
```haskell
type User = "name" .== String .+ "id" .== Int

getField :: forall l r a. (l .! r ~ a) => Label l -> Rec r -> a
```

---

## 7. Row-Based Effect Systems

### 7.1 Effects as Row Extensions

Modern effect systems use row polymorphism:

```koka
// Koka effect rows
fun greet(): <console, exn> string
  println("Enter name:")
  val name = readline()
  if name == "" then throw("empty name")
  "Hello, " ++ name

// Effect polymorphism
fun twice<e>(action: () -> e a): e (a, a)
  (action(), action())
```

### 7.2 Effect Row Operations

```
Effect Row Syntax:
                                                                    
  <e>           = Effect row variable                              
  <console|e>   = Console effect + rest of row                     
  <exn,state|e> = Exception + State + rest                         
  <>            = Pure (empty effect row)                           
```

### 7.3 Frank Language

Frank (Lindley, McBride, et al.) uses row-typed abilities:

```frank
-- Ability with operations
ability State X
  get : X
  put : X -> Unit

-- Handler with row polymorphism
runState : {<State X|e>a -> X -> {e}(a, X)}
runState <get -> k>    x = runState (k x)   x
runState <put x -> k>  _ = runState (k Unit) x
runState {a}           x = (a, x)
```

### 7.4 Eff Language

Eff (Bauer, Pretnar) uses row-like effect typing:

```eff
effect State : sig
  val get : unit â†’ int
  val put : int â†’ unit
end

let state_handler = handler
  | val x â†’ (fun _ â†’ x)
  | get () k â†’ (fun s â†’ k s s)
  | put s k â†’ (fun _ â†’ k () s)
```

### 7.5 Row Polymorphism for Effect Inference

```
Effect inference via rows:
                                                                    
Program:                                                           
  let f () =                                                       
    print "hello";                                                 
    read_int ()                                                    
                                                                    
Inferred:                                                          
  f : unit -> <io, console | e> int                                
                                                                    
Row variable 'e' captures any additional effects                    
the caller might have in scope.                                    
```

---

## 8. TypeScript Mapped and Conditional Types

### 8.1 Mapped Types

TypeScript provides row-like transformations:

```typescript
// Original type
type Person = {
  name: string;
  age: number;
};

// Mapped type - make all properties optional
type Partial<T> = {
  [P in keyof T]?: T[P];
};

// Result
type PartialPerson = Partial<Person>;
// { name?: string; age?: number; }
```

### 8.2 Key Remapping

```typescript
// Rename all keys with prefix
type Prefixed<T, P extends string> = {
  [K in keyof T as `${P}${string & K}`]: T[K];
};

type PrefixedPerson = Prefixed<Person, "user_">;
// { user_name: string; user_age: number; }
```

### 8.3 Conditional Types with Rows

```typescript
// Extract properties of a specific type
type ExtractStrings<T> = {
  [K in keyof T as T[K] extends string ? K : never]: T[K];
};

type StringProps = ExtractStrings<Person>;
// { name: string }
```

### 8.4 Pick and Omit

```typescript
// Standard row operations
type Pick<T, K extends keyof T> = {
  [P in K]: T[P];
};

type Omit<T, K extends keyof any> = Pick<T, Exclude<keyof T, K>>;

type NameOnly = Pick<Person, "name">;      // { name: string }
type AgeOnly = Omit<Person, "name">;        // { age: number }
```

### 8.5 Template Literal Types

```typescript
// Dynamic property generation
type Getters<T> = {
  [K in keyof T as `get${Capitalize<string & K>}`]: () => T[K];
};

type PersonGetters = Getters<Person>;
// { getName: () => string; getAge: () => number; }
```

---

## 9. Advanced Row Theories

### 9.1 Scoped Labels (Leijen 2005)

Daan Leijen's extension allows duplicate labels:

```
Row ::= âˆ…
     |  (â„“ : Ï„ ; Ï)
     |  Ï

-- Duplicate labels allowed
{x : int ; x : string ; y : bool}

-- Selection with scoping
r.x    -- Gets outermost x (int)
(r\x).x -- Gets next x (string) after removing first
```

### 9.2 Qualified Types for Rows

```
Constrained row polymorphism:

lacks(Ï, â„“)     -- Row Ï doesn't contain label â„“
has(Ï, â„“ : Ï„)   -- Row Ï contains label â„“ with type Ï„

Example:
extend : âˆ€Î± Ï. lacks(Ï, â„“) â‡’ Î± â†’ {Ï} â†’ {â„“ : Î± ; Ï}
```

### 9.3 First-Class Labels

Some systems make labels first-class:

```
Label : String â†’ LabelType

get : âˆ€â„“ Î± Ï. Label â„“ â†’ {â„“ : Î± ; Ï} â†’ Î±

-- Dynamic label access
let lbl = #name
get lbl {name = "Alice", age = 30}  -- "Alice"
```

### 9.4 Row Kinds

Higher-kinded row polymorphism:

```
kind Row = * â†’ *

-- Functor over rows
class RowFunctor f where
  rowMap : âˆ€Ï. (âˆ€â„“ Î±. Î± â†’ f Î±) â†’ {Ï} â†’ {Ï}[f]

-- Apply type constructor to all fields
type Optionalized r = {r}[Option]
-- {x : int ; y : string} becomes {x : Option int ; y : Option string}
```

### 9.5 Substructural Row Types

Combining rows with linearity:

```
Linear row:    lin {â„“â‚ : Ï„â‚ ; â„“â‚‚ : Ï„â‚‚}  -- Each field used exactly once
Affine row:    aff {â„“â‚ : Ï„â‚ ; â„“â‚‚ : Ï„â‚‚}  -- Each field used at most once
Relevant row:  rel {â„“â‚ : Ï„â‚ ; â„“â‚‚ : Ï„â‚‚}  -- Each field used at least once

-- Row-polymorphic linear function
swap : âˆ€Î± Î² Ï. lin {x : Î± ; y : Î² ; Ï} â†’ lin {x : Î² ; y : Î± ; Ï}
```

---

## 10. Security Applications

### 10.1 Row Types for Capabilities

```
Capability rows for access control:

type FileOps = {read : ReadCap ; write : WriteCap ; exec : ExecCap}

-- Function requiring specific capabilities
readFile : âˆ€Ï. {read : ReadCap | Ï} â†’ Path â†’ String

-- Capability attenuation via row restriction
attenuate : {read : ReadCap ; write : WriteCap | Ï} 
          â†’ {read : ReadCap | Ï}
```

### 10.2 Information Flow with Row Types

```
Security label rows:

type SecurityContext = {
  clearance : Level ;
  compartments : Set Compartment ;
  integrity : IntegrityLevel
}

-- Row polymorphic security check
canAccess : âˆ€Ï. {clearance : Level | Ï} 
          â†’ {classification : Level | Ï'} 
          â†’ Bool
```

### 10.3 Effect Rows for Security

```
Security effects as row types:

<audit : AUDIT, crypto : CRYPTO | e>

-- Function with security effect requirements
signData : âˆ€e. Data â†’ <crypto : CRYPTO | e> Signature

-- Effect masking for sandboxing
sandbox : <network : NETWORK | e> a â†’ <e> (Option a)
```

### 10.4 Protocol State via Row Types

```
Protocol state machine:

type ConnState = {
  connected : Bool ;
  authenticated : Bool ;
  encrypted : Bool
}

-- State-dependent operations
sendSecure : {connected : True ; authenticated : True ; encrypted : True | Ï} 
           â†’ Data â†’ IO ()

-- State transitions
authenticate : {connected : True ; authenticated : Bool | Ï}
             â†’ Credentials
             â†’ {connected : True ; authenticated : True | Ï}
```

### 10.5 Taint Tracking with Rows

```
Taint sources as row labels:

type TaintRow = {
  user_input : Tainted ;
  network : Tainted ;
  file_system : Tainted ;
  sanitized : Clean
}

-- Taint-aware string concatenation
concat : âˆ€Ïâ‚ Ïâ‚‚. String<Ïâ‚> â†’ String<Ïâ‚‚> â†’ String<Ïâ‚ âˆª Ïâ‚‚>

-- Sanitization removes taint
sanitize : String<{user_input : Tainted | Ï}> 
         â†’ String<{user_input : Clean | Ï}>
```

---

## 11. Implementation Strategies

### 11.1 Row Representation

**Option 1: Sorted List**
```
Row = [(Label, Type)]  -- Sorted by label

lookup : Label â†’ Row â†’ Option Type
extend : Label â†’ Type â†’ Row â†’ Row  -- O(n) insertion
```

**Option 2: Map/Dictionary**
```
Row = Map Label Type

lookup : Label â†’ Row â†’ Option Type  -- O(log n)
extend : Label â†’ Type â†’ Row â†’ Row   -- O(log n)
```

**Option 3: Hash Consing**
```
RowNode = Empty
        | Extend Label Type RowRef

-- Structural sharing, O(1) equality
```

### 11.2 Row Unification Algorithm

```
unify_row(r1, r2):
  match (r1, r2):
    case (RowVar(v1), r2):
      if occurs(v1, r2) then fail
      else substitute(v1, r2)
    
    case (r1, RowVar(v2)):
      unify_row(r2, r1)
    
    case (Empty, Empty):
      success
    
    case (Extend(l1, t1, rest1), r2):
      (t2, rest2) = extract(l1, r2)  -- Find l1 in r2
      unify(t1, t2)
      unify_row(rest1, rest2)
    
    case (Empty, Extend(_, _, _)):
      fail  -- Different row lengths
```

### 11.3 Row Label Extraction

```
extract(label, row):
  match row:
    case Empty:
      fail  -- Label not found
    
    case Extend(l, t, rest) when l == label:
      return (t, rest)
    
    case Extend(l, t, rest):
      (t2, rest2) = extract(label, rest)
      return (t2, Extend(l, t, rest2))
    
    case RowVar(v):
      -- Create fresh variables
      fresh_t = fresh_type_var()
      fresh_rest = fresh_row_var()
      substitute(v, Extend(label, fresh_t, fresh_rest))
      return (fresh_t, fresh_rest)
```

### 11.4 Row Constraint Solving

```
Constraint types:

RowEq(r1, r2)           -- r1 = r2
Lacks(r, label)         -- label âˆ‰ r
Has(r, label, type)     -- label : type âˆˆ r

Solver:
  solve([]):
    success
  
  solve(RowEq(r1, r2) :: rest):
    subst = unify_row(r1, r2)
    solve(apply_subst(subst, rest))
  
  solve(Lacks(RowVar(v), l) :: rest):
    -- Defer constraint until v is instantiated
    solve(rest ++ [Lacks(RowVar(v), l)])
  
  solve(Lacks(Extend(l', t, r), l) :: rest) when l' == l:
    fail
  
  solve(Lacks(Extend(l', t, r), l) :: rest) when l' != l:
    solve(Lacks(r, l) :: rest)
```

### 11.5 Compilation of Row Operations

```
Record field access compilation:

Source:
  r.x

Compilation (known offset):
  load r[offset_of_x]

Compilation (row-polymorphic):
  -- Pass dictionary with field offsets
  let dict = row_dictionary(typeof(r))
  load r[dict.x]

Dictionary structure:
  struct RowDict {
    x_offset : Int
    y_offset : Int
    ...
  }
```

---

## 12. TERAS Product Applications

### 12.1 MENARA (Mobile Security)

```
Permission rows for mobile apps:

type AppPermissions = {
  camera : PermLevel ;
  location : PermLevel ;
  contacts : PermLevel ;
  storage : PermLevel
}

-- Permission-polymorphic API
capturePhoto : âˆ€Ï. {camera : Granted | Ï} â†’ PhotoResult

-- Permission checking
checkPermission : âˆ€â„“ Ï. Label â„“ â†’ {â„“ : PermLevel | Ï} â†’ Bool

-- Dynamic permission request
requestPermission : âˆ€â„“ Ï. Label â„“ 
                  â†’ {â„“ : Denied | Ï} 
                  â†’ IO {â„“ : PermLevel | Ï}
```

### 12.2 GAPURA (Web Application Firewall)

```
HTTP request/response rows:

type HttpRequest = {
  method : Method ;
  path : Path ;
  headers : Headers ;
  body : Body ;
  cookies : Cookies
}

-- Row-polymorphic header access
getHeader : âˆ€Ï. HeaderName â†’ {headers : Headers | Ï} â†’ Option String

-- Request transformation
addSecurityHeaders : âˆ€Ï. {headers : Headers | Ï} 
                   â†’ {headers : Headers | Ï}

-- Taint tracking per field
type TaintedRequest = {
  method : Clean Method ;
  path : Tainted Path ;        -- User-controlled
  headers : Tainted Headers ;  -- User-controlled
  body : Tainted Body          -- User-controlled
}
```

### 12.3 ZIRAH (Endpoint Detection)

```
Process state rows:

type ProcessState = {
  pid : PID ;
  ppid : PID ;
  user : UID ;
  memory_map : MemMap ;
  open_files : FileSet ;
  network_sockets : SocketSet ;
  integrity : IntegrityLevel
}

-- Row-polymorphic process inspection
getProcessField : âˆ€â„“ Î± Ï. Label â„“ â†’ {â„“ : Î± | Ï} â†’ Î±

-- Behavioral pattern matching
type BehaviorPattern = {
  file_access : Pattern ;
  network_activity : Pattern ;
  memory_operations : Pattern
}

matchBehavior : âˆ€Ï. {file_access : Pattern | Ï} 
              â†’ ProcessState â†’ MatchResult
```

### 12.4 BENTENG (Identity Verification)

```
Identity attribute rows:

type IdentityDocument = {
  full_name : String ;
  date_of_birth : Date ;
  nationality : Country ;
  document_number : DocNum ;
  expiry_date : Date ;
  biometric_data : BiometricTemplate
}

-- Attribute extraction (row-polymorphic)
extractAttribute : âˆ€â„“ Î± Ï. Label â„“ â†’ {â„“ : Î± | Ï} â†’ Î±

-- Verification result rows
type VerificationResult = {
  face_match : Confidence ;
  liveness : LivenessScore ;
  document_authenticity : AuthScore ;
  name_match : MatchScore
}

-- Aggregate verification
aggregate : âˆ€Ï. {face_match : Confidence ; liveness : LivenessScore | Ï}
          â†’ OverallScore
```

### 12.5 SANDI (Digital Signatures)

```
Cryptographic operation rows:

type SigningContext = {
  algorithm : Algorithm ;
  key_id : KeyID ;
  certificate : Certificate ;
  timestamp_authority : TSA
}

-- Row-polymorphic signing
sign : âˆ€Ï. {algorithm : Algorithm ; key_id : KeyID | Ï} 
     â†’ Data â†’ Signature

-- Verification context
type VerifyContext = {
  certificate : Certificate ;
  revocation_status : RevocationStatus ;
  trust_chain : TrustChain ;
  timestamp : Timestamp
}

verify : âˆ€Ï. {certificate : Certificate ; revocation_status : Valid | Ï}
       â†’ Data â†’ Signature â†’ VerifyResult
```

---

## 13. Integration with Prior Sessions

### 13.1 With Linear Types (A-04)

```
Linear row fields:

type LinearRow = {
  lin resource : Resource ;  -- Must be used exactly once
  normal_field : Int         -- Regular field
}

-- Consuming linear field
useResource : lin {resource : Resource | Ï} â†’ {Ï}

-- Row-polymorphic linear projection
extractLin : âˆ€â„“ Î± Ï. lin {â„“ : Î± | Ï} â†’ (lin Î±, {Ï})
```

### 13.2 With Effect Systems (A-05, A-11)

```
Effect rows compose with record rows:

type EffectfulRecord<e, r> = <e> {r}

-- Access field with effects
getEffectful : âˆ€â„“ Î± r e. Label â„“ â†’ <e> {â„“ : Î± | r} â†’ <e> Î±

-- Effectful record update
updateEffectful : âˆ€â„“ Î± r e. Label â„“ â†’ Î± â†’ <e> {â„“ : Î± | r} â†’ <e> {â„“ : Î± | r}
```

### 13.3 With Refinement Types (A-08)

```
Refined row types:

type BoundedRecord = {
  x : {v : Int | v >= 0} ;
  y : {v : Int | v >= 0} ;
  z : {v : Int | v == x + y}  -- Refinement over other fields
}

-- Row-polymorphic refinement
type PositiveRow Ï = âˆ€â„“ âˆˆ Ï. Ï.â„“ : {v : Int | v > 0}
```

### 13.4 With Region Types (A-12)

```
Region-annotated rows:

type RegionRecord<Ï_mem> = {
  data : Buffer at Ï_mem ;
  metadata : Info at Ï_mem
}

-- Row-polymorphic region access
accessInRegion : âˆ€r Ï_mem. Cap<Ï_mem> â†’ {r} at Ï_mem â†’ IO {r}
```

### 13.5 With Ownership Types (A-13)

```
Ownership-annotated row fields:

type OwnedRecord = {
  owned handle : FileHandle ;      -- Owned, will be dropped
  borrowed ref : &FileHandle ;     -- Borrowed, won't be dropped
}

-- Row-polymorphic ownership transfer
transferField : âˆ€â„“ Î± Ï. owned {â„“ : Î± | Ï} â†’ (owned Î±, {Ï})
```

### 13.6 With Capability Types (A-14)

```
Capability rows:

type CapabilitySet = {
  file_read : Cap<FileRead> ;
  file_write : Cap<FileWrite> ;
  network : Cap<Network>
}

-- Capability row attenuation
attenuate : âˆ€Ï. {file_write : Cap<FileWrite> | Ï} 
          â†’ {file_read : Cap<FileRead> | Ï}

-- Capability-polymorphic operation
withCap : âˆ€â„“ c Ï. {â„“ : Cap<c> | Ï} â†’ (Cap<c> â†’ IO a) â†’ IO a
```

### 13.7 With Staged Types (A-15)

```
Staged row construction:

-- Generate record type at compile time
generateFields : Code [FieldSpec] â†’ Code (Row Type)

-- Splice computed row type
type DynamicRecord = $$(generateFields fieldSpecs)

-- Row operations in staged code
stagedProject : âˆ€â„“ Î± Ï. Label â„“ â†’ Code {â„“ : Î± | Ï} â†’ Code Î±
```

---

## 14. Bibliography

### Primary Sources

1. **Wand, M.** (1987). "Complete Type Inference for Simple Objects." LICS.
   - Original row variable formulation

2. **Wand, M.** (1991). "Type Inference for Record Concatenation and Multiple Inheritance." Information and Computation.
   - Extended treatment with concatenation

3. **RÃ©my, D.** (1989). "Typechecking Records and Variants in a Natural Extension of ML." POPL.
   - Presence/absence flags

4. **RÃ©my, D.** (1994). "Type Inference for Records in a Natural Extension of ML." Theoretical Aspects of Object-Oriented Programming.
   - Comprehensive ML extension

5. **Ohori, A.** (1995). "A Polymorphic Record Calculus and Its Compilation." TOPLAS.
   - Compilation strategies

### OCaml and Variants

6. **Garrigue, J.** (1998). "Programming with Polymorphic Variants." ML Workshop.
   - OCaml polymorphic variants

7. **Garrigue, J.** (2000). "Code Reuse Through Polymorphic Variants." FOSE.
   - Practical applications

### Modern Systems

8. **Leijen, D.** (2005). "Extensible Records with Scoped Labels." Trends in Functional Programming.
   - Duplicate labels

9. **Lindley, S. and Cheney, J.** (2012). "Row-Based Effect Types for Database Integration." TLDI.
   - Effect rows

10. **HillerstrÃ¶m, D. and Lindley, S.** (2016). "Liberating Effects with Rows and Handlers." TyDe.
    - Row-typed effect handlers

### Implementation

11. **Morris, J.G. and Jones, M.P.** (2019). "Instance Chains: Type Class Programming Without Overlapping Instances." ICFP.
    - Row constraints

12. **Chlipala, A.** (2015). "Ur/Web: A Simple Model for Programming the Web." POPL.
    - Row types for web

### TypeScript

13. **Bierman, G., Abadi, M., and Torgersen, M.** (2014). "Understanding TypeScript." ECOOP.
    - Structural typing foundation

14. **Microsoft.** (2016-present). "TypeScript Handbook: Mapped Types."
    - https://www.typescriptlang.org/docs/handbook/2/mapped-types.html

---

## Document Metadata

```
â•”â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•—
â•‘  Document ID: TERAS-RESEARCH-A16-SURVEY                                      â•‘
â•‘  Version: 1.0.0                                                              â•‘
â•‘  Status: COMPLETE                                                            â•‘
â•‘  Classification: TERAS Internal - Research                                   â•‘
â•‘                                                                              â•‘
â•‘  Research Coverage:                                                          â•‘
â•‘  â€¢ Wand's Row Polymorphism: COMPREHENSIVE                                    â•‘
â•‘  â€¢ RÃ©my's ML Extension: COMPREHENSIVE                                        â•‘
â•‘  â€¢ OCaml Polymorphic Variants: COMPREHENSIVE                                 â•‘
â•‘  â€¢ PureScript Row Types: COMPREHENSIVE                                       â•‘
â•‘  â€¢ Extensible Records: DETAILED                                              â•‘
â•‘  â€¢ Row-Based Effects: COMPREHENSIVE                                          â•‘
â•‘  â€¢ TypeScript Mapped Types: DETAILED                                         â•‘
â•‘  â€¢ Advanced Theories: COMPREHENSIVE                                          â•‘
â•‘  â€¢ Security Applications: DETAILED                                           â•‘
â•‘  â€¢ TERAS Integration: COMPLETE                                               â•‘
â•‘                                                                              â•‘
â•‘  Next: A-16 Comparison Document                                              â•‘
â•šâ•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•
```
