# TERAS-LANG Research Track
# Session A-16: Row Types and Row Polymorphism
# Document Type: Comprehensive Survey

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  RESEARCH SESSION A-16: ROW TYPES AND ROW POLYMORPHISM                       ║
║                                                                               ║
║  Date: 2026-01-03                                                            ║
║  Domain: A (Type Theory Foundations)                                         ║
║  Session: 16 of 20                                                           ║
║  Predecessor: A-15 (Staged Types and Multi-Stage Programming)                ║
║  Successor: A-17 (Higher-Kinded Types)                                       ║
║                                                                              ║
║  Research Coverage:                                                          ║
║  • Wand's Row Polymorphism (1987-1991)                                       ║
║  • Rémy's ML Record Extension (1989-1994)                                    ║
║  • OCaml Polymorphic Variants                                                ║
║  • PureScript Row Types                                                      ║
║  • Extensible Records (Elm, Ur/Web)                                          ║
║  • TypeScript Mapped Types                                                   ║
║  • Row-Based Effect Systems                                                  ║
║  • Scoped Labels and Qualified Types                                         ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

## Table of Contents

1. [Foundations and Historical Context](#1-foundations-and-historical-context)
2. [Wand's Row Polymorphism](#2-wands-row-polymorphism)
3. [Rémy's ML Extension](#3-rémys-ml-extension)
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
let get_x r = r.x  (* Type: {x: α | ρ} → α *)
```

### 1.2 The Variance Challenge

Records and variants have opposite variance:

| Construct | Subtyping Direction | Covariance |
|-----------|---------------------|------------|
| Records | More fields ≤ Fewer fields | Width subtyping (subsumption) |
| Variants | Fewer cases ≤ More cases | Opposite to records |

This duality suggests a unified treatment via row types.

### 1.3 Historical Development

```
Timeline of Row Polymorphism:
                                                                    
1987 ─┬─ Wand: Row Variables (POPL)                               
      │  First formal treatment of record polymorphism             
      │                                                            
1989 ─┼─ Rémy: Record Extension (POPL)                            
      │  Presence/absence flags, ML-style inference                
      │                                                            
1994 ─┼─ Rémy: Typing Record Concatenation (POPL)                 
      │  Safe record concatenation with row types                  
      │                                                            
1996 ─┼─ OCaml Polymorphic Variants                               
      │  Row types for sum types (variants)                        
      │                                                            
2006 ─┼─ Leijen: Extensible Records with Scoped Labels            
      │  Duplicate labels, scoped resolution                       
      │                                                            
2012 ─┼─ PureScript                                               
      │  First-class row polymorphism in production                
      │                                                            
2016 ─┼─ TypeScript Mapped Types                                  
      │  Practical row-like manipulation                           
      │                                                            
2019 ─┴─ Row Polymorphism in Effect Systems                       
        Koka, Frank, Eff                                           
```

---

## 2. Wand's Row Polymorphism

### 2.1 Core Insight (1987)

Mitchell Wand introduced row variables to type record operations polymorphically.

**Key Type Forms**:
```
Row ::= ∅                    (* Empty row *)
     |  (ℓ : τ ; ρ)         (* Label extension *)
     |  ρ                    (* Row variable *)

Record ::= {ρ}               (* Record from row *)
```

**Row Variable**: ρ ranges over sets of labeled types.

### 2.2 Type Rules

**Record Construction**:
```
Γ ⊢ e : τ    Γ ⊢ r : {ρ}    ℓ ∉ ρ
────────────────────────────────────
Γ ⊢ {ℓ = e ; r} : {ℓ : τ ; ρ}
```

**Field Selection**:
```
Γ ⊢ r : {ℓ : τ ; ρ}
────────────────────
Γ ⊢ r.ℓ : τ
```

**Polymorphic Projection**:
```
get_x : ∀α ρ. {x : α ; ρ} → α
get_x = λr. r.x
```

### 2.3 Example Derivation

```
get_x {x = 1; y = 2; z = 3}
│
├─ r : {x : int ; y : int ; z : int ; ∅}
│
├─ Unify: {x : α ; ρ} ~ {x : int ; y : int ; z : int ; ∅}
│  α := int
│  ρ := (y : int ; z : int ; ∅)
│
└─ Result: int
```

### 2.4 Limitations of Original Formulation

1. **Row commutativity**: Order-dependent (ℓ₁ : τ₁ ; ℓ₂ : τ₂) ≠ (ℓ₂ : τ₂ ; ℓ₁ : τ₁)
2. **No duplicate labels**: Each label appears at most once
3. **Lacks row constraints**: Cannot express "ℓ ∉ ρ" in types directly

---

## 3. Rémy's ML Extension

### 3.1 Presence/Absence Flags (1989)

Didier Rémy extended row types with explicit presence annotations:

```
Flag ::= Pre(τ)    (* Field present with type τ *)
      |  Abs       (* Field absent *)

Row ::= ∅
     |  (ℓ : Flag ; ρ)
     |  ρ

Record ::= {| ρ |}
```

### 3.2 The Key Innovation

Every label has a status (present or absent) for every row:

```
{| x : Pre(int) ; y : Pre(string) ; z : Abs ; ρ |}
```

This row has `x` and `y` present, `z` absent, and ρ determines remaining labels.

### 3.3 Type Rules with Flags

**Field Access**:
```
Γ ⊢ r : {| ℓ : Pre(τ) ; ρ |}
─────────────────────────────
Γ ⊢ r.ℓ : τ
```

**Record Extension**:
```
Γ ⊢ e : τ    Γ ⊢ r : {| ℓ : Abs ; ρ |}
────────────────────────────────────────
Γ ⊢ {ℓ = e ; r} : {| ℓ : Pre(τ) ; ρ |}
```

**Field Removal**:
```
Γ ⊢ r : {| ℓ : Pre(τ) ; ρ |}
─────────────────────────────
Γ ⊢ r \ ℓ : {| ℓ : Abs ; ρ |}
```

### 3.4 Row Unification

Rémy's algorithm handles row unification with flags:

```
Unify((ℓ : f₁ ; ρ₁), (ℓ : f₂ ; ρ₂)) =
  Unify(f₁, f₂) ∘ Unify(ρ₁, ρ₂)

Unify(Pre(τ₁), Pre(τ₂)) = Unify(τ₁, τ₂)
Unify(Abs, Abs) = id
Unify(Pre(_), Abs) = FAIL
Unify(ρ, row) = [ρ ↦ row]  (* Row variable substitution *)
```

### 3.5 Record Concatenation (1994)

Rémy solved safe record concatenation:

```
concat : ∀ρ₁ ρ₂ ρ₃. 
         {| ρ₁ |} → {| ρ₂ |} → {| ρ₃ |}
         where ρ₁ ⊕ ρ₂ = ρ₃
```

The constraint `ρ₁ ⊕ ρ₂ = ρ₃` ensures:
- Labels in ρ₁ and ρ₂ are disjoint
- ρ₃ contains exactly labels from both

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
-- Int ≁ String
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
-- Requires: "name" ::: String ∈ r
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
  val get : unit → int
  val put : int → unit
end

let state_handler = handler
  | val x → (fun _ → x)
  | get () k → (fun s → k s s)
  | put s k → (fun _ → k () s)
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
Row ::= ∅
     |  (ℓ : τ ; ρ)
     |  ρ

-- Duplicate labels allowed
{x : int ; x : string ; y : bool}

-- Selection with scoping
r.x    -- Gets outermost x (int)
(r\x).x -- Gets next x (string) after removing first
```

### 9.2 Qualified Types for Rows

```
Constrained row polymorphism:

lacks(ρ, ℓ)     -- Row ρ doesn't contain label ℓ
has(ρ, ℓ : τ)   -- Row ρ contains label ℓ with type τ

Example:
extend : ∀α ρ. lacks(ρ, ℓ) ⇒ α → {ρ} → {ℓ : α ; ρ}
```

### 9.3 First-Class Labels

Some systems make labels first-class:

```
Label : String → LabelType

get : ∀ℓ α ρ. Label ℓ → {ℓ : α ; ρ} → α

-- Dynamic label access
let lbl = #name
get lbl {name = "Alice", age = 30}  -- "Alice"
```

### 9.4 Row Kinds

Higher-kinded row polymorphism:

```
kind Row = * → *

-- Functor over rows
class RowFunctor f where
  rowMap : ∀ρ. (∀ℓ α. α → f α) → {ρ} → {ρ}[f]

-- Apply type constructor to all fields
type Optionalized r = {r}[Option]
-- {x : int ; y : string} becomes {x : Option int ; y : Option string}
```

### 9.5 Substructural Row Types

Combining rows with linearity:

```
Linear row:    lin {ℓ₁ : τ₁ ; ℓ₂ : τ₂}  -- Each field used exactly once
Affine row:    aff {ℓ₁ : τ₁ ; ℓ₂ : τ₂}  -- Each field used at most once
Relevant row:  rel {ℓ₁ : τ₁ ; ℓ₂ : τ₂}  -- Each field used at least once

-- Row-polymorphic linear function
swap : ∀α β ρ. lin {x : α ; y : β ; ρ} → lin {x : β ; y : α ; ρ}
```

---

## 10. Security Applications

### 10.1 Row Types for Capabilities

```
Capability rows for access control:

type FileOps = {read : ReadCap ; write : WriteCap ; exec : ExecCap}

-- Function requiring specific capabilities
readFile : ∀ρ. {read : ReadCap | ρ} → Path → String

-- Capability attenuation via row restriction
attenuate : {read : ReadCap ; write : WriteCap | ρ} 
          → {read : ReadCap | ρ}
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
canAccess : ∀ρ. {clearance : Level | ρ} 
          → {classification : Level | ρ'} 
          → Bool
```

### 10.3 Effect Rows for Security

```
Security effects as row types:

<audit : AUDIT, crypto : CRYPTO | e>

-- Function with security effect requirements
signData : ∀e. Data → <crypto : CRYPTO | e> Signature

-- Effect masking for sandboxing
sandbox : <network : NETWORK | e> a → <e> (Option a)
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
sendSecure : {connected : True ; authenticated : True ; encrypted : True | ρ} 
           → Data → IO ()

-- State transitions
authenticate : {connected : True ; authenticated : Bool | ρ}
             → Credentials
             → {connected : True ; authenticated : True | ρ}
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
concat : ∀ρ₁ ρ₂. String<ρ₁> → String<ρ₂> → String<ρ₁ ∪ ρ₂>

-- Sanitization removes taint
sanitize : String<{user_input : Tainted | ρ}> 
         → String<{user_input : Clean | ρ}>
```

---

## 11. Implementation Strategies

### 11.1 Row Representation

**Option 1: Sorted List**
```
Row = [(Label, Type)]  -- Sorted by label

lookup : Label → Row → Option Type
extend : Label → Type → Row → Row  -- O(n) insertion
```

**Option 2: Map/Dictionary**
```
Row = Map Label Type

lookup : Label → Row → Option Type  -- O(log n)
extend : Label → Type → Row → Row   -- O(log n)
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
Lacks(r, label)         -- label ∉ r
Has(r, label, type)     -- label : type ∈ r

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
capturePhoto : ∀ρ. {camera : Granted | ρ} → PhotoResult

-- Permission checking
checkPermission : ∀ℓ ρ. Label ℓ → {ℓ : PermLevel | ρ} → Bool

-- Dynamic permission request
requestPermission : ∀ℓ ρ. Label ℓ 
                  → {ℓ : Denied | ρ} 
                  → IO {ℓ : PermLevel | ρ}
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
getHeader : ∀ρ. HeaderName → {headers : Headers | ρ} → Option String

-- Request transformation
addSecurityHeaders : ∀ρ. {headers : Headers | ρ} 
                   → {headers : Headers | ρ}

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
getProcessField : ∀ℓ α ρ. Label ℓ → {ℓ : α | ρ} → α

-- Behavioral pattern matching
type BehaviorPattern = {
  file_access : Pattern ;
  network_activity : Pattern ;
  memory_operations : Pattern
}

matchBehavior : ∀ρ. {file_access : Pattern | ρ} 
              → ProcessState → MatchResult
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
extractAttribute : ∀ℓ α ρ. Label ℓ → {ℓ : α | ρ} → α

-- Verification result rows
type VerificationResult = {
  face_match : Confidence ;
  liveness : LivenessScore ;
  document_authenticity : AuthScore ;
  name_match : MatchScore
}

-- Aggregate verification
aggregate : ∀ρ. {face_match : Confidence ; liveness : LivenessScore | ρ}
          → OverallScore
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
sign : ∀ρ. {algorithm : Algorithm ; key_id : KeyID | ρ} 
     → Data → Signature

-- Verification context
type VerifyContext = {
  certificate : Certificate ;
  revocation_status : RevocationStatus ;
  trust_chain : TrustChain ;
  timestamp : Timestamp
}

verify : ∀ρ. {certificate : Certificate ; revocation_status : Valid | ρ}
       → Data → Signature → VerifyResult
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
useResource : lin {resource : Resource | ρ} → {ρ}

-- Row-polymorphic linear projection
extractLin : ∀ℓ α ρ. lin {ℓ : α | ρ} → (lin α, {ρ})
```

### 13.2 With Effect Systems (A-05, A-11)

```
Effect rows compose with record rows:

type EffectfulRecord<e, r> = <e> {r}

-- Access field with effects
getEffectful : ∀ℓ α r e. Label ℓ → <e> {ℓ : α | r} → <e> α

-- Effectful record update
updateEffectful : ∀ℓ α r e. Label ℓ → α → <e> {ℓ : α | r} → <e> {ℓ : α | r}
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
type PositiveRow ρ = ∀ℓ ∈ ρ. ρ.ℓ : {v : Int | v > 0}
```

### 13.4 With Region Types (A-12)

```
Region-annotated rows:

type RegionRecord<ρ_mem> = {
  data : Buffer at ρ_mem ;
  metadata : Info at ρ_mem
}

-- Row-polymorphic region access
accessInRegion : ∀r ρ_mem. Cap<ρ_mem> → {r} at ρ_mem → IO {r}
```

### 13.5 With Ownership Types (A-13)

```
Ownership-annotated row fields:

type OwnedRecord = {
  owned handle : FileHandle ;      -- Owned, will be dropped
  borrowed ref : &FileHandle ;     -- Borrowed, won't be dropped
}

-- Row-polymorphic ownership transfer
transferField : ∀ℓ α ρ. owned {ℓ : α | ρ} → (owned α, {ρ})
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
attenuate : ∀ρ. {file_write : Cap<FileWrite> | ρ} 
          → {file_read : Cap<FileRead> | ρ}

-- Capability-polymorphic operation
withCap : ∀ℓ c ρ. {ℓ : Cap<c> | ρ} → (Cap<c> → IO a) → IO a
```

### 13.7 With Staged Types (A-15)

```
Staged row construction:

-- Generate record type at compile time
generateFields : Code [FieldSpec] → Code (Row Type)

-- Splice computed row type
type DynamicRecord = $$(generateFields fieldSpecs)

-- Row operations in staged code
stagedProject : ∀ℓ α ρ. Label ℓ → Code {ℓ : α | ρ} → Code α
```

---

## 14. Bibliography

### Primary Sources

1. **Wand, M.** (1987). "Complete Type Inference for Simple Objects." LICS.
   - Original row variable formulation

2. **Wand, M.** (1991). "Type Inference for Record Concatenation and Multiple Inheritance." Information and Computation.
   - Extended treatment with concatenation

3. **Rémy, D.** (1989). "Typechecking Records and Variants in a Natural Extension of ML." POPL.
   - Presence/absence flags

4. **Rémy, D.** (1994). "Type Inference for Records in a Natural Extension of ML." Theoretical Aspects of Object-Oriented Programming.
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

10. **Hillerström, D. and Lindley, S.** (2016). "Liberating Effects with Rows and Handlers." TyDe.
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
╔══════════════════════════════════════════════════════════════════════════════╗
║  Document ID: TERAS-RESEARCH-A16-SURVEY                                      ║
║  Version: 1.0.0                                                              ║
║  Status: COMPLETE                                                            ║
║  Classification: TERAS Internal - Research                                   ║
║                                                                              ║
║  Research Coverage:                                                          ║
║  • Wand's Row Polymorphism: COMPREHENSIVE                                    ║
║  • Rémy's ML Extension: COMPREHENSIVE                                        ║
║  • OCaml Polymorphic Variants: COMPREHENSIVE                                 ║
║  • PureScript Row Types: COMPREHENSIVE                                       ║
║  • Extensible Records: DETAILED                                              ║
║  • Row-Based Effects: COMPREHENSIVE                                          ║
║  • TypeScript Mapped Types: DETAILED                                         ║
║  • Advanced Theories: COMPREHENSIVE                                          ║
║  • Security Applications: DETAILED                                           ║
║  • TERAS Integration: COMPLETE                                               ║
║                                                                              ║
║  Next: A-16 Comparison Document                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```
