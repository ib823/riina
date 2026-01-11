# RESEARCH_A05_EFFECT_SYSTEMS_SURVEY.md

## TERAS Research Track: Session A-05
## Effect Systems and Monads - Exhaustive Survey

**Document Version:** 1.0.0
**Created:** 2026-01-03
**Session:** A-05 of 47
**Track:** Foundational Type Theory (Sessions A-01 through A-08)

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Historical Development](#2-historical-development)
3. [Moggi's Computational Monads](#3-moggis-computational-monads)
4. [Monad Fundamentals](#4-monad-fundamentals)
5. [Effect Systems](#5-effect-systems)
6. [Algebraic Effects and Handlers](#6-algebraic-effects-and-handlers)
7. [Row Polymorphism for Effects](#7-row-polymorphism-for-effects)
8. [Delimited Continuations](#8-delimited-continuations)
9. [Language Implementations](#9-language-implementations)
10. [Integration with Type Systems](#10-integration-with-type-systems)
11. [Security Applications](#11-security-applications)
12. [TERAS Relevance Analysis](#12-teras-relevance-analysis)
13. [Open Problems and Future Directions](#13-open-problems-and-future-directions)
14. [Bibliography](#14-bibliography)

---

## 1. Executive Summary

Effect systems provide a principled approach to tracking and reasoning about computational effects in programming languages. This survey covers the theoretical foundations from Moggi's monadic semantics through modern algebraic effects and handlers, with particular emphasis on applications to security verification and TERAS-LANG integration.

### Key Findings

1. **Monadic Foundation**: Moggi's 1989/1991 work established monads as the categorical semantics for computational effects, enabling uniform treatment of state, exceptions, continuations, I/O, and nondeterminism.

2. **Algebraic Effects**: Plotkin and Power's algebraic effects (2001-2009) characterize monads through operations and equations, leading to Plotkin and Pretnar's effect handlers which provide modular, composable effect implementation.

3. **Row Polymorphism**: Koka and similar languages demonstrate that row-polymorphic effect types enable effect polymorphism without complex subtyping constraints, with decidable inference.

4. **Practical Systems**: F* demonstrates successful integration of effects with dependent types and SMT-based verification, validating cryptographic implementations (HACL*, miTLS, Project Everest).

5. **TERAS Integration**: Effect systems are essential for tracking security-relevant effects (I/O, state, exceptions, cryptographic operations) and ensuring effect-safe composition of security components.

---

## 2. Historical Development

### 2.1 Pre-Monadic Era

**Denotational Semantics (1970s-1980s):**
- Scott-Strachey semantics: programs as mathematical functions
- Challenge: modeling effects (state, I/O) in purely functional framework
- Ad-hoc solutions: state-passing transformations, continuation semantics

**Effect Annotations (Lucassen & Gifford, 1988):**
- First effect system for polymorphic languages
- Track read/write effects on memory regions
- Effect polymorphism for generic code
- Typing judgment: Î“ âŠ¢ e : Ï„ ! Îµ (expression e has type Ï„ with effects Îµ)

### 2.2 Moggi's Revolution (1989-1991)

**"Computational Lambda-Calculus and Monads" (LICS 1989):**
- Key insight: distinguish values from computations
- Computations carry "potential for effects"
- Categorical semantics via monads

**"Notions of Computation and Monads" (Information and Computation, 1991):**
- Full development of monadic metalanguage
- Examples: partiality, nondeterminism, state, exceptions, continuations
- Kleisli category as semantic framework

**Impact:**
- Foundation for Haskell's IO monad
- Inspired Wadler's monads for functional programming
- Established categorical approach to effects

### 2.3 Algebraic Effects Era (2001-present)

**Plotkin & Power (2001-2003):**
- "Notions of Computation Determine Monads"
- Algebraic operations + equations characterize many monads
- Operations: primitive effects (lookup, update, throw, etc.)
- Equations: laws effects must satisfy

**Plotkin & Pretnar (2009):**
- "Handlers of Algebraic Effects"
- Effect handlers as first-class control construct
- Modular, composable effect implementation
- Foundation for Eff, Koka, OCaml 5.0, etc.

### 2.4 Modern Developments (2014-present)

**Language Implementations:**
- Koka (Microsoft Research): Row-polymorphic effects
- Eff (Bauer & Pretnar): Research language for handlers
- OCaml 5.0: Effect handlers for concurrency
- Unison: Effects as "abilities"
- Scala 3: Experimental effect support

**Integration with Verification:**
- F*: Dependent types + effects + SMT
- Liquid Effects: Refinement types + effects
- Project Everest: Verified cryptography

---

## 3. Moggi's Computational Monads

### 3.1 The Problem

Classical denotational semantics identifies programs with functions:
```
âŸ¦Ï„â‚ â†’ Ï„â‚‚âŸ§ = âŸ¦Ï„â‚âŸ§ â†’ âŸ¦Ï„â‚‚âŸ§
```

This creates problems:
- **Partiality**: Not all computations terminate
- **State**: Functions don't model mutable state
- **Exceptions**: No way to represent failure
- **I/O**: Side effects have no denotation
- **Nondeterminism**: Functions are deterministic

### 3.2 Moggi's Solution

**Key Insight:** Distinguish values from computations.

```
Values:      A, B, ...       (data)
Computations: TA             (computations returning A)
```

**Interpretation:**
- TA is the type of "computations that may perform effects and produce a value of type A"
- T is a type constructor (functor) with additional structure: a monad

### 3.3 The Computational Lambda-Calculus (Î»c)

**Syntax:**
```
Values:       V ::= x | Î»x.M | ...
Computations: M ::= V | let x â‡ M in N | ...
```

**Key Construct:** let x â‡ M in N
- "Execute M, bind result to x, then execute N"
- Sequences computations, threading effects

**Types:**
```
Ï„ ::= Î± | Ï„â‚ â†’ Ï„â‚‚ | TÏ„

Î“ âŠ¢ M : TÏ„    (computation M produces Ï„)
Î“ âŠ¢ V : Ï„     (value V has type Ï„)
```

### 3.4 Examples of Monads for Effects

**Partiality (Lift Monad):**
```
TA = A + âŠ¥ = A_âŠ¥
return a = inl a
bind m f = case m of inl a â†’ f a | âŠ¥ â†’ âŠ¥
```

**Exceptions:**
```
TA = A + E         (E is exception type)
return a = inl a
bind m f = case m of inl a â†’ f a | inr e â†’ inr e
throw e = inr e
```

**State:**
```
TA = S â†’ (A Ã— S)   (S is state type)
return a = Î»s. (a, s)
bind m f = Î»s. let (a, s') = m s in f a s'
get = Î»s. (s, s)
put s' = Î»s. ((), s')
```

**Nondeterminism:**
```
TA = P(A)          (powerset)
return a = {a}
bind m f = âˆª{f a | a âˆˆ m}
choose = {true, false}
```

**Continuations:**
```
TA = (A â†’ R) â†’ R   (R is answer type)
return a = Î»k. k a
bind m f = Î»k. m (Î»a. f a k)
callcc f = Î»k. f (Î»a. Î»_. k a) k
```

### 3.5 Monad Laws

Any monad (T, return, bind) must satisfy:

**Left Identity:**
```
let x â‡ return v in M  â‰¡  M[v/x]
```

**Right Identity:**
```
let x â‡ M in return x  â‰¡  M
```

**Associativity:**
```
let y â‡ (let x â‡ M in N) in P  â‰¡  let x â‡ M in (let y â‡ N in P)
```

These laws ensure computations compose correctly.

---

## 4. Monad Fundamentals

### 4.1 Categorical Definition

A **monad** on a category C is a triple (T, Î·, Î¼) where:
- T : C â†’ C is an endofunctor
- Î· : Id â†’ T is a natural transformation (unit)
- Î¼ : TÂ² â†’ T is a natural transformation (multiplication)

satisfying:
```
Î¼ âˆ˜ TÎ¼ = Î¼ âˆ˜ Î¼T       (associativity)
Î¼ âˆ˜ TÎ· = Î¼ âˆ˜ Î·T = id  (unit laws)
```

### 4.2 Kleisli Category

Given monad (T, Î·, Î¼), the **Kleisli category** C_T has:
- Objects: same as C
- Morphisms: A â†’_T B are morphisms A â†’ TB in C
- Composition: g âˆ˜_T f = Î¼ âˆ˜ Tg âˆ˜ f
- Identity: Î·_A

**Interpretation:** Kleisli morphisms are "effectful functions."

### 4.3 Strong Monads

For modeling computation, we need **strong monads**:

A monad T on a category with products is **strong** if there exists:
```
t_{A,B} : A Ã— TB â†’ T(A Ã— B)
```
natural in A and B, satisfying coherence conditions.

**Interpretation:** We can "sequence" a value with a computation.

### 4.4 Monad Transformers

**Problem:** How to combine multiple effects?

**Solution:** Monad transformers stack effects.

```haskell
StateT s m a = s -> m (a, s)
ExceptT e m a = m (Either e a)
ReaderT r m a = r -> m a
WriterT w m a = m (a, w)
```

**Lifting:**
```haskell
lift :: m a -> StateT s m a
lift m = \s -> do { a <- m; return (a, s) }
```

**Challenge:** Transformer ordering matters; not all combinations work.

### 4.5 Free Monads

The **free monad** over a functor F:
```
Free F A = A + F (Free F A)
         â‰… Î¼X. A + F X
```

**Interpretation:**
- Syntax tree of operations
- Leaves are return values
- Nodes are operations with continuations

**Operations:**
```haskell
return :: a -> Free F a
return a = Pure a

(>>=) :: Free F a -> (a -> Free F b) -> Free F b
Pure a >>= f = f a
Free op >>= f = Free (fmap (>>= f) op)
```

**Handlers:** Interpret Free F a by providing semantics for F.

---

## 5. Effect Systems

### 5.1 Basic Effect Systems

**Typing Judgment with Effects:**
```
Î“ âŠ¢ e : Ï„ ! Îµ
```
- e has type Ï„
- e may perform effects in Îµ
- Îµ is a set/row of effect labels

**Example Effects:**
```
Îµ ::= âˆ…             -- pure
    | {exn}         -- may throw exception
    | {state}       -- may access state
    | {io}          -- may perform I/O
    | Îµâ‚ âˆª Îµâ‚‚       -- union of effects
```

### 5.2 Effect Subtyping

**Subtyping Rule:**
```
Î“ âŠ¢ e : Ï„ ! Îµâ‚    Îµâ‚ âŠ† Îµâ‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : Ï„ ! Îµâ‚‚
```

**Function Subtyping:**
```
Ï„â‚' â‰¤ Ï„â‚    Ï„â‚‚ â‰¤ Ï„â‚‚'    Îµ âŠ† Îµ'
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
(Ï„â‚ â†’^Îµ Ï„â‚‚) â‰¤ (Ï„â‚' â†’^Îµ' Ï„â‚‚')
```

### 5.3 Effect Polymorphism

**Challenge:** Generic functions should work with any effects.

**Solution:** Effect variables.

```
map : âˆ€Î± Î² Îµ. (Î± â†’^Îµ Î²) â†’ List Î± â†’^Îµ List Î²
```

**Constraints:** Sometimes need effect constraints:
```
runState : âˆ€Î± Îµ. (âˆ€s. State s Î±) â†’^Îµ Î±    [Îµ âŠ‡ state]
```

### 5.4 Effect Inference

**Algorithm:** Extend Hindley-Milner with effect variables.

1. Generate fresh effect variables
2. Collect effect constraints
3. Solve constraints
4. Generalize effect variables

**Challenge:** Effect polymorphism with subtyping can be undecidable.

**Solutions:**
- Row polymorphism (no subtyping)
- Qualified types (constraint-based)
- Bounded quantification (restricted)

### 5.5 Latent Effects

**Latent vs. Manifest Effects:**
- **Manifest**: Effects performed when evaluating expression
- **Latent**: Effects that would occur if function is called

```
Ï„ â†’^Îµ Ï„'   -- Îµ is latent (happens when called)
```

**Importance:** Must track both for sound reasoning.

---

## 6. Algebraic Effects and Handlers

### 6.1 Algebraic Effects

**Core Idea:** Effects as algebraic operations with equations.

**Signature Î£:** Set of operation symbols with arities.
```
op : A â†’ B    (operation op takes A, returns B)
```

**Examples:**
```
get    : Unit â†’ State
put    : State â†’ Unit
throw  : Exn â†’ âŠ¥
read   : Unit â†’ Char
write  : Char â†’ Unit
choose : Unit â†’ Bool
```

**Equations:** Laws that operations must satisfy.
```
put s; put s' â‰¡ put s'              (put-put)
put s; get () â‰¡ put s; return s     (put-get)
get (); Î»s. put s â‰¡ return ()       (get-put)
```

### 6.2 Effect Handlers

**Handler Definition:**
```
handle e with {
  return x â†’ e_ret,
  opâ‚(x, k) â†’ eâ‚,
  opâ‚‚(x, k) â†’ eâ‚‚,
  ...
}
```

- **return clause**: What to do with final value
- **operation clauses**: How to implement each operation
- **k**: The continuation (rest of computation)

**Example: Exception Handler:**
```
handle computation with {
  return x â†’ Some x,
  throw(e, k) â†’ None
}
```

**Example: State Handler:**
```
handle computation with {
  return x â†’ Î»s. x,
  get((), k) â†’ Î»s. k s s,
  put(s', k) â†’ Î»s. k () s'
} initial_state
```

### 6.3 Handler Semantics

**Operational Semantics:**

```
handle V with H â†’ H.return(V)

handle E[op(V)] with H â†’ H.op(V, Î»x. handle E[x] with H)
```

Where E[Â·] is an evaluation context and H.op is the handler clause for op.

**Key Property:** Handler captures delimited continuation E[Â·].

### 6.4 Deep vs. Shallow Handlers

**Deep Handlers:** Handler wraps recursive calls.
```
// Continuation k is already handled
op(x, k) â†’ ... k v ...   // k's effects handled
```

**Shallow Handlers:** Must re-handle.
```
// Must explicitly re-handle k
op(x, k) â†’ ... handle (k v) with H ...
```

**Trade-offs:**
- Deep: simpler reasoning, most common
- Shallow: more control, can change handler

### 6.5 Effect Rows

**Type of Effectful Computation:**
```
Eff Îµ Î±   -- computation with effects Îµ producing Î±
```

**Effect Row:**
```
Îµ ::= âŸ¨âŸ©                   -- empty (pure)
    | âŸ¨l | ÎµâŸ©             -- effect l with tail Îµ
    | Î¼                    -- effect variable
```

**Handler Type:**
```
handle : Eff âŸ¨l | ÎµâŸ© Î± â†’ (Î± â†’ Eff Îµ Î²) â†’ ... â†’ Eff Îµ Î²
```

**Key:** Handler removes effect l from row.

---

## 7. Row Polymorphism for Effects

### 7.1 Row Types

**Syntax:**
```
Row  ::= âŸ¨âŸ© | âŸ¨l : Ï„ | ÏâŸ© | Ï
Effect Row ::= âŸ¨âŸ© | âŸ¨l | ÎµâŸ© | Î¼
```

**Row Extension:**
```
âŸ¨l | ÎµâŸ© -- effect row with l and tail Îµ
```

**Row Equivalence:**
```
âŸ¨lâ‚ | âŸ¨lâ‚‚ | ÎµâŸ©âŸ© â‰¡ âŸ¨lâ‚‚ | âŸ¨lâ‚ | ÎµâŸ©âŸ©  (order doesn't matter)
```

### 7.2 Koka's Effect System

**Effect Types:**
```
Ï„ ::= Î± | Ï„â‚ â†’ Îµ Ï„â‚‚ | ...
Îµ ::= âŸ¨âŸ© | âŸ¨l | ÎµâŸ© | Î¼
```

**Built-in Effects:**
```
exn   : exceptions
div   : divergence
st<h> : state on heap h
io    : console I/O
```

**Function Types:**
```
() â†’ âŸ¨exn | ÎµâŸ© int    -- may throw, other effects in Îµ
() â†’ âŸ¨âŸ© int           -- total (no effects)
() â†’ âŸ¨divâŸ© int        -- may diverge
```

### 7.3 Effect Polymorphism via Rows

**Example:**
```
map : âˆ€Î± Î² Î¼. (Î± â†’ Î¼ Î²) â†’ list<Î±> â†’ Î¼ list<Î²>
```

Here Î¼ is an effect variable - map works with any effects.

**Effect Inference:**
```
fun foo(f, g) { f(); g() }
// Inferred: âˆ€Î± Î² Î¼. (() â†’ Î¼ Î±, () â†’ Î¼ Î²) â†’ Î¼ Î²
```

### 7.4 Duplicate Labels

**Challenge:** What if same effect appears twice?

**Koka Solution:** Allow duplicate labels with scoping.
```
âŸ¨state | âŸ¨state | ÎµâŸ©âŸ©  -- two state effects
```

Inner handler handles inner label; outer handles outer.

### 7.5 Effect Row Unification

**Algorithm:** Variant of record row unification.

```
unify(âŸ¨l | Îµâ‚âŸ©, âŸ¨l | Îµâ‚‚âŸ©) = unify(Îµâ‚, Îµâ‚‚)
unify(âŸ¨l | Îµâ‚âŸ©, âŸ¨l' | Îµâ‚‚âŸ©) = 
  let Îµ = fresh in
  unify(Îµâ‚, âŸ¨l' | ÎµâŸ©); unify(Îµâ‚‚, âŸ¨l | ÎµâŸ©)
unify(Î¼, Îµ) = Î¼ := Îµ  (occurs check)
```

**Properties:**
- Principal types exist
- Inference is decidable
- No subtyping required

---

## 8. Delimited Continuations

### 8.1 Continuations Overview

**Continuation:** "The rest of the computation."

```
1 + (2 * 3)
       ^
Continuation at * is: Î»v. 1 + v
```

**call/cc (Scheme):** Capture undelimited continuation.
```
(call/cc (lambda (k) ... (k v) ...))
```

Problem: Captures "everything", hard to compose.

### 8.2 Delimited Continuations

**Delimiters:** Mark boundaries of captured continuation.

**Operators (Felleisen, Danvy-Filinski):**
```
reset : (() â†’ Î±) â†’ Î±        -- delimiter
shift : ((Î± â†’ Î²) â†’ Î²) â†’ Î±   -- capture up to delimiter
```

**Example:**
```
reset (Î»(). 1 + shift (Î»k. k (k 10)))
= reset (Î»(). 1 + (1 + 10))   -- k = Î»v. 1 + v
= 12
```

### 8.3 Connection to Effect Handlers

**Key Insight:** Effect handlers generalize delimited continuations.

```
handle e with H â‰ˆ reset e
op(v)           â‰ˆ shift (Î»k. H.op(v, k))
```

**Handlers provide:**
- Named operations (not just one shift)
- Typed continuations
- Structured composition

### 8.4 Implementation Strategies

**CPS Transform:**
- Transform program to continuation-passing style
- Explicit continuation arguments
- Handlers become functions

**Segmented Stacks:**
- Copy stack segment on capture
- Restore on resume
- Used by OCaml 5.0

**Multi-prompt Delimited Continuations:**
- Multiple delimiter types
- Tagged prompts
- More efficient than copying

---

## 9. Language Implementations

### 9.1 Haskell

**Monad Type Class:**
```haskell
class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b
```

**Common Monads:**
```haskell
Maybe a        -- optional values
Either e a     -- errors with type e
State s a      -- stateful computation
Reader r a     -- read-only environment
Writer w a     -- logging/output
IO a           -- real-world effects
```

**Do-Notation:**
```haskell
do { x <- action1; y <- action2; return (x + y) }
-- desugars to:
action1 >>= \x -> action2 >>= \y -> return (x + y)
```

**Monad Transformers:**
```haskell
type App a = StateT Config (ExceptT Error IO) a
```

**Limitations:**
- No effect polymorphism without transformers
- Transformer stacks are cumbersome
- Effect ordering fixed by stack

### 9.2 Koka

**Effect-Typed Language:**
```koka
fun greet() : console ()
  println("Hello!")

fun divide(x: int, y: int) : exn int
  if y == 0 then throw("division by zero")
  else x / y

fun maybe-divide(x: int, y: int) : int
  with handler
    ctl throw(msg) 0
  divide(x, y)
```

**Effect Inference:**
```koka
fun map(f, xs)
  match xs
    Nil -> Nil
    Cons(x, xx) -> Cons(f(x), map(f, xx))
// Inferred: forall<a,b,e> (f: (a) -> e b, xs: list<a>) -> e list<b>
```

**Built-in Handler:**
```koka
with handler
  return(x) -> ...
  ctl op(args) -> ... resume(result) ...
```

### 9.3 OCaml 5.0

**Effect Handlers (Experimental):**
```ocaml
effect Get : int
effect Put : int -> unit

let run_state init f =
  let state = ref init in
  match f () with
  | x -> x
  | effect Get k -> continue k !state
  | effect (Put s) k -> state := s; continue k ()
```

**Multicore Support:**
- Effects for concurrency (async/await)
- Fibers via effect handlers
- No colored functions

### 9.4 F*

**Effect System with Dependent Types:**
```fstar
val incr : unit -> ST unit (requires (fun h -> True))
                           (ensures (fun h0 _ h1 -> sel h1 r = sel h0 r + 1))
```

**Effect Definition:**
```fstar
effect ST (a:Type) (pre:heap -> Type) (post:heap -> a -> heap -> Type) =
  STATE a (fun p h0 -> pre h0 /\ (forall x h1. post h0 x h1 ==> p x h1))
```

**Dijkstra Monad:**
- Predicate transformers as effects
- Weakest precondition semantics
- SMT-automated verification

### 9.5 Eff

**Research Language for Handlers:**
```eff
effect Lookup : unit -> int
effect Update : int -> unit

let state init = handler
  | effect (Lookup ()) k -> (fun s -> continue k s s)
  | effect (Update s') k -> (fun _ -> continue k () s')
  | x -> (fun _ -> x)
  | finally f -> f init
```

### 9.6 Unison

**Abilities (Effects):**
```unison
unique ability Store v where
  get : v
  put : v -> ()

storeHandler : v -> Request {Store v} a -> a
storeHandler v = cases
  {a} -> a
  {Store.get -> k} -> handle k v with storeHandler v
  {Store.put v' -> k} -> handle k () with storeHandler v'
```

---

## 10. Integration with Type Systems

### 10.1 Effects + Dependent Types

**Challenge:** Effects complicate dependent type checking.

**Issues:**
- Type-level computation must be pure
- Effect-free fragment needed for types
- Termination checking for types

**F* Approach:**
- Total/Pure/Ghost effects for specifications
- Effectful computations separate from types
- SMT solves proof obligations

**Idris Approach:**
- Effects library on top of pure types
- Algebraic effects via dependent types
- Effects don't enter type level

### 10.2 Effects + Refinement Types

**Combined Judgment:**
```
Î“ âŠ¢ e : {x:Ï„ | Ï†} ! Îµ
```

**Example:**
```
read_file : (path:String) â†’ âŸ¨io, exn | ÎµâŸ© {s:String | valid_content(s)}
```

**Verification:**
- SMT checks refinements
- Effect system tracks effects
- Combined: verified effectful code

### 10.3 Effects + Linear Types

**Challenge:** Linear resources must be used exactly once.

**Integration:**
- Linear state: must thread through computation
- Effects on linear resources tracked
- Affine monads (resources may be discarded)

**ATS Approach:**
- Linear views for resources
- Effects via linear types
- Explicit resource passing

### 10.4 Session Types as Effects

**Session Types:** Types for communication protocols.

```
!int.?bool.end   -- send int, receive bool, end
```

**As Effects:**
- Session operations are effects
- Handler implements communication
- Type tracks protocol state

**Example:**
```
effect Send : int -> unit
effect Recv : unit -> bool

session_handler = handler
  | effect (Send v) k -> write_channel(v); continue k ()
  | effect Recv k -> continue k (read_channel())
```

---

## 11. Security Applications

### 11.1 Information Flow as Effects

**Security Levels:**
```
data Level = Low | High

effect Read : Level -> Data
effect Write : Level -> Data -> ()
```

**IFC Handler:**
```
ifc_handler current_level = handler
  | effect (Read l) k ->
      if l âŠ‘ current_level
      then continue k (read_level l)
      else fail "information leak"
  | effect (Write l v) k ->
      if current_level âŠ‘ l
      then write_level l v; continue k ()
      else fail "information leak"
```

### 11.2 Capability-Based Security

**Capabilities as Effects:**
```
effect FileRead : Path -> String
effect FileWrite : Path -> String -> ()
effect NetConnect : Host -> Connection
```

**Sandboxing:**
```
sandbox : Eff âŸ¨FileRead, NetConnect | ÎµâŸ© Î± â†’ Eff Îµ (Option Î±)
sandbox = handle_with {
  return x â†’ Some x,
  FileRead(p, k) â†’ None,        -- deny file access
  NetConnect(h, k) â†’ None       -- deny network
}
```

### 11.3 Cryptographic Verification

**F* for Cryptography:**
```fstar
val encrypt : k:aes_key -> p:plaintext{length p <= max_plain} 
            -> ST ciphertext
              (requires (fun h -> key_valid h k))
              (ensures (fun h0 c h1 -> 
                length c = length p + tag_len /\
                h0 == h1))
```

**Project Everest Applications:**
- HACL*: Verified crypto library
- miTLS: Verified TLS implementation
- EverCrypt: Agile crypto provider

### 11.4 Audit Logging

**Audit Effect:**
```
effect Log : LogEntry -> ()

logged_handler = handler
  | effect (Log entry) k ->
      write_audit_log(entry);
      continue k ()
```

**Mandatory Logging:**
- Security operations emit Log effects
- Handler ensures all logs written
- Type guarantees logging happens

---

## 12. TERAS Relevance Analysis

### 12.1 Effect Requirements for TERAS

| TERAS Component | Required Effects | Priority |
|----------------|------------------|----------|
| MENARA (Mobile) | IO, State, Crypto, Net | Critical |
| GAPURA (WAF) | IO, State, Net, Log | Critical |
| ZIRAH (EDR) | IO, State, Syscall, Log | Critical |
| BENTENG (eKYC) | IO, State, Crypto, Net | Critical |
| SANDI (Signatures) | IO, Crypto, Time | Critical |
| Core Platform | State, Log, Audit | Critical |

### 12.2 Proposed TERAS Effect System

**Core Effects:**
```teras
effect State<H>            -- Mutable state on heap H
effect IO                  -- Console/File I/O
effect Net                 -- Network operations
effect Crypto              -- Cryptographic operations
effect Audit               -- Audit logging
effect Time                -- Time/clock access
effect Random              -- Secure random
effect Exn                 -- Exceptions
effect Div                 -- Divergence
```

**Security-Specific Effects:**
```teras
effect SecretRead<L>       -- Read at security level L
effect SecretWrite<L>      -- Write at security level L
effect CapUse<C>           -- Capability usage
effect SessionOp<S>        -- Session state transition
```

### 12.3 Effect Typing Integration

**Combined with A-04 (Linear Types):**
```teras
// Linear + Effectful function
fn sign(key: lin SigningKey) -> âŸ¨Crypto, AuditâŸ© Signature
```

**Combined with A-03 (Refinement Types):**
```teras
// Refined + Effectful
fn encrypt(
    data: {d: Bytes | len(d) < MAX_LEN}
) -> âŸ¨Crypto | ÎµâŸ© {c: Ciphertext | valid(c)}
```

### 12.4 Handler-Based Architecture

**Modular Security Handlers:**
```teras
// Production: Real cryptography
prod_crypto_handler : Eff âŸ¨Crypto | ÎµâŸ© Î± â†’ Eff Îµ Î±

// Testing: Mock cryptography
test_crypto_handler : Eff âŸ¨Crypto | ÎµâŸ© Î± â†’ Eff Îµ Î±

// Audit: Logged cryptography
audit_crypto_handler : Eff âŸ¨Crypto | ÎµâŸ© Î± â†’ Eff âŸ¨Audit | ÎµâŸ© Î±
```

**Benefit:** Same code, different handlers for different contexts.

### 12.5 Implementation Strategy

**Phase 1: Core Effect System**
- Effect annotations in syntax
- Row-polymorphic effect inference
- Basic effect tracking

**Phase 2: Security Effects**
- IFC effects for information flow
- Capability effects
- Audit effects

**Phase 3: Handlers**
- User-defined handlers
- Standard library handlers
- Handler composition

**Phase 4: Integration**
- Linear effects (linear resources)
- Refined effects (refined results)
- Verified effects (SMT checking)

---

## 13. Open Problems and Future Directions

### 13.1 Theoretical Challenges

1. **Effect Polymorphism + Subtyping**
   - Decidable inference with subeffects
   - Principal types with bounded effects

2. **Higher-Order Effects**
   - Effects that take effects as parameters
   - Effect-level abstraction

3. **Effect Inference Completeness**
   - When can all effects be inferred?
   - Annotation burden trade-offs

### 13.2 Practical Challenges

1. **Performance**
   - Efficient handler implementation
   - Avoiding continuation allocation
   - Fusion/optimization

2. **Composability**
   - Handler interference
   - Effect ordering
   - Semantic preservation

3. **Debugging**
   - Stack traces with handlers
   - Effect-aware debugging
   - Runtime monitoring

### 13.3 TERAS-Specific Research

1. **Security Effect Soundness**
   - Formal verification of IFC effects
   - Capability effect correctness

2. **Effect-Aware Verification**
   - SMT encoding of effect properties
   - Automated effect verification

3. **Distributed Effects**
   - Effects across network boundaries
   - Serialization of handlers

---

## 14. Bibliography

### 14.1 Foundational Works

1. Moggi, E. (1989). "Computational Lambda-Calculus and Monads." LICS 1989.

2. Moggi, E. (1991). "Notions of Computation and Monads." Information and Computation 93(1).

3. Wadler, P. (1992). "The Essence of Functional Programming." POPL 1992.

4. Wadler, P. (1995). "Monads for Functional Programming." Advanced Functional Programming.

### 14.2 Effect Systems

5. Lucassen, J.M. & Gifford, D.K. (1988). "Polymorphic Effect Systems." POPL 1988.

6. Talpin, J.-P. & Jouvelot, P. (1994). "The Type and Effect Discipline." Information and Computation 111(2).

7. Leijen, D. (2014). "Koka: Programming with Row Polymorphic Effect Types." MSFP 2014.

### 14.3 Algebraic Effects and Handlers

8. Plotkin, G. & Power, J. (2002). "Notions of Computation Determine Monads." FoSSaCS 2002.

9. Plotkin, G. & Pretnar, M. (2009). "Handlers of Algebraic Effects." ESOP 2009.

10. Plotkin, G. & Pretnar, M. (2013). "Handling Algebraic Effects." Logical Methods in Computer Science 9(4).

11. Bauer, A. & Pretnar, M. (2015). "Programming with Algebraic Effects and Handlers." Journal of Logical and Algebraic Methods in Programming 84(1).

### 14.4 Row Polymorphism

12. Wand, M. (1989). "Type Inference for Record Concatenation and Multiple Inheritance." LICS 1989.

13. RÃ©my, D. (1994). "Type Inference for Records in Natural Extension of ML." Theoretical Aspects of Object-Oriented Programming.

14. Gaster, B.R. & Jones, M.P. (1996). "A Polymorphic Type System for Extensible Records and Variants." Technical Report.

### 14.5 Verification with Effects

15. Swamy, N. et al. (2016). "Dependent Types and Multi-Monadic Effects in F*." POPL 2016.

16. Ahman, D. et al. (2017). "Dijkstra Monads for Free." POPL 2017.

17. Protzenko, J. et al. (2017). "Verified Low-Level Programming Embedded in F*." ICFP 2017.

### 14.6 Language Implementations

18. Leroy, X. (2021). "The theory of effects: from monads to algebraic effects." CollÃ¨ge de France Lectures.

19. Sivaramakrishnan, K.C. et al. (2021). "Retrofitting Effect Handlers onto OCaml." PLDI 2021.

20. BrachthÃ¤user, J.I. et al. (2020). "Effects as Capabilities: Effect Handlers and Lightweight Effect Polymorphism." OOPSLA 2020.

---

## Document Metadata

**Research Track:** A (Theoretical Foundations)
**Session:** A-05
**Topic:** Effect Systems and Monads
**Preceding Sessions:** A-01 (MLTT), A-02 (CoC/CIC), A-03 (Refinement), A-04 (Linear)
**Following Session:** A-06 (Session Types)

**Coverage Assessment:**
- Historical Development: Complete
- Theoretical Foundations: Complete
- Practical Implementations: Comprehensive
- TERAS Relevance: Detailed
- Open Problems: Identified

**Sources Consulted:** 40+ academic papers, language documentation, implementation guides

---

*This survey establishes the effect system foundations for TERAS-LANG, enabling compile-time tracking of computational effects essential for security verification.*
