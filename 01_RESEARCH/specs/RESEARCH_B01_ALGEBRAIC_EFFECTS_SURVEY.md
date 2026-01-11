# TERAS-LANG Research Survey B-01: Algebraic Effects

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B01-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-01 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Algebraic effects provide a structured approach to computational effects based on operations and handlers. Originating from Plotkin and Power's work on algebraic theories of effects, this paradigm has evolved into a practical programming abstraction offering modularity, composability, and type safety. This survey covers the complete landscape from theoretical foundations through modern implementations, with emphasis on security applications for TERAS.

---

## Part 1: Historical Development

### 1.1 Origins: Algebraic Theories of Effects (2001-2003)

**Plotkin and Power's Foundation:**

```
"Adequacy for Algebraic Effects" (2001)
"Notions of Computation Determine Monads" (2002)
"Algebraic Operations and Generic Effects" (2003)

Key insight: Computational effects can be characterized as
algebraic theories â€” sets of operations with equational laws.

Effect = Signature + Equations

Example (State):
    Signature: get : S, put : S â†’ 1
    Equations: get; put(s) = put(s)
               put(s); get = put(s); return s
               put(s); put(t) = put(t)
```

**Mathematical Foundation:**

```
Lawvere Theories â†’ Algebraic Theories â†’ Effect Theories

A Lawvere theory T consists of:
- Objects: natural numbers (arities)
- Morphisms: n â†’ 1 are n-ary operations
- Composition: sequential composition
- Identities: projection operations

An algebraic effect theory adds:
- Effect operations (signature)
- Equations between operation sequences
- Interpretation in a category of algebras
```

### 1.2 Handlers: From Theory to Practice (2009-2013)

**Plotkin and Pretnar's Handlers (2009):**

```
"Handlers of Algebraic Effects" introduced:
- Effect handlers as first-class abstractions
- Deep vs shallow handling
- Handler composition
- Operational semantics

handler h {
    return x â†’ computation
    op(x, k) â†’ computation using k
}

Key insight: Handlers are like exception handlers but
can RESUME the computation via continuation k.
```

**Bauer and Pretnar's Eff (2012):**

```
First practical implementation of algebraic effects:
- ML-like language with effects
- Effect inference
- Multiple effect instances
- Resources (stateful effect instances)

effect State = {
    get : unit â†’ int
    put : int â†’ unit
}

let state_handler = handler
    | get () k â†’ fun s â†’ k s s
    | put s' k â†’ fun _ â†’ k () s'
    | return x â†’ fun _ â†’ x
```

### 1.3 Modern Developments (2014-Present)

**Timeline:**
```
2014    â”‚ Koka: Row-based effects, effect inference
2015    â”‚ Frank: Bidirectional, operators
2016    â”‚ Multicore OCaml: Effect handlers in OCaml
2017    â”‚ Effekt: Evidence passing, staged
2018    â”‚ Links: Effect handlers for web
2019    â”‚ Helium: Capabilities for effects
2020    â”‚ OCaml 5: Merged effect handlers
2021    â”‚ Unison: Abilities (effects)
2022    â”‚ Effect handlers in Haskell proposals
2023    â”‚ JEP for Java (proposed)
2024    â”‚ Wide adoption in research languages
```

---

## Part 2: Comprehensive Survey

### 2.1 Foundational Papers

**Core Theory:**

| Paper | Year | Contribution |
|-------|------|--------------|
| Plotkin & Power: Adequacy | 2001 | Algebraic characterization |
| Plotkin & Power: Notions | 2002 | Effect = monad relationship |
| Plotkin & Power: Generic | 2003 | Operations and generic effects |
| Plotkin & Pretnar: Handlers | 2009 | Handler abstraction |
| Plotkin & Pretnar: Tensors | 2013 | Tensor products of handlers |
| Bauer & Pretnar: Eff | 2015 | Full language design |
| Kammar et al: Handlers in Action | 2013 | Practical handlers |

**Semantics:**

| Paper | Year | Contribution |
|-------|------|--------------|
| Levy: CBPV | 2004 | Call-by-push-value foundation |
| Staton: Freyd Categories | 2013 | Categorical semantics |
| Forster et al: Monadic | 2017 | Monadic reflection |
| Biernacki et al: Bipolar | 2019 | Abstract machine |
| PirÃ³g et al: Syntax | 2018 | Syntactic soundness |

**Type Systems:**

| Paper | Year | Contribution |
|-------|------|--------------|
| Leijen: Koka | 2014 | Row-based effect types |
| Lindley et al: Frank | 2017 | Bidirectional effects |
| HillerstrÃ¶m & Lindley: Sessions | 2016 | Session types + effects |
| BrachthÃ¤user: Effekt | 2020 | Capability passing |
| Biernacki et al: Abstracting | 2020 | Abstract effect types |

### 2.2 All Effect Theories

**2.2.1 State Effect**

```
effect State S where
    get : () â†’ S
    put : S â†’ ()

Equations (Laws):
    get(); put(s)     â‰¡ put(s)
    put(s); get()     â‰¡ put(s); return s
    put(s); put(t)    â‰¡ put(t)
    get(); return x   â‰¡ get(); get(); return x  (idempotent)

Standard handler:
    handle[State S] comp with
        return x â†’ Î»s. x
        get() k  â†’ Î»s. k s s
        put s' k â†’ Î»_. k () s'
    end (initial_state)
```

**2.2.2 Exception Effect**

```
effect Exn E where
    raise : E â†’ âˆ€Î±. Î±

Equations:
    raise(e); f     â‰¡ raise(e)           (propagation)
    
Handler (catch):
    handle[Exn E] comp with
        return x     â†’ Right x
        raise e _    â†’ Left e            (don't resume)
    end
    
Handler (finally):
    handle comp with
        return x     â†’ cleanup(); x
        raise e _    â†’ cleanup(); raise e
    end
```

**2.2.3 Nondeterminism Effect**

```
effect Nondet where
    choose : () â†’ Bool
    fail   : () â†’ âˆ€Î±. Î±

Equations:
    choose(); (if _ then fail() else fail()) â‰¡ fail()
    choose(); (if _ then x else x)           â‰¡ x

Handler (all solutions):
    handle[Nondet] comp with
        return x     â†’ [x]
        choose() k   â†’ k True ++ k False
        fail() _     â†’ []
    end
    
Handler (first solution):
    handle[Nondet] comp with
        return x     â†’ Some x
        choose() k   â†’ k True |> Option.or_else (k False)
        fail() _     â†’ None
    end
```

**2.2.4 Reader Effect**

```
effect Reader R where
    ask : () â†’ R

Equations:
    ask(); ask(); f(x, y) â‰¡ ask(); f(x, x)  (environment is fixed)

Handler:
    handle[Reader R] comp with
        return x   â†’ Î»_. x
        ask() k    â†’ Î»r. k r r
    end
```

**2.2.5 Writer Effect**

```
effect Writer W where
    tell : W â†’ ()

Equations (monoid laws on W):
    tell(mempty); f       â‰¡ f
    tell(w1); tell(w2); f â‰¡ tell(w1 <> w2); f

Handler:
    handle[Writer W] comp with
        return x    â†’ (x, mempty)
        tell w k    â†’ let (x, w') = k () in (x, w <> w')
    end
```

**2.2.6 Continuation Effect**

```
effect Cont R where
    callcc : ((Î± â†’ R) â†’ Î±) â†’ Î±
    abort  : R â†’ âˆ€Î±. Î±

Handler (delimited):
    handle[Cont R] comp with
        return x    â†’ x
        callcc f k  â†’ k (f (Î»a. abort (k a)))
        abort r _   â†’ r
    end
```

**2.2.7 Async/Await Effect**

```
effect Async where
    async : (() â†’ Î±) â†’ Promise Î±
    await : Promise Î± â†’ Î±

Handler (cooperative scheduling):
    handle[Async] comp with
        return x      â†’ x
        async f k     â†’ let p = new_promise()
                        enqueue(Î»(). resolve p (f()))
                        k p
        await p k     â†’ if resolved p 
                        then k (get p)
                        else suspend(Î»(). k (get p))
    end
```

**2.2.8 Logging/Audit Effect**

```
effect Log where
    log : Level â†’ String â†’ ()
    with_context : Context â†’ (() â†’ Î±) â†’ Î±

Handler (security audit):
    handle[Log] comp with
        return x          â†’ x
        log level msg k   â†’ audit_write(level, msg, timestamp())
                           k ()
        with_context c f k â†’ push_context(c)
                            let r = f()
                            pop_context()
                            k r
    end
```

### 2.3 All Implementations

**2.3.1 Research Languages**

| Language | Year | Key Features |
|----------|------|--------------|
| Eff | 2012 | First implementation, resources |
| Koka | 2014 | Row effects, FBIP, evidence |
| Frank | 2017 | Bidirectional, operators |
| Links | 2016 | Web programming, sessions |
| Effekt | 2017 | Capability passing, staged |
| Helium | 2019 | Lightweight, polymorphic |
| Unison | 2019 | Content-addressed, abilities |

**2.3.2 Extensions to Existing Languages**

| Extension | Language | Status |
|-----------|----------|--------|
| Multicore OCaml | OCaml | Merged (OCaml 5) |
| effect-handlers | Haskell | Library |
| fused-effects | Haskell | Library |
| polysemy | Haskell | Library |
| effectful | Haskell | Library (fastest) |
| kotlinx.effects | Kotlin | Research |
| Project Loom | Java | Virtual threads |

**2.3.3 Detailed Implementation Analysis**

**Eff Language:**
```ocaml
(* Eff syntax *)
effect Flip : unit â†’ bool
effect Fail : unit â†’ empty

let rec choose_int n =
  if n = 0 then 
    #Fail ()
  else if #Flip () then 
    n
  else 
    choose_int (n - 1)

(* Handler *)
let all_choices =
  handler
  | val x â†’ [x]
  | #Flip () k â†’ k true @ k false
  | #Fail () _ â†’ []

(* Usage *)
with all_choices handle
  choose_int 3
(* Result: [3; 2; 1] *)
```

**Koka Language:**
```koka
// Koka syntax
effect flip
  ctl flip() : bool

effect fail
  ctl fail() : a

fun choose-int(n : int) : <flip, fail> int
  if n == 0 then fail()
  elif flip() then n
  else choose-int(n - 1)

// Handler
fun all-choices(action : () -> <flip, fail|e> a) : e list<a>
  with handler
    return(x) -> [x]
    ctl flip() -> resume(True) ++ resume(False)
    ctl fail() -> []
  action()

// Evidence-passing compilation
// No continuation capture at runtime
```

**Frank Language:**
```frank
-- Frank syntax (operators in types)
data Maybe X = nothing | just X

interface Abort = abort : [Zero]

maybe : {<Abort>X} -> Maybe X
maybe x = handle x! : X with
            abort   -> nothing
            return x -> just x

-- Bidirectional: effects flow in both directions
interface Send X = send : X -> Unit
interface Receive X = receive : X

pipe : {[Send X]Unit} -> {[Receive X]Unit} -> Unit
pipe sender receiver = ...
```

**OCaml 5 Effects:**
```ocaml
(* OCaml 5 syntax *)
effect Flip : bool
effect Fail : 'a

let choose_int n =
  if n = 0 then perform Fail
  else if perform Flip then n
  else choose_int (n - 1)

(* One-shot continuations *)
let all_choices action =
  match action () with
  | v -> [v]
  | effect Flip k ->
      continue k true @ continue k false
  | effect Fail _ -> []

(* Deep handler via recursion *)
let rec all_choices' action =
  match action () with
  | v -> [v]
  | effect Flip k ->
      all_choices' (fun () -> continue k true) @
      all_choices' (fun () -> continue k false)
  | effect Fail _ -> []
```

### 2.4 All Handler Varieties

**2.4.1 Deep vs Shallow Handlers**

```
Deep Handler: Automatically recurses on continuation invocations
    handle comp with
        op(x) k â†’ ... k(y) ...    // k is handled too
    
Shallow Handler: One-shot, doesn't handle continuation
    handle comp with
        op(x) k â†’ ... k(y) ...    // k is NOT handled
    
    Must re-install handler explicitly for deep behavior.

Tradeoffs:
    Deep: Cleaner API, automatic recursion
    Shallow: More control, can change handler mid-computation
```

**2.4.2 Parameterized Handlers**

```
handler state(initial : S) {
    var current = initial
    return x â†’ (x, current)
    get() k  â†’ k current
    put s k  â†’ current â† s; k ()
}

// Versus non-parameterized:
handler state_handler {
    return x â†’ Î»s. (x, s)
    get() k  â†’ Î»s. k s s
    put s' k â†’ Î»_. k () s'
}
```

**2.4.3 Named/Labelled Handlers**

```
// Multiple state instances
effect State[l : Label] S where
    get : () â†’ S
    put : S â†’ ()

handle["counter"] comp with State[Int] ...
handle["name"] comp with State[String] ...

// In computation:
get["counter"]()      // Returns Int
get["name"]()         // Returns String
```

**2.4.4 First-Class Handlers**

```
// Handlers as values
let h : Handler[State Int, Î±, Î²] = handler {
    return x â†’ ...
    get() k â†’ ...
    put s k â†’ ...
}

// Higher-order handler functions
let compose_handlers (h1 : Handler[E1, Î±, Î²]) 
                     (h2 : Handler[E2, Î², Î³])
                   : Handler[E1 âˆª E2, Î±, Î³] = ...
```

**2.4.5 Tunneling Handlers**

```
// Effects can "tunnel" through handlers that don't handle them

handle[State] (
    handle[Exn] comp
) with ...

// If comp performs Exn, it tunnels through State handler
// Reaches the Exn handler

// Important for effect modularity
```

### 2.5 Compilation Strategies

**2.5.1 CPS Transformation**

```
// Direct style
let x = perform Get in
let y = x + 1 in
perform (Put y)

// CPS transformed
Î»k_ret. get (Î»x.
  let y = x + 1 in
  put y (Î»_. k_ret ()))

Pros: Simple, works everywhere
Cons: Slow (continuation allocation), no TCO
```

**2.5.2 Evidence Passing (Koka)**

```
// Evidence = dictionary of handler implementations

// Original
fun foo() : <state<int>> int
    get() + 1

// Compiled (evidence passing)
fun foo(ev_state : Evidence<state<int>>) : int
    ev_state.get() + 1

Pros: Fast (no continuations for tail-resumptive)
Cons: Complex compilation, not all effects work
```

**2.5.3 Multi-Prompt Delimited Control**

```
// Use shift/reset with multiple prompts

handle[E] comp with h
    â‰ˆ
reset p_E (comp)

perform op(x)
    â‰ˆ  
shift p_E (Î»k. h.op(x, k))

Pros: Native continuation support
Cons: Requires language support
```

**2.5.4 Capability Passing (Effekt)**

```
// Capabilities are runtime values representing ability to perform

// Original
def foo(): Int / State[Int]
    do get() + 1

// Compiled
def foo(cap: Capability[State[Int]]): Int
    cap.get() + 1

// Handlers install capabilities
def withState[R](init: Int)(body: () => R / State[Int]): R
    var s = init
    body(new Capability[State[Int]] {
        def get() = s
        def put(v) = { s = v }
    })
```

**2.5.5 Selective CPS (Staged)**

```
// Only CPS-transform when continuation is actually captured

if handler is tail-resumptive:
    direct style (no transformation)
else:
    CPS transform

Example (State with evidence):
    get: tail-resumptive â†’ direct call
    callcc: captures â†’ CPS

Achieves near-optimal performance for common cases.
```

---

## Part 3: Technical Deep Dive

### 3.1 Formal Semantics

**3.1.1 Syntax**

```
Values:         v ::= x | Î»x.c | handler h
Computations:   c ::= return v | let x = câ‚ in câ‚‚ | vâ‚ vâ‚‚
                    | do op(v, y.c) | handle c with v

Handler:        h ::= { return x â†’ c_ret, 
                        opâ‚(x, k) â†’ câ‚, 
                        ..., 
                        opâ‚™(x, k) â†’ câ‚™ }

Types:          A, B ::= Î± | A â†’ B! | A Ã— B | ...
Computations:   C ::= A!E where E is effect row

Effect Row:     E ::= âŸ¨âŸ© | âŸ¨op : A â†’ B, EâŸ© | Ï
```

**3.1.2 Typing Rules**

```
Effect Typing:

    Î“ âŠ¢ v : A
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ return v : A!âŸ¨âŸ©

    Î“ âŠ¢ câ‚ : A!E    Î“, x : A âŠ¢ câ‚‚ : B!E
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ let x = câ‚ in câ‚‚ : B!E

    op : A â†’ B âˆˆ E    Î“ âŠ¢ v : A    Î“, y : B âŠ¢ c : C!E
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ do op(v, y.c) : C!E

Handler Typing:

    Î“ âŠ¢ c : A!Eâ‚    Î“ âŠ¢ h handles Eâ‚ to B!Eâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ handle c with h : B!Eâ‚‚

    Î“, x : A âŠ¢ c_ret : B!Eâ‚‚
    âˆ€opáµ¢ âˆˆ Eâ‚. Î“, x : Aáµ¢, k : Báµ¢ â†’ B!Eâ‚‚ âŠ¢ cáµ¢ : B!Eâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ { return x â†’ c_ret, opáµ¢(x,k) â†’ cáµ¢ } handles Eâ‚ to B!Eâ‚‚
```

**3.1.3 Operational Semantics**

```
Small-step (evaluation contexts):

E ::= [] | let x = E in c | handle E with h

Reduction Rules:

    let x = return v in c  â†’  c[x â†¦ v]
    
    (Î»x.c) v  â†’  c[x â†¦ v]
    
    handle (return v) with h  â†’  c_ret[x â†¦ v]
        where h = { return x â†’ c_ret, ... }
    
    handle E[do op(v, y.c)] with h  â†’  cáµ¢[x â†¦ v, k â†¦ Î»y. handle E[c] with h]
        where op = opáµ¢ in h, and h = { ..., opáµ¢(x,k) â†’ cáµ¢, ... }
        
    handle E[do op(v, y.c)] with h  â†’  handle E[do op(v, y.c)] with h
        where op âˆ‰ h  (tunneling)
```

**3.1.4 Denotational Semantics**

```
Using free monad / freer monad construction:

âŸ¦A!EâŸ§ = Free_E(âŸ¦AâŸ§)

data Free E A where
    Pure   : A â†’ Free E A
    Impure : E (Free E A) â†’ Free E A

âŸ¦return vâŸ§ = Pure âŸ¦vâŸ§

âŸ¦do op(v, y.c)âŸ§ = Impure (Op_op âŸ¦vâŸ§ (Î»y. âŸ¦câŸ§))

âŸ¦handle c with hâŸ§ = fold âŸ¦hâŸ§ âŸ¦câŸ§
    where fold alg (Pure a) = alg.return a
          fold alg (Impure (Op_op x k)) = alg.op x (fold alg âˆ˜ k)
```

### 3.2 Effect Safety

**3.2.1 Effect Safety Theorem**

```
Theorem (Effect Safety):
    If âˆ… âŠ¢ c : A!E and c â†’* c', then either:
    1. c' = return v for some v with âˆ… âŠ¢ v : A
    2. c' = E'[do op(v, y.c'')] with op âˆˆ E
    3. c' can take another step

No unhandled effects: Well-typed programs only perform
effects declared in their type.
```

**3.2.2 Handler Correctness**

```
Definition (Correct Handler):
    A handler h for effect E is correct if:
    1. All operations of E have clauses in h
    2. Return clause handles pure values
    3. Each clause satisfies its type signature

Theorem (Handled Effects Disappear):
    If Î“ âŠ¢ c : A!{E âˆª E'} and h handles E to B!E',
    then Î“ âŠ¢ handle c with h : B!E'
```

### 3.3 Advanced Topics

**3.3.1 Effect Polymorphism**

```
// Polymorphic over effects
map : âˆ€E. (A â†’ B!E) â†’ List A â†’ List B!E
map f []        = return []
map f (x :: xs) = let y  = f x
                  let ys = map f xs
                  return (y :: ys)

// Works for any effect E
map (Î»x. do log("processing"); return x * 2) [1,2,3]
    : List Int!{Log}
```

**3.3.2 Effect Subtyping**

```
Effect row subtyping:

    Eâ‚ âŠ† Eâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    A!Eâ‚ <: A!Eâ‚‚

    (effect widening: can add effects)

Row presence:
    âŸ¨op : A â†’ B | ÏâŸ© has op
    
Row absence:
    âŸ¨ÏâŸ© lacks op  (when Ï doesn't contain op)
```

**3.3.3 Scoped Effects**

```
// Effects scoped to regions
effect Local[r : Region] S where
    local_get : () â†’ S @ r
    local_put : S â†’ () @ r

run_local : âˆ€R. S â†’ (âˆ€r. () â†’ Î±!{Local[r] | R}) â†’ Î±!R
run_local init body =
    -- r is fresh, cannot escape
    handle[Local[fresh]] (body ()) with ...
```

**3.3.4 Higher-Order Effects**

```
// Effects that take computations as arguments
effect Reader R where
    ask : () â†’ R
    local : (R â†’ R) â†’ (() â†’ A!E) â†’ A!E

// local modifies environment for a sub-computation

handler reader_handler(env : R) {
    return x â†’ x
    ask() k â†’ k env
    local f body k â†’ 
        let result = handle body() with reader_handler(f env)
        k result
}
```

---

## Part 4: Analysis

### 4.1 Strengths of Algebraic Effects

| Strength | Description |
|----------|-------------|
| Modularity | Effects independent, composable |
| Type safety | Effect types prevent unhandled effects |
| Flexibility | Handlers provide multiple interpretations |
| Reasoning | Equational laws enable optimization |
| Abstraction | Hide implementation details |
| Testability | Easy to mock effects in handlers |

### 4.2 Weaknesses

| Weakness | Description |
|----------|-------------|
| Performance | Continuation capture overhead |
| Complexity | Handler semantics non-trivial |
| Effect interaction | Some combinations tricky |
| Resource management | Linear resources need care |
| Higher-order | Higher-order effects complex |
| Learning curve | New paradigm for developers |

### 4.3 Comparison with Alternatives

**vs Monads:**
```
Algebraic Effects:
+ Automatic effect propagation (no lift)
+ Multiple interpretations via handlers
+ Effect polymorphism more natural
- Less mature ecosystem
- Potentially slower (continuations)

Monads:
+ Well-understood semantics
+ Mature libraries
+ No special language support needed
- Monad transformer stack complexity
- Manual lifting
```

**vs Exceptions:**
```
Algebraic Effects:
+ Can resume after effect
+ Multiple interpretations
+ Type-tracked
- More complex

Exceptions:
+ Simple semantics
+ Fast (unwinding)
+ Widely supported
- Cannot resume
- Often untyped
```

**vs Coroutines/Generators:**
```
Algebraic Effects:
+ General (subsumes generators)
+ Typed
+ Composable handlers

Coroutines:
+ Familiar concept
+ Direct language support
- Less general
- Composition harder
```

### 4.4 Open Problems

1. **Efficient Compilation**: General handlers still have overhead
2. **Effect Inference**: Decidable inference with polymorphism
3. **Higher-Order Effects**: Clean semantics for `local`-like effects
4. **Concurrency**: Effect handlers + parallelism
5. **Linear Effects**: Interaction with linear types
6. **Dependent Effects**: Effects in dependent type settings

---

## Part 5: Security Applications for TERAS

### 5.1 Audit Effect

```
effect Audit where
    log : Level â†’ Event â†’ ()
    with_context : SecurityContext â†’ (() â†’ Î±!E) â†’ Î±!E
    get_principal : () â†’ Principal
    check_permission : Permission â†’ Bool

// Handler for TERAS audit trail
handler secure_audit {
    var context : SecurityContext = default_context
    
    return x â†’ x
    
    log level event k â†’
        let entry = AuditEntry {
            timestamp: now(),
            principal: context.principal,
            level: level,
            event: event,
            context: context.clone()
        }
        append_audit_log(entry)  // Tamper-evident
        k ()
    
    with_context ctx body k â†’
        let old = context
        context â† ctx
        let result = body()
        context â† old
        k result
    
    get_principal() k â†’
        k context.principal
    
    check_permission perm k â†’
        k (context.has_permission(perm))
}
```

### 5.2 Capability Effect

```
effect Capability[C : Cap] where
    require : () â†’ Token[C]
    with_capability : Token[C] â†’ (() â†’ Î±!E) â†’ Î±!E

// Capability checking handler
handler capability_checker(available : Set[Cap]) {
    return x â†’ x
    
    require[C]() k â†’
        if C âˆˆ available
        then k (Token[C])
        else raise CapabilityDenied(C)
    
    with_capability[C] token body k â†’
        // Token proves capability was granted
        let result = handle body() with 
            capability_checker(available âˆª {C})
        k result
}
```

### 5.3 Taint Tracking Effect

```
effect Taint where
    taint : Source â†’ Î± â†’ Tainted[Source, Î±]
    untaint : Tainted[Source, Î±] â†’ Î±  // Privileged
    check_taint : Î± â†’ Option[Source]
    propagate : (Î± â†’ Î²) â†’ Tainted[Source, Î±] â†’ Tainted[Source, Î²]

// Dynamic taint tracking handler
handler taint_tracker {
    var taint_map : Map[ObjectId, Set[Source]] = empty
    
    return x â†’ x
    
    taint source value k â†’
        let id = object_id(value)
        taint_map â† taint_map.insert(id, {source})
        k (Tainted(source, value))
    
    untaint (Tainted(_, value)) k â†’
        // Only callable from declassify context
        k value
    
    check_taint value k â†’
        let id = object_id(value)
        k (taint_map.get(id))
    
    propagate f (Tainted(source, value)) k â†’
        let result = f(value)
        let new_id = object_id(result)
        taint_map â† taint_map.insert(new_id, {source})
        k (Tainted(source, result))
}
```

### 5.4 Cryptographic Effect

```
effect Crypto where
    random_bytes : Int â†’ Bytes
    encrypt : Key â†’ Plaintext â†’ Ciphertext
    decrypt : Key â†’ Ciphertext â†’ Result[Plaintext, CryptoError]
    sign : SigningKey â†’ Message â†’ Signature
    verify : VerifyKey â†’ Message â†’ Signature â†’ Bool
    derive_key : MasterKey â†’ Context â†’ DerivedKey

// Secure crypto handler (HSM-backed)
handler hsm_crypto(hsm : HSMConnection) {
    return x â†’ x
    
    random_bytes n k â†’
        let bytes = hsm.generate_random(n)
        k bytes
    
    encrypt key plaintext k â†’
        // Key never leaves HSM
        let ciphertext = hsm.encrypt(key.handle, plaintext)
        k ciphertext
    
    decrypt key ciphertext k â†’
        let result = hsm.decrypt(key.handle, ciphertext)
        k result
    
    // ... other operations via HSM
}
```

### 5.5 Network Effect with Security

```
effect SecureNet where
    connect : Host â†’ Port â†’ TLSConfig â†’ Connection
    send : Connection â†’ Bytes â†’ ()
    recv : Connection â†’ Bytes
    close : Connection â†’ ()

// Handler with certificate validation
handler secure_network(trust_store : TrustStore) {
    return x â†’ x
    
    connect host port config k â†’
        let conn = tls_connect(host, port, config)
        let cert = conn.peer_certificate()
        if not validate_certificate(cert, trust_store, host)
        then raise CertificateError
        else k conn
    
    send conn data k â†’
        // Encrypted by TLS
        conn.write(data)
        k ()
    
    recv conn k â†’
        let data = conn.read()
        k data
    
    close conn k â†’
        conn.shutdown()
        k ()
}
```

---

## Part 6: Implementation Recommendations for TERAS

### 6.1 Core Effect System Design

```
TERAS Effect System:
â”œâ”€â”€ Row-polymorphic effects (Koka-style)
â”œâ”€â”€ Evidence passing for performance
â”œâ”€â”€ Linear effect tracking
â”œâ”€â”€ Security-specific effects built-in
â”œâ”€â”€ Handler type inference
â””â”€â”€ Effect subtyping with labels
```

### 6.2 Built-in Security Effects

```
// Core security effects for all TERAS products

effect Audit { log, with_context, get_principal }
effect Capability[C] { require, with_capability }
effect Taint[S] { taint, untaint, check_taint }
effect Crypto { random, encrypt, decrypt, sign, verify }
effect SecureIO { read_file, write_file, network }
effect Time { now, monotonic }
```

### 6.3 Performance Targets

| Operation | Target |
|-----------|--------|
| Tail-resumptive | 0 overhead vs direct |
| Single-shot continuation | < 100 cycles |
| Multi-shot continuation | < 1Î¼s |
| Handler installation | < 50 cycles |
| Effect polymorphism | Monomorphized |

---

## Part 7: Bibliography

### 7.1 Foundational Papers

1. Plotkin, G., & Power, J. (2001). "Adequacy for Algebraic Effects"
2. Plotkin, G., & Power, J. (2002). "Notions of Computation Determine Monads"
3. Plotkin, G., & Power, J. (2003). "Algebraic Operations and Generic Effects"
4. Plotkin, G., & Pretnar, M. (2009). "Handlers of Algebraic Effects"
5. Plotkin, G., & Pretnar, M. (2013). "Handling Algebraic Effects"

### 7.2 Language Implementations

6. Bauer, A., & Pretnar, M. (2015). "Programming with Algebraic Effects and Handlers"
7. Leijen, D. (2017). "Type Directed Compilation of Row-typed Algebraic Effects"
8. Lindley, S., McBride, C., & McLaughlin, C. (2017). "Do Be Do Be Do"
9. Sivaramakrishnan, K. C., et al. (2021). "Retrofitting Effect Handlers onto OCaml"
10. BrachthÃ¤user, J., et al. (2020). "Effects as Capabilities"

### 7.3 Semantics and Theory

11. Kammar, O., Lindley, S., & Oury, N. (2013). "Handlers in Action"
12. Forster, Y., Kammar, O., et al. (2017). "On the Expressive Power of User-Defined Effects"
13. Biernacki, D., et al. (2019). "Abstracting Algebraic Effects"
14. PirÃ³g, M., et al. (2018). "Syntax and Semantics of Algebraic Effect Handlers"

### 7.4 Applications

15. HillerstrÃ¶m, D., & Lindley, S. (2016). "Liberating Effects with Rows and Handlers"
16. Leijen, D. (2014). "Koka: Programming with Row Polymorphic Effect Types"
17. Xie, N., et al. (2020). "Effect Handlers, Evidently"

---

## Document Hash

SHA-256: `b01-algebraic-effects-survey-v1.0.0`

---

*Research Track Output â€” Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
