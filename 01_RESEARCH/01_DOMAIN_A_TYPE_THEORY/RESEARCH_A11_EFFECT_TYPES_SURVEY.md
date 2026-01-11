# RESEARCH_A11_EFFECT_TYPES_SURVEY.md

## TERAS-LANG Research Track
### Session A-11: Effect Types (Koka, Frank, Eff)

---

**Document ID:** RESEARCH_A11_EFFECT_TYPES_SURVEY  
**Version:** 1.0.0  
**Created:** 2026-01-03  
**Domain:** A (Type Theory Foundations)  
**Session:** A-11  
**Status:** COMPLETE

---

## 1. EXECUTIVE SUMMARY

Effect types provide a mechanism for tracking computational effects in a program's type system, enabling the compiler to reason about side effects, control flow, and resource usage. This survey examines the major effect type systems and languages, with particular focus on Koka, Frank, Eff, Effekt, and Flix, as well as the integration of effect handlers into mainstream languages like OCaml 5.

### 1.1 Key Findings

| System | Effect Typing Approach | Key Innovation | TERAS Relevance |
|--------|----------------------|----------------|-----------------|
| Koka | Row-polymorphic effects | Evidence passing + Perceus RC | 9/10 |
| Frank | Bidirectional effects | Multihandlers, invisible effect variables | 8/10 |
| Eff | First-class effects | Algebraic effect handlers | 8/10 |
| Effekt | Capability-based effects | Second-class functions | 7/10 |
| Flix | Boolean unification | Purity tracking + Datalog | 8/10 |
| OCaml 5 | Untyped handlers | Retrofitted onto existing language | 6/10 |

---

## 2. THEORETICAL FOUNDATIONS

### 2.1 Origins of Effect Systems

Effect systems originated with Gifford and Lucassen's 1986 work on polymorphic effect systems. The key insight was that function types could be enriched with an effect annotation describing what side effects the function might have.

**Original Polymorphic Effect System (Lucassen & Gifford, 1988):**
```
τ ::= Int | Bool | τ₁ →^ε τ₂    (types)
ε ::= {ε₁, ε₂, ...}             (effect sets)

Typing rule for application:
Γ ⊢ e₁ : τ₁ →^ε τ₂ !ε₁
Γ ⊢ e₂ : τ₁ !ε₂
─────────────────────────────
Γ ⊢ e₁ e₂ : τ₂ !(ε₁ ∪ ε₂ ∪ ε)
```

### 2.2 Algebraic Effects Theory

Algebraic effects, introduced by Plotkin and Power (2002), provide a mathematical foundation for computational effects. Effects are modeled as operations of an algebraic theory.

**Key Theoretical Components:**

1. **Effect Signature (Σ):** A set of operation symbols with arities
   ```
   Σ = {op₁ : A₁ → B₁, op₂ : A₂ → B₂, ...}
   ```

2. **Free Monad Interpretation:** Algebraic effects correspond to the free monad over the effect signature
   ```
   Free Σ A = Return A | Op (∃op ∈ Σ. A_op × (B_op → Free Σ A))
   ```

3. **Effect Handlers:** Interpret effect operations as computations
   ```
   handle e with
   | return x → e_ret
   | op₁(x, k) → e₁
   | op₂(x, k) → e₂
   ```

### 2.3 Row Polymorphism for Effects

Row polymorphism, adapted from record typing, provides a flexible mechanism for effect polymorphism.

**Row Types:**
```
ρ ::= ⟨⟩                    (empty row)
    | ⟨l : τ | ρ⟩           (row extension)
    | α                      (row variable)

Effect rows:
ε ::= ⟨⟩                    (pure)
    | ⟨l | ε⟩               (effect extension)
    | ε                      (effect variable)
```

---

## 3. KOKA: ROW-POLYMORPHIC EFFECT TYPES

### 3.1 Overview

Koka is a functional programming language developed by Daan Leijen at Microsoft Research, featuring a precise effect type system based on row polymorphism with scoped labels.

**Key Characteristics:**
- **Paradigm:** Strict functional with effect types
- **Effect System:** Row-polymorphic with algebraic effect handlers
- **Memory Management:** Perceus reference counting (no GC)
- **Compilation Target:** C code
- **Key Innovation:** Evidence-passing compilation

### 3.2 Effect Type Syntax

```koka
// Effect declarations
effect state<s>
  fun get() : s
  fun set(x : s) : ()

// Function with effect annotation
fun increment() : <state<int>> ()
  val x = get()
  set(x + 1)

// Effect polymorphic function
fun twice(f : () -> <e> ()) : <e> ()
  f()
  f()

// Handler
fun run-state<s,a>(init: s, action: () -> <state<s>|e> a) : e (s, a)
  var st := init
  with handler
    fun get()  { st }
    fun set(x) { st := x }
  (st, action())
```

### 3.3 Row-Polymorphic Effect Inference

Koka performs effect inference based on Hindley-Milner with row polymorphism:

```
[VAR]
Γ(x) = τ
─────────────
Γ ⊢ x : τ ! ⟨⟩

[APP]
Γ ⊢ e₁ : τ₁ → τ₂ ! ε₁
Γ ⊢ e₂ : τ₁ ! ε₂
─────────────────────────
Γ ⊢ e₁ e₂ : τ₂ ! (ε₁ ∪ ε₂)

[HANDLE]
Γ ⊢ e : τ ! ⟨l | ε⟩
h handles l returning τ'
─────────────────────────
Γ ⊢ handle_l e with h : τ' ! ε
```

### 3.4 Evidence Passing Translation

Koka compiles effect handlers using evidence passing:

```
⟦handle e with h⟧ = 
  let ev = make_evidence(h) in
  ⟦e⟧[ev]

⟦perform op(v)⟧ = 
  let ev = find_evidence(op) in
  ev.op(v, current_continuation)
```

### 3.5 Perceus Reference Counting

Koka uses Perceus for garbage-free memory management:
- **Reuse Analysis:** In-place mutation when possible
- **FIP (Fully In-Place):** Zero allocation functional updates
- **Drop Specialization:** Efficient deallocation patterns

---

## 4. FRANK: BIDIRECTIONAL EFFECT TYPES

### 4.1 Overview

Frank is a strict functional language designed by Sam Lindley, Conor McBride, and Craig McLaughlin. Its key innovation is eliminating the distinction between function abstraction and effect handling.

**Key Paper:** "Do be do be do" (POPL 2017, JFP 2020)

### 4.2 Operators and Multihandlers

In Frank, a function is simply an operator that handles no commands:

```frank
// Regular function (handles no effects)
inc : Int -> Int
inc n = n + 1

// Operator handling effects
catch : <Abort>X -> {X}
catch x           = x
catch <abort -> _> = unit

// Multihandler (handles multiple sources)
pipe : <Send X>Unit -> <Receive X>Y -> Y
pipe <send x -> s> <receive -> r> = pipe (s unit) (r x)
pipe unit          y              = y
```

### 4.3 Invisible Effect Variables

Frank features invisible effect variables - most functions are implicitly effect-polymorphic:

```frank
// map is effect-polymorphic (ambient effects propagate)
map : {X -> Y} -> List X -> List Y
map f []        = []
map f (x :: xs) = f x :: map f xs

// The block {X -> Y} can use any ambient effects
// No explicit effect variable needed
```

### 4.4 Ambient Ability

The concept of "ambient ability" - the set of effects currently available:

```frank
interface State S =
  get : S
  put : S -> Unit

state : S -> <State S>X -> X
state s x             = x
state s <get -> k>    = state s (k s)
state s <put s' -> k> = state s' (k unit)
```

---

## 5. EFF: FIRST-CLASS ALGEBRAIC EFFECTS

### 5.1 Overview

Eff is a programming language developed by Andrej Bauer and Matija Pretnar as a direct implementation of algebraic effects and handlers.

### 5.2 Effect Type Syntax

```eff
(* Effect type declaration *)
effect state = {
  operation get : unit -> int
  operation set : int -> unit
}

(* Handler type *)
A => B    (* transforms type A to type B *)

(* Effect instance creation *)
let s = new state
```

### 5.3 Effect Instances and Resources

```eff
(* Create effect instance with resource *)
let counter = new state @ 0 with
  operation get () @ r -> (r, r)
  operation set n @ r -> ((), n)

(* Use the instance *)
let increment () =
  let x = counter#get () in
  counter#set (x + 1)
```

### 5.4 Handler Semantics

```eff
(* Deep handler - recursive interpretation *)
handle e with
  | val x -> e_ret
  | op(x; k) -> e_op   (* k is continuation *)
```

---

## 6. EFFEKT: CAPABILITY-BASED EFFECTS

### 6.1 Overview

Effekt is a research language by Jonathan Brachthäuser et al. at Universität Tübingen where effects are treated as capabilities.

### 6.2 Effects as Capabilities

```effekt
// Effect declaration
effect Fail {
  def fail(msg: String): Nothing
}

// Using an effect (requires capability)
def divide(x: Int, y: Int): Int / { Fail } =
  if (y == 0) do fail("division by zero")
  else x / y

// Handler provides capability
try { divide(10, 0) }
with Fail {
  def fail(msg) = resume(0)
}
```

### 6.3 Second-Class Functions

Effekt treats all functions as second-class values:

```effekt
// Block (second-class function)
def map[A, B](l: List[A]) { f: A => B / {} }: List[B] / {} = ...

// Blocks cannot escape their lexical scope
```

### 6.4 Contextual Effect Polymorphism

Effect polymorphism without explicit effect variables:

```effekt
def eachLine(file: String) { f: String => Unit / {} }: Unit / { FileIO } = ...

// Different uses have different effects
eachLine("data.txt") { line => println(line) }
eachLine("data.txt") { line => do log(line) }
```

---

## 7. FLIX: BOOLEAN UNIFICATION EFFECTS

### 7.1 Overview

Flix is a functional-logic programming language by Magnus Madsen featuring Boolean unification for effect inference.

### 7.2 Effect Annotation Syntax

```flix
// Pure function
def add(x: Int32, y: Int32): Int32 = x + y

// Impure function (has IO effect)
def greet(name: String): Unit \ IO = 
  println("Hello, ${name}!")

// Effect polymorphic function
def map(f: a -> b \ ef, l: List[a]): List[b] \ ef = 
  match l {
    case Nil     => Nil
    case x :: xs => f(x) :: map(f, xs)
  }
```

### 7.3 Boolean Unification for Effects

```
Effect formulas:
φ ::= ⊤ (impure) | ⊥ (pure) | α (variable)
    | φ₁ ∧ φ₂ | φ₁ ∨ φ₂ | ¬φ

Unification example:
f : a -> b \ α
g : b -> c \ β
f . g : a -> c \ (α ∨ β)
```

### 7.4 Purity Tracking

Flix separates pure and impure code statically:

```flix
// Pure expressions are guaranteed side-effect-free
def factorial(n: Int32): Int32 = 
  if (n == 0) 1 else n * factorial(n - 1)

// Compiler can optimize, parallelize pure code
```

---

## 8. OCAML 5: RETROFITTED EFFECT HANDLERS

### 8.1 Overview

OCaml 5 introduced effect handlers as a concurrency substrate for lightweight threads, async/await, and coroutines.

**Key Paper:** "Retrofitting Effect Handlers onto OCaml" (PLDI 2021)

### 8.2 Effect Handler Syntax

```ocaml
(* Effect declaration *)
type _ Effect.t += 
  | Get : int Effect.t
  | Set : int -> unit Effect.t

(* Perform effect *)
let increment () =
  let x = Effect.perform Get in
  Effect.perform (Set (x + 1))

(* Handle effects *)
let run_state init action =
  let state = ref init in
  Effect.Deep.match_with action ()
    { retc = (fun x -> x)
    ; exnc = raise
    ; effc = fun (type a) (eff : a Effect.t) ->
        match eff with
        | Get -> Some (fun k -> continue k !state)
        | Set x -> Some (fun k -> state := x; continue k ())
        | _ -> None
    }
```

### 8.3 Fiber Implementation

Effect handlers are implemented using fibers (lightweight stacks):

```
Execution Stack:
┌────────┐     ┌────────┐     ┌────────┐
│ main   │ ←── │ fiber1 │ ←── │ fiber2 │ ← stack pointer
└────────┘     └────────┘     └────────┘

On effect: capture fiber2, return to fiber1
On resume: push fiber2 back, continue
```

### 8.4 Untyped Effects

OCaml 5 does not track effects in types (unlike Koka, Eff, etc.):
- Simpler type system
- Backward compatibility
- Effects as implementation detail

---

## 9. COMPARATIVE ANALYSIS

### 9.1 Effect Typing Approaches

| Approach | Languages | Advantages | Disadvantages |
|----------|-----------|------------|---------------|
| Row polymorphism | Koka, Links | Flexible, composable | Complex inference |
| Boolean unification | Flix | Efficient inference | Limited expressivity |
| Capability-based | Effekt | Simple polymorphism | Second-class functions |
| Untyped | OCaml 5 | Simple, compatible | No static tracking |
| First-class effects | Eff | Expressive | Complex type system |

### 9.2 Handler Semantics

| Language | Handler Style | Continuation | Performance |
|----------|--------------|--------------|-------------|
| Koka | Deep, lexical | Multi-shot | Excellent |
| Frank | Multihandlers | One-shot | Good |
| Eff | Deep, dynamic | Multi-shot | Moderate |
| Effekt | Lexical | One-shot | Excellent |
| OCaml 5 | Both | One-shot | Very good |

### 9.3 Compilation Strategies

| Language | Strategy | Target | Performance |
|----------|----------|--------|-------------|
| Koka | Evidence passing | C | Near-C |
| Effekt | CPS + regions | JS, LLVM | Zero-cost |
| OCaml 5 | Fibers | Native | Low overhead |
| Flix | Monomorphization | JVM | JIT optimized |

---

## 10. SECURITY APPLICATIONS

### 10.1 Effect Types for Security

```teras
// Information flow via effects
effect Secret<T>
effect Public<T>

fn process_secret(x: Secret<Data>) -> Public<Hash>
  // Effect system tracks secret → public flow

// Capability-based security
effect FileRead(path: Path)
effect FileWrite(path: Path)
effect Network(addr: Address)

fn sandboxed_compute<R>(
  action: () -> R / { Pure }  // No effects allowed
) -> R
```

### 10.2 TERAS Security Effects

Potential effect categories:

```teras
// Memory effects
effect Alloc<R>           // Allocate in region R
effect Read<R,T>          // Read from region R
effect Write<R,T>         // Write to region R

// Cryptographic effects  
effect Random             // Use CSPRNG
effect Encrypt<Alg>       // Encryption operation
effect Sign<Key>          // Signing operation

// Network effects
effect Send<Proto,Chan>   // Send on channel
effect Recv<Proto,Chan>   // Receive from channel

// Time effects
effect ConstantTime       // Must be constant-time
```

---

## 11. TERAS-LANG IMPLICATIONS

### 11.1 Design Considerations

**Effect Type Representation:**
```teras
// Option 1: Row-based (Koka-style)
fn f() -> T / <State<S>, IO | e>

// Option 2: Set-based (simpler)
fn f() -> T / { State<S>, IO }

// Option 3: Capability-based (Effekt-style)
fn f(cap: { State<S>, IO }) -> T
```

### 11.2 Integration with Linear Types

```teras
// Linear resources with effects
fn with_file<R>(
  path: Path,
  action: (lin File) -> R / { IO }
) -> R / { IO, FileError }
```

### 11.3 Integration with Session Types

```teras
// Protocol effects
effect Protocol<P>

session AuthProtocol = 
  !Credentials.?Response.end

fn authenticate(
  chan: lin Chan<AuthProtocol>
) -> bool / { Protocol<AuthProtocol> }
```

---

## 12. BIBLIOGRAPHY

### Primary Sources

1. Leijen, D. (2017). "Type Directed Compilation of Row-Typed Algebraic Effects." POPL 2017.
2. Lindley, S., McBride, C., McLaughlin, C. (2017). "Do be do be do." POPL 2017.
3. Bauer, A., Pretnar, M. (2015). "Programming with algebraic effects and handlers." JLAMP.
4. Brachthäuser, J.I., et al. (2020). "Effects as capabilities." OOPSLA 2020.
5. Madsen, M., van de Pol, J. (2020). "Polymorphic Types and Effects with Boolean Unification." OOPSLA 2020.
6. Sivaramakrishnan, K.C., et al. (2021). "Retrofitting Effect Handlers onto OCaml." PLDI 2021.
7. Plotkin, G., Power, J. (2002). "Notions of Computation Determine Monads." FOSSACS 2002.
8. Lucassen, J.M., Gifford, D.K. (1988). "Polymorphic effect systems." POPL 1988.

---

**Document Checksum (SHA-256):** To be computed on final version  
**Related Documents:** A-05 (Effect Systems), A-04 (Linear Types), A-07 (Session Types)  
**Next Session:** A-12 (Region Types)
