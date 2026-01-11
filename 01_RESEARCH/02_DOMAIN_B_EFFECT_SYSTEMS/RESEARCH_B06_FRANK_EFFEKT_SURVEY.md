# TERAS-LANG Research Survey B-06: Frank and Effekt Languages

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B06-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-06 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Frank and Effekt represent two innovative approaches to algebraic effects. Frank introduces bidirectional effect typing and operators-as-interfaces, while Effekt pioneers capability-based effect handling with efficient compilation. This survey provides comprehensive analysis of both languages with focus on novel features applicable to TERAS.

---

## Part 1: Frank Language

### 1.1 Frank Overview

```
Frank Design Principles:
├── Effects as "abilities" (bidirectional)
├── Operators in types (interface declarations)
├── Implicit handler invocation
├── Call-by-push-value foundation
├── Pattern matching on computations
└── Do-be-do-be-do (thunk/computation distinction)
```

### 1.2 Bidirectional Effects

```frank
-- Frank: Effects flow in BOTH directions
-- Not just "computation uses effect"
-- Also "handler provides ability"

interface Send X = send : X -> Unit
interface Receive X = receive : X

-- Pipe: bidirectional effect flow
pipe : {[Send X]Unit} -> {[Receive X]Unit} -> Unit
pipe sender receiver = ...

-- sender USES Send (outgoing)
-- receiver USES Receive (incoming)
-- pipe CONNECTS them
```

### 1.3 Operators as Interfaces

```frank
-- Interface declaration (like effect)
interface State S = get : S
                  | put : S -> Unit

-- Thunks vs Values
-- {e} is a suspended computation (thunk)
-- e! forces a computation

-- Handler syntax
state : S -> {<State S>X} -> X
state _ x           = x           -- Pure value, return it
state s {get -> k}  = state s (k s)      -- Resume with current state
state _ {put s -> k} = state s (k unit)  -- Update state, resume

-- Usage
example : Int
example = state 0 {put (get! + 1); get!}
```

### 1.4 Do-Be-Do-Be-Do

```frank
-- Key insight: distinguish values and computations

-- Values: things that ARE
-- Computations: things that DO

-- A computation of type X is written {X}
-- Force with !
-- Suspend with {}

-- This enables:
-- 1. Pattern matching on computations
-- 2. Bidirectional effect flow
-- 3. Implicit handler application

map : {a -> b} -> List a -> List b
map f []        = []
map f (x :: xs) = f! x :: map f xs
--     ^^ force the function
```

### 1.5 Frank Type System

```frank
-- Ability-annotated function types
-- [E]X means "computation with ability E returning X"

interface Abort = abort : Zero

catch : {[Abort]X} -> {X} -> X
catch mx handler = ...

-- Zero is the empty type (no values)
-- abort : Zero means "doesn't return normally"

-- Multi-ability
interface State S = get : S | put : S -> Unit
interface Abort = abort : Zero

stateful-catch : S -> {[State S, Abort]X} -> {[State S]X} -> [State S]X
```

### 1.6 Frank Handler Semantics

```
Frank handler evaluation:

Pattern matching on suspended computations:
    state s {get -> k}
    
1. Evaluate the suspended computation {get -> k}
2. If it performs get, match and bind continuation to k
3. Execute handler body state s (k s)
4. k s is a new suspended computation
5. Recursively handle

This is "deep" handling by default.
```

---

## Part 2: Effekt Language

### 2.1 Effekt Overview

```
Effekt Design Principles:
├── Capabilities as values
├── Lexically scoped effects
├── Second-class continuations
├── Multi-backend compilation (JS, LLVM, Chez)
├── Efficient capability passing
└── Effect safety through lexical scope
```

### 2.2 Capabilities Model

```effekt
// Effects provide CAPABILITIES
// Capabilities are LEXICALLY SCOPED
// Cannot be returned or stored in data structures

effect Flip(): Bool

def allChoices[R](prog: () => R / Flip): List[R] =
  try { [prog()] }
  with Flip { () => resume(true) ++ resume(false) }

// The capability to perform Flip is:
// 1. Created by the handler
// 2. Available in prog's scope
// 3. Cannot escape the handler
```

### 2.3 Lexical Scoping

```effekt
// Effekt's KEY innovation: effects are lexically scoped

effect State[S]():
  def get(): S
  def put(s: S): Unit

def example(): Int / State[Int] =
  val x = do get()  // "do" performs effect
  do put(x + 1)
  do get()

// Handler creates capability
def withState[R](init: Int)(body: () => R / State[Int]): R =
  var s = init
  try { body() }
  with State[Int] {
    def get() = resume(s)
    def put(newS) = { s = newS; resume(()) }
  }

// CANNOT do this (capability escape):
// def bad() = val cap = ???; return cap  // Type error!
```

### 2.4 Second-Class Continuations

```effekt
// Continuations are SECOND-CLASS
// Cannot be stored in data structures
// Cannot be returned from handlers
// CAN be called multiple times within handler

effect Choose(): Bool

def allResults[R](prog: () => R / Choose): List[R] =
  try { [prog()] }
  with Choose { () =>
    // resume is second-class
    // Can call multiple times here
    resume(true) ++ resume(false)
    // But CANNOT: val k = resume; ...
  }
```

### 2.5 Capability Passing Compilation

```effekt
// Source
def foo(): Int / State[Int] =
  do get() + 1

// Compiled (capability passing)
def foo(cap: Capability[State[Int]]): Int =
  cap.get() + 1

// Handler provides capability
def withState[R](init: Int)(body: Capability[State[Int]] => R): R =
  var s = init
  body(new Capability[State[Int]] {
    def get() = s
    def put(newS) = { s = newS }
  })
```

### 2.6 Multi-Backend Architecture

```
Effekt Backends:
├── JavaScript (primary)
│   └── CPS transformation
├── LLVM
│   └── Stack manipulation
├── Chez Scheme
│   └── Native continuations
└── (experimental) ML backend

Each backend optimizes differently:
- JS: Closure-based continuations
- LLVM: Segmented stacks
- Chez: First-class continuations
```

---

## Part 3: Comparative Analysis

### 3.1 Feature Comparison

| Feature | Frank | Effekt |
|---------|-------|--------|
| Effect model | Abilities (bidirectional) | Capabilities (lexical) |
| Handler style | Pattern matching | try/with blocks |
| Continuations | First-class | Second-class |
| Multi-shot | Yes | Yes (in handler) |
| Effect escape | Possible | Prevented |
| Compilation | Research | Multi-backend |
| Performance | Slow (research) | Good |

### 3.2 Type System Comparison

| Feature | Frank | Effekt |
|---------|-------|--------|
| Effect types | Ability sets | Effect rows |
| Polymorphism | Ability polymorphism | Effect polymorphism |
| Row types | Implicit | Explicit |
| Dependent | No | No |
| Linear | No | Implicit (second-class) |
| Inference | Yes | Yes |

### 3.3 Handler Comparison

```frank
-- Frank handler (pattern matching)
state : S -> {<State S>X} -> X
state s {get -> k}   = state s (k s)
state _ {put s' -> k} = state s' (k unit)
state _ x            = x
```

```effekt
// Effekt handler (try/with)
def withState[R](init: S)(body: () => R / State[S]): R =
  var s = init
  try { body() }
  with State[S] {
    def get() = resume(s)
    def put(newS) = { s = newS; resume(()) }
  }
```

---

## Part 4: Security Implications

### 4.1 Frank Security Features

```frank
-- Bidirectional effects for protocols
interface SecureChannel = 
    send : Ciphertext -> Unit
  | recv : Ciphertext

-- Protocol implementation as bidirectional pipe
secure-pipe : {[Send Plaintext]Unit} 
           -> {[Receive Plaintext]Unit} 
           -> [SecureChannel]Unit
secure-pipe sender receiver = 
  -- Encrypts send, decrypts receive
```

### 4.2 Effekt Security Features

```effekt
// Lexical scoping prevents capability escape

effect SecretAccess():
  def readSecret(): String
  def writeSecret(s: String): Unit

// Capability CANNOT escape
def withSecretAccess[R](body: () => R / SecretAccess): R =
  try { body() }
  with SecretAccess {
    def readSecret() = resume(loadFromHSM())
    def writeSecret(s) = { saveToHSM(s); resume(()) }
  }

// This is TYPE ERROR:
// def bad(): Capability[SecretAccess] / SecretAccess =
//   ???  // Cannot return the capability!
```

### 4.3 Security Model Comparison

| Aspect | Frank | Effekt |
|--------|-------|--------|
| Capability escape | Possible | Prevented |
| Effect containment | Type-level | Lexical + type |
| Resource lifetime | Manual | Scoped |
| Continuation control | First-class | Second-class |

---

## Part 5: Lessons for TERAS

### 5.1 From Frank

| Feature | Value for TERAS |
|---------|-----------------|
| Bidirectional effects | Protocol modeling |
| Operators-as-interfaces | Clean effect syntax |
| Pattern matching | Ergonomic handlers |
| CBPV foundation | Formal semantics |

### 5.2 From Effekt

| Feature | Value for TERAS |
|---------|-----------------|
| Lexical scoping | Security boundaries |
| Second-class continuations | Resource safety |
| Capability passing | Performance |
| Multi-backend | Portability |

### 5.3 TERAS Synthesis

```rust
// TERAS can combine Frank's elegance with Effekt's safety

// Frank-style operator syntax
effect State<S> {
    get : () -> S,
    put : S -> ()
}

// Effekt-style lexical scoping
scoped handler state_handler<S>(init: S) for State<S> {
    // Continuation cannot escape this scope
}

// Bidirectional for protocols (Frank-inspired)
effect SecureChannel {
    send : Plaintext -> (),
    recv : () -> Plaintext
}
```

---

## Part 6: Bibliography

### Frank
1. Lindley, S., McBride, C., McLaughlin, C. (2017). "Do Be Do Be Do"
2. Convent, L., et al. (2020). "Doo Bee Doo Bee Doo"

### Effekt
3. Brachthäuser, J., et al. (2020). "Effects as Capabilities"
4. Brachthäuser, J., et al. (2022). "Effekt: Capability-passing Style for Type- and Effect-safe, Extensible Effect Handlers"

---

*Research Track Output — Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
