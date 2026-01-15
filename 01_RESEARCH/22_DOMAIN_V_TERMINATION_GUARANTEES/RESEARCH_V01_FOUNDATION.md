# TERAS-LANG Research Domain V: Formal Termination Guarantees

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-V-TERMINATION-GUARANTEES |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | V: Formal Termination Guarantees |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# V-01: The "Halting Problem" & The TERAS Solution

## 1. The Existential Threat

**Context:**
The Halting Problem (Turing, 1936) proves that no general algorithm can decide whether an arbitrary program terminates. This is an undecidability result.

**The Consequence:**
- A program can infinite-loop, causing **Denial of Service (DoS)**.
- Resource exhaustion attacks are possible even against "type-safe" code.
- Smart contracts (Ethereum) famously require "gas" as a workaround because termination cannot be guaranteed.

**The TERAS Reality:**
Current proofs (Progress, Preservation) guarantee that well-typed programs **don't get stuck**. But they do NOT guarantee that programs **terminate**. A program that loops forever satisfies type safety but violates availability.

**The Goal:**
Prove that ALL TERAS programs terminate (or are explicitly marked as non-terminating servers/loops with productivity guarantees).

## 2. The Solution: Structural Termination & Sized Types

We will NOT solve the Halting Problem (impossible). We will RESTRICT the language to a decidable subset that is still practically useful.

### 2.1 The Core Insight

Most real programs terminate for simple structural reasons:
- Recursion on structurally smaller arguments
- Bounded loops with decreasing counters
- Finite iteration over finite data structures

We make these reasons **explicit and machine-checkable**.

### 2.2 The Mechanisms

#### Mechanism 1: Structural Recursion
All recursive functions must recurse on a **structurally smaller** argument.

```
// ALLOWED: n decreases structurally
fn factorial(n: Nat) -> Nat {
  case n of
    Zero => 1
    Succ(m) => n * factorial(m)  // m < n structurally
}

// REJECTED: no structural decrease
fn bad(n: Nat) -> Nat {
  bad(n)  // ERROR: n does not decrease
}
```

#### Mechanism 2: Sized Types
Types carry size annotations that decrease through computation.

```
type List<T, size: Nat> =
  | Nil : List<T, 0>
  | Cons : T -> List<T, n> -> List<T, n+1>

// The size annotation proves termination
fn length<T, n>(xs: List<T, n>) -> Nat {
  case xs of
    Nil => 0
    Cons(_, tail) => 1 + length(tail)  // tail has size n-1
}
```

#### Mechanism 3: Well-Founded Recursion
For complex cases, require an explicit **measure function** that decreases.

```
fn ackermann(m: Nat, n: Nat) -> Nat
  decreasing (m, n) lexicographically  // Explicit termination measure
{
  case (m, n) of
    (Zero, _) => n + 1
    (Succ(m'), Zero) => ackermann(m', 1)
    (Succ(m'), Succ(n')) => ackermann(m', ackermann(m, n'))
}
```

#### Mechanism 4: Productivity for Codata
For infinite structures (streams, servers), prove **productivity** instead of termination.

```
// Coinductive: produces output infinitely, but always makes progress
codata Stream<T> = Cons : T -> Stream<T>

fn nats_from(n: Nat) -> Stream<Nat> {
  Cons(n, nats_from(n + 1))  // Productive: always yields a value
}
```

## 3. The Mathematical Standard

### 3.1 For Terminating Programs

For every function $f$ in program $P$:

$$
\forall \text{inputs } x, \exists n \in \mathbb{N}, \text{steps}(f(x)) \leq n
$$

The bound $n$ may depend on input size, but it must exist.

### 3.2 For Productive Codata

For every corecursive function $g$:

$$
\forall k \in \mathbb{N}, \text{observe}_k(g) \text{ terminates}
$$

Where $\text{observe}_k$ extracts the first $k$ elements.

## 4. Architecture of Domain V

### 4.1 Termination Checker

A separate phase after type checking:
1. **Structural Analysis**: Identify recursive calls
2. **Size Inference**: Compute size annotations on types
3. **Measure Verification**: Check that measures decrease
4. **Proof Generation**: Emit termination proof for formal verification

### 4.2 Integration with Type System

Extend `has_type` with termination annotations:

```coq
Inductive has_type_terminating :
  type_env -> store_ty -> security_level ->
  expr -> ty -> effect -> termination_measure -> Prop
```

### 4.3 Escape Hatches (Explicit & Audited)

For genuinely non-terminating code (servers, REPLs):

```
#[non_terminating]
fn event_loop() -> ! {
  // Explicitly marked, audited, sandboxed
}
```

Such code:
- Must be in a separate module
- Cannot be called from terminating code
- Runs under Track U (Runtime Guardian) supervision with watchdogs

## 5. Implementation Strategy (Infinite Timeline)

1. **Step 1: Define Sized Type System**
   - Extend `Syntax.v` with size annotations
   - Prove size preservation through evaluation

2. **Step 2: Implement Termination Checker**
   - Call graph analysis
   - Size constraint solving
   - Proof certificate generation

3. **Step 3: Verify in Coq**
   - Prove: "If termination checker accepts, program terminates"
   - Formalize: Strong normalization for pure subset
   - Formalize: Productivity for codata

4. **Step 4: Integration**
   - Termination checking becomes mandatory compilation phase
   - Programs that don't pass are rejected

## 6. Obsolescence of Threats

- **DoS via Infinite Loops:** OBSOLETE. Non-terminating code is rejected or explicitly sandboxed.
- **Resource Exhaustion:** OBSOLETE. Bounded recursion implies bounded resources.
- **ReDoS (Regex DoS):** OBSOLETE. Regex engine uses only terminating constructs.
- **Algorithmic Complexity Attacks:** MITIGATED. Size types expose complexity.

## 7. Dependencies

| Dependency | Direction | Nature |
|------------|-----------|--------|
| Track A (Formal) | V depends on A | Extends type system |
| Track B (Proto) | V feeds B | Termination checker implementation |
| Track U (Guardian) | V coordinates with U | Non-terminating code monitoring |

---

**"That which does not terminate does not exist in TERAS—unless explicitly caged."**
