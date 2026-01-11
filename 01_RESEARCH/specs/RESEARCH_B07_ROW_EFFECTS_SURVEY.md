# TERAS-LANG Research Survey B-07: Row-Polymorphic Effects

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B07-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-07 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Row polymorphism provides a powerful mechanism for effect composition, enabling functions to be polymorphic over "the rest of the effects." This survey covers row type theory, application to effects, comparison with alternative approaches, and implementation strategies critical for TERAS-LANG's effect system.

---

## Part 1: Row Type Theory Foundations

### 1.1 Origins: RÃ©my's Record Calculus (1989)

```
RÃ©my's row types for extensible records:

Row ::= âŸ¨âŸ©                    -- empty row
      | âŸ¨â„“ : Ï„ | ÏâŸ©           -- field â„“ with type Ï„, rest Ï
      | Ï                      -- row variable

Record type: { Ï } where Ï is a row

Key insight: Row variables enable polymorphism over fields
```

### 1.2 Row Operations

```
Row Presence/Absence:

âŸ¨â„“ : Ï„ | ÏâŸ©  -- â„“ is PRESENT with type Ï„
âŸ¨â„“ âˆ‰ | ÏâŸ©   -- â„“ is ABSENT

Row Extension:
Ïâ‚ | Ïâ‚‚ = merge of Ïâ‚ and Ïâ‚‚ (if compatible)

Row Restriction:
Ï \ â„“ = row Ï with â„“ removed
```

### 1.3 Row Type Rules

```
Field Access:
    Î“ âŠ¢ e : { â„“ : Ï„ | Ï }
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ e.â„“ : Ï„

Field Extension:
    Î“ âŠ¢ e : { Ï }    â„“ âˆ‰ Ï
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ { â„“ = v | e } : { â„“ : Ï„ | Ï }

Row Polymorphism:
    âˆ€Ï. { â„“ : Ï„ | Ï } â†’ Ï„
    -- Works for ANY record with field â„“
```

---

## Part 2: Effect Rows

### 2.1 Effects as Rows

```
Adapting row types to effects:

Effect Row ::= âŸ¨âŸ©                  -- pure (no effects)
             | âŸ¨E : ops | ÎµâŸ©       -- effect E with operations ops
             | Îµ                    -- effect row variable

Function with effects:
    A -[Îµ]â†’ B   where Îµ is effect row

Key insight: Functions can be polymorphic over "other effects"
```

### 2.2 Effect Row Typing

```
Effect Row Typing Rules:

Operation:
    op : A â†’ B âˆˆ E
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ op(e) : B ! âŸ¨E | ÎµâŸ©

Handler (removes effect):
    Î“ âŠ¢ c : A ! âŸ¨E | ÎµâŸ©
    Î“ âŠ¢ h handles E
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ handle c with h : B ! Îµ

Row Subsumption:
    Îµâ‚ âŠ† Îµâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    A ! Îµâ‚ <: A ! Îµâ‚‚
```

### 2.3 Effect Row Syntax (Various Languages)

```koka
// Koka
fun foo(): <state<int>, exn | e> int
//         ^^^^^^^^^^^^^^^^   ^
//         concrete effects   row variable

fun bar(): <console> ()
//         ^^^^^^^^^
//         closed row (no variable)
```

```links
-- Links
sig foo : () {State:Int, Exn | e}-> Int
```

```
// TERAS (proposed)
fn foo() -[State<i32>, Exn | Îµ]-> i32
```

---

## Part 3: Row Polymorphism Details

### 3.1 Row Variables

```
Row variable Îµ represents "unknown effects"

Example:
    map : (A -[Îµ]â†’ B) â†’ List<A> -[Îµ]â†’ List<B>

The SAME effect row Îµ appears:
1. In the function argument's effect
2. In map's own effect

This means: map has whatever effects f has!
```

### 3.2 Presence and Absence

```
Some systems track presence AND absence:

âŸ¨E : Present | ÏâŸ©    -- E definitely present
âŸ¨E : Absent | ÏâŸ©     -- E definitely absent
âŸ¨ÏâŸ©                   -- E presence unknown

This enables:
- Ensuring effect not in row: âŸ¨E : Absent | ÏâŸ©
- Conditional handling
- More precise types
```

### 3.3 Scoped Row Variables

```
Scoped labels (Leijen):

âŸ¨E^s | ÎµâŸ©  -- E scoped to region s

Enables:
- Multiple instances of same effect
- Effect instance identity
- Handler matching by scope
```

### 3.4 Row Kinds

```
Kind system for rows:

Row kinds:
    â—‹   -- empty row kind
    â„“::Îº -- row extending with label â„“

Kind rules:
    âŸ¨âŸ© : â—‹
    âŸ¨â„“ : Ï„ | ÏâŸ© : â„“::Îº  where Ï : Îº

Purpose:
- Prevent duplicate labels
- Enable row polymorphism
- Type-level computation on rows
```

---

## Part 4: Implementation Strategies

### 4.1 Row Unification

```
Unifying row types:

unify(âŸ¨â„“ : Ï„â‚ | Ïâ‚âŸ©, âŸ¨â„“ : Ï„â‚‚ | Ïâ‚‚âŸ©):
    unify(Ï„â‚, Ï„â‚‚)
    unify(Ïâ‚, Ïâ‚‚)

unify(âŸ¨â„“â‚ : Ï„â‚ | Ïâ‚âŸ©, âŸ¨â„“â‚‚ : Ï„â‚‚ | Ïâ‚‚âŸ©) where â„“â‚ â‰  â„“â‚‚:
    // Row rewriting needed
    Ïâ‚' = fresh row variable
    unify(Ïâ‚, âŸ¨â„“â‚‚ : Ï„â‚‚ | Ïâ‚'âŸ©)
    unify(âŸ¨â„“â‚ : Ï„â‚ | Ïâ‚'âŸ©, Ïâ‚‚)

unify(âŸ¨â„“ : Ï„ | ÏâŸ©, Îµ):
    Ï' = fresh row variable
    substitute(Îµ, âŸ¨â„“ : Ï„ | Ï'âŸ©)
    unify(Ï, Ï')
```

### 4.2 Row Simplification

```
Canonical form for rows:

âŸ¨Eâ‚, Eâ‚‚, Eâ‚ƒ | ÎµâŸ© where Eâ‚ < Eâ‚‚ < Eâ‚ƒ (ordered)

Simplification rules:
- Sort labels alphabetically
- Remove duplicates
- Substitute known variables

Example:
    âŸ¨Exn, State, Exn | ÎµâŸ© â†’ âŸ¨Exn, State | ÎµâŸ©
```

### 4.3 Evidence for Rows

```
Evidence-passing for row effects:

// Source
fn foo() -[State<i32>, Exn | Îµ]-> i32

// Compiled
fn foo(ev_state: Evidence<State<i32>>, 
       ev_exn: Evidence<Exn>,
       ev_rest: Evidence<Îµ>) -> i32

Key insight: Evidence is a PRODUCT of effect evidences
```

---

## Part 5: Comparison with Alternatives

### 5.1 Row Types vs Set Types

| Aspect | Row Types | Set Types |
|--------|-----------|-----------|
| Order | Matters (with scopes) | Doesn't matter |
| Duplicates | Controlled by kinds | Implicit dedup |
| Polymorphism | Row variables | Effect variables |
| Presence tracking | Explicit | Implicit |
| Complexity | Higher | Lower |

### 5.2 Row Types vs Type Classes

| Aspect | Row Types | Type Classes |
|--------|-----------|--------------|
| Composition | Structural | Nominal |
| Inference | Direct | Instance search |
| Multiple | Natural | Awkward |
| Performance | Good | Depends |

### 5.3 Languages Using Row Effects

| Language | Row Style | Notes |
|----------|-----------|-------|
| Koka | Full row polymorphism | Most complete |
| Links | Row polymorphism | Web focus |
| Eff | Set-based | No row variables |
| OCaml 5 | None | Untyped effects |
| Frank | Implicit rows | Via abilities |

---

## Part 6: Security Applications

### 6.1 Effect Containment

```rust
// Row types prove effect containment

fn pure_computation() -[âŸ¨âŸ©]-> i32 {
    // Cannot perform ANY effects
    42
}

fn only_log() -[Log | âŸ¨âŸ©]-> () {
    // Can ONLY perform Log effect
    Log::info("message");
    // State::get()  // TYPE ERROR!
}
```

### 6.2 Effect Attenuation

```rust
// Reducing available effects (sandboxing)

fn attenuate<A, E1, E2>(
    f: () -[E1]-> A
) -[E2]-> A 
where 
    E1 âŠ† E2,  // E2 has at least E1
{
    f()  // Safe: E1 is subset of E2
}
```

### 6.3 Effect Isolation

```rust
// Isolating effects to scopes

fn isolated<A, E>(f: () -[E]-> A) -[âŸ¨âŸ©]-> A
where
    E: Handleable,  // All effects can be handled
{
    handle_all(f)  // Returns pure result
}
```

---

## Part 7: TERAS Row Effect Design

### 7.1 Syntax

```rust
// Effect row syntax
fn foo<Îµ>() -[State<i32>, Exn | Îµ]-> i32 {
    let x = State::get();
    if x < 0 { Exn::throw("negative") }
    x + 1
}

// Closed row (no additional effects)
fn bar() -[Log]-> () {
    Log::info("pure logging");
}

// Pure function
fn pure() -[]-> i32 {
    42
}
```

### 7.2 Row Operations

```rust
// Effect presence
fn requires_state<Îµ>(f: () -[State<i32> | Îµ]-> A) { ... }

// Effect absence
fn no_state<Îµ>(f: () -[Îµ]-> A) -[Îµ]-> A 
where
    Îµ: Lacks<State<_>>,  // Îµ definitely doesn't have State
{
    f()
}

// Effect combination
fn combined<Îµ1, Îµ2>(
    f: () -[Îµ1]-> A,
    g: A -[Îµ2]-> B
) -[Îµ1 | Îµ2]-> B {
    g(f())
}
```

### 7.3 Handler Interaction

```rust
// Handler removes effect from row
handler state_handler<S>(init: S) for State<S> {
    // Handles State<S>, passes through Îµ
    // () -[State<S> | Îµ]-> A  becomes  () -[Îµ]-> (A, S)
}
```

---

## Part 8: Bibliography

1. RÃ©my, D. (1989). "Type Checking Records and Variants in a Natural Extension of ML"
2. Leijen, D. (2005). "Extensible Records with Scoped Labels"
3. HillerstrÃ¶m, D., Lindley, S. (2016). "Liberating Effects with Rows and Handlers"
4. Leijen, D. (2014). "Koka: Programming with Row Polymorphic Effect Types"
5. Gaster, B., Jones, M. (1996). "A Polymorphic Type System for Extensible Records and Variants"

---

*Research Track Output â€” Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
