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

### 1.1 Origins: Rémy's Record Calculus (1989)

```
Rémy's row types for extensible records:

Row ::= ⟨⟩                    -- empty row
      | ⟨ℓ : τ | ρ⟩           -- field ℓ with type τ, rest ρ
      | ρ                      -- row variable

Record type: { ρ } where ρ is a row

Key insight: Row variables enable polymorphism over fields
```

### 1.2 Row Operations

```
Row Presence/Absence:

⟨ℓ : τ | ρ⟩  -- ℓ is PRESENT with type τ
⟨ℓ ∉ | ρ⟩   -- ℓ is ABSENT

Row Extension:
ρ₁ | ρ₂ = merge of ρ₁ and ρ₂ (if compatible)

Row Restriction:
ρ \ ℓ = row ρ with ℓ removed
```

### 1.3 Row Type Rules

```
Field Access:
    Γ ⊢ e : { ℓ : τ | ρ }
    ─────────────────────────
    Γ ⊢ e.ℓ : τ

Field Extension:
    Γ ⊢ e : { ρ }    ℓ ∉ ρ
    ────────────────────────────────
    Γ ⊢ { ℓ = v | e } : { ℓ : τ | ρ }

Row Polymorphism:
    ∀ρ. { ℓ : τ | ρ } → τ
    -- Works for ANY record with field ℓ
```

---

## Part 2: Effect Rows

### 2.1 Effects as Rows

```
Adapting row types to effects:

Effect Row ::= ⟨⟩                  -- pure (no effects)
             | ⟨E : ops | ε⟩       -- effect E with operations ops
             | ε                    -- effect row variable

Function with effects:
    A -[ε]→ B   where ε is effect row

Key insight: Functions can be polymorphic over "other effects"
```

### 2.2 Effect Row Typing

```
Effect Row Typing Rules:

Operation:
    op : A → B ∈ E
    ──────────────────────────────────
    Γ ⊢ op(e) : B ! ⟨E | ε⟩

Handler (removes effect):
    Γ ⊢ c : A ! ⟨E | ε⟩
    Γ ⊢ h handles E
    ─────────────────────────────────
    Γ ⊢ handle c with h : B ! ε

Row Subsumption:
    ε₁ ⊆ ε₂
    ──────────────────────────
    A ! ε₁ <: A ! ε₂
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
fn foo() -[State<i32>, Exn | ε]-> i32
```

---

## Part 3: Row Polymorphism Details

### 3.1 Row Variables

```
Row variable ε represents "unknown effects"

Example:
    map : (A -[ε]→ B) → List<A> -[ε]→ List<B>

The SAME effect row ε appears:
1. In the function argument's effect
2. In map's own effect

This means: map has whatever effects f has!
```

### 3.2 Presence and Absence

```
Some systems track presence AND absence:

⟨E : Present | ρ⟩    -- E definitely present
⟨E : Absent | ρ⟩     -- E definitely absent
⟨ρ⟩                   -- E presence unknown

This enables:
- Ensuring effect not in row: ⟨E : Absent | ρ⟩
- Conditional handling
- More precise types
```

### 3.3 Scoped Row Variables

```
Scoped labels (Leijen):

⟨E^s | ε⟩  -- E scoped to region s

Enables:
- Multiple instances of same effect
- Effect instance identity
- Handler matching by scope
```

### 3.4 Row Kinds

```
Kind system for rows:

Row kinds:
    ○   -- empty row kind
    ℓ::κ -- row extending with label ℓ

Kind rules:
    ⟨⟩ : ○
    ⟨ℓ : τ | ρ⟩ : ℓ::κ  where ρ : κ

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

unify(⟨ℓ : τ₁ | ρ₁⟩, ⟨ℓ : τ₂ | ρ₂⟩):
    unify(τ₁, τ₂)
    unify(ρ₁, ρ₂)

unify(⟨ℓ₁ : τ₁ | ρ₁⟩, ⟨ℓ₂ : τ₂ | ρ₂⟩) where ℓ₁ ≠ ℓ₂:
    // Row rewriting needed
    ρ₁' = fresh row variable
    unify(ρ₁, ⟨ℓ₂ : τ₂ | ρ₁'⟩)
    unify(⟨ℓ₁ : τ₁ | ρ₁'⟩, ρ₂)

unify(⟨ℓ : τ | ρ⟩, ε):
    ρ' = fresh row variable
    substitute(ε, ⟨ℓ : τ | ρ'⟩)
    unify(ρ, ρ')
```

### 4.2 Row Simplification

```
Canonical form for rows:

⟨E₁, E₂, E₃ | ε⟩ where E₁ < E₂ < E₃ (ordered)

Simplification rules:
- Sort labels alphabetically
- Remove duplicates
- Substitute known variables

Example:
    ⟨Exn, State, Exn | ε⟩ → ⟨Exn, State | ε⟩
```

### 4.3 Evidence for Rows

```
Evidence-passing for row effects:

// Source
fn foo() -[State<i32>, Exn | ε]-> i32

// Compiled
fn foo(ev_state: Evidence<State<i32>>, 
       ev_exn: Evidence<Exn>,
       ev_rest: Evidence<ε>) -> i32

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

fn pure_computation() -[⟨⟩]-> i32 {
    // Cannot perform ANY effects
    42
}

fn only_log() -[Log | ⟨⟩]-> () {
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
    E1 ⊆ E2,  // E2 has at least E1
{
    f()  // Safe: E1 is subset of E2
}
```

### 6.3 Effect Isolation

```rust
// Isolating effects to scopes

fn isolated<A, E>(f: () -[E]-> A) -[⟨⟩]-> A
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
fn foo<ε>() -[State<i32>, Exn | ε]-> i32 {
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
fn requires_state<ε>(f: () -[State<i32> | ε]-> A) { ... }

// Effect absence
fn no_state<ε>(f: () -[ε]-> A) -[ε]-> A 
where
    ε: Lacks<State<_>>,  // ε definitely doesn't have State
{
    f()
}

// Effect combination
fn combined<ε1, ε2>(
    f: () -[ε1]-> A,
    g: A -[ε2]-> B
) -[ε1 | ε2]-> B {
    g(f())
}
```

### 7.3 Handler Interaction

```rust
// Handler removes effect from row
handler state_handler<S>(init: S) for State<S> {
    // Handles State<S>, passes through ε
    // () -[State<S> | ε]-> A  becomes  () -[ε]-> (A, S)
}
```

---

## Part 8: Bibliography

1. Rémy, D. (1989). "Type Checking Records and Variants in a Natural Extension of ML"
2. Leijen, D. (2005). "Extensible Records with Scoped Labels"
3. Hillerström, D., Lindley, S. (2016). "Liberating Effects with Rows and Handlers"
4. Leijen, D. (2014). "Koka: Programming with Row Polymorphic Effect Types"
5. Gaster, B., Jones, M. (1996). "A Polymorphic Type System for Extensible Records and Variants"

---

*Research Track Output — Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
