# TERAS-LANG Research Survey B-09: Effect Subtyping and Masking

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B09-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-09 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Effect subtyping allows computations with fewer effects to be used where more effects are permitted. Effect masking enables hiding handled effects. This survey covers the theory and practice of effect relations critical for TERAS's composable effect system.

---

## Part 1: Effect Subtyping

### 1.1 Basic Subtyping

```
Effect Subtyping Rule:

    ε₁ ⊆ ε₂
    ─────────────────
    A ! ε₁ <: A ! ε₂

Meaning: A computation with fewer effects can be used
         where more effects are allowed.

Example:
    pure_fn : A → B ! ⟨⟩
    effectful_ctx : (A → B ! ⟨State, Log⟩) → C
    
    effectful_ctx(pure_fn)  // OK: ⟨⟩ ⊆ ⟨State, Log⟩
```

### 1.2 Function Subtyping

```
Function Subtyping (contravariant in effect):

    A₂ <: A₁    B₁ <: B₂    ε₁ ⊆ ε₂
    ────────────────────────────────────────
    (A₁ -[ε₁]→ B₁) <: (A₂ -[ε₂]→ B₂)

Key: Effect is COVARIANT in functions
     (more effects = more general)
```

### 1.3 Row Subtyping

```
Row Extension as Subtyping:

    ⟨E₁, E₂ | ε⟩ ⊇ ⟨E₁ | ε⟩

The larger row (more effects) is SUPERTYPE.

Rules:
    ε <: ⟨E | ε⟩               (extension)
    ⟨E | ε₁⟩ <: ⟨E | ε₂⟩  if ε₁ <: ε₂  (depth)
```

---

## Part 2: Effect Masking

### 2.1 What is Masking?

```
Effect Masking: Hiding effects that are handled

handle c with h : A ! (ε \ E)
                      ^^^^^^^
                      E is MASKED from the result type

The handler "absorbs" effect E, so it doesn't appear
in the resulting computation's type.
```

### 2.2 Masking Rules

```
Handler Masking:

    Γ ⊢ c : A ! ⟨E | ε⟩
    Γ ⊢ h handles E to B ! ε'
    ─────────────────────────────────
    Γ ⊢ handle c with h : B ! (ε ∪ ε')

The effect E is removed from the row,
handler's own effects ε' are added.
```

### 2.3 Partial Masking

```
Masking specific instances:

effect State<S>  // Parameterized effect

handle["counter"] comp with state_handler(0)
// Masks State<Int> labeled "counter"
// Other State instances remain

Type transformation:
    ⟨State["counter"], State["name"] | ε⟩
    → ⟨State["name"] | ε⟩
```

---

## Part 3: Effect Tunneling

### 3.1 Tunneling Concept

```
Effect Tunneling: Effects passing through handlers

handler h for E1 {
    // Only handles E1
    // E2 effects "tunnel" through
}

handle h {
    do_e1();   // Handled by h
    do_e2();   // Tunnels to outer handler
}
```

### 3.2 Tunneling Semantics

```
Operational rule:

    handle E[do op(v)] with h  →  handle E[do op(v)] with h
        when op ∉ h  (op not handled by h)

Type rule:

    Γ ⊢ c : A ! ⟨E₁, E₂ | ε⟩
    h handles E₁ only
    ────────────────────────────────
    Γ ⊢ handle c with h : B ! ⟨E₂ | ε⟩
```

---

## Part 4: Advanced Topics

### 4.1 Effect Polymorphic Masking

```
Polymorphic handler:

fn run_state<A, ε>(init: S, f: () -[State<S> | ε]-> A) -[ε]-> (A, S)
                                              ^^^        ^^^
                                         effect row    row without State

The handler is polymorphic over OTHER effects ε.
```

### 4.2 Effect Coercion

```
Implicit coercion via subtyping:

fn use_log(f: () -[Log | ε]-> A) -[Log | ε]-> A

fn pure_fn() -[]-> i32 { 42 }

use_log(pure_fn)  // Coercion: [] <: [Log | ε]
```

### 4.3 Effect Lattice

```
Effect lattice structure:

       ⊤ (all effects)
      / \
     /   \
    E₁   E₂
     \   /
      \ /
       ⊥ (pure / no effects)

Meet: ε₁ ∩ ε₂ (common effects)
Join: ε₁ ∪ ε₂ (combined effects)
```

---

## Part 5: Security Implications

### 5.1 Effect Attenuation

```rust
// Reducing allowed effects (sandboxing)
fn attenuate<A>(
    allowed: EffectSet,
    f: () -[E]-> A
) -[E ∩ allowed]-> A
where
    E ⊆ allowed  // Must be subset
{
    f()  // Type system guarantees safety
}
```

### 5.2 Effect Capability Masking

```rust
// Hide capability after use
fn one_shot_capability<A>(
    cap: Capability<FileWrite>,
    f: () -[FileWrite | ε]-> A
) -[ε]-> A {  // FileWrite masked!
    handle capability_handler(cap) {
        f()
    }
    // cap is consumed, FileWrite gone from type
}
```

---

## Part 6: TERAS Design

### 6.1 Subtyping Rules

```rust
// Effect subtyping in TERAS

// Pure is subtype of any effect
impl<ε> EffectSubtype<ε> for Pure {}

// Row extension is subtyping
impl<E, ε1, ε2> EffectSubtype<Row<E, ε2>> for Row<E, ε1>
where
    ε1: EffectSubtype<ε2>
{}
```

### 6.2 Masking Syntax

```rust
// Handler masks its effect
handler state_handler<S> for State<S> masks State<S> {
    // ...
}

// Named masking
handler["counter"] state_handler for State<i32> masks State<i32>["counter"] {
    // ...
}
```

---

## Part 7: Bibliography

1. Leijen, D. (2014). "Koka: Programming with Row Polymorphic Effect Types"
2. Biernacki, D., et al. (2019). "Abstracting Algebraic Effects"
3. Hillerström, D., Lindley, S. (2016). "Liberating Effects with Rows and Handlers"

---

*Research Track Output — Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
