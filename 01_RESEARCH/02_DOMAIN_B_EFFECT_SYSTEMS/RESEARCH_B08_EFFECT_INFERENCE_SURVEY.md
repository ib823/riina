# TERAS-LANG Research Survey B-08: Effect Inference

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B08-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-08 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Effect inference automatically determines what effects a function may perform, reducing annotation burden while maintaining type safety. This survey covers constraint generation, solving algorithms, decidability results, and practical implementation strategies for TERAS-LANG.

---

## Part 1: Effect Inference Fundamentals

### 1.1 Goals of Effect Inference

```
Effect inference objectives:
├── Infer effect annotations automatically
├── Reduce programmer annotation burden
├── Maintain soundness and completeness
├── Enable effect polymorphism
├── Support modular type checking
└── Provide informative error messages
```

### 1.2 Inference Process Overview

```
Effect Inference Pipeline:

1. Parse program (no effect annotations)
2. Generate fresh effect variables
3. Collect effect constraints
4. Solve constraints
5. Generalize inferred effects
6. Insert evidence parameters (compilation)
```

---

## Part 2: Constraint Generation

### 2.1 Constraint Language

```
Effect Constraints:

ε = ε'              -- equality
ε ⊆ ε'             -- subset/subtyping
E ∈ ε              -- effect membership
ε = ε₁ ∪ ε₂        -- union
ε = ε' \ E         -- difference (handling)
```

### 2.2 Constraint Generation Rules

```
Constraint generation: Γ ⊢ e ⇒ τ ! ε | C

Variable:
    x : τ ∈ Γ    ε = fresh
    ────────────────────────────
    Γ ⊢ x ⇒ τ ! ε | {ε = ⟨⟩}

Application:
    Γ ⊢ e₁ ⇒ τ₁ ! ε₁ | C₁
    Γ ⊢ e₂ ⇒ τ₂ ! ε₂ | C₂
    τ_f = fresh, τ_r = fresh, ε_f = fresh
    ─────────────────────────────────────────────────────────
    Γ ⊢ e₁ e₂ ⇒ τ_r ! ε | C₁ ∪ C₂ ∪ {τ₁ = τ₂ → τ_r ! ε_f, 
                                      ε = ε₁ ∪ ε₂ ∪ ε_f}

Effect Operation:
    op : A → B ∈ E    ε = fresh
    ─────────────────────────────────────
    Γ ⊢ op ⇒ A → B ! ε | {E ∈ ε}

Handler:
    Γ ⊢ c ⇒ τ_c ! ε_c | C_c
    Γ ⊢ h handles E ⇒ τ_c → τ_r ! ε_h | C_h
    ε_r = fresh
    ────────────────────────────────────────────────────
    Γ ⊢ handle c with h ⇒ τ_r ! ε_r | C_c ∪ C_h ∪ 
                                       {ε_r = (ε_c \ E) ∪ ε_h}
```

### 2.3 Constraint Example

```
// Source
fn example() {
    let x = get();    // State effect
    put(x + 1);
    log("done");      // Log effect
}

// Generated constraints
ε₁ = ⟨⟩                          // variable binding is pure
State ∈ ε₂                        // get() needs State
State ∈ ε₃                        // put() needs State
Log ∈ ε₄                          // log() needs Log
ε = ε₁ ∪ ε₂ ∪ ε₃ ∪ ε₄            // function effect is union

// Solution
ε = ⟨State, Log⟩
```

---

## Part 3: Constraint Solving

### 3.1 Unification-Based Solving

```
Row Unification Algorithm:

unify(ε₁, ε₂):
    if ε₁ is variable:
        substitute(ε₁, ε₂)
    elif ε₂ is variable:
        substitute(ε₂, ε₁)
    elif ε₁ = ⟨E | ρ₁⟩ and ε₂ = ⟨E | ρ₂⟩:
        unify(ρ₁, ρ₂)
    elif ε₁ = ⟨E₁ | ρ₁⟩ and ε₂ = ⟨E₂ | ρ₂⟩ and E₁ ≠ E₂:
        ρ = fresh
        unify(ρ₁, ⟨E₂ | ρ⟩)
        unify(⟨E₁ | ρ⟩, ρ₂)
    elif ε₁ = ⟨⟩ and ε₂ = ⟨⟩:
        success
    else:
        error "Cannot unify"
```

### 3.2 Subset Constraint Solving

```
Subset Constraints: ε₁ ⊆ ε₂

Solving approach:
1. Decompose into membership constraints
   ε₁ ⊆ ε₂ → ∀E ∈ ε₁. E ∈ ε₂
   
2. Propagate memberships
   E ∈ ε, ε ⊆ ε' → E ∈ ε'
   
3. Check consistency
   E ∈ ε, ε = ⟨⟩ → error
```

### 3.3 Fixed-Point Iteration

```
For recursive functions:

1. Initialize: ε = ⟨⟩
2. Analyze function body with current ε
3. Compute new ε' from body
4. If ε' ⊆ ε: done
5. Else: ε = ε ∪ ε', goto 2

Guaranteed to terminate:
- Effect set is finite
- Each iteration adds effects
- Bounded by total effect count
```

---

## Part 4: Generalization

### 4.1 Effect Generalization

```
After solving, generalize free effect variables:

inferred: fn foo() -[State<i32>]-> i32
generalized: fn foo<ε>() -[State<i32> | ε]-> i32

But NOT always:
- Don't generalize effects that escape
- Don't generalize effects in recursive groups
- Respect value restriction
```

### 4.2 Principal Types

```
Principal Effect Types:

A type ε is principal if:
∀ ε'. ε' satisfies constraints → ε ⊆ ε'

With row polymorphism:
- Principal types exist for rank-1
- Higher-rank needs annotations
- Effect polymorphism complicates
```

### 4.3 Let Generalization

```
Let-bound generalization:

let f = λx. body in expr

1. Infer type of body: τ ! ε with constraints C
2. Solve constraints C
3. Generalize free variables not in Γ
4. Check value restriction (no effects in let-bound)
5. Add to Γ with generalized type
```

---

## Part 5: Decidability and Complexity

### 5.1 Decidability Results

```
Decidable cases:
✓ Simple effect sets
✓ Row polymorphism (first-order)
✓ Effect subtyping with lattice

Undecidable/hard cases:
✗ Higher-rank effect polymorphism
✗ Effect-dependent types
✗ Arbitrary effect equations
```

### 5.2 Complexity Analysis

```
Inference complexity:

Simple effects (sets): O(n × e) 
    n = program size, e = effect count
    
Row polymorphism: O(n × e × r)
    r = row operations
    
With handlers: O(n × e × h)
    h = handler nesting depth
    
Practical: Near-linear for typical programs
```

### 5.3 Practical Considerations

```
Performance optimizations:
├── Incremental solving
├── Constraint simplification
├── Effect caching
├── Lazy generalization
└── Modular checking

Error recovery:
├── Partial solutions on failure
├── Understandable error messages
├── Suggestion generation
└── Effect difference reporting
```

---

## Part 6: Implementation Strategies

### 6.1 Koka's Inference Algorithm

```
Koka inference phases:

1. Syntax-directed constraint generation
2. Row constraint simplification
3. HM-style unification
4. Effect generalization with value restriction
5. Evidence insertion

Key innovations:
- Efficient row representation
- Scoped effect handling
- Tail-resumptive detection
```

### 6.2 Bidirectional Effect Checking

```
Combining inference and checking:

check(Γ, e, A ! ε):
    (A', ε', C) = infer(Γ, e)
    C' = C ∪ {A' = A, ε' ⊆ ε}
    solve(C')

infer(Γ, e):
    // Generate constraints, return (type, effect, constraints)

Benefits:
- Better error messages
- Handles higher-rank
- Supports annotations
```

### 6.3 Modular Inference

```
Module-level inference:

1. Infer types within module
2. Export with generalized signatures
3. Use signatures at import sites

Challenges:
- Cross-module effects
- Separate compilation
- Interface stability
```

---

## Part 7: Error Reporting

### 7.1 Effect Error Messages

```
Good error messages need:

1. Which effect is problematic
   "Effect 'FileWrite' not handled"

2. Where it comes from
   "at line 42: write_file(path, data)"

3. What handlers are available
   "Available handlers: FileRead (line 30)"

4. How to fix it
   "Add handler 'with file_write_handler { ... }'"
```

### 7.2 Effect Blame Tracking

```
Track effect sources through inference:

EffectOrigin = {
    effect: Effect,
    location: SourceLoc,
    reason: String,
    trace: List<EffectOrigin>  // propagation trace
}

On error, walk trace to find root cause.
```

---

## Part 8: TERAS Inference Design

### 8.1 Inference Algorithm

```rust
// TERAS effect inference

fn infer_effects(expr: &Expr, ctx: &Context) -> (Type, EffectRow, Constraints) {
    match expr {
        Expr::Var(x) => {
            let ty = ctx.lookup(x);
            let eff = fresh_effect_var();
            (ty, eff, vec![Constraint::Eq(eff, empty_row())])
        }
        
        Expr::App(f, arg) => {
            let (ty_f, eff_f, c_f) = infer_effects(f, ctx);
            let (ty_arg, eff_arg, c_arg) = infer_effects(arg, ctx);
            let ty_ret = fresh_type_var();
            let eff_body = fresh_effect_var();
            let eff_total = fresh_effect_var();
            
            let constraints = c_f.union(c_arg).union(vec![
                Constraint::Eq(ty_f, FnType(ty_arg, ty_ret, eff_body)),
                Constraint::Eq(eff_total, union(eff_f, eff_arg, eff_body)),
            ]);
            
            (ty_ret, eff_total, constraints)
        }
        
        Expr::EffectOp(effect, op) => {
            let (arg_ty, ret_ty) = effect.op_signature(op);
            let eff = fresh_effect_var();
            (FnType(arg_ty, ret_ty, eff), eff, 
             vec![Constraint::Member(effect, eff)])
        }
        
        Expr::Handle(body, handler) => {
            let (ty_body, eff_body, c_body) = infer_effects(body, ctx);
            let handled_effect = handler.effect();
            let eff_result = fresh_effect_var();
            
            let constraints = c_body.union(vec![
                Constraint::Eq(eff_result, remove(eff_body, handled_effect)),
            ]);
            
            (ty_body, eff_result, constraints)
        }
        
        // ... other cases
    }
}
```

### 8.2 Solving Strategy

```rust
fn solve_constraints(constraints: Vec<Constraint>) -> Result<Substitution, Error> {
    let mut subst = Substitution::empty();
    let mut worklist = constraints;
    
    while let Some(c) = worklist.pop() {
        match c {
            Constraint::Eq(eff1, eff2) => {
                let (subst', new_constraints) = unify_effects(
                    subst.apply(eff1), 
                    subst.apply(eff2)
                )?;
                subst = subst.compose(subst');
                worklist.extend(new_constraints);
            }
            
            Constraint::Member(effect, row) => {
                let row = subst.apply(row);
                if !row.contains(effect) {
                    if row.is_closed() {
                        return Err(Error::UnhandledEffect(effect, row));
                    }
                    // Add effect to open row
                    let new_row = row.extend(effect);
                    subst = subst.compose(Substitution::single(row.var(), new_row));
                }
            }
            
            Constraint::Subset(eff1, eff2) => {
                // Decompose into membership constraints
                for e in subst.apply(eff1).effects() {
                    worklist.push(Constraint::Member(e, eff2.clone()));
                }
            }
        }
    }
    
    Ok(subst)
}
```

---

## Part 9: Bibliography

1. Leijen, D. (2014). "Koka: Programming with Row Polymorphic Effect Types"
2. Hillerström, D., Lindley, S. (2016). "Liberating Effects with Rows and Handlers"
3. Talpin, J.P., Jouvelot, P. (1994). "The Type and Effect Discipline"
4. Lucassen, J., Gifford, D. (1988). "Polymorphic Effect Systems"
5. Nielson, F., Nielson, H.R. (1999). "Type and Effect Systems"

---

*Research Track Output — Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
