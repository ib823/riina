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
â”œâ”€â”€ Infer effect annotations automatically
â”œâ”€â”€ Reduce programmer annotation burden
â”œâ”€â”€ Maintain soundness and completeness
â”œâ”€â”€ Enable effect polymorphism
â”œâ”€â”€ Support modular type checking
â””â”€â”€ Provide informative error messages
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

Îµ = Îµ'              -- equality
Îµ âŠ† Îµ'             -- subset/subtyping
E âˆˆ Îµ              -- effect membership
Îµ = Îµâ‚ âˆª Îµâ‚‚        -- union
Îµ = Îµ' \ E         -- difference (handling)
```

### 2.2 Constraint Generation Rules

```
Constraint generation: Î“ âŠ¢ e â‡’ Ï„ ! Îµ | C

Variable:
    x : Ï„ âˆˆ Î“    Îµ = fresh
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ x â‡’ Ï„ ! Îµ | {Îµ = âŸ¨âŸ©}

Application:
    Î“ âŠ¢ eâ‚ â‡’ Ï„â‚ ! Îµâ‚ | Câ‚
    Î“ âŠ¢ eâ‚‚ â‡’ Ï„â‚‚ ! Îµâ‚‚ | Câ‚‚
    Ï„_f = fresh, Ï„_r = fresh, Îµ_f = fresh
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ eâ‚ eâ‚‚ â‡’ Ï„_r ! Îµ | Câ‚ âˆª Câ‚‚ âˆª {Ï„â‚ = Ï„â‚‚ â†’ Ï„_r ! Îµ_f, 
                                      Îµ = Îµâ‚ âˆª Îµâ‚‚ âˆª Îµ_f}

Effect Operation:
    op : A â†’ B âˆˆ E    Îµ = fresh
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ op â‡’ A â†’ B ! Îµ | {E âˆˆ Îµ}

Handler:
    Î“ âŠ¢ c â‡’ Ï„_c ! Îµ_c | C_c
    Î“ âŠ¢ h handles E â‡’ Ï„_c â†’ Ï„_r ! Îµ_h | C_h
    Îµ_r = fresh
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ handle c with h â‡’ Ï„_r ! Îµ_r | C_c âˆª C_h âˆª 
                                       {Îµ_r = (Îµ_c \ E) âˆª Îµ_h}
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
Îµâ‚ = âŸ¨âŸ©                          // variable binding is pure
State âˆˆ Îµâ‚‚                        // get() needs State
State âˆˆ Îµâ‚ƒ                        // put() needs State
Log âˆˆ Îµâ‚„                          // log() needs Log
Îµ = Îµâ‚ âˆª Îµâ‚‚ âˆª Îµâ‚ƒ âˆª Îµâ‚„            // function effect is union

// Solution
Îµ = âŸ¨State, LogâŸ©
```

---

## Part 3: Constraint Solving

### 3.1 Unification-Based Solving

```
Row Unification Algorithm:

unify(Îµâ‚, Îµâ‚‚):
    if Îµâ‚ is variable:
        substitute(Îµâ‚, Îµâ‚‚)
    elif Îµâ‚‚ is variable:
        substitute(Îµâ‚‚, Îµâ‚)
    elif Îµâ‚ = âŸ¨E | Ïâ‚âŸ© and Îµâ‚‚ = âŸ¨E | Ïâ‚‚âŸ©:
        unify(Ïâ‚, Ïâ‚‚)
    elif Îµâ‚ = âŸ¨Eâ‚ | Ïâ‚âŸ© and Îµâ‚‚ = âŸ¨Eâ‚‚ | Ïâ‚‚âŸ© and Eâ‚ â‰  Eâ‚‚:
        Ï = fresh
        unify(Ïâ‚, âŸ¨Eâ‚‚ | ÏâŸ©)
        unify(âŸ¨Eâ‚ | ÏâŸ©, Ïâ‚‚)
    elif Îµâ‚ = âŸ¨âŸ© and Îµâ‚‚ = âŸ¨âŸ©:
        success
    else:
        error "Cannot unify"
```

### 3.2 Subset Constraint Solving

```
Subset Constraints: Îµâ‚ âŠ† Îµâ‚‚

Solving approach:
1. Decompose into membership constraints
   Îµâ‚ âŠ† Îµâ‚‚ â†’ âˆ€E âˆˆ Îµâ‚. E âˆˆ Îµâ‚‚
   
2. Propagate memberships
   E âˆˆ Îµ, Îµ âŠ† Îµ' â†’ E âˆˆ Îµ'
   
3. Check consistency
   E âˆˆ Îµ, Îµ = âŸ¨âŸ© â†’ error
```

### 3.3 Fixed-Point Iteration

```
For recursive functions:

1. Initialize: Îµ = âŸ¨âŸ©
2. Analyze function body with current Îµ
3. Compute new Îµ' from body
4. If Îµ' âŠ† Îµ: done
5. Else: Îµ = Îµ âˆª Îµ', goto 2

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
generalized: fn foo<Îµ>() -[State<i32> | Îµ]-> i32

But NOT always:
- Don't generalize effects that escape
- Don't generalize effects in recursive groups
- Respect value restriction
```

### 4.2 Principal Types

```
Principal Effect Types:

A type Îµ is principal if:
âˆ€ Îµ'. Îµ' satisfies constraints â†’ Îµ âŠ† Îµ'

With row polymorphism:
- Principal types exist for rank-1
- Higher-rank needs annotations
- Effect polymorphism complicates
```

### 4.3 Let Generalization

```
Let-bound generalization:

let f = Î»x. body in expr

1. Infer type of body: Ï„ ! Îµ with constraints C
2. Solve constraints C
3. Generalize free variables not in Î“
4. Check value restriction (no effects in let-bound)
5. Add to Î“ with generalized type
```

---

## Part 5: Decidability and Complexity

### 5.1 Decidability Results

```
Decidable cases:
âœ“ Simple effect sets
âœ“ Row polymorphism (first-order)
âœ“ Effect subtyping with lattice

Undecidable/hard cases:
âœ— Higher-rank effect polymorphism
âœ— Effect-dependent types
âœ— Arbitrary effect equations
```

### 5.2 Complexity Analysis

```
Inference complexity:

Simple effects (sets): O(n Ã— e) 
    n = program size, e = effect count
    
Row polymorphism: O(n Ã— e Ã— r)
    r = row operations
    
With handlers: O(n Ã— e Ã— h)
    h = handler nesting depth
    
Practical: Near-linear for typical programs
```

### 5.3 Practical Considerations

```
Performance optimizations:
â”œâ”€â”€ Incremental solving
â”œâ”€â”€ Constraint simplification
â”œâ”€â”€ Effect caching
â”œâ”€â”€ Lazy generalization
â””â”€â”€ Modular checking

Error recovery:
â”œâ”€â”€ Partial solutions on failure
â”œâ”€â”€ Understandable error messages
â”œâ”€â”€ Suggestion generation
â””â”€â”€ Effect difference reporting
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

check(Î“, e, A ! Îµ):
    (A', Îµ', C) = infer(Î“, e)
    C' = C âˆª {A' = A, Îµ' âŠ† Îµ}
    solve(C')

infer(Î“, e):
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
2. HillerstrÃ¶m, D., Lindley, S. (2016). "Liberating Effects with Rows and Handlers"
3. Talpin, J.P., Jouvelot, P. (1994). "The Type and Effect Discipline"
4. Lucassen, J., Gifford, D. (1988). "Polymorphic Effect Systems"
5. Nielson, F., Nielson, H.R. (1999). "Type and Effect Systems"

---

*Research Track Output â€” Domain B: Effect Systems*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
