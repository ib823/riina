# TERAS-LANG Research Survey A-20: Type System Soundness Proofs

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A20-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

## Executive Summary

Type system soundness ensures that well-typed programs cannot exhibit certain classes of errors at runtime. This survey covers progress and preservation theorems, semantic type soundness, logical relations, mechanized proofs, and soundness for advanced type features. For TERAS-LANG, rigorous soundness proofs provide mathematical guarantees that security properties enforced by the type system cannot be violated.

---

## 1. Foundations of Type Soundness

### 1.1 What is Type Soundness?

Type soundness states that the type system accurately predicts runtime behavior:

```
"Well-typed programs don't go wrong" â€” Robin Milner

Formally:
    If âˆ… âŠ¢ e : Ï„ and e â†’* v, then v is a value of type Ï„
    If âˆ… âŠ¢ e : Ï„, then e does not get stuck
```

**"Getting stuck"**: Reaching a state that is neither a value nor can take a step.

### 1.2 Why Soundness Matters

| Property | Without Soundness | With Soundness |
|----------|-------------------|----------------|
| Memory safety | Runtime errors possible | Guaranteed safe |
| Type integrity | Casts may fail | Types accurate |
| Security | Exploits possible | Properties enforced |
| Optimization | Conservative only | Type-based opts safe |

### 1.3 Historical Development

```
Timeline of Type Soundness:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
1978    â”‚ Milner: "Well-typed programs don't go wrong"
1981    â”‚ Wright: Syntactic approach foundations
1992    â”‚ Harper: Progress + Preservation formulation
1994    â”‚ Wright & Felleisen: Syntactic soundness for ML
1997    â”‚ Appel & McAllester: Indexed logical relations
2001    â”‚ Ahmed: Step-indexed logical relations
2007    â”‚ Dreyer: Recursive types with step-indexing
2009    â”‚ POPLmark: Mechanization challenge
2010    â”‚ Iris: Higher-order concurrent separation logic
2017    â”‚ RustBelt: Rust soundness in Iris
2019    â”‚ Stacked Borrows: Rust aliasing model
2020+   â”‚ Semantic approaches dominate research
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

---

## 2. Syntactic Type Soundness

### 2.1 Progress and Preservation

The classic formulation splits soundness into two properties:

**Progress**: Well-typed closed terms are either values or can step.
```
If âˆ… âŠ¢ e : Ï„, then either:
    1. e is a value, or
    2. âˆƒe'. e â†’ e'
```

**Preservation (Subject Reduction)**: Typing is preserved under reduction.
```
If Î“ âŠ¢ e : Ï„ and e â†’ e', then Î“ âŠ¢ e' : Ï„
```

**Type Safety**: Combining these by induction on execution:
```
Theorem (Type Safety):
    If âˆ… âŠ¢ e : Ï„, then e does not get stuck.
    
Proof: By induction on the length of reduction sequence.
    Base: e is the original term, which is well-typed.
    Step: If e â†’ e' and e is well-typed:
        - By Progress, e is a value (done) or steps to e'
        - By Preservation, e' is well-typed
        - Continue inductively
```

### 2.2 Simply Typed Lambda Calculus (STLC)

**Syntax:**
```
Types:       Ï„ ::= Î± | Ï„â‚ â†’ Ï„â‚‚
Terms:       e ::= x | Î»x:Ï„. e | eâ‚ eâ‚‚
Values:      v ::= Î»x:Ï„. e
Contexts:    Î“ ::= âˆ… | Î“, x : Ï„
```

**Typing Rules:**
```
    (x : Ï„) âˆˆ Î“          Î“, x : Ï„â‚ âŠ¢ e : Ï„â‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€      â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ x : Ï„            Î“ âŠ¢ Î»x:Ï„â‚. e : Ï„â‚ â†’ Ï„â‚‚

    Î“ âŠ¢ eâ‚ : Ï„â‚ â†’ Ï„â‚‚    Î“ âŠ¢ eâ‚‚ : Ï„â‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ eâ‚ eâ‚‚ : Ï„â‚‚
```

**Operational Semantics (Call-by-Value):**
```
    eâ‚ â†’ eâ‚'                    eâ‚‚ â†’ eâ‚‚'
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€            â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    eâ‚ eâ‚‚ â†’ eâ‚' eâ‚‚              v eâ‚‚ â†’ v eâ‚‚'

    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    (Î»x:Ï„. e) v â†’ [x â†¦ v]e   (Î²-reduction)
```

**Progress Proof (STLC):**
```
Theorem: If âˆ… âŠ¢ e : Ï„, then e is a value or âˆƒe'. e â†’ e'.

Proof by induction on typing derivation:
    Case Var: Impossible (âˆ… has no bindings)
    
    Case Lam: e = Î»x:Ï„â‚. e'
        e is a value. Done.
        
    Case App: e = eâ‚ eâ‚‚ with âˆ… âŠ¢ eâ‚ : Ï„' â†’ Ï„ and âˆ… âŠ¢ eâ‚‚ : Ï„'
        By IH on eâ‚: eâ‚ is a value or steps
            If eâ‚ steps to eâ‚': eâ‚ eâ‚‚ â†’ eâ‚' eâ‚‚
            If eâ‚ is a value:
                By canonical forms, eâ‚ = Î»x:Ï„'. eâ‚'
                By IH on eâ‚‚: eâ‚‚ is a value or steps
                    If eâ‚‚ steps to eâ‚‚': (Î»x:Ï„'. eâ‚') eâ‚‚ â†’ (Î»x:Ï„'. eâ‚') eâ‚‚'
                    If eâ‚‚ is a value v: (Î»x:Ï„'. eâ‚') v â†’ [x â†¦ v]eâ‚'
```

**Preservation Proof (STLC):**
```
Theorem: If Î“ âŠ¢ e : Ï„ and e â†’ e', then Î“ âŠ¢ e' : Ï„.

Proof by induction on typing derivation:
    Case App: e = eâ‚ eâ‚‚, need to show preservation for each reduction:
        
        Subcase eâ‚ â†’ eâ‚':
            By IH, Î“ âŠ¢ eâ‚' : Ï„' â†’ Ï„
            Î“ âŠ¢ eâ‚‚ : Ï„' (unchanged)
            By App rule, Î“ âŠ¢ eâ‚' eâ‚‚ : Ï„
            
        Subcase eâ‚‚ â†’ eâ‚‚':
            Similar
            
        Subcase (Î»x:Ï„'. e) v â†’ [x â†¦ v]e (Î²-reduction):
            Î“ âŠ¢ Î»x:Ï„'. e : Ï„' â†’ Ï„
            By inversion, Î“, x : Ï„' âŠ¢ e : Ï„
            Î“ âŠ¢ v : Ï„'
            By substitution lemma, Î“ âŠ¢ [x â†¦ v]e : Ï„
```

### 2.3 Canonical Forms Lemma

```
Lemma (Canonical Forms):
    If âˆ… âŠ¢ v : Ï„â‚ â†’ Ï„â‚‚ and v is a value, then v = Î»x:Ï„â‚. e for some e.
    If âˆ… âŠ¢ v : Bool and v is a value, then v = true or v = false.
    If âˆ… âŠ¢ v : Int and v is a value, then v = n for some integer n.
    ...
```

### 2.4 Substitution Lemma

```
Lemma (Substitution):
    If Î“, x : Ï„' âŠ¢ e : Ï„ and Î“ âŠ¢ v : Ï„',
    then Î“ âŠ¢ [x â†¦ v]e : Ï„.

Proof by induction on typing of e.
```

---

## 3. Semantic Type Soundness

### 3.1 Limitations of Syntactic Approach

Syntactic soundness struggles with:
- Recursive types (need coinduction)
- General references (mutable state)
- Concurrency (shared memory)
- Higher-order state
- Foreign function interfaces
- Unsafe escape hatches

### 3.2 Logical Relations

Logical relations define type meaning semantically:

```
âŸ¦Ï„âŸ§ = { v | v "behaves like" type Ï„ }

For STLC:
    âŸ¦IntâŸ§ = { n | n is an integer }
    âŸ¦BoolâŸ§ = { true, false }
    âŸ¦Ï„â‚ â†’ Ï„â‚‚âŸ§ = { Î»x. e | âˆ€v âˆˆ âŸ¦Ï„â‚âŸ§. [x â†¦ v]e âˆˆ âŸ¦Ï„â‚‚âŸ§ }
```

**Problem**: Function case is not well-founded for recursive types.

### 3.3 Step-Indexed Logical Relations

Solution: Index relations by "steps remaining":

```
âŸ¦Ï„âŸ§â‚™ = values that behave like Ï„ for n more steps

âŸ¦IntâŸ§â‚™ = { n | n is an integer }
âŸ¦Ï„â‚ â†’ Ï„â‚‚âŸ§â‚™ = { Î»x. e | âˆ€k < n. âˆ€v âˆˆ âŸ¦Ï„â‚âŸ§â‚–. 
                        if [x â†¦ v]e â†’áµ v' then v' âˆˆ âŸ¦Ï„â‚‚âŸ§â‚™â‚‹â‚– }
```

**Key insight**: Require fewer steps in recursive calls.

### 3.4 Kripke Logical Relations

For state-dependent types, use possible worlds:

```
World W = (heap typing, invariants)

âŸ¦Ï„âŸ§áµ‚ = values that behave like Ï„ in world W

Semantic typing: Î“ âŠ¨ e : Ï„ iff
    âˆ€W, Î³ âˆˆ âŸ¦Î“âŸ§áµ‚. Î³(e) âˆˆ âŸ¦Ï„âŸ§áµ‚
```

### 3.5 Iris: Higher-Order Separation Logic

Iris provides a framework for semantic soundness:

```
Key concepts:
- Propositions: iProp (predicates over resources)
- Resources: ownership, invariants, protocols
- Modalities: â–· (later), â–¡ (persistent), â—‡ (eventually)

Type interpretation in Iris:
    âŸ¦Ï„âŸ§ : iProp â†’ Val â†’ iProp
    
    âŸ¦IntâŸ§(P)(v) = âŒœv âˆˆ ZâŒ
    âŸ¦Ï„â‚ â†’ Ï„â‚‚âŸ§(P)(v) = â–¡(âˆ€w. âŸ¦Ï„â‚âŸ§(P)(w) -âˆ— WP (v w) {âŸ¦Ï„â‚‚âŸ§(P)})
```

---

## 4. Soundness for Advanced Features

### 4.1 Polymorphism

**System F Progress and Preservation:**

```
Types:       Ï„ ::= Î± | Ï„â‚ â†’ Ï„â‚‚ | âˆ€Î±. Ï„
Terms:       e ::= ... | Î›Î±. e | e [Ï„]

Progress for type application:
    If âˆ… âŠ¢ e [Ï„] : Ï„' and e is a value:
        By canonical forms, e = Î›Î±. e' for some e'
        e [Ï„] â†’ [Î± â†¦ Ï„]e'
        
Preservation for type application:
    If Î“ âŠ¢ (Î›Î±. e) [Ï„] : [Î± â†¦ Ï„]Ï„' and (Î›Î±. e) [Ï„] â†’ [Î± â†¦ Ï„]e:
        By inversion, Î“, Î± âŠ¢ e : Ï„'
        By type substitution lemma, Î“ âŠ¢ [Î± â†¦ Ï„]e : [Î± â†¦ Ï„]Ï„'
```

**Parametricity**: Polymorphic programs can't inspect type parameters.

### 4.2 Recursive Types

**Equi-recursive types**: Î¼Î±.Ï„ = [Î± â†¦ Î¼Î±.Ï„]Ï„

```
Challenge: Infinite unfolding

Solution (step-indexing):
    âŸ¦Î¼Î±.Ï„âŸ§â‚™ = { v | âˆ€k < n. unfold(v) âˆˆ âŸ¦[Î± â†¦ Î¼Î±.Ï„]Ï„âŸ§â‚– }
    
The step index decreases on unfolding, ensuring well-foundedness.
```

**Iso-recursive types**: Explicit fold/unfold.

```
Î“ âŠ¢ e : [Î± â†¦ Î¼Î±.Ï„]Ï„           Î“ âŠ¢ e : Î¼Î±.Ï„
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€      â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ fold e : Î¼Î±.Ï„              Î“ âŠ¢ unfold e : [Î± â†¦ Î¼Î±.Ï„]Ï„
```

### 4.3 Mutable References

**Typing:**
```
Î“ âŠ¢ e : Ï„                 Î“ âŠ¢ e : Ref Ï„        Î“ âŠ¢ eâ‚ : Ref Ï„  Î“ âŠ¢ eâ‚‚ : Ï„
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€           â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€      â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ ref e : Ref Ï„         Î“ âŠ¢ !e : Ï„           Î“ âŠ¢ eâ‚ := eâ‚‚ : Unit
```

**Challenge**: Preservation requires heap typing.

```
Configuration: (H, e) where H is heap, e is expression

Extended preservation:
    If Î£ âŠ¢ H and Î£; âˆ… âŠ¢ e : Ï„ and (H, e) â†’ (H', e'),
    then âˆƒÎ£' âŠ‡ Î£. Î£' âŠ¢ H' and Î£'; âˆ… âŠ¢ e' : Ï„
```

### 4.4 Subtyping

**Subsumption rule:**
```
Î“ âŠ¢ e : Ï„â‚    Ï„â‚ <: Ï„â‚‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : Ï„â‚‚
```

**Soundness requires**:
- Subtyping is transitive and reflexive
- Subsumption preserves well-typedness

**Coercive vs Non-coercive subtyping**:
- Non-coercive: Values unchanged, just different view
- Coercive: Runtime representation may change

### 4.5 GADTs

```haskell
data Expr a where
    LitInt :: Int -> Expr Int
    LitBool :: Bool -> Expr Bool
    Add :: Expr Int -> Expr Int -> Expr Int
```

**Soundness challenge**: Pattern matching introduces local type equalities.

```
eval :: Expr a -> a
eval (LitInt n) = n    -- Here we know a ~ Int
eval (Add e1 e2) = eval e1 + eval e2
```

**Solution**: Track type equalities in context.
```
Î“; Î” âŠ¢ e : Ï„   where Î” = set of type equalities

Pattern match on (LitInt n):
    Î”' = Î” âˆª {a ~ Int}
    Check body under Î”'
```

### 4.6 Linear Types

**Linear typing judgment:**
```
Î“; Î” âŠ¢ e : Ï„   where Î” contains linear variables (used exactly once)
```

**Linear soundness**: Each linear resource consumed exactly once.

```
Progress (linear):
    Same as standard, but also verify linear resources available
    
Preservation (linear):
    If Î“; Î” âŠ¢ e : Ï„ and e â†’ e',
    then âˆƒÎ”' âŠ† Î”. Î“; Î”' âŠ¢ e' : Ï„
    (Linear resources may be consumed by reduction)
```

**Semantic approach (Iris)**:
```
âŸ¦A âŠ¸ BâŸ§(v) = â–¡(âˆ€w. âŸ¦AâŸ§(w) -âˆ— WP (v w) {âŸ¦BâŸ§})

-âˆ— is separating implication: consuming the resource
```

### 4.7 Effect Systems

**Effect typing:**
```
Î“ âŠ¢ e : Ï„ ! Îµ   (e has type Ï„ and may perform effects Îµ)
```

**Effect safety**: Effects in Îµ are the only effects that occur.

```
Theorem (Effect Safety):
    If âˆ… âŠ¢ e : Ï„ ! Îµ and e â†’* v,
    then all effects performed during reduction are in Îµ.
    
Proof: By progress + preservation for effect typing.
```

---

## 5. Mechanized Proofs

### 5.1 Why Mechanize?

| Benefit | Description |
|---------|-------------|
| Certainty | Machine-checked, no human error |
| Maintenance | Proofs updated with type system changes |
| Documentation | Proofs serve as formal specification |
| Exploration | Find edge cases via proof attempts |

### 5.2 Proof Assistants

**Coq:**
```coq
Theorem progress : forall e T,
  has_type empty e T ->
  value e \/ exists e', step e e'.
Proof.
  intros e T H.
  induction H; auto.
  - (* application case *)
    right. destruct IHhas_type1 as [Hv1 | [e1' Hs1]].
    + destruct IHhas_type2 as [Hv2 | [e2' Hs2]].
      * inversion H; subst.
        exists ([x := e2] t). apply ST_AppAbs. auto.
      * exists (app e1 e2'). apply ST_App2. auto. auto.
    + exists (app e1' e2). apply ST_App1. auto.
Qed.
```

**Agda:**
```agda
progress : âˆ€ {e T} â†’ âˆ… âŠ¢ e âˆ¶ T â†’ Value e âŠŽ âˆƒ[ e' ] (e âŸ¶ e')
progress (âŠ¢Î» _) = injâ‚ V-Î»
progress (âŠ¢Â· âŠ¢eâ‚ âŠ¢eâ‚‚) with progress âŠ¢eâ‚ | progress âŠ¢eâ‚‚
... | injâ‚‚ (eâ‚' , stepâ‚) | _ = injâ‚‚ (eâ‚' Â· _ , Î¾-Â·â‚ stepâ‚)
... | injâ‚ vâ‚ | injâ‚‚ (eâ‚‚' , stepâ‚‚) = injâ‚‚ (_ Â· eâ‚‚' , Î¾-Â·â‚‚ vâ‚ stepâ‚‚)
... | injâ‚ (V-Î») | injâ‚ vâ‚‚ = injâ‚‚ (_ , Î²-Î» vâ‚‚)
```

**Lean 4:**
```lean
theorem progress {e : Expr} {T : Ty} (h : HasType .empty e T) : 
    Value e âˆ¨ âˆƒ e', Step e e' := by
  induction h with
  | lam => left; exact Value.lam
  | app h1 h2 ih1 ih2 =>
    rcases ih1 with hv1 | âŸ¨e1', hs1âŸ©
    Â· rcases ih2 with hv2 | âŸ¨e2', hs2âŸ©
      Â· cases hv1; right; exact âŸ¨_, Step.beta hv2âŸ©
      Â· right; exact âŸ¨_, Step.app2 hv1 hs2âŸ©
    Â· right; exact âŸ¨_, Step.app1 hs1âŸ©
```

### 5.3 POPLmark Challenge

The POPLmark challenge (2005) standardized benchmarks:

```
Part 1A: Transitivity of subtyping
Part 1B: Weakening and substitution
Part 2A: Progress and preservation for F<:
Part 2B: Preservation with reduction under binders

Challenges:
- Variable binding (de Bruijn, HOAS, nominal, locally nameless)
- Substitution lemmas
- Induction principles for mutually recursive judgments
```

### 5.4 Binding Representations

| Approach | Pros | Cons |
|----------|------|------|
| Named | Intuitive | Alpha-equivalence complex |
| de Bruijn | Alpha-free | Hard to read |
| Locally nameless | Best of both | Some complexity |
| HOAS | Substitution free | Exotic terms possible |
| Nominal | Intuitive + rigorous | Requires special logic |

**Locally nameless example:**
```coq
Inductive term : Set :=
  | bvar : nat -> term        (* bound variable, de Bruijn index *)
  | fvar : atom -> term       (* free variable, named *)
  | abs : term -> term        (* Î». body *)
  | app : term -> term -> term.

(* Opening: replace bound var 0 with free var x *)
Fixpoint open_rec (k : nat) (x : atom) (t : term) : term :=
  match t with
  | bvar n => if k =? n then fvar x else bvar n
  | fvar y => fvar y
  | abs t' => abs (open_rec (S k) x t')
  | app t1 t2 => app (open_rec k x t1) (open_rec k x t2)
  end.
```

### 5.5 Notable Mechanized Proofs

| System | Proof Assistant | Features |
|--------|-----------------|----------|
| CompCert | Coq | Verified C compiler |
| CakeML | HOL4 | Verified ML compiler |
| RustBelt | Coq/Iris | Rust type system soundness |
| Oxide | Coq | Rust ownership soundness |
| F* | F* (self) | Effectful verification |
| Stacked Borrows | Miri/Coq | Rust aliasing model |

---

## 6. Soundness for Security Types

### 6.1 Information Flow Soundness

**Noninterference**: High-security inputs don't affect low-security outputs.

```
Theorem (Noninterference):
    If âˆ… âŠ¢ e : Ï„ @ Low and
       e evaluates to v under high-security context Hâ‚ and
       e evaluates to v' under high-security context Hâ‚‚,
    then v = v'.
    
Interpretation: Low-labeled results are independent of high inputs.
```

**Proof approach**: Logical relation indexed by security levels.

```
âŸ¦Ï„ @ LâŸ§ = { (vâ‚, vâ‚‚) | vâ‚ and vâ‚‚ are L-equivalent }

L-equivalence:
    - For L = Low: vâ‚ = vâ‚‚ (must be identical)
    - For L = High: any (vâ‚, vâ‚‚) (can differ)
```

### 6.2 Capability Safety

**Capability soundness**: Objects only accessible via explicit capabilities.

```
Theorem (Capability Safety):
    If âˆ… âŠ¢ e : Ï„ with capability set C and
       e â†’* e' performs operation requiring capability c,
    then c âˆˆ C.

Interpretation: No capability amplification.
```

**Object capability model:**
```
âŸ¦Cap câŸ§ = { v | v grants capability c }
âŸ¦Obj Ï„ with CâŸ§ = { v | v.methods require only capabilities in C }
```

### 6.3 Linear Resource Safety

**Linear soundness**: Resources used exactly once.

```
Theorem (Linear Safety):
    If âˆ…;Î” âŠ¢ e : Ï„ where Î” = {xâ‚ : Aâ‚, ..., xâ‚™ : Aâ‚™} (linear)
    and e â†’* v,
    then each xáµ¢ was consumed exactly once during reduction.
```

**Semantic interpretation in Iris:**
```
âŸ¦A âŠ¸ BâŸ§ = Î»P, v. â–¡(âˆ€w. âŸ¦AâŸ§(P, w) -âˆ— WP (v w) {u. âŸ¦BâŸ§(P, u)})

Key: -âˆ— (magic wand / separating implication) ensures linear use
```

### 6.4 Session Type Safety

**Session soundness**: Communication follows protocol.

```
Theorem (Session Fidelity):
    If âˆ… âŠ¢ (P | Q) : ok with session type S between P and Q,
    then every communication between P and Q follows S.

Theorem (Progress for Sessions):
    If âˆ… âŠ¢ (P | Q) : ok, then either:
    1. P and Q have both terminated, or
    2. (P | Q) can take a step
    
(No deadlock for well-typed sessions)
```

---

## 7. RustBelt: Case Study

### 7.1 Overview

RustBelt (2018) provides semantic soundness for Rust's type system:

- Handles ownership, borrowing, lifetimes
- Accounts for interior mutability (Cell, RefCell, Mutex)
- Verifies unsafe code via semantic typing
- Built on Iris separation logic

### 7.2 Key Ideas

**Lifetime logic:**
```
Lifetime tokens: [Î±] represents ownership of lifetime Î±
Borrows: &Îº Ï„ requires [Îº] to access

Semantic interpretation:
    âŸ¦&'a Ï„âŸ§(Îº) = âˆƒÎ¹. &Îº â†¦ Î¹ âˆ— â–·âŸ¦Ï„âŸ§(Î¹)
    
    (Shared reference contains a fraction of the pointee)
```

**Unsafe code verification:**
```
For unsafe { block }:
    1. Assume semantic typing of safe API
    2. Prove block maintains invariants
    3. Conclude safe API is actually safe
```

### 7.3 Example: Mutex

```rust
pub struct Mutex<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}
```

**Semantic typing in Iris:**
```
âŸ¦Mutex<T>âŸ§ = âˆƒÎ¹. MutexInv(Î¹) âˆ— MutexToken(Î¹)

MutexInv(Î¹) = inv(Î¹, âˆƒb. locked â†¦ b âˆ— if b then emp else âŸ¦TâŸ§)
MutexToken(Î¹) = persistent token for Î¹
```

**Proof obligation for `lock`:**
```
{ MutexInv(Î¹) âˆ— MutexToken(Î¹) }
  lock()
{ MutexGuard âˆ— âŸ¦TâŸ§ }
```

---

## 8. Proving Soundness for TERAS-LANG

### 8.1 Required Theorems

```
Core Safety:
â”œâ”€â”€ Progress: Well-typed terms step or are values
â”œâ”€â”€ Preservation: Typing preserved under reduction
â””â”€â”€ Type Safety: Well-typed terms don't get stuck

Security Safety:
â”œâ”€â”€ Noninterference: High inputs don't affect low outputs
â”œâ”€â”€ Capability Safety: No capability amplification
â”œâ”€â”€ Linear Safety: Resources used exactly once
â””â”€â”€ Effect Safety: Only declared effects occur

Advanced Safety:
â”œâ”€â”€ Session Fidelity: Protocols followed
â”œâ”€â”€ State Machine Safety: Valid transitions only
â””â”€â”€ Termination: Total functions terminate
```

### 8.2 Proof Strategy

```
Recommended approach: Semantic soundness via Iris

1. Define semantic interpretation âŸ¦Ï„âŸ§ for each type
2. Prove fundamental theorem: syntactic typing implies semantic
3. Derive safety properties from semantic interpretation

Advantages:
- Handles mutable state
- Extensible to new features
- Supports unsafe escape hatches
- Handles concurrency
```

### 8.3 Semantic Interpretation Sketch

```
Base types:
    âŸ¦IntâŸ§(P, v) = âŒœv âˆˆ ZâŒ
    âŸ¦BoolâŸ§(P, v) = âŒœv âˆˆ {true, false}âŒ

Functions:
    âŸ¦A â†’ BâŸ§(P, v) = â–¡(âˆ€w. âŸ¦AâŸ§(P, w) -âˆ— WP (v w) {u. âŸ¦BâŸ§(P, u)})

Linear functions:
    âŸ¦A âŠ¸ BâŸ§(P, v) = âˆ€w. âŸ¦AâŸ§(P, w) -âˆ— WP (v w) {u. âŸ¦BâŸ§(P, u)}
    (No â–¡, so can only use once)

Security labels:
    âŸ¦A @ LâŸ§(P, v) = âŸ¦AâŸ§(P, v) âˆ— label(v, L)
    
Capabilities:
    âŸ¦Cap câŸ§(P, v) = cap(v, c)
    
Effects:
    âŸ¦A -[Îµ]â†’ BâŸ§(P, v) = â–¡(âˆ€w. âŸ¦AâŸ§(P, w) -âˆ— 
                           WP_Îµ (v w) {u. âŸ¦BâŸ§(P, u)})
    (WP_Îµ restricts to effects in Îµ)
```

### 8.4 Fundamental Theorem

```
Theorem (Fundamental):
    If Î“ âŠ¢ e : Ï„, then Î“ âŠ¨ e : Ï„
    
Where:
    Î“ âŠ¨ e : Ï„ = âˆ€P, Î³. âŸ¦Î“âŸ§(P, Î³) âŠ¢ WP (Î³(e)) {v. âŸ¦Ï„âŸ§(P, v)}
    
Proof: By induction on typing derivation.
```

---

## 9. Mechanization for TERAS-LANG

### 9.1 Recommended Tools

| Tool | Use Case | Effort |
|------|----------|--------|
| Coq + Iris | Full semantic soundness | High |
| Agda | Syntactic soundness, total proofs | Medium |
| Lean 4 | Modern, good automation | Medium |
| F* | Effects, refinement types | Medium |

### 9.2 Proof Development Roadmap

```
Phase 1: Core Language (8 weeks)
â”œâ”€â”€ Define syntax and operational semantics
â”œâ”€â”€ Define type system
â”œâ”€â”€ Prove progress and preservation
â””â”€â”€ Mechanize in Coq/Agda/Lean

Phase 2: Polymorphism (4 weeks)
â”œâ”€â”€ Add System F-style polymorphism
â”œâ”€â”€ Prove parametricity
â””â”€â”€ Extend mechanization

Phase 3: Linear Types (6 weeks)
â”œâ”€â”€ Add linear/affine/relevant modalities
â”œâ”€â”€ Prove linear safety
â””â”€â”€ Semantic interpretation in Iris

Phase 4: Effects (4 weeks)
â”œâ”€â”€ Add effect system
â”œâ”€â”€ Prove effect safety
â””â”€â”€ Integrate with semantics

Phase 5: Security (6 weeks)
â”œâ”€â”€ Add security labels
â”œâ”€â”€ Prove noninterference
â”œâ”€â”€ Add capabilities, prove safety

Phase 6: Advanced (6 weeks)
â”œâ”€â”€ GADTs and type families
â”œâ”€â”€ Session types
â”œâ”€â”€ State machines

Total: 34 weeks
```

### 9.3 Proof Patterns

**Pattern: Logical Relations for Polymorphism**
```coq
(* Parametricity: polymorphic functions are uniform *)
Fixpoint V (T : ty) (Ï : tyvar -> relation) : relation :=
  match T with
  | TVar X => Ï X
  | TArrow T1 T2 => fun v1 v2 =>
      forall w1 w2, V T1 Ï w1 w2 -> 
        E T2 Ï (App v1 w1) (App v2 w2)
  | TForall T => fun v1 v2 =>
      forall R : relation, 
        E T (extend Ï R) (TApp v1) (TApp v2)
  end
```

**Pattern: Step-Indexing for Recursion**
```coq
(* Step-indexed logical relation *)
Fixpoint V (n : nat) (T : ty) : val -> Prop :=
  match n with
  | 0 => fun _ => True  (* vacuously true at 0 *)
  | S n' => 
      match T with
      | TArrow T1 T2 => fun v =>
          forall k w, k < n' -> V k T1 w -> 
            safe_for (n' - k) T2 (App v w)
      | ...
      end
  end
```

---

## 10. Integration with TERAS Architecture

### 10.1 Safety Properties by Product

| Product | Required Safety Properties |
|---------|---------------------------|
| MENARA | Permission safety, IFC for mobile |
| GAPURA | Request/response type safety, effect safety |
| ZIRAH | Capability safety, process isolation |
| BENTENG | Identity verification correctness |
| SANDI | Cryptographic type safety, key linearity |

### 10.2 Proof Dependencies

```
TERAS-LANG Soundness Proof Structure:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
                    [Type Safety]
                         â”‚
        â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
        â”‚                â”‚                â”‚
   [Progress]      [Preservation]   [Canonical Forms]
        â”‚                â”‚                â”‚
        â–¼                â–¼                â–¼
   [Effect         [Substitution    [Value
    Safety]         Lemma]           Characterization]
        â”‚                â”‚
        â–¼                â–¼
   [Capability     [Label Flow
    Safety]         Safety]
        â”‚                â”‚
        â–¼                â–¼
   [Noninterference] [Linear Safety]
        â”‚                â”‚
        â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”´â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
                                            â–¼
                              [Security Soundness]
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

---

## 11. Summary and Recommendations

### 11.1 Key Findings

| Approach | Complexity | Coverage | Extensibility |
|----------|------------|----------|---------------|
| Syntactic | Low | Core features | Limited |
| Step-indexed | Medium | Recursive types | Good |
| Semantic (Iris) | High | All features | Excellent |

### 11.2 Recommendations for TERAS-LANG

1. **Use semantic soundness** (Iris-based) for full coverage
2. **Start with syntactic proofs** for core language
3. **Mechanize all proofs** in Coq/Lean
4. **Prove security properties** alongside type safety
5. **Document proof assumptions** for unsafe code

### 11.3 Critical Security Proofs

```
Must prove:
â”œâ”€â”€ Noninterference (IFC soundness)
â”œâ”€â”€ Capability safety (no amplification)
â”œâ”€â”€ Linear resource safety (exactly once)
â”œâ”€â”€ Effect safety (only declared effects)
â”œâ”€â”€ Session fidelity (protocols followed)
â””â”€â”€ State machine safety (valid transitions)

These ensure TERAS security guarantees are mathematically verified.
```

---

## 12. References

1. Wright, A., & Felleisen, M. (1994). "A Syntactic Approach to Type Soundness"
2. Pierce, B. C. (2002). "Types and Programming Languages"
3. Ahmed, A. (2006). "Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types"
4. Jung, R., et al. (2018). "RustBelt: Securing the Foundations of the Rust Programming Language"
5. Jung, R., et al. (2018). "Iris from the Ground Up"
6. Dreyer, D., et al. (2011). "Logical Step-Indexed Logical Relations"
7. Aydemir, B., et al. (2005). "The POPLmark Challenge"
8. Harper, R. (2016). "Practical Foundations for Programming Languages"
9. Krishnaswami, N. (2009). "Verifying Higher-Order Imperative Programs with Higher-Order Separation Logic"
10. Sabelfeld, A., & Myers, A. (2003). "Language-Based Information-Flow Security"

---

*Survey document for TERAS-LANG research track. Comprehensive coverage of type system soundness proofs with security applications.*
