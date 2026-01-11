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
"Well-typed programs don't go wrong" — Robin Milner

Formally:
    If ∅ ⊢ e : τ and e →* v, then v is a value of type τ
    If ∅ ⊢ e : τ, then e does not get stuck
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
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
1978    │ Milner: "Well-typed programs don't go wrong"
1981    │ Wright: Syntactic approach foundations
1992    │ Harper: Progress + Preservation formulation
1994    │ Wright & Felleisen: Syntactic soundness for ML
1997    │ Appel & McAllester: Indexed logical relations
2001    │ Ahmed: Step-indexed logical relations
2007    │ Dreyer: Recursive types with step-indexing
2009    │ POPLmark: Mechanization challenge
2010    │ Iris: Higher-order concurrent separation logic
2017    │ RustBelt: Rust soundness in Iris
2019    │ Stacked Borrows: Rust aliasing model
2020+   │ Semantic approaches dominate research
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
```

---

## 2. Syntactic Type Soundness

### 2.1 Progress and Preservation

The classic formulation splits soundness into two properties:

**Progress**: Well-typed closed terms are either values or can step.
```
If ∅ ⊢ e : τ, then either:
    1. e is a value, or
    2. ∃e'. e → e'
```

**Preservation (Subject Reduction)**: Typing is preserved under reduction.
```
If Γ ⊢ e : τ and e → e', then Γ ⊢ e' : τ
```

**Type Safety**: Combining these by induction on execution:
```
Theorem (Type Safety):
    If ∅ ⊢ e : τ, then e does not get stuck.
    
Proof: By induction on the length of reduction sequence.
    Base: e is the original term, which is well-typed.
    Step: If e → e' and e is well-typed:
        - By Progress, e is a value (done) or steps to e'
        - By Preservation, e' is well-typed
        - Continue inductively
```

### 2.2 Simply Typed Lambda Calculus (STLC)

**Syntax:**
```
Types:       τ ::= α | τ₁ → τ₂
Terms:       e ::= x | λx:τ. e | e₁ e₂
Values:      v ::= λx:τ. e
Contexts:    Γ ::= ∅ | Γ, x : τ
```

**Typing Rules:**
```
    (x : τ) ∈ Γ          Γ, x : τ₁ ⊢ e : τ₂
    ───────────────      ─────────────────────────
    Γ ⊢ x : τ            Γ ⊢ λx:τ₁. e : τ₁ → τ₂

    Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
    ─────────────────────────────────────
    Γ ⊢ e₁ e₂ : τ₂
```

**Operational Semantics (Call-by-Value):**
```
    e₁ → e₁'                    e₂ → e₂'
    ────────────────            ─────────────────
    e₁ e₂ → e₁' e₂              v e₂ → v e₂'

    ────────────────────────────────────
    (λx:τ. e) v → [x ↦ v]e   (β-reduction)
```

**Progress Proof (STLC):**
```
Theorem: If ∅ ⊢ e : τ, then e is a value or ∃e'. e → e'.

Proof by induction on typing derivation:
    Case Var: Impossible (∅ has no bindings)
    
    Case Lam: e = λx:τ₁. e'
        e is a value. Done.
        
    Case App: e = e₁ e₂ with ∅ ⊢ e₁ : τ' → τ and ∅ ⊢ e₂ : τ'
        By IH on e₁: e₁ is a value or steps
            If e₁ steps to e₁': e₁ e₂ → e₁' e₂
            If e₁ is a value:
                By canonical forms, e₁ = λx:τ'. e₁'
                By IH on e₂: e₂ is a value or steps
                    If e₂ steps to e₂': (λx:τ'. e₁') e₂ → (λx:τ'. e₁') e₂'
                    If e₂ is a value v: (λx:τ'. e₁') v → [x ↦ v]e₁'
```

**Preservation Proof (STLC):**
```
Theorem: If Γ ⊢ e : τ and e → e', then Γ ⊢ e' : τ.

Proof by induction on typing derivation:
    Case App: e = e₁ e₂, need to show preservation for each reduction:
        
        Subcase e₁ → e₁':
            By IH, Γ ⊢ e₁' : τ' → τ
            Γ ⊢ e₂ : τ' (unchanged)
            By App rule, Γ ⊢ e₁' e₂ : τ
            
        Subcase e₂ → e₂':
            Similar
            
        Subcase (λx:τ'. e) v → [x ↦ v]e (β-reduction):
            Γ ⊢ λx:τ'. e : τ' → τ
            By inversion, Γ, x : τ' ⊢ e : τ
            Γ ⊢ v : τ'
            By substitution lemma, Γ ⊢ [x ↦ v]e : τ
```

### 2.3 Canonical Forms Lemma

```
Lemma (Canonical Forms):
    If ∅ ⊢ v : τ₁ → τ₂ and v is a value, then v = λx:τ₁. e for some e.
    If ∅ ⊢ v : Bool and v is a value, then v = true or v = false.
    If ∅ ⊢ v : Int and v is a value, then v = n for some integer n.
    ...
```

### 2.4 Substitution Lemma

```
Lemma (Substitution):
    If Γ, x : τ' ⊢ e : τ and Γ ⊢ v : τ',
    then Γ ⊢ [x ↦ v]e : τ.

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
⟦τ⟧ = { v | v "behaves like" type τ }

For STLC:
    ⟦Int⟧ = { n | n is an integer }
    ⟦Bool⟧ = { true, false }
    ⟦τ₁ → τ₂⟧ = { λx. e | ∀v ∈ ⟦τ₁⟧. [x ↦ v]e ∈ ⟦τ₂⟧ }
```

**Problem**: Function case is not well-founded for recursive types.

### 3.3 Step-Indexed Logical Relations

Solution: Index relations by "steps remaining":

```
⟦τ⟧ₙ = values that behave like τ for n more steps

⟦Int⟧ₙ = { n | n is an integer }
⟦τ₁ → τ₂⟧ₙ = { λx. e | ∀k < n. ∀v ∈ ⟦τ₁⟧ₖ. 
                        if [x ↦ v]e →ᵏ v' then v' ∈ ⟦τ₂⟧ₙ₋ₖ }
```

**Key insight**: Require fewer steps in recursive calls.

### 3.4 Kripke Logical Relations

For state-dependent types, use possible worlds:

```
World W = (heap typing, invariants)

⟦τ⟧ᵂ = values that behave like τ in world W

Semantic typing: Γ ⊨ e : τ iff
    ∀W, γ ∈ ⟦Γ⟧ᵂ. γ(e) ∈ ⟦τ⟧ᵂ
```

### 3.5 Iris: Higher-Order Separation Logic

Iris provides a framework for semantic soundness:

```
Key concepts:
- Propositions: iProp (predicates over resources)
- Resources: ownership, invariants, protocols
- Modalities: ▷ (later), □ (persistent), ◇ (eventually)

Type interpretation in Iris:
    ⟦τ⟧ : iProp → Val → iProp
    
    ⟦Int⟧(P)(v) = ⌜v ∈ Z⌝
    ⟦τ₁ → τ₂⟧(P)(v) = □(∀w. ⟦τ₁⟧(P)(w) -∗ WP (v w) {⟦τ₂⟧(P)})
```

---

## 4. Soundness for Advanced Features

### 4.1 Polymorphism

**System F Progress and Preservation:**

```
Types:       τ ::= α | τ₁ → τ₂ | ∀α. τ
Terms:       e ::= ... | Λα. e | e [τ]

Progress for type application:
    If ∅ ⊢ e [τ] : τ' and e is a value:
        By canonical forms, e = Λα. e' for some e'
        e [τ] → [α ↦ τ]e'
        
Preservation for type application:
    If Γ ⊢ (Λα. e) [τ] : [α ↦ τ]τ' and (Λα. e) [τ] → [α ↦ τ]e:
        By inversion, Γ, α ⊢ e : τ'
        By type substitution lemma, Γ ⊢ [α ↦ τ]e : [α ↦ τ]τ'
```

**Parametricity**: Polymorphic programs can't inspect type parameters.

### 4.2 Recursive Types

**Equi-recursive types**: μα.τ = [α ↦ μα.τ]τ

```
Challenge: Infinite unfolding

Solution (step-indexing):
    ⟦μα.τ⟧ₙ = { v | ∀k < n. unfold(v) ∈ ⟦[α ↦ μα.τ]τ⟧ₖ }
    
The step index decreases on unfolding, ensuring well-foundedness.
```

**Iso-recursive types**: Explicit fold/unfold.

```
Γ ⊢ e : [α ↦ μα.τ]τ           Γ ⊢ e : μα.τ
─────────────────────────      ────────────────────────────
Γ ⊢ fold e : μα.τ              Γ ⊢ unfold e : [α ↦ μα.τ]τ
```

### 4.3 Mutable References

**Typing:**
```
Γ ⊢ e : τ                 Γ ⊢ e : Ref τ        Γ ⊢ e₁ : Ref τ  Γ ⊢ e₂ : τ
───────────────           ───────────────      ─────────────────────────────
Γ ⊢ ref e : Ref τ         Γ ⊢ !e : τ           Γ ⊢ e₁ := e₂ : Unit
```

**Challenge**: Preservation requires heap typing.

```
Configuration: (H, e) where H is heap, e is expression

Extended preservation:
    If Σ ⊢ H and Σ; ∅ ⊢ e : τ and (H, e) → (H', e'),
    then ∃Σ' ⊇ Σ. Σ' ⊢ H' and Σ'; ∅ ⊢ e' : τ
```

### 4.4 Subtyping

**Subsumption rule:**
```
Γ ⊢ e : τ₁    τ₁ <: τ₂
────────────────────────
Γ ⊢ e : τ₂
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
Γ; Δ ⊢ e : τ   where Δ = set of type equalities

Pattern match on (LitInt n):
    Δ' = Δ ∪ {a ~ Int}
    Check body under Δ'
```

### 4.6 Linear Types

**Linear typing judgment:**
```
Γ; Δ ⊢ e : τ   where Δ contains linear variables (used exactly once)
```

**Linear soundness**: Each linear resource consumed exactly once.

```
Progress (linear):
    Same as standard, but also verify linear resources available
    
Preservation (linear):
    If Γ; Δ ⊢ e : τ and e → e',
    then ∃Δ' ⊆ Δ. Γ; Δ' ⊢ e' : τ
    (Linear resources may be consumed by reduction)
```

**Semantic approach (Iris)**:
```
⟦A ⊸ B⟧(v) = □(∀w. ⟦A⟧(w) -∗ WP (v w) {⟦B⟧})

-∗ is separating implication: consuming the resource
```

### 4.7 Effect Systems

**Effect typing:**
```
Γ ⊢ e : τ ! ε   (e has type τ and may perform effects ε)
```

**Effect safety**: Effects in ε are the only effects that occur.

```
Theorem (Effect Safety):
    If ∅ ⊢ e : τ ! ε and e →* v,
    then all effects performed during reduction are in ε.
    
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
progress : ∀ {e T} → ∅ ⊢ e ∶ T → Value e ⊎ ∃[ e' ] (e ⟶ e')
progress (⊢λ _) = inj₁ V-λ
progress (⊢· ⊢e₁ ⊢e₂) with progress ⊢e₁ | progress ⊢e₂
... | inj₂ (e₁' , step₁) | _ = inj₂ (e₁' · _ , ξ-·₁ step₁)
... | inj₁ v₁ | inj₂ (e₂' , step₂) = inj₂ (_ · e₂' , ξ-·₂ v₁ step₂)
... | inj₁ (V-λ) | inj₁ v₂ = inj₂ (_ , β-λ v₂)
```

**Lean 4:**
```lean
theorem progress {e : Expr} {T : Ty} (h : HasType .empty e T) : 
    Value e ∨ ∃ e', Step e e' := by
  induction h with
  | lam => left; exact Value.lam
  | app h1 h2 ih1 ih2 =>
    rcases ih1 with hv1 | ⟨e1', hs1⟩
    · rcases ih2 with hv2 | ⟨e2', hs2⟩
      · cases hv1; right; exact ⟨_, Step.beta hv2⟩
      · right; exact ⟨_, Step.app2 hv1 hs2⟩
    · right; exact ⟨_, Step.app1 hs1⟩
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
  | abs : term -> term        (* λ. body *)
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
    If ∅ ⊢ e : τ @ Low and
       e evaluates to v under high-security context H₁ and
       e evaluates to v' under high-security context H₂,
    then v = v'.
    
Interpretation: Low-labeled results are independent of high inputs.
```

**Proof approach**: Logical relation indexed by security levels.

```
⟦τ @ L⟧ = { (v₁, v₂) | v₁ and v₂ are L-equivalent }

L-equivalence:
    - For L = Low: v₁ = v₂ (must be identical)
    - For L = High: any (v₁, v₂) (can differ)
```

### 6.2 Capability Safety

**Capability soundness**: Objects only accessible via explicit capabilities.

```
Theorem (Capability Safety):
    If ∅ ⊢ e : τ with capability set C and
       e →* e' performs operation requiring capability c,
    then c ∈ C.

Interpretation: No capability amplification.
```

**Object capability model:**
```
⟦Cap c⟧ = { v | v grants capability c }
⟦Obj τ with C⟧ = { v | v.methods require only capabilities in C }
```

### 6.3 Linear Resource Safety

**Linear soundness**: Resources used exactly once.

```
Theorem (Linear Safety):
    If ∅;Δ ⊢ e : τ where Δ = {x₁ : A₁, ..., xₙ : Aₙ} (linear)
    and e →* v,
    then each xᵢ was consumed exactly once during reduction.
```

**Semantic interpretation in Iris:**
```
⟦A ⊸ B⟧ = λP, v. □(∀w. ⟦A⟧(P, w) -∗ WP (v w) {u. ⟦B⟧(P, u)})

Key: -∗ (magic wand / separating implication) ensures linear use
```

### 6.4 Session Type Safety

**Session soundness**: Communication follows protocol.

```
Theorem (Session Fidelity):
    If ∅ ⊢ (P | Q) : ok with session type S between P and Q,
    then every communication between P and Q follows S.

Theorem (Progress for Sessions):
    If ∅ ⊢ (P | Q) : ok, then either:
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
Lifetime tokens: [α] represents ownership of lifetime α
Borrows: &κ τ requires [κ] to access

Semantic interpretation:
    ⟦&'a τ⟧(κ) = ∃ι. &κ ↦ ι ∗ ▷⟦τ⟧(ι)
    
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
⟦Mutex<T>⟧ = ∃ι. MutexInv(ι) ∗ MutexToken(ι)

MutexInv(ι) = inv(ι, ∃b. locked ↦ b ∗ if b then emp else ⟦T⟧)
MutexToken(ι) = persistent token for ι
```

**Proof obligation for `lock`:**
```
{ MutexInv(ι) ∗ MutexToken(ι) }
  lock()
{ MutexGuard ∗ ⟦T⟧ }
```

---

## 8. Proving Soundness for TERAS-LANG

### 8.1 Required Theorems

```
Core Safety:
├── Progress: Well-typed terms step or are values
├── Preservation: Typing preserved under reduction
└── Type Safety: Well-typed terms don't get stuck

Security Safety:
├── Noninterference: High inputs don't affect low outputs
├── Capability Safety: No capability amplification
├── Linear Safety: Resources used exactly once
└── Effect Safety: Only declared effects occur

Advanced Safety:
├── Session Fidelity: Protocols followed
├── State Machine Safety: Valid transitions only
└── Termination: Total functions terminate
```

### 8.2 Proof Strategy

```
Recommended approach: Semantic soundness via Iris

1. Define semantic interpretation ⟦τ⟧ for each type
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
    ⟦Int⟧(P, v) = ⌜v ∈ Z⌝
    ⟦Bool⟧(P, v) = ⌜v ∈ {true, false}⌝

Functions:
    ⟦A → B⟧(P, v) = □(∀w. ⟦A⟧(P, w) -∗ WP (v w) {u. ⟦B⟧(P, u)})

Linear functions:
    ⟦A ⊸ B⟧(P, v) = ∀w. ⟦A⟧(P, w) -∗ WP (v w) {u. ⟦B⟧(P, u)}
    (No □, so can only use once)

Security labels:
    ⟦A @ L⟧(P, v) = ⟦A⟧(P, v) ∗ label(v, L)
    
Capabilities:
    ⟦Cap c⟧(P, v) = cap(v, c)
    
Effects:
    ⟦A -[ε]→ B⟧(P, v) = □(∀w. ⟦A⟧(P, w) -∗ 
                           WP_ε (v w) {u. ⟦B⟧(P, u)})
    (WP_ε restricts to effects in ε)
```

### 8.4 Fundamental Theorem

```
Theorem (Fundamental):
    If Γ ⊢ e : τ, then Γ ⊨ e : τ
    
Where:
    Γ ⊨ e : τ = ∀P, γ. ⟦Γ⟧(P, γ) ⊢ WP (γ(e)) {v. ⟦τ⟧(P, v)}
    
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
├── Define syntax and operational semantics
├── Define type system
├── Prove progress and preservation
└── Mechanize in Coq/Agda/Lean

Phase 2: Polymorphism (4 weeks)
├── Add System F-style polymorphism
├── Prove parametricity
└── Extend mechanization

Phase 3: Linear Types (6 weeks)
├── Add linear/affine/relevant modalities
├── Prove linear safety
└── Semantic interpretation in Iris

Phase 4: Effects (4 weeks)
├── Add effect system
├── Prove effect safety
└── Integrate with semantics

Phase 5: Security (6 weeks)
├── Add security labels
├── Prove noninterference
├── Add capabilities, prove safety

Phase 6: Advanced (6 weeks)
├── GADTs and type families
├── Session types
├── State machines

Total: 34 weeks
```

### 9.3 Proof Patterns

**Pattern: Logical Relations for Polymorphism**
```coq
(* Parametricity: polymorphic functions are uniform *)
Fixpoint V (T : ty) (ρ : tyvar -> relation) : relation :=
  match T with
  | TVar X => ρ X
  | TArrow T1 T2 => fun v1 v2 =>
      forall w1 w2, V T1 ρ w1 w2 -> 
        E T2 ρ (App v1 w1) (App v2 w2)
  | TForall T => fun v1 v2 =>
      forall R : relation, 
        E T (extend ρ R) (TApp v1) (TApp v2)
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
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                    [Type Safety]
                         │
        ┌────────────────┼────────────────┐
        │                │                │
   [Progress]      [Preservation]   [Canonical Forms]
        │                │                │
        ▼                ▼                ▼
   [Effect         [Substitution    [Value
    Safety]         Lemma]           Characterization]
        │                │
        ▼                ▼
   [Capability     [Label Flow
    Safety]         Safety]
        │                │
        ▼                ▼
   [Noninterference] [Linear Safety]
        │                │
        └────────────────┴──────────────────┐
                                            ▼
                              [Security Soundness]
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
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
├── Noninterference (IFC soundness)
├── Capability safety (no amplification)
├── Linear resource safety (exactly once)
├── Effect safety (only declared effects)
├── Session fidelity (protocols followed)
└── State machine safety (valid transitions)

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
