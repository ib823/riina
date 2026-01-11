# TERAS-LANG Research Survey C-02: Security Type Systems

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C02-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-02 |
| Domain | C: Information Flow Control |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Security type systems extend conventional type systems to track and enforce information flow policies. This survey covers typing rules, subtyping, polymorphism over security labels, and the integration of security types with dependent and refinement types for TERAS.

---

## Part 1: Security Type Foundations

### 1.1 Labeled Types

```
Security Type Syntax:

τ_sec ::= τ^L              -- base type with label
        | τ₁^L → τ₂^L'     -- function type with labels
        | Ref(τ^L)         -- reference with label
        | (τ₁^L₁, τ₂^L₂)   -- product with labels

Examples:
    int^Secret           -- secret integer
    string^Public        -- public string
    (int^H → int^L)      -- function H to L (potential leak)
```

### 1.2 Label Polymorphism

```
Polymorphism over labels:

∀L. τ^L → τ^L    -- Identity preserving label
∀L₁ L₂. L₁ ⊑ L₂ ⇒ τ^L₁ → τ^L₂  -- Upgrade function

Example:
    id : ∀L. int^L → int^L
    id(secret)  : int^Secret
    id(public)  : int^Public
```

### 1.3 PC (Program Counter) Label

```
PC Label: Security context of current execution

Purpose: Prevent implicit flows

Rule:
    Γ, pc ⊢ if e then c₁ else c₂
    requires: e : bool^L and pc' = pc ⊔ L
              c₁, c₂ typed under pc'

Example:
    pc = Low
    if secret_bool then    -- pc becomes High
        public := 1        -- ERROR: writing Low under pc=High
```

---

## Part 2: Typing Rules

### 2.1 Core Typing Judgments

```
Typing judgment: Γ; pc ⊢ e : τ^L

Γ = typing environment
pc = program counter label
e = expression
τ^L = labeled type

Soundness: Well-typed programs satisfy noninterference
```

### 2.2 Expression Typing

```
Variable:
    (x : τ^L) ∈ Γ
    ──────────────────
    Γ; pc ⊢ x : τ^L

Literal:
    ────────────────────────
    Γ; pc ⊢ n : int^⊥

Application:
    Γ; pc ⊢ e₁ : (τ₁^L₁ → τ₂^L₂)^L_f
    Γ; pc ⊢ e₂ : τ₁^L₁'
    L₁' ⊑ L₁    L_f ⊑ L₂
    ──────────────────────────────────
    Γ; pc ⊢ e₁ e₂ : τ₂^(L₂ ⊔ L_f)

Abstraction:
    Γ, x : τ₁^L₁; pc ⊢ e : τ₂^L₂
    ───────────────────────────────────────
    Γ; pc ⊢ λx.e : (τ₁^L₁ → τ₂^L₂)^pc
```

### 2.3 Command Typing

```
Assignment:
    Γ; pc ⊢ e : τ^L_e
    (x : Ref(τ^L_x)) ∈ Γ
    L_e ⊔ pc ⊑ L_x
    ────────────────────────────
    Γ; pc ⊢ x := e : cmd^(L_e ⊔ pc)

Sequence:
    Γ; pc ⊢ c₁ : cmd^L₁
    Γ; pc ⊢ c₂ : cmd^L₂
    ──────────────────────────────
    Γ; pc ⊢ c₁; c₂ : cmd^(L₁ ⊔ L₂)

Conditional:
    Γ; pc ⊢ e : bool^L
    Γ; pc ⊔ L ⊢ c₁ : cmd^L₁
    Γ; pc ⊔ L ⊢ c₂ : cmd^L₂
    ────────────────────────────────────
    Γ; pc ⊢ if e then c₁ else c₂ : cmd^(L ⊔ L₁ ⊔ L₂)

While:
    Γ; pc ⊢ e : bool^L
    Γ; pc ⊔ L ⊢ c : cmd^L'
    ────────────────────────────────
    Γ; pc ⊢ while e do c : cmd^(L ⊔ L')
```

---

## Part 3: Subtyping

### 3.1 Label Subtyping

```
Label subtyping: L₁ ⊑ L₂

Covariance in labeled types:
    L₁ ⊑ L₂
    ────────────────
    τ^L₁ <: τ^L₂

Contravariance in function domain (standard):
    τ₁' <: τ₁    τ₂ <: τ₂'    L₁' ⊑ L₁    L₂ ⊑ L₂'
    ─────────────────────────────────────────────────────
    (τ₁^L₁ → τ₂^L₂) <: (τ₁'^L₁' → τ₂'^L₂')
```

### 3.2 Reference Subtyping

```
References are INVARIANT in label:

    Ref(τ^L) <: Ref(τ^L)   -- only same label

NOT: Ref(τ^High) <: Ref(τ^Low)  -- would allow write
NOT: Ref(τ^Low) <: Ref(τ^High)  -- would allow read

Reason: References support both read and write
```

### 3.3 Subsumption Rule

```
Subsumption:
    Γ; pc ⊢ e : τ₁    τ₁ <: τ₂
    ────────────────────────────
    Γ; pc ⊢ e : τ₂

Allows implicit "upgrades" to higher labels.
```

---

## Part 4: Advanced Features

### 4.1 Dependent Security Labels

```
Labels dependent on values:

label_of : ∀a. a → Label
check : (x : τ^L) → {L ⊑ label_of(x)} → τ^(label_of(x))

Example:
    fn process(user: User) → Data^(user.clearance) {
        // Return type depends on user's clearance
    }
```

### 4.2 Refinement Types with Labels

```
Combining refinements and security:

{ x : int^L | x > 0 }^L'    -- Positive int, double labeled
                            -- L for content, L' for existence

Example:
    fn check_positive(n: {x: int^Secret | x > 0}) → bool^Public {
        true  // Reveals existence of positive, but not value
    }
```

### 4.3 First-Class Labels

```
Labels as values:

type Label = SecurityLevel

fn process_at_level(L: Label, data: int^L) → int^L {
    data + 1
}

// Runtime label operations
let current_label : Label = get_label(data)
if current_label ⊑ threshold then ...
```

---

## Part 5: Integrity Types

### 5.1 Dual to Confidentiality

```
Integrity Labels (I):

High Integrity: Trusted, validated
Low Integrity: Untrusted, tainted

Flow direction (opposite to confidentiality):
    Untrusted → Trusted  ✗  (could corrupt)
    Trusted → Untrusted  ✓  (allowed)
```

### 5.2 Combined Label

```
Combined Confidentiality + Integrity:

Label = (Confidentiality, Integrity)
      = (C, I)

Example:
    (Secret, Trusted)    -- Secret and trusted
    (Public, Untrusted)  -- Public but tainted
    (Secret, Untrusted)  -- Secret from untrusted source

Flow rule:
    (C₁, I₁) ⊑ (C₂, I₂) iff C₁ ⊑ C₂ and I₂ ⊑ I₁
```

### 5.3 Robust Declassification

```
Integrity protects declassification:

fn declassify(data: int^(Secret, Trusted)) → int^(Public, Trusted)
    where CurrentPrincipal: HasAuthority
{
    // Only trusted code can declassify
}

// Untrusted code cannot declassify:
fn bad_declassify(data: int^(Secret, Untrusted)) → int^(Public, _)
    // ERROR: Cannot declassify from untrusted source
```

---

## Part 6: Type Inference for Security

### 6.1 Constraint Generation

```
Generate label constraints during type inference:

infer(Γ, x := e):
    (τ_e, L_e, C_e) = infer(Γ, e)
    L_x = lookup(Γ, x)
    C = C_e ∪ {L_e ⊔ pc ⊑ L_x}
    return (cmd, L_e ⊔ pc, C)
```

### 6.2 Constraint Solving

```
Solving label constraints:

Constraints: { L₁ ⊑ L₂, L₂ ⊑ L₃, ... }

For lattice labels:
    - Compute transitive closure
    - Check consistency
    - Find minimal satisfying assignment

For DLM labels:
    - More complex (principals)
    - May require annotation
```

### 6.3 Principal Types

```
Principal security types:

For simple lattices: principal types exist
For DLM: may need annotations for principals

Example (inferred):
    fn id(x) = x
    // Inferred: ∀L. τ^L → τ^L
```

---

## Part 7: Exceptions and Control Flow

### 7.1 Exceptions as Implicit Flow

```
Problem: Exceptions leak information

if secret then throw() else ()
// Exception raised ⇔ secret is true!

Solution: Label exceptions

throw : ∀L. unit → τ ! Exception^L
catch : (unit → τ ! Exception^L) → (unit → τ) → τ

Constraint: Handler pc must be ⊒ L
```

### 7.2 Termination Channel

```
Termination leaks one bit:

while secret do skip

Non-termination ⇔ secret is true

Solutions:
1. TINI: Ignore (accept leak)
2. TSNI: Forbid secret-dependent loops
3. PSNI: Bound iterations
```

---

## Part 8: TERAS Security Types

### 8.1 Syntax

```rust
// Labeled type syntax
type Secret<T> = Labeled<SecretLevel, T>;
type Public<T> = Labeled<PublicLevel, T>;

// Function with labels
fn process(
    secret: int @ Secret,
    public: int @ Public
) -> int @ Secret {
    secret + public  // Result is Secret (join)
}

// Label polymorphism
fn identity<L: Label>(x: int @ L) -> int @ L {
    x
}
```

### 8.2 Integration with Effects

```rust
// Security effect
effect Security {
    label<L, T>(value: T) -> T @ L,
    unlabel<L, T>(labeled: T @ L) -> T @ {pc: L},
    declassify<L1, L2, T>(value: T @ L1) -> T @ L2
        where CurrentPrincipal: CanDeclassify<L1, L2>
}

// Coeffect for clearance
fn read_secret() -[IO]-> SecretData 
    @ {Clearance::Secret}  // Requires Secret clearance
```

### 8.3 Product Integration

```rust
// MENARA (Mobile)
type SensitiveLocation = Location @ PrivacySensitive;
type UserCredentials = Credentials @ Secret;

// GAPURA (WAF)
type RequestData = Bytes @ Untrusted;
type ValidatedInput = Bytes @ Trusted;

// ZIRAH (EDR)
type ThreatSignature = Signature @ Internal;
type ScanResult = Result @ Confidential;

// BENTENG (eKYC)
type BiometricData = FaceTemplate @ Secret;
type VerificationResult = bool @ Internal;

// SANDI (Digital Sig)
type PrivateKey = Key @ TopSecret;
type PublicKey = Key @ Public;
```

---

## Part 9: Bibliography

1. Volpano, D., Smith, G., Irvine, C. (1996). "A Sound Type System for Secure Flow Analysis"
2. Heintze, N., Riecke, J.G. (1998). "The SLam Calculus"
3. Pottier, F., Simonet, V. (2003). "Information Flow Inference for ML"
4. Zdancewic, S. (2002). "Programming Languages for Information Security"
5. Rajani, V., Garg, D. (2018). "Types for Information Flow Control"

---

*Research Track Output — Domain C: Information Flow Control*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
