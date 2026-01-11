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

Ï„_sec ::= Ï„^L              -- base type with label
        | Ï„â‚^L â†’ Ï„â‚‚^L'     -- function type with labels
        | Ref(Ï„^L)         -- reference with label
        | (Ï„â‚^Lâ‚, Ï„â‚‚^Lâ‚‚)   -- product with labels

Examples:
    int^Secret           -- secret integer
    string^Public        -- public string
    (int^H â†’ int^L)      -- function H to L (potential leak)
```

### 1.2 Label Polymorphism

```
Polymorphism over labels:

âˆ€L. Ï„^L â†’ Ï„^L    -- Identity preserving label
âˆ€Lâ‚ Lâ‚‚. Lâ‚ âŠ‘ Lâ‚‚ â‡’ Ï„^Lâ‚ â†’ Ï„^Lâ‚‚  -- Upgrade function

Example:
    id : âˆ€L. int^L â†’ int^L
    id(secret)  : int^Secret
    id(public)  : int^Public
```

### 1.3 PC (Program Counter) Label

```
PC Label: Security context of current execution

Purpose: Prevent implicit flows

Rule:
    Î“, pc âŠ¢ if e then câ‚ else câ‚‚
    requires: e : bool^L and pc' = pc âŠ” L
              câ‚, câ‚‚ typed under pc'

Example:
    pc = Low
    if secret_bool then    -- pc becomes High
        public := 1        -- ERROR: writing Low under pc=High
```

---

## Part 2: Typing Rules

### 2.1 Core Typing Judgments

```
Typing judgment: Î“; pc âŠ¢ e : Ï„^L

Î“ = typing environment
pc = program counter label
e = expression
Ï„^L = labeled type

Soundness: Well-typed programs satisfy noninterference
```

### 2.2 Expression Typing

```
Variable:
    (x : Ï„^L) âˆˆ Î“
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ x : Ï„^L

Literal:
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ n : int^âŠ¥

Application:
    Î“; pc âŠ¢ eâ‚ : (Ï„â‚^Lâ‚ â†’ Ï„â‚‚^Lâ‚‚)^L_f
    Î“; pc âŠ¢ eâ‚‚ : Ï„â‚^Lâ‚'
    Lâ‚' âŠ‘ Lâ‚    L_f âŠ‘ Lâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ eâ‚ eâ‚‚ : Ï„â‚‚^(Lâ‚‚ âŠ” L_f)

Abstraction:
    Î“, x : Ï„â‚^Lâ‚; pc âŠ¢ e : Ï„â‚‚^Lâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ Î»x.e : (Ï„â‚^Lâ‚ â†’ Ï„â‚‚^Lâ‚‚)^pc
```

### 2.3 Command Typing

```
Assignment:
    Î“; pc âŠ¢ e : Ï„^L_e
    (x : Ref(Ï„^L_x)) âˆˆ Î“
    L_e âŠ” pc âŠ‘ L_x
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ x := e : cmd^(L_e âŠ” pc)

Sequence:
    Î“; pc âŠ¢ câ‚ : cmd^Lâ‚
    Î“; pc âŠ¢ câ‚‚ : cmd^Lâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ câ‚; câ‚‚ : cmd^(Lâ‚ âŠ” Lâ‚‚)

Conditional:
    Î“; pc âŠ¢ e : bool^L
    Î“; pc âŠ” L âŠ¢ câ‚ : cmd^Lâ‚
    Î“; pc âŠ” L âŠ¢ câ‚‚ : cmd^Lâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ if e then câ‚ else câ‚‚ : cmd^(L âŠ” Lâ‚ âŠ” Lâ‚‚)

While:
    Î“; pc âŠ¢ e : bool^L
    Î“; pc âŠ” L âŠ¢ c : cmd^L'
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ while e do c : cmd^(L âŠ” L')
```

---

## Part 3: Subtyping

### 3.1 Label Subtyping

```
Label subtyping: Lâ‚ âŠ‘ Lâ‚‚

Covariance in labeled types:
    Lâ‚ âŠ‘ Lâ‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Ï„^Lâ‚ <: Ï„^Lâ‚‚

Contravariance in function domain (standard):
    Ï„â‚' <: Ï„â‚    Ï„â‚‚ <: Ï„â‚‚'    Lâ‚' âŠ‘ Lâ‚    Lâ‚‚ âŠ‘ Lâ‚‚'
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    (Ï„â‚^Lâ‚ â†’ Ï„â‚‚^Lâ‚‚) <: (Ï„â‚'^Lâ‚' â†’ Ï„â‚‚'^Lâ‚‚')
```

### 3.2 Reference Subtyping

```
References are INVARIANT in label:

    Ref(Ï„^L) <: Ref(Ï„^L)   -- only same label

NOT: Ref(Ï„^High) <: Ref(Ï„^Low)  -- would allow write
NOT: Ref(Ï„^Low) <: Ref(Ï„^High)  -- would allow read

Reason: References support both read and write
```

### 3.3 Subsumption Rule

```
Subsumption:
    Î“; pc âŠ¢ e : Ï„â‚    Ï„â‚ <: Ï„â‚‚
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“; pc âŠ¢ e : Ï„â‚‚

Allows implicit "upgrades" to higher labels.
```

---

## Part 4: Advanced Features

### 4.1 Dependent Security Labels

```
Labels dependent on values:

label_of : âˆ€a. a â†’ Label
check : (x : Ï„^L) â†’ {L âŠ‘ label_of(x)} â†’ Ï„^(label_of(x))

Example:
    fn process(user: User) â†’ Data^(user.clearance) {
        // Return type depends on user's clearance
    }
```

### 4.2 Refinement Types with Labels

```
Combining refinements and security:

{ x : int^L | x > 0 }^L'    -- Positive int, double labeled
                            -- L for content, L' for existence

Example:
    fn check_positive(n: {x: int^Secret | x > 0}) â†’ bool^Public {
        true  // Reveals existence of positive, but not value
    }
```

### 4.3 First-Class Labels

```
Labels as values:

type Label = SecurityLevel

fn process_at_level(L: Label, data: int^L) â†’ int^L {
    data + 1
}

// Runtime label operations
let current_label : Label = get_label(data)
if current_label âŠ‘ threshold then ...
```

---

## Part 5: Integrity Types

### 5.1 Dual to Confidentiality

```
Integrity Labels (I):

High Integrity: Trusted, validated
Low Integrity: Untrusted, tainted

Flow direction (opposite to confidentiality):
    Untrusted â†’ Trusted  âœ—  (could corrupt)
    Trusted â†’ Untrusted  âœ“  (allowed)
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
    (Câ‚, Iâ‚) âŠ‘ (Câ‚‚, Iâ‚‚) iff Câ‚ âŠ‘ Câ‚‚ and Iâ‚‚ âŠ‘ Iâ‚
```

### 5.3 Robust Declassification

```
Integrity protects declassification:

fn declassify(data: int^(Secret, Trusted)) â†’ int^(Public, Trusted)
    where CurrentPrincipal: HasAuthority
{
    // Only trusted code can declassify
}

// Untrusted code cannot declassify:
fn bad_declassify(data: int^(Secret, Untrusted)) â†’ int^(Public, _)
    // ERROR: Cannot declassify from untrusted source
```

---

## Part 6: Type Inference for Security

### 6.1 Constraint Generation

```
Generate label constraints during type inference:

infer(Î“, x := e):
    (Ï„_e, L_e, C_e) = infer(Î“, e)
    L_x = lookup(Î“, x)
    C = C_e âˆª {L_e âŠ” pc âŠ‘ L_x}
    return (cmd, L_e âŠ” pc, C)
```

### 6.2 Constraint Solving

```
Solving label constraints:

Constraints: { Lâ‚ âŠ‘ Lâ‚‚, Lâ‚‚ âŠ‘ Lâ‚ƒ, ... }

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
    // Inferred: âˆ€L. Ï„^L â†’ Ï„^L
```

---

## Part 7: Exceptions and Control Flow

### 7.1 Exceptions as Implicit Flow

```
Problem: Exceptions leak information

if secret then throw() else ()
// Exception raised â‡” secret is true!

Solution: Label exceptions

throw : âˆ€L. unit â†’ Ï„ ! Exception^L
catch : (unit â†’ Ï„ ! Exception^L) â†’ (unit â†’ Ï„) â†’ Ï„

Constraint: Handler pc must be âŠ’ L
```

### 7.2 Termination Channel

```
Termination leaks one bit:

while secret do skip

Non-termination â‡” secret is true

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

*Research Track Output â€” Domain C: Information Flow Control*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
