# RESEARCH_A05_EFFECT_SYSTEMS_DECISION.md

## TERAS Research Track: Session A-05
## Effect Systems Integration Decision for TERAS-LANG

**Document Version:** 1.0.0
**Created:** 2026-01-03
**Session:** A-05 of 47
**Track:** Foundational Type Theory
**Status:** APPROVED

---

## 1. Decision Summary

### 1.1 Primary Decision

**ADOPT** a row-polymorphic algebraic effect system with first-class handlers as the computational effect tracking mechanism for TERAS-LANG.

### 1.2 Decision Statement

TERAS-LANG shall implement:

1. **Row-polymorphic effect types** with decidable inference (Koka-style)
2. **Algebraic effect operations** as first-class constructs
3. **Effect handlers** for modular effect implementation
4. **Security-specific effects** for IFC, capabilities, and audit
5. **Integration hooks** with linear types (A-04) and refinement types (A-03)

### 1.3 Rationale

| Criterion | Weight | Score | Justification |
|-----------|--------|-------|---------------|
| Security expressiveness | 25% | 9/10 | IFC, capabilities, audit as effects |
| Type system integration | 20% | 9/10 | Orthogonal to linear/refinement |
| Decidability | 15% | 9/10 | Row unification decidable |
| Performance potential | 15% | 8/10 | Evidence passing + specialization |
| Developer ergonomics | 15% | 8/10 | Inference, no transformers |
| Implementation feasibility | 10% | 7/10 | Complex but well-documented |

**Weighted Score: 8.5/10** - Exceeds threshold for adoption.

---

## 2. Architecture Decision Records

### ADR-A05-001: Row-Polymorphic Effect Rows

**Context:** TERAS-LANG requires effect tracking with polymorphism and decidable inference.

**Decision:** Implement effect types as rows with row variables.

```teras
// Effect row syntax
Îµ ::= âŸ¨âŸ©                   -- empty (pure)
    | âŸ¨l | ÎµâŸ©             -- effect l extended with tail Îµ  
    | Î¼                    -- effect row variable

// Function with effects
(Ï„â‚ â†’^Îµ Ï„â‚‚)               -- function from Ï„â‚ to Ï„â‚‚ with effects Îµ
```

**Consequences:**
- Positive: Decidable unification-based inference
- Positive: Effect polymorphism without subtyping
- Positive: Principal types exist
- Negative: Row ordering can confuse
- Mitigated: Canonical ordering, clear documentation

### ADR-A05-002: Algebraic Effect Operations

**Context:** Need modular, composable effect specifications.

**Decision:** Define effects through operation signatures.

```teras
// Effect declaration
effect State<S> {
    get : () -> S
    put : S -> ()
}

effect Exception<E> {
    throw : E -> âŠ¥
}

effect IO {
    read_line : () -> String
    print : String -> ()
}
```

**Consequences:**
- Positive: Clear effect interfaces
- Positive: Separates effect specification from implementation
- Positive: Multiple handlers for same effect
- Negative: Requires handler mechanism
- Mitigated: Built-in handlers for common effects

### ADR-A05-003: Effect Handlers

**Context:** Effects need implementation; handlers provide modular semantics.

**Decision:** Support first-class effect handlers with deep handler semantics.

```teras
// Handler syntax
handle computation with {
    return(x) => e_ret,
    opâ‚(args, resume) => eâ‚,
    opâ‚‚(args, resume) => eâ‚‚,
    ...
}

// Example: State handler
let run_state<S, A>(init: S, comp: Eff<âŸ¨State<S> | ÎµâŸ©, A>) -> Eff<Îµ, (A, S)> =
    handle comp with {
        return(x) => \s -> (x, s),
        get((), resume) => \s -> resume(s)(s),
        put(s', resume) => \_ -> resume(())(s')
    }(init)
```

**Consequences:**
- Positive: Modular effect implementation
- Positive: Handler composition
- Positive: Same code, different handlers (testing, production)
- Negative: Continuation capture complexity
- Mitigated: Evidence passing for common cases

### ADR-A05-004: Security-Specific Effects

**Context:** TERAS requires effects for security-relevant operations.

**Decision:** Define dedicated security effect families.

```teras
// Information Flow Control
effect SecretRead<L: Level> {
    read : () -> Data<L>
}

effect SecretWrite<L: Level> {
    write : Data<L> -> ()
}

// Capability Usage
effect UseCapability<R: Resource> {
    use : lin Capability<R> -> R
    release : lin Capability<R> -> ()
}

// Audit Logging
effect Audit {
    log : AuditEntry -> ()
}

// Cryptographic Operations
effect Crypto {
    random : Size -> Bytes
    hash : Bytes -> Digest
    encrypt : (Key, Plaintext) -> Ciphertext
    decrypt : (Key, Ciphertext) -> Option<Plaintext>
}
```

**Consequences:**
- Positive: Security properties tracked by types
- Positive: Handler-based enforcement
- Positive: Testability (mock handlers)
- Negative: Effect proliferation
- Mitigated: Effect hierarchies, bundled effects

### ADR-A05-005: Integration with Linear Types

**Context:** Session A-04 established linear types; effects must integrate.

**Decision:** Allow effects on linear resources with proper consumption.

```teras
// Linear resource with effects
effect FileOp {
    open : Path -> lin FileHandle
    read : &FileHandle -> Bytes      // borrow, effect
    write : &mut FileHandle -> Bytes -> ()
    close : lin FileHandle -> ()     // consume
}

// Handler ensures resource lifecycle
file_handler : Handler<FileOp> = {
    open(path, resume) => ...,
    close(handle, resume) => { 
        syscall_close(handle); 
        resume(()) 
    },
    ...
}
```

**Key Rule:** Effect operations may consume linear arguments; resume receives non-linear continuation result.

---

## 3. Effect Type System Specification

### 3.1 Effect Row Syntax

```
Effect Labels:
  l ::= State<Ï„> | Exception<Ï„> | IO | Crypto 
      | SecretRead<L> | SecretWrite<L> 
      | Audit | UseCapability<R> | ...

Effect Rows:
  Îµ ::= âŸ¨âŸ©           -- empty row (pure)
      | âŸ¨l | ÎµâŸ©     -- extension
      | Î¼            -- row variable

Types with Effects:
  Ï„ ::= ...
      | Ï„â‚ â†’^Îµ Ï„â‚‚   -- effectful function
      | Eff<Îµ, Ï„>   -- effectful computation
```

### 3.2 Row Equivalence

```
âŸ¨lâ‚ | âŸ¨lâ‚‚ | ÎµâŸ©âŸ© â‰¡ âŸ¨lâ‚‚ | âŸ¨lâ‚ | ÎµâŸ©âŸ©    (commutativity)
âŸ¨l | âŸ¨l | ÎµâŸ©âŸ© â‰¡ âŸ¨l | ÎµâŸ©              (idempotence, optional)
```

**Note:** Duplicate labels allowed for nested handlers of same effect.

### 3.3 Typing Rules

**Pure Subtyping:**
```
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Eff<âŸ¨âŸ©, Ï„> â‰¤ Ï„          (pure computation is value)
```

**Effect Weakening:**
```
Î“ âŠ¢ e : Eff<Îµâ‚, Ï„>
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ e : Eff<âŸ¨l | Îµâ‚âŸ©, Ï„>   (can add effects)
```

**Operation Typing:**
```
op : Ï„â‚ â†’ Ï„â‚‚ âˆˆ Effect(l)
Î“ âŠ¢ e : Ï„â‚
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ op(e) : Eff<âŸ¨l | Î¼âŸ©, Ï„â‚‚>
```

**Handler Typing:**
```
Î“ âŠ¢ computation : Eff<âŸ¨l | ÎµâŸ©, Î±>
Î“ âŠ¢ handler : Handler<l, Î±, Î², Îµ>
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ handle computation with handler : Eff<Îµ, Î²>
```

### 3.4 Effect Inference

**Algorithm:** Extend HM with effect row unification.

```
infer(Î“, e) = (Ï„, Îµ, C)
  where Ï„ is inferred type
        Îµ is inferred effect row
        C is constraint set

unify_row(âŸ¨l | Îµâ‚âŸ©, âŸ¨l | Îµâ‚‚âŸ©) = unify_row(Îµâ‚, Îµâ‚‚)
unify_row(âŸ¨l | Îµâ‚âŸ©, âŸ¨l' | Îµâ‚‚âŸ©) = 
  let Î¼ fresh in
  unify_row(Îµâ‚, âŸ¨l' | Î¼âŸ©) âˆª unify_row(Îµâ‚‚, âŸ¨l | Î¼âŸ©)
unify_row(Î¼, Îµ) = [Î¼ â†¦ Îµ] if Î¼ âˆ‰ FV(Îµ)
```

---

## 4. Standard Effect Library

### 4.1 Core Effects

```teras
/// State effect with type-safe state
effect State<S> {
    get : () -> S
    put : S -> ()
    modify : (S -> S) -> ()
}

/// Exception effect
effect Exception<E> {
    throw : E -> âŠ¥
    try_catch : (() ->^âŸ¨Exception<E> | ÎµâŸ© A) -> (E -> A) ->^Îµ A
}

/// Reader effect (immutable environment)
effect Reader<R> {
    ask : () -> R
    local : (R -> R) -> (() ->^âŸ¨Reader<R> | ÎµâŸ© A) ->^Îµ A
}

/// Writer effect (append-only output)
effect Writer<W: Monoid> {
    tell : W -> ()
}

/// Nondeterminism
effect Choice {
    choose : () -> Bool
    fail : () -> âŠ¥
}
```

### 4.2 Security Effects

```teras
/// Information flow control
effect IFC<L: SecurityLevel> {
    classify : (data: Ï„) -> Labeled<L, Ï„>
    declassify : (labeled: Labeled<H, Ï„>, proof: CanDeclassify<H, L>) -> Labeled<L, Ï„>
    read_labeled : Labeled<L, Ï„> -> Ï„  // requires current level âŠ’ L
}

/// Capability-based access control
effect Cap<R: Resource> {
    acquire : (resource: R) -> lin Capability<R>
    use_cap : (cap: lin Capability<R>) -> (R -> âŸ¨ÎµâŸ© Î±) ->^Îµ (Î±, lin Capability<R>)
    revoke : (cap: lin Capability<R>) -> ()
}

/// Audit logging (mandatory)
effect Audit {
    log_operation : (op: OperationType, params: LogParams) -> ()
    log_access : (resource: ResourceId, action: Action) -> ()
    log_security_event : (event: SecurityEvent) -> ()
}

/// Cryptographic operations
effect Crypto {
    secure_random : (size: {n: Nat | n â‰¤ MAX_RANDOM}) -> Bytes<n>
    hash : (alg: HashAlgorithm, data: Bytes) -> Digest
    mac : (key: MacKey, data: Bytes) -> Mac
    verify_mac : (key: MacKey, data: Bytes, mac: Mac) -> Bool
    
    // Asymmetric
    sign : (key: lin SigningKey, data: Bytes) -> (Signature, lin SigningKey)
    verify : (key: &VerifyingKey, data: Bytes, sig: Signature) -> Bool
    
    // Symmetric
    encrypt_aead : (key: &AeadKey, nonce: Nonce, plaintext: Bytes, aad: Bytes) 
                   -> Ciphertext
    decrypt_aead : (key: &AeadKey, nonce: Nonce, ciphertext: Ciphertext, aad: Bytes) 
                   -> Option<Bytes>
}
```

### 4.3 I/O Effects

```teras
/// Console I/O
effect Console {
    print : String -> ()
    print_line : String -> ()
    read_line : () -> String
}

/// File I/O (with linear handles)
effect File {
    open : (path: Path, mode: Mode) -> lin FileHandle
    read : (handle: &FileHandle, size: Size) -> Bytes
    write : (handle: &mut FileHandle, data: Bytes) -> Size
    close : (handle: lin FileHandle) -> ()
}

/// Network I/O
effect Net {
    connect : (addr: Address) -> lin Connection
    send : (conn: &mut Connection, data: Bytes) -> Size
    recv : (conn: &Connection, size: Size) -> Bytes
    disconnect : (conn: lin Connection) -> ()
}
```

---

## 5. Handler Implementation

### 5.1 Handler Definition Syntax

```teras
handler state_handler<S, A> for State<S> {
    return(x) = \s -> (x, s)
    
    get((), resume) = \s -> {
        resume(s)(s)
    }
    
    put(s', resume) = \_ -> {
        resume(())(s')
    }
}

fn run_state<S, A>(init: S, comp: Eff<âŸ¨State<S> | ÎµâŸ©, A>) -> Eff<Îµ, (A, S)> {
    handle comp with state_handler(init)
}
```

### 5.2 Security Handler Examples

```teras
/// Production crypto handler - real cryptography
handler prod_crypto_handler for Crypto {
    return(x) = x
    
    secure_random(size, resume) = {
        let bytes = call_secure_random_syscall(size);
        resume(bytes)
    }
    
    hash(alg, data, resume) = {
        let digest = match alg {
            SHA256 => sha256_impl(data),
            SHA3_256 => sha3_256_impl(data),
            BLAKE3 => blake3_impl(data),
        };
        resume(digest)
    }
    
    // ... other operations
}

/// Testing crypto handler - deterministic for testing
handler test_crypto_handler<Seed> for Crypto {
    return(x) = \seed -> x
    
    secure_random(size, resume) = \seed -> {
        let (bytes, new_seed) = deterministic_random(seed, size);
        resume(bytes)(new_seed)
    }
    
    // ... other operations with deterministic behavior
}

/// Audit-wrapping crypto handler
handler audited_crypto_handler for Crypto {
    return(x) = x
    
    secure_random(size, resume) = {
        log_operation(CryptoOp::Random, size);
        let bytes = secure_random_impl(size);
        resume(bytes)
    }
    
    hash(alg, data, resume) = {
        log_operation(CryptoOp::Hash, (alg, data.len()));
        let digest = hash_impl(alg, data);
        resume(digest)
    }
    
    sign(key, data, resume) = {
        log_operation(CryptoOp::Sign, (key.id(), data.len()));
        let (sig, key) = sign_impl(key, data);
        resume((sig, key))
    }
    
    // ... audit wrapping for all operations
}
```

### 5.3 IFC Handler

```teras
handler ifc_handler<CurrentLevel: Level> for IFC<L> {
    return(x) = x
    
    classify(data, resume) = {
        let labeled = Labeled { data, level: L };
        resume(labeled)
    }
    
    read_labeled(labeled, resume) = {
        // Static check: CurrentLevel âŠ’ labeled.level
        // This is enforced by the type system
        resume(labeled.data)
    }
    
    declassify(labeled, proof, resume) = {
        // proof witnesses that declassification is authorized
        let new_labeled = Labeled { 
            data: labeled.data, 
            level: proof.target_level 
        };
        resume(new_labeled)
    }
}
```

---

## 6. Implementation Strategy

### 6.1 Compilation Phases

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ TERAS Source    â”‚
â”‚ (with effects)  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
         â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Effect          â”‚ â—„â”€â”€ Effect inference
â”‚ Elaboration     â”‚     Handler resolution
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
         â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Evidence        â”‚ â—„â”€â”€ Insert handler evidence
â”‚ Translation     â”‚     Capability threading
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
         â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Optimization    â”‚ â—„â”€â”€ Handler specialization
â”‚                 â”‚     Effect fusion
â””â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”˜
         â”‚
         â–¼
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Code            â”‚ â—„â”€â”€ Native code generation
â”‚ Generation      â”‚     Zero runtime overhead
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 6.2 Evidence Passing (Default)

**Transform:**
```teras
// Before
fn effectful<S>() -> âŸ¨State<S>âŸ© A {
    let x = get();
    put(x + 1);
    x
}

// After evidence passing
fn effectful_ev<S>(h: StateHandler<S>) -> A {
    let x = h.get();
    h.put(x + 1);
    x
}
```

**Benefits:**
- No continuation capture
- Direct function calls
- Good for one-shot handlers

### 6.3 CPS for Multi-Shot

**When needed:**
- Backtracking (Choice effect)
- Coroutines/generators
- Exception with state rollback

**Transform:**
```teras
// Before
fn choose_example() -> âŸ¨ChoiceâŸ© Int {
    if choose() { 1 } else { 2 }
}

// After CPS
fn choose_example_cps(k: Int -> R) -> âŸ¨ChoiceâŸ© R {
    if choose() { k(1) } else { k(2) }
}
```

---

## 7. Performance Considerations

### 7.1 Zero-Cost Effect Checking

**Guarantee:** All effect checking at compile time.

- Effect rows are erased after type checking
- No runtime effect tags
- Handlers inline when monomorphic

### 7.2 Handler Specialization

**Optimization:**
```
// Generic
handle comp with h

// After specialization (when h known)
// Handler code inlined at operation sites
comp_specialized
```

### 7.3 Effect Fusion

**Optimization:**
```teras
// Before: two handlers
handle (handle comp with h1) with h2

// After fusion: combined handler
handle comp with h1_h2_fused
```

### 7.4 Benchmarks Target

| Operation | Target | Rationale |
|-----------|--------|-----------|
| Pure function | =C | No overhead |
| State handler | =C pointer | Evidence = pointer |
| Exception | =C setjmp | Similar mechanism |
| Crypto | =C + overhead | Real crypto cost |

---

## 8. Risk Assessment

### 8.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Handler performance | Medium | High | Evidence passing default |
| Effect inference complexity | Low | Medium | Well-documented algorithm |
| Integration with linear | Medium | Medium | Clean separation |
| Multi-shot overhead | Medium | Medium | CPS only when needed |

### 8.2 Design Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Too many effects | Medium | Medium | Effect hierarchies |
| Handler interference | Low | High | Type system prevents |
| Learning curve | Medium | Medium | Good documentation |

---

## 9. Implementation Roadmap

### Phase 1: Core Effect System (Weeks 1-6)
- [ ] Effect row types in parser
- [ ] Row unification algorithm
- [ ] Effect inference
- [ ] Basic effect tracking

### Phase 2: Handlers (Weeks 7-12)
- [ ] Handler syntax
- [ ] Evidence passing translation
- [ ] Built-in handlers (State, Exception)
- [ ] Handler composition

### Phase 3: Security Effects (Weeks 13-18)
- [ ] IFC effect family
- [ ] Capability effects
- [ ] Audit effects
- [ ] Crypto effects

### Phase 4: Optimization (Weeks 19-24)
- [ ] Handler specialization
- [ ] Effect fusion
- [ ] CPS translation (multi-shot)
- [ ] Performance validation

### Phase 5: Integration (Weeks 25-28)
- [ ] Linear type integration (A-04)
- [ ] Refinement integration (A-03)
- [ ] Documentation
- [ ] Security audit

---

## 10. Decision Approval

### 10.1 Alignment with TERAS Principles

| TERAS Law | Alignment | Notes |
|-----------|-----------|-------|
| Law 1: Self-Sufficiency | âœ“ | Custom implementation |
| Law 2: Formal Verification | âœ“ | Type-checked effects |
| Law 3: Zero Third-Party | âœ“ | No external deps |
| Law 4: Malaysian Identity | â—‹ | Neutral |
| Law 5: Post-Quantum Ready | â—‹ | Orthogonal |
| Law 6: Memory Safety | âœ“ | Effect tracking aids |
| Law 7: Auditability | âœ“ | Audit effect |
| Law 8: Performance | âœ“ | Zero runtime overhead |

**Overall Alignment: 9.0/10**

### 10.2 Sign-Off

**Decision:** APPROVED for implementation in TERAS-LANG

**Rationale:**
- Row-polymorphic effects provide decidable inference
- Handlers enable modular security patterns
- Security effects track critical operations
- Evidence passing ensures performance

**Next Steps:**
1. Proceed to A-06 (Session Types) for protocol verification
2. Begin Phase 1 implementation per roadmap
3. Define standard effect library interfaces

---

## 11. References

1. Leijen, D. (2014). "Koka: Programming with Row Polymorphic Effect Types."
2. Plotkin, G. & Pretnar, M. (2009). "Handlers of Algebraic Effects."
3. Swamy, N. et al. (2016). "Dependent Types and Multi-Monadic Effects in F*."
4. Moggi, E. (1991). "Notions of Computation and Monads."
5. HillerstrÃ¶m, D. & Lindley, S. (2016). "Liberating Effects with Rows and Handlers."

---

## Document Metadata

**Research Track:** A (Theoretical Foundations)
**Session:** A-05
**Document Type:** Architecture Decision
**Status:** APPROVED
**Preceding Documents:**
- RESEARCH_A05_EFFECT_SYSTEMS_SURVEY.md
- RESEARCH_A05_EFFECT_SYSTEMS_COMPARISON.md
**Following Session:** A-06 (Session Types)

**SHA-256 Lineage:**
- Parent: RESEARCH_A04_LINEAR_TYPES_DECISION.md
- This Document: [Computed on finalization]

---

*This decision establishes the effect system foundation for TERAS-LANG, enabling compile-time tracking and verification of computational effects essential for security-critical software.*
