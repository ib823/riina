# TERAS-LANG Architecture Decision B-02: Monadic Effects

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B02-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-02 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL:**

1. **Use algebraic effects as primary** (per B-01), NOT monads
2. **Provide monad compatibility layer** for interoperability
3. **Support indexed monads** for security label tracking
4. **Offer free monad DSLs** for configuration and protocols
5. **NOT use monad transformers** as the effect composition mechanism

### 1.2 Architecture Decision ID

`TERAS-ARCH-B02-MON-001`

### 1.3 Status

**APPROVED** â€” Ratified for TERAS-LANG implementation

---

## 2. Rationale

### 2.1 Why NOT Monads as Primary

| Issue | Impact on TERAS |
|-------|-----------------|
| No multi-shot continuations | Cannot implement backtracking handlers |
| Transformer order matters | Complex security reasoning |
| nÂ² instances problem | Maintenance burden |
| Cannot have multiple same-effect | Multiple audit contexts problematic |

### 2.2 Why Monad Compatibility

| Benefit | Application |
|---------|-------------|
| Existing Rust ecosystem | tokio, async-std interop |
| Familiar patterns | Developer onboarding |
| Proven patterns | Audit, capability, etc. |

### 2.3 Why Indexed Monads

```rust
// Security labels via indexed types
struct Labeled<L: Label, T>(T);

// Indexed monad for label tracking
trait IMonad {
    type Input;
    type Output;
    fn ibind<B, L2>(self, f: impl FnOnce(A) -> M<L2, B>) -> M<L2, B>
    where
        Self::Output == L2::Input;
}
```

---

## 3. Design Details

### 3.1 Monad Compatibility Layer

```rust
// Trait for monad-like computations
trait Monad: Sized {
    fn pure<A>(a: A) -> Self where Self: Contains<A>;
    fn bind<B>(self, f: impl FnOnce(A) -> Self::Output<B>) -> Self::Output<B>;
}

// Convert algebraic effect to monad
impl<E: Effect, A> Monad for Eff<E, A> {
    fn pure(a: A) -> Eff<E, A> { Eff::pure(a) }
    fn bind<B>(self, f: impl FnOnce(A) -> Eff<E, B>) -> Eff<E, B> {
        self.and_then(f)
    }
}
```

### 3.2 Free Monad for DSLs

```rust
// Free monad for protocol DSLs
enum Free<F, A> {
    Pure(A),
    Free(F, Box<dyn FnOnce(F::Output) -> Free<F, A>>),
}

// Protocol as functor
enum ProtocolF<Next> {
    Send(Message, Next),
    Recv(Box<dyn FnOnce(Message) -> Next>),
    Close(Next),
}

// Interpretation
fn interpret_protocol<A>(
    p: Free<ProtocolF, A>,
    conn: &mut Connection
) -> Result<A> {
    match p {
        Free::Pure(a) => Ok(a),
        Free::Free(ProtocolF::Send(msg, next), k) => {
            conn.send(msg)?;
            interpret_protocol(k(next), conn)
        }
        // ...
    }
}
```

### 3.3 Indexed Monad for Security

```rust
// Phantom types for security levels
struct Public;
struct Confidential;
struct Secret;

// Indexed monad tracking security level
struct SecureM<Pre: Label, Post: Label, A> {
    run: Box<dyn FnOnce() -> (A, LabelProof<Post>)>,
    _pre: PhantomData<Pre>,
}

impl<L1: Label, L2: Label, A> SecureM<L1, L2, A> {
    fn and_then<L3: Label, B>(
        self,
        f: impl FnOnce(A) -> SecureM<L2, L3, B>
    ) -> SecureM<L1, L3, B>
    where
        L1: FlowsTo<L2>,  // Compile-time check
    {
        SecureM {
            run: Box::new(move || {
                let (a, _) = (self.run)();
                (f(a).run)()
            }),
            _pre: PhantomData,
        }
    }
}
```

---

## 4. Integration with Algebraic Effects

### 4.1 Effect-to-Monad Bridge

```rust
// Run effectful computation as monad
fn run_as_monad<M: Monad, E: Effect, A>(
    eff: Eff<E, A>,
    handler: impl MonadHandler<E, M>
) -> M::Output<A> {
    handler.handle(eff)
}

// Monad handler trait
trait MonadHandler<E: Effect, M: Monad> {
    fn handle<A>(&self, eff: Eff<E, A>) -> M::Output<A>;
}
```

### 4.2 Async Monad Compatibility

```rust
// Bridge to async/await
impl<E: Effect, A> IntoFuture for Eff<E, A>
where
    E: AsyncCompatible,
{
    type Output = A;
    type IntoFuture = EffFuture<E, A>;
    
    fn into_future(self) -> Self::IntoFuture {
        EffFuture::new(self)
    }
}
```

---

## 5. What We're NOT Using

### 5.1 Rejected: MTL-style as Primary

**Reason**: Transformer stacks don't compose cleanly for security.

### 5.2 Rejected: Free Monads for All Effects

**Reason**: Performance overhead too high for general use.

### 5.3 Rejected: Freer/Extensible Effects

**Reason**: Algebraic effects (B-01) superior for TERAS requirements.

---

## 6. Implementation Notes

| Component | Priority | Duration |
|-----------|----------|----------|
| Monad trait | Medium | 1 week |
| Indexed monad | High | 2 weeks |
| Free DSL support | Low | 2 weeks |
| Async bridge | High | 2 weeks |

---

## 7. References

1. Moggi, E. (1991). "Notions of Computation and Monads"
2. Kiselyov, O., Ishii, H. (2015). "Freer Monads, More Extensible Effects"
3. TERAS Architecture Decision B-01

---

*Architecture Decision Record for TERAS-LANG monadic effects.*
