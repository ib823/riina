# TERAS-LANG Research Comparison B-04: Effect Handlers

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-B04-COMPARISON |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | B-04 |
| Domain | B: Effect Systems |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## 1. Handler Implementations Compared

| System | Handler Style | Continuation | Multi-shot |
|--------|---------------|--------------|------------|
| Eff | Deep, first-class | Full | Yes |
| Koka | Deep, evidence | Optimized | Yes |
| Frank | Deep, implicit | Full | Yes |
| OCaml 5 | Shallow, explicit | One-shot | No |
| Effekt | Deep, capability | One-shot | No |
| Multicore OCaml | Fiber-based | One-shot | No |

---

## 2. Feature Comparison Matrix

### 2.1 Handler Features

| Feature | Eff | Koka | Frank | OCaml 5 | Effekt |
|---------|-----|------|-------|---------|--------|
| Deep handlers | ✓ | ✓ | ✓ | Manual | ✓ |
| Shallow handlers | ✓ | ✓ | ✗ | ✓ | ✗ |
| First-class | ✓ | ✓ | ✗ | ✓ | ✓ |
| Parameterized | ✓ | ✓ | ✓ | Manual | ✓ |
| Named/labelled | ✓ | ✓ | ✗ | ✗ | ✓ |
| Scoped | ✓ | ✓ | ✗ | ✗ | ✓ |
| Forwarding | ✗ | ✓ | ✗ | Manual | ✗ |

### 2.2 Continuation Properties

| Property | Eff | Koka | Frank | OCaml 5 | Effekt |
|----------|-----|------|-------|---------|--------|
| Multi-shot | ✓ | ✓ | ✓ | ✗ | ✗ |
| Linear enforced | ✗ | ✗ | ✗ | ✓ | ✓ |
| Tail-resumptive opt | ✗ | ✓ | ✗ | N/A | ✓ |
| Delimited | ✓ | ✓ | ✓ | ✓ | ✓ |

### 2.3 Performance

| Metric | Eff | Koka | Frank | OCaml 5 | Effekt |
|--------|-----|------|-------|---------|--------|
| Handler install | Slow | Fast | Slow | Fast | Fast |
| Tail-resumptive | Slow | ~0 | Slow | Fast | ~0 |
| Multi-shot | OK | OK | OK | N/A | N/A |
| Memory | High | Low | High | Medium | Low |

---

## 3. Compilation Strategy Comparison

### 3.1 CPS-Based (Eff, Frank)

**Pros:**
- Simple, correct
- Multi-shot natural
- Universal

**Cons:**
- Slow
- No TCO
- High allocation

### 3.2 Evidence Passing (Koka)

**Pros:**
- Fast for tail-resumptive
- Good optimization
- Low overhead

**Cons:**
- Complex compilation
- Some effects need CPS fallback

### 3.3 Fiber-Based (OCaml 5)

**Pros:**
- Fast context switch
- Native support
- Good for concurrency

**Cons:**
- One-shot only
- Shallow only default
- No multi-shot

### 3.4 Capability Passing (Effekt)

**Pros:**
- Lexically scoped
- Good for security
- Efficient

**Cons:**
- One-shot only
- Less flexible

---

## 4. Security-Relevant Comparison

| Aspect | Eff | Koka | OCaml 5 | Effekt |
|--------|-----|------|---------|--------|
| Effect containment | ✓ | ✓ | ✗ | ✓ |
| Resource safety | ◐ | ◐ | ✓ | ✓ |
| Scoping control | ✓ | ✓ | ✗ | ✓ |
| Audit hooks | Manual | Manual | Manual | Manual |

---

## 5. TERAS Suitability Scores

| Criterion | Weight | Eff | Koka | OCaml 5 | Effekt |
|-----------|--------|-----|------|---------|--------|
| Performance | 25% | 4 | 9 | 8 | 9 |
| Safety | 25% | 7 | 8 | 5 | 9 |
| Flexibility | 20% | 9 | 8 | 5 | 7 |
| Type safety | 20% | 8 | 9 | 4 | 9 |
| Simplicity | 10% | 7 | 7 | 8 | 7 |
| **Total** | 100% | **6.80** | **8.40** | **5.80** | **8.30** |

---

## 6. Recommendation

**ADOPT Koka-style deep handlers with:**
1. Evidence passing for performance
2. Tail-resumptive optimization
3. Multi-shot support where needed
4. Scoped handlers for security
5. Linear continuation option for resources

**Key insight:** Combine Koka's performance with Effekt's security model.

---

*Comparison document for TERAS-LANG Research Track — Domain B*
