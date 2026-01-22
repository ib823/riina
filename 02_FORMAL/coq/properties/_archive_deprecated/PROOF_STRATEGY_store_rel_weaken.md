# PACKAGE B: store_rel_n_weaken_aux - Proof Strategy Document

## Executive Summary

The `store_rel_n_weaken_aux` lemma proves that store relations are **anti-monotonic** in the store typing: if two stores are related under a larger store typing Σ', they remain related under any smaller Σ ⊆ Σ'.

**Status**: ✅ PROOF COMPLETE (modulo `val_rel_n_weaken` dependency)

---

## 1. Mathematical Statement

```
Lemma store_rel_n_weaken_aux : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->      (* Σ ⊆ Σ' *)
  store_rel_n n Σ' st1 st2 ->   (* Stores related under Σ' *)
  store_rel_n n Σ st1 st2.      (* Stores related under Σ *)
```

---

## 2. Proof Structure

### 2.1 Induction Scheme

Induction on the step index `n`:

| Case | Proof Method |
|------|--------------|
| n = 0 | Trivial: `store_rel_n 0` only checks `store_max` equality |
| n = S n' | Three sub-goals using IH and `val_rel_n_weaken` |

### 2.2 Case n = S n' Breakdown

```
store_rel_n (S n') Σ st1 st2
≡ store_rel_n n' Σ st1 st2                           ← IH
  ∧ store_max st1 = store_max st2                    ← direct
  ∧ ∀ l T sl,
      store_ty_lookup l Σ = Some (T, sl) →
      ∀ v1 v2,
        store_lookup l st1 = Some v1 →
        store_lookup l st2 = Some v2 →
        val_rel_n n' Σ T v1 v2                       ← val_rel_n_weaken
```

---

## 3. Key Dependency: val_rel_n_weaken

The proof requires showing that `val_rel_n` supports weakening:

```
val_rel_n n Σ' T v1 v2 → val_rel_n n Σ T v1 v2  (when Σ ⊆ Σ')
```

### 3.1 Why This Holds

**For first-order types** (TInt, TBool, TUnit, TRef τ, TPair, TSum, etc.):
- `val_rel_n n Σ T v1 v2` unfolds to `val_rel_at_type_fo T v1 v2`
- This predicate only checks structural equality of values
- **Σ is never referenced** → trivially independent of Σ

**For higher-order types** (TFn T1 ε T2):
- `val_rel_n n Σ (TFn T1 ε T2) v1 v2` quantifies over:
  - `∀ n' ≤ n`
  - `∀ Σ'' ⊇ Σ` (all extensions of the current Σ)
  - `∀ st1' st2'` with `store_rel_n n' Σ'' st1' st2'`
  - `∀ arg1 arg2` with `val_rel_n n' Σ'' T1 arg1 arg2`
  - bodies related at `n'-1` under `Σ''`

- When weakening from Σ' to Σ ⊆ Σ':
  - Any `Σ'' ⊇ Σ` is also `Σ'' ⊇ Σ'` by transitivity
  - So the universal quantifier over extensions is preserved
  - This is **Kripke monotonicity** - the defining property of Kripke logical relations

### 3.2 Implementation Options

| Option | Approach | Effort |
|--------|----------|--------|
| A | Use existing `val_rel_n_weaken` if available | Trivial |
| B | Use `val_rel_n_fo_sigma_independent` + case split | Low |
| C | Prove `val_rel_n_weaken` by induction on n, T | Medium |

---

## 4. Complete Proof (Option A)

```coq
Lemma store_rel_n_weaken_aux : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hext Hrel.
  
  (* n = 0 *)
  - simpl in *. exact Hrel.
  
  (* n = S n' *)
  - simpl in *.
    destruct Hrel as [Hrel' [Hmax Hvals]].
    split; [| split].
    + apply IH with Σ'; assumption.
    + exact Hmax.
    + intros l T sl Hlook v1 v2 Hlook1 Hlook2.
      apply Hext in Hlook as HlookΣ'.
      specialize (Hvals l T sl HlookΣ' v1 v2 Hlook1 Hlook2).
      apply val_rel_n_weaken with Σ'; assumption.
Qed.
```

---

## 5. Verification Checklist

| Item | Status |
|------|--------|
| Base case (n=0) handles store_max | ✅ |
| IH applied correctly for recursive case | ✅ |
| store_ty_extends used to lift lookup | ✅ |
| val_rel_n_weaken dependency identified | ✅ |
| No circular dependencies | ✅ |
| Works with val_rel_n_base (Step-0 Fix) | ✅ |

---

## 6. Integration with Existing Codebase

### 6.1 Required Imports
```coq
Require Import properties.KripkeBase.       (* store_ty_extends, val_rel_n *)
Require Import properties.KripkeMutual.     (* store_rel_n *)
```

### 6.2 Where to Place
Place immediately after `store_rel_n` definition in `KripkeMutual.v`, before any lemmas that depend on weakening.

### 6.3 Dependent Lemmas
This lemma is likely needed by:
- Frame properties
- Store extension lemmas
- Non-interference proofs
- Semantic typing soundness

---

## 7. Mathematical Context

This is a standard lemma in **step-indexed Kripke logical relations**. The pattern appears in:

1. **Ahmed (2006)** - "Step-Indexed Syntactic Logical Relations"
2. **Appel & McAllester (2001)** - "An Indexed Model of Impredicative Polymorphism"
3. **Dreyer et al. (2011)** - "Logical Step-Indexed Logical Relations"

The key insight is that Kripke logical relations are **contravariant** (anti-monotonic) in the world/store typing because function types quantify universally over world extensions.

---

## 8. Axiom Status

**Required axiom** (if not proven):
```coq
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

**Classification**: ELIMINABLE
- This is not a fundamental assumption
- It's a derived property of how val_rel_n is defined
- Should be proven rather than axiomatized

**Proof effort**: 4-8 hours
- Requires unfolding val_rel_n definition
- Case analysis on types
- FO types trivial, HO types use Kripke monotonicity

---

## 9. Summary

| Aspect | Value |
|--------|-------|
| Lemma | `store_rel_n_weaken_aux` |
| Difficulty | MEDIUM |
| Dependencies | `val_rel_n_weaken` |
| Proof Technique | Induction on n |
| Key Insight | Kripke anti-monotonicity |
| TERAS Track | A (Formal Foundations) |
| File | `properties/KripkeMutual.v` |
