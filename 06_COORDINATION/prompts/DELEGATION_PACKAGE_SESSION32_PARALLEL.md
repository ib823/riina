# Claude.ai Delegation Package - Session 32 Parallel Work

## Generated: 2026-01-22
## Purpose: Parallel axiom/admit elimination for RIINA Coq proofs

---

# PACKAGE A: AxiomEliminationVerified.v - exp_rel_step1 Lemmas (8 admits)

## Context

These lemmas prove that single-step evaluation preserves the step-indexed logical relation at step 1. The key insight is that for values, evaluation is deterministic and preserves structure.

## Key Definitions (from NonInterference_v2.v)

```coq
(* val_rel_n 0 for v2 semantics *)
val_rel_n 0 Σ T v1 v2 =
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)

(* store_rel_n 0 *)
store_rel_n 0 Σ st1 st2 = (store_max st1 = store_max st2)

(* val_rel_at_type_fo for products *)
val_rel_at_type_fo (TProd T1 T2) v1 v2 =
  exists x1 y1 x2 y2,
    v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
    val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
```

## Lemma 1: exp_rel_step1_fst_typed

```coq
Lemma exp_rel_step1_fst_typed : forall Γ Σ Σ' T1 T2 v v' st1 st2 ctx ε,
  has_type Γ Σ' Public v (TProd T1 T2) ε ->
  has_type Γ Σ' Public v' (TProd T1 T2) ε ->
  value v -> value v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EFst v, st1, ctx) -->* (a1, st1', ctx') /\
    (EFst v', st2, ctx) -->* (a2, st2', ctx') /\
    value a1 /\ value a2 /\
    val_rel_n 0 Σ'' T1 a1 a2 /\
    store_rel_n 0 Σ'' st1' st2'.
```

**Proof Strategy**:
1. Since v, v' are values of type TProd T1 T2, by canonical forms they are EPair a1 b1 and EPair a2 b2
2. EFst (EPair a b) --> a in one step (ST_FstPair)
3. Store doesn't change, so st1' = st1, st2' = st2
4. Σ'' = Σ' (no new allocations)
5. Need to show val_rel_n 0 Σ' T1 a1 a2 - extract from product typing

## Lemma 2: exp_rel_step1_snd_typed

Same as above but for ESnd - extracts second component.

## Lemma 3: exp_rel_step1_let_typed

```coq
Lemma exp_rel_step1_let_typed : forall Σ Σ' T v v' x e2 e2' st1 st2 ctx,
  value v -> value v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists r1 r2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (ELet x v e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ELet x v' e2', st2, ctx) -->* (r2, st2', ctx') /\
    val_rel_n 0 Σ'' T r1 r2 /\
    store_rel_n 0 Σ'' st1' st2'.
```

**Proof Strategy**:
1. ELet x v e2 --> subst x v e2 in one step (ST_LetValue)
2. The result depends on e2 - this lemma may need additional premises about e2, e2' being related

## Expected Output

A Coq file with proofs for exp_rel_step1_fst_typed and exp_rel_step1_snd_typed. Use these patterns:
- `canonical_forms_prod` for extracting pair structure from typed values
- `inversion` on has_type for product types
- `econstructor` for existentials
- Store doesn't change for pure operations, so st1' = st1, Σ'' = Σ'

---

# PACKAGE B: MasterTheorem.v - Composition Lemmas (9 admits)

## Context

MasterTheorem.v builds the final non-interference theorem by composing proofs from different components. The admits are typically about composing relations.

## Key Pattern

Most admits follow this pattern:
```coq
(* Given *)
val_rel_n n Σ T v1 v2
store_rel_n n Σ st1 st2
(* Some operation preserving the relation *)
(* Conclude *)
val_rel_n n Σ' T' v1' v2'
store_rel_n n Σ' st1' st2'
```

## Specific Admits to Prove

1. **Relation composition under evaluation**
2. **Store extension preservation**
3. **Context weakening for relations**

## Proof Techniques

- Use `val_rel_n_mono_store` for store extension
- Use `store_rel_n_weaken` for weakening
- Use transitivity of store_ty_extends

---

# PACKAGE C: ReferenceOps.v - Reference Operations (6 admits)

## Context

ReferenceOps.v handles the semantic properties of reference operations (ref, deref, assign). These are critical for proving AX-01, AX-02, AX-03.

## Key Definitions

```coq
(* Fresh location *)
fresh_loc st = store_max st

(* Store update *)
store_update l v st = update the mapping at location l to value v

(* Store allocation *)
store_alloc v st = (fresh_loc st, store with v at fresh_loc st)
```

## Lemmas Needed

1. **fresh_loc_not_in_store**: fresh_loc st is not in the domain of st
2. **store_update_preserves_other**: updating l doesn't affect l' ≠ l
3. **store_alloc_extends**: allocation extends the store typing

## Proof Strategy

- Use the definition of fresh_loc = store_max
- Induction on store structure if needed
- Properties follow from well-formedness of store typing

---

# PACKAGE D: NonInterferenceZero.v - Zero-Step Cases (5 admits)

## Context

Zero-step cases establish base cases for the step-indexed logical relation. In v2, step 0 is NOT trivial - it requires value, closed, and type structure.

## Key Insight

```coq
val_rel_n 0 Σ T v1 v2 =
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)
```

So zero-step cases need to establish:
1. Both expressions are values
2. Both are closed
3. For FO types: structural equality (same constructor, related components)

## Proof Pattern

```coq
Proof.
  intros.
  rewrite val_rel_n_0_unfold.
  repeat split; try assumption.
  (* For the type-specific part *)
  destruct (first_order_type T) eqn:Hfo.
  - (* FO case: need val_rel_at_type_fo *)
    simpl. (* case analysis on T *)
  - (* HO case: trivial True *)
    auto.
Qed.
```

---

# PACKAGE E: KripkeMutual.v - Kripke Monotonicity (3 admits)

## Context

Kripke monotonicity says that if values are related at one store typing, they remain related at an extended store typing. This is crucial for handling allocation.

## Key Theorem

```coq
val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2
```

## Proof Strategy

For first-order types, this is straightforward because val_rel_at_type_fo doesn't depend on the store typing.

For function types (TFn), this requires showing that the function body evaluation still works with the extended store - this is the "Kripke" property.

## FO Version (Already Proven)

```coq
Lemma val_rel_n_mono_store_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
```

The general version needs induction on the type structure with special handling for TFn.

---

# INSTRUCTIONS FOR CLAUDE.AI

## Setup

1. Create a new Coq file for your proofs
2. Start with these imports:
```coq
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.NonInterference_v2.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
```

3. Use the unfolding lemmas:
```coq
val_rel_n_0_unfold
val_rel_n_S_unfold
store_rel_n_0_unfold
store_rel_n_S_unfold
```

## Proof Style

- Use `intros` to introduce hypotheses
- Use `rewrite` with unfolding lemmas
- Use `repeat split; try assumption` for conjunctions
- Use `destruct` for case analysis
- Use `exists` or `econstructor` for existentials
- End with `Qed.` (no `Admitted.`)

## Deliverable

For each package, provide:
1. Complete Coq proof code
2. Any helper lemmas needed
3. Notes on any blocking issues

## Priority Order

1. Package D (NonInterferenceZero) - Foundation
2. Package A (exp_rel_step1) - Most admits
3. Package C (ReferenceOps) - Critical for axiom proofs
4. Package E (KripkeMutual) - Needed for composition
5. Package B (MasterTheorem) - Final assembly

---

# VERIFICATION

After completing proofs, verify with:
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA your_proof_file.v
```

The proof compiles if there are no errors.

---

*Mode: ULTRA KIASU | ZERO TRUST | ZERO ADMITS*
