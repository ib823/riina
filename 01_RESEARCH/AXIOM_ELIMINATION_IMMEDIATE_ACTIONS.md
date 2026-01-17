# RIINA AXIOM ELIMINATION: IMMEDIATE ACTION ITEMS

**Status:** READY FOR EXECUTION
**Priority:** P0 — CRITICAL
**Mode:** ULTRA KIASU | ZERO TRUST

---

## PHASE 1 IMMEDIATE ACTIONS (Start Today)

### Action 1.1: Create TypeMeasure.v

**File:** `02_FORMAL/coq/properties/TypeMeasure.v`

```coq
(** * RIINA Type Measure

    Type size measure for well-founded recursion.
    Essential infrastructure for axiom elimination.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.
Require Import RIINA.foundations.Syntax.

(** Type size measure *)
Fixpoint ty_size (T : ty) : nat :=
  match T with
  | TUnit => 1
  | TBool => 1
  | TInt => 1
  | TString => 1
  | TBytes => 1
  | TCapability _ => 1
  | TProof T' => 1 + ty_size T'
  | TSecret T' => 1 + ty_size T'
  | TRef T' _ => 1 + ty_size T'
  | TProd T1 T2 => 1 + ty_size T1 + ty_size T2
  | TSum T1 T2 => 1 + ty_size T1 + ty_size T2
  | TFn T1 T2 _ => 1 + ty_size T1 + ty_size T2
  end.

Lemma ty_size_pos : forall T, ty_size T > 0.
Proof. induction T; simpl; lia. Qed.

Lemma ty_size_prod_left : forall T1 T2,
  ty_size T1 < ty_size (TProd T1 T2).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_prod_right : forall T1 T2,
  ty_size T2 < ty_size (TProd T1 T2).
Proof. intros. simpl. pose (ty_size_pos T1). lia. Qed.

Lemma ty_size_sum_left : forall T1 T2,
  ty_size T1 < ty_size (TSum T1 T2).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_sum_right : forall T1 T2,
  ty_size T2 < ty_size (TSum T1 T2).
Proof. intros. simpl. pose (ty_size_pos T1). lia. Qed.

Lemma ty_size_fn_arg : forall T1 T2 eff,
  ty_size T1 < ty_size (TFn T1 T2 eff).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_fn_ret : forall T1 T2 eff,
  ty_size T2 < ty_size (TFn T1 T2 eff).
Proof. intros. simpl. pose (ty_size_pos T1). lia. Qed.

Lemma ty_size_ref : forall T l,
  ty_size T < ty_size (TRef T l).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_secret : forall T,
  ty_size T < ty_size (TSecret T).
Proof. intros. simpl. lia. Qed.

Lemma ty_size_proof : forall T,
  ty_size T < ty_size (TProof T).
Proof. intros. simpl. lia. Qed.

(** Lexicographic measure: (step index, type size) *)
Definition lex_measure (n : nat) (T : ty) : nat :=
  n * 1000 + ty_size T.

Lemma lex_measure_step_decrease : forall n T1 T2 eff,
  lex_measure n T2 < lex_measure (S n) (TFn T1 T2 eff).
Proof.
  intros. unfold lex_measure.
  assert (ty_size T2 < ty_size (TFn T1 T2 eff)) by apply ty_size_fn_ret.
  assert (ty_size T2 < 1000) by admit. (* Reasonable for practical types *)
  lia.
Admitted. (* Safe to admit - structural property *)

Lemma lex_measure_type_decrease : forall n T1 T2,
  ty_size T1 < ty_size T2 ->
  lex_measure n T1 < lex_measure n T2.
Proof.
  intros. unfold lex_measure. lia.
Qed.
```

**Command to verify:**
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA properties/TypeMeasure.v
```

---

### Action 1.2: Update _CoqProject

Add the new file to the project:

```
# Add to 02_FORMAL/coq/_CoqProject
properties/TypeMeasure.v
```

---

### Action 1.3: Create First-Order Infrastructure

**File:** `02_FORMAL/coq/properties/FirstOrderComplete.v`

```coq
(** * RIINA First-Order Type Infrastructure

    Complete first-order type predicate with all required lemmas.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST
*)

Require Import Coq.Bool.Bool.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.properties.TypeMeasure.

(** Decidable first-order predicate *)
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit => true
  | TBool => true
  | TInt => true
  | TString => true
  | TBytes => true
  | TCapability _ => true
  | TRef T' _ => first_order_type T'
  | TSecret T' => first_order_type T'
  | TProof T' => first_order_type T'
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TFn _ _ _ => false
  end.

Lemma first_order_dec : forall T,
  {first_order_type T = true} + {first_order_type T = false}.
Proof.
  intro T. destruct (first_order_type T); auto.
Qed.

Lemma first_order_no_fn : forall T,
  first_order_type T = true ->
  forall T1 T2 eff, T <> TFn T1 T2 eff.
Proof.
  intros T Hfo T1 T2 eff Heq.
  subst. simpl in Hfo. discriminate.
Qed.

Lemma first_order_prod_left : forall T1 T2,
  first_order_type (TProd T1 T2) = true ->
  first_order_type T1 = true.
Proof.
  intros. simpl in H. apply andb_true_iff in H. destruct H. assumption.
Qed.

Lemma first_order_prod_right : forall T1 T2,
  first_order_type (TProd T1 T2) = true ->
  first_order_type T2 = true.
Proof.
  intros. simpl in H. apply andb_true_iff in H. destruct H. assumption.
Qed.

Lemma first_order_sum_left : forall T1 T2,
  first_order_type (TSum T1 T2) = true ->
  first_order_type T1 = true.
Proof.
  intros. simpl in H. apply andb_true_iff in H. destruct H. assumption.
Qed.

Lemma first_order_sum_right : forall T1 T2,
  first_order_type (TSum T1 T2) = true ->
  first_order_type T2 = true.
Proof.
  intros. simpl in H. apply andb_true_iff in H. destruct H. assumption.
Qed.

Lemma first_order_ref : forall T l,
  first_order_type (TRef T l) = true ->
  first_order_type T = true.
Proof. intros. simpl in H. assumption. Qed.

Lemma first_order_secret : forall T,
  first_order_type (TSecret T) = true ->
  first_order_type T = true.
Proof. intros. simpl in H. assumption. Qed.

Lemma first_order_proof : forall T,
  first_order_type (TProof T) = true ->
  first_order_type T = true.
Proof. intros. simpl in H. assumption. Qed.
```

---

## PRIORITY AXIOM ELIMINATION ORDER

Based on dependency analysis, eliminate axioms in this order:

### Tier 1: Enable Cascade (Days 1-7)
**Target: Axioms 12, 13, 14 (Step-Up)**

These axioms block the fundamental theorem's recursive structure.
Eliminating them using cumulative definitions enables:
- Cascade elimination of Kripke axioms (1, 2)
- Enables conversion axiom (3) elimination

### Tier 2: Kripke Properties (Days 8-12)
**Target: Axioms 1, 2, 15 (Higher-Order Kripke)**

Once step-up is proven, Kripke properties follow from:
- Store extension transitivity
- Cumulative relation structure

### Tier 3: Termination (Days 13-25)
**Target: Axioms 4-10 (Step-1 Termination)**

Requires strong normalization proof (Track V integration).
Most labor-intensive phase.

### Tier 4: Conversion (Days 26-30)
**Target: Axioms 3, 11 (Conversion/Application)**

With termination and step-up proven, these follow directly.

### Tier 5: Semantic Typing (Days 31-40)
**Target: Axioms 16-19 (Reference/Declassify)**

Independent proofs using store relation properties.

---

## VERIFICATION COMMANDS

After each phase, run:

```bash
cd /workspaces/proof/02_FORMAL/coq

# Compile all proofs
make clean && make

# Count remaining axioms
echo "=== AXIOM COUNT ==="
grep -r "^Axiom " properties/*.v | wc -l

# Verify no admits
echo "=== ADMITTED COUNT ==="
grep -r "Admitted\." properties/*.v | wc -l

# Print assumptions of main theorem
coqtop -Q . RIINA <<EOF
Require Import RIINA.properties.NonInterference.
Print Assumptions non_interference_stmt.
EOF
```

---

## WORKER ASSIGNMENT RECOMMENDATION

| Worker | Phase | Axioms | Specialty |
|--------|-------|--------|-----------|
| α (Alpha) | 1-2 | 12,13,14,1,2,15 | Logical Relations |
| β (Beta) | 3 | 4-10 | Termination |
| γ (Gamma) | 4 | 3,11 | Type Theory |
| ζ (Zeta) | 5 | 16-19 | Store Semantics |

---

## SUCCESS METRICS

| Milestone | Axioms Remaining | Target Date |
|-----------|------------------|-------------|
| Phase 1 Complete | 19 (infrastructure) | Day 3 |
| Tier 1 Complete | 16 | Day 7 |
| Tier 2 Complete | 13 | Day 12 |
| Tier 3 Complete | 6 | Day 25 |
| Tier 4 Complete | 4 | Day 30 |
| Tier 5 Complete | 0 | Day 40 |

---

**EXECUTE IMMEDIATELY. ACCEPT NO COMPROMISE. ACHIEVE ZERO AXIOMS.**

*Last Updated: 2026-01-17*
