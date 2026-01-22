# Claude.ai Delegation Package - Session 32

## Overview

This document contains self-contained proof tasks that can be completed by Claude.ai web interface.
Each package is independent and can be worked on separately.

---

## PACKAGE A: ApplicationComplete Base Cases (EASY)

### Target File: `properties/ApplicationComplete.v`

### Task: Prove val_rel_n at step 1 for base types

These are straightforward structural proofs using the val_rel_n definition.

### Context: val_rel_n Definition

```coq
(* val_rel_n for S n unfolds to: *)
val_rel_n (S n) Σ T v1 v2 =
  val_rel_n n Σ T v1 v2 /\
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  val_rel_at_type Σ (store_rel_n n) (val_rel_n n) (store_rel_n n) T v1 v2

(* val_rel_at_type for base types: *)
val_rel_at_type _ _ _ _ TUnit v1 v2 = (v1 = EUnit /\ v2 = EUnit)
val_rel_at_type _ _ _ _ TBool v1 v2 = (exists b, v1 = EBool b /\ v2 = EBool b)
val_rel_at_type _ _ _ _ TInt v1 v2 = (exists i, v1 = EInt i /\ v2 = EInt i)
val_rel_at_type _ _ _ _ TString v1 v2 = (exists s, v1 = EString s /\ v2 = EString s)

(* val_rel_n 0 Σ T v1 v2 carries structural info for FO types *)
val_rel_n 0 Σ T v1 v2 =
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)
```

### Lemma 1: val_rel_n_1_unit

```coq
Lemma val_rel_n_1_unit : forall Σ,
  val_rel_n 1 Σ TUnit EUnit EUnit.
Proof.
  intros Σ.
  (* Goal: val_rel_n 1 Σ TUnit EUnit EUnit *)
  (* Unfold val_rel_n (S 0) = val_rel_n 0 /\ value /\ value /\ closed /\ closed /\ val_rel_at_type *)
  simpl.
  repeat split.
  - (* val_rel_n 0: for TUnit, this requires value, closed, and val_rel_at_type_fo *)
    simpl. repeat split.
    + apply VUnit.  (* value EUnit *)
    + apply VUnit.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + (* val_rel_at_type_fo TUnit = v1 = EUnit /\ v2 = EUnit *) auto.
  - apply VUnit.
  - apply VUnit.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - (* val_rel_at_type TUnit EUnit EUnit = EUnit = EUnit /\ EUnit = EUnit *) auto.
Qed.
```

### Lemma 2: val_rel_n_1_bool

```coq
Lemma val_rel_n_1_bool : forall Σ b,
  val_rel_n 1 Σ TBool (EBool b) (EBool b).
Proof.
  intros Σ b.
  simpl.
  repeat split.
  - simpl. repeat split.
    + apply VBool.
    + apply VBool.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + exists b. auto.
  - apply VBool.
  - apply VBool.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - exists b. auto.
Qed.
```

### Lemma 3: val_rel_n_1_int

```coq
Lemma val_rel_n_1_int : forall Σ i,
  val_rel_n 1 Σ TInt (EInt i) (EInt i).
Proof.
  intros Σ i.
  simpl.
  repeat split.
  - simpl. repeat split.
    + apply VInt.
    + apply VInt.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + exists i. auto.
  - apply VInt.
  - apply VInt.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - exists i. auto.
Qed.
```

### Lemma 4: val_rel_n_1_string

```coq
Lemma val_rel_n_1_string : forall Σ s,
  val_rel_n 1 Σ TString (EString s) (EString s).
Proof.
  intros Σ s.
  simpl.
  repeat split.
  - simpl. repeat split.
    + apply VString.
    + apply VString.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + exists s. auto.
  - apply VString.
  - apply VString.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - unfold closed_expr. intros x Hfree. inversion Hfree.
  - exists s. auto.
Qed.
```

### Expected Output

Provide the complete proof script for each lemma. Verify that:
1. All proofs end with `Qed.` (not `Admitted.`)
2. No axioms are introduced
3. Only uses standard Coq tactics (simpl, repeat split, auto, apply, etc.)

---

## PACKAGE B: KripkeMutual Store Weakening (MEDIUM)

### Target File: `properties/KripkeMutual.v`

### Task: Prove store relation weakening lemmas

These lemmas show that store relations are preserved when weakening the store typing.

### Context: Key Definitions

```coq
(* Store typing extension - Σ' extends Σ *)
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
                 store_ty_lookup l Σ' = Some (T, sl).

(* Store relation at step n *)
store_rel_n n Σ st1 st2 :=
  match n with
  | 0 => store_max st1 = store_max st2
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        forall v1 v2,
          store_lookup l st1 = Some v1 ->
          store_lookup l st2 = Some v2 ->
          val_rel_n n' Σ T v1 v2)
  end.

(* For FIRST-ORDER types, val_rel_n doesn't depend on Σ *)
(* This is because val_rel_at_type_fo only checks structural equality *)
```

### Lemma 1: store_rel_n_weaken_aux

```coq
(* Store relation weakening: if stores are related at Σ', they're related at Σ ⊆ Σ' *)
Lemma store_rel_n_weaken_aux : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  (* HINT: Induction on n *)
  (* For n = 0: store_rel_n 0 just checks store_max equality, independent of Σ *)
  (* For n = S n':
     - IH gives store_rel_n n' Σ st1 st2
     - store_max equality preserved
     - For the val_rel_n part: if l is in Σ, it's also in Σ' by extension
       Use the hypothesis store_rel_n (S n') Σ' st1 st2 which gives
       val_rel_n n' Σ' T v1 v2 for locations in Σ'
     - Need: val_rel_n doesn't depend on Σ for FO types (use val_rel_n_weaken_fo)
  *)
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hext Hrel.
  - (* n = 0 *)
    simpl in *. exact Hrel.
  - (* n = S n' *)
    simpl in *.
    destruct Hrel as [Hrel' [Hmax Hvals]].
    repeat split.
    + (* store_rel_n n' Σ st1 st2 *)
      apply IH with Σ'; assumption.
    + (* store_max st1 = store_max st2 *)
      exact Hmax.
    + (* val_rel_n for locations in Σ *)
      intros l T sl Hlook v1 v2 Hlook1 Hlook2.
      (* l is in Σ, so by extension l is in Σ' *)
      apply Hext in Hlook.
      (* Use Hvals with the extended lookup *)
      specialize (Hvals l T sl Hlook v1 v2 Hlook1 Hlook2).
      (* Hvals : val_rel_n n' Σ' T v1 v2 *)
      (* Need: val_rel_n n' Σ T v1 v2 *)
      (* For FO types, use val_rel_n_weaken_fo *)
      (* For HO types, this requires frame property *)
      admit. (* Requires val_rel_n_weaken or case analysis on T *)
Admitted.
```

### Key Insight for Completion

The proof requires showing that `val_rel_n n' Σ' T v1 v2 -> val_rel_n n' Σ T v1 v2` when `Σ ⊆ Σ'`.

For **first-order types**, this is straightforward because `val_rel_at_type_fo` doesn't reference Σ at all.

For **higher-order types** (TFn), the situation is subtle because function bodies may reference locations in Σ. However, since we're weakening (going from larger Σ' to smaller Σ), and the function bodies only need locations that exist when the function was created, this should still work.

**Strategy**:
1. Use `first_order_type T` as a decision point
2. For FO types: use `val_rel_n_weaken_fo` (should exist or be provable)
3. For HO types: use the frame property or prove directly

---

## PACKAGE C: val_rel_n Step-Up for First-Order Types (MEDIUM)

### Target File: `properties/AxiomEliminationVerified.v`

### Task: Prove step-up lemma for first-order types

### Context

```coq
(* For first-order types, val_rel_at_type equals val_rel_at_type_fo *)
Lemma val_rel_at_type_fo_equiv : forall T Σ sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 <-> val_rel_at_type_fo T v1 v2.

(* val_rel_at_type_fo is step-independent - it only checks structural equality *)
(* This means for FO types, the step index doesn't affect the semantic content *)
```

### Lemma: val_rel_n_step_up_fo_typed_pos

```coq
Lemma val_rel_n_step_up_fo_typed_pos : forall n Σ T v1 v2,
  n > 0 ->
  first_order_type T = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hpos Hfo Hv1 Hv2 Hc1 Hc2 Hn.
  (* Since n > 0, write n = S n' *)
  destruct n as [| n']. { lia. }
  (* Have: val_rel_n (S n') Σ T v1 v2 *)
  (* Want: val_rel_n (S (S n')) Σ T v1 v2 *)

  (* Unfold both *)
  simpl in Hn.
  destruct Hn as [Hn' [Hv1' [Hv2' [Hc1' [Hc2' Hrat]]]]].
  (* Hrat : val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2 *)

  simpl.
  repeat split.
  - (* val_rel_n (S n') Σ T v1 v2 : reconstruct *)
    simpl. repeat split; try assumption.
  - exact Hv1'.
  - exact Hv2'.
  - exact Hc1'.
  - exact Hc2'.
  - (* val_rel_at_type for step S n' *)
    (* Key: For FO types, val_rel_at_type = val_rel_at_type_fo which is step-independent *)
    (* Use val_rel_at_type_fo_equiv to convert *)
    pose proof (val_rel_at_type_fo_equiv T Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo) as Hiff_n.
    pose proof (val_rel_at_type_fo_equiv T Σ (store_rel_n (S n')) (val_rel_n (S n')) (store_rel_n (S n')) v1 v2 Hfo) as Hiff_Sn.
    (* Extract val_rel_at_type_fo from Hrat using forward direction of Hiff_n *)
    apply Hiff_n in Hrat.
    (* Convert back using backward direction of Hiff_Sn *)
    apply Hiff_Sn.
    exact Hrat.
Qed.
```

### Expected Output

Verify the proof compiles and ends with `Qed.`

---

## Submission Instructions

1. Copy each proof to Claude.ai web interface
2. Ask Claude to verify the proof compiles
3. If errors occur, ask Claude to fix them
4. Return the working proof scripts

## Priority

1. **PACKAGE A** (Highest) - Simple, independent proofs
2. **PACKAGE C** (Medium) - Important for axiom elimination
3. **PACKAGE B** (Lower) - More complex, may need iteration

---

*Generated: Session 32, 2026-01-22*
*Classification: RIINA AXIOM ELIMINATION*
