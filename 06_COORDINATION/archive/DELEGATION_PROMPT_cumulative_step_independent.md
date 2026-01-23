# ULTIMATE DELEGATION PROMPT: val_rel_le_fo_step_independent Fix

## Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR

## CRITICAL INSTRUCTIONS

1. **READ THIS ENTIRE PROMPT** before writing any code
2. **DO NOT ASSUME** anything not explicitly stated
3. **DO NOT USE AXIOMS** - all proofs must end with `Qed`
4. **VERIFY** every step compiles before proceeding
5. Output a **SINGLE SELF-CONTAINED .v FILE** that compiles independently

---

## THE PROBLEM

We have a lemma `val_rel_le_fo_step_independent` that is ADMITTED because of a fundamental gap:

```coq
Lemma val_rel_le_fo_step_independent : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m > 0 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
```

**The Gap:** At m = 1 for compound types (TProd, TSum):
- val_rel_le 1 gives outer structure (v1 = EPair a1 b1, v2 = EPair a2 b2)
- Component relations are at step 0: `val_rel_le 0 = True` (NO INFO!)
- We need `val_rel_le (S n'')` for components but can't step up from True

---

## THE SOLUTION STRATEGY

For first-order types, the structural relation is **PREDICATE-INDEPENDENT**. We use a three-step approach:

1. **Define** `val_rel_at_type_fo` - structural relation independent of step index
2. **Prove extraction**: `val_rel_le m` (m > 0, FO type) → `val_rel_at_type_fo`
3. **Prove construction**: `val_rel_at_type_fo` + value + closed → `val_rel_le n` (any n > 0)

Then: `val_rel_le m` → extract → `val_rel_at_type_fo` → construct → `val_rel_le n`

---

## COMPLETE TYPE DEFINITIONS

```coq
(** Type aliases *)
Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition label := string.
Definition effect_label := string.
Definition effect := list effect_label.

(** Core types - MUST match exactly *)
Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TFn : ty -> ty -> effect -> ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> security_level -> ty
  | TSecret : ty -> ty
  | TLabeled : ty -> label -> ty.

(** Expressions *)
Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : nat -> expr
  | EVar : ident -> expr
  | ELam : ident -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | EInl : expr -> ty -> expr
  | EInr : expr -> ty -> expr
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  | ERef : expr -> security_level -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr.
```

---

## VALUE PREDICATE

```coq
Fixpoint value (e : expr) : Prop :=
  match e with
  | EUnit => True
  | EBool _ => True
  | EInt _ => True
  | EString _ => True
  | ELoc _ => True
  | ELam _ _ _ => True
  | EPair e1 e2 => value e1 /\ value e2
  | EInl e _ => value e
  | EInr e _ => value e
  | _ => False
  end.
```

---

## FIRST-ORDER TYPE PREDICATE

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList _ | TOption _ => true
  | TRef _ _ => true
  | TSecret _ | TLabeled _ _ => true
  end.
```

**CRITICAL LEMMAS TO PROVE:**

```coq
Lemma first_order_type_prod : forall T1 T2,
  first_order_type (TProd T1 T2) = true ->
  first_order_type T1 = true /\ first_order_type T2 = true.

Lemma first_order_type_sum : forall T1 T2,
  first_order_type (TSum T1 T2) = true ->
  first_order_type T1 = true /\ first_order_type T2 = true.
```

---

## CLOSED EXPRESSION

```coq
Fixpoint free_vars (e : expr) : list ident :=
  match e with
  | EUnit | EBool _ | EInt _ | EString _ | ELoc _ => nil
  | EVar x => x :: nil
  | ELam x _ body => remove string_dec x (free_vars body)
  | EApp e1 e2 | EPair e1 e2 | EAssign e1 e2 => free_vars e1 ++ free_vars e2
  | EFst e | ESnd e | EInl e _ | EInr e _ | ERef e _ | EDeref e => free_vars e
  | ECase e x1 e1 x2 e2 =>
      free_vars e ++ remove string_dec x1 (free_vars e1) ++ remove string_dec x2 (free_vars e2)
  | EIf e1 e2 e3 => free_vars e1 ++ free_vars e2 ++ free_vars e3
  | ELet x e1 e2 => free_vars e1 ++ remove string_dec x (free_vars e2)
  end.

Definition closed_expr (e : expr) : Prop := free_vars e = nil.
```

**CRITICAL LEMMAS TO PROVE:**

```coq
Lemma closed_pair : forall e1 e2,
  closed_expr (EPair e1 e2) -> closed_expr e1 /\ closed_expr e2.

Lemma closed_inl : forall e T,
  closed_expr (EInl e T) -> closed_expr e.

Lemma closed_inr : forall e T,
  closed_expr (EInr e T) -> closed_expr e.

Lemma value_pair : forall e1 e2,
  value (EPair e1 e2) -> value e1 /\ value e2.

Lemma value_inl : forall e T,
  value (EInl e T) -> value e.

Lemma value_inr : forall e T,
  value (EInr e T) -> value e.
```

---

## STORE TYPING

```coq
Definition store_ty := list (ty * security_level).
```

---

## STEP 1: PREDICATE-INDEPENDENT STRUCTURAL RELATION

This is the KEY definition. It captures structural equality for first-order types WITHOUT any step index or predicate parameters.

```coq
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  (* Primitive types: exact equality *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2

  (* Security types: indistinguishable *)
  | TSecret _ => True
  | TLabeled _ _ => True

  (* Reference: same location *)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l

  (* Collections: simplified *)
  | TList _ => True
  | TOption _ => True

  (* Product: component-wise recursion *)
  | TProd T1 T2 =>
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2

  (* Sum: matching constructor *)
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2)
      \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)

  (* Function: not first-order *)
  | TFn _ _ _ => True
  end.
```

---

## STEP 2: CUMULATIVE VALUE RELATION (val_rel_le)

```coq
(** Structural part at a specific step *)
Definition val_rel_struct (val_rel_prev : store_ty -> ty -> expr -> expr -> Prop)
                          (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret _ | TLabeled _ _ => True
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList _ | TOption _ => True
  | TProd T1 T2 =>
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_prev Σ T1 a1 a2 /\
        val_rel_prev Σ T2 b1 b2
  | TSum T1 T2 =>
      (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\
                     val_rel_prev Σ T1 a1 a2) \/
      (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\
                     val_rel_prev Σ T2 b1 b2)
  | TFn T1 T2 eff => True  (* Simplified for FO focus *)
  end.

(** Cumulative relation *)
Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      val_rel_le n' Σ T v1 v2 /\
      val_rel_struct (val_rel_le n') Σ T v1 v2
  end.
```

---

## STEP 3: THE EXTRACTION LEMMA

**THIS IS CRITICAL.** Prove that val_rel_le at any step > 0 gives val_rel_at_type_fo:

```coq
Lemma val_rel_le_extract_fo : forall n Σ T v1 v2,
  first_order_type T = true ->
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  val_rel_at_type_fo T v1 v2.
```

**PROOF STRATEGY:**
1. Destruct n as S n'
2. From val_rel_le (S n'), extract val_rel_struct
3. val_rel_struct gives value, closed, and type-specific structure
4. For TProd/TSum: extract component structure recursively
5. **KEY INSIGHT:** At step 1, outer structure is known. Components at step 0 = True.
   BUT: we also have value/closed for components (from value/closed of outer).
   For PRIMITIVE component types (TInt, TBool, etc.), the structural info comes
   from val_rel_struct directly, NOT from recursion.

**THE TRICK FOR COMPOUND TYPES:**
When T = TProd T1 T2 and n = 1:
- val_rel_struct gives: v1 = EPair a1 b1, v2 = EPair a2 b2
- Component relations: val_rel_le 0 = True (no info)
- BUT: We need to BUILD val_rel_at_type_fo T1 a1 a2

SOLUTION: Use well-founded induction on TYPE STRUCTURE, not step index.
- For primitive T1: val_rel_at_type_fo is determined by the VALUES themselves
- For compound T1: recurse on type structure

Actually, the issue is that val_rel_le 1 for TProd does NOT guarantee component equality!
At step 1, we only know the SHAPE (it's a pair), not that components are equal.

**REVISED APPROACH:**
The lemma as stated may be UNPROVABLE for compound types at m = 1.

Instead, prove a WEAKER but USEFUL lemma:

```coq
(** For primitive first-order types, step independence holds at m >= 1 *)
Lemma val_rel_le_fo_step_independent_primitive : forall m n Σ T v1 v2,
  first_order_type T = true ->
  match T with TProd _ _ | TSum _ _ => False | _ => True end ->
  m > 0 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.

(** For compound first-order types, require m >= 2 *)
Lemma val_rel_le_fo_step_independent_compound : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m >= 2 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
```

---

## ALTERNATIVE: UNIFIED LEMMA WITH TYPE DEPTH

Define type depth (maximum nesting of TProd/TSum):

```coq
Fixpoint type_depth (T : ty) : nat :=
  match T with
  | TProd T1 T2 => 1 + max (type_depth T1) (type_depth T2)
  | TSum T1 T2 => 1 + max (type_depth T1) (type_depth T2)
  | _ => 0
  end.
```

Then the unified lemma:

```coq
Lemma val_rel_le_fo_step_independent : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m > type_depth T ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
```

This ensures we have enough steps for full structural information.

---

## YOUR TASK

Create a **SINGLE SELF-CONTAINED .v FILE** that:

1. Defines all types, predicates, and relations as specified above
2. Proves the helper lemmas (first_order_type decomposition, value/closed for pairs/sums)
3. Proves EITHER:
   - Option A: Two separate lemmas (primitive + compound with m >= 2)
   - Option B: Unified lemma with type_depth premise

4. All proofs must end with `Qed` - NO AXIOMS, NO ADMITTED

5. Include `Print Assumptions` for all main theorems to verify ZERO axioms

---

## REQUIRED IMPORTS

```coq
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Import ListNotations.
```

---

## VERIFICATION CHECKLIST

Before submitting, verify:

1. [ ] File compiles with `coqc` without errors
2. [ ] All proofs end with `Qed`
3. [ ] `Print Assumptions` shows "Closed under the global context" for all main lemmas
4. [ ] No `Axiom`, `Parameter`, `Admitted`, or `admit` anywhere

---

## OUTPUT FORMAT

Provide ONLY the complete .v file content. Do not include explanations outside the file.
The file should be named: `val_rel_le_fo_step_independent_PROOF.v`

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR*
*"QED Eternum."*
