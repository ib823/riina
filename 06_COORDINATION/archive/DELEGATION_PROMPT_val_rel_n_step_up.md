# CLAUDE AI DELEGATION PROMPT — val_rel_n_step_up

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  RIINA — Rigorous Immutable Invariant — Normalized Axiom                          ║
║  FORMAL PROOF DELEGATION: val_rel_n_step_up (Step-Indexed Step-Up Lemma)         ║
║                                                                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR              ║
║  "QED Eternum."                                               ║
║                                                                                  ║
║  DIFFICULTY: HARD — Requires careful understanding of step-indexed relations     ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## SECTION 0: MANDATORY MINDSET — READ AND INTERNALIZE COMPLETELY

Before you do ANYTHING, you MUST internalize these rules:

### Rule 1: Revolutionary Excellence
In whatever task you execute or document you generate, the mindset you MUST apply is that the solution is the most ideal that you can ever dream of. It will be the most revolutionary, disruptive, and first ever in human history, putting all other solutions to be TOTALLY OBSOLETE.

### Rule 2: Perfect Security — All Threats Obsolete
Any threats known or unknown, from the first threats or vulnerability ever recorded in human history to today/this exact second, and also any new threats upcoming and in the future are COMPLETELY OBSOLETE and will ALWAYS be obsolete as the solution is the PERFECT solution, and NO other solution will be better.

### Rule 3: ULTRA KIASU — Extreme Paranoid Verification
In any task, be EXTREMELY KIASU, EXTREMELY PARANOID, EXTREMELY NO-TRUST to anything you research or deep research until you can independently verify or validate. Trust NOTHING. Verify EVERYTHING.

### Rule 4: NO SHORTCUTS — INFINITE TIMELINE
You are NOT lazy. You know all shortcuts and what to skip or to summarize but you will NEVER EVER do that or resort to it. You will ensure everything is correctly executed based on the most fundamental or foundational work.

### Rule 5: EXTREME RIGOUR
Every proof must be COMPLETE with NO gaps, NO handwaving, NO "obvious" claims. Every single tactic must be justified. Every single step must be verified.

### Rule 6: NO ASSUMPTIONS
Do NOT assume anything that is not explicitly stated. Do NOT leave gaps for "the reader to fill in". Every definition, every lemma, every theorem must be COMPLETE and SELF-CONTAINED.

---

## SECTION 1: PROBLEM STATEMENT

### 1.1 What is Step-Indexed Logical Relations?

Step-indexed logical relations are a technique for proving properties of programs with:
- **Recursive types** (like functions that can call themselves)
- **Higher-order functions** (functions that take/return functions)
- **Mutable state** (references)

The key idea: instead of defining relatedness directly (which would be circular for recursive types), we define it **indexed by a natural number n** representing "how many computation steps we're willing to observe".

### 1.2 The Core Definitions

**val_rel_n n Σ T v1 v2** means: "values v1 and v2 are related at type T, observable for n steps, under store typing Σ"

The definition is:
- **At n = 0**: Basic structural check (values, closed, first-order structure)
- **At n = S n'**: Cumulative (includes n') PLUS structural relation at level n'

### 1.3 The Step-Up Problem

**QUESTION:** If `val_rel_n n Σ T v1 v2` holds, does `val_rel_n (S n) Σ T v1 v2` hold?

**ANSWER:** It depends on the type T!

| Type Category | Step-Up | Reason |
|---------------|---------|--------|
| **First-Order** (TUnit, TBool, TInt, TProd, TSum, TRef, etc.) | **YES, provable** | Structure is predicate-independent |
| **Higher-Order** (TFn) | **Needs typing** | Kripke property requires termination |

### 1.4 What You Must Prove

You must prove **val_rel_n_step_up_fo**: the step-up lemma for FIRST-ORDER types.

```coq
Theorem val_rel_n_step_up_fo : forall n Σ T v1 v2,
  first_order_type T = true ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
```

This is FULLY PROVABLE without external premises because for first-order types, the structural relation `val_rel_at_type` is equivalent to `val_rel_at_type_fo`, which does NOT depend on the step index predicates.

---

## SECTION 2: COMPLETE TYPE DEFINITIONS

```coq
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Import ListNotations.

Open Scope Z_scope.

(** ========================================================================
    BASIC TYPE ALIASES
    ======================================================================== *)

Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition label := string.
Definition effect_label := string.
Definition effect := list effect_label.

(** ========================================================================
    CORE TYPE DEFINITION
    ======================================================================== *)

Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TFn : ty -> ty -> effect -> ty      (* Function: TFn T1 T2 ε *)
  | TProd : ty -> ty -> ty              (* Product: TProd T1 T2 *)
  | TSum : ty -> ty -> ty               (* Sum: TSum T1 T2 *)
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> security_level -> ty   (* Reference: TRef T sl *)
  | TSecret : ty -> ty
  | TLabeled : ty -> label -> ty.

(** ========================================================================
    EXPRESSION DEFINITION
    ======================================================================== *)

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

(** ========================================================================
    VALUE PREDICATE
    ======================================================================== *)

Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc : forall l, value (ELoc l)
  | VLam : forall x T body, value (ELam x T body)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T).
```

---

## SECTION 3: FIRST-ORDER TYPE PREDICATE

```coq
(** ========================================================================
    FIRST-ORDER TYPE PREDICATE
    ========================================================================

    A type is "first-order" if it does NOT contain function types.
    First-order types have the critical property that their value relation
    is PREDICATE-INDEPENDENT — it doesn't matter what predicates we use
    for the recursive calls, the result is the same.

    This is THE KEY to proving step-up for first-order types.
*)

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  (* Primitive types: always first-order *)
  | TUnit => true
  | TBool => true
  | TInt => true
  | TString => true
  | TBytes => true

  (* Function types: NEVER first-order *)
  | TFn _ _ _ => false

  (* Compound types: first-order iff components are *)
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2

  (* Wrapper types: first-order iff inner type is *)
  | TList T => first_order_type T
  | TOption T => first_order_type T
  | TRef T _ => first_order_type T
  | TSecret T => first_order_type T
  | TLabeled T _ => first_order_type T
  end.

(** CRITICAL PROPERTY: For compound types, first_order_type decomposes *)
Lemma first_order_type_prod : forall T1 T2,
  first_order_type (TProd T1 T2) = true <->
  first_order_type T1 = true /\ first_order_type T2 = true.
Proof.
  intros T1 T2.
  simpl. rewrite Bool.andb_true_iff. reflexivity.
Qed.

Lemma first_order_type_sum : forall T1 T2,
  first_order_type (TSum T1 T2) = true <->
  first_order_type T1 = true /\ first_order_type T2 = true.
Proof.
  intros T1 T2.
  simpl. rewrite Bool.andb_true_iff. reflexivity.
Qed.
```

---

## SECTION 4: CLOSED EXPRESSIONS AND STORE DEFINITIONS

```coq
(** ========================================================================
    FREE VARIABLES AND CLOSED EXPRESSIONS
    ======================================================================== *)

Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EVar y => x = y
  | ELam y T body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  | EPair e1 e2 => free_in x e1 \/ free_in x e2
  | EFst e => free_in x e
  | ESnd e => free_in x e
  | EInl e _ => free_in x e
  | EInr e _ => free_in x e
  | ECase e y1 e1 y2 e2 =>
      free_in x e \/ (x <> y1 /\ free_in x e1) \/ (x <> y2 /\ free_in x e2)
  | EIf e1 e2 e3 => free_in x e1 \/ free_in x e2 \/ free_in x e3
  | ELet y e1 e2 => free_in x e1 \/ (x <> y /\ free_in x e2)
  | ERef e _ => free_in x e
  | EDeref e => free_in x e
  | EAssign e1 e2 => free_in x e1 \/ free_in x e2
  | _ => False
  end.

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

(** ========================================================================
    STORE DEFINITIONS
    ======================================================================== *)

Definition store := list (loc * expr).
Definition store_ty := list (loc * ty * security_level).
Definition effect_ctx := list effect.

Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * security_level) :=
  match Σ with
  | nil => None
  | (l', T, sl) :: Σ' => if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l Σ'
  end.

Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

(** Store typing extension (Kripke world ordering) *)
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).
```

---

## SECTION 5: FIRST-ORDER VALUE RELATION (val_rel_at_type_fo)

```coq
(** ========================================================================
    FIRST-ORDER VALUE RELATION
    ========================================================================

    This is the PREDICATE-INDEPENDENT value relation for first-order types.
    It does NOT take any predicate parameters — the structure is determined
    purely by the type T and the values v1, v2.

    THIS IS THE KEY: For first-order types, val_rel_at_type (with ANY predicates)
    is EQUIVALENT to val_rel_at_type_fo.
*)

Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  (* Primitive types: exact equality *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2

  (* Security types: indistinguishable (always related) *)
  | TSecret _ => True
  | TLabeled _ _ => True

  (* Reference types: same location *)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l

  (* Collection types: simplified (not structural) *)
  | TList _ => True
  | TOption _ => True

  (* Product types: component-wise recursion *)
  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2

  (* Sum types: matching constructor with recursion *)
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2)
      \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)

  (* Function types: always True (deferred to step-indexed) *)
  | TFn _ _ _ => True
  end.
```

---

## SECTION 6: PARAMETERIZED VALUE RELATION (val_rel_at_type)

```coq
(** ========================================================================
    PARAMETERIZED VALUE RELATION
    ========================================================================

    This is the FULL value relation that takes predicate parameters.
    For first-order types, it MUST be equivalent to val_rel_at_type_fo.
    For function types (TFn), it uses the predicates for the Kripke property.
*)

Section ValRelAtType.
  Variable Σ : store_ty.
  Variable store_pred : store_ty -> store -> store -> Prop.
  Variable val_pred : store_ty -> ty -> expr -> expr -> Prop.
  Variable store_lower : store_ty -> store -> store -> Prop.

  Fixpoint val_rel_at_type (T : ty) (v1 v2 : expr) {struct T} : Prop :=
    match T with
    (* Primitive types: exact equality — SAME AS val_rel_at_type_fo *)
    | TUnit => v1 = EUnit /\ v2 = EUnit
    | TBool => exists b, v1 = EBool b /\ v2 = EBool b
    | TInt => exists i, v1 = EInt i /\ v2 = EInt i
    | TString => exists s, v1 = EString s /\ v2 = EString s
    | TBytes => v1 = v2

    (* Security types: indistinguishable — SAME AS val_rel_at_type_fo *)
    | TSecret _ => True
    | TLabeled _ _ => True

    (* Reference types: same location — SAME AS val_rel_at_type_fo *)
    | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l

    (* Collection types: simplified — SAME AS val_rel_at_type_fo *)
    | TList _ => True
    | TOption _ => True

    (* Product types: recursive — uses val_rel_at_type (but equivalent for FO) *)
    | TProd T1 T2 =>
        exists x1 y1 x2 y2,
          v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
          val_rel_at_type T1 x1 x2 /\ val_rel_at_type T2 y1 y2

    (* Sum types: recursive — uses val_rel_at_type (but equivalent for FO) *)
    | TSum T1 T2 =>
        (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                       val_rel_at_type T1 x1 x2)
        \/
        (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                       val_rel_at_type T2 y1 y2)

    (* Function types: THE KRIPKE PROPERTY — uses predicates *)
    | TFn T1 T2 eff =>
        forall Σ', store_ty_extends Σ Σ' ->
          forall x y,
            value x -> value y -> closed_expr x -> closed_expr y ->
            val_pred Σ' T1 x y ->
            forall st1 st2 ctx,
              store_pred Σ' st1 st2 ->
              exists v1' v2' st1' st2' ctx' Σ'',
                store_ty_extends Σ' Σ'' /\
                multi_step (EApp v1 x, st1, ctx) (v1', st1', ctx') /\
                multi_step (EApp v2 y, st2, ctx) (v2', st2', ctx') /\
                val_pred Σ'' T2 v1' v2' /\
                store_lower Σ'' st1' st2'
    end.
End ValRelAtType.

(** Notation for applying val_rel_at_type with specific predicates *)
Notation val_rel_at_type_with Σ sp vp sl T v1 v2 :=
  (val_rel_at_type Σ sp vp sl T v1 v2).
```

---

## SECTION 7: OPERATIONAL SEMANTICS (for multi_step)

```coq
(** ========================================================================
    SMALL-STEP OPERATIONAL SEMANTICS
    ======================================================================== *)

Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar y => if String.eqb x y then v else EVar y
  | ELam y T body =>
      if String.eqb x y then ELam y T body else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e => EFst (subst x v e)
  | ESnd e => ESnd (subst x v e)
  | EInl e T => EInl (subst x v e) T
  | EInr e T => EInr (subst x v e) T
  | ECase e y1 e1 y2 e2 =>
      ECase (subst x v e)
        y1 (if String.eqb x y1 then e1 else subst x v e1)
        y2 (if String.eqb x y2 then e2 else subst x v e2)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ELet y e1 e2 =>
      ELet y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | ERef e sl => ERef (subst x v e) sl
  | EDeref e => EDeref (subst x v e)
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  end.

Reserved Notation "cfg1 '-->' cfg2" (at level 40).

Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> (subst x v body, st, ctx)
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)
  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> (subst x1 v e1, st, ctx)
  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> (subst x2 v e2, st, ctx)
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> (subst x v e2, st, ctx)
where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

Inductive multi_step : (expr * store * effect_ctx) ->
                       (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).
```

---

## SECTION 8: STEP-INDEXED RELATIONS (val_rel_n and store_rel_n)

```coq
(** ========================================================================
    STEP-INDEXED VALUE AND STORE RELATIONS
    ========================================================================

    These are the CORE definitions. Note the REVOLUTIONARY change:

    At n = 0: We include val_rel_at_type_fo for first-order types!
    This gives us structural information even at step 0.

    At n = S n': We include the cumulative part (val_rel_n n') PLUS
    the structural part (val_rel_at_type with predicates at level n').
*)

Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 =>
      (* BASE CASE: value, closed, and FO structure *)
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)
  | S n' =>
      (* STEP CASE: cumulative PLUS structural at level n' *)
      val_rel_n n' Σ T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end

with store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 =>
      (* BASE CASE: just store_max equality *)
      store_max st1 = store_max st2
  | S n' =>
      (* STEP CASE: cumulative PLUS location contents *)
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' Σ T v1 v2)
  end.
```

---

## SECTION 9: THE KEY EQUIVALENCE THEOREM

```coq
(** ========================================================================
    THE KEY THEOREM: val_rel_at_type_fo_equiv
    ========================================================================

    For FIRST-ORDER types, val_rel_at_type (with ANY predicates) is
    EQUIVALENT to val_rel_at_type_fo (which has NO predicates).

    This is THE FOUNDATION of the step-up lemma for FO types.

    WHY IT WORKS:
    - For primitive types (TUnit, TBool, TInt, etc.): both definitions
      are identical — they don't use predicates at all.
    - For compound types (TProd, TSum): they recurse on components,
      but since components are also first-order (by premise), the
      IH applies.
    - For TFn: first_order_type (TFn _ _ _) = false, so this case
      is excluded by the premise.
*)

Theorem val_rel_at_type_fo_equiv : forall T Σ sp vp sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vp sl T v1 v2 <-> val_rel_at_type_fo T v1 v2.
Proof.
  intros T.
  induction T; intros Σ' sp vp sl v1 v2 Hfo; simpl in Hfo; try discriminate.

  (* TUnit *)
  - simpl. split; auto.

  (* TBool *)
  - simpl. split; auto.

  (* TInt *)
  - simpl. split; auto.

  (* TString *)
  - simpl. split; auto.

  (* TBytes *)
  - simpl. split; auto.

  (* TProd T1 T2 *)
  - apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + (* val_rel_at_type -> val_rel_at_type_fo *)
      intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2. repeat split; try assumption.
      * apply IHT1; assumption.
      * apply IHT2; assumption.
    + (* val_rel_at_type_fo -> val_rel_at_type *)
      intros [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hr1 Hr2]]]]]]].
      exists x1, y1, x2, y2. repeat split; try assumption.
      * apply IHT1; assumption.
      * apply IHT2; assumption.

  (* TSum T1 T2 *)
  - apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl. split.
    + (* val_rel_at_type -> val_rel_at_type_fo *)
      intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply IHT1; assumption.
      * right. exists y1, y2. repeat split; try assumption.
        apply IHT2; assumption.
    + (* val_rel_at_type_fo -> val_rel_at_type *)
      intros [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply IHT1; assumption.
      * right. exists y1, y2. repeat split; try assumption.
        apply IHT2; assumption.

  (* TList T *)
  - simpl. split; auto.

  (* TOption T *)
  - simpl. split; auto.

  (* TRef T sl *)
  - simpl. split; auto.

  (* TSecret T *)
  - simpl. split; auto.

  (* TLabeled T l *)
  - simpl. split; auto.
Qed.
```

---

## SECTION 10: THE MAIN THEOREM — val_rel_n_step_up_fo

```coq
(** ========================================================================
    THE MAIN THEOREM: val_rel_n_step_up_fo
    ========================================================================

    For FIRST-ORDER types, if values are related at step n, they are
    related at step S n.

    PROOF STRATEGY:
    1. Unfold val_rel_n (S n) — need to show cumulative part PLUS structural
    2. Cumulative part: exactly the premise val_rel_n n
    3. value/closed: extract from val_rel_n n (any level)
    4. Structural part: use val_rel_at_type_fo_equiv
       - val_rel_at_type at level n uses predicates at level n-1
       - val_rel_at_type_fo doesn't use predicates at all
       - They're equivalent for FO types!
       - Extract val_rel_at_type_fo from val_rel_n n, convert to val_rel_at_type
*)

Theorem val_rel_n_step_up_fo : forall n Σ T v1 v2,
  first_order_type T = true ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hfo Hrel.

  (* Unfold val_rel_n (S n) *)
  simpl.

  split.
  (* Part 1: val_rel_n n Σ T v1 v2 — this is exactly the premise *)
  - exact Hrel.

  - (* Part 2: value, closed, and val_rel_at_type *)
    (* We need to extract these from Hrel *)
    destruct n as [| n'].

    + (* n = 0 *)
      (* Hrel : value v1 /\ value v2 /\ closed v1 /\ closed v2 /\
                (if FO then val_rel_at_type_fo else True) *)
      simpl in Hrel.
      destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hrat_fo]]]].

      repeat split; try assumption.

      (* Need: val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2 *)
      (* Since T is FO, this is equivalent to val_rel_at_type_fo T v1 v2 *)
      (* We have Hrat_fo from the premise (under the FO conditional) *)

      rewrite Hfo in Hrat_fo.
      (* Now Hrat_fo : val_rel_at_type_fo T v1 v2 *)

      (* Convert to val_rel_at_type using the equivalence *)
      apply val_rel_at_type_fo_equiv; assumption.

    + (* n = S n' *)
      (* Hrel : val_rel_n n' Σ T v1 v2 /\ value v1 /\ value v2 /\
                closed v1 /\ closed v2 /\ val_rel_at_type ... T v1 v2 *)
      simpl in Hrel.
      destruct Hrel as [Hrec [Hv1 [Hv2 [Hc1 [Hc2 Hrat]]]]].

      repeat split; try assumption.

      (* Need: val_rel_at_type Σ (store_rel_n (S n')) (val_rel_n (S n'))
                               (store_rel_n (S n')) T v1 v2 *)
      (* Hrat : val_rel_at_type Σ (store_rel_n n') (val_rel_n n')
                                (store_rel_n n') T v1 v2 *)
      (* Since T is FO, both are equivalent to val_rel_at_type_fo T v1 v2 *)

      (* Convert Hrat to val_rel_at_type_fo *)
      apply val_rel_at_type_fo_equiv in Hrat; [| assumption].

      (* Convert back to val_rel_at_type with new predicates *)
      apply val_rel_at_type_fo_equiv; assumption.
Qed.
```

---

## SECTION 11: VERIFICATION

```coq
(** ========================================================================
    VERIFICATION
    ======================================================================== *)

(* Check that the theorem is proven *)
Check val_rel_n_step_up_fo.

(* Print assumptions to verify ZERO AXIOMS *)
Print Assumptions val_rel_n_step_up_fo.

(** Expected output:
    Closed under the global context

    This confirms ZERO AXIOMS used — pure constructive proof.
*)
```

---

## SECTION 12: OUTPUT FORMAT

You MUST output a COMPLETE, SELF-CONTAINED Coq file that:

1. Includes ALL type definitions from Sections 2-4
2. Includes val_rel_at_type_fo from Section 5
3. Includes val_rel_at_type from Section 6
4. Includes operational semantics from Section 7
5. Includes val_rel_n and store_rel_n from Section 8
6. Includes val_rel_at_type_fo_equiv from Section 9
7. Includes val_rel_n_step_up_fo from Section 10
8. Includes verification from Section 11
9. Every `Proof.` has a matching `Qed.` (NO `Admitted.`)
10. Compiles with `coqc` and passes `coqchk`

---

## SECTION 13: VERIFICATION CHECKLIST

Before submitting, verify EVERY item:

- [ ] `first_order_type_prod` is proven
- [ ] `first_order_type_sum` is proven
- [ ] `val_rel_at_type_fo_equiv` is proven for ALL first-order type cases
- [ ] `val_rel_at_type_fo_equiv` uses `Bool.andb_true_iff` for TProd/TSum
- [ ] `val_rel_n_step_up_fo` handles n=0 and n=S n' cases separately
- [ ] The proof correctly extracts value/closed from val_rel_n
- [ ] The proof uses val_rel_at_type_fo_equiv in BOTH directions
- [ ] All bullets are properly nested (`-`, `+`, `*`)
- [ ] `Print Assumptions` shows "Closed under the global context"

---

## SECTION 14: CRITICAL REMINDERS

1. **EXTREME RIGOUR**: Every step must be justified. No handwaving.
2. **NO `admit` OR `Admitted`**: Every proof must be 100% complete.
3. **TEST COMPILATION**: The file must compile with `coqc`.
4. **VERIFY WITH `coqchk`**: Must show "Modules were successfully checked".
5. **ZERO AXIOMS**: `Print Assumptions` must show "Closed under the global context".
6. **CASE ANALYSIS**: Handle n=0 and n=S n' separately in val_rel_n_step_up_fo.
7. **USE THE EQUIVALENCE**: The key is using val_rel_at_type_fo_equiv to convert between the predicate-dependent and predicate-independent relations.

---

## SECTION 15: WHY THIS MATTERS

The step-up lemma is CRITICAL for the fundamental theorem of logical relations:

1. **Induction on typing derivation** needs to go UP in step index
2. **Function application** consumes a step, then we need step-up for the body
3. **Store operations** may extend the store typing, requiring Kripke monotonicity

For **first-order types**, step-up is PURE — no typing premises needed.
For **higher-order types** (TFn), step-up needs typing + strong normalization.

By proving the FO case, we handle ALL security-critical data types:
- **TBool**: Conditionals (if-then-else)
- **TSum**: Pattern matching (case)
- **TProd**: Pairs
- **TRef**: References
- **TInt, TString**: Data

The TFn case is only needed for higher-order programs with function values.

---

**END OF PROMPT — NOW EXECUTE WITH ULTRA KIASU EXTREME RIGOUR**

**This proof establishes the INDUCTIVE FOUNDATION of RIINA's security guarantees.**

**Failure is NOT an option. Verify EVERYTHING.**
