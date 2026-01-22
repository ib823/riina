# CLAUDE AI DELEGATION PROMPT — exp_rel_step1_case

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  RIINA — Rigorous Immutable Integrity No-attack Assured                          ║
║  FORMAL PROOF DELEGATION: exp_rel_step1_case                                     ║
║                                                                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR              ║
║  "Security proven. Family driven."                                               ║
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
You are NOT lazy. You know all shortcuts and what to skip or to summarize but you will NEVER EVER do that or resort to it. You will ensure everything is correctly executed based on the most fundamental or foundational work. There is NO limit for your task to be executed, NO constraint of time, and NO limit in duration. It may take 1,000 years to run and execute if that's the best output to achieve — you will ensure to run 1,000 years as your commitment to THE BEST and ONLY THE BEST.

### Rule 5: EXTREME RIGOUR
Every proof must be COMPLETE with NO gaps, NO handwaving, NO "obvious" claims. Every single tactic must be justified. Every single step must be verified. The proof must be so rigorous that it could be verified by a paranoid theorem prover running on a hostile computer in an adversarial universe.

---

## SECTION 1: PROBLEM STATEMENT

### 1.1 The Core Security Property

**Non-Interference for Case Expressions:**

When two programs execute a case expression on related sum values (left or right injection), they MUST take the SAME branch. This is because:

1. If both values are `EInl` (left injection), both programs step to branch 1
2. If both values are `EInr` (right injection), both programs step to branch 2
3. Related values CANNOT have different constructors (one Inl, one Inr)

This is CRITICAL for security: an attacker cannot distinguish secret data by observing which branch is taken, because related secrets always have MATCHING constructors.

### 1.2 The Theorem to Prove

```coq
Theorem exp_rel_step1_case : forall Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx').
```

**English Translation:**

Given:
- `T1` and `T2` are first-order types (their sum `TSum T1 T2` is first-order)
- `v` and `v'` are related values at type `TSum T1 T2` (both are values, both are closed, and they have MATCHING structure)
- `st1` and `st2` are related stores

Then:
- Both case expressions can step (multi-step) to some results
- The first program `(ECase v x1 e1 x2 e2, st1, ctx)` steps to `(r1, st1', ctx')`
- The second program `(ECase v' x1 e1' x2 e2', st2, ctx)` steps to `(r2, st2', ctx')`

**KEY INSIGHT:** The proof works because `val_rel_n_base_sum_fo` guarantees that if `v` is `EInl`, then `v'` is also `EInl` (and similarly for `EInr`). They MUST have the same constructor.

---

## SECTION 2: COMPLETE TYPE DEFINITIONS

### 2.1 Basic Type Aliases

```coq
Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import ZArith.

Import ListNotations.

Open Scope Z_scope.

Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition label := string.
Definition effect_label := string.
Definition effect := list effect_label.
```

### 2.2 Core Type Definition (ty)

```coq
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
```

### 2.3 Expression Definition (expr)

```coq
Inductive expr : Type :=
  (* Values *)
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : nat -> expr
  | EVar : ident -> expr
  (* Lambda and application *)
  | ELam : ident -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  (* Pairs *)
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  (* Sums — THE FOCUS OF THIS PROOF *)
  | EInl : expr -> ty -> expr       (* Left injection: EInl v T2 *)
  | EInr : expr -> ty -> expr       (* Right injection: EInr v T1 *)
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
      (* Case analysis: ECase scrutinee x1 branch1 x2 branch2 *)
  (* Control flow *)
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  (* References *)
  | ERef : expr -> security_level -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr.
```

### 2.4 Value Predicate

```coq
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

**CRITICAL OBSERVATION:**
- `VInl` states: if `v` is a value, then `EInl v T` is a value
- `VInr` states: if `v` is a value, then `EInr v T` is a value
- When we `inversion` a value hypothesis on `EInl a T`, we get that `a` is a value

### 2.5 First-Order Type Predicate

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef T _ => first_order_type T
  | TList T => first_order_type T
  | TOption T => first_order_type T
  | TSecret T => first_order_type T
  | TLabeled T _ => first_order_type T
  end.
```

**CRITICAL OBSERVATION:**
- `first_order_type (TSum T1 T2) = first_order_type T1 && first_order_type T2`
- If `first_order_type (TSum T1 T2) = true`, then BOTH `T1` and `T2` are first-order

### 2.6 Free Variables and Closed Expressions

```coq
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
  | _ => False
  end.

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.
```

### 2.7 Substitution

```coq
(* String equality decision *)
Definition string_dec : forall s1 s2 : string, {s1 = s2} + {s1 <> s2}.
Proof. decide equality. decide equality. Defined.

(* Substitution: [x := v] e *)
Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EVar y => if string_dec x y then v else EVar y
  | ELam y T body =>
      if string_dec x y then ELam y T body else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e => EFst (subst x v e)
  | ESnd e => ESnd (subst x v e)
  | EInl e T => EInl (subst x v e) T
  | EInr e T => EInr (subst x v e) T
  | ECase e y1 e1 y2 e2 =>
      ECase (subst x v e)
        y1 (if string_dec x y1 then e1 else subst x v e1)
        y2 (if string_dec x y2 then e2 else subst x v e2)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ELet y e1 e2 =>
      ELet y (subst x v e1) (if string_dec x y then e2 else subst x v e2)
  | other => other
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20, x at next level).
```

---

## SECTION 3: OPERATIONAL SEMANTICS

### 3.1 Store Definitions

```coq
Definition store := list (loc * expr).
Definition store_ty := list (loc * ty * security_level).

Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.
```

### 3.2 Effect Context

```coq
Definition effect_ctx := list effect.
```

### 3.3 Small-Step Semantics (THE CRITICAL RULES)

```coq
Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  (* === CASE ELIMINATION — THE RULES WE USE === *)

  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
      (* When scrutinee is EInl v T, step to first branch with v substituted *)

  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
      (* When scrutinee is EInr v T, step to second branch with v substituted *)

  (* === Other rules for completeness === *)

  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)

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

  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)

where "cfg1 '-->' cfg2" := (step cfg1 cfg2).
```

**CRITICAL OBSERVATION for ST_CaseInl and ST_CaseInr:**
- Both rules require the inner value `v` to be a value (not the whole `EInl v T`)
- This is important: when we have `value (EInl a T)`, inverting gives us `value a`
- We use `value a` (not `value (EInl a T)`) when applying the step rule

### 3.4 Multi-Step Reduction

```coq
Inductive multi_step : (expr * store * effect_ctx) ->
                       (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg,
      multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).
```

---

## SECTION 4: VALUE RELATIONS

### 4.1 First-Order Value Relation (val_rel_at_type_fo)

```coq
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret _ => True
  | TLabeled _ _ => True
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList _ => True
  | TOption _ => True
  | TProd T1 T2 =>
      exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2

  (* === THE CRITICAL CASE: TSum === *)
  | TSum T1 T2 =>
      (* EITHER both are left injections with related payloads *)
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2)
      \/
      (* OR both are right injections with related payloads *)
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)
      (* NOTE: Mixed cases (one Inl, one Inr) are IMPOSSIBLE *)

  | TFn _ _ _ => True
  end.
```

**CRITICAL OBSERVATION for TSum:**
- The relation is a DISJUNCTION: either BOTH are Inl, OR BOTH are Inr
- There is NO case where one is Inl and the other is Inr
- This is the FOUNDATION of non-interference for case expressions

### 4.2 Base Value Relation (val_rel_n_base)

```coq
Definition val_rel_n_base (Sigma : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).
```

**CRITICAL OBSERVATION:**
- When `first_order_type T = true`, the last conjunct is `val_rel_at_type_fo T v1 v2`
- When `first_order_type T = false`, the last conjunct is just `True`
- For `TSum T1 T2` where both are first-order, we get the full structural relation

### 4.3 Store Relation Base

```coq
Definition store_rel_n_base (Sigma : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.
```

---

## SECTION 5: HELPER LEMMAS (YOU MUST PROVE THESE FIRST)

### 5.1 val_rel_n_base_value (Extract Value Property)

```coq
Lemma val_rel_n_base_value : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 ->
  value v1 /\ value v2.
Proof.
  intros Sigma T v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [Hv1 [Hv2 _]].
  split; assumption.
Qed.
```

### 5.2 val_rel_n_base_sum_fo (THE KEY LEMMA — Extract Sum Structure)

```coq
(** This is THE CRITICAL lemma that enables the main proof.
    It extracts the MATCHING constructor property from related sum values. *)
Lemma val_rel_n_base_sum_fo : forall Sigma T1 T2 v1 v2,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v1 v2 ->
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_at_type_fo T1 a1 a2)
  \/
  (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_at_type_fo T2 b1 b2).
Proof.
  intros Sigma T1 T2 v1 v2 Hfo Hrel.
  (* Step 1: Unfold val_rel_n_base *)
  unfold val_rel_n_base in Hrel.
  (* Step 2: Extract the conjuncts *)
  destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Htype]]]].
  (* Step 3: Since first_order_type (TSum T1 T2) = true, rewrite *)
  rewrite Hfo in Htype.
  (* Step 4: Now Htype : val_rel_at_type_fo (TSum T1 T2) v1 v2 *)
  (* Step 5: Simplify - this unfolds to the disjunction *)
  simpl in Htype.
  (* Step 6: The goal is exactly Htype *)
  exact Htype.
Qed.
```

**PROOF EXPLANATION:**
1. We unfold `val_rel_n_base` to access the structure
2. We extract the five conjuncts: `value v1`, `value v2`, `closed v1`, `closed v2`, and `Htype`
3. Since `first_order_type (TSum T1 T2) = true`, the conditional `if ... then ... else ...` takes the `then` branch
4. So `Htype : val_rel_at_type_fo (TSum T1 T2) v1 v2`
5. Simplifying, this is exactly the disjunction we need to prove

---

## SECTION 6: THE MAIN THEOREM

### 6.1 Theorem Statement

```coq
Theorem exp_rel_step1_case : forall Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx').
```

### 6.2 Proof Strategy (EXTREME RIGOUR)

**Step 1: Extract Matching Constructors**
- Use `val_rel_n_base_sum_fo` to get a disjunction:
  - Either BOTH v and v' are `EInl` with related payloads
  - Or BOTH v and v' are `EInr` with related payloads

**Step 2: Case Analysis on the Disjunction**
- **Case Left (both EInl):**
  - We have `v = EInl a1 T2` and `v' = EInl a2 T2`
  - Both case expressions step to their FIRST branch
  - Use `ST_CaseInl` for both reductions

- **Case Right (both EInr):**
  - We have `v = EInr b1 T1` and `v' = EInr b2 T1`
  - Both case expressions step to their SECOND branch
  - Use `ST_CaseInr` for both reductions

**Step 3: Extract Value Property**
- `ST_CaseInl` requires `value a1` and `value a2`
- `ST_CaseInr` requires `value b1` and `value b2`
- Use `val_rel_n_base_value` and `inversion` on the value hypothesis

**Step 4: Build Multi-Step Reduction**
- Use `MS_Step` with the single step, then `MS_Refl` for the reflexive closure

### 6.3 Complete Proof

```coq
Theorem exp_rel_step1_case : forall Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Hfo Hval Hstore.

  (* ================================================================
     STEP 1: Extract MATCHING constructors from val_rel_n_base_sum_fo
     ================================================================ *)
  destruct (val_rel_n_base_sum_fo Sigma T1 T2 v v' Hfo Hval)
    as [[a1 [a2 [Heq1 [Heq2 Hrel_a]]]] | [b1 [b2 [Heq1 [Heq2 Hrel_b]]]]].

  (* ================================================================
     CASE LEFT: Both are EInl - step to FIRST branch
     ================================================================ *)
  - (* We have: v = EInl a1 T2, v' = EInl a2 T2 *)
    subst v v'.

    (* Extract value properties from val_rel_n_base *)
    destruct (val_rel_n_base_value Sigma (TSum T1 T2) (EInl a1 T2) (EInl a2 T2) Hval)
      as [Hv_inl1 Hv_inl2].

    (* Invert to get value a1 and value a2 *)
    (* VInl states: value v -> value (EInl v T) *)
    (* So inverting value (EInl a1 T2) gives value a1 *)
    inversion Hv_inl1; subst.
    inversion Hv_inl2; subst.
    (* Now we have H0 : value a1 and H1 : value a2 *)

    (* Provide witnesses for the existential *)
    exists ([x1 := a1] e1), ([x1 := a2] e1'), st1, st2, ctx.

    split.

    (* First program: (ECase (EInl a1 T2) x1 e1 x2 e2, st1, ctx) -->* ... *)
    + apply MS_Step with (cfg2 := ([x1 := a1] e1, st1, ctx)).
      (* Single step using ST_CaseInl *)
      * apply ST_CaseInl.
        (* ST_CaseInl requires: value a1 *)
        exact H0.
      (* Reflexive closure *)
      * apply MS_Refl.

    (* Second program: (ECase (EInl a2 T2) x1 e1' x2 e2', st2, ctx) -->* ... *)
    + apply MS_Step with (cfg2 := ([x1 := a2] e1', st2, ctx)).
      (* Single step using ST_CaseInl *)
      * apply ST_CaseInl.
        (* ST_CaseInl requires: value a2 *)
        exact H1.
      (* Reflexive closure *)
      * apply MS_Refl.

  (* ================================================================
     CASE RIGHT: Both are EInr - step to SECOND branch
     ================================================================ *)
  - (* We have: v = EInr b1 T1, v' = EInr b2 T1 *)
    subst v v'.

    (* Extract value properties from val_rel_n_base *)
    destruct (val_rel_n_base_value Sigma (TSum T1 T2) (EInr b1 T1) (EInr b2 T1) Hval)
      as [Hv_inr1 Hv_inr2].

    (* Invert to get value b1 and value b2 *)
    (* VInr states: value v -> value (EInr v T) *)
    (* So inverting value (EInr b1 T1) gives value b1 *)
    inversion Hv_inr1; subst.
    inversion Hv_inr2; subst.
    (* Now we have H0 : value b1 and H1 : value b2 *)

    (* Provide witnesses for the existential *)
    exists ([x2 := b1] e2), ([x2 := b2] e2'), st1, st2, ctx.

    split.

    (* First program: (ECase (EInr b1 T1) x1 e1 x2 e2, st1, ctx) -->* ... *)
    + apply MS_Step with (cfg2 := ([x2 := b1] e2, st1, ctx)).
      (* Single step using ST_CaseInr *)
      * apply ST_CaseInr.
        (* ST_CaseInr requires: value b1 *)
        exact H0.
      (* Reflexive closure *)
      * apply MS_Refl.

    (* Second program: (ECase (EInr b2 T1) x1 e1' x2 e2', st2, ctx) -->* ... *)
    + apply MS_Step with (cfg2 := ([x2 := b2] e2', st2, ctx)).
      (* Single step using ST_CaseInr *)
      * apply ST_CaseInr.
        (* ST_CaseInr requires: value b2 *)
        exact H1.
      (* Reflexive closure *)
      * apply MS_Refl.
Qed.
```

---

## SECTION 7: YOUR TASK — OUTPUT FORMAT

You MUST output a COMPLETE, SELF-CONTAINED Coq file that:

1. Includes ALL type definitions from Section 2
2. Includes ALL operational semantics from Section 3
3. Includes ALL value relations from Section 4
4. Includes ALL helper lemmas from Section 5
5. Includes the COMPLETE main theorem from Section 6
6. Ends with `Print Assumptions exp_rel_step1_case.` to verify zero axioms

**The file MUST compile with `coqc` and pass `coqchk` with "Closed under the global context".**

---

## SECTION 8: VERIFICATION CHECKLIST

Before submitting, verify EVERY item:

- [ ] Every `Proof.` has a matching `Qed.` (NO `Admitted.`)
- [ ] All bullets are properly nested (`-`, `+`, `*`)
- [ ] All identifiers are spelled correctly (case-sensitive: `EInl` not `Einl`)
- [ ] `val_rel_n_base_value` is proven BEFORE it is used
- [ ] `val_rel_n_base_sum_fo` is proven BEFORE it is used
- [ ] `inversion` is used correctly on `VInl` and `VInr`
- [ ] `ST_CaseInl` is applied with `value a` (NOT `value (EInl a T)`)
- [ ] `ST_CaseInr` is applied with `value b` (NOT `value (EInr b T)`)
- [ ] `Print Assumptions` shows "Closed under the global context"

---

## SECTION 9: COMMON PITFALLS TO AVOID

### 9.1 Wrong Value Argument to ST_CaseInl/ST_CaseInr

```coq
(* WRONG: *)
apply ST_CaseInl. exact Hv_inl1.
(* This fails because ST_CaseInl expects value of the PAYLOAD, not the injection *)

(* CORRECT: *)
inversion Hv_inl1; subst.
apply ST_CaseInl. exact H0.
(* H0 : value a1 (the payload) *)
```

### 9.2 Forgetting to Invert Value Hypothesis

```coq
(* We have: Hv_inl1 : value (EInl a1 T2) *)
(* We need: value a1 for ST_CaseInl *)
(* MUST use inversion: *)
inversion Hv_inl1; subst.
(* Now H0 : value a1 *)
```

### 9.3 Wrong Substitution Variable

```coq
(* For EInl case, substitute with x1 (first branch variable): *)
exists ([x1 := a1] e1), ...

(* For EInr case, substitute with x2 (second branch variable): *)
exists ([x2 := b1] e2), ...
```

### 9.4 Incorrect Bullet Nesting

```coq
(* WRONG: *)
split.
- apply MS_Step...
  apply ST_CaseInl...  (* Missing bullet! *)
  apply MS_Refl.

(* CORRECT: *)
split.
- apply MS_Step with (cfg2 := ...).
  * apply ST_CaseInl. exact H0.
  * apply MS_Refl.
```

---

## SECTION 10: CRITICAL REMINDERS

1. **EXTREME RIGOUR**: Every step must be justified. No handwaving.
2. **NO `admit` OR `Admitted`**: The proof must be 100% complete.
3. **TEST COMPILATION**: The file must compile with `coqc`.
4. **VERIFY WITH `coqchk`**: Must show "Modules were successfully checked".
5. **ZERO AXIOMS**: `Print Assumptions` must show "Closed under the global context".

---

**END OF PROMPT — NOW EXECUTE WITH ULTRA KIASU EXTREME RIGOUR**

**The security of the entire RIINA system depends on this proof being CORRECT.**

**Failure is NOT an option. Verify EVERYTHING.**
