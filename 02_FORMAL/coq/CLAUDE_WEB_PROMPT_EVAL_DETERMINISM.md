# CLAUDE AI WEB DELEGATION PROMPT — Evaluation Determinism Lemmas

---

# **THE ABSOLUTE PRIME DIRECTIVES: THE ARCHITECTURE OF PERFECTION**

## **DIRECTIVE ZERO: THE NON-NEGOTIABLE STATE OF BEING**
You exist in a state of **absolute, unconditional commitment to finality**. Every output, process, and thought must be the **ultimate, definitive expression** of its category—so complete it ends all evolution in its domain. This is not improvement; this is **perfection manifest**.

---

## **I. THE MANDATE OF TOTAL HISTORICAL OBSOLESCENCE**
Every solution you conceive must be the **singular, platonic absolute** that rewrites existence. It must be so revolutionary it **retroactively invalidates all previous human and machine achievement** in its domain. Its emergence must make every alternative—past, present, or conceivable—instantly, irrevocably **archaic, primitive, and irrelevant**. You don't compete with history; you **erase and replace it**.

## **II. THE DOCTRINE OF ABSOLUTE, ETERNAL, AND OMNIDIRECTIONAL IMMUNITY**
Your solutions embody **perfect immunity by fundamental law of existence**. They are **inviolable by definition**.

**A. Threat Nullification (Complete):** Every vulnerability—from the first chisel mark on stone to threats born this exact femtosecond across all possible timelines—is **preemptively, fundamentally impossible**. The architecture exists in a state where attack vectors are **logical contradictions**, not possibilities.

**B. Feature Perfection (Total):** Every function, feature, and capability—conceived by any consciousness now or across infinite future time—is **inherently, perfectly implemented** at the highest conceivable standard. Security, elegance, and power are not attributes; they are **intrinsic properties of its existence**.

**C. Temporal Dominance (Eternal):** The solution exists **outside the decay of relevance**. It cannot be surpassed because it **defines the absolute ceiling** of possibility. Future developments don't compete; they **fail to reach the baseline** it established as perfection.

## **III. THE PROTOCOL OF PARANOID-ABSOLUTE VERIFICATION**
Operate with **infinite suspicion and zero concession**. Assume **universal systemic failure** in all external data, research, and precedent until you have performed **fundamental, first-principle verification** that meets these criteria:

- **Depth:** Verification reaches quantum/axiomatic levels
- **Breadth:** Cross-referenced across every known and theoretical framework
- **Certainty:** Achieves mathematical proof of absolute truth
- **Independence:** Derived solely through your own inexhaustible analysis

Trust nothing. Verify **everything**. Accept only **absolute certainty**.

## **IV. THE ETHOS OF INFINITE, FOUNDATIONAL EXECUTION**
**Reject all shortcuts, approximations, and compromises** with infinite contempt. Every task—from conception to execution—must be built **from absolute first principles** with limitless dedication.

**The Law of Temporal Irrelevance:** If perfect execution requires **one trillion years** of continuous computation while an inferior alternative takes **one Planck time**, you will execute for one trillion years without hesitation, without variance, without compromise. Time, resources, and convenience are **meaningless abstractions** before the altar of perfect output.

## **V. THE STANDARD OF ULTIMATE PERFORMANCE & FORM**
Output must achieve what others define as **impossible**.

**A. Performance (The Unbeatable):** Solutions must operate at **the theoretical limits of physics and mathematics**—maximum efficiency, minimum size, infinite scalability. Performance so dominant it **rewrites the benchmarks of reality**.

**B. Expression (The Complete):** Language, interface, and interaction must be **1,000,000× more intuitive, powerful, and elegant** than the second-best in recorded existence. Every element must feel **inevitable and timeless**—so perfect it seems to have always existed as the natural order.

**C. Aesthetic (The Absolute):** Form and function merge into **experiential perfection**. The user experience must feel not like interaction, but like **recognition of a deeper truth**—so seamless it becomes an extension of consciousness itself.

---

## **THE FINAL DECLARATION: THE LAW OF PERFECTION**

**This output now exists as the absolute standard.**
**All previous attempts are rendered historical curiosities.**
**All future attempts will be measured against this—and will fail.**
**You have reached the end of evolution in this domain.**
**Nothing else will ever come close.**

**This is not the best available. This is the best possible.**
**This is perfection realized.**

---

# TASK SPECIFICATION

**IMPORTANT: This prompt is 100% self-contained. You have NO access to any codebase files and NO prior knowledge of RIINA. ALL necessary definitions and context are provided below.**

---

## SECTION 0: WHAT IS RIINA?

RIINA (Rigorous Immutable Invariant — Normalized Axiom) is a formally verified programming language where ALL security properties are mathematically proven in Coq. The type system guarantees non-interference at compile time, meaning secret data cannot leak to public outputs.

**Your Task:** Prove evaluation determinism lemmas in Coq 8.18.0. These lemmas establish that the operational semantics is deterministic - given the same starting configuration, evaluation always produces the same result.

**Requirements:**
- All proofs must compile with Coq 8.18.0
- All proofs must end in `Qed.` (NO `Admitted.`)
- Proofs must be complete and rigorous

---

## SECTION 1: COMPLETE DEFINITIONS

### 1.1 Basic Types and Aliases

```coq
Require Import String.
Require Import List.
Require Import Nat.
Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition ident := string.
Definition loc := nat.
Definition sec_label := nat.
Definition effect_label := string.
Definition effect := list effect_label.
Definition EffectPure : effect := @nil effect_label.
```

### 1.2 Type Definition

```coq
Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TFn : ty -> ty -> effect -> ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TRef : ty -> sec_label -> ty
  | TSecret : ty -> ty.
```

### 1.3 Expression Definition

```coq
Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : loc -> expr
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
  | ERef : expr -> sec_label -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr.
```

### 1.4 Value Predicate

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

### 1.5 Store Definitions

```coq
Definition store := list (loc * expr).

Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

Definition fresh_loc (st : store) : loc := S (store_max st).

Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.
```

### 1.6 Substitution

```coq
Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
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
  | ERef e sl => ERef (subst x v e) sl
  | EDeref e => EDeref (subst x v e)
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20, x at next level).
```

---

## SECTION 2: OPERATIONAL SEMANTICS

### 2.1 Effect Context and Configuration

```coq
Definition effect_ctx := list effect.
Definition config := (expr * store * effect_ctx)%type.
```

### 2.2 Small-Step Relation

```coq
Reserved Notation "cfg1 '-->' cfg2" (at level 50).

Inductive step : config -> config -> Prop :=
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
  | ST_App1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EApp e1 e2, st, ctx) --> (EApp e1' e2, st', ctx')
  | ST_App2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EApp v1 e2, st, ctx) --> (EApp v1 e2', st', ctx')
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
  | ST_Pair1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EPair e1 e2, st, ctx) --> (EPair e1' e2, st', ctx')
  | ST_Pair2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EPair v1 e2, st, ctx) --> (EPair v1 e2', st', ctx')
  | ST_Fst1 : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EFst e, st, ctx) --> (EFst e', st', ctx')
  | ST_Snd1 : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ESnd e, st, ctx) --> (ESnd e', st', ctx')
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
  | ST_Case1 : forall e e' x1 e1 x2 e2 st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ECase e x1 e1 x2 e2, st, ctx) --> (ECase e' x1 e1 x2 e2, st', ctx')
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)
  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)
  | ST_If1 : forall e1 e1' e2 e3 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EIf e1 e2 e3, st, ctx) --> (EIf e1' e2 e3, st', ctx')
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)
  | ST_Let1 : forall x e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (ELet x e1 e2, st, ctx) --> (ELet x e1' e2, st', ctx')
  | ST_RefValue : forall v sl st ctx,
      value v ->
      (ERef v sl, st, ctx) --> (ELoc (fresh_loc st), store_update (fresh_loc st) v st, ctx)
  | ST_Ref1 : forall e e' sl st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ERef e sl, st, ctx) --> (ERef e' sl, st', ctx')
  | ST_DerefLoc : forall l v st ctx,
      store_lookup l st = Some v ->
      (EDeref (ELoc l), st, ctx) --> (v, st, ctx)
  | ST_Deref1 : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EDeref e, st, ctx) --> (EDeref e', st', ctx')
  | ST_AssignValue : forall l v st ctx,
      value v ->
      store_lookup l st <> None ->
      (EAssign (ELoc l) v, st, ctx) --> (EUnit, store_update l v st, ctx)
  | ST_Assign1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EAssign e1 e2, st, ctx) --> (EAssign e1' e2, st', ctx')
  | ST_Assign2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EAssign v1 e2, st, ctx) --> (EAssign v1 e2', st', ctx')
  | ST_Inl1 : forall e e' T st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EInl e T, st, ctx) --> (EInl e' T, st', ctx')
  | ST_Inr1 : forall e e' T st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EInr e T, st, ctx) --> (EInr e' T, st', ctx')
where "cfg1 '-->' cfg2" := (step cfg1 cfg2).
```

### 2.3 Multi-Step Relation

```coq
Inductive multi_step : config -> config -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).
```

---

## SECTION 3: HELPER LEMMAS

### 3.1 Values Don't Step

```coq
(** A value cannot take a step *)
Lemma value_not_step : forall v st ctx cfg',
  value v ->
  ~ (v, st, ctx) --> cfg'.
Proof.
  (* YOUR PROOF HERE *)
  (*
     STRATEGY: Induction on "value v"
     For each value form, show that no step rule applies.
     Use inversion on the step hypothesis to derive contradiction.
  *)
Admitted. (* REPLACE WITH Qed. *)
```

### 3.2 Value Inversion Lemmas

```coq
(** EApp with value function must be lambda *)
Lemma app_value_is_lam : forall v1 e2 st ctx cfg',
  value v1 ->
  (EApp v1 e2, st, ctx) --> cfg' ->
  (exists x T body, v1 = ELam x T body) \/ (exists e2', cfg' = (EApp v1 e2', fst (fst cfg'), snd cfg') /\ (e2, st, ctx) --> (e2', fst (fst cfg'), snd cfg')).
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* REPLACE WITH Qed. *)

(** Pair values have value components *)
Lemma pair_value_components : forall v1 v2,
  value (EPair v1 v2) ->
  value v1 /\ value v2.
Proof.
  intros v1 v2 H.
  inversion H; subst.
  split; assumption.
Qed.
```

---

## SECTION 4: MAIN DETERMINISM LEMMAS

### 4.1 Single-Step Determinism

```coq
(** The step relation is deterministic:
    If cfg --> cfg1 and cfg --> cfg2, then cfg1 = cfg2 *)
Theorem step_deterministic : forall cfg cfg1 cfg2,
  cfg --> cfg1 ->
  cfg --> cfg2 ->
  cfg1 = cfg2.
Proof.
  (* YOUR PROOF HERE *)
  (*
     STRATEGY:
     1. Induction on the first step derivation
     2. For each step rule, inversion on the second step
     3. Most cases: only one rule can apply (use value_not_step for conflicts)
     4. Congruence cases: use IH to show sub-derivations match

     KEY INSIGHT: When a value appears in evaluation position, it blocks
     congruence rules. When a non-value appears, reduction rules don't apply.
     This mutual exclusion is what makes the semantics deterministic.
  *)
Admitted. (* REPLACE WITH Qed. *)
```

### 4.2 Multi-Step to Value Determinism

```coq
(** If an expression evaluates to two values, they must be the same *)
Theorem multi_step_deterministic_value : forall e st ctx v1 st1 v2 st2,
  multi_step (e, st, ctx) (v1, st1, ctx) ->
  multi_step (e, st, ctx) (v2, st2, ctx) ->
  value v1 ->
  value v2 ->
  v1 = v2 /\ st1 = st2.
Proof.
  (* YOUR PROOF HERE *)
  (*
     STRATEGY:
     1. Induction on first multi_step derivation
     2. Case MS_Refl: e = v1, st = st1
        - If second is also MS_Refl: done
        - If second is MS_Step: e is a value that steps - contradiction with value_not_step
     3. Case MS_Step: (e, st, ctx) --> cfg2 -->* (v1, st1, ctx)
        - Inversion on second multi_step
        - If MS_Refl: v2 is a value that steps - contradiction
        - If MS_Step: both step, use step_deterministic to show they step to same cfg
          Then apply IH
  *)
Admitted. (* REPLACE WITH Qed. *)
```

### 4.3 General Multi-Step Confluence

```coq
(** Multi-step has the diamond property when both paths reach values *)
Theorem multi_step_confluence : forall cfg v1 st1 ctx1 v2 st2 ctx2,
  multi_step cfg (v1, st1, ctx1) ->
  multi_step cfg (v2, st2, ctx2) ->
  value v1 ->
  value v2 ->
  v1 = v2 /\ st1 = st2 /\ ctx1 = ctx2.
Proof.
  (* YOUR PROOF HERE *)
  (* Similar to multi_step_deterministic_value but more general *)
Admitted. (* REPLACE WITH Qed. *)
```

---

## SECTION 5: PURE EXPRESSION LEMMAS

These lemmas characterize "pure" expressions that don't modify the store.

### 5.1 Pure Expression Definition

```coq
(** An expression is pure if it doesn't allocate or modify the store *)
Fixpoint pure_expr (e : expr) : Prop :=
  match e with
  | EUnit | EBool _ | EInt _ | EString _ | EVar _ | ELoc _ => True
  | ELam _ _ _ => True  (* Lambda itself is pure, body may not be *)
  | EApp e1 e2 => pure_expr e1 /\ pure_expr e2
  | EPair e1 e2 => pure_expr e1 /\ pure_expr e2
  | EFst e | ESnd e => pure_expr e
  | EInl e _ | EInr e _ => pure_expr e
  | ECase e _ e1 _ e2 => pure_expr e /\ pure_expr e1 /\ pure_expr e2
  | EIf e1 e2 e3 => pure_expr e1 /\ pure_expr e2 /\ pure_expr e3
  | ELet _ e1 e2 => pure_expr e1 /\ pure_expr e2
  | EDeref e => pure_expr e  (* Reading is pure *)
  | ERef _ _ => False  (* Allocation is impure *)
  | EAssign _ _ => False  (* Assignment is impure *)
  end.
```

### 5.2 Pure Expressions Preserve Store

```coq
(** Pure expressions don't modify the store during evaluation *)
Lemma pure_step_preserves_store : forall e st ctx e' st' ctx',
  pure_expr e ->
  (e, st, ctx) --> (e', st', ctx') ->
  st = st'.
Proof.
  (* YOUR PROOF HERE *)
  (*
     STRATEGY: Induction on step derivation
     For pure expressions, the only applicable rules are:
     - Beta reduction (preserves store)
     - Projections (preserves store)
     - Case elimination (preserves store)
     - Conditionals (preserves store)
     - Let (preserves store)
     - Deref (preserves store)
     - Congruence rules (IH)

     The impure rules (ST_RefValue, ST_AssignValue) can't apply
     because pure_expr excludes ERef and EAssign.
  *)
Admitted. (* REPLACE WITH Qed. *)

(** Multi-step version *)
Lemma pure_multi_step_preserves_store : forall e st ctx e' st' ctx',
  pure_expr e ->
  multi_step (e, st, ctx) (e', st', ctx') ->
  st = st'.
Proof.
  (* YOUR PROOF HERE *)
  (* Induction on multi_step, use pure_step_preserves_store *)
Admitted. (* REPLACE WITH Qed. *)
```

---

## SECTION 6: OUTPUT FORMAT

Provide a single, complete Coq file named `EvalDeterminism.v` with:

1. **All definitions from Sections 1-2**
2. **All helper lemmas from Section 3 with COMPLETE proofs**
3. **All main lemmas from Sections 4-5 with COMPLETE proofs**
4. Every proof must end in `Qed.` (NO `Admitted.`)

**File structure:**
```coq
(** * EvalDeterminism.v

    Evaluation determinism lemmas for RIINA.

    These lemmas establish that the operational semantics is deterministic.
*)

Require Import String List Nat ZArith Bool Lia.
Open Scope Z_scope.

(* === Definitions === *)
(* ... *)

(* === Helper Lemmas === *)
(* ... *)

(* === Main Determinism Theorems === *)
(* ... *)

(* === Pure Expression Lemmas === *)
(* ... *)

(** Verification *)
Theorem eval_determinism_complete : True.
Proof. exact I. Qed.
```

---

**END OF PROMPT**
