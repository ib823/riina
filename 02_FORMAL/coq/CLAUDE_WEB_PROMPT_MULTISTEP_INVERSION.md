# CLAUDE AI WEB DELEGATION PROMPT — Multi-Step Evaluation Inversion Lemmas

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

**Your Task:** Prove multi-step evaluation inversion lemmas in Coq 8.18.0. These lemmas decompose multi-step reductions of compound expressions (ERef, EDeref, EAssign) into their constituent evaluation steps.

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

(* Identifiers are strings *)
Definition ident := string.

(* Locations are natural numbers *)
Definition loc := nat.

(* Security levels *)
Definition sec_label := nat.
Definition Public : sec_label := 0.
Definition Secret : sec_label := 1.

(* Effects *)
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

(* Value is decidable for our purposes *)
Definition is_value (e : expr) : bool :=
  match e with
  | EUnit | EBool _ | EInt _ | EString _ | ELoc _ | ELam _ _ _ => true
  | EPair e1 e2 => is_value e1 && is_value e2
  | EInl e _ | EInr e _ => is_value e
  | _ => false
  end.
```

### 1.5 Store Definitions

```coq
(* Store maps locations to values *)
Definition store := list (loc * expr).

(* Lookup in store *)
Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

(* Maximum location in store *)
Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

(* Fresh location for allocation *)
Definition fresh_loc (st : store) : loc := S (store_max st).

(* Update store at location *)
Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.
```

### 1.6 Substitution

```coq
(* Substitution: replace variable x with value v in expression e *)
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

### 2.1 Effect Context

```coq
(* Effect context for tracking effects during evaluation *)
Definition effect_ctx := list effect.
```

### 2.2 Small-Step Relation

```coq
(* Small-step operational semantics *)
(* (expression, store, effect_context) --> (expression', store', effect_context') *)

Reserved Notation "cfg1 '-->' cfg2" (at level 50).

Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  (* Beta reduction *)
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)

  (* Application congruence - function position *)
  | ST_App1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EApp e1 e2, st, ctx) --> (EApp e1' e2, st', ctx')

  (* Application congruence - argument position *)
  | ST_App2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EApp v1 e2, st, ctx) --> (EApp v1 e2', st', ctx')

  (* Pair projections *)
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)

  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)

  (* Pair congruence *)
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

  (* Sum elimination *)
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)

  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)

  | ST_Case1 : forall e e' x1 e1 x2 e2 st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ECase e x1 e1 x2 e2, st, ctx) --> (ECase e' x1 e1 x2 e2, st', ctx')

  (* Conditionals *)
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)

  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)

  | ST_If1 : forall e1 e1' e2 e3 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EIf e1 e2 e3, st, ctx) --> (EIf e1' e2 e3, st', ctx')

  (* Let binding *)
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)

  | ST_Let1 : forall x e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (ELet x e1 e2, st, ctx) --> (ELet x e1' e2, st', ctx')

  (* Reference allocation *)
  | ST_RefValue : forall v sl st ctx,
      value v ->
      (ERef v sl, st, ctx) --> (ELoc (fresh_loc st), store_update (fresh_loc st) v st, ctx)

  | ST_Ref1 : forall e e' sl st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ERef e sl, st, ctx) --> (ERef e' sl, st', ctx')

  (* Dereference *)
  | ST_DerefLoc : forall l v st ctx,
      store_lookup l st = Some v ->
      (EDeref (ELoc l), st, ctx) --> (v, st, ctx)

  | ST_Deref1 : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EDeref e, st, ctx) --> (EDeref e', st', ctx')

  (* Assignment *)
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

where "cfg1 '-->' cfg2" := (step cfg1 cfg2).
```

### 2.3 Multi-Step Relation

```coq
(* Multi-step reduction (reflexive transitive closure) *)
Inductive multi_step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg,
      multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).
```

---

## SECTION 3: HELPER LEMMAS (Prove These First)

### 3.1 Values Don't Step

```coq
(** Values are stuck - they don't take steps *)
Lemma value_does_not_step : forall v st ctx cfg',
  value v ->
  ~ (v, st, ctx) --> cfg'.
Proof.
  (* YOUR PROOF HERE *)
  (* Hint: Induction on value v, then inversion on the step relation *)
Admitted. (* REPLACE WITH Qed. *)
```

### 3.2 Multi-Step Transitivity

```coq
(** Multi-step is transitive *)
Lemma multi_step_trans : forall cfg1 cfg2 cfg3,
  multi_step cfg1 cfg2 ->
  multi_step cfg2 cfg3 ->
  multi_step cfg1 cfg3.
Proof.
  (* YOUR PROOF HERE *)
  (* Hint: Induction on multi_step cfg1 cfg2 *)
Admitted. (* REPLACE WITH Qed. *)
```

### 3.3 Multi-Step Congruence Lemmas

```coq
(** Multi-step under ERef context *)
Lemma multi_step_ref : forall e e' sl st st' ctx ctx',
  multi_step (e, st, ctx) (e', st', ctx') ->
  multi_step (ERef e sl, st, ctx) (ERef e' sl, st', ctx').
Proof.
  (* YOUR PROOF HERE *)
  (* Hint: Induction on multi_step, use ST_Ref1 for step case *)
Admitted. (* REPLACE WITH Qed. *)

(** Multi-step under EDeref context *)
Lemma multi_step_deref : forall e e' st st' ctx ctx',
  multi_step (e, st, ctx) (e', st', ctx') ->
  multi_step (EDeref e, st, ctx) (EDeref e', st', ctx').
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* REPLACE WITH Qed. *)

(** Multi-step under EAssign left context *)
Lemma multi_step_assign1 : forall e1 e1' e2 st st' ctx ctx',
  multi_step (e1, st, ctx) (e1', st', ctx') ->
  multi_step (EAssign e1 e2, st, ctx) (EAssign e1' e2, st', ctx').
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* REPLACE WITH Qed. *)

(** Multi-step under EAssign right context (when left is value) *)
Lemma multi_step_assign2 : forall v1 e2 e2' st st' ctx ctx',
  value v1 ->
  multi_step (e2, st, ctx) (e2', st', ctx') ->
  multi_step (EAssign v1 e2, st, ctx) (EAssign v1 e2', st', ctx').
Proof.
  (* YOUR PROOF HERE *)
Admitted. (* REPLACE WITH Qed. *)
```

---

## SECTION 4: MAIN INVERSION LEMMAS (The Primary Task)

These are the critical lemmas that decompose multi-step evaluations.

### 4.1 ERef Inversion

```coq
(** When (ERef e sl) evaluates to a value, e must have evaluated to a value first,
    then the reference was allocated *)
Lemma multi_step_ref_inversion : forall e sl st v st' ctx,
  multi_step (ERef e sl, st, ctx) (v, st', ctx) ->
  value v ->
  exists v_inner st_mid l,
    multi_step (e, st, ctx) (v_inner, st_mid, ctx) /\
    value v_inner /\
    v = ELoc l /\
    l = fresh_loc st_mid /\
    st' = store_update l v_inner st_mid.
Proof.
  (* YOUR PROOF HERE *)
  (*
     PROOF STRATEGY:
     1. Induction on multi_step
     2. Base case (MS_Refl): ERef e sl is a value - but ERef is never a value!
        Use inversion on "value (ERef e sl)" to derive contradiction.
     3. Step case (MS_Step): We have (ERef e sl, st, ctx) --> cfg2 -->* (v, st', ctx)
        Inversion on the step gives two cases:
        a) ST_RefValue: e is already a value v_inner, we step to (ELoc l, st_mid, ctx)
           Then (ELoc l, st_mid, ctx) -->* (v, st', ctx)
           Since ELoc l is a value and v is a value, by determinism v = ELoc l, st' = st_mid
        b) ST_Ref1: e steps to e', then (ERef e' sl, st', ctx') -->* (v, st'', ctx)
           Apply IH to get the decomposition for e'
           Compose with the step from e to e'
  *)
Admitted. (* REPLACE WITH Qed. *)
```

### 4.2 EDeref Inversion

```coq
(** When (EDeref e) evaluates to a value, e must have evaluated to a location first,
    then the location was dereferenced *)
Lemma multi_step_deref_inversion : forall e st v st' ctx,
  multi_step (EDeref e, st, ctx) (v, st', ctx) ->
  value v ->
  exists l st_mid,
    multi_step (e, st, ctx) (ELoc l, st_mid, ctx) /\
    st' = st_mid /\
    store_lookup l st_mid = Some v.
Proof.
  (* YOUR PROOF HERE *)
  (*
     PROOF STRATEGY:
     1. Induction on multi_step
     2. Base case: EDeref e is never a value, contradiction
     3. Step case: Inversion on step gives:
        a) ST_DerefLoc: e = ELoc l, store_lookup l st = Some v', step to (v', st, ctx)
           Then (v', st, ctx) -->* (v, st', ctx)
           Since v' is retrieved from store (thus a value) and values don't step,
           we must have v = v', st' = st
        b) ST_Deref1: e steps to e', apply IH
  *)
Admitted. (* REPLACE WITH Qed. *)
```

### 4.3 EAssign Inversion

```coq
(** When (EAssign e1 e2) evaluates to a value, both subexpressions evaluated,
    then the assignment occurred *)
Lemma multi_step_assign_inversion : forall e1 e2 st v st' ctx,
  multi_step (EAssign e1 e2, st, ctx) (v, st', ctx) ->
  value v ->
  exists l v_val st_mid1 st_mid2,
    multi_step (e1, st, ctx) (ELoc l, st_mid1, ctx) /\
    multi_step (e2, st_mid1, ctx) (v_val, st_mid2, ctx) /\
    value v_val /\
    v = EUnit /\
    store_lookup l st_mid2 <> None /\
    st' = store_update l v_val st_mid2.
Proof.
  (* YOUR PROOF HERE *)
  (*
     PROOF STRATEGY:
     1. Induction on multi_step
     2. Base case: EAssign is never a value, contradiction
     3. Step case: Inversion on step gives three cases:
        a) ST_AssignValue: e1 = ELoc l, e2 = v_val (value), step to (EUnit, updated_store, ctx)
           Then (EUnit, ...) -->* (v, st', ctx)
           Since EUnit is a value, v = EUnit, st' = updated_store
        b) ST_Assign1: e1 steps to e1', apply IH
        c) ST_Assign2: e1 is value, e2 steps to e2', apply IH
  *)
Admitted. (* REPLACE WITH Qed. *)
```

---

## SECTION 5: OUTPUT FORMAT

Provide a single, complete Coq file named `MultiStepInversion.v` with:

1. **All definitions from Sections 1-2** (copy them exactly)
2. **All helper lemmas from Section 3 with COMPLETE proofs**
3. **All main lemmas from Section 4 with COMPLETE proofs**
4. Every proof must end in `Qed.` (NO `Admitted.`)

**File structure:**
```coq
(** * MultiStepInversion.v

    Multi-step evaluation inversion lemmas for RIINA.

    These lemmas decompose multi-step reductions of compound expressions
    (ERef, EDeref, EAssign) into their constituent evaluation steps.
*)

Require Import String List Nat ZArith Bool Lia.
Open Scope Z_scope.

(* === Section 1-2: Definitions === *)
(* ... all definitions ... *)

(* === Section 3: Helper Lemmas === *)
(* ... helper proofs ... *)

(* === Section 4: Main Inversion Lemmas === *)
(* ... main proofs ... *)

(** Verification: All lemmas proven *)
Theorem multi_step_inversion_complete : True.
Proof. exact I. Qed.
```

---

**END OF PROMPT**
