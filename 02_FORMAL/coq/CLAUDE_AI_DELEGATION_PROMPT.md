# CLAUDE AI DELEGATION PROMPT — RIINA FORMAL PROOFS

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  RIINA — Rigorous Immutable Invariant — Normalized Axiom                          ║
║  FORMAL PROOF DELEGATION PROMPT FOR CLAUDE AI (WEB)                              ║
║                                                                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE           ║
║  "QED Eternum."                                               ║
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

### Rule 5: Unbeatable Performance
Performance MUST be top of its class, unbeatable, efficient, and extremely small size hence insane performance. NOTHING else beats RIINA. In terms of language, it is the most complete fullstack and produces the best UI/UX, 1,000,000 times better than any 2nd best in human history, rendering all others totally backwards and obsolete.

---

## SECTION 1: RIINA CODEBASE CONTEXT

### 1.1 What is RIINA?

RIINA is the world's **first formally verified programming language** where:
- ALL security properties are mathematically PROVEN in Coq
- The type system GUARANTEES non-interference at compile time
- ZERO runtime security vulnerabilities are possible by construction
- The proofs eliminate ALL 350+ known threat categories

### 1.2 Coq Version and Environment

```
Coq Version: Rocq 9.1 (Coq 8.21)
Project Path: /workspaces/proof/02_FORMAL/coq/
Namespace: RIINA
Build Command: make (uses Makefile generated from _CoqProject)
```

### 1.3 Required Imports (ALWAYS include these)

```coq
Require Import String.
Require Import List.
Require Import Nat.
Require Import Lia.
Require Import Arith.
Require Import Bool.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.

Import ListNotations.
```

---

## SECTION 2: COMPLETE TYPE DEFINITIONS

### 2.0 Basic Type Aliases

```coq
(* Identifiers are strings *)
Definition ident := string.

(* Locations are natural numbers *)
Definition loc := nat.

(* Configuration: expression, store, effect context *)
Definition config := (expr * store * effect_ctx)%type.

(* Type aliases for security levels, labels, etc. *)
Definition security_level := nat.  (* 0 = public, 1 = secret, etc. *)
Definition label := string.
Definition taint_source := string.
Definition sanitizer := string.
Definition capability := string.
Definition proposition := expr.
Definition effect_label := string.
Definition effect := list effect_label.
Definition EffectPure := @nil effect_label.
```

### 2.1 Core Type Definition (ty)

```coq
Inductive ty : Type :=
  (* Primitive types *)
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  (* Function type with effect *)
  | TFn : ty -> ty -> effect -> ty
  (* Compound types *)
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  (* Collection types *)
  | TList : ty -> ty
  | TOption : ty -> ty
  (* Reference types *)
  | TRef : ty -> security_level -> ty
  (* Security types *)
  | TSecret : ty -> ty
  | TLabeled : ty -> label -> ty
  | TTainted : ty -> taint_source -> ty
  | TSanitized : ty -> sanitizer -> ty
  (* Capability types *)
  | TCapability : capability -> ty
  | TCapabilityFull : capability -> ty
  (* Proof types *)
  | TProof : proposition -> ty
  (* Channel types *)
  | TChan : ty -> ty
  | TSecureChan : ty -> security_level -> ty
  (* Constant-time types *)
  | TConstantTime : ty -> ty
  | TZeroizing : ty -> ty.
```

### 2.2 Expression Definition (expr)

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
  (* Sums *)
  | EInl : expr -> ty -> expr
  | EInr : expr -> ty -> expr
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
  (* Control flow *)
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  (* Effects *)
  | EPerform : effect_label -> expr -> expr
  | EHandle : expr -> ident -> expr -> expr
  (* References *)
  | ERef : expr -> security_level -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  (* Security operations *)
  | EClassify : expr -> security_level -> expr
  | EDeclassify : expr -> expr -> expr
  (* Proofs *)
  | EProve : expr -> expr
  | ERequire : effect_label -> expr -> expr
  | EGrant : effect_label -> expr -> expr.
```

### 2.3 Value Predicate

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

### 2.4 First-Order Type Predicate

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false  (* Functions are higher-order *)
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef T _ => first_order_type T
  | TList T => first_order_type T
  | TOption T => first_order_type T
  | TSecret T => first_order_type T
  | TLabeled T _ => first_order_type T
  | TTainted T _ => first_order_type T
  | TSanitized T _ => first_order_type T
  | TCapability _ | TCapabilityFull _ => true
  | TProof _ => true
  | TChan T => first_order_type T
  | TSecureChan T _ => first_order_type T
  | TConstantTime T => first_order_type T
  | TZeroizing T => first_order_type T
  end.
```

### 2.5 Free Variables and Closed Expressions

```coq
(* Free variable check *)
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
  | EHandle e y h => free_in x e \/ (x <> y /\ free_in x h)
  | _ => False  (* Constants, locations have no free variables *)
  end.

(* Closed expression: no free variables *)
Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.
```

### 2.6 Substitution

```coq
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
  | EHandle e y h =>
      EHandle (subst x v e) y (if string_dec x y then h else subst x v h)
  | other => other  (* Constants, locations unchanged *)
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20, x at next level).
```

---

## SECTION 3: STORE AND OPERATIONAL SEMANTICS

### 3.1 Store Definitions

```coq
(* Store: maps locations to values *)
Definition store := list (loc * expr).

(* Store typing: maps locations to types with security levels *)
Definition store_ty := list (loc * ty * security_level).

(* Lookup in store *)
Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

(* Lookup in store typing *)
Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * security_level) :=
  match Σ with
  | nil => None
  | (l', T, sl) :: Σ' =>
      if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l Σ'
  end.

(* Fresh location allocator *)
Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

Definition fresh_loc (st : store) : loc := S (store_max st).

(* Store update: replace value at location or add new *)
Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.

(* Store typing extension - Kripke world ordering *)
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).
```

### 3.2 Small-Step Operational Semantics

```coq
(* Effect context *)
Definition effect_ctx := list effect.

(* Small-step relation: (e, st, ctx) --> (e', st', ctx') *)
Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  (* Beta reduction *)
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)

  (* Application congruence *)
  | ST_App1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EApp e1 e2, st, ctx) --> (EApp e1' e2, st', ctx')

  | ST_App2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EApp v1 e2, st, ctx) --> (EApp v1 e2', st', ctx')

  (* Projections *)
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)

  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)

  (* Sum elimination *)
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)

  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)

  (* Conditionals *)
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)

  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)

  (* Let binding *)
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)

  (* Effects *)
  | ST_HandleStep : forall e e' x h st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EHandle e x h, st, ctx) --> (EHandle e' x h, st', ctx')

  | ST_HandleValue : forall v x h st ctx,
      value v ->
      (EHandle v x h, st, ctx) --> ([x := v] h, st, ctx)

  (* References *)
  | ST_RefStep : forall e e' sl st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ERef e sl, st, ctx) --> (ERef e' sl, st', ctx')

  | ST_RefValue : forall v sl st ctx l,
      value v ->
      l = fresh_loc st ->
      (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)

  | ST_DerefStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EDeref e, st, ctx) --> (EDeref e', st', ctx')

  | ST_DerefLoc : forall v l st ctx,
      store_lookup l st = Some v ->
      (EDeref (ELoc l), st, ctx) --> (v, st, ctx)

  | ST_Assign1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EAssign e1 e2, st, ctx) --> (EAssign e1' e2, st', ctx')

  | ST_AssignLoc : forall l v st ctx,
      value v ->
      store_lookup l st <> None ->
      (EAssign (ELoc l) v, st, ctx) --> (EUnit, store_update l v st, ctx)

where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

(* Multi-step reduction *)
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

## SECTION 4: STEP-INDEXED LOGICAL RELATIONS (THE CORE)

### 4.1 Key Insight: Cumulative Definition

The value relation is **CUMULATIVE**: `val_rel_n n Σ T v1 v2` explicitly includes
`val_rel_n n' Σ T v1 v2` for all n' < n as a conjunct. This makes downward
monotonicity trivial.

**CRITICAL**: At step 0, `val_rel_n 0 Σ T v1 v2 = True`. This is standard in
step-indexed logical relations but means you get NO structural information
at step 0. You need n ≥ 1 to extract value/closed/structural properties.

### 4.2 Type-Structural Value Relation (val_rel_at_type)

```coq
(* val_rel_at_type: structural relation at a fixed step index
   Takes parameterized predicates for store/value relations *)
Section ValRelAtN.
  Variable Σ : store_ty.
  Variable store_rel_pred : store_ty -> store -> store -> Prop.
  Variable val_rel_lower : store_ty -> ty -> expr -> expr -> Prop.
  Variable store_rel_lower : store_ty -> store -> store -> Prop.

  Fixpoint val_rel_at_type (T : ty) (v1 v2 : expr) {struct T} : Prop :=
    match T with
    (* Primitive types - equality *)
    | TUnit => v1 = EUnit /\ v2 = EUnit
    | TBool => exists b, v1 = EBool b /\ v2 = EBool b
    | TInt => exists i, v1 = EInt i /\ v2 = EInt i
    | TString => exists s, v1 = EString s /\ v2 = EString s
    | TBytes => v1 = v2

    (* Security types - indistinguishable (always True) *)
    | TSecret T' => True
    | TLabeled T' _ => True
    | TTainted T' _ => True
    | TSanitized T' _ => True
    | TCapability _ | TCapabilityFull _ => True
    | TProof _ => True
    | TChan _ | TSecureChan _ _ => True
    | TConstantTime T' | TZeroizing T' => True
    | TList T' | TOption T' => True

    (* Reference types - same location *)
    | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l

    (* Product types - component-wise with SAME-LEVEL recursion *)
    | TProd T1 T2 =>
        exists x1 y1 x2 y2,
          v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
          val_rel_at_type T1 x1 x2 /\ val_rel_at_type T2 y1 y2

    (* Sum types - matching constructor with SAME-LEVEL recursion *)
    | TSum T1 T2 =>
        (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                       val_rel_at_type T1 x1 x2) \/
        (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                       val_rel_at_type T2 y1 y2)

    (* Function types - Kripke quantification *)
    | TFn T1 T2 eff =>
        forall Σ', store_ty_extends Σ Σ' ->
          forall x y,
            value x -> value y -> closed_expr x -> closed_expr y ->
            val_rel_lower Σ' T1 x y ->  (* Arguments at LOWER step, EXTENDED store *)
            forall st1 st2 ctx,
              store_rel_pred Σ' st1 st2 ->  (* Store at EXTENDED store *)
              exists v1' v2' st1' st2' ctx' Σ'',
                store_ty_extends Σ' Σ'' /\
                (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
                (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
                val_rel_lower Σ'' T2 v1' v2' /\  (* Results at LOWER step, FINAL store *)
                store_rel_lower Σ'' st1' st2'
    end.
End ValRelAtN.
```

### 4.3 Step-Indexed Relations (val_rel_n and store_rel_n)

```coq
(* MUTUALLY RECURSIVE step-indexed relations *)
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True  (* At step 0, everything is trivially related *)
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\  (* CUMULATIVE: includes all lower levels *)
      value v1 /\ value v2 /\
      closed_expr v1 /\ closed_expr v2 /\
      (* val_rel_at_type uses predicates at LOWER step n' *)
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end
with store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => True  (* At step 0, everything is trivially related *)
  | S n' =>
      store_rel_n n' Σ st1 st2 /\  (* CUMULATIVE: includes all lower levels *)
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' Σ T v1 v2)
  end.
```

### 4.4 Key Properties (ALREADY PROVEN)

```coq
(* Downward monotonicity - trivial from cumulative definition *)
Lemma val_rel_n_mono : forall n m Σ T v1 v2,
  val_rel_n n Σ T v1 v2 -> m <= n -> val_rel_n m Σ T v1 v2.

Lemma store_rel_n_mono : forall n m Σ st1 st2,
  store_rel_n n Σ st1 st2 -> m <= n -> store_rel_n m Σ st1 st2.

(* Store extension reflexivity and transitivity *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 -> store_ty_extends Σ2 Σ3 -> store_ty_extends Σ1 Σ3.

(* For FIRST-ORDER types, val_rel_at_type is PREDICATE-INDEPENDENT *)
Lemma val_rel_at_type_first_order : forall T Σ v1 v2 sp1 sp2 vl1 vl2 sl1 sl2,
  first_order_type T = true ->
  val_rel_at_type Σ sp1 vl1 sl1 T v1 v2 ->
  val_rel_at_type Σ sp2 vl2 sl2 T v1 v2.

(* For FIRST-ORDER types, val_rel_at_type is STORE-TYPING-INDEPENDENT *)
Lemma val_rel_at_type_store_ty_indep : forall T Σ Σ' sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  val_rel_at_type Σ' sp vl sl T v1 v2.
```

### 4.5 THE STEP-0 FIX: val_rel_at_type_fo (REVOLUTIONARY)

**THE PROBLEM:** With `val_rel_n 0 = True`, we cannot prove:
- `exp_rel_step1_if`: need SAME boolean to take SAME branch
- `exp_rel_step1_case`: need MATCHING constructor to take SAME branch

**THE SOLUTION:** Use `val_rel_at_type_fo` which gives structural equality
for first-order types INDEPENDENT of step index:

```coq
(** First-order value relation - gives structure even at step 0 *)
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b  (* SAME b! *)
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret _ => True  (* Secrets always indistinguishable *)
  | TLabeled _ _ => True
  | TTainted _ _ => True
  | TSanitized _ _ => True
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList _ => True  (* Simplified *)
  | TOption _ => True
  | TProd T1 T2 =>
      exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)
  | TFn _ _ _ => True  (* Functions: defer to step-indexed *)
  | _ => True
  end.

(** REVOLUTIONARY: val_rel_n_base gives structure for FO types at ANY step *)
Definition val_rel_n_base (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).
```

**WHY THIS WORKS:**

For TBool: `val_rel_at_type_fo TBool v1 v2 = exists b, v1 = EBool b /\ v2 = EBool b`

This means v1 and v2 are THE SAME boolean! So when we prove `exp_rel_step1_if`:
- If both are `EBool true`, both take the THEN branch
- If both are `EBool false`, both take the ELSE branch

**KEY EXTRACTION LEMMAS (PROVEN in NonInterference_v3.v):**

```coq
(** Extract value from val_rel_n_base *)
Lemma val_rel_n_base_value : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 ->
  value v1 /\ value v2.
Proof.
  intros. unfold val_rel_n_base in H.
  destruct H as [Hv1 [Hv2 _]]. auto.
Qed.

(** Extract closed from val_rel_n_base *)
Lemma val_rel_n_base_closed : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 ->
  closed_expr v1 /\ closed_expr v2.
Proof.
  intros. unfold val_rel_n_base in H.
  destruct H as [_ [_ [Hc1 [Hc2 _]]]]. auto.
Qed.

(** Extract SAME boolean from val_rel_n_base TBool - THE KEY LEMMA *)
Lemma val_rel_n_base_bool : forall Sigma v1 v2,
  val_rel_n_base Sigma TBool v1 v2 ->
  exists b, v1 = EBool b /\ v2 = EBool b.
Proof.
  intros. unfold val_rel_n_base in H.
  destruct H as [_ [_ [_ [_ Hfo]]]].
  simpl in Hfo. exact Hfo.
Qed.

(** Extract MATCHING constructors from val_rel_n_base TSum *)
Lemma val_rel_n_base_sum_fo : forall Sigma T1 T2 v1 v2,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v1 v2 ->
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\
                 val_rel_at_type_fo T1 a1 a2) \/
  (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\
                 val_rel_at_type_fo T2 b1 b2).
Proof.
  intros. unfold val_rel_n_base in H0.
  destruct H0 as [_ [_ [_ [_ Hfo]]]].
  rewrite H in Hfo. simpl in Hfo. exact Hfo.
Qed.

(** Extract MATCHING structure from val_rel_n_base TProd *)
Lemma val_rel_n_base_prod_fo : forall Sigma T1 T2 v1 v2,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Sigma (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2.
Proof.
  intros. unfold val_rel_n_base in H0.
  destruct H0 as [_ [_ [_ [_ Hfo]]]].
  rewrite H in Hfo. simpl in Hfo. exact Hfo.
Qed.
```

**STORE RELATION BASE:**

```coq
(** Store relation at base level - just store_max equality *)
Definition store_rel_n_base (Sigma : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.
```

These lemmas are what make `exp_rel_step1_if` and `exp_rel_step1_case` PROVABLE without axioms!

### 4.6 COMPLETE PROOF EXAMPLE: exp_rel_step1_if (PROVEN IN NonInterference_v3.v)

```coq
(** FORMER AXIOM: exp_rel_step1_if - NOW PROVEN *)
Theorem exp_rel_step1_if : forall Sigma v v' e2 e2' e3 e3' st1 st2 ctx,
  val_rel_n_base Sigma TBool v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (EIf v e2 e3, st1, ctx) -->* (r1, st1', ctx') /\
    (EIf v' e2' e3', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Sigma v v' e2 e2' e3 e3' st1 st2 ctx Hval Hstore.
  (* Extract SAME boolean *)
  destruct (val_rel_n_base_bool Sigma v v' Hval) as [b [Heq1 Heq2]].
  subst v v'.
  (* Both have the SAME boolean b *)
  destruct b.
  - (* b = true: both step to then branch *)
    exists e2, e2', st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := (e2, st1, ctx)).
      * apply ST_IfTrue.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := (e2', st2, ctx)).
      * apply ST_IfTrue.
      * apply MS_Refl.
  - (* b = false: both step to else branch *)
    exists e3, e3', st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := (e3, st1, ctx)).
      * apply ST_IfFalse.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := (e3', st2, ctx)).
      * apply ST_IfFalse.
      * apply MS_Refl.
Qed.
```

**KEY INSIGHT:** The proof works because `val_rel_n_base_bool` extracts the SAME boolean `b` from both `v` and `v'`. This is possible because `val_rel_at_type_fo TBool v v' = exists b, v = EBool b /\ v' = EBool b`.

### 4.7 COMPLETE PROOF EXAMPLE: exp_rel_step1_case_fo (PROVEN)

```coq
(** FORMER AXIOM: exp_rel_step1_case - NOW PROVEN for FO types *)
Theorem exp_rel_step1_case_fo : forall Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n_base Sigma (TSum T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ECase v x1 e1 x2 e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ECase v' x1 e1' x2 e2', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Sigma T1 T2 v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Hfo Hval Hstore.
  (* Extract MATCHING constructors *)
  destruct (val_rel_n_base_sum_fo Sigma T1 T2 v v' Hfo Hval)
    as [[a1 [a2 [Heq1 [Heq2 _]]]] | [b1 [b2 [Heq1 [Heq2 _]]]]].
  - (* Both EInl: step to first branch *)
    subst v v'.
    destruct (val_rel_n_base_value Sigma (TSum T1 T2) (EInl a1 T2) (EInl a2 T2) Hval)
      as [Hva1 Hva2].
    inversion Hva1; subst.
    inversion Hva2; subst.
    exists ([x1 := a1] e1), ([x1 := a2] e1'), st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := ([x1 := a1] e1, st1, ctx)).
      * apply ST_CaseInl. exact H0.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := ([x1 := a2] e1', st2, ctx)).
      * apply ST_CaseInl. exact H1.
      * apply MS_Refl.
  - (* Both EInr: step to second branch *)
    subst v v'.
    destruct (val_rel_n_base_value Sigma (TSum T1 T2) (EInr b1 T1) (EInr b2 T1) Hval)
      as [Hvb1 Hvb2].
    inversion Hvb1; subst.
    inversion Hvb2; subst.
    exists ([x2 := b1] e2), ([x2 := b2] e2'), st1, st2, ctx.
    split.
    + apply MS_Step with (cfg2 := ([x2 := b1] e2, st1, ctx)).
      * apply ST_CaseInr. exact H0.
      * apply MS_Refl.
    + apply MS_Step with (cfg2 := ([x2 := b2] e2', st2, ctx)).
      * apply ST_CaseInr. exact H1.
      * apply MS_Refl.
Qed.
```

### 4.8 COMPLETE PROOF EXAMPLE: exp_rel_step1_let (PROVEN)

```coq
(** FORMER AXIOM: exp_rel_step1_let - NOW PROVEN *)
Theorem exp_rel_step1_let : forall Sigma T v v' x e2 e2' st1 st2 ctx,
  val_rel_n_base Sigma T v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ELet x v e2, st1, ctx) -->* (r1, st1', ctx') /\
    (ELet x v' e2', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Sigma T v v' x e2 e2' st1 st2 ctx Hval Hstore.
  destruct (val_rel_n_base_value Sigma T v v' Hval) as [Hv1 Hv2].
  exists ([x := v] e2), ([x := v'] e2'), st1, st2, ctx.
  split.
  - apply MS_Step with (cfg2 := ([x := v] e2, st1, ctx)).
    + apply ST_LetValue. exact Hv1.
    + apply MS_Refl.
  - apply MS_Step with (cfg2 := ([x := v'] e2', st2, ctx)).
    + apply ST_LetValue. exact Hv2.
    + apply MS_Refl.
Qed.
```

### 4.9 COMPLETE PROOF EXAMPLE: exp_rel_step1_handle (PROVEN)

```coq
(** FORMER AXIOM: exp_rel_step1_handle - NOW PROVEN *)
Theorem exp_rel_step1_handle : forall Sigma T v v' x h h' st1 st2 ctx,
  val_rel_n_base Sigma T v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (EHandle v x h, st1, ctx) -->* (r1, st1', ctx') /\
    (EHandle v' x h', st2, ctx) -->* (r2, st2', ctx').
Proof.
  intros Sigma T v v' x h h' st1 st2 ctx Hval Hstore.
  destruct (val_rel_n_base_value Sigma T v v' Hval) as [Hv1 Hv2].
  exists ([x := v] h), ([x := v'] h'), st1, st2, ctx.
  split.
  - apply MS_Step with (cfg2 := ([x := v] h, st1, ctx)).
    + apply ST_HandleValue. exact Hv1.
    + apply MS_Refl.
  - apply MS_Step with (cfg2 := ([x := v'] h', st2, ctx)).
    + apply ST_HandleValue. exact Hv2.
    + apply MS_Refl.
Qed.
```

---

## SECTION 5: YOUR TASK

**SPECIFIC TASK:**
[INSERT YOUR SPECIFIC TASK HERE]

**OUTPUT REQUIREMENTS:**

1. **Coq Syntax**: Output MUST be valid Rocq 9.1 (Coq 8.21) syntax
2. **Complete Proofs**: Every lemma MUST end with `Qed.` (NO `Admitted.`)
3. **Bullet Structure**: Use `-`, `+`, `*`, `--`, `++`, `**` correctly
4. **No Placeholders**: Every tactic must be concrete, no `...` or `TODO`
5. **Compatible Imports**: Use only the imports listed in Section 1.3
6. **Namespace**: All definitions go in RIINA namespace

**VERIFICATION CHECKLIST (YOU MUST VERIFY):**

- [ ] Does every `Proof.` have a matching `Qed.`?
- [ ] Are all bullets properly nested?
- [ ] Are all identifiers spelled correctly (case-sensitive)?
- [ ] Does the proof use only available lemmas?
- [ ] Is the proof COMPLETE with no admits?

---

## SECTION 6: EXAMPLE OUTPUT FORMAT

```coq
(** * Lemma: [Name]

    [Detailed description of what this lemma proves]

    Proof Strategy:
    1. [Step 1]
    2. [Step 2]
    ...
*)
Lemma lemma_name : forall ...,
  [statement].
Proof.
  intros ...
  [complete tactic sequence]
Qed.
```

---

## SECTION 7: CRITICAL REMINDERS

1. **DO NOT SKIP STEPS** — Every case must be handled explicitly
2. **DO NOT USE `admit`** — Every proof must be complete
3. **DO NOT GUESS** — If unsure, state assumptions explicitly
4. **VERIFY TERMINATION** — Recursive definitions must terminate
5. **CHECK BULLET STRUCTURE** — Coq is strict about bullet nesting

---

## SECTION 8: KNOWN COQ PITFALLS

### 8.1 Bullet Structure Errors

```coq
(* WRONG - unfinished bullet *)
Proof.
  split.
  - (* first goal *)
    apply H1.
  - (* second goal *)
    split.
    + (* sub-goal 1 - NOT FINISHED *)
(* Coq error: "Wrong bullet -: Current bullet + is not finished" *)

(* CORRECT - finish all sub-goals before next top-level bullet *)
Proof.
  split.
  - apply H1.
  - split.
    + apply H2.
    + apply H3.  (* Must finish + before going to next - *)
Qed.
```

### 8.2 Destruct Existentials Correctly

```coq
(* For conjunctions: *)
destruct H as [H1 H2].

(* For disjunctions: *)
destruct H as [H1 | H2].

(* For existentials: *)
destruct H as [x Hx].

(* For nested existentials: *)
destruct H as [x [y [Heq1 [Heq2 Hrel]]]].
```

### 8.3 IHT1 vs IHT2 in Type Induction

```coq
(* When doing induction on type T, for TProd T1 T2: *)
(* Use IHT1 for the first component, IHT2 for the second *)
induction T; intros ...
  - (* TProd T1 T2 *)
    apply IHT1 with ...; assumption.  (* For first component *)
    apply IHT2 with ...; assumption.  (* For second component *)
```

### 8.4 First-Order Type Boolean Extraction

```coq
(* For TProd/TSum, first_order_type returns a boolean AND *)
(* To extract, use: *)
apply Bool.andb_true_iff in Hfo.
destruct Hfo as [Hfo1 Hfo2].
(* Now Hfo1 : first_order_type T1 = true *)
(* And Hfo2 : first_order_type T2 = true *)
```

### 8.5 Common val_rel_n Extraction Pattern

```coq
(* For n = S n', val_rel_n has structure: *)
(*   val_rel_n n' ... /\ value v1 /\ value v2 /\ closed v1 /\ closed v2 /\ ... *)
destruct Hrel as [Hprev [Hv1 [Hv2 [Hc1 [Hc2 HT]]]]].
(* Now:
   - Hprev : val_rel_n n' Σ T v1 v2  (cumulative part)
   - Hv1 : value v1
   - Hv2 : value v2
   - Hc1 : closed_expr v1
   - Hc2 : closed_expr v2
   - HT : val_rel_at_type ... T v1 v2  (structural part)
*)
```

---

## APPENDIX: COMMON TACTICS

```coq
(* Introduction and destruction *)
intros.                    (* Introduce hypotheses *)
destruct H as [H1 H2].     (* Destruct conjunction *)
destruct H as [H1 | H2].   (* Destruct disjunction *)
inversion H.               (* Invert inductive hypothesis *)

(* Goals *)
exact H.                   (* Exact match *)
apply H.                   (* Apply hypothesis *)
reflexivity.               (* Prove equality *)
assumption.                (* Goal is in context *)

(* Arithmetic *)
lia.                       (* Linear integer arithmetic *)
auto.                      (* Automatic proof search *)

(* Existentials *)
exists x.                  (* Provide witness *)
destruct H as [x Hx].      (* Extract witness *)

(* Rewriting *)
rewrite H.                 (* Rewrite with equality *)
rewrite <- H.              (* Rewrite backwards *)
subst.                     (* Substitute all equalities *)

(* Compound *)
split.                     (* Split conjunction goal *)
left. / right.             (* Choose disjunct *)
repeat split.              (* Split multiple conjunctions *)
```

---

**END OF PROMPT — NOW EXECUTE YOUR TASK WITH ULTRA KIASU PRECISION**
