# CLAUDE AI WEB PROMPT: RIINA Typing Lemmas

**Target:** Claude AI Web / ChatGPT 5.2 Extended Thinking
**Purpose:** Prove typing infrastructure lemmas for step-indexed logical relations
**Output:** Complete Coq 8.18.0 file with ALL proofs ending in `Qed.`

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

## Context

RIINA (Rigorous Immutable Invariant — Normalized Axiom) is a formally verified programming language. Its type safety and security properties are proven in Coq 8.18.0 using step-indexed logical relations.

This prompt requests **typing infrastructure lemmas** - lemmas about how typing judgments interact with contexts, stores, and substitutions. These are foundational lemmas required by the fundamental theorem of logical relations.

## Your Mission

Create a **complete, self-contained Coq file** named `TypingLemmas.v` that proves all the typing infrastructure lemmas listed below.

**CRITICAL REQUIREMENTS:**
1. Every proof MUST end with `Qed.` — NO `Admitted.` allowed
2. The file must be 100% self-contained (include all definitions)
3. Must compile with Coq 8.18.0
4. Use only standard library imports (no external dependencies)

---

# COMPLETE DEFINITIONS

Copy these definitions EXACTLY into your output file:

```coq
(** * TypingLemmas.v - Typing Infrastructure for RIINA *)
(**
    RIINA (Rigorous Immutable Invariant — Normalized Axiom)
    Typing infrastructure lemmas for step-indexed logical relations.
    All proofs complete with Qed. - NO Admitted.
    Coq Version: 8.18.0
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import ZArith.
Require Import Bool.
Require Import Lia.

Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.

(* ========================================================================= *)
(** ** SECTION 1: BASIC TYPE ALIASES *)
(* ========================================================================= *)

Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition Public : security_level := 0%nat.
Definition Secret : security_level := 1%nat.
Definition effect_label := string.
Definition effect := list effect_label.
Definition EffectPure : effect := nil.
Definition sec_label := security_level.

(* ========================================================================= *)
(** ** SECTION 2: TYPE DEFINITION *)
(* ========================================================================= *)

Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TFn : ty -> ty -> effect -> ty      (* Function: T1 -> T2 with effect *)
  | TProd : ty -> ty -> ty              (* Product: T1 * T2 *)
  | TSum : ty -> ty -> ty               (* Sum: T1 + T2 *)
  | TRef : ty -> sec_label -> ty        (* Reference: ref T at security level *)
  | TSecret : ty -> ty                  (* Secret/classified value *)
  | TList : ty -> ty
  | TOption : ty -> ty
  | TCapability : string -> ty
  | TProof : ty -> ty.

(* Type equality is decidable *)
Lemma ty_eq_dec : forall (T1 T2 : ty), {T1 = T2} + {T1 <> T2}.
Proof.
  decide equality.
  - apply string_dec.
  - apply Nat.eq_dec.
  - apply list_eq_dec. apply string_dec.
Qed.

(* ========================================================================= *)
(** ** SECTION 3: EXPRESSION DEFINITION *)
(* ========================================================================= *)

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
  | EAssign : expr -> expr -> expr
  | EClassify : expr -> expr
  | EDeclassify : expr -> expr -> expr.

(* ========================================================================= *)
(** ** SECTION 4: VALUE PREDICATE *)
(* ========================================================================= *)

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

(* ========================================================================= *)
(** ** SECTION 5: FREE VARIABLES AND CLOSED EXPRESSIONS *)
(* ========================================================================= *)

Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EUnit | EBool _ | EInt _ | EString _ | ELoc _ => False
  | EVar y => x = y
  | ELam y _ body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  | EPair e1 e2 => free_in x e1 \/ free_in x e2
  | EFst e | ESnd e => free_in x e
  | EInl e _ | EInr e _ => free_in x e
  | ECase e y1 e1 y2 e2 =>
      free_in x e \/ (x <> y1 /\ free_in x e1) \/ (x <> y2 /\ free_in x e2)
  | EIf e1 e2 e3 => free_in x e1 \/ free_in x e2 \/ free_in x e3
  | ELet y e1 e2 => free_in x e1 \/ (x <> y /\ free_in x e2)
  | ERef e _ => free_in x e
  | EDeref e => free_in x e
  | EAssign e1 e2 => free_in x e1 \/ free_in x e2
  | EClassify e => free_in x e
  | EDeclassify e1 e2 => free_in x e1 \/ free_in x e2
  end.

Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(* ========================================================================= *)
(** ** SECTION 6: STORE DEFINITIONS *)
(* ========================================================================= *)

Definition store := list (loc * expr).
Definition store_ty := list (loc * ty * sec_label).

Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

Fixpoint store_ty_lookup (l : loc) (Sigma : store_ty) : option (ty * sec_label) :=
  match Sigma with
  | nil => None
  | (l', T, sl) :: rest =>
      if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l rest
  end.

Definition store_ty_extends (Sigma Sigma' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Sigma = Some (T, sl) ->
    store_ty_lookup l Sigma' = Some (T, sl).

(* ========================================================================= *)
(** ** SECTION 7: TYPING CONTEXT *)
(* ========================================================================= *)

Definition ctx := list (ident * ty).
Definition lin_ctx := list (ident * ty).

Fixpoint ctx_lookup (x : ident) (Gamma : ctx) : option ty :=
  match Gamma with
  | nil => None
  | (y, T) :: rest => if string_dec x y then Some T else ctx_lookup x rest
  end.

Definition ctx_extends (Gamma Gamma' : ctx) : Prop :=
  forall x T, ctx_lookup x Gamma = Some T -> ctx_lookup x Gamma' = Some T.

(* ========================================================================= *)
(** ** SECTION 8: TYPING JUDGMENT *)
(* ========================================================================= *)

Inductive has_type : ctx -> store_ty -> lin_ctx -> expr -> ty -> effect -> Prop :=
  | T_Unit : forall Gamma Sigma Delta,
      has_type Gamma Sigma Delta EUnit TUnit EffectPure
  | T_Bool : forall Gamma Sigma Delta b,
      has_type Gamma Sigma Delta (EBool b) TBool EffectPure
  | T_Int : forall Gamma Sigma Delta n,
      has_type Gamma Sigma Delta (EInt n) TInt EffectPure
  | T_String : forall Gamma Sigma Delta s,
      has_type Gamma Sigma Delta (EString s) TString EffectPure
  | T_Var : forall Gamma Sigma Delta x T,
      ctx_lookup x Gamma = Some T ->
      has_type Gamma Sigma Delta (EVar x) T EffectPure
  | T_Loc : forall Gamma Sigma Delta l T sl,
      store_ty_lookup l Sigma = Some (T, sl) ->
      has_type Gamma Sigma Delta (ELoc l) (TRef T sl) EffectPure
  | T_Lam : forall Gamma Sigma Delta x T1 T2 e eff,
      has_type ((x, T1) :: Gamma) Sigma Delta e T2 eff ->
      has_type Gamma Sigma Delta (ELam x T1 e) (TFn T1 T2 eff) EffectPure
  | T_App : forall Gamma Sigma Delta e1 e2 T1 T2 eff eff1 eff2,
      has_type Gamma Sigma Delta e1 (TFn T1 T2 eff) eff1 ->
      has_type Gamma Sigma Delta e2 T1 eff2 ->
      has_type Gamma Sigma Delta (EApp e1 e2) T2 (eff1 ++ eff2 ++ eff)
  | T_Pair : forall Gamma Sigma Delta e1 e2 T1 T2 eff1 eff2,
      has_type Gamma Sigma Delta e1 T1 eff1 ->
      has_type Gamma Sigma Delta e2 T2 eff2 ->
      has_type Gamma Sigma Delta (EPair e1 e2) (TProd T1 T2) (eff1 ++ eff2)
  | T_Fst : forall Gamma Sigma Delta e T1 T2 eff,
      has_type Gamma Sigma Delta e (TProd T1 T2) eff ->
      has_type Gamma Sigma Delta (EFst e) T1 eff
  | T_Snd : forall Gamma Sigma Delta e T1 T2 eff,
      has_type Gamma Sigma Delta e (TProd T1 T2) eff ->
      has_type Gamma Sigma Delta (ESnd e) T2 eff
  | T_Inl : forall Gamma Sigma Delta e T1 T2 eff,
      has_type Gamma Sigma Delta e T1 eff ->
      has_type Gamma Sigma Delta (EInl e T2) (TSum T1 T2) eff
  | T_Inr : forall Gamma Sigma Delta e T1 T2 eff,
      has_type Gamma Sigma Delta e T2 eff ->
      has_type Gamma Sigma Delta (EInr e T1) (TSum T1 T2) eff
  | T_Case : forall Gamma Sigma Delta e x1 e1 x2 e2 T1 T2 T eff eff1 eff2,
      has_type Gamma Sigma Delta e (TSum T1 T2) eff ->
      has_type ((x1, T1) :: Gamma) Sigma Delta e1 T eff1 ->
      has_type ((x2, T2) :: Gamma) Sigma Delta e2 T eff2 ->
      has_type Gamma Sigma Delta (ECase e x1 e1 x2 e2) T (eff ++ eff1 ++ eff2)
  | T_If : forall Gamma Sigma Delta e1 e2 e3 T eff1 eff2 eff3,
      has_type Gamma Sigma Delta e1 TBool eff1 ->
      has_type Gamma Sigma Delta e2 T eff2 ->
      has_type Gamma Sigma Delta e3 T eff3 ->
      has_type Gamma Sigma Delta (EIf e1 e2 e3) T (eff1 ++ eff2 ++ eff3)
  | T_Let : forall Gamma Sigma Delta x e1 e2 T1 T2 eff1 eff2,
      has_type Gamma Sigma Delta e1 T1 eff1 ->
      has_type ((x, T1) :: Gamma) Sigma Delta e2 T2 eff2 ->
      has_type Gamma Sigma Delta (ELet x e1 e2) T2 (eff1 ++ eff2)
  | T_Ref : forall Gamma Sigma Delta e T sl eff,
      has_type Gamma Sigma Delta e T eff ->
      has_type Gamma Sigma Delta (ERef e sl) (TRef T sl) eff
  | T_Deref : forall Gamma Sigma Delta e T sl eff,
      has_type Gamma Sigma Delta e (TRef T sl) eff ->
      has_type Gamma Sigma Delta (EDeref e) T eff
  | T_Assign : forall Gamma Sigma Delta e1 e2 T sl eff1 eff2,
      has_type Gamma Sigma Delta e1 (TRef T sl) eff1 ->
      has_type Gamma Sigma Delta e2 T eff2 ->
      has_type Gamma Sigma Delta (EAssign e1 e2) TUnit (eff1 ++ eff2).

(* ========================================================================= *)
(** ** SECTION 9: SUBSTITUTION *)
(* ========================================================================= *)

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
  | EClassify e => EClassify (subst x v e)
  | EDeclassify e1 e2 => EDeclassify (subst x v e1) (subst x v e2)
  end.
```

---

# LEMMAS TO PROVE

You must prove ALL of the following lemmas. Each proof must end with `Qed.`

## Category 1: Store Typing Extension Properties

```coq
(** Reflexivity of store typing extension *)
Lemma store_ty_extends_refl : forall Sigma,
  store_ty_extends Sigma Sigma.

(** Transitivity of store typing extension *)
Lemma store_ty_extends_trans : forall Sigma1 Sigma2 Sigma3,
  store_ty_extends Sigma1 Sigma2 ->
  store_ty_extends Sigma2 Sigma3 ->
  store_ty_extends Sigma1 Sigma3.

(** Lookup decidability *)
Lemma store_ty_lookup_dec : forall l Sigma,
  {exists T sl, store_ty_lookup l Sigma = Some (T, sl)} +
  {store_ty_lookup l Sigma = None}.
```

## Category 2: Context Extension Properties

```coq
(** Reflexivity of context extension *)
Lemma ctx_extends_refl : forall Gamma,
  ctx_extends Gamma Gamma.

(** Transitivity of context extension *)
Lemma ctx_extends_trans : forall Gamma1 Gamma2 Gamma3,
  ctx_extends Gamma1 Gamma2 ->
  ctx_extends Gamma2 Gamma3 ->
  ctx_extends Gamma1 Gamma3.

(** Adding a binding extends the context *)
Lemma ctx_extends_cons : forall Gamma x T,
  ctx_extends Gamma ((x, T) :: Gamma).

(** Lookup in extended context *)
Lemma ctx_lookup_extends : forall Gamma Gamma' x T,
  ctx_extends Gamma Gamma' ->
  ctx_lookup x Gamma = Some T ->
  ctx_lookup x Gamma' = Some T.
```

## Category 3: Typing Weakening Lemmas

```coq
(** Store typing weakening: typing preserved under store extension *)
Lemma has_type_store_weakening : forall Gamma Sigma Sigma' Delta e T eff,
  has_type Gamma Sigma Delta e T eff ->
  store_ty_extends Sigma Sigma' ->
  has_type Gamma Sigma' Delta e T eff.

(** Context weakening: typing preserved under context extension *)
Lemma has_type_ctx_weakening : forall Gamma Gamma' Sigma Delta e T eff,
  has_type Gamma Sigma Delta e T eff ->
  ctx_extends Gamma Gamma' ->
  has_type Gamma' Sigma Delta e T eff.

(** Specific weakening: adding an unused variable *)
Lemma has_type_weakening_cons : forall Gamma Sigma Delta x T' e T eff,
  has_type Gamma Sigma Delta e T eff ->
  ~ free_in x e ->
  has_type ((x, T') :: Gamma) Sigma Delta e T eff.
```

## Category 4: Substitution Lemmas

```coq
(** Substitution preserves typing *)
Lemma substitution_preserves_typing : forall Gamma Sigma Delta x v e T_x T eff,
  has_type ((x, T_x) :: Gamma) Sigma Delta e T eff ->
  has_type Gamma Sigma Delta v T_x EffectPure ->
  value v ->
  closed_expr v ->
  has_type Gamma Sigma Delta (subst x v e) T eff.

(** Substitution with closed value doesn't introduce free variables *)
Lemma subst_closed : forall x v e,
  closed_expr v ->
  closed_expr e ->
  closed_expr (subst x v e).

(** Free variable behavior under substitution *)
Lemma free_in_subst : forall x y v e,
  free_in y (subst x v e) ->
  (y <> x /\ free_in y e) \/ free_in y v.
```

## Category 5: Value Typing Properties

```coq
(** Values have pure effect *)
Lemma value_has_pure_effect : forall Gamma Sigma Delta v T eff,
  value v ->
  has_type Gamma Sigma Delta v T eff ->
  eff = EffectPure.

(** Closed values can be typed in empty context *)
Lemma closed_value_empty_ctx : forall Sigma Delta v T eff,
  has_type nil Sigma Delta v T eff ->
  closed_expr v.

(** Canonical forms for booleans *)
Lemma canonical_bool : forall Sigma Delta v,
  value v ->
  has_type nil Sigma Delta v TBool EffectPure ->
  exists b, v = EBool b.

(** Canonical forms for functions *)
Lemma canonical_fn : forall Sigma Delta v T1 T2 eff,
  value v ->
  has_type nil Sigma Delta v (TFn T1 T2 eff) EffectPure ->
  exists x body, v = ELam x T1 body.

(** Canonical forms for pairs *)
Lemma canonical_pair : forall Sigma Delta v T1 T2,
  value v ->
  has_type nil Sigma Delta v (TProd T1 T2) EffectPure ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.

(** Canonical forms for references *)
Lemma canonical_ref : forall Sigma Delta v T sl,
  value v ->
  has_type nil Sigma Delta v (TRef T sl) EffectPure ->
  exists l, v = ELoc l.
```

## Category 6: Type Uniqueness

```coq
(** Typing is deterministic for well-formed expressions *)
Lemma typing_unique : forall Gamma Sigma Delta e T1 T2 eff1 eff2,
  has_type Gamma Sigma Delta e T1 eff1 ->
  has_type Gamma Sigma Delta e T2 eff2 ->
  T1 = T2.
```

---

# OUTPUT FORMAT

Provide a single, complete Coq file that:

1. Starts with the header comment and all imports
2. Includes ALL definitions from Section 1-9 above
3. Proves ALL lemmas listed in Categories 1-6
4. Every proof ends with `Qed.` (ZERO `Admitted.`)
5. Compiles successfully with `coqc TypingLemmas.v`
6. Ends with a summary theorem and `Print Assumptions`

Example ending:
```coq
(** All typing lemmas proven *)
Theorem all_typing_lemmas_proven : True.
Proof. exact I. Qed.

Print Assumptions all_typing_lemmas_proven.
```

---

# PROOF STRATEGIES

## For Extension Properties (Categories 1-2):
- Use `unfold` to expand definitions
- Apply the hypothesis directly or use transitivity

## For Weakening Lemmas (Category 3):
- Use induction on the typing derivation (`induction Htype`)
- Apply the IH and extension lemmas
- Key case: `T_Var` uses `ctx_lookup_extends`, `T_Loc` uses `store_ty_extends`

## For Substitution Lemmas (Category 4):
- Use induction on expression structure or typing derivation
- Handle variable cases carefully with `string_dec`
- Binding cases (lambda, let, case) need case analysis on whether the bound variable equals the substituted variable

## For Value Properties (Category 5):
- Values are constructed from value constructors
- Use inversion on `value v` and `has_type ... v ...`
- Canonical forms follow from value inversion + typing inversion

## For Type Uniqueness (Category 6):
- Induction on the first typing derivation
- Invert the second derivation and show types must match
- Expression constructors determine unique typing rules

---

# VERIFICATION

After generating, verify:
1. `coqc TypingLemmas.v` succeeds with no errors
2. Output shows "Closed under the global context" (no axioms)
3. All 20+ lemmas proven with `Qed.`

**BEGIN GENERATION NOW.**
