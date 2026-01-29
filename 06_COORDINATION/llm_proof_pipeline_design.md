# RIINA LLM-Assisted Proof Pipeline v1.0.0

**Document ID:** RIINA_LLM_PROOF_PIPELINE_v1_0_0  
**Version:** 1.0.0  
**Date:** January 2026  
**Author:** RIINA Formal Verification Team  
**Status:** Technical Specification

---

## Executive Summary

This document specifies a complete LLM-assisted formal proof generation pipeline for the RIINA programming language. The pipeline leverages the superior LLM tooling available for Lean 4 and Dafny while maintaining Coq 8.18.0 as the trusted ground truth for all verified proofs.

**Architecture Overview:**

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     RIINA Coq Specifications (.v)                       │
│            (Type Safety, Non-Interference, Termination, etc.)           │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                    ┌───────────────┴───────────────┐
                    ▼                               ▼
        ┌───────────────────────┐       ┌───────────────────────┐
        │  riina-proof-export   │       │  riina-proof-export   │
        │     (Coq → Lean 4)    │       │    (Coq → Dafny)      │
        └───────────────────────┘       └───────────────────────┘
                    │                               │
                    ▼                               ▼
        ┌───────────────────────┐       ┌───────────────────────┐
        │   Lean 4 Specs (.lean)│       │  Dafny Specs (.dfy)   │
        └───────────────────────┘       └───────────────────────┘
                    │                               │
                    ▼                               ▼
        ┌───────────────────────┐       ┌───────────────────────┐
        │  Lean Copilot / LLM   │       │  GPT-4 / Claude LLM   │
        │   Proof Generation    │       │   Proof Generation    │
        │   (74.2% automation)  │       │   (82-96% automation) │
        └───────────────────────┘       └───────────────────────┘
                    │                               │
                    ▼                               ▼
        ┌───────────────────────┐       ┌───────────────────────┐
        │  Lean 4 Type Checker  │       │   Dafny Verifier      │
        │     (Validation)      │       │     (Validation)      │
        └───────────────────────┘       └───────────────────────┘
                    │                               │
                    └───────────────┬───────────────┘
                                    ▼
                    ┌───────────────────────────────┐
                    │     riina-proof-import        │
                    │  (Extract Proof Structure)    │
                    └───────────────────────────────┘
                                    │
                                    ▼
                    ┌───────────────────────────────┐
                    │   Coq Proof Sketch (.v)       │
                    │  (Human-Assisted Completion)  │
                    └───────────────────────────────┘
                                    │
                                    ▼
                    ┌───────────────────────────────┐
                    │    Coq 8.18.0 Type Checker    │
                    │    (TRUSTED GROUND TRUTH)     │
                    └───────────────────────────────┘
```

**Key Design Principles:**

1. **Coq as Single Source of Truth**: All proofs must ultimately check in Coq. Lean/Dafny are proof discovery aids, not replacements.
2. **LLM-Friendly Targets**: Export to formats where LLM tooling achieves highest success rates.
3. **Proof Structure Extraction**: Import validated proofs as structured hints, not verbatim translations.
4. **Incremental Adoption**: Pipeline augments existing Coq workflow; never blocks manual proving.

---

## 1. Translation Rules: Coq to Lean 4

### 1.1 Type System Correspondence

| Coq Construct | Lean 4 Equivalent | Notes |
|---------------|-------------------|-------|
| `Inductive T` | `inductive T` | Direct correspondence |
| `Definition f` | `def f` | Must prove termination |
| `Fixpoint f` | `def f` / `partial def f` | Use `partial` for non-structural recursion |
| `Lemma`/`Theorem` | `theorem` | Proofs via tactics |
| `Axiom` | `axiom` | Avoid; use `sorry` for development |
| `Section`/`Variable` | `variable` / `section` | Similar scoping |
| `Set`/`Type` | `Type` / `Type*` | Universe polymorphism differs |
| `Prop` | `Prop` | Proof irrelevance in both |

### 1.2 Tactic Correspondence

| Coq Tactic | Lean 4 Equivalent | Example |
|------------|-------------------|---------|
| `intros x y` | `intro x y` | `intro h` in Lean |
| `destruct e` | `cases e` / `match e with` | Pattern matching |
| `induction e` | `induction e with` | Named cases |
| `simpl` | `simp` / `dsimp` | `simp` more aggressive |
| `unfold f` | `unfold f` / `simp only [f]` | Direct unfold |
| `rewrite H` | `rw [H]` | `rw [←H]` for reverse |
| `apply H` | `apply H` / `exact H` | `exact` for direct terms |
| `exact t` | `exact t` | Identical |
| `constructor` | `constructor` | Identical |
| `auto` | `trivial` / `decide` / `aesop` | Aesop is most powerful |
| `lia` / `omega` | `omega` | Mathlib's `omega` |
| `inversion H` | `cases H` / `rcases H` | Pattern match on hypothesis |
| `eauto` | `aesop` | Extensible automation |
| `reflexivity` | `rfl` | Propositional equality |
| `split` | `constructor` / `And.intro` | Conjunction introduction |
| `left`/`right` | `left`/`right` | Disjunction introduction |
| `exists x` | `use x` / `exact ⟨x, h⟩` | Existential witness |
| `assert (H: P)` | `have H : P := ...` | Local hypothesis |

### 1.3 Notation Translation

```coq
(* Coq notation *)
Notation "x ⊑ y" := (flows_to x y) (at level 70).
Notation "⟨ e , s ⟩ ⟶ ⟨ e' , s' ⟩" := (step (e, s) (e', s')) (at level 40).
```

```lean
-- Lean 4 notation
infixl:70 " ⊑ " => flowsTo
notation "⟨" e ", " s "⟩ ⟶ ⟨" e' ", " s' "⟩" => Step (e, s) (e', s')
```

### 1.4 Concrete RIINA Examples

#### Example 1: Security Level Lattice

**Coq (Original):**
```coq
Inductive security_level : Type :=
  | LPublic
  | LInternal
  | LSession
  | LUser
  | LSystem
  | LSecret.

Definition flows_to (l1 l2 : security_level) : Prop :=
  match l1, l2 with
  | LPublic, _ => True
  | LInternal, LInternal | LInternal, LSession | LInternal, LUser 
  | LInternal, LSystem | LInternal, LSecret => True
  | LSession, LSession | LSession, LUser | LSession, LSystem | LSession, LSecret => True
  | LUser, LUser | LUser, LSystem | LUser, LSecret => True
  | LSystem, LSystem | LSystem, LSecret => True
  | LSecret, LSecret => True
  | _, _ => False
  end.

Lemma flows_to_refl : forall l, flows_to l l.
Proof.
  intros l. destruct l; simpl; auto.
Qed.

Lemma flows_to_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof.
  intros l1 l2 l3 H12 H23.
  destruct l1, l2, l3; simpl in *; auto; contradiction.
Qed.
```

**Lean 4 (Translated):**
```lean
inductive SecurityLevel : Type where
  | LPublic
  | LInternal
  | LSession
  | LUser
  | LSystem
  | LSecret
  deriving DecidableEq, Repr

def flowsTo : SecurityLevel → SecurityLevel → Prop
  | .LPublic, _ => True
  | .LInternal, .LInternal | .LInternal, .LSession | .LInternal, .LUser 
  | .LInternal, .LSystem | .LInternal, .LSecret => True
  | .LSession, .LSession | .LSession, .LUser | .LSession, .LSystem 
  | .LSession, .LSecret => True
  | .LUser, .LUser | .LUser, .LSystem | .LUser, .LSecret => True
  | .LSystem, .LSystem | .LSystem, .LSecret => True
  | .LSecret, .LSecret => True
  | _, _ => False

instance : Decidable (flowsTo l1 l2) := by
  unfold flowsTo; cases l1 <;> cases l2 <;> decide

infixl:70 " ⊑ " => flowsTo

theorem flowsTo_refl : ∀ l, l ⊑ l := by
  intro l; cases l <;> trivial

theorem flowsTo_trans : ∀ l1 l2 l3, l1 ⊑ l2 → l2 ⊑ l3 → l1 ⊑ l3 := by
  intro l1 l2 l3 h12 h23
  cases l1 <;> cases l2 <;> cases l3 <;> simp_all [flowsTo]
```

#### Example 2: RIINA Type Definition

**Coq (Original):**
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
  | TRef : ty -> security_level -> ty
  | TSecret : ty -> ty
  | TLabeled : ty -> security_level -> ty
  | TChan : session_type -> ty.

Fixpoint ty_size (t : ty) : nat :=
  match t with
  | TUnit | TBool | TInt | TString | TBytes => 1
  | TFn t1 t2 _ => 1 + ty_size t1 + ty_size t2
  | TProd t1 t2 => 1 + ty_size t1 + ty_size t2
  | TSum t1 t2 => 1 + ty_size t1 + ty_size t2
  | TRef t _ => 1 + ty_size t
  | TSecret t => 1 + ty_size t
  | TLabeled t _ => 1 + ty_size t
  | TChan _ => 1
  end.
```

**Lean 4 (Translated):**
```lean
inductive Ty : Type where
  | TUnit : Ty
  | TBool : Ty
  | TInt : Ty
  | TString : Ty
  | TBytes : Ty
  | TFn : Ty → Ty → Effect → Ty
  | TProd : Ty → Ty → Ty
  | TSum : Ty → Ty → Ty
  | TRef : Ty → SecurityLevel → Ty
  | TSecret : Ty → Ty
  | TLabeled : Ty → SecurityLevel → Ty
  | TChan : SessionType → Ty
  deriving DecidableEq, Repr

def Ty.size : Ty → Nat
  | .TUnit | .TBool | .TInt | .TString | .TBytes => 1
  | .TFn t1 t2 _ => 1 + t1.size + t2.size
  | .TProd t1 t2 => 1 + t1.size + t2.size
  | .TSum t1 t2 => 1 + t1.size + t2.size
  | .TRef t _ => 1 + t.size
  | .TSecret t => 1 + t.size
  | .TLabeled t _ => 1 + t.size
  | .TChan _ => 1
```

#### Example 3: Progress Theorem

**Coq (Original):**
```coq
Theorem progress : forall Γ e T eff,
  has_type Γ e T eff ->
  closed e ->
  value e \/ exists e' s', step (e, empty_store) (e', s').
Proof.
  intros Γ e T eff Hty Hclosed.
  induction Hty; auto.
  - (* EApp case *)
    right. destruct IHHty1 as [Hv1 | [e1' [s1' Hstep1]]]; auto.
    + destruct IHHty2 as [Hv2 | [e2' [s2' Hstep2]]]; auto.
      * inversion Hv1; subst.
        exists (subst x e2 e), empty_store.
        apply ST_AppAbs; auto.
      * exists (EApp e1 e2'), s2'.
        apply ST_App2; auto.
    + exists (EApp e1' e2), s1'.
      apply ST_App1; auto.
  (* ... remaining cases ... *)
Qed.
```

**Lean 4 (Translated):**
```lean
theorem progress : ∀ Γ e T eff,
    HasType Γ e T eff →
    Closed e →
    Value e ∨ ∃ e' s', Step (e, emptyStore) (e', s') := by
  intro Γ e T eff hty hclosed
  induction hty with
  | TUnit => left; exact Value.VUnit
  | TBool b => left; exact Value.VBool b
  | TInt n => left; exact Value.VInt n
  | TLam x τ body _ => left; exact Value.VLam x τ body
  | TApp _ _ _ _ ih1 ih2 =>
    right
    rcases ih1 (closed_app_l hclosed) with hv1 | ⟨e1', s1', hstep1⟩
    · rcases ih2 (closed_app_r hclosed) with hv2 | ⟨e2', s2', hstep2⟩
      · cases hv1 with
        | VLam x τ body =>
          exact ⟨subst x _ body, emptyStore, Step.ST_AppAbs hv2⟩
      · exact ⟨Expr.EApp _ e2', s2', Step.ST_App2 hv1 hstep2⟩
    · exact ⟨Expr.EApp e1' _, s1', Step.ST_App1 hstep1⟩
  -- ... remaining cases with similar structure ...
```

### 1.5 Handling Differences

| Issue | Coq Behavior | Lean 4 Handling |
|-------|--------------|-----------------|
| Universe polymorphism | Explicit `Set`/`Type` | Use `Type*` / `universe u` |
| Proof irrelevance | `Prop` is proof-irrelevant | Same in `Prop` |
| Dependent pattern matching | `match ... return ... with` | `match ... with` (inferred) |
| Termination checking | Structural by default | Must be explicit or use `partial` |
| Axiom of choice | `Require Import Classical` | `import Mathlib.Logic.Classical` |
| Functional extensionality | Axiom | `funext` in Mathlib |

---

## 2. Translation Rules: Coq to Dafny

### 2.1 Type System Correspondence

| Coq Construct | Dafny Equivalent | Notes |
|---------------|------------------|-------|
| `Inductive T` | `datatype T` | Algebraic data types |
| `Definition f` | `function f` | Pure, must terminate |
| `Fixpoint f` | `function f` with `decreases` | Explicit termination |
| `Lemma`/`Theorem` | `lemma` | `requires`/`ensures` |
| `Axiom` | `lemma {:axiom}` or `assume` | Use sparingly |
| `nat` | `nat` | Non-negative integers |
| `bool` | `bool` | Direct correspondence |
| `list A` | `seq<A>` | Sequences |
| `option A` | `Option<A>` (custom) or `A?` | Nullable type |

### 2.2 Specification Correspondence

| Coq Construct | Dafny Equivalent |
|---------------|------------------|
| `forall x, P x` | `forall x :: P(x)` |
| `exists x, P x` | `exists x :: P(x)` |
| `P /\ Q` | `P && Q` |
| `P \/ Q` | `P \|\| Q` |
| `P -> Q` | `P ==> Q` |
| `~P` | `!P` |
| `x = y` | `x == y` |
| Step-indexed relation `rel_n n` | `decreases n` clause |

### 2.3 Concrete RIINA Examples

#### Example 1: Security Level Lattice

**Coq (Original):**
```coq
Inductive security_level : Type :=
  | LPublic | LInternal | LSession | LUser | LSystem | LSecret.

Definition flows_to (l1 l2 : security_level) : Prop := (* ... *).

Lemma flows_to_refl : forall l, flows_to l l.
Lemma flows_to_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
```

**Dafny (Translated):**
```dafny
datatype SecurityLevel = LPublic | LInternal | LSession | LUser | LSystem | LSecret

predicate FlowsTo(l1: SecurityLevel, l2: SecurityLevel) {
  match (l1, l2)
    case (LPublic, _) => true
    case (LInternal, LInternal) | (LInternal, LSession) | 
         (LInternal, LUser) | (LInternal, LSystem) | (LInternal, LSecret) => true
    case (LSession, LSession) | (LSession, LUser) | 
         (LSession, LSystem) | (LSession, LSecret) => true
    case (LUser, LUser) | (LUser, LSystem) | (LUser, LSecret) => true
    case (LSystem, LSystem) | (LSystem, LSecret) => true
    case (LSecret, LSecret) => true
    case _ => false
}

lemma FlowsToRefl(l: SecurityLevel)
  ensures FlowsTo(l, l)
{
  // Dafny auto-verifies via case analysis
}

lemma FlowsToTrans(l1: SecurityLevel, l2: SecurityLevel, l3: SecurityLevel)
  requires FlowsTo(l1, l2)
  requires FlowsTo(l2, l3)
  ensures FlowsTo(l1, l3)
{
  // Dafny auto-verifies via case analysis on all combinations
}
```

#### Example 2: RIINA Type and Expression Definitions

**Coq (Original):**
```coq
Inductive ty : Type :=
  | TUnit | TBool | TInt | TString | TBytes
  | TFn : ty -> ty -> effect -> ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TRef : ty -> security_level -> ty
  | TSecret : ty -> ty
  | TLabeled : ty -> security_level -> ty
  | TChan : session_type -> ty.

Inductive expr : Type :=
  | EUnit | EBool : bool -> expr | EInt : nat -> expr
  | EVar : ident -> expr
  | ELam : ident -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr | ESnd : expr -> expr
  | EInl : expr -> ty -> expr | EInr : expr -> ty -> expr
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  (* ... effects, refs, etc. ... *)
  .
```

**Dafny (Translated):**
```dafny
datatype Effect = Pure | IO | State | Crypto | Network | Concurrent

datatype SessionType = 
  | STEnd 
  | STSend(ty: Ty, cont: SessionType) 
  | STRecv(ty: Ty, cont: SessionType)
  | STChoice(left: SessionType, right: SessionType)
  | STBranch(left: SessionType, right: SessionType)

datatype Ty =
  | TUnit | TBool | TInt | TString | TBytes
  | TFn(arg: Ty, ret: Ty, eff: Effect)
  | TProd(fst: Ty, snd: Ty)
  | TSum(left: Ty, right: Ty)
  | TRef(inner: Ty, level: SecurityLevel)
  | TSecret(inner: Ty)
  | TLabeled(inner: Ty, level: SecurityLevel)
  | TChan(session: SessionType)

type Ident = string

datatype Expr =
  | EUnit
  | EBool(b: bool)
  | EInt(n: nat)
  | EString(s: string)
  | EVar(name: Ident)
  | ELam(param: Ident, paramTy: Ty, body: Expr)
  | EApp(func: Expr, arg: Expr)
  | EPair(fst: Expr, snd: Expr)
  | EFst(pair: Expr)
  | ESnd(pair: Expr)
  | EInl(value: Expr, rightTy: Ty)
  | EInr(value: Expr, leftTy: Ty)
  | ECase(scrutinee: Expr, leftVar: Ident, leftBody: Expr, rightVar: Ident, rightBody: Expr)
  | EIf(cond: Expr, thenBranch: Expr, elseBranch: Expr)
  | ELet(bindVar: Ident, bindExpr: Expr, body: Expr)
  | ERef(initial: Expr, level: SecurityLevel)
  | EDeref(ref: Expr)
  | EAssign(ref: Expr, value: Expr)
  | EClassify(expr: Expr)
  | EDeclassify(expr: Expr, proof: Expr)

function TySize(t: Ty): nat {
  match t
    case TUnit | TBool | TInt | TString | TBytes => 1
    case TFn(t1, t2, _) => 1 + TySize(t1) + TySize(t2)
    case TProd(t1, t2) => 1 + TySize(t1) + TySize(t2)
    case TSum(t1, t2) => 1 + TySize(t1) + TySize(t2)
    case TRef(t, _) => 1 + TySize(t)
    case TSecret(t) => 1 + TySize(t)
    case TLabeled(t, _) => 1 + TySize(t)
    case TChan(_) => 1
}
```

#### Example 3: Type Checking and Progress

**Coq (Original):**
```coq
Inductive has_type : context -> expr -> ty -> effect -> Prop :=
  | T_Unit : forall Γ, has_type Γ EUnit TUnit Pure
  | T_Bool : forall Γ b, has_type Γ (EBool b) TBool Pure
  | T_Int : forall Γ n, has_type Γ (EInt n) TInt Pure
  | T_Var : forall Γ x T,
      lookup Γ x = Some T ->
      has_type Γ (EVar x) T Pure
  | T_Lam : forall Γ x T1 T2 e eff,
      has_type (extend Γ x T1) e T2 eff ->
      has_type Γ (ELam x T1 e) (TFn T1 T2 eff) Pure
  | T_App : forall Γ e1 e2 T1 T2 eff1 eff2 eff,
      has_type Γ e1 (TFn T1 T2 eff) eff1 ->
      has_type Γ e2 T1 eff2 ->
      effect_join eff1 (effect_join eff2 eff) eff ->
      has_type Γ (EApp e1 e2) T2 eff
  (* ... *)
  .

Theorem progress : forall Γ e T eff,
  has_type Γ e T eff -> closed e ->
  value e \/ exists e' s', step (e, empty_store) (e', s').
```

**Dafny (Translated):**
```dafny
type Context = map<Ident, Ty>

predicate HasType(ctx: Context, e: Expr, t: Ty, eff: Effect)
  decreases e
{
  match e
    case EUnit => t == TUnit && eff == Pure
    case EBool(_) => t == TBool && eff == Pure
    case EInt(_) => t == TInt && eff == Pure
    case EVar(x) => x in ctx && ctx[x] == t && eff == Pure
    case ELam(x, paramTy, body) =>
      exists retTy, bodyEff ::
        t == TFn(paramTy, retTy, bodyEff) &&
        HasType(ctx[x := paramTy], body, retTy, bodyEff) &&
        eff == Pure
    case EApp(e1, e2) =>
      exists argTy, funEff, e1Eff, e2Eff ::
        HasType(ctx, e1, TFn(argTy, t, funEff), e1Eff) &&
        HasType(ctx, e2, argTy, e2Eff) &&
        EffectJoin(e1Eff, EffectJoin(e2Eff, funEff)) == eff
    case EPair(e1, e2) =>
      exists t1, t2, eff1, eff2 ::
        t == TProd(t1, t2) &&
        HasType(ctx, e1, t1, eff1) &&
        HasType(ctx, e2, t2, eff2) &&
        EffectJoin(eff1, eff2) == eff
    // ... remaining cases ...
    case _ => false
}

predicate Value(e: Expr) {
  match e
    case EUnit => true
    case EBool(_) => true
    case EInt(_) => true
    case EString(_) => true
    case ELam(_, _, _) => true
    case EPair(e1, e2) => Value(e1) && Value(e2)
    case EInl(v, _) => Value(v)
    case EInr(v, _) => Value(v)
    case _ => false
}

predicate Closed(e: Expr) {
  FreeVars(e) == {}
}

datatype StepResult = 
  | Stepped(newExpr: Expr, newStore: Store) 
  | Stuck

lemma Progress(ctx: Context, e: Expr, t: Ty, eff: Effect)
  requires HasType(ctx, e, t, eff)
  requires Closed(e)
  requires ctx == map[]
  ensures Value(e) || exists e', s' :: Step(e, EmptyStore()) == Stepped(e', s')
{
  match e
    case EUnit => assert Value(e);
    case EBool(_) => assert Value(e);
    case EInt(_) => assert Value(e);
    case ELam(_, _, _) => assert Value(e);
    case EApp(e1, e2) =>
      // Recursive case: need to show e1 and e2 make progress
      // Then case split on whether they are values
      // If both values, e1 must be lambda, so beta-reduce
      assert !Value(e);
      // ... detailed proof steps extracted by LLM ...
    case EIf(cond, thenE, elseE) =>
      if Value(cond) {
        assert cond.EBool?;  // By canonical forms
        // Step to appropriate branch
      } else {
        Progress(ctx, cond, TBool, eff);
        // Step the condition
      }
    // ... remaining cases ...
}
```

### 2.4 Step-Indexed Relations in Dafny

For RIINA's non-interference proofs using step-indexed logical relations:

**Coq (Step-indexed relation):**
```coq
Fixpoint exp_rel (n : nat) (T : ty) (e1 e2 : expr) (s1 s2 : store) : Prop :=
  match n with
  | 0 => True
  | S n' =>
    forall v1 s1', steps_to n' (e1, s1) (v1, s1') ->
    exists v2 s2', steps_to n' (e2, s2) (v2, s2') /\
    val_rel n' T v1 v2 s1' s2'
  end.
```

**Dafny (with decreases clause):**
```dafny
predicate ExpRel(n: nat, t: Ty, e1: Expr, e2: Expr, s1: Store, s2: Store)
  decreases n, TySize(t)
{
  if n == 0 then true
  else
    forall v1, s1' ::
      StepsTo(n-1, (e1, s1), (v1, s1')) ==>
      exists v2, s2' ::
        StepsTo(n-1, (e2, s2), (v2, s2')) &&
        ValRel(n-1, t, v1, v2, s1', s2')
}

predicate ValRel(n: nat, t: Ty, v1: Expr, v2: Expr, s1: Store, s2: Store)
  decreases n, TySize(t)
{
  match t
    case TUnit => v1 == EUnit && v2 == EUnit
    case TBool => v1.EBool? && v2.EBool? && v1.b == v2.b
    case TInt => v1.EInt? && v2.EInt? && v1.n == v2.n
    case TFn(argTy, retTy, _) =>
      v1.ELam? && v2.ELam? &&
      forall arg1, arg2, s1', s2' ::
        ValRel(n, argTy, arg1, arg2, s1', s2') ==>
        ExpRel(n, retTy, 
               Subst(v1.param, arg1, v1.body),
               Subst(v2.param, arg2, v2.body),
               s1', s2')
    case TProd(t1, t2) =>
      v1.EPair? && v2.EPair? &&
      ValRel(n, t1, v1.fst, v2.fst, s1, s2) &&
      ValRel(n, t2, v1.snd, v2.snd, s1, s2)
    case TLabeled(innerTy, level) =>
      // Values at same security level must be related
      ValRel(n, innerTy, v1, v2, s1, s2)
    case TSecret(innerTy) =>
      // Secret values: any two values are related (observational equivalence)
      true
    case _ => false
}
```

---

## 3. LLM Proof Search Strategy

### 3.1 LLM Selection by Target

| Target | Primary LLM | Secondary LLM | Rationale |
|--------|-------------|---------------|-----------|
| **Lean 4** | Claude 3.5 Sonnet / Opus | GPT-4 Turbo | Claude excels at mathematical reasoning; Lean Copilot integration |
| **Dafny** | GPT-4 Turbo | Claude 3.5 Sonnet | Dafny vericoding benchmarks (POPL 2026) show GPT-4 achieves 96% on standard lemmas |
| **Coq (direct)** | DeepSeek-Prover-V2 | Claude 3.5 Opus | Specialized for Coq; Claude as fallback |
| **Proof structure extraction** | Claude 3.5 Opus | - | Best at understanding proof architecture |

### 3.2 Prompt Engineering Templates

#### Template 1: Initial Proof Generation (Lean 4)

```markdown
You are a Lean 4 proof assistant. You will be given a theorem statement translated from Coq.

**Context:** RIINA is a security-typed programming language. The theorem establishes a key property.

**Theorem to prove:**
```lean
{LEAN_THEOREM_STATEMENT}
```

**Available lemmas:**
```lean
{RELEVANT_LEMMAS}
```

**Instructions:**
1. Analyze the theorem structure
2. Identify the proof strategy (induction, case analysis, direct construction)
3. Write the proof using Lean 4 tactics
4. Use `sorry` for subgoals you cannot complete
5. Explain your reasoning in comments

**Output format:**
```lean
theorem {NAME} : {STATEMENT} := by
  -- Strategy: {BRIEF_EXPLANATION}
  {TACTICS}
```
```

#### Template 2: Iterative Refinement (Error Feedback)

```markdown
Your previous proof attempt failed. Here is the error:

**Error message:**
```
{LEAN_OR_DAFNY_ERROR}
```

**Failed proof:**
```lean
{PREVIOUS_ATTEMPT}
```

**Analysis tasks:**
1. Identify the specific subgoal that failed
2. Explain why the tactic/approach didn't work
3. Propose an alternative approach
4. Provide a corrected proof

**Common issues to check:**
- Missing hypothesis in context
- Incorrect type (need explicit coercion?)
- Termination not established (need `decreases` clause?)
- Need additional lemma (search library?)
```

#### Template 3: Proof Decomposition (Large Theorems)

```markdown
The following theorem is too complex for direct proof. Decompose it into lemmas.

**Main theorem:**
```coq
{LARGE_THEOREM}
```

**Instructions:**
1. Identify independent sub-properties
2. Extract each as a standalone lemma
3. Show how lemmas combine to prove main theorem
4. Estimate difficulty of each lemma (Easy/Medium/Hard)

**Output format:**
```
Lemma 1 (Easy): {STATEMENT}
  Purpose: {WHY_NEEDED}
  Proof sketch: {APPROACH}

Lemma 2 (Medium): {STATEMENT}
  Purpose: {WHY_NEEDED}  
  Proof sketch: {APPROACH}

Main theorem proof:
  apply Lemma_1
  apply Lemma_2
  ...
```
```

#### Template 4: Dafny Verification

```markdown
You are a Dafny verification expert. Prove the following lemma.

**Lemma:**
```dafny
{DAFNY_LEMMA}
```

**Preconditions:**
```dafny
requires {PRECONDITIONS}
```

**Postconditions:**
```dafny
ensures {POSTCONDITIONS}
```

**Hints:**
- Available helper functions: {FUNCTION_LIST}
- This corresponds to Coq lemma: {COQ_LEMMA_NAME}
- Key insight from Coq proof: {INSIGHT}

**Instructions:**
1. Add loop invariants if needed
2. Add `decreases` clauses for recursive calls
3. Add `assert` statements to guide the verifier
4. Use `calc` blocks for equational reasoning

**Dafny verification will automatically check your proof. Aim for 0 errors.**
```

### 3.3 Proof Decomposition Strategy

For large theorems like Progress and Preservation:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         Progress Theorem                                 │
│   ∀ Γ e T eff, has_type Γ e T eff → closed e →                          │
│     value e ∨ ∃ e' s', step (e, s) (e', s')                             │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                    ┌───────────────┼───────────────┐
                    │               │               │
                    ▼               ▼               ▼
        ┌───────────────┐ ┌───────────────┐ ┌───────────────┐
        │ Progress_Unit │ │ Progress_Bool │ │ Progress_Int  │
        │    (Easy)     │ │    (Easy)     │ │    (Easy)     │
        └───────────────┘ └───────────────┘ └───────────────┘
                    │
        ┌───────────┴───────────────────────────────┐
        │                                           │
        ▼                                           ▼
┌───────────────────┐                   ┌───────────────────────┐
│   Progress_Lam    │                   │    Progress_App       │
│      (Easy)       │                   │      (Medium)         │
└───────────────────┘                   └───────────────────────┘
                                                    │
                                        ┌───────────┴───────────┐
                                        ▼                       ▼
                            ┌───────────────────┐   ┌───────────────────┐
                            │ Canonical_Forms   │   │  Beta_Reduction   │
                            │     (Medium)      │   │      (Easy)       │
                            └───────────────────┘   └───────────────────┘
```

**Decomposition Rules:**
1. Split by expression constructor (one lemma per case)
2. Extract canonical forms lemmas (if type T, value must have shape X)
3. Extract substitution lemmas separately
4. Group IH applications into helper lemmas

### 3.4 Iterative Refinement Protocol

```python
# Pseudocode for refinement loop
def prove_with_llm(theorem, target_lang, max_attempts=5):
    proof = None
    errors = []
    
    for attempt in range(max_attempts):
        if attempt == 0:
            prompt = INITIAL_PROOF_TEMPLATE.format(theorem=theorem)
        else:
            prompt = REFINEMENT_TEMPLATE.format(
                theorem=theorem,
                previous_attempt=proof,
                errors=errors[-1]
            )
        
        proof = llm_generate(prompt)
        
        # Type check with native tool
        result = verify(proof, target_lang)
        
        if result.success:
            return ProofResult(success=True, proof=proof)
        else:
            errors.append(result.error_message)
            
            # Analyze error type for better feedback
            if "termination" in result.error_message.lower():
                prompt += "\nHINT: Add explicit termination measure"
            elif "type mismatch" in result.error_message.lower():
                prompt += "\nHINT: Check type annotations"
    
    return ProofResult(
        success=False, 
        partial_proof=proof,
        errors=errors,
        manual_hint="Consider decomposing into smaller lemmas"
    )
```

### 3.5 Tool Integration: Lean Copilot

For Lean 4 proofs, integrate with Lean Copilot (Welleck et al., NeurIPS 2023):

```lean
-- Enable Lean Copilot in RIINA Lean project
import LeanCopilot

-- Use copilot to suggest tactics
theorem flowsTo_trans : ∀ l1 l2 l3, l1 ⊑ l2 → l2 ⊑ l3 → l1 ⊑ l3 := by
  intro l1 l2 l3 h12 h23
  suggest  -- Lean Copilot suggests: cases l1 <;> cases l2 <;> cases l3 <;> simp_all

-- Use copilot for search
theorem progress : ... := by
  induction hty with
  | TApp _ _ _ _ ih1 ih2 =>
    search  -- Lean Copilot explores tactic space
```

---

## 4. Validation Back to Coq

### 4.1 Architecture: Proof Structure Extraction

The key insight is that we extract **proof structure** (strategy, key lemmas, case splits) rather than attempting mechanical translation of proof terms.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    Validated Lean 4 / Dafny Proof                       │
└─────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
                    ┌───────────────────────────────┐
                    │   Structure Extraction (LLM)  │
                    │                               │
                    │  • Main proof strategy        │
                    │  • Key lemmas used            │
                    │  • Induction variables        │
                    │  • Case split structure       │
                    │  • Critical invariants        │
                    └───────────────────────────────┘
                                    │
                                    ▼
                    ┌───────────────────────────────┐
                    │    Coq Proof Sketch (.v)      │
                    │                               │
                    │  Theorem foo : ...            │
                    │  Proof.                       │
                    │    (* Strategy: induction *)  │
                    │    induction e.               │
                    │    - (* Case EUnit *)         │
                    │      admit. (* TODO *)        │
                    │    - (* Case EApp *)          │
                    │      (* Key: canonical forms*)│
                    │      admit.                   │
                    │  Admitted.                    │
                    └───────────────────────────────┘
                                    │
                                    ▼
                    ┌───────────────────────────────┐
                    │   Human-Assisted Completion   │
                    │   (Fill in admits)            │
                    └───────────────────────────────┘
                                    │
                                    ▼
                    ┌───────────────────────────────┐
                    │      Coq Type Checker         │
                    │    (FINAL VERIFICATION)       │
                    └───────────────────────────────┘
```

### 4.2 Lean 4 → Coq Translation

#### Extraction Rules

| Lean 4 Construct | Coq Equivalent | Notes |
|------------------|----------------|-------|
| `by tactics` | `Proof. tactics. Qed.` | Tactic mode |
| `intro h` | `intros h` | Hypothesis introduction |
| `cases h` | `destruct h` | Case analysis |
| `induction h with` | `induction h` | Named cases differ |
| `simp` | `simpl; auto` | Coq `simpl` is weaker |
| `rw [h]` | `rewrite h` | Same direction |
| `rw [←h]` | `rewrite <- h` | Reverse rewrite |
| `exact term` | `exact term` | Direct term |
| `apply h` | `apply h` | Same |
| `constructor` | `constructor` | Same |
| `trivial` | `trivial` or `auto` | Same |
| `omega` | `lia` or `omega` | Arithmetic |
| `aesop` | `eauto` + hints | Needs hint DB setup |
| `rcases h with ⟨x, y, hz⟩` | `destruct h as [x [y hz]]` | Nested destruct |
| `use witness` | `exists witness` | Existential intro |

#### Example: Lean → Coq Proof Sketch

**Lean 4 Proof (validated):**
```lean
theorem flowsTo_trans : ∀ l1 l2 l3, l1 ⊑ l2 → l2 ⊑ l3 → l1 ⊑ l3 := by
  intro l1 l2 l3 h12 h23
  cases l1 <;> cases l2 <;> cases l3 <;> simp_all [flowsTo]
```

**Extracted Coq Sketch:**
```coq
Lemma flows_to_trans : forall l1 l2 l3,
  flows_to l1 l2 -> flows_to l2 l3 -> flows_to l1 l3.
Proof.
  (* Strategy: Triple case analysis on l1, l2, l3 *)
  (* Lean proof used: cases <;> simp_all *)
  intros l1 l2 l3 H12 H23.
  destruct l1, l2, l3; simpl in *; auto.
  (* Note: Coq may need explicit contradiction handling *)
  all: try contradiction.
Qed.
```

### 4.3 Dafny → Coq Translation

#### Extraction Rules

| Dafny Construct | Coq Equivalent | Notes |
|-----------------|----------------|-------|
| `requires P` | Hypothesis in context | Add to theorem statement |
| `ensures Q` | Conclusion | Goal to prove |
| `decreases n` | `Fixpoint` structural recursion | May need `Program Fixpoint` |
| `assert P` | `assert (P) by auto` | Intermediate goal |
| `calc { ... }` | `transitivity` / `rewrite` chain | Equational reasoning |
| `forall x :: P(x)` | `forall x, P x` | Universal |
| `exists x :: P(x)` | `exists x, P x` | Existential |
| `ghost var` | (elide) | Proof-only, no runtime |

#### Example: Dafny → Coq Proof Sketch

**Dafny Proof (validated):**
```dafny
lemma Progress(ctx: Context, e: Expr, t: Ty, eff: Effect)
  requires HasType(ctx, e, t, eff)
  requires Closed(e)
  requires ctx == map[]
  ensures Value(e) || exists e', s' :: Step(e, EmptyStore()) == Stepped(e', s')
{
  match e
    case EUnit => assert Value(e);
    case EApp(e1, e2) =>
      Progress(ctx, e1, ...);  // IH on e1
      Progress(ctx, e2, ...);  // IH on e2
      if Value(e1) && Value(e2) {
        assert e1.ELam?;  // Canonical forms
        // Beta reduction applies
      }
}
```

**Extracted Coq Sketch:**
```coq
Theorem progress : forall e T eff,
  has_type empty_ctx e T eff ->
  closed e ->
  value e \/ exists e' s', step (e, empty_store) (e', s').
Proof.
  (* Strategy: Induction on typing derivation *)
  (* Key insight from Dafny: case split on expression, use canonical forms *)
  intros e T eff Hty Hclosed.
  induction Hty.
  - (* EUnit *) left. constructor.
  - (* EApp e1 e2 *)
    right.
    (* IH: e1 makes progress or is value *)
    destruct IHHty1 as [Hval1 | [e1' [s1' Hstep1]]]; auto.
    + (* e1 is value *)
      destruct IHHty2 as [Hval2 | [e2' [s2' Hstep2]]]; auto.
      * (* Both values: use canonical forms *)
        (* Dafny insight: e1 must be lambda *)
        inversion Hval1; subst.
        (* TODO: construct beta-reduction step *)
        admit.
      * (* e2 steps *)
        exists (EApp e1 e2'), s2'. apply ST_App2; auto.
    + (* e1 steps *)
      exists (EApp e1' e2), s1'. apply ST_App1; auto.
Admitted. (* Fill remaining cases *)
```

### 4.4 Handling Foundational Differences

| Issue | Lean 4 | Coq | Resolution |
|-------|--------|-----|------------|
| **Proof irrelevance** | `Prop` is proof-irrelevant | Same | No issue |
| **Impredicativity** | `Prop` is impredicative | Same | No issue |
| **Quotient types** | Built-in `Quotient` | Require `Require Import Setoid` | Use setoids in Coq |
| **Classical logic** | Import `Mathlib.Logic.Classical` | `Require Import Classical` | Match axioms |
| **Functional extensionality** | `funext` in Mathlib | Axiom or use `FunctionalExtensionality` | Add axiom |
| **Axiom of choice** | Available in Mathlib | `Require Import ClassicalChoice` | Match axioms |
| **Decidability** | `Decidable` typeclass | `{dec: forall x, decidable (P x)}` | Add instances |
| **Large elimination** | Allowed from `Prop` to `Type` | Restricted | May need `sumbool` |

**Resolution Protocol:**

```coq
(* RIINA Coq Axiom Baseline *)
(* These axioms match what is available in Lean 4 Mathlib *)

Require Import FunctionalExtensionality.  (* funext *)
Require Import ClassicalChoice.           (* AC *)
Require Import ProofIrrelevance.          (* proof_irrelevance *)

(* Document any Lean proof that uses axioms not in this baseline *)
```

### 4.5 Trusted Computing Base

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    TRUSTED COMPUTING BASE                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                    Coq 8.18.0 Kernel                            │   │
│  │  • Type checker                                                 │   │
│  │  • Conversion checker                                           │   │
│  │  • Universe consistency                                         │   │
│  ├─────────────────────────────────────────────────────────────────┤   │
│  │                    RIINA Coq Axioms                             │   │
│  │  • Functional extensionality (standard)                         │   │
│  │  • Proof irrelevance (standard)                                 │   │
│  │  • Classical logic (for some proofs)                            │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
├─────────────────────────────────────────────────────────────────────────┤
│                       NOT IN TCB                                        │
│                                                                         │
│  • Lean 4 proofs (proof discovery only)                                │
│  • Dafny proofs (proof discovery only)                                 │
│  • LLM outputs (must be verified)                                      │
│  • Translation tools (output checked by Coq)                           │
│  • riina-proof-export (generates unchecked specs)                      │
│  • riina-proof-import (generates sketches, not proofs)                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 5. Tooling Specification

### 5.1 `riina-proof-export`: Coq → Lean 4 / Dafny

**Purpose:** Parse RIINA Coq specifications and generate equivalent Lean 4 and Dafny files.

**Command-line Interface:**
```bash
riina-proof-export [OPTIONS] <INPUT.v> 

OPTIONS:
  --target <lean4|dafny|both>   Target language (default: both)
  --output-dir <DIR>            Output directory (default: ./export/)
  --theorem <NAME>              Export specific theorem only
  --include-deps                Include dependent definitions
  --verbose                     Show translation decisions
  --config <FILE>               Custom translation config

EXAMPLES:
  riina-proof-export RIINATypeSafety.v --target lean4
  riina-proof-export RIINANonInterference.v --target dafny
  riina-proof-export RIINACore.v --theorem progress --include-deps
```

**Architecture:**
```
┌─────────────────────────────────────────────────────────────────────────┐
│                         riina-proof-export                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐     │
│  │   Coq Parser    │───▶│   AST Builder   │───▶│  Type Resolver  │     │
│  │  (SerAPI/coq-lsp)│    │                 │    │                 │     │
│  └─────────────────┘    └─────────────────┘    └─────────────────┘     │
│                                                          │              │
│                              ┌────────────────────────────┘              │
│                              ▼                                          │
│                    ┌─────────────────┐                                  │
│                    │ Dependency Graph │                                  │
│                    │    Builder       │                                  │
│                    └─────────────────┘                                  │
│                              │                                          │
│              ┌───────────────┴───────────────┐                          │
│              ▼                               ▼                          │
│  ┌─────────────────────┐         ┌─────────────────────┐               │
│  │  Lean 4 Emitter     │         │   Dafny Emitter     │               │
│  │  • Inductive → ind  │         │  • Inductive → dt   │               │
│  │  • Fixpoint → def   │         │  • Fixpoint → func  │               │
│  │  • Lemma → theorem  │         │  • Lemma → lemma    │               │
│  └─────────────────────┘         └─────────────────────┘               │
│              │                               │                          │
│              ▼                               ▼                          │
│        output.lean                     output.dfy                       │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

**Output Structure:**
```
export/
├── lean4/
│   ├── RIINABasic.lean           # Types, effects, security levels
│   ├── RIINAExpr.lean            # Expression syntax
│   ├── RIINATyping.lean          # Typing relation
│   ├── RIINASemantics.lean       # Operational semantics
│   ├── RIINATypeSafety.lean      # Progress + Preservation
│   ├── RIINANonInterference.lean # Non-interference theorems
│   └── lakefile.lean             # Build configuration
├── dafny/
│   ├── RIINABasic.dfy
│   ├── RIINAExpr.dfy
│   ├── RIINATyping.dfy
│   ├── RIINASemantics.dfy
│   ├── RIINATypeSafety.dfy
│   ├── RIINANonInterference.dfy
│   └── riina.toml                # Dafny project config
└── export.log                    # Translation decisions and warnings
```

**Implementation Notes:**
- Use SerAPI or coq-lsp for Coq parsing (avoids re-implementing Coq parser)
- Emit `sorry`/`admit` for theorem bodies (proofs generated separately)
- Generate dependency graph to ensure correct import order
- Emit translation warnings for unsupported features

### 5.2 `riina-proof-import`: Lean 4 / Dafny → Coq Sketch

**Purpose:** Extract proof structure from validated Lean 4/Dafny proofs and generate Coq proof sketches.

**Command-line Interface:**
```bash
riina-proof-import [OPTIONS] <INPUT.lean|INPUT.dfy>

OPTIONS:
  --source <lean4|dafny>        Source language (auto-detected from extension)
  --output <FILE.v>             Output Coq file
  --original <FILE.v>           Original Coq theorem (for context)
  --llm <claude|gpt4|local>     LLM for structure extraction (default: claude)
  --detail <minimal|full>       Sketch detail level (default: full)
  --validate                    Check Lean/Dafny proof before import

EXAMPLES:
  riina-proof-import progress_proof.lean --output progress_sketch.v
  riina-proof-import non_interference.dfy --original RIINANonInterference.v
```

**Architecture:**
```
┌─────────────────────────────────────────────────────────────────────────┐
│                         riina-proof-import                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────────────┐                                                    │
│  │ Lean4/Dafny     │                                                    │
│  │ Proof File      │                                                    │
│  └────────┬────────┘                                                    │
│           │                                                             │
│           ▼                                                             │
│  ┌─────────────────┐    ┌─────────────────┐                            │
│  │   Validator     │───▶│ Parse Proof AST │                            │
│  │ (lean4/dafny)   │    │                 │                            │
│  └─────────────────┘    └────────┬────────┘                            │
│                                  │                                      │
│                                  ▼                                      │
│                    ┌─────────────────────────┐                          │
│                    │  LLM Structure Extractor │                          │
│                    │                         │                          │
│                    │  Input: Proof AST       │                          │
│                    │  Output:                │                          │
│                    │    • Main strategy      │                          │
│                    │    • Induction vars     │                          │
│                    │    • Case structure     │                          │
│                    │    • Key lemmas         │                          │
│                    │    • Invariants         │                          │
│                    └────────────┬────────────┘                          │
│                                 │                                       │
│                                 ▼                                       │
│                    ┌─────────────────────────┐                          │
│                    │   Coq Sketch Generator  │                          │
│                    │                         │                          │
│                    │  • Tactic translation   │                          │
│                    │  • Comment annotations  │                          │
│                    │  • admit placement      │                          │
│                    └────────────┬────────────┘                          │
│                                 │                                       │
│                                 ▼                                       │
│                           output.v                                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

**Sketch Output Format:**
```coq
(* Auto-generated Coq proof sketch *)
(* Source: progress_proof.lean (Lean 4) *)
(* Generated: 2026-01-15T10:30:00Z *)
(* Status: SKETCH - requires manual completion *)

(* ═══════════════════════════════════════════════════════════════════════ *)
(* PROOF STRUCTURE EXTRACTED BY LLM                                        *)
(* ═══════════════════════════════════════════════════════════════════════ *)
(* 
   Strategy: Induction on typing derivation (has_type)
   
   Key insights from Lean proof:
   1. Base cases (EUnit, EBool, EInt, ELam) are immediate
   2. EApp case requires:
      - IH on e1 and e2
      - Case split on whether e1, e2 are values
      - Canonical forms lemma: if value has function type, it's a lambda
   3. EIf case requires:
      - IH on condition
      - Canonical forms: bool value is EBool
   
   Required lemmas:
   - canonical_forms_fn : value e -> has_type Γ e (TFn T1 T2 eff) eff' -> 
                          exists x T body, e = ELam x T body
   - canonical_forms_bool : value e -> has_type Γ e TBool eff -> 
                            exists b, e = EBool b
*)

Require Import RIINA.Core.
Require Import RIINA.Typing.
Require Import RIINA.Semantics.

(* Auxiliary lemma suggested by Lean proof *)
Lemma canonical_forms_fn : forall Γ e T1 T2 eff eff',
  value e ->
  has_type Γ e (TFn T1 T2 eff) eff' ->
  exists x T body, e = ELam x T body.
Proof.
  (* TODO: Lean proof used: cases on value, inversion on typing *)
  intros Γ e T1 T2 eff eff' Hval Hty.
  inversion Hval; subst; inversion Hty; subst.
  - (* ELam case *) eauto.
  - (* Other value cases lead to contradiction *)
    admit.
Admitted.

Theorem progress : forall Γ e T eff,
  has_type Γ e T eff ->
  closed e ->
  value e \/ exists e' s', step (e, empty_store) (e', s').
Proof.
  (* === STRATEGY: Induction on typing derivation === *)
  intros Γ e T eff Hty Hclosed.
  induction Hty.
  
  - (* Case: T_Unit *)
    (* Lean: left; exact Value.VUnit *)
    left. constructor.
    
  - (* Case: T_Bool *)
    (* Lean: left; exact Value.VBool b *)
    left. constructor.
    
  - (* Case: T_Int *)
    (* Lean: left; exact Value.VInt n *)
    left. constructor.
    
  - (* Case: T_Lam *)
    (* Lean: left; exact Value.VLam x τ body *)
    left. constructor.
    
  - (* Case: T_App e1 e2 *)
    (* Lean proof structure:
       1. Apply IH to e1 and e2
       2. Case split: e1 value or steps
       3. If e1 value, case split: e2 value or steps
       4. If both values, use canonical_forms_fn
       5. Construct beta reduction step *)
    right.
    destruct IHHty1 as [Hval1 | Hstep1].
    + (* e1 is value *)
      destruct IHHty2 as [Hval2 | Hstep2].
      * (* Both values: canonical forms + beta *)
        pose proof (canonical_forms_fn _ _ _ _ _ _ Hval1 Hty1) as [x [T [body Heq]]].
        subst.
        exists (subst x e2 body), empty_store.
        (* TODO: Apply ST_AppAbs rule *)
        admit.
      * (* e2 steps *)
        destruct Hstep2 as [e2' [s2' Hstep2']].
        exists (EApp e1 e2'), s2'.
        apply ST_App2; auto.
    + (* e1 steps *)
      destruct Hstep1 as [e1' [s1' Hstep1']].
      exists (EApp e1' e2), s1'.
      apply ST_App1; auto.
      
  - (* Case: T_If *)
    (* Lean: case split on condition *)
    admit.
    
  (* ... remaining cases ... *)
  
Admitted. (* SKETCH - 3 admits remaining *)
```

### 5.3 CI/CD Integration

**GitHub Actions Workflow:**

```yaml
# .github/workflows/riina-proof-pipeline.yml
name: RIINA Proof Pipeline

on:
  push:
    paths:
      - 'coq/**/*.v'
      - 'lean4/**/*.lean'
      - 'dafny/**/*.dfy'
  pull_request:
    paths:
      - 'coq/**/*.v'
  workflow_dispatch:
    inputs:
      theorem:
        description: 'Specific theorem to prove'
        required: false

jobs:
  # Stage 1: Export Coq specs to Lean 4 and Dafny
  export-specs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Coq 8.18.0
        uses: coq-community/docker-coq-action@v1
        with:
          coq_version: '8.18.0'
          
      - name: Export to Lean 4
        run: |
          riina-proof-export coq/RIINACore.v --target lean4 --output-dir export/lean4/
          
      - name: Export to Dafny
        run: |
          riina-proof-export coq/RIINACore.v --target dafny --output-dir export/dafny/
          
      - uses: actions/upload-artifact@v4
        with:
          name: exported-specs
          path: export/

  # Stage 2: Generate proofs with LLMs
  llm-proof-generation:
    needs: export-specs
    runs-on: ubuntu-latest
    strategy:
      matrix:
        target: [lean4, dafny]
        theorem: [progress, preservation, non_interference]
    steps:
      - uses: actions/download-artifact@v4
        with:
          name: exported-specs
          
      - name: Setup ${{ matrix.target }}
        run: |
          if [ "${{ matrix.target }}" = "lean4" ]; then
            curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
            lake build
          else
            dotnet tool install --global dafny
          fi
          
      - name: Generate proof with LLM
        env:
          ANTHROPIC_API_KEY: ${{ secrets.ANTHROPIC_API_KEY }}
          OPENAI_API_KEY: ${{ secrets.OPENAI_API_KEY }}
        run: |
          riina-llm-prove \
            --target ${{ matrix.target }} \
            --theorem ${{ matrix.theorem }} \
            --input export/${{ matrix.target }}/ \
            --output proofs/${{ matrix.target }}/ \
            --max-attempts 5
            
      - name: Validate proof
        run: |
          if [ "${{ matrix.target }}" = "lean4" ]; then
            lake build
          else
            dafny verify proofs/dafny/*.dfy
          fi
          
      - uses: actions/upload-artifact@v4
        with:
          name: proofs-${{ matrix.target }}-${{ matrix.theorem }}
          path: proofs/

  # Stage 3: Import proofs back to Coq
  import-to-coq:
    needs: llm-proof-generation
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: actions/download-artifact@v4
        with:
          pattern: proofs-*
          merge-multiple: true
          path: proofs/
          
      - name: Import Lean proofs
        run: |
          for proof in proofs/lean4/*.lean; do
            riina-proof-import "$proof" --output coq/sketches/
          done
          
      - name: Import Dafny proofs
        run: |
          for proof in proofs/dafny/*.dfy; do
            riina-proof-import "$proof" --output coq/sketches/
          done
          
      - name: Attempt Coq compilation
        run: |
          cd coq/sketches/
          make || echo "::warning::Some proofs need manual completion"
          
      - uses: actions/upload-artifact@v4
        with:
          name: coq-sketches
          path: coq/sketches/

  # Stage 4: Final Coq verification (manual trigger)
  final-verification:
    if: github.event_name == 'workflow_dispatch'
    needs: import-to-coq
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Coq 8.18.0
        uses: coq-community/docker-coq-action@v1
        with:
          coq_version: '8.18.0'
          
      - name: Build all Coq proofs
        run: |
          cd coq/
          make
          
      - name: Verify no admits
        run: |
          ! grep -r "Admitted\|admit" coq/*.v || \
            (echo "::error::Found admitted proofs" && exit 1)
```

---

## 6. Timeline and Effort Estimate

### 6.1 Development Phases

| Phase | Duration | Effort | Deliverables |
|-------|----------|--------|--------------|
| **Phase 1: Tooling Foundation** | 6 weeks | 1 FTE | `riina-proof-export` (Coq → Lean 4/Dafny) |
| **Phase 2: LLM Integration** | 4 weeks | 1 FTE | Prompt templates, refinement loop, API integration |
| **Phase 3: Proof Import** | 4 weeks | 1 FTE | `riina-proof-import`, structure extraction |
| **Phase 4: CI/CD Pipeline** | 2 weeks | 0.5 FTE | GitHub Actions workflow, automation |
| **Phase 5: Validation & Tuning** | 4 weeks | 1 FTE | Benchmark suite, parameter tuning |

**Total: ~20 weeks (5 months), ~4.5 FTE-months**

### 6.2 Automation vs. Manual Effort

| Component | Automation Level | Manual Effort Required |
|-----------|------------------|------------------------|
| Coq → Lean 4 type translation | 95% | Edge cases, complex dependent types |
| Coq → Dafny type translation | 90% | Step-indexed relations, termination |
| Lean 4 proof generation (LLM) | 74% | 26% of subgoals |
| Dafny proof generation (LLM) | 82-96% | Complex loop invariants |
| Proof structure extraction | 80% | Novel proof techniques |
| Coq sketch → complete proof | 40-60% | Fill admits, fix tactic issues |
| CI/CD pipeline | 95% | Initial setup, secrets |

### 6.3 Expected Speedup

| Theorem Category | Manual Coq Time | With Pipeline | Speedup |
|------------------|-----------------|---------------|---------|
| Simple induction (Progress base cases) | 2 hours | 15 minutes | 8× |
| Medium induction (Progress app case) | 1 day | 2 hours | 4× |
| Complex (Non-interference) | 1 week | 2 days | 3.5× |
| Very complex (Termination) | 2 weeks | 1 week | 2× |

**Overall expected speedup: 2.5-4× for typical RIINA proofs**

### 6.4 Theorem Categories by LLM Benefit

| Category | LLM Success Rate | Recommendation |
|----------|------------------|----------------|
| **High Benefit** | | |
| Type safety (progress) | 85% | Primary LLM target |
| Type safety (preservation) | 80% | Primary LLM target |
| Canonical forms lemmas | 90% | Auto-generate |
| Substitution lemmas | 75% | LLM with hints |
| **Medium Benefit** | | |
| Non-interference | 60% | LLM for structure, manual finish |
| Effect system soundness | 65% | LLM for routine cases |
| Memory safety | 70% | Similar to type safety |
| **Low Benefit (Manual Preferred)** | | |
| Termination (strong normalization) | 35% | Complex reducibility argument |
| Step-indexed logical relations | 40% | Intricate index manipulation |
| Concurrency proofs | 30% | Requires domain expertise |

### 6.5 Risk Mitigation

| Risk | Mitigation |
|------|------------|
| LLM generates unsound proof structure | All proofs validated in Coq TCB |
| Translation loses semantic nuance | Conservative translation + human review |
| Lean/Dafny proof uses unavailable axiom | Axiom tracking, warn on import |
| LLM API rate limits | Local model fallback, caching |
| Tool breakage on Coq updates | Pin Coq version, test matrix |

---

## 7. References

1. **Lean Copilot** — Welleck et al., "Autoformalization with Large Language Models" (NeurIPS 2023). 74.2% tactic automation rate.

2. **AlphaVerus** — Meta AI Research, "Bootstrapping Verified Code Generation" (2025). 44% success rate on Verus proofs.

3. **SAFE (ICLR 2025)** — "Self-supervised Autoformalization with Foundation Models". Cross-prover generalization.

4. **Dafny Vericoding Benchmarks (POPL 2026)** — Comprehensive benchmarks showing GPT-4 achieves 82-96% on verification conditions.

5. **Martin Kleppmann's Blog (Dec 2025)** — "AI and Formal Verification: A Practitioner's Perspective". Real-world experience report.

6. **Harmonic/Aristotle (IMO 2025)** — DeepMind + Harmonic. Gold medal performance on IMO using Lean 4.

7. **DeepSeek-Prover-V2** — State-of-the-art Coq proof generation (27% → 45% with ensemble).

8. **CoqHammer** — Hammer-style automation for Coq. Integration point for ATP hints.

---

## Appendix A: Full Translation Tables

### A.1 Coq Standard Library → Lean 4 Mathlib

| Coq | Lean 4 |
|-----|--------|
| `Require Import Coq.Lists.List` | `import Mathlib.Data.List.Basic` |
| `Require Import Coq.Arith.Arith` | `import Mathlib.Data.Nat.Basic` |
| `Require Import Coq.Bool.Bool` | `import Mathlib.Data.Bool.Basic` |
| `Require Import Coq.Strings.String` | `import Mathlib.Data.String.Basic` |
| `Require Import Coq.Program.Equality` | `import Mathlib.Logic.Basic` |
| `Require Import Lia` | `import Mathlib.Tactic.Linarith` |

### A.2 Coq Standard Library → Dafny

| Coq | Dafny |
|-----|-------|
| `list A` | `seq<A>` |
| `option A` | Custom `datatype Option<A> = None \| Some(value: A)` |
| `nat` | `nat` |
| `Z` | `int` |
| `bool` | `bool` |
| `string` | `string` |
| `Prop` | `bool` (decidable) or `predicate` |

---

## Appendix B: Example Prompt Session

**User prompt to Claude for Lean 4 proof:**

```
You are proving a theorem about RIINA, a security-typed language.

Theorem (Progress): If an expression e has type T in empty context with effect eff,
and e is closed, then either e is a value or e can take a step.

Here is the Lean 4 statement:

```lean
theorem progress : ∀ e T eff,
    HasType [] e T eff →
    Closed e →
    Value e ∨ ∃ e' s', Step (e, emptyStore) (e', s')
```

Available definitions:
- `HasType : Context → Expr → Ty → Effect → Prop` (typing relation)
- `Value : Expr → Prop` (value predicate)
- `Closed : Expr → Prop` (no free variables)
- `Step : (Expr × Store) → (Expr × Store) → Prop` (small-step)

Prove this theorem using Lean 4 tactics. Use `sorry` for any subgoals you cannot complete.
```

**Claude's response:**

```lean
theorem progress : ∀ e T eff,
    HasType [] e T eff →
    Closed e →
    Value e ∨ ∃ e' s', Step (e, emptyStore) (e', s') := by
  intro e T eff hty hclosed
  -- Induction on typing derivation
  induction hty with
  | TUnit => 
    left; exact Value.VUnit
  | TBool b => 
    left; exact Value.VBool b
  | TInt n => 
    left; exact Value.VInt n
  | TVar x hx =>
    -- Contradiction: closed expression can't have free variable
    simp [Closed, FreeVars] at hclosed
    exact absurd hx hclosed
  | TLam x τ body _ => 
    left; exact Value.VLam x τ body
  | TApp e1 e2 t1 _ hty1 hty2 ih1 ih2 =>
    right
    -- Apply IH to subterms
    have hcl1 : Closed e1 := closed_app_left hclosed
    have hcl2 : Closed e2 := closed_app_right hclosed
    rcases ih1 hcl1 with hv1 | ⟨e1', s1', hstep1⟩
    · -- e1 is value
      rcases ih2 hcl2 with hv2 | ⟨e2', s2', hstep2⟩
      · -- Both values: use canonical forms
        have ⟨x, τ, body, heq⟩ := canonical_forms_fn hv1 hty1
        subst heq
        exact ⟨subst x e2 body, emptyStore, Step.ST_AppAbs hv2⟩
      · -- e2 steps
        exact ⟨Expr.EApp e1 e2', s2', Step.ST_App2 hv1 hstep2⟩
    · -- e1 steps
      exact ⟨Expr.EApp e1' e2, s1', Step.ST_App1 hstep1⟩
  | TIf cond thenE elseE _ hcond hthen helse ihcond _ _ =>
    sorry -- TODO: similar structure
  | _ => sorry
```

---

**Document Version History:**

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2026-01 | Initial specification |

---

*End of Document: RIINA_LLM_PROOF_PIPELINE_v1_0_0*