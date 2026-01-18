# CLAUDE AI DELEGATION PROMPT — RIINA FORMAL PROOFS

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  RIINA — Rigorous Immutable Integrity No-attack Assured                          ║
║  FORMAL PROOF DELEGATION PROMPT FOR CLAUDE AI (WEB)                              ║
║                                                                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE           ║
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
Coq Version: 8.18.0
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

---

## SECTION 3: CUMULATIVE VALUE RELATION (THE CORE)

### 3.1 Key Insight

The value relation is CUMULATIVE: `val_rel_le n Σ T v1 v2` means v1 and v2 are related at type T for ALL steps up to and including n.

### 3.2 Definition

```coq
Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True  (* At step 0, everything is trivially related *)
  | S n' =>
      (* Must be related at all previous steps *)
      val_rel_le n' Σ T v1 v2 /\
      (* At step S n', must also satisfy structural requirements *)
      (value v1 /\ value v2 /\
       closed_expr v1 /\ closed_expr v2 /\
       match T with
       (* Primitive types - equality *)
       | TUnit => v1 = EUnit /\ v2 = EUnit
       | TBool => exists b, v1 = EBool b /\ v2 = EBool b
       | TInt => exists i, v1 = EInt i /\ v2 = EInt i
       | TString => exists s, v1 = EString s /\ v2 = EString s
       | TBytes => v1 = v2
       (* Security types - indistinguishable (always True) *)
       | TSecret _ => True
       | TLabeled _ _ => True
       | TTainted _ _ => True
       | TSanitized _ _ => True
       | TCapability _ => True
       | TCapabilityFull _ => True
       | TProof _ => True
       | TChan _ => True
       | TSecureChan _ _ => True
       | TConstantTime _ => True
       | TZeroizing _ => True
       | TList _ => True
       | TOption _ => True
       (* Reference types - same location *)
       | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
       (* Product types - component-wise *)
       | TProd T1 T2 =>
           exists x1 y1 x2 y2,
             v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
             val_rel_le n' Σ T1 x1 x2 /\
             val_rel_le n' Σ T2 y1 y2
       (* Sum types - matching constructor *)
       | TSum T1 T2 =>
           (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                          val_rel_le n' Σ T1 x1 x2) \/
           (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                          val_rel_le n' Σ T2 y1 y2)
       (* Function types - Kripke quantification *)
       | TFn T1 T2 eff =>
           forall Σ', store_ty_extends Σ Σ' ->
             forall x y,
               value x -> value y -> closed_expr x -> closed_expr y ->
               val_rel_le n' Σ' T1 x y ->
                 forall st1 st2 ctx,
                   store_rel_simple Σ' st1 st2 ->
                   exists v1' v2' st1' st2' ctx' Σ'',
                     store_ty_extends Σ' Σ'' /\
                     (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
                     (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
                     value v1' /\ value v2' /\
                     val_rel_le n' Σ'' T2 v1' v2' /\
                     store_rel_simple Σ'' st1' st2'
       end)
  end.
```

---

## SECTION 4: YOUR TASK

**SPECIFIC TASK:**
[INSERT YOUR SPECIFIC TASK HERE]

**OUTPUT REQUIREMENTS:**

1. **Coq Syntax**: Output MUST be valid Coq 8.18.0 syntax
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

## SECTION 5: EXAMPLE OUTPUT FORMAT

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

## SECTION 6: CRITICAL REMINDERS

1. **DO NOT SKIP STEPS** — Every case must be handled explicitly
2. **DO NOT USE `admit`** — Every proof must be complete
3. **DO NOT GUESS** — If unsure, state assumptions explicitly
4. **VERIFY TERMINATION** — Recursive definitions must terminate
5. **CHECK BULLET STRUCTURE** — Coq is strict about bullet nesting

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
