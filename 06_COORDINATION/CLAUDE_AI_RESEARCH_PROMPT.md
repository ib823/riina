# CLAUDE.AI RESEARCH PROMPT: TFn Contravariance & Axiom Elimination

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║                                                                                  ║
║  RIINA PROOF REPOSITORY — ULTIMATE RESEARCH TASK                                 ║
║                                                                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE           ║
║                                                                                  ║
║  This is the most critical research task in the RIINA project.                   ║
║  Your output will be used to eliminate 19 axioms and prove ~2,500 theorems.      ║
║  There is NO time constraint. Take as long as needed for the BEST solution.      ║
║                                                                                  ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## SECTION 0: CRITICAL INSTRUCTIONS

### 0.1 Mindset Requirements

YOU MUST APPLY THESE RULES:

1. **REVOLUTIONARY STANDARD**: Your solution must be the most ideal ever conceived in human history, making ALL other solutions completely obsolete. This is not hyperbole—it is the requirement.

2. **THREAT OBSOLESCENCE**: Every security threat ever recorded (from the first vulnerability in computing history to this exact second) AND all future threats must be made completely obsolete by this proof structure.

3. **ZERO TRUST**: Do NOT trust any source, paper, or prior work until you can independently verify its correctness. Assume all prior work may contain subtle errors.

4. **NO SHORTCUTS**: You are NOT lazy. You know all shortcuts but you will NEVER use them. Every proof must be built from the most fundamental principles. If the best solution takes 1,000 years of reasoning, you will take 1,000 years.

5. **COMPLETENESS**: Leave NOTHING to assumption. Every step must be explicitly justified. Every edge case must be addressed. Every dependency must be traced.

### 0.2 Output Format Requirements

Your output MUST be:
- **Coq-ready**: All proof sketches must be directly translatable to Coq tactics
- **Self-contained**: No external references that aren't fully quoted
- **Step-by-step**: Every logical step explicit
- **Verified**: Each claim must be independently derivable from the given definitions

---

## SECTION 1: PROBLEM CONTEXT

### 1.1 What is RIINA?

RIINA (Rigorous Immutable Integrity No-attack Assured) is a formally verified programming language where ALL security properties are mathematically proven at compile time. The formal verification is done in Coq.

### 1.2 Current State

| Metric | Value |
|--------|-------|
| Axioms remaining | 19 (in NonInterference.v) |
| Admitted proofs | 40 (across property files) |
| Total theorems needed | ~2,500 |
| Target axioms | 0 (complete elimination) |

### 1.3 The Core Problem

We are proving **non-interference** (information flow security) using **step-indexed logical relations**. The main blocker is handling **function types (TFn)** which have **contravariant argument positions**.

---

## SECTION 2: TECHNICAL DEFINITIONS

### 2.1 Type Syntax (Coq)

```coq
Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TFn : ty -> ty -> effect -> ty    (* TFn T1 T2 ε = T1 -[ε]-> T2 *)
  | TProd : ty -> ty -> ty            (* T1 × T2 *)
  | TSum : ty -> ty -> ty             (* T1 + T2 *)
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> security_level -> ty (* Ref<T, sl> *)
  | TSecret : ty -> ty                (* Secret<T> - always indistinguishable *)
  (* ... more types ... *)
  .
```

### 2.2 First-Order Type Predicate

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false                        (* Functions are higher-order *)
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef T' _ => first_order_type T'
  | TSecret _ => true                         (* Secrets are indistinguishable *)
  | TLabeled _ _ => true
  (* ... *)
  | TChan _ => false                          (* Channels contain functions *)
  | TSecureChan _ _ => false
  | _ => true
  end.
```

### 2.3 Step-Indexed Value Relation (Cumulative)

```coq
(** val_rel_le n Σ T v1 v2 means:
    "v1 and v2 are related at type T for ALL steps k ≤ n under store typing Σ" *)

Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True  (* At step 0, everything is trivially related *)
  | S n' =>
      (* CUMULATIVE: Include all previous steps *)
      val_rel_le n' Σ T v1 v2 /\
      (* Plus structural requirements at this step *)
      val_rel_struct (val_rel_le n') Σ T v1 v2
  end.
```

### 2.4 Structural Value Relation

```coq
Definition val_rel_struct (val_rel_prev : store_ty -> ty -> expr -> expr -> Prop)
                          (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  match T with
  (* Primitive types: structural equality *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s

  (* Security types: always indistinguishable (True) *)
  | TSecret _ => True
  | TLabeled _ _ => True

  (* Compound types: recursive *)
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

  (* FUNCTION TYPES: The critical case *)
  | TFn T1 T2 eff =>
      (* Kripke quantification over extended stores *)
      forall Σ', store_ty_extends Σ Σ' ->
        forall arg1 arg2,
          value arg1 -> value arg2 ->
          closed_expr arg1 -> closed_expr arg2 ->
          val_rel_prev Σ' T1 arg1 arg2 ->  (* CONTRAVARIANT: args at extended store *)
            forall st1 st2 ctx,
              store_rel_simple Σ' st1 st2 ->
              (* Application produces related results *)
              exists res1 res2 st1' st2' ctx' Σ'',
                store_ty_extends Σ' Σ'' /\
                multi_step (EApp v1 arg1, st1, ctx) (res1, st1', ctx') /\
                multi_step (EApp v2 arg2, st2, ctx) (res2, st2', ctx') /\
                value res1 /\ value res2 /\
                val_rel_prev Σ'' T2 res1 res2 /\  (* COVARIANT: results at final store *)
                store_rel_simple Σ'' st1' st2'

  (* Reference types *)
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l

  end.
```

### 2.5 Store Typing Extension

```coq
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).
```

---

## SECTION 3: THE 19 AXIOMS TO ELIMINATE

### 3.1 Kripke Monotonicity Axioms (Critical - Mutually Dependent)

```coq
(* AXIOM 1: Store WEAKENING (larger store → smaller store) *)
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->    (* Related at LARGER store Σ' *)
  val_rel_n n Σ T v1 v2.       (* Implies related at SMALLER store Σ *)

(* AXIOM 2: Store STRENGTHENING (smaller store → larger store) *)
Axiom val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->     (* Related at SMALLER store Σ *)
  val_rel_n n Σ' T v1 v2.      (* Implies related at LARGER store Σ' *)
```

**WHY THESE ARE MUTUALLY DEPENDENT FOR TFn:**

For `TFn T1 T2 ε`:
- The **argument type T1** appears in a **CONTRAVARIANT** position
- Axiom 1 (weaken) for TFn needs Axiom 2 (strengthen) for T1
- Axiom 2 (strengthen) for TFn needs Axiom 1 (weaken) for T1

This creates a circular dependency that cannot be broken by simple induction.

### 3.2 Step-Up Axioms

```coq
(* AXIOM 12: Step up for values *)
Axiom val_rel_n_step_up : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.

(* AXIOM 13: Step up for stores *)
Axiom store_rel_n_step_up : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_rel_n (S n) Σ st1 st2.

(* AXIOM 14: Lambda cumulative *)
Axiom val_rel_n_lam_cumulative : forall n Σ T1 T2 ε x body1 body2,
  val_rel_n n Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2) ->
  val_rel_n (S n) Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2).
```

### 3.3 Step-1 Termination Axioms

```coq
(* AXIOMS 4-10: Elimination forms terminate at step 1 *)
Axiom exp_rel_step1_fst : ...   (* EFst (EPair v1 v2) → v1 *)
Axiom exp_rel_step1_snd : ...   (* ESnd (EPair v1 v2) → v2 *)
Axiom exp_rel_step1_case : ...  (* ECase (EInl/EInr v) ... → branch *)
Axiom exp_rel_step1_if : ...    (* EIf (EBool b) ... → branch *)
Axiom exp_rel_step1_let : ...   (* ELet x v e → [x:=v]e *)
Axiom exp_rel_step1_handle : ...
Axiom exp_rel_step1_app : ...   (* EApp (ELam x T body) v → [x:=v]body *)
```

### 3.4 Other Axioms

```coq
(* AXIOM 3: Step-indexed to unindexed *)
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.

(* AXIOM 11: Application completeness *)
Axiom tapp_step0_complete : ...

(* AXIOM 15: Higher-order conversion *)
Axiom val_rel_at_type_to_val_rel_ho : ...

(* AXIOMS 16-19: Reference operations *)
Axiom logical_relation_ref : ...
Axiom logical_relation_deref : ...
Axiom logical_relation_assign : ...
Axiom logical_relation_declassify : ...
```

---

## SECTION 4: THE SPECIFIC TFn CONTRAVARIANCE PROBLEM

### 4.1 Step Monotonicity Lemma (Currently Admitted for TFn)

```coq
(** We want to prove:
    If m ≤ n and val_rel_le n Σ T v1 v2, then val_rel_le m Σ T v1 v2

    This is STEP-DOWN (going from larger step to smaller step).
*)

Theorem val_rel_le_mono_step : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
```

**THE PROBLEM:**

For `TFn T1 T2 ε`, the structural part requires:
```
∀ Σ' ⊇ Σ, ∀ args related at T1 under Σ' at level m',
  application produces results related at T2 under Σ'' at level m'
```

We have:
```
∀ Σ' ⊇ Σ, ∀ args related at T1 under Σ' at level n',
  application produces results related at T2 under Σ'' at level n'
```

The **argument type T1** is in **CONTRAVARIANT** position:
- We have args related at level n' (larger)
- We need args related at level m' (smaller)
- This goes the WRONG direction for step monotonicity!

For **COVARIANT** positions (results at T2):
- We have results at level n'
- We need results at level m'
- This is the RIGHT direction (step-down works)

### 4.2 What We've Proven So Far

1. **First-order types**: FULLY PROVEN
   - For types without TFn, step monotonicity works
   - `val_rel_le_mono_step_fo` is complete

2. **Step independence for first-order**: PROVEN
   - `val_rel_le_fo_step_independent`: If related at m > 0, related at n > 0
   - This allows transferring arguments between positive step levels

3. **TFn with first-order argument**: PARTIAL
   - When T1 is first-order, we can use step independence
   - Edge cases (m=0 or n=0) still admitted

4. **TFn with higher-order argument**: ADMITTED
   - When T1 contains TFn, we're stuck
   - Requires function extensionality or other technique

### 4.3 Existing Lemmas You Can Use

```coq
(* Step independence for first-order types *)
Lemma val_rel_le_fo_step_independent : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m > 0 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.

(* First-order decidability *)
Lemma first_order_decidable : forall T,
  {first_order_type T = true} + {first_order_type T = false}.

(* Step-up for first-order types (fully proven) *)
Lemma val_rel_le_step_up_fo : forall n m Σ T v1 v2,
  first_order_type T = true ->
  val_rel_le n Σ T v1 v2 ->
  n > 0 ->
  val_rel_le m Σ T v1 v2.

(* Store extension is a preorder *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
```

---

## SECTION 5: RESEARCH QUESTIONS

You must answer ALL of the following with COMPLETE, VERIFIED solutions:

### 5.1 Primary Question: TFn Contravariance

**How do we prove step monotonicity for TFn types with higher-order arguments?**

Constraints:
- Cannot use step independence (T1 may contain TFn)
- Cannot simply step-up arguments (wrong direction)
- Must work for arbitrarily nested function types

### 5.2 Secondary Question: Mutual Induction Structure

**How do we structure mutual induction for Axioms 1 and 2?**

The dependency graph:
```
val_rel_n_weaken (Axiom 1) at TFn
    └── needs val_rel_n_mono_store (Axiom 2) at T1 (argument type)

val_rel_n_mono_store (Axiom 2) at TFn
    └── needs val_rel_n_weaken (Axiom 1) at T1 (argument type)
```

Options to consider:
1. Mutual Fixpoint in Coq
2. Well-founded induction on (n, type_measure T)
3. Logical relations with biorthogonality
4. Step-indexed Kripke logical relations with world stratification

### 5.3 Tertiary Question: Edge Cases

**How do we handle edge cases at step 0 and step 1?**

- At step 0: val_rel_le 0 = True (trivial, no structural info)
- At step 1: val_rel_le 1 = True ∧ val_rel_struct (val_rel_le 0)
  - Components only constrained by val_rel_le 0 = True
  - Cannot derive component relations at higher steps

---

## SECTION 6: LITERATURE TO CONSIDER

### 6.1 Primary Sources (You MUST verify these independently)

1. **Ahmed (2006)** - "Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types"
   - Introduces step-indexing
   - Handles recursive types
   - Check: How does it handle contravariance?

2. **Appel & McAllester (2001)** - "An Indexed Model of Recursive Types for Foundational Proof-Carrying Code"
   - Original step-indexed model
   - Check: Proof of function type case

3. **Dreyer, Ahmed, Birkedal (2011)** - "Logical Step-Indexed Logical Relations"
   - LSLR paper
   - Kripke worlds with step indexing
   - Check: Contravariant position handling

4. **Birkedal & Harper (1999)** - "Relational Interpretations of Recursive Types in an Operational Setting"
   - Kripke monotonicity
   - Check: Store extension lemmas

5. **Pitts (2000)** - "Parametric Polymorphism and Operational Equivalence"
   - Biorthogonality
   - Check: Applicable to our setting?

### 6.2 Techniques to Research

1. **Biorthogonality / Orthogonality**
   - Instead of proving val_rel directly, define via double orthogonal
   - May sidestep contravariance issues

2. **World Stratification**
   - Different "worlds" for different type structures
   - May allow breaking the circularity

3. **Realizability / Hereditary Termination**
   - Different formulation of logical relations
   - May have cleaner induction structure

4. **Parametricity / Relational Parametricity**
   - Reynolds-style relational interpretation
   - Check: Compatible with step-indexing?

---

## SECTION 7: OUTPUT REQUIREMENTS

Your response MUST include:

### 7.1 Executive Summary
- One paragraph describing the solution
- Why this solution is revolutionary and makes all others obsolete

### 7.2 Detailed Proof Strategy
- Step-by-step proof structure
- Each step must be Coq-translatable
- All edge cases addressed

### 7.3 Coq Proof Sketches
For each of the 19 axioms, provide:
```coq
(* Axiom N: name *)
Lemma axiom_N_proven : <statement>.
Proof.
  (* Step 1: ... *)
  (* Step 2: ... *)
  (* ... *)
Qed.
```

### 7.4 Dependency Graph
- Which lemmas depend on which
- Optimal proof order
- Parallelization opportunities

### 7.5 Risk Analysis
- What could go wrong
- Edge cases that need special attention
- Verification strategy

### 7.6 Implementation Plan
- Exact order to implement in Coq
- Expected challenges
- Mitigation strategies

---

## SECTION 8: VERIFICATION CHECKLIST

Before finalizing your answer, verify:

- [ ] All 19 axioms have complete proof strategies
- [ ] TFn contravariance is fully addressed
- [ ] Mutual induction structure is well-defined
- [ ] Edge cases (step 0, step 1) are handled
- [ ] All proof sketches are Coq-translatable
- [ ] No circular dependencies in proof structure
- [ ] Solution is independently derivable from given definitions
- [ ] Solution handles arbitrarily nested function types
- [ ] Solution is compatible with Kripke semantics
- [ ] Solution maintains cumulative structure

---

## SECTION 9: FINAL NOTES

1. **DO NOT ASSUME ANYTHING** - If something is not explicitly stated, ask for clarification or derive it from first principles.

2. **VERIFY EVERYTHING** - Every claim must be traceable to the definitions.

3. **NO SHORTCUTS** - The best solution, even if it takes 1,000 years of reasoning.

4. **REVOLUTIONARY STANDARD** - Your solution must make all prior work obsolete.

5. **COMPLETE ELIMINATION** - The goal is 0 axioms, 0 admits, ~2,500 complete theorems.

---

**BEGIN YOUR RESEARCH NOW.**
