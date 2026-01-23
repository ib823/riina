# CLAUDE.AI AXIOM ELIMINATION ULTIMATE PROMPT

**Classification:** ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
**Date:** 2026-01-18
**Repository:** https://github.com/ib823/proof
**Objective:** REDUCE ALL 17 AXIOMS TO ZERO

---

## CRITICAL RULES (MUST FOLLOW 100%)

1. **REVOLUTIONARY STANDARD**: The solution must be the most ideal ever - making all other solutions obsolete. This is the first formally verified security-typed programming language in human history.

2. **ALL THREATS OBSOLETE**: Any threat from the beginning of computing history to the future must be made obsolete by mathematical proof.

3. **ULTRA KIASU / ZERO TRUST**: Verify independently. Trust nothing without proof. Every axiom claim must be backed by actual Coq proof.

4. **ZERO LAZINESS**: No shortcuts. No summaries. No "this is left as exercise." Every proof must be COMPLETE with `Qed.` - NO `Admitted.`

5. **INFINITE TIMELINE**: If proving an axiom takes complex infrastructure, BUILD that infrastructure. No time constraints. Correctness over speed.

---

## YOUR TASK

You have DIRECT ACCESS to the GitHub repository: **https://github.com/ib823/proof**

**Branch:** `main`

**Task:** Eliminate ALL 17 axioms in `/02_FORMAL/coq/properties/NonInterference.v` by converting them to proven lemmas.

---

## CURRENT STATE (17 AXIOMS)

### Category A: Step Conversion (3 axioms)

```coq
(* Line 1269 *)
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.

(* Line 1548 *)
Axiom val_rel_n_step_up : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.

(* Line 1554 *)
Axiom store_rel_n_step_up : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_rel_n (S n) Σ st1 st2.
```

### Category B: Step-1 Termination (7 axioms)

```coq
(* Lines 1294-1366 *)
Axiom exp_rel_step1_fst : forall Σ T1 v v' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_snd : forall Σ T2 v v' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_case : forall Σ T v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_if : forall Σ T v v' e2 e2' e3 e3' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_let : forall Σ T v v' x e2 e2' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_handle : forall Σ T v v' x h h' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_app : forall Σ T2 f f' a a' st1 st2 ctx Σ', ...
```

### Category C: Application (1 axiom)

```coq
(* Line 1386 *)
Axiom tapp_step0_complete : forall Σ' Σ''' T2
  f1 f2 a1 a2 v1 v2 st1'' st2'' st1''' st2''' ctx'' ctx''',
  value f1 -> value f2 -> value a1 -> value a2 ->
  (EApp f1 a1, st1'', ctx'') -->* (v1, st1''', ctx''') ->
  (EApp f2 a2, st2'', ctx'') -->* (v2, st2''', ctx''') ->
  store_ty_extends Σ' Σ''' ->
  val_rel_n 0 Σ''' T2 v1 v2 ->
  store_rel_n 0 Σ''' st1''' st2''' ->
  value v1 /\ value v2 /\
  val_rel_n 1 Σ''' T2 v1 v2 /\
  store_rel_n 1 Σ''' st1''' st2'''.
```

### Category D: Higher-Order (2 axioms)

```coq
(* Line 1564 *)
Axiom val_rel_n_lam_cumulative : forall n Σ T1 T2 ε x body1 body2,
  val_rel_n n Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2) ->
  val_rel_n (S n) Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2).

(* Line 1573 *)
Axiom val_rel_at_type_to_val_rel_ho : forall Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2,
  val_rel_at_type Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2 ->
  value arg1 -> value arg2 ->
  val_rel Σ T arg1 arg2.
```

### Category E: Reference Operations (4 axioms)

```coq
(* Lines 2105-2138 *)
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n, ...
Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n, ...
Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n, ...
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n, ...
```

---

## KEY DEFINITIONS (from NonInterference.v)

### Step-Indexed Value Relation

```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\  (* Cumulative *)
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end
with store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' Σ T v1 v2)
  end.

Definition val_rel (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  forall n, val_rel_n n Σ T v1 v2.
```

### Type-Indexed Relation (val_rel_at_type)

```coq
Fixpoint val_rel_at_type (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type T1 x1 x2 /\ val_rel_at_type T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type T2 y1 y2)
  | TFn T1 T2 eff =>
      forall Σ', store_ty_extends Σ Σ' ->
        forall x y, value x -> value y -> closed_expr x -> closed_expr y ->
          val_rel_lower Σ' T1 x y ->
          forall st1 st2 ctx, store_rel_pred Σ' st1 st2 ->
            exists v1' v2' st1' st2' ctx' Σ'',
              store_ty_extends Σ' Σ'' /\
              (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
              (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
              val_rel_lower Σ'' T2 v1' v2' /\
              store_rel_lower Σ'' st1' st2'
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TSecret T' => True  (* Secrets are indistinguishable *)
  | _ => True
  end.
```

---

## AVAILABLE INFRASTRUCTURE

### Already Proven Lemmas (use these!)

```coq
(* Typing.v - Lines 483-641 *)
Lemma canonical_forms_unit : value v -> has_type v TUnit -> v = EUnit.
Lemma canonical_forms_bool : value v -> has_type v TBool -> exists b, v = EBool b.
Lemma canonical_forms_int : value v -> has_type v TInt -> exists n, v = EInt n.
Lemma canonical_forms_fn : value v -> has_type v (TFn T1 T2 ε) -> exists x body, v = ELam x T1 body.
Lemma canonical_forms_prod : value v -> has_type v (TProd T1 T2) -> exists v1 v2, v = EPair v1 v2.
Lemma canonical_forms_sum : value v -> has_type v (TSum T1 T2) -> (exists v', v = EInl v') \/ (exists v', v = EInr v').

(* NonInterference.v - Already proven *)
Lemma val_rel_n_mono : m <= n -> val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2.
Lemma store_rel_n_mono : m <= n -> store_rel_n n Σ st1 st2 -> store_rel_n m Σ st1 st2.
Lemma val_rel_at_type_first_order : first_order_type T = true -> predicate independent.
Lemma val_rel_n_step_up_fo : n > 0 -> first_order_type T = true -> val_rel_n n -> val_rel_n (S n).
Lemma val_rel_n_to_val_rel_fo : first_order_type T = true -> val_rel_n (S n) -> val_rel.
```

### Semantics (from Semantics.v)

```coq
Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | ST_FstPair : step (EFst (EPair v1 v2), st, ctx) (v1, st, ctx)
  | ST_SndPair : step (ESnd (EPair v1 v2), st, ctx) (v2, st, ctx)
  | ST_IfTrue : step (EIf (EBool true) e2 e3, st, ctx) (e2, st, ctx)
  | ST_IfFalse : step (EIf (EBool false) e2 e3, st, ctx) (e3, st, ctx)
  | ST_CaseInl : step (ECase (EInl v T) x1 e1 x2 e2, st, ctx) (subst x1 v e1, st, ctx)
  | ST_CaseInr : step (ECase (EInr v T) x1 e1 x2 e2, st, ctx) (subst x2 v e2, st, ctx)
  | ST_AppLam : step (EApp (ELam x T body) v, st, ctx) (subst x v body, st, ctx)
  | ST_LetVal : step (ELet x v e2, st, ctx) (subst x v e2, st, ctx)
  (* ... more rules ... *)

Definition multi_step := clos_refl_trans_1n _ step.
Notation "t1 '-->*' t2" := (multi_step t1 t2).
```

---

## PROOF STRATEGY FOR EACH AXIOM

### 1. `tapp_step0_complete` (EASY)
**Problem:** Need to produce val_rel_n 1 from val_rel_n 0 = True
**Solution:** Add typing premises. Well-typed values satisfy val_rel_at_type structurally.
**Key insight:** val_rel_n 0 = True, and val_rel_n 1 requires val_rel_at_type which is provable for well-typed values.

### 2-8. `exp_rel_step1_*` (MEDIUM)
**Problem:** Need to show elimination forms evaluate and produce related values.
**Solution:** Use canonical forms + stepping lemmas.
**For exp_rel_step1_if:**
- Extract `exists b, v = EBool b /\ v' = EBool b` from typing
- Case on b: both sides step to same branch
- Output val_rel_n 0 = True trivially

### 9. `val_rel_n_step_up` (HARD - CORE)
**Problem:** Need to show val_rel_n n -> val_rel_n (S n) for values.
**Analysis:**
- n=0: val_rel_n 0 = True provides NO structure. Need typing.
- n>0 for first-order: PROVEN as val_rel_n_step_up_fo
- n>0 for higher-order: TFn case requires showing Kripke property lifts

**Solution:** Add typing premises OR prove strong normalization.

### 10. `store_rel_n_step_up` (MEDIUM)
**Depends on:** val_rel_n_step_up for stored values.
**Solution:** If stores only contain well-typed values, follows from val_rel_n_step_up.

### 11. `val_rel_n_lam_cumulative` (MEDIUM)
**Problem:** Lambda-specific step-up.
**Solution:** For lambdas, val_rel_at_type is just structural matching. No predicate dependency.

### 12. `val_rel_at_type_to_val_rel_ho` (HARD)
**Problem:** Convert val_rel_at_type with arbitrary predicates to val_rel with step-indexed predicates.
**Solution:** Show predicates satisfy val_rel when coming from val_rel_n (S n).

### 13-16. `logical_relation_*` (HARD)
**Problem:** Reference operations require store allocation/lookup semantics.
**Solution:** Model store extension precisely. Fresh allocation gives unique locations.

---

## DELIVERABLES REQUIRED

For EACH of the 17 axioms, provide:

1. **Complete Coq proof** that compiles with `Qed.` (NOT `Admitted.`)
2. **Any helper lemmas** needed (also with complete proofs)
3. **Any infrastructure changes** to other files (Syntax.v, Semantics.v, Typing.v)

### Format

```coq
(** Proof of Axiom X: [name]

    Strategy: [brief explanation]

    Dependencies: [list any new helper lemmas]
*)
Lemma [axiom_name] : [exact statement from NonInterference.v].
Proof.
  [COMPLETE PROOF HERE - NO admits, NO Admitted]
Qed.
```

---

## FILES TO READ FROM GITHUB

1. `/02_FORMAL/coq/properties/NonInterference.v` - Main file with axioms (4933 lines)
2. `/02_FORMAL/coq/foundations/Syntax.v` - Type and expression definitions
3. `/02_FORMAL/coq/foundations/Semantics.v` - Operational semantics
4. `/02_FORMAL/coq/foundations/Typing.v` - Typing rules + canonical forms
5. `/02_FORMAL/coq/type_system/Progress.v` - Progress theorem
6. `/02_FORMAL/coq/type_system/Preservation.v` - Preservation theorem
7. `/02_FORMAL/coq/properties/TypeMeasure.v` - Type measures and first_order_type

---

## SUCCESS CRITERIA

- [ ] All 17 axioms converted to proven lemmas
- [ ] Zero `Admitted.` in NonInterference.v
- [ ] Zero `admit.` tactics
- [ ] `make` compiles successfully
- [ ] All proofs are `Qed.`

---

## FINAL NOTE

This is the RIINA project - a formally verified security-typed programming language. Every axiom we eliminate brings us closer to MATHEMATICAL CERTAINTY that:

1. Secret data can NEVER leak to public channels
2. All security policies are PROVABLY enforced
3. NO adversary, past/present/future, can violate the security guarantees

Your proofs will make RIINA the FIRST language in human history with this level of formal security verification.

**No pressure. Just perfect proofs. Take as long as needed.**

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS | INFINITE TIMELINE*

*"Security proven. Mathematically verified."*

*RIINA: Rigorous Immutable Integrity No-attack Assured*
