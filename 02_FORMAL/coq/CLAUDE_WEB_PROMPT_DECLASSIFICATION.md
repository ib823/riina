# PROMPT: Fix 2 Admits in Declassification.v

You are working on a Coq 8.18+ (also compiles with Rocq 9.1) formal verification codebase called RIINA. You must fix the 2 `Admitted` statements in the file `properties/Declassification.v`.

**CRITICAL RULES:**
- Output ONLY the replacement proof bodies for the 2 admits
- Every `Admitted.` must become `Qed.` with a complete proof
- Do NOT change any existing `Qed.` proofs — they already compile
- Do NOT add new axioms
- Do NOT change lemma signatures
- Use ONLY the available infrastructure listed below
- If a lemma is UNSOUND (cannot be proven), convert it to a justified axiom with clear documentation

---

## THE COMPLETE FILE (properties/Declassification.v) — 269 lines

```coq
(** * Declassification.v

    RIINA Declassification Semantic Typing Proof

    This file proves the semantic typing lemma for declassification:
    - logical_relation_declassify (Axiom 19): Declassification is sound

    PHASE 5: Store Semantics & Semantic Typing Axioms
    TARGET: Eliminate axiom 19 - 1 admit → 0 admits
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.
Require Import Arith.PeanoNat.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.type_system.Preservation.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.LexOrder.
Require Import RIINA.properties.FirstOrderComplete.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.CumulativeMonotone.
Require Import RIINA.properties.KripkeProperties.
Require Import RIINA.properties.StoreRelation.

Import ListNotations.

(** Secrets are trivially related at any step *)
Lemma val_rel_le_secret_trivial : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_le n Σ (TSecret T) v1 v2.
Proof.
  intros n Σ T v1 v2 Hv1 Hv2 Hc1 Hc2.
  apply val_rel_le_secret_always; auto.
Qed.

(** Declassification evaluates to the unwrapped value *)
Lemma declassify_eval : forall v p st ctx,
  value v ->
  declass_ok (EClassify v) p ->
  multi_step (EDeclassify (EClassify v) p, st, ctx) (v, st, ctx).
Proof.
  intros v p st ctx Hv Hok.
  apply MS_Step with (cfg2 := (v, st, ctx)).
  - apply ST_DeclassifyValue; auto.
  - apply MS_Refl.
Qed.

(** Core declassification lemma — ALREADY PROVEN *)
Lemma logical_relation_declassify_proven : forall n Σ T v1 v2 p st1 st2 ctx,
  val_rel_le n Σ (TSecret T) (EClassify v1) (EClassify v2) ->
  store_rel_simple Σ st1 st2 ->
  value v1 -> value v2 ->
  declass_ok (EClassify v1) p -> declass_ok (EClassify v2) p ->
  multi_step (EDeclassify (EClassify v1) p, st1, ctx) (v1, st1, ctx) /\
  multi_step (EDeclassify (EClassify v2) p, st2, ctx) (v2, st2, ctx) /\
  store_rel_simple Σ st1 st2.
Proof.
  intros n Σ T v1 v2 p st1 st2 ctx Hrel Hst Hval1 Hval2 Hok1 Hok2.
  repeat split.
  - apply declassify_eval; auto.
  - apply declassify_eval; auto.
  - exact Hst.
Qed.

(** Helper: Evaluation is deterministic — ALREADY PROVEN *)
Lemma eval_deterministic : forall e st ctx v1 st1 v2 st2,
  multi_step (e, st, ctx) (v1, st1, ctx) ->
  multi_step (e, st, ctx) (v2, st2, ctx) ->
  value v1 -> value v2 ->
  v1 = v2 /\ st1 = st2.
Proof.
  (* ... full proof omitted, already Qed ... *)
Admitted. (* PLACEHOLDER — this is actually Qed in the real file *)

(** ===== ADMIT 1 (line 194) ===== *)
Lemma same_expr_related_stores_related_results : forall n Σ T e st1 st2 ctx v1 v2 st1' st2',
  store_rel_le n Σ st1 st2 ->
  multi_step (e, st1, ctx) (v1, st1', ctx) ->
  multi_step (e, st2, ctx) (v2, st2', ctx) ->
  value v1 -> value v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  admit.
Admitted.

(** ===== ADMIT 2 (line 217) ===== *)
Lemma exp_rel_le_declassify : forall n Σ T e1 e2 p st1 st2 ctx,
  exp_rel_le n Σ (TSecret T) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  e1 = e2 ->
  exp_rel_le n Σ T (EDeclassify e1 p) (EDeclassify e2 p) st1 st2 ctx.
Proof.
  admit.
Admitted.

(** Declassification is safe when policy allows — ALREADY PROVEN *)
Lemma declassify_policy_safe : forall Γ Σ Δ e T eff1 eff2 p,
  has_type Γ Σ Δ e (TSecret T) eff1 ->
  has_type Γ Σ Δ p (TProof (TSecret T)) eff2 ->
  declass_ok e p ->
  has_type Γ Σ Δ (EDeclassify e p) T (effect_join eff1 eff2).
Proof.
  intros Γ Σ Δ e T eff1 eff2 p Htype_e Htype_p Hok.
  apply T_Declassify; assumption.
Qed.

Theorem declassification_zero_admits : True.
Proof. exact I. Qed.
```

---

## AVAILABLE INFRASTRUCTURE

### From Semantics.v — Step Rules for Declassify

```coq
(* EDeclassify steps *)
| ST_Declassify1 : forall e e' p st st' ctx ctx',
    (e, st, ctx) --> (e', st', ctx') ->
    (EDeclassify e p, st, ctx) --> (EDeclassify e' p, st', ctx')
| ST_Declassify2 : forall v e' p st st' ctx ctx',
    value v ->
    (p, st, ctx) --> (e', st', ctx') ->
    (EDeclassify v e', st, ctx) --> (EDeclassify v e', st', ctx')
| ST_DeclassifyValue : forall v p st ctx,
    value (EClassify v) ->
    declass_ok (EClassify v) p ->
    (EDeclassify (EClassify v) p, st, ctx) --> (v, st, ctx)
```

### From Semantics.v — Multi-step and Determinism

```coq
Inductive multi_step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.

(* PROVEN *)
Lemma value_not_step : forall v st ctx cfg, value v -> ~ ((v, st, ctx) --> cfg).
Theorem step_deterministic_cfg : forall cfg cfg1 cfg2, step cfg cfg1 -> step cfg cfg2 -> cfg1 = cfg2.
```

### From Semantics.v — Values

```coq
Inductive value : expr -> Prop :=
  | VUnit   : value EUnit
  | VBool   : forall b, value (EBool b)
  | VInt    : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc    : forall l, value (ELoc l)
  | VLam    : forall x T e, value (ELam x T e)
  | VPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl    : forall v T, value v -> value (EInl v T)
  | VInr    : forall v T, value v -> value (EInr v T)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve  : forall v, value v -> value (EProve v).
```

**IMPORTANT**: `EDeclassify`, `EDeref`, `ERef`, `EAssign` are NOT value constructors.

### From CumulativeRelation.v — exp_rel_le definition

```coq
Definition exp_rel_le (n : nat) (Σ : store_ty) (T : ty)
    (e1 e2 : expr) (st1 st2 : store) (ctx : effect_ctx) : Prop :=
  forall k v1 v2 st1' st2' ctx',
    k <= n ->
    multi_step (e1, st1, ctx) (v1, st1', ctx') ->
    multi_step (e2, st2, ctx) (v2, st2', ctx') ->
    value v1 -> value v2 ->
    exists Σ',
      store_ty_extends Σ Σ' /\
      val_rel_le k Σ' T v1 v2 /\
      store_rel_simple Σ' st1' st2'.
```

### From CumulativeRelation.v — val_rel_le for secrets

```coq
(* val_rel_le for TSecret T is ALWAYS True for any closed values *)
Lemma val_rel_le_secret_always : forall n Σ T v1 v2,
  value v1 -> value v2 -> closed_expr v1 -> closed_expr v2 ->
  val_rel_le n Σ (TSecret T) v1 v2.

(* val_rel_le at step > 0 implies value, closedness *)
Lemma val_rel_le_value : forall k Σ T v1 v2,
  k > 0 -> val_rel_le k Σ T v1 v2 -> value v1 /\ value v2.
Lemma val_rel_le_closed : forall k Σ T v1 v2,
  k > 0 -> val_rel_le k Σ T v1 v2 -> closed_expr v1 /\ closed_expr v2.

(* Store typing *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
```

### From StoreRelation.v

```coq
Lemma store_rel_le_to_simple : forall n Σ st1 st2,
  store_rel_le n Σ st1 st2 -> store_rel_simple Σ st1 st2.
```

### Multi-step composition lemma from Semantics.v

```coq
Lemma multi_step_declassify1 : forall e e' p st st' ctx ctx',
  multi_step (e, st, ctx) (e', st', ctx') ->
  multi_step (EDeclassify e p, st, ctx) (EDeclassify e' p, st', ctx').
```

---

## ANALYSIS AND PROOF STRATEGY

### Admit 1: same_expr_related_stores_related_results

**THIS LEMMA IS UNSOUND AS STATED.** It claims that evaluating the SAME expression under DIFFERENT stores gives related values at ANY type T. This is false: if `e = EDeref (ELoc 0)` and st1 maps loc 0 to `EInt 1` while st2 maps loc 0 to `EInt 2`, then `v1 = EInt 1` and `v2 = EInt 2`, and they are NOT related at `TInt` (which requires equality).

**RECOMMENDATION**: Convert to a justified axiom with documentation, OR remove it entirely if `exp_rel_le_declassify` can be proven without it.

### Admit 2: exp_rel_le_declassify

**Proof strategy**:
1. `subst e2` (from `e1 = e2`).
2. Unfold `exp_rel_le`. Intros `k v1 v2 st1' st2' ctx' Hk Heval1 Heval2 Hval1 Hval2`.
3. We have `(EDeclassify e1 p, st1, ctx) -->* (v1, st1', ctx')` and same for st2.
4. The hypothesis `H : exp_rel_le n Σ (TSecret T) e1 e1 st1 st2 ctx` relates evaluations of `e1` under both stores.
5. By multi_step inversion on declassify: `e1` evaluates to some `EClassify w1` under st1 (with store st_mid1), then `EDeclassify (EClassify w1) p` steps to `w1`. Similarly for st2 → `w2`.
6. Apply H to get `val_rel_le k Σ' (TSecret T) (EClassify w1) (EClassify w2)` and `store_rel_simple Σ' st_mid1 st_mid2`.
7. Since declassify doesn't modify the store: `st1' = st_mid1` and `st2' = st_mid2`.
8. For the result: we need `val_rel_le k Σ' T w1 w2`. Since `e1 = e1` (same expression under different stores), this is the hard part.
9. **Key insight**: For TSecret values, `val_rel_le k Σ' (TSecret T) (EClassify w1) (EClassify w2)` is trivially True — it does NOT relate w1 and w2 at T. After declassification, we need `val_rel_le k Σ' T w1 w2`, which is NOT guaranteed.
10. **This requires an additional assumption**: either e1 is pure (doesn't read the store), or w1 = w2. Since the lemma has `e1 = e2`, the intent is that the expression is the same, but under different stores it can produce different results.

**CONCLUSION**: `exp_rel_le_declassify` as stated also may not be provable without additional infrastructure (purity analysis). If it cannot be proven, convert both admits to justified axioms.

**PRACTICAL APPROACH**: If the proof IS possible, it would require showing that declassification's soundness relies on the policy system guaranteeing that the declassified expression produces "equivalent enough" results under related stores. This is the fundamental theorem of information flow. Convert to justified axiom with clear documentation.

---

## OUTPUT FORMAT

For each admit, provide either:
1. A complete proof ending in `Qed.`
2. OR a justified axiom conversion with documentation explaining why it cannot be proven

Provide ONLY the replacement for the 2 admit blocks (lines 194-204 and lines 217-225).
