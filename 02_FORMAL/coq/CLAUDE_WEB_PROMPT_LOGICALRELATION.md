# PROMPT: Fix Admits and Axioms in NonInterference_v2_LogicalRelation.v

You are working on a Coq 8.18+ (also compiles with Rocq 9.1) formal verification codebase called RIINA. This file has **5 Axioms** and **12 Admits**. Fix as many as possible.

**CRITICAL RULES:**
- Output ONLY the replacement for each axiom/admit you fix
- Convert `Axiom` to `Lemma` + proof + `Qed.` if possible
- Convert `Admitted.` to `Qed.` with complete proof if possible
- If NOT provable, add `(* JUSTIFIED AXIOM/ADMIT: ... *)` documentation
- Do NOT change existing `Qed.` proofs
- Do NOT add new axioms
- Use ONLY the available infrastructure listed below

---

## FILE OVERVIEW

The file is 3772 lines. It builds the fundamental theorem of logical relations for RIINA's non-interference proof using step-indexed relations from `NonInterference_v2.v`.

**Imports:**
```coq
Require Export RIINA.properties.NonInterference_v2.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Preservation.
Require Import RIINA.properties.NonInterference_v2_Monotone.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.TypeMeasure.
```

---

## THE 5 AXIOMS

### Axioms 1-3 (lines 675, 685, 695): Reference operations

```coq
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e T ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).

Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e (TRef T l) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).

Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n,
  has_type Γ Σ Δ e1 (TRef T l) ε1 ->
  has_type Γ Σ Δ e2 T ε2 ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ TUnit (subst_rho rho1 (EAssign e1 e2)) (subst_rho rho2 (EAssign e1 e2)).
```

**Status**: These need a bridge from `exp_rel_n` (NonInterference_v2.v) to `exp_rel_le` (CumulativeRelation.v) where proofs exist in ReferenceOps.v. Without that bridge, keep as justified axioms.

### Axiom 4 (line 708): Declassification

```coq
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n,
  has_type Γ Σ Δ e (TSecret T) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeclassify e p)) (subst_rho rho2 (EDeclassify e p)).
```

**Status**: Same bridge problem. Keep as justified axiom.

### Axiom 5 (line 1675): val_rel_n_to_val_rel

```coq
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```

**Where** `val_rel Σ T v1 v2 := forall n, val_rel_n n Σ T v1 v2`.

**Analysis**: This says "related at some step → related at all steps". For first-order types, this is already proven (`val_rel_n_to_val_rel_fo`). For higher-order types, this requires the step-up lemma which is itself partially admitted. Keep as justified axiom.

---

## THE 12 ADMITS — Grouped by Pattern

### Pattern A: HO typing extraction (9 admits)

These all follow the same pattern. When building `val_rel_n (S n')`, there's a typing conjunct:
```coq
(if first_order_type T then True
 else has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure)
```
For FO types, this is `True` (trivial). For HO types, we need typing evidence.

**Key insight**: `val_rel_n (S n') Σ T v1 v2` at the S-case ALREADY CONTAINS typing info (it's a conjunct). Use `val_rel_n_S_unfold` to extract it.

The affected lemmas and their admits:

#### 1. val_rel_n_prod (line 1832)
```coq
Lemma val_rel_n_prod : forall n Σ T1 T2 v1 v2 v1' v2',
  val_rel_n n Σ T1 v1 v1' ->
  val_rel_n n Σ T2 v2 v2' ->
  val_rel_n n Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
```
Admit at line 1832: HO case needs typing for pair from components.

#### 2-3. val_rel_n_from_prod_fst (lines 1877, 1880)
```coq
Lemma val_rel_n_from_prod_fst : forall n Σ T1 T2 a1 b1 a2 b2,
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) (EPair a1 b1) (EPair a2 b2) ->
  val_rel_n n Σ T1 a1 a2.
```
Admits: HO typing extraction (line 1877) and n = S(S n'') case (line 1880).

#### 4-5. val_rel_n_from_prod_snd (lines 1921, 1924)
Same pattern as fst but for second component.

#### 6-7. val_rel_n_sum_inl (line 1971), val_rel_n_sum_inr (line 2019)
```coq
Lemma val_rel_n_sum_inl : forall n Σ T1 T2 v1 v2,
  val_rel_n n Σ T1 v1 v2 ->
  val_rel_n n Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
```
Admit: HO typing for sum wrapper.

#### 8. val_rel_n_from_sum_inl (line 2067)
```coq
Lemma val_rel_n_from_sum_inl : forall n Σ T1 T2 a1 a2,
  n > 0 ->
  val_rel_n n Σ (TSum T1 T2) (EInl a1 T2) (EInl a2 T2) ->
  val_rel_n n Σ T1 a1 a2.
```

#### 9. val_rel_n_from_sum_inr (line 2077)
Same pattern for Inr.

### Pattern B: Secret/Proof type construction (2 admits)

#### 10. val_rel_n_classify (line 2200)
```coq
Lemma val_rel_n_classify : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ (TSecret T) (EClassify v1) (EClassify v2).
```

#### 11. val_rel_n_prove (line 2210)
```coq
Lemma val_rel_n_prove : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ (TProof T) (EProve v1) (EProve v2).
```

### Pattern C: Large proof engineering (2 admits)

#### 12. step_up_and_fundamental_mutual (lines 2351, 2522)
Large mutual induction proof. Admitted at line 2351 (beta-reduction case needs val_rel_n 0 for substituted body) and line 2522 (fundamental theorem at S n' — the entire inductive case).

#### 13. logical_relation (line 3691)
```coq
(* admitted with comment: "Remaining cases admitted for v2 migration" *)
```
The fundamental theorem proof is incomplete — missing some expression form cases.

---

## KEY DEFINITIONS

### val_rel_n (from NonInterference_v2.v)

```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 =>
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T
       then val_rel_at_type_fo T v1 v2
       else has_type nil Σ Public v1 T EffectPure /\
            has_type nil Σ Public v2 T EffectPure)
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T
       then True
       else has_type nil Σ Public v1 T EffectPure /\
            has_type nil Σ Public v2 T EffectPure) /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end.

Lemma val_rel_n_S_unfold : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 =
  (val_rel_n n Σ T v1 v2 /\ value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T then True
    else has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure) /\
   val_rel_at_type Σ (store_rel_n n) (val_rel_n n) (store_rel_n n) T v1 v2).

Lemma val_rel_n_0_unfold : forall Σ T v1 v2,
  val_rel_n 0 Σ T v1 v2 =
  (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T
    then val_rel_at_type_fo T v1 v2
    else has_type nil Σ Public v1 T EffectPure /\
         has_type nil Σ Public v2 T EffectPure)).
```

### first_order_type (from NonInterference_v2.v)

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TCapability _ | TCapabilityFull _ => true
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TFn _ _ _ => false
  | TRef _ _ => false
  | TSecret _ => false
  | TLabeled _ _ => false
  | TProof _ => false
  | TTainted _ => false
  | TSanitized _ => false
  | TChan _ => false
  | TSecureChan _ => false
  | TConstantTime _ => false
  | TZeroizing _ => false
  end.
```

### val_rel_at_type_fo (excerpt)

```coq
(* For TProd: *)
val_rel_at_type_fo (TProd T1 T2) v1 v2 =
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2

(* For TSum: *)
val_rel_at_type_fo (TSum T1 T2) v1 v2 =
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_at_type_fo T1 a1 a2)
  \/ (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_at_type_fo T2 b1 b2)

(* For TSecret, TProof: val_rel_at_type is True *)
```

### Proven helpers available

```coq
Lemma val_rel_n_closed : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 -> closed_expr v1 /\ closed_expr v2.

Lemma val_rel_n_value : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 -> value v1 /\ value v2.

Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n -> val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2.

Lemma val_rel_n_step_up_fo : forall T Σ v1 v2 n,
  first_order_type T = true ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.

Lemma val_rel_at_type_fo_equiv : forall T Σ sr vr sr' v1 v2,
  first_order_type T = true ->
  (val_rel_at_type Σ sr vr sr' T v1 v2 <-> val_rel_at_type_fo T v1 v2).

Lemma value_pair_inv : forall v1 v2,
  value (EPair v1 v2) -> value v1 /\ value v2.

Lemma closed_expr_pair_inv : forall v1 v2,
  closed_expr (EPair v1 v2) -> closed_expr v1 /\ closed_expr v2.

Lemma closed_expr_inl : forall v T, closed_expr v -> closed_expr (EInl v T).
Lemma closed_expr_inr : forall v T, closed_expr v -> closed_expr (EInr v T).
Lemma closed_expr_pair : forall v1 v2, closed_expr v1 -> closed_expr v2 -> closed_expr (EPair v1 v2).
Lemma closed_expr_classify : forall v, closed_expr v -> closed_expr (EClassify v).
Lemma closed_expr_prove : forall v, closed_expr v -> closed_expr (EProve v).
```

---

## PROOF STRATEGY FOR PATTERN A (HO typing extraction)

The key technique for all Pattern A admits:

For `val_rel_n (S n') Σ T v1 v2`, the S-case contains:
```
(if first_order_type T then True
 else has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure)
```

So when `first_order_type T = false`, we can extract typing from the hypothesis.

**For val_rel_n_classify / val_rel_n_prove**: These build `val_rel_n` for `TSecret T` / `TProof T` where `first_order_type` is always `false`. The HO typing branch requires `has_type nil Σ Public (EClassify v1) (TSecret T) EffectPure`. This needs a typing rule `T_Classify` that constructs typing for `EClassify`. Check if this typing rule exists.

**For val_rel_n_prod at HO**: Need to construct `has_type nil Σ Public (EPair v1 v2) (TProd T1 T2) EffectPure` from typing of components. Requires `T_Pair` typing rule.

**For val_rel_n_from_prod_fst at n = S(S n'')**: The n=1 case is handled. For n=S(S n''), use the IH or extract from the cumulative part `val_rel_n n' Σ (TProd T1 T2) ...` which is part of the S-case.

---

## OUTPUT FORMAT

For each fixable admit/axiom, provide the complete replacement proof. For unfixable ones, add `(* JUSTIFIED: ... *)` documentation. Group your output by axiom/admit number.
