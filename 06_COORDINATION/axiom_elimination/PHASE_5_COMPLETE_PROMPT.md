# PHASE 5: Store Semantics & Semantic Typing Axioms - COMPLETE PROMPT

**Mode:** ULTRA KIASU | ZERO TRUST | QED ETERNUM
**Target:** 12 Admits across 5 files
**Context:** Self-contained type systems - these files use different relation definitions than NonInterference_v2.v

---

## CRITICAL CONTEXT

### Available Proven Theorems (from Phase 1)
```coq
(* From ReducibilityFull_FINAL.v - PROVEN *)
Theorem well_typed_SN : forall Σ pc e T ε,
  has_type nil Σ pc e T ε -> SN_expr e.
Proof. (* ... *) Qed.

(* Standard axioms allowed *)
Axiom store_wf_global : forall st l v,
  store_lookup l st = Some v -> value v.

Axiom lambda_body_SN : forall Γ Σ pc x T1 T2 eff body ρ v,
  has_type Γ Σ pc (ELam x T1 body) (TFn T1 T2 eff) EffectPure ->
  env_reducible Γ ρ ->
  (forall y, lookup y Γ = None -> ρ y = EVar y) ->
  value v ->
  SN_expr v ->
  SN_expr ([x := v] (subst_env (extend_rho ρ x (EVar x)) body)).
```

### Proof Strategy Context
- Files use `val_rel_le` and `exp_rel_le` from CumulativeRelation.v
- These have proper Kripke monotonicity structure (unlike val_rel_n)
- First-order types are fully proven
- Higher-order types (TFn) require typing preconditions

---

## FILE 1: Declassification.v (243 lines, 1 admit)

### ADMIT TO PROVE (line 207)
```coq
Lemma exp_rel_le_declassify : forall n Σ T e1 e2 p st1 st2 ctx,
  exp_rel_le n Σ (TSecret T) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  (* For syntactically equal expressions, declassify produces related results *)
  e1 = e2 ->
  exp_rel_le n Σ T (EDeclassify e1 p) (EDeclassify e2 p) st1 st2 ctx.
```

**PROOF STRATEGY:**
- When e1 = e2, both sides evaluate identically (determinism)
- Identical results are trivially related
- Requires: `eval_deterministic_related_stores` infrastructure lemma

### COMPLETE FILE CONTENT:
```coq
(** * Declassification.v

    RIINA Declassification Semantic Typing Proof

    This file proves the semantic typing lemma for declassification:
    - logical_relation_declassify (Axiom 19): Declassification is sound

    PHASE 5: Store Semantics & Semantic Typing Axioms
    TARGET: Eliminate axiom 19

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_ζ (Zeta)
    Phase: 5 (Semantic Typing)

    References:
    - Sabelfeld & Myers (2003) "Language-based information-flow security"
    - Myers et al. (2006) "Decentralized robustness"
    - NonInterference.v (original axiom definition)
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

(** ** Axiom 19: Declassification (EDeclassify)

    When declassifying related secret values, the results are related.

    SEMANTIC JUSTIFICATION:
    The key insight is that TSecret values are ALWAYS trivially related.
    In the value relation:
      val_rel_at_type (TSecret T) v1 v2 = True

    This is the foundation of information hiding: an attacker cannot
    distinguish between any two secret values, regardless of their
    actual content.

    When we declassify:
    1. The input expressions e evaluate to classified values EClassify v1, EClassify v2
    2. These are related at type TSecret T (trivially True)
    3. EDeclassify strips the EClassify wrapper
    4. The underlying values v1, v2 become the result

    The soundness of declassification depends on the POLICY validation.
    The type system ensures that declassification only happens when
    the policy allows it. Once the policy check passes, the operation
    simply unwraps the value.

    Original axiom from NonInterference.v:
    Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n,
      has_type Γ Σ Δ e (TSecret T) ε ->
      env_rel Σ Γ rho1 rho2 ->
      rho_no_free_all rho1 ->
      rho_no_free_all rho2 ->
      exp_rel_n n Σ T (subst_rho rho1 (EDeclassify e p))
                      (subst_rho rho2 (EDeclassify e p)).
*)

(** ** Secret Values Are Always Related

    This is the foundation of information hiding.
    Any two closed secret values are indistinguishable.
*)

(** Secrets are trivially related at any step *)
Lemma val_rel_le_secret_trivial : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_le n Σ (TSecret T) v1 v2.
Proof.
  intros n Σ T v1 v2 Hv1 Hv2 Hc1 Hc2.
  apply val_rel_le_secret_always; auto.
Qed.

(** ** Declassification Operational Semantics

    EDeclassify (EClassify v) p --> v

    The declassification operation unwraps the classified value,
    assuming the policy check passes (handled by typing).
*)

(** Declassification evaluates to the unwrapped value *)
Lemma declassify_eval : forall v p st ctx,
  value v ->
  declass_ok (EClassify v) p ->
  multi_step (EDeclassify (EClassify v) p, st, ctx) (v, st, ctx).
Proof.
  intros v p st ctx Hv Hok.
  (* Single step via ST_DeclassifyValue, then reflexivity *)
  apply MS_Step with (cfg2 := (v, st, ctx)).
  - apply ST_DeclassifyValue; auto.
  - apply MS_Refl.
Qed.

(** ** Main Lemma: Declassification Preserves Relation

    If secret expressions evaluate to related (trivially) secret values,
    then declassification produces related results.

    SEMANTIC JUSTIFICATION:
    Since TSecret values are ALWAYS related (True), any two secret values
    that we declassify are related. The unwrapped values are what the
    secret originally contained.

    NOTE: The key subtlety is that we don't need the underlying values
    to be related BEFORE declassification - the secret type hides them.
    After declassification, we only claim they're related if the
    expressions were syntactically identical (same substitution applied).
*)

(** Core declassification lemma

    This lemma requires explicit value and declass_ok premises.
    In the full semantic typing proof, these are extracted from:
    - val_rel_le at step > 0 guarantees values are values
    - has_type (T_Declassify) guarantees declass_ok
*)
Lemma logical_relation_declassify_proven : forall n Σ T v1 v2 p st1 st2 ctx,
  val_rel_le n Σ (TSecret T) (EClassify v1) (EClassify v2) ->
  store_rel_simple Σ st1 st2 ->
  value v1 ->
  value v2 ->
  declass_ok (EClassify v1) p ->
  declass_ok (EClassify v2) p ->
  (* Declassify evaluates to the unwrapped values *)
  multi_step (EDeclassify (EClassify v1) p, st1, ctx) (v1, st1, ctx) /\
  multi_step (EDeclassify (EClassify v2) p, st2, ctx) (v2, st2, ctx) /\
  (* Store is unchanged (declassify is pure) *)
  store_rel_simple Σ st1 st2.
Proof.
  intros n Σ T v1 v2 p st1 st2 ctx Hrel Hst Hval1 Hval2 Hok1 Hok2.
  repeat split.
  - (* Evaluation of declassify on v1 *)
    apply declassify_eval; auto.
  - (* Evaluation of declassify on v2 *)
    apply declassify_eval; auto.
  - (* Store unchanged *)
    exact Hst.
Qed.

(** ** Declassification with Syntactically Identical Expressions

    When declassifying the same expression under related environments,
    the results are related because:
    1. Same expression means same underlying computation
    2. Related environments produce related intermediate values
    3. Declassification is deterministic
*)

(** Full expression relation for declassification

    When e1 = e2, they evaluate identically (determinism), so declassification
    produces identical results, which are trivially related.

    NOTE: This lemma requires determinism infrastructure for related stores.
    The core insight is sound: same expression + related stores → related results.
*)
Lemma exp_rel_le_declassify : forall n Σ T e1 e2 p st1 st2 ctx,
  exp_rel_le n Σ (TSecret T) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  (* For syntactically equal expressions, declassify produces related results *)
  e1 = e2 ->
  exp_rel_le n Σ T (EDeclassify e1 p) (EDeclassify e2 p) st1 st2 ctx.
Proof.
  intros n Σ T e1 e2 p st1 st2 ctx Hexp Hst Heq.
  subst e2.
  (* Now we have EDeclassify e1 p in both positions.
     exp_rel_le requires showing that for all k <= n, if both evaluate
     to values, those values are related.

     Since the SAME expression is being evaluated under related stores,
     determinism implies the results are related.

     This requires a "determinism modulo store relation" lemma:
     - Same expression
     - Related stores
     - Both terminate
     → Results are related

     Infrastructure lemma needed: eval_deterministic_related_stores *)
  unfold exp_rel_le.
  intros k v1 v2 st1' st2' ctx' Hk Heval1 Heval2 Hval1 Hval2.
  (* The key insight: same expression (EDeclassify e1 p) evaluated under
     related stores st1, st2 produces related results.
     This follows from determinism + store relation preservation. *)
  (* Infrastructure admit - requires determinism lemma *)
  admit.
Admitted.

(** ** Policy-Based Declassification

    Declassification requires:
    1. The secret expression e : TSecret T
    2. A policy proof p : TProof (TSecret T)
    3. The policy validation declass_ok e p
*)

(** Declassification is safe when policy allows *)
Lemma declassify_policy_safe : forall Γ Σ Δ e T eff1 eff2 p,
  has_type Γ Σ Δ e (TSecret T) eff1 ->
  has_type Γ Σ Δ p (TProof (TSecret T)) eff2 ->
  declass_ok e p ->
  has_type Γ Σ Δ (EDeclassify e p) T (effect_join eff1 eff2).
Proof.
  intros Γ Σ Δ e T eff1 eff2 p Htype_e Htype_p Hok.
  apply T_Declassify; assumption.
Qed.

(** ** Verification: Axiom Count

    This file provides proven lemmas that replace:
    - Axiom 19: logical_relation_declassify -> logical_relation_declassify_proven

    SECURITY JUSTIFICATION:
    The soundness of declassification relies on:
    1. TSecret values being trivially related (information hiding)
    2. Declassification only permitted when policy allows
    3. The type system ensuring policy validation

    The semantic proof captures (1). Properties (2) and (3) are
    enforced by the typing rules (T_Declassify, T_Classify).
*)

(** End of Declassification.v *)
```

---

## FILE 2: ValRelStepLimit_PROOF.v (148 lines, 1 admit)

### ADMIT TO PROVE (line 106)
```coq
Theorem val_rel_n_to_val_rel_proven : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```

**PROOF STRATEGY:**
- First-order types: fully proven via `val_rel_n_to_val_rel_fo_proven`
- Higher-order types: requires deriving typing from the relation
- Key insight: values in val_rel_n are well-typed (from fundamental theorem)

### COMPLETE FILE CONTENT:
```coq
(** * ValRelStepLimit_PROOF.v

    RIINA Axiom Elimination Proof

    Target Axiom: val_rel_n_to_val_rel
    Location: NonInterference_v2_LogicalRelation.v
    Status: PARTIAL - FO case PROVEN, HO case requires typing

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.
Require Import Arith.Compare_dec.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.NonInterference_v2.
Require Import RIINA.properties.NonInterference_v2_LogicalRelation.

Import ListNotations.

(** ============================================================ *)
(** Section 1: First-Order Case - FULLY PROVEN                    *)
(** ============================================================ *)

(** For first-order types, step indices are irrelevant.
    Uses val_rel_n_fo_equiv from NonInterference_v2.v *)
Theorem val_rel_n_to_val_rel_fo_proven : forall Σ T v1 v2,
  first_order_type T = true ->
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hfo Hval1 Hval2 [n0 Hrel].
  (* Extract closed_expr from the relation *)
  destruct (val_rel_n_closed (S n0) Σ T v1 v2 Hrel) as [Hc1 Hc2].
  (* Use val_rel_n_fo_equiv: for FO types, any step index works *)
  unfold val_rel. intro m.
  apply (val_rel_n_fo_equiv (S n0) m Σ T v1 v2 Hfo Hrel).
Qed.

(** ============================================================ *)
(** Section 2: General Case - With Typing Preconditions           *)
(** ============================================================ *)

(** Helper: repeated step-up with typing *)
Lemma val_rel_n_step_up_k : forall k n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  val_rel_n (n + k) Σ T v1 v2.
Proof.
  induction k as [| k' IH]; intros n Σ T v1 v2 Hrel Hty1 Hty2.
  - (* k = 0 *)
    replace (n + 0) with n by lia. exact Hrel.
  - (* k = S k' *)
    replace (n + S k') with (S (n + k')) by lia.
    apply val_rel_n_step_up.
    + apply IH; assumption.
    + exact Hty1.
    + exact Hty2.
Qed.

(** For higher-order types, we need typing preconditions. *)
Theorem val_rel_n_to_val_rel_with_typing : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hval1 Hval2 [n0 Hrel] Hty1 Hty2.
  unfold val_rel. intro m.
  destruct (le_lt_dec m (S n0)) as [Hle | Hgt].
  - (* m <= S n0: use downward monotonicity *)
    apply (val_rel_n_mono m (S n0) Σ T v1 v2 Hle Hrel).
  - (* m > S n0: use step-up *)
    assert (Hdiff : m = S n0 + (m - S n0)) by lia.
    rewrite Hdiff.
    apply val_rel_n_step_up_k; assumption.
Qed.

(** ============================================================ *)
(** Section 3: Original Axiom Signature                           *)
(** ============================================================ *)

(** The original axiom WITHOUT explicit typing preconditions.
    For FO types: fully provable.
    For HO types: requires deriving typing from the relation. *)
Theorem val_rel_n_to_val_rel_proven : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hval1 Hval2 Hex.
  destruct (first_order_decidable T) as [Hfo | Hho].
  - apply val_rel_n_to_val_rel_fo_proven; assumption.
  - apply val_rel_n_to_val_rel_with_typing; try assumption;
    intros; admit.
Admitted.

(** ============================================================ *)
(** Section 4: Verification                                       *)
(** ============================================================ *)

Print Assumptions val_rel_n_to_val_rel_fo_proven.
(* Should show: val_rel_n_step_up (admitted) *)

Print Assumptions val_rel_n_to_val_rel_with_typing.
(* Should show: val_rel_n_step_up (admitted) *)

(** ============================================================ *)
(** Section 5: Summary                                             *)
(** ============================================================ *)

(**
    RESULTS:

    1. val_rel_n_to_val_rel_fo_proven - FULLY PROVEN for FO types
       Uses val_rel_n_fo_equiv which is Qed in NonInterference_v2.v

    2. val_rel_n_to_val_rel_with_typing - PROVEN (modulo val_rel_n_step_up)
       The with-typing version is proven given typing preconditions.
       val_rel_n_step_up has one admit for the TFn fundamental theorem.

    3. val_rel_n_to_val_rel_proven - PARTIAL
       FO case: proven
       HO case: admits deriving typing from the relation

    BLOCKING FACTOR:
    The HO case requires "semantic typing" - proving that values in
    val_rel_n are well-typed. This is true by construction (values
    come from well-typed terms via the fundamental theorem) but
    extracting typing from the relation requires additional lemmas.

    RECOMMENDATION:
    - For first-order programs: axiom is ELIMINATED
    - For higher-order programs: use val_rel_n_to_val_rel_with_typing
      with explicit typing preconditions
*)

(** End of ValRelStepLimit_PROOF.v *)
```

---

## FILE 3: RelationBridge.v (246 lines, 3 admits)

### ADMITS TO PROVE
1. **Line 149**: `val_rel_le_to_n_attempt` - Bridge val_rel_le → val_rel_n
2. **Line 207**: `store_rel_n_mono_store` - Store relation strengthening
3. **Line 216**: `store_rel_n_weaken` - Store relation weakening

**ANALYSIS (from file):**
The file documents a FUNDAMENTAL GAP between val_rel_le and val_rel_n:
- val_rel_le has proper Kripke structure (TFn quantifies over store extensions)
- val_rel_n LACKS Kripke structure for TFn
- These are structurally incompatible for TFn types

**RECOMMENDATION:**
- Document admits as DESIGN LIMITATIONS
- Use val_rel_le for all new proofs
- Consider refactoring NonInterference.v to use val_rel_le

### COMPLETE FILE CONTENT:
```coq
(** * RelationBridge.v

    RIINA Relation Bridge: Connecting val_rel_n and val_rel_le

    This file establishes the connection between two parallel relation
    definitions in the RIINA codebase:
    - val_rel_n (NonInterference.v): Original fundamental theorem relations
    - val_rel_le (CumulativeRelation.v): Phase 2 cumulative relations

    GOAL: Derive val_rel_n_mono_store (Axiom 2) from proven val_rel_le_mono_store

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_ζ (Zeta)
    Phase: Zero-Admits Elimination
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
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.CumulativeMonotone.
Require Import RIINA.properties.NonInterference_v2_LogicalRelation.

Import ListNotations.

(** * Section 1: Structural Comparison

    EXHAUSTIVE ANALYSIS of the two relation definitions:

    ┌──────────────────────────────────────────────────────────────────────┐
    │                    STRUCTURAL COMPARISON TABLE                        │
    ├──────────────────────────────────────────────────────────────────────┤
    │ Aspect              │ val_rel_n           │ val_rel_le              │
    │                     │ (NonInterference.v) │ (CumulativeRelation.v)  │
    ├─────────────────────┼─────────────────────┼─────────────────────────┤
    │ Step 0              │ True                │ True                    │
    │ Cumulative          │ val_rel_n n'        │ val_rel_le n'           │
    │ Value/Closed        │ Separate conjuncts  │ Inside val_rel_struct   │
    ├─────────────────────┼─────────────────────┼─────────────────────────┤
    │ TFn Kripke Quant    │ NO                  │ YES (forall Σ' ext Σ)   │
    │ TFn Arg Relation    │ val_rel_at_type T1  │ val_rel_le n' Σ' T1     │
    │                     │ (structural only)   │ (at EXTENDED store!)    │
    │ TFn Store Premise   │ store_rel_n n' Σ    │ store_rel_simple Σ'     │
    │ TFn Result Vals     │ val_rel_n n' Σ T2   │ val_rel_le n' Σ'' T2    │
    │                     │ (ORIGINAL store!)   │ (FINAL store!)          │
    │ TFn Result Store    │ store_rel_n n' Σ''  │ store_rel_simple Σ''    │
    ├─────────────────────┼─────────────────────┼─────────────────────────┤
    │ TProd/TSum          │ Structural recursion│ val_rel_le n' recursion │
    │ TRef                │ Same location       │ Same location           │
    │ Base types          │ Identical           │ Identical               │
    └──────────────────────────────────────────────────────────────────────┘

    CRITICAL INSIGHT:
    The val_rel_le definition has KRIPKE STRUCTURE built into TFn,
    which is why val_rel_le_mono_store is provable for TFn.

    The val_rel_n definition LACKS Kripke structure in TFn,
    which is why val_rel_n_mono_store requires the frame property.
*)

(** * Section 2: First-Order Type Equivalence

    For first-order types (no TFn), the two definitions should be equivalent.
    This is because:
    1. Both have the same base case (True at step 0)
    2. Both have the same cumulative structure
    3. Both have identical structural cases for non-TFn types
*)

(** Check if a type is first-order (no function types) *)
(* first_order_type is already defined in TypeMeasure.v *)

(** For base types, val_rel_at_type doesn't depend on the parameters *)
Lemma val_rel_at_type_base_independent : forall T v1 v2 Σ1 Σ2 sr1 sr2 vr1 vr2 srl1 srl2,
  match T with TUnit | TBool | TInt | TString | TBytes | TSecret _ | TRef _ _ | TCapability _ | TProof _ => True | _ => False end ->
  val_rel_at_type Σ1 sr1 vr1 srl1 T v1 v2 <-> val_rel_at_type Σ2 sr2 vr2 srl2 T v1 v2.
Proof.
  intros T v1 v2 Σ1 Σ2 sr1 sr2 vr1 vr2 srl1 srl2 Hbase.
  destruct T; simpl; try reflexivity; try contradiction.
Qed.

(** * Section 3: Bridge Lemma Attempts

    We attempt to prove the bridge in both directions.
    This analysis will reveal exactly where the proofs succeed or fail.
*)

(** Direction 1: val_rel_le → val_rel_n

    HYPOTHESIS: This direction should be easier because val_rel_le
    is STRONGER (has Kripke quantification for TFn).

    STRATEGY: Instantiate the Kripke quantification with Σ' = Σ (reflexivity).
*)

(** Helper: store_rel_simple is weaker than store_rel_n at positive steps *)
Lemma store_rel_n_implies_simple : forall n Σ st1 st2,
  n > 0 ->
  store_rel_n n Σ st1 st2 ->
  store_rel_simple Σ st1 st2.
Proof.
  intros n Σ st1 st2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel.
  destruct Hrel as [_ [Hmax _]].
  unfold store_rel_simple. exact Hmax.
Qed.

(** Helper: store_ty_extends is reflexive *)
Lemma store_ty_extends_refl_local : forall Σ, store_ty_extends Σ Σ.
Proof.
  intros Σ. unfold store_ty_extends. auto.
Qed.

(** ATTEMPT: val_rel_le n Σ T v1 v2 → val_rel_n n Σ T v1 v2

    This lemma CANNOT be proven due to FUNDAMENTAL STRUCTURAL INCOMPATIBILITY:

    val_rel_n at (S n') requires val_rel_at_type, which:
    - Uses STRUCTURAL RECURSION on type T
    - For TFn: arguments checked with val_rel_at_type T1 (structural)
    - Does NOT have step-index in argument relation

    val_rel_le at (S n') requires val_rel_struct, which:
    - Uses STEP-INDEXED RECURSION on n
    - For TFn: arguments checked with val_rel_le n' Σ' T1 (step-indexed)
    - HAS step-index in argument relation

    These are INCOMPATIBLE TYPE SIGNATURES that cannot unify.
    The Coq type checker confirms this: cannot unify val_rel_n with val_rel_at_type.

    RIGOROUS CONCLUSION: Bridge strategy FAILS due to definition mismatch.
*)
Lemma val_rel_le_to_n_attempt : forall n Σ T v1 v2,
  val_rel_le n Σ T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  (* PROOF IMPOSSIBLE due to fundamental type incompatibility.
     Documented in GAP ANALYSIS section below. *)
Admitted.

(** * Section 4: GAP ANALYSIS

    The attempted proof reveals FUNDAMENTAL GAPS between the definitions:

    GAP 1: Argument Relation
    ========================
    - val_rel_le uses: val_rel_le n' Σ' T1 (cumulative, with value/closed)
    - val_rel_n uses: val_rel_at_type T1 (structural only, no step index)

    These are DIFFERENT relations. val_rel_at_type recurses structurally
    on the type, while val_rel_le recurses on the step index.

    GAP 2: Store Relation
    =====================
    - val_rel_le uses: store_rel_simple Σ' (just store_max equality)
    - val_rel_n uses: store_rel_n n' Σ (cumulative, with location contents)

    store_rel_n is STRONGER than store_rel_simple.

    GAP 3: Result Store Typing
    ==========================
    - val_rel_le: result values related at Σ'' (final extended store)
    - val_rel_n: result values related at Σ (ORIGINAL store!)

    This is a CRITICAL difference. val_rel_n's definition is arguably
    WRONG from a Kripke semantics perspective, but it's what we have.

    GAP 4: Kripke Quantification
    ============================
    - val_rel_le: forall Σ' extending Σ (proper Kripke semantics)
    - val_rel_n: NO such quantification (missing Kripke structure)

    CONCLUSION:
    ===========
    The two definitions are NOT directly equivalent for TFn types.
    The bridge approach requires additional lemmas to close each gap.
*)

(** * Section 5: Alternative Strategy

    Since direct bridging fails, we consider an alternative:
    Prove val_rel_n_mono_store DIRECTLY using the same technique
    as val_rel_le_mono_store, but adapted to the val_rel_n structure.

    The key insight is that even though val_rel_n lacks explicit
    Kripke quantification, the SEMANTIC MEANING should be preserved
    under store extension for well-typed values.
*)

(** First, let's prove the store relation direction we need *)
(* ADMITTED for v2 migration: base case no longer trivial + direction wrong *)
Lemma store_rel_n_mono_store : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n n Σ' st1 st2.
Proof.
Admitted.

(** The correct direction: weakening (Σ' → Σ) *)
(* ADMITTED for v2 migration: base case no longer trivial *)
Lemma store_rel_n_weaken : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
Admitted.

(** * Section 6: Final Analysis

    RIGOROUS CONCLUSION:

    1. val_rel_le and val_rel_n are NOT structurally equivalent for TFn types.

    2. val_rel_le has CORRECT Kripke semantics (quantification over extensions).
       This is why val_rel_le_mono_store is fully provable.

    3. val_rel_n LACKS proper Kripke semantics for TFn.
       This is a DESIGN ISSUE in the original NonInterference.v definition.

    4. The bridge strategy CANNOT work without additional axioms because:
       - Gap 1 (arg relation): structural vs cumulative
       - Gap 2 (store relation): simple vs full
       - Gap 3 (result store): original vs final
       - Gap 4 (Kripke quantification): missing vs present

    5. The CORRECT long-term solution is to REFACTOR NonInterference.v
       to use the val_rel_le definition (with proper Kripke semantics).

    6. SHORT-TERM SOLUTION: Document the gaps as semantic justifications
       for the remaining admits, with a clear path to resolution.

    This analysis provides ZERO TRUST verification that the admits are
    NOT due to proof difficulty but due to FUNDAMENTAL DEFINITION GAPS.
*)

(** End of RelationBridge.v *)
```

---

## FILE 4: ReferenceOps.v (323 lines, 3 admits)

### ADMITS TO PROVE
1. **Line 264**: `exp_rel_le_ref` - Expression relation for ERef
2. **Line 286**: `exp_rel_le_deref` - Expression relation for EDeref
3. **Line 309**: `exp_rel_le_assign` - Expression relation for EAssign

**PROOF STRATEGY:**
All three require multi_step inversion infrastructure:
- Need to decompose evaluation sequences
- Core lemmas (logical_relation_*_proven) are fully proven
- Missing: infrastructure to connect exp_rel_le to core lemmas

### COMPLETE FILE CONTENT:
```coq
(** * ReferenceOps.v

    RIINA Reference Operations Semantic Typing Proofs

    This file proves the semantic typing lemmas for reference operations:
    - logical_relation_ref (Axiom 16): Reference creation preserves relation
    - logical_relation_deref (Axiom 17): Dereference preserves relation
    - logical_relation_assign (Axiom 18): Assignment preserves relation

    PHASE 5: Store Semantics & Semantic Typing Axioms
    TARGET: Eliminate axioms 16, 17, 18

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_ζ (Zeta)
    Phase: 5 (Semantic Typing)

    References:
    - Ahmed (2006) "Step-Indexed Syntactic Logical Relations"
    - Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"
    - NonInterference.v (original axiom definitions)
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

(** ** Axiom 16: Reference Creation (ERef)

    When creating a reference to a related value, the resulting
    locations are related (and in fact, identical).

    SEMANTIC JUSTIFICATION:
    1. The value expressions evaluate to related values v1, v2
    2. Both stores have the same max (from store_rel_simple)
    3. Therefore fresh_loc st1 = fresh_loc st2
    4. Both allocations write to the same location
    5. The resulting locations ELoc l are trivially related (same l)
    6. Store typing is extended consistently

    Original axiom from NonInterference.v:
    Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
      has_type Γ Σ Δ e T ε ->
      env_rel Σ Γ rho1 rho2 ->
      rho_no_free_all rho1 ->
      rho_no_free_all rho2 ->
      exp_rel_n n Σ (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).
*)

(** Helper: Related stores allocate to same location *)
Lemma ref_same_location : forall Σ st1 st2,
  store_rel_simple Σ st1 st2 ->
  fresh_loc st1 = fresh_loc st2.
Proof.
  intros Σ st1 st2 Hrel.
  apply store_alloc_same with (Σ := Σ). exact Hrel.
Qed.

(** Reference creation produces same location in related stores *)
Lemma logical_relation_ref_proven : forall n Σ T sl v1 v2 st1 st2 ctx,
  n > 0 ->
  value v1 ->
  value v2 ->
  store_wf Σ st1 ->
  val_rel_le n Σ T v1 v2 ->
  store_rel_simple Σ st1 st2 ->
  store_rel_le n Σ st1 st2 ->
  let l := fresh_loc st1 in
  let Σ' := store_ty_update l T sl Σ in
  let st1' := store_update l v1 st1 in
  let st2' := store_update l v2 st2 in
  (* Reference creation evaluates to ELoc l in both *)
  multi_step (ERef v1 sl, st1, ctx) (ELoc l, st1', ctx) /\
  multi_step (ERef v2 sl, st2, ctx) (ELoc l, st2', ctx) /\
  (* Resulting locations are related *)
  val_rel_le n Σ' (TRef T sl) (ELoc l) (ELoc l) /\
  (* Store relation is maintained *)
  store_rel_simple Σ' st1' st2' /\
  (* Store typing is extended *)
  store_ty_extends Σ Σ'.
Proof.
  intros n Σ T sl v1 v2 st1 st2 ctx Hn Hv1 Hv2 Hwf Hval Hsimple Hrel.
  simpl.
  (* First, establish that fresh_loc is the same in both stores *)
  assert (Hfresh_eq : fresh_loc st1 = fresh_loc st2).
  { apply ref_same_location with (Σ := Σ). exact Hsimple. }
  (* Split into 5 parts *)
  repeat split.
  - (* ERef v1 sl evaluates to ELoc (fresh_loc st1) *)
    apply MS_Step with (cfg2 := (ELoc (fresh_loc st1), store_update (fresh_loc st1) v1 st1, ctx)).
    + apply ST_RefValue; auto.
    + apply MS_Refl.
  - (* ERef v2 sl evaluates to ELoc (fresh_loc st2) = ELoc (fresh_loc st1) *)
    rewrite Hfresh_eq.
    apply MS_Step with (cfg2 := (ELoc (fresh_loc st2), store_update (fresh_loc st2) v2 st2, ctx)).
    + apply ST_RefValue; auto.
    + rewrite <- Hfresh_eq. apply MS_Refl.
  - (* val_rel_le n Σ' (TRef T sl) (ELoc l) (ELoc l) *)
    apply val_rel_le_build_ref.
  - (* store_rel_simple Σ' st1' st2' *)
    unfold store_rel_simple.
    apply store_max_update_eq.
    unfold store_rel_simple in Hsimple. exact Hsimple.
  - (* store_ty_extends Σ Σ' *)
    apply store_ty_extends_alloc.
    apply fresh_loc_not_in_store_ty.
    exact Hwf.
Qed.

(** ** Axiom 17: Dereference (EDeref)

    When dereferencing related locations, the retrieved values are related.

    SEMANTIC JUSTIFICATION:
    1. The reference expressions evaluate to the same location ELoc l
    2. By store_rel_le, values at location l are related in both stores
    3. Looking up l in both stores gives related values

    Original axiom from NonInterference.v:
    Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n,
      has_type Γ Σ Δ e (TRef T l) ε ->
      env_rel Σ Γ rho1 rho2 ->
      rho_no_free_all rho1 ->
      rho_no_free_all rho2 ->
      exp_rel_n n Σ T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).
*)

(** Dereference retrieves related values from related stores *)
Lemma logical_relation_deref_proven : forall n Σ T sl l st1 st2 ctx,
  store_rel_le n Σ st1 st2 ->
  store_ty_lookup l Σ = Some (T, sl) ->
  exists v1 v2,
    store_lookup l st1 = Some v1 /\
    store_lookup l st2 = Some v2 /\
    (* Dereference evaluates to the looked-up values *)
    multi_step (EDeref (ELoc l), st1, ctx) (v1, st1, ctx) /\
    multi_step (EDeref (ELoc l), st2, ctx) (v2, st2, ctx) /\
    (* Retrieved values are related *)
    val_rel_le n Σ T v1 v2.
Proof.
  intros n Σ T sl l st1 st2 ctx Hrel Hlook.
  (* Use store_rel_le_lookup to get related values *)
  destruct (store_rel_le_lookup n Σ st1 st2 l T sl Hrel Hlook)
    as [v1 [v2 [Hst1 [Hst2 Hval]]]].
  exists v1, v2.
  repeat split; auto.
  - (* EDeref (ELoc l) evaluates to v1 in st1 *)
    apply MS_Step with (cfg2 := (v1, st1, ctx)).
    + apply ST_DerefLoc. exact Hst1.
    + apply MS_Refl.
  - (* EDeref (ELoc l) evaluates to v2 in st2 *)
    apply MS_Step with (cfg2 := (v2, st2, ctx)).
    + apply ST_DerefLoc. exact Hst2.
    + apply MS_Refl.
Qed.

(** ** Axiom 18: Assignment (EAssign)

    When assigning related values to related locations, the store
    relation is maintained and the result is EUnit (trivially related).

    SEMANTIC JUSTIFICATION:
    1. The reference expressions evaluate to the same location ELoc l
    2. The value expressions evaluate to related values v1, v2
    3. Updating both stores at l with related values maintains store_rel_le
    4. The result is EUnit in both cases (trivially related)

    Original axiom from NonInterference.v:
    Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n,
      has_type Γ Σ Δ e1 (TRef T l) ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      env_rel Σ Γ rho1 rho2 ->
      rho_no_free_all rho1 ->
      rho_no_free_all rho2 ->
      exp_rel_n n Σ TUnit (subst_rho rho1 (EAssign e1 e2))
                          (subst_rho rho2 (EAssign e1 e2)).
*)

(** Assignment preserves store relation and produces related units *)
Lemma logical_relation_assign_proven : forall n Σ T sl l v1 v2 st1 st2 ctx,
  value v1 ->
  value v2 ->
  store_rel_le n Σ st1 st2 ->
  store_ty_lookup l Σ = Some (T, sl) ->
  val_rel_le n Σ T v1 v2 ->
  let st1' := store_update l v1 st1 in
  let st2' := store_update l v2 st2 in
  (* Assignment evaluates to EUnit *)
  multi_step (EAssign (ELoc l) v1, st1, ctx) (EUnit, st1', ctx) /\
  multi_step (EAssign (ELoc l) v2, st2, ctx) (EUnit, st2', ctx) /\
  (* Result is related *)
  val_rel_le n Σ TUnit EUnit EUnit /\
  (* Store relation is maintained *)
  store_rel_le n Σ st1' st2'.
Proof.
  intros n Σ T sl l v1 v2 st1 st2 ctx Hv1 Hv2 Hrel Hlook Hval.
  simpl.
  (* Get old values from store_rel_le_lookup to satisfy ST_AssignLoc precondition *)
  destruct (store_rel_le_lookup n Σ st1 st2 l T sl Hrel Hlook)
    as [v1' [v2' [Hst1 [Hst2 _]]]].
  (* Split into 4 parts carefully to avoid splitting store_rel_le *)
  split; [| split; [| split]].
  - (* EAssign (ELoc l) v1 evaluates to EUnit with updated store *)
    apply MS_Step with (cfg2 := (EUnit, store_update l v1 st1, ctx)).
    + apply ST_AssignLoc with (v1 := v1'); auto.
    + apply MS_Refl.
  - (* EAssign (ELoc l) v2 evaluates to EUnit with updated store *)
    apply MS_Step with (cfg2 := (EUnit, store_update l v2 st2, ctx)).
    + apply ST_AssignLoc with (v1 := v2'); auto.
    + apply MS_Refl.
  - (* val_rel_le n Σ TUnit EUnit EUnit *)
    apply val_rel_le_unit.
  - (* store_rel_le n Σ (store_update l v1 st1) (store_update l v2 st2) *)
    apply store_rel_le_update with (T := T) (sl := sl); auto.
Qed.

(** ** Combined Lemma: Full Expression Relation for References

    These lemmas establish that reference operations preserve the
    expression relation, which is what the original axioms state.
*)

(** Expression relation for ERef

    PROOF STRATEGY (requires multi_step inversion):
    1. Unfold exp_rel_le: need to show that for any evaluation of
       (ERef e1 sl) and (ERef e2 sl) to values v1, v2, they are related.
    2. By determinism of evaluation, this reduces to showing that
       if e1 -->* v1' and e2 -->* v2', then ERef v1' sl and ERef v2' sl
       both step to ELoc l for the same l.
    3. Use exp_rel_le hypothesis to get val_rel_le for v1', v2'.
    4. Apply logical_relation_ref_proven.

    STATUS: Admitted - requires evaluation inversion infrastructure
*)
Lemma exp_rel_le_ref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ T e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ (TRef T sl) (ERef e1 sl) (ERef e2 sl) st1 st2 ctx.
Proof.
  intros n Σ T sl e1 e2 st1 st2 ctx Hexp Hst.
  unfold exp_rel_le.
  intros k v1 v2 st1' st2' ctx' Hk Heval1 Heval2.
  (* Need to decompose multi_step evaluations and apply core lemma *)
  (* This requires showing that ERef e sl evaluates by first evaluating e *)
  admit.
Admitted.

(** Expression relation for EDeref

    PROOF STRATEGY (requires multi_step inversion):
    1. Unfold exp_rel_le: show that deref evaluations produce related values.
    2. By exp_rel_le hypothesis, e1 and e2 evaluate to related references.
    3. By val_rel_le_ref_same_loc, they point to the same location l.
    4. Apply logical_relation_deref_proven to get related dereferenced values.

    STATUS: Admitted - requires evaluation inversion infrastructure
*)
Lemma exp_rel_le_deref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ T (EDeref e1) (EDeref e2) st1 st2 ctx.
Proof.
  intros n Σ T sl e1 e2 st1 st2 ctx Hexp Hst.
  unfold exp_rel_le.
  intros k v1 v2 st1' st2' ctx' Hk Heval1 Heval2.
  (* Need to decompose: EDeref e -->* v means e -->* ELoc l then deref *)
  admit.
Admitted.

(** Expression relation for EAssign

    PROOF STRATEGY (requires multi_step inversion):
    1. Unfold exp_rel_le: show that assignment evaluations produce EUnit.
    2. Assignment evaluates both subexpressions, then does the store update.
    3. By exp_rel_le hypotheses, references and values are related.
    4. Apply logical_relation_assign_proven for the final step.

    STATUS: Admitted - requires evaluation inversion infrastructure
*)
Lemma exp_rel_le_assign : forall n Σ T sl e1 e2 e1' e2' st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  exp_rel_le n Σ T e1' e2' st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ TUnit (EAssign e1 e1') (EAssign e2 e2') st1 st2 ctx.
Proof.
  intros n Σ T sl e1 e2 e1' e2' st1 st2 ctx Hexp1 Hexp2 Hst.
  unfold exp_rel_le.
  intros k v1 v2 st1' st2' ctx' Hk Heval1 Heval2.
  (* Need to decompose assignment evaluation sequence *)
  admit.
Admitted.

(** ** Verification: Axiom Count

    This file provides proven lemmas that replace:
    - Axiom 16: logical_relation_ref -> logical_relation_ref_proven
    - Axiom 17: logical_relation_deref -> logical_relation_deref_proven
    - Axiom 18: logical_relation_assign -> logical_relation_assign_proven

    Note: Some sub-lemmas are admitted pending detailed operational
    semantics reasoning. The semantic justifications are sound and
    the overall proof strategy is correct.
*)

(** End of ReferenceOps.v *)
```

---

## FILE 5: KripkeMutual.v (319 lines, 4 admits)

### ADMITS TO PROVE
1. **Line 171**: `store_rel_n_weaken_aux_fo` (partial - HIGH case)
2. **Line 184**: `store_rel_n_weaken_aux` (general case)
3. **Line 243**: `val_rel_n_weaken_proof` (general case)
4. **Line 284**: `val_rel_n_mono_store_proof` (general case)

**KEY INSIGHT from file:**
- First-order types are FULLY PROVEN
- Higher-order types (TFn) require mutual induction on (n, type_measure T)
- TFn case needs FRAME PROPERTY from separation logic

### COMPLETE FILE CONTENT:
```coq
(** * KripkeMutual.v

    RIINA Mutual Kripke Monotonicity Proofs

    This file proves Axioms 1 and 2 (val_rel_n_weaken and val_rel_n_mono_store)
    using mutual induction on (n, type_measure T).

    CRITICAL INSIGHT:
    The two axioms are mutually dependent for TFn types:
    - Axiom 1 (weaken Σ' → Σ) requires Axiom 2 for store premise conversion
    - Axiom 2 (strengthen Σ → Σ') requires Axiom 1 for store premise conversion

    For first-order types, both are trivial because val_rel_at_type
    doesn't depend on Σ in the structural cases.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_ζ (Zeta)
    Phase: Zero-Admits Elimination
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
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.NonInterference_v2_LogicalRelation.

Import ListNotations.

(** ** First-order case: val_rel_at_type is Σ-independent

    For first-order types, val_rel_at_type only checks structural
    properties that don't involve Σ. This makes both directions trivial.

    IMPORTANT: This lemma must be defined before val_rel_n_weaken_fo
    since it's used in that proof.
*)

(** Check if val_rel_at_type depends on Σ for first-order types *)
Lemma val_rel_at_type_fo_independent : forall T v1 v2 Σ Σ'
  (sr1 : store_ty -> store -> store -> Prop)
  (sr2 : store_ty -> store -> store -> Prop)
  (vr1 : store_ty -> ty -> expr -> expr -> Prop)
  (vr2 : store_ty -> ty -> expr -> expr -> Prop)
  (srl1 : store_ty -> store -> store -> Prop)
  (srl2 : store_ty -> store -> store -> Prop),
  first_order_type T = true ->
  val_rel_at_type Σ sr1 vr1 srl1 T v1 v2 <->
  val_rel_at_type Σ' sr2 vr2 srl2 T v1 v2.
Proof.
  (* For first-order types, val_rel_at_type is purely structural
     and doesn't depend on Σ or the relation parameters.
     The proof requires induction on type structure. *)
  intros T. induction T; intros v1 v2 Σ Σ' sr1 sr2 vr1 vr2 srl1 srl2 Hfo;
  simpl in Hfo; try discriminate; simpl; try reflexivity.
  - (* TProd T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    split; intros H.
    + destruct H as (x1 & y1 & x2 & y2 & Heq1 & Heq2 & Hr1 & Hr2).
      exists x1, y1, x2, y2. repeat split; try assumption.
      * apply IHT1 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
      * apply IHT2 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
    + destruct H as (x1 & y1 & x2 & y2 & Heq1 & Heq2 & Hr1 & Hr2).
      exists x1, y1, x2, y2. repeat split; try assumption.
      * apply IHT1 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
      * apply IHT2 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
  - (* TSum T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    split; intros H.
    + destruct H as [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply IHT1 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
      * right. exists y1, y2. repeat split; try assumption.
        apply IHT2 with (Σ := Σ) (sr1 := sr1) (vr1 := vr1) (srl1 := srl1); auto.
    + destruct H as [[x1 [x2 [Heq1 [Heq2 Hr]]]] | [y1 [y2 [Heq1 [Heq2 Hr]]]]].
      * left. exists x1, x2. repeat split; try assumption.
        apply IHT1 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
      * right. exists y1, y2. repeat split; try assumption.
        apply IHT2 with (Σ := Σ') (sr1 := sr2) (vr1 := vr2) (srl1 := srl2); auto.
Qed.

(** ** Helper: val_rel_n weakening for first-order types

    For first-order types, val_rel_at_type is Σ-independent, so weakening
    is straightforward using val_rel_at_type_fo_independent.
*)
(* PROVEN: For first-order types, val_rel_n doesn't depend on Σ *)
Lemma val_rel_n_weaken_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hfo Hext Hrel.
  - (* n = 0: val_rel_n 0 doesn't depend on Σ at all *)
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    rewrite Hfo in Hrel. rewrite Hfo.
    destruct Hrel as (Hv1 & Hv2 & Hc1 & Hc2 & Hrat).
    (* For n=0 FO types, the definition is val_rel_at_type_fo which doesn't involve Σ *)
    repeat split; assumption.
  - (* n = S n': use induction and val_rel_at_type_fo_independent *)
    rewrite val_rel_n_S_unfold in Hrel.
    rewrite Hfo in Hrel.
    destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & _ & Hrat).
    rewrite val_rel_n_S_unfold.
    rewrite Hfo.
    repeat split; try assumption.
    + (* Recursive case: val_rel_n n' Σ T v1 v2 *)
      apply IH with Σ'; assumption.
    + (* val_rel_at_type case: use FO independence *)
      apply (val_rel_at_type_fo_equiv T Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
      apply (val_rel_at_type_fo_equiv T Σ' (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
      exact Hrat.
Qed.

(** ** Helper: Store relation weakening for first-order store types

    If stores are related at Σ' (larger), they remain related at Σ (smaller),
    assuming all types in Σ are first-order.
*)
(* PROVEN: Store weakening for first-order store types *)
Lemma store_rel_n_weaken_aux_fo : forall n Σ Σ' st1 st2,
  (* Restriction: all types in Σ must be first-order *)
  (forall l T sl, store_ty_lookup l Σ = Some (T, sl) -> first_order_type T = true) ->
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hfo_all Hext Hrel.
  - (* n = 0: store_rel_n 0 is just store_max equality - Σ-independent *)
    rewrite store_rel_n_0_unfold in Hrel.
    rewrite store_rel_n_0_unfold.
    exact Hrel.
  - (* n = S n' *)
    rewrite store_rel_n_S_unfold in Hrel.
    destruct Hrel as (Hrec & Hmax & Htyped).
    rewrite store_rel_n_S_unfold.
    repeat split.
    + (* Recursive: store_rel_n n' Σ st1 st2 *)
      apply IH with Σ'; assumption.
    + (* store_max equality *)
      exact Hmax.
    + (* Typed locations in Σ *)
      intros l T sl Hlook.
      (* Since store_ty_extends Σ Σ', l is also in Σ' *)
      assert (Hlook' : store_ty_lookup l Σ' = Some (T, sl)).
      { apply Hext. exact Hlook. }
      destruct (Htyped l T sl Hlook') as (v1 & v2 & Hst1 & Hst2 & Hval_rel).
      exists v1, v2.
      repeat split; try assumption.
      (* Handle security-aware conditional *)
      destruct (is_low_dec sl) eqn:Hsl.
      * (* LOW: val_rel_n n' Σ' T v1 v2 -> val_rel_n n' Σ T v1 v2 *)
        (* T is first-order by Hfo_all, so we can use val_rel_n_weaken_fo *)
        apply val_rel_n_weaken_fo with Σ'; try assumption.
        apply Hfo_all with l sl. exact Hlook.
      * (* HIGH: typing needs store_ty adjustment *)
        destruct Hval_rel as [Hv1 [Hv2 [Hc1 [Hc2 [Hty1 Hty2]]]]].
        repeat split; try assumption.
        (* has_type nil Σ' T -> has_type nil Σ T for values - typing_weaken *)
        -- admit.  (* typing_weaken for Σ -> Σ' direction is the opposite *)
        -- admit.
Admitted.

(** Original lemma without restriction - kept for API compatibility but
    requires mutual induction for TFn types which is not structurally
    possible in val_rel_n definition. For the unrestricted case, use
    val_rel_le from CumulativeRelation.v which has proper Kripke structure.
*)
(* ADMITTED for v2 migration: base case no longer trivial *)
Lemma store_rel_n_weaken_aux : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
Admitted.

(** ** Helper: Store relation strengthening (Axiom 2 for stores)

    If stores are related at Σ (smaller), they remain related at Σ' (larger).
    This is the STRENGTHENING direction.

    CRITICAL: This only holds for locations IN Σ. Locations in Σ' \ Σ
    are not constrained by store_rel_n n Σ, so we can't make claims about them.

    Actually, store_rel_n only checks locations that are IN the store typing.
    So store_rel_n n Σ' checks MORE locations than store_rel_n n Σ.
    This means strengthening DOES NOT HOLD in general!

    Wait, let me re-read store_rel_n...
*)

(** Let me examine the actual definition more carefully *)
Lemma store_rel_n_structure : forall n Σ st1 st2,
  store_rel_n (S n) Σ st1 st2 <->
  (store_rel_n n Σ st1 st2 /\
   store_max st1 = store_max st2 /\
   forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
     exists v1 v2,
       store_lookup l st1 = Some v1 /\
       store_lookup l st2 = Some v2 /\
       (if is_low_dec sl
        then val_rel_n n Σ T v1 v2
        else (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
              has_type nil Σ Public v1 T EffectPure /\
              has_type nil Σ Public v2 T EffectPure))).
Proof.
  intros. simpl. reflexivity.
Qed.

(** ** Main Theorem: Mutual Kripke Monotonicity

    We prove both axioms simultaneously by well-founded induction on
    (n, type_measure T) with lexicographic ordering.
*)

(** Axiom 1: Weakening (larger store to smaller store) - First-order version *)
Theorem val_rel_n_weaken_fo_proof : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  (* For first-order types, val_rel_at_type is Σ-independent *)
  intros. apply val_rel_n_weaken_fo with Σ'; assumption.
Qed.

(** Axiom 1: Weakening (larger store to smaller store) - General *)
(* ADMITTED for v2 migration: base case no longer trivial *)
Theorem val_rel_n_weaken_proof : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
Admitted.

(** Axiom 2: Strengthening (smaller store to larger store) - First-order *)
(* PROVEN: For first-order types, val_rel_n doesn't depend on Σ *)
Lemma val_rel_n_mono_store_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  (* For first-order types, val_rel_n is Σ-independent.
     Both weakening and strengthening are the same: just transfer the relation. *)
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hfo Hext Hrel.
  - (* n = 0: val_rel_n 0 doesn't depend on Σ at all for FO types *)
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    (* Rewrite the conditional to eliminate Σ dependency *)
    rewrite Hfo in Hrel. rewrite Hfo.
    exact Hrel.
  - (* n = S n': use induction and val_rel_at_type_fo_independent *)
    rewrite val_rel_n_S_unfold in Hrel.
    rewrite Hfo in Hrel.
    destruct Hrel as (Hrec & Hv1 & Hv2 & Hc1 & Hc2 & _ & Hrat).
    rewrite val_rel_n_S_unfold.
    rewrite Hfo.
    repeat split; try assumption.
    + (* Recursive case: val_rel_n n' Σ' T v1 v2 *)
      apply IH with Σ; assumption.
    + (* val_rel_at_type case: use FO independence *)
      apply (val_rel_at_type_fo_equiv T Σ' (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
      apply (val_rel_at_type_fo_equiv T Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
      exact Hrat.
Qed.

(** Axiom 2: Strengthening (smaller store to larger store) - General *)
(* ADMITTED for v2 migration: base case no longer trivial *)
Theorem val_rel_n_mono_store_proof : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
Admitted.

(** ** Summary

    The mutual induction structure is:

    1. Base case (n = 0): Both directions trivially True

    2. First-order types: val_rel_at_type is Σ-independent
       - Axiom 1: trivial
       - Axiom 2: trivial

    3. TFn types: Mutual dependency
       - Axiom 1 (Σ' → Σ) requires:
         * Axiom 2 for store premise (store_rel_n n' Σ → store_rel_n n' Σ')
         * Axiom 1 recursively for result type at n' < n

       - Axiom 2 (Σ → Σ') requires:
         * Axiom 1 for store premise (store_rel_n n' Σ' → store_rel_n n' Σ)
         * Axiom 2 recursively for result type at n' < n
         * ADDITIONAL: Σ'' (from execution) extends Σ'

    The ADDITIONAL requirement for Axiom 2 is the key blocker.
    It requires showing that function execution preserves
    store locations that the function doesn't know about.

    This is a semantic property of well-typed evaluation:
    - Well-typed terms only access locations in their store typing
    - Other locations are preserved unchanged
    - Therefore Σ'' can be extended to include Σ' \ Σ

    This requires the FRAME PROPERTY from separation logic or
    similar reasoning about non-interference with unknown locations.
*)

(** End of KripkeMutual.v *)
```

---

## DELIVERABLES

For each file, provide:
1. **FIXED FILE**: Complete `.v` file with all admits replaced by Qed proofs
2. **CHANGE LOG**: List each admit with the proof technique used
3. **ASSUMPTIONS**: Any new axioms or infrastructure lemmas required

### OUTPUT FORMAT
```
=== FILE: <filename>.v ===
[Complete Coq file content]

=== CHANGE LOG ===
1. Line X: <lemma_name> - <proof technique>
2. ...

=== ASSUMPTIONS ===
- <any new axioms or required infrastructure>
```

---

## PRIORITY ORDER

1. **Declassification.v** (1 admit) - Easiest, requires determinism lemma
2. **ValRelStepLimit_PROOF.v** (1 admit) - FO done, HO needs semantic typing
3. **ReferenceOps.v** (3 admits) - Core lemmas proven, need eval inversion
4. **KripkeMutual.v** (4 admits) - FO proven, HO needs frame property
5. **RelationBridge.v** (3 admits) - Design limitation, may not be provable

---

**Mode:** ULTRA KIASU | ZERO TRUST | QED ETERNUM
**Goal:** 12 admits → 0 admits across 5 files
