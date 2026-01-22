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
