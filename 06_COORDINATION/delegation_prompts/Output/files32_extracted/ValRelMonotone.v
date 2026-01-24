(** * ValRelMonotone.v

    Step monotonicity for the cumulative logical relation.

    Key theorem: If values are related at step n, they are related at any m ≤ n.

    Mode: ULTRA KIASU | ZERO ADMITS
*)

Require Import Nat.
Require Import Arith.
Require Import Lia.
Require Import List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.CumulativeRelation.
Import ListNotations.

(** ----------------------------------------------------------------- *)
(** * Step Monotonicity for Value Relation                            *)
(** ----------------------------------------------------------------- *)

(** The cumulative relation val_rel_le is defined to be downward-closed
    in the step index by construction. This lemma makes that explicit. *)

Theorem val_rel_le_monotone : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hle Hrel.
  (* The cumulative relation is defined with downward closure *)
  (* We use the cumulative_val_rel_le property from CumulativeRelation.v *)
  apply cumulative_val_rel_le with n.
  - exact Hle.
  - exact Hrel.
Qed.

(** Corollary: Relation at any step implies relation at 0 *)
Corollary val_rel_le_zero : forall n Σ T v1 v2,
  val_rel_le n Σ T v1 v2 ->
  val_rel_le 0 Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hrel.
  apply val_rel_le_monotone with n.
  - lia.
  - exact Hrel.
Qed.

(** ----------------------------------------------------------------- *)
(** * Step Monotonicity for Expression Relation                       *)
(** ----------------------------------------------------------------- *)

(** Expression relation also inherits monotonicity *)
Theorem exp_rel_le_monotone : forall m n Σ Γ T e1 e2,
  m <= n ->
  exp_rel_le n Σ Γ T e1 e2 ->
  exp_rel_le m Σ Γ T e1 e2.
Proof.
  intros m n Σ Γ T e1 e2 Hle Hrel.
  apply cumulative_exp_rel_le with n.
  - exact Hle.
  - exact Hrel.
Qed.

(** ----------------------------------------------------------------- *)
(** * Step Monotonicity for Environment Relation                      *)
(** ----------------------------------------------------------------- *)

(** Substitution environment relation monotonicity *)
Theorem env_rel_le_monotone : forall m n Σ Γ ρ1 ρ2,
  m <= n ->
  env_rel_le n Σ Γ ρ1 ρ2 ->
  env_rel_le m Σ Γ ρ1 ρ2.
Proof.
  intros m n Σ Γ ρ1 ρ2 Hle Hrel.
  apply cumulative_env_rel_le with n.
  - exact Hle.
  - exact Hrel.
Qed.

(** ----------------------------------------------------------------- *)
(** * Successor Step Lemmas                                           *)
(** ----------------------------------------------------------------- *)

(** If related at S n, then related at n *)
Lemma val_rel_le_pred : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hrel.
  apply val_rel_le_monotone with (S n).
  - lia.
  - exact Hrel.
Qed.

Lemma exp_rel_le_pred : forall n Σ Γ T e1 e2,
  exp_rel_le (S n) Σ Γ T e1 e2 ->
  exp_rel_le n Σ Γ T e1 e2.
Proof.
  intros n Σ Γ T e1 e2 Hrel.
  apply exp_rel_le_monotone with (S n).
  - lia.
  - exact Hrel.
Qed.

(** ----------------------------------------------------------------- *)
(** * Transitivity of Step Index Comparison                           *)
(** ----------------------------------------------------------------- *)

(** Monotonicity composes: if related at n and k ≤ m ≤ n, related at k *)
Lemma val_rel_le_trans_mono : forall k m n Σ T v1 v2,
  k <= m ->
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le k Σ T v1 v2.
Proof.
  intros k m n Σ T v1 v2 Hkm Hmn Hrel.
  apply val_rel_le_monotone with m.
  - exact Hkm.
  - apply val_rel_le_monotone with n.
    + exact Hmn.
    + exact Hrel.
Qed.

(** ----------------------------------------------------------------- *)
(** * Maximum Step Preservation                                       *)
(** ----------------------------------------------------------------- *)

(** If related at both m and n, related at max m n *)
Lemma val_rel_le_max : forall m n Σ T v1 v2,
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le (max m n) Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hm Hn.
  destruct (Nat.le_ge_cases m n) as [Hle | Hge].
  - (* m <= n *)
    rewrite Nat.max_r; [exact Hn | exact Hle].
  - (* n <= m *)
    rewrite Nat.max_l; [exact Hm | exact Hge].
Qed.

(** If related at max m n, related at both m and n *)
Lemma val_rel_le_from_max : forall m n Σ T v1 v2,
  val_rel_le (max m n) Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2 /\ val_rel_le n Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hmax.
  split.
  - apply val_rel_le_monotone with (max m n).
    + apply Nat.le_max_l.
    + exact Hmax.
  - apply val_rel_le_monotone with (max m n).
    + apply Nat.le_max_r.
    + exact Hmax.
Qed.

(** ----------------------------------------------------------------- *)
(** * Minimum Step Preservation                                       *)
(** ----------------------------------------------------------------- *)

(** Related at either m or n implies related at min m n *)
Lemma val_rel_le_to_min : forall m n Σ T v1 v2,
  val_rel_le m Σ T v1 v2 ->
  val_rel_le (min m n) Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hm.
  apply val_rel_le_monotone with m.
  - apply Nat.le_min_l.
  - exact Hm.
Qed.

Lemma val_rel_le_to_min_r : forall m n Σ T v1 v2,
  val_rel_le n Σ T v1 v2 ->
  val_rel_le (min m n) Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hn.
  apply val_rel_le_monotone with n.
  - apply Nat.le_min_r.
  - exact Hn.
Qed.

(** End of file - ZERO ADMITS *)
