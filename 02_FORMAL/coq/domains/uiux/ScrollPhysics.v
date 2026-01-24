(* ============================================================================ *)
(* RIINA Mobile OS - Animation System: Scroll Physics                            *)
(* ============================================================================ *)
(* Spec: RESEARCH_MOBILEOS03 Section 3.3 - Scroll Physics                        *)
(* This module proves natural deceleration and paging exactness                  *)
(* ============================================================================ *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Bool.Bool.

Open Scope R_scope.

(* ============================================================================ *)
(* SECTION 1: Core Types                                                         *)
(* ============================================================================ *)

(* Scroll state with velocity *)
Record ScrollState := mkScrollState {
  scroll_position : R;
  scroll_velocity : R;
  friction_coefficient : R;
  friction_positive : friction_coefficient > 0
}.

(* Deceleration physics: v(t) = v0 * e^(-μ*t) *)
Definition velocity_at_time (v0 friction t : R) : R :=
  v0 * exp (- friction * t).

(* Paging with exact boundaries *)
Record PagingState := mkPagingState {
  page_width : R;
  current_offset : R;
  target_page : nat;
  page_width_positive : page_width > 0;
  offset_exact : current_offset = INR target_page * page_width
}.

(* ============================================================================ *)
(* SECTION 2: Theorems                                                           *)
(* ============================================================================ *)

(* Spec: RESEARCH_MOBILEOS03 Section 3.3 - Velocity at t=0 equals initial *)
Theorem deceleration_initial_velocity :
  forall (v0 friction : R),
    friction > 0 ->
    velocity_at_time v0 friction 0 = v0.
Proof.
  intros v0 friction H_friction.
  unfold velocity_at_time.
  replace (- friction * 0) with 0 by lra.
  rewrite exp_0.
  lra.
Qed.

(* Spec: RESEARCH_MOBILEOS03 Section 3.3 - Paging lands on exact boundary *)
Theorem paging_exact_boundary :
  forall (ps : PagingState),
    current_offset ps = INR (target_page ps) * page_width ps.
Proof.
  intros ps.
  destruct ps as [pw co tp pw_pos exact].
  simpl.
  exact exact.
Qed.

(* ============================================================================ *)
(* SECTION 3: Supporting Lemmas                                                  *)
(* ============================================================================ *)

Lemma velocity_decays : forall (v0 friction t : R),
  friction > 0 -> t > 0 -> v0 > 0 ->
  velocity_at_time v0 friction t < v0.
Proof.
  intros v0 friction t H_f H_t H_v.
  unfold velocity_at_time.
  (* exp(- friction * t) < 1 when friction * t > 0 *)
  assert (H_prod: friction * t > 0) by (apply Rmult_gt_0_compat; assumption).
  assert (H_neg: - (friction * t) < 0) by lra.
  assert (H_exp: exp (- (friction * t)) < exp 0).
  { apply exp_increasing. exact H_neg. }
  rewrite exp_0 in H_exp.
  replace (- friction * t) with (- (friction * t)) by lra.
  (* v0 * exp(...) < v0 * 1 = v0 *)
  rewrite <- (Rmult_1_r v0) at 2.
  apply Rmult_lt_compat_l; assumption.
Qed.

Lemma page_width_positive_lemma : forall (ps : PagingState),
  page_width ps > 0.
Proof.
  intros ps.
  destruct ps as [pw co tp pw_pos exact].
  simpl.
  exact pw_pos.
Qed.
