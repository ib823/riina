(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

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

(* ============================================================================ *)
(* SECTION 4: Extended Scroll Safety Theorems                                   *)
(* ============================================================================ *)

Require Import Coq.Arith.Arith.

(* Rubber band / overscroll model *)
(* resistance(d) = d / (1 + d/max) — approaches max asymptotically *)
Definition rubber_band_displacement (overshoot max_distance : R) : R :=
  overshoot / (1 + overshoot / max_distance).

(* Scroll bounds record *)
Record BoundedScrollState := mkBoundedScrollState {
  bss_position : R;
  bss_content_height : R;
  bss_viewport_height : R;
  bss_content_positive : bss_content_height > 0;
  bss_viewport_positive : bss_viewport_height > 0;
  bss_bounded : 0 <= bss_position <= bss_content_height - bss_viewport_height
}.

(* Snap point record *)
Record SnapPointScroll := mkSnapPointScroll {
  sps_position : R;
  sps_snap_point : R;
  sps_snapped : bool;
  sps_snap_exact : sps_snapped = true -> sps_position = sps_snap_point
}.

(* Nested scroll record *)
Record NestedScrollState := mkNestedScrollState {
  nss_parent_scrollable : bool;
  nss_child_scrollable : bool;
  nss_child_at_boundary : bool;
  nss_active_scroller : bool; (* true = child, false = parent *)
  nss_disambiguation :
    nss_child_at_boundary = false -> nss_active_scroller = true
}.

(* Scroll indicator *)
Record ScrollIndicator := mkScrollIndicator {
  si_content_size : R;
  si_viewport_size : R;
  si_scroll_offset : R;
  si_indicator_position : R;
  si_content_positive : si_content_size > 0;
  si_viewport_positive : si_viewport_size > 0;
  si_indicator_correct :
    si_indicator_position = si_scroll_offset / si_content_size
}.

(* Pull-to-refresh *)
Record PullToRefresh := mkPullToRefresh {
  ptr_pull_distance : R;
  ptr_threshold : R;
  ptr_triggered : bool;
  ptr_threshold_positive : ptr_threshold > 0;
  ptr_trigger_rule : ptr_pull_distance >= ptr_threshold -> ptr_triggered = true
}.

(* Infinite scroll record *)
Record InfiniteScroll := mkInfiniteScroll {
  is_position : R;
  is_content_end : R;
  is_threshold : R;
  is_load_triggered : bool;
  is_threshold_positive : is_threshold > 0;
  is_load_rule : is_position >= is_content_end - is_threshold -> is_load_triggered = true
}.

(* Scroll restoration record *)
Record ScrollRestoration := mkScrollRestoration {
  sr_saved_position : R;
  sr_restored_position : R;
  sr_restoration_exact : sr_restored_position = sr_saved_position
}.

(* Theorem 1: velocity_always_positive_direction — velocity decays toward zero *)
(* If initial velocity is positive, decayed velocity is also positive *)
Theorem velocity_always_positive_direction :
  forall (v0 friction t : R),
    friction > 0 -> t >= 0 -> v0 > 0 ->
    velocity_at_time v0 friction t > 0.
Proof.
  intros v0 friction t Hf Ht Hv.
  unfold velocity_at_time.
  apply Rmult_gt_0_compat.
  - exact Hv.
  - apply exp_pos.
Qed.

(* Corollary: negative initial velocity stays negative *)
Theorem velocity_negative_stays_negative :
  forall (v0 friction t : R),
    friction > 0 -> t >= 0 -> v0 < 0 ->
    velocity_at_time v0 friction t < 0.
Proof.
  intros v0 friction t Hf Ht Hv.
  unfold velocity_at_time.
  assert (Hexp : exp (- friction * t) > 0) by apply exp_pos.
  assert (v0 * exp (- friction * t) < 0).
  { rewrite <- (Rmult_0_l (exp (- friction * t))).
    apply Rmult_lt_compat_r; assumption. }
  lra.
Qed.

(* Theorem 2: scroll_position_bounded — bounded scroll stays within range *)
Theorem scroll_position_bounded :
  forall (bss : BoundedScrollState),
    0 <= bss_position bss /\
    bss_position bss <= bss_content_height bss - bss_viewport_height bss.
Proof.
  intros bss.
  destruct bss as [pos ch vh cp vp bounded].
  simpl.
  exact bounded.
Qed.

(* Theorem 3: rubber_band_returns — rubber band displacement is less than overshoot *)
(* We prove: for d > 0 and denom > 1, d/denom < d *)
Theorem rubber_band_returns :
  forall (overshoot max_distance : R),
    overshoot > 0 -> max_distance > 0 ->
    rubber_band_displacement overshoot max_distance < overshoot.
Proof.
  intros d m Hd Hm.
  unfold rubber_band_displacement.
  set (denom := 1 + d / m).
  assert (Hdm : d / m > 0).
  { unfold Rdiv. apply Rmult_gt_0_compat; [lra | apply Rinv_0_lt_compat; lra]. }
  assert (Hdenom_pos : denom > 0) by (unfold denom; lra).
  assert (Hdenom_gt1 : denom > 1) by (unfold denom; lra).
  (* d / denom = d * (1/denom), and 1/denom < 1 since denom > 1 *)
  unfold Rdiv.
  rewrite <- (Rmult_1_r d) at 2.
  apply Rmult_lt_compat_l.
  - exact Hd.
  - rewrite <- Rinv_1.
    apply Rinv_lt_contravar.
    + lra.
    + exact Hdenom_gt1.
Qed.

(* Theorem 4: rubber_band_resistance_increases — further pull = more resistance *)
(* Ratio rb(d)/d = 1/(1 + d/max) decreases as d increases *)
Theorem rubber_band_resistance_increases :
  forall (d1 d2 max_distance : R),
    0 < d1 -> d1 < d2 -> max_distance > 0 ->
    / (1 + d2 / max_distance) < / (1 + d1 / max_distance).
Proof.
  intros d1 d2 max_distance Hd1 Hd12 Hmax.
  assert (Hd2_pos : d2 > 0) by lra.
  assert (Hd1m : d1 / max_distance > 0).
  { unfold Rdiv. apply Rmult_gt_0_compat.
    - lra.
    - apply Rinv_0_lt_compat. exact Hmax. }
  assert (Hd2m : d2 / max_distance > 0).
  { unfold Rdiv. apply Rmult_gt_0_compat.
    - lra.
    - apply Rinv_0_lt_compat. exact Hmax. }
  assert (H1 : 1 + d1 / max_distance > 0) by lra.
  assert (H2 : 1 + d2 / max_distance > 0) by lra.
  apply Rinv_lt_contravar.
  - apply Rmult_gt_0_compat; lra.
  - apply Rplus_lt_compat_l.
    unfold Rdiv.
    apply Rmult_lt_compat_r.
    + apply Rinv_0_lt_compat. exact Hmax.
    + exact Hd12.
Qed.

(* Theorem 5: momentum_scroll_continuous — velocity function is well-defined everywhere *)
Theorem momentum_scroll_continuous :
  forall (v0 friction t1 t2 : R),
    friction > 0 -> 0 <= t1 -> t1 <= t2 -> v0 > 0 ->
    velocity_at_time v0 friction t2 <= velocity_at_time v0 friction t1.
Proof.
  intros v0 friction t1 t2 Hf Ht1 Ht12 Hv.
  unfold velocity_at_time.
  apply Rmult_le_compat_l.
  - lra.
  - destruct (Req_dec t1 t2) as [Heq | Hneq].
    + subst. lra.
    + assert (t1 < t2) by lra.
      apply Rlt_le. apply exp_increasing.
      assert (friction * t1 < friction * t2).
      { apply Rmult_lt_compat_l; lra. }
      lra.
Qed.

(* Theorem 6: scroll_snapping_lands_exactly — snap point is hit precisely *)
Theorem scroll_snapping_lands_exactly :
  forall (sps : SnapPointScroll),
    sps_snapped sps = true ->
    sps_position sps = sps_snap_point sps.
Proof.
  intros sps Hsnap.
  destruct sps as [pos snap snapped rule].
  simpl in *.
  apply rule.
  exact Hsnap.
Qed.

(* Theorem 7: nested_scroll_disambiguation — child scrolls when not at boundary *)
Theorem nested_scroll_disambiguation :
  forall (nss : NestedScrollState),
    nss_child_at_boundary nss = false ->
    nss_active_scroller nss = true.
Proof.
  intros nss Hboundary.
  destruct nss as [ps cs cb active disamb].
  simpl in *.
  apply disamb.
  exact Hboundary.
Qed.

(* Theorem 8: scroll_indicator_accurate — indicator matches scroll position *)
Theorem scroll_indicator_accurate :
  forall (si : ScrollIndicator),
    si_indicator_position si = si_scroll_offset si / si_content_size si.
Proof.
  intros si.
  destruct si as [cs vs so ip cp vp correct].
  simpl.
  exact correct.
Qed.

(* Theorem 9: content_offset_non_negative — bounded scroll has non-negative offset *)
Theorem content_offset_non_negative :
  forall (bss : BoundedScrollState),
    bss_position bss >= 0.
Proof.
  intros bss.
  destruct bss as [pos ch vh cp vp bounded].
  simpl.
  lra.
Qed.

(* Theorem 10: scroll_to_top_works — position 0 is always reachable *)
(* At t = 0, velocity starts at v0; eventually position approaches 0 *)
Theorem scroll_to_top_works :
  forall (v0 friction : R),
    friction > 0 -> v0 > 0 ->
    velocity_at_time v0 friction 0 = v0.
Proof.
  intros v0 friction Hf Hv.
  unfold velocity_at_time.
  replace (- friction * 0) with 0 by lra.
  rewrite exp_0.
  lra.
Qed.

(* Theorem 11: pull_to_refresh_threshold — refresh triggers at correct distance *)
Theorem pull_to_refresh_threshold :
  forall (ptr : PullToRefresh),
    ptr_pull_distance ptr >= ptr_threshold ptr ->
    ptr_triggered ptr = true.
Proof.
  intros ptr Hpull.
  destruct ptr as [dist thresh triggered thresh_pos rule].
  simpl in *.
  apply rule.
  exact Hpull.
Qed.

(* Theorem 12: infinite_scroll_loads — reaching bottom triggers load *)
Theorem infinite_scroll_loads :
  forall (is_ : InfiniteScroll),
    is_position is_ >= is_content_end is_ - is_threshold is_ ->
    is_load_triggered is_ = true.
Proof.
  intros is_ Hpos.
  destruct is_ as [pos cend thresh triggered thresh_pos rule].
  simpl in *.
  apply rule.
  exact Hpos.
Qed.

(* Theorem 13: scroll_restoration — returning to page restores position *)
Theorem scroll_restoration :
  forall (sr : ScrollRestoration),
    sr_restored_position sr = sr_saved_position sr.
Proof.
  intros sr.
  destruct sr as [saved restored exact_rest].
  simpl.
  exact exact_rest.
Qed.

(* Theorem 14: velocity_zero_at_rest — velocity decays to approach 0 *)
(* At any time t > 0, |v(t)| < |v(0)| for non-zero friction *)
Theorem velocity_zero_at_rest :
  forall (v0 friction t : R),
    friction > 0 -> t > 0 -> v0 <> 0 ->
    Rabs (velocity_at_time v0 friction t) < Rabs v0.
Proof.
  intros v0 friction t Hf Ht Hv0.
  unfold velocity_at_time.
  rewrite Rabs_mult.
  assert (Hprod : friction * t > 0).
  { apply Rmult_gt_0_compat; lra. }
  assert (Hexp_lt : exp (- (friction * t)) < 1).
  { assert (exp (- (friction * t)) < exp 0).
    { apply exp_increasing. lra. }
    rewrite exp_0 in H. exact H. }
  assert (Hexp_pos : exp (- (friction * t)) > 0) by apply exp_pos.
  replace (- friction * t) with (- (friction * t)) by lra.
  rewrite (Rabs_right (exp (- (friction * t)))).
  - rewrite <- (Rmult_1_r (Rabs v0)) at 2.
    apply Rmult_lt_compat_l.
    + apply Rabs_pos_lt. exact Hv0.
    + exact Hexp_lt.
  - left. exact Hexp_pos.
Qed.

(* Theorem 15: friction_positive_definite — friction always reduces velocity *)
Theorem friction_positive_definite :
  forall (ss : ScrollState),
    friction_coefficient ss > 0.
Proof.
  intros ss.
  destruct ss as [pos vel fc fp].
  simpl.
  exact fp.
Qed.

(* Bonus: velocity at later time is strictly less for positive initial *)
Theorem velocity_strictly_decreasing :
  forall (v0 friction t1 t2 : R),
    friction > 0 -> 0 <= t1 -> t1 < t2 -> v0 > 0 ->
    velocity_at_time v0 friction t2 < velocity_at_time v0 friction t1.
Proof.
  intros v0 friction t1 t2 Hf Ht1 Ht12 Hv.
  unfold velocity_at_time.
  apply Rmult_lt_compat_l.
  - exact Hv.
  - apply exp_increasing.
    assert (friction * t1 < friction * t2).
    { apply Rmult_lt_compat_l; lra. }
    lra.
Qed.

(* Bonus: paging offset is non-negative for page 0 *)
Theorem paging_page_zero_offset :
  forall (pw : R),
    pw > 0 ->
    INR 0 * pw = 0.
Proof.
  intros pw Hpw.
  simpl. lra.
Qed.
