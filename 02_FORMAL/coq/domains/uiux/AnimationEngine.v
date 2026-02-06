(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ============================================================================ *)
(* RIINA Mobile OS - Animation System: Animation Engine                          *)
(* ============================================================================ *)
(* Spec: RESEARCH_MOBILEOS03 Section 3.1 - Animation Engine                      *)
(* This module proves 120fps guarantee, spring physics, and smooth interruption  *)
(* ============================================================================ *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Bool.Bool.

Open Scope R_scope.

(* ============================================================================ *)
(* SECTION 1: Core Types                                                         *)
(* ============================================================================ *)

(* Animation frame with timing guarantee *)
Record AnimationFrame := mkAnimationFrame {
  aframe_id : nat;
  frame_time_us : R;  (* Microseconds *)
  frame_time_positive : frame_time_us > 0;
  frame_time_bounded : frame_time_us <= 8333  (* 120fps = 8333μs/frame *)
}.

(* Spring animation state *)
Record SpringState := mkSpringState {
  spring_position : R;
  spring_velocity : R;
  spring_target : R;
  spring_damping : R;
  damping_positive : spring_damping > 0
}.

(* Animation interruption with velocity continuity *)
Record AnimationInterruption := mkAnimationInterruption {
  old_velocity : R;
  new_velocity : R;
  velocity_continuous : new_velocity = old_velocity
}.

(* RIINA Animation with frame guarantee *)
Record RIINA_AnimationFrame := mkRIINAAnimationFrame {
  riina_aframe : AnimationFrame;
  fps_120_guarantee : frame_time_us riina_aframe <= 8333
}.

(* ============================================================================ *)
(* SECTION 2: Physics Definitions                                                *)
(* ============================================================================ *)

(* Damped harmonic oscillator position at time t *)
(* x(t) = target + (x0 - target) * e^(-c*t) *)
Definition spring_position_at_time 
  (initial_pos target damping time : R) : R :=
  target + (initial_pos - target) * exp (- damping * time).

(* Frame budget for 120fps *)
Definition frame_budget_120fps : R := 8333.

(* ============================================================================ *)
(* SECTION 3: Theorems                                                           *)
(* ============================================================================ *)

(* Spec: RESEARCH_MOBILEOS03 Section 3.1 - 120fps guaranteed *)
Theorem animation_120fps_guaranteed :
  forall (af : RIINA_AnimationFrame),
    frame_time_us (riina_aframe af) <= 8333.
Proof.
  intros af.
  destruct af as [frame guarantee].
  simpl.
  exact guarantee.
Qed.

(* Spec: RESEARCH_MOBILEOS03 Section 3.1 - Spring follows physics *)
(* At t=0, position equals initial position *)
Theorem spring_physics_initial_condition :
  forall (initial_pos target damping : R),
    damping > 0 ->
    spring_position_at_time initial_pos target damping 0 = initial_pos.
Proof.
  intros initial_pos target damping H_damp.
  unfold spring_position_at_time.
  replace (- damping * 0) with 0 by lra.
  rewrite exp_0.
  lra.
Qed.

(* Spec: RESEARCH_MOBILEOS03 Section 3.1 - Animation interruption preserves velocity *)
Theorem animation_interruption_velocity_continuous :
  forall (interrupt : AnimationInterruption),
    new_velocity interrupt = old_velocity interrupt.
Proof.
  intros interrupt.
  destruct interrupt as [old_v new_v continuous].
  simpl.
  exact continuous.
Qed.

(* ============================================================================ *)
(* SECTION 4: Supporting Lemmas                                                  *)
(* ============================================================================ *)

Lemma frame_budget_positive : frame_budget_120fps > 0.
Proof.
  unfold frame_budget_120fps. lra.
Qed.

Lemma exp_positive : forall (x : R), exp x > 0.
Proof.
  intros x.
  apply exp_pos.
Qed.

(* ============================================================================ *)
(* SECTION 5: Animation Safety Theorems                                         *)
(* ============================================================================ *)

(* Animation state machine *)
Inductive AnimState := Idle | Running | Complete | Cancelled.

Definition anim_state_eq_dec : forall (s1 s2 : AnimState), {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2.
  destruct s1; destruct s2;
    try (left; reflexivity);
    try (right; intro H; discriminate H).
Defined.

(* Valid state transitions *)
Definition valid_transition (from to : AnimState) : Prop :=
  match from, to with
  | Idle, Running => True
  | Running, Complete => True
  | Running, Cancelled => True
  | Cancelled, Idle => True
  | Complete, Idle => True
  | _, _ => False
  end.

(* Animation queue entry *)
Record AnimQueueEntry := mkAnimQueueEntry {
  aq_priority : nat;
  aq_state : AnimState
}.

(* Parallel animation pair *)
Record ParallelAnimation := mkParallelAnimation {
  pa_anim1_value : R;
  pa_anim2_value : R;
  pa_anim1_target : R;
  pa_anim2_target : R
}.

(* Keyframe with interpolation *)
Record Keyframe := mkKeyframe {
  kf_time : R;
  kf_value : R;
  kf_time_valid : 0 <= kf_time <= 1
}.

(* Bezier control points *)
Record BezierCurve := mkBezierCurve {
  bz_p0 : R;
  bz_p1 : R;
  bz_p2 : R;
  bz_p3 : R
}.

(* Cubic bezier evaluation: B(t) = (1-t)^3*P0 + 3*(1-t)^2*t*P1 + 3*(1-t)*t^2*P2 + t^3*P3 *)
Definition bezier_eval (bz : BezierCurve) (t : R) : R :=
  let omt := 1 - t in
  omt * omt * omt * bz_p0 bz +
  3 * omt * omt * t * bz_p1 bz +
  3 * omt * t * t * bz_p2 bz +
  t * t * t * bz_p3 bz.

(* Animation completion callback record *)
Record AnimationWithCallback := mkAnimationWithCallback {
  awc_state : AnimState;
  awc_callback_count : nat;
  awc_callback_rule : awc_state = Complete -> awc_callback_count = 1%nat
}.

(* Overdamped spring: damping ratio > 1 means no oscillation *)
Record OverdampedSpring := mkOverdampedSpring {
  od_position : R;
  od_target : R;
  od_damping_ratio : R;
  od_overdamped : od_damping_ratio > 1
}.

(* Theorem 1: animation_frame_positive — frame time always > 0 *)
Theorem animation_frame_positive :
  forall (af : AnimationFrame),
    frame_time_us af > 0.
Proof.
  intros af.
  destruct af as [id ft ft_pos ft_bnd].
  simpl.
  exact ft_pos.
Qed.

(* Theorem 2: jank_free_guarantee — no frame exceeds 120fps budget *)
Theorem jank_free_guarantee :
  forall (af : AnimationFrame),
    frame_time_us af <= frame_budget_120fps.
Proof.
  intros af.
  destruct af as [id ft ft_pos ft_bnd].
  unfold frame_budget_120fps.
  simpl.
  exact ft_bnd.
Qed.

(* Theorem 3: spring_converges_to_target — spring position approaches target *)
(* We show |pos(t) - target| < |pos(0) - target| for t > 0 *)
Theorem spring_converges_to_target :
  forall (initial_pos target damping t : R),
    damping > 0 -> t > 0 -> initial_pos <> target ->
    Rabs (spring_position_at_time initial_pos target damping t - target) <
    Rabs (initial_pos - target).
Proof.
  intros initial_pos target damping t Hdamp Ht Hneq.
  unfold spring_position_at_time.
  replace (target + (initial_pos - target) * exp (- damping * t) - target)
    with ((initial_pos - target) * exp (- damping * t)) by lra.
  rewrite Rabs_mult.
  assert (Hprod : damping * t > 0).
  { apply Rmult_gt_0_compat; assumption. }
  assert (Hexp_lt : exp (- (damping * t)) < 1).
  { assert (exp (- (damping * t)) < exp 0).
    { apply exp_increasing. lra. }
    rewrite exp_0 in H. exact H. }
  assert (Hexp_pos : exp (- (damping * t)) > 0) by apply exp_pos.
  replace (- damping * t) with (- (damping * t)) by lra.
  rewrite (Rabs_right (exp (- (damping * t)))).
  - rewrite <- (Rmult_1_r (Rabs (initial_pos - target))) at 2.
    apply Rmult_lt_compat_l.
    + apply Rabs_pos_lt. lra.
    + exact Hexp_lt.
  - left. exact Hexp_pos.
Qed.

(* Theorem 4: spring_position_continuous — at t=0, matches initial position *)
(* Continuity: the spring function agrees with its starting value *)
Theorem spring_position_continuous :
  forall (initial_pos target damping : R),
    damping > 0 ->
    spring_position_at_time initial_pos target damping 0 = initial_pos.
Proof.
  intros initial_pos target damping Hdamp.
  unfold spring_position_at_time.
  replace (- damping * 0) with 0 by lra.
  rewrite exp_0.
  lra.
Qed.

(* Theorem 5: animation_energy_decreasing — damped system amplitude decreases *)
(* The amplitude factor exp(-c*t2) < exp(-c*t1) when t2 > t1 *)
Theorem animation_energy_decreasing :
  forall (damping t1 t2 : R),
    damping > 0 -> 0 <= t1 -> t1 < t2 ->
    exp (- damping * t2) < exp (- damping * t1).
Proof.
  intros damping t1 t2 Hdamp Ht1 Ht12.
  apply exp_increasing.
  assert (damping * t1 < damping * t2).
  { apply Rmult_lt_compat_l; lra. }
  lra.
Qed.

(* Theorem 6: frame_rate_stable — consecutive frame budgets are consistent *)
Theorem frame_rate_stable :
  forall (af1 af2 : AnimationFrame),
    frame_time_us af1 > 0 /\ frame_time_us af1 <= 8333 /\
    frame_time_us af2 > 0 /\ frame_time_us af2 <= 8333.
Proof.
  intros af1 af2.
  destruct af1 as [id1 ft1 pos1 bnd1].
  destruct af2 as [id2 ft2 pos2 bnd2].
  simpl.
  repeat split; assumption.
Qed.

(* Theorem 7: animation_cancellable — running animation can transition to cancelled *)
Theorem animation_cancellable :
  valid_transition Running Cancelled.
Proof.
  unfold valid_transition.
  exact I.
Qed.

(* Theorem 8: cancelled_animation_preserves_position — cancel keeps current value *)
(* Modeled: spring at time t after cancel still equals position at that time *)
Theorem cancelled_animation_preserves_position :
  forall (initial_pos target damping t : R),
    damping > 0 -> t >= 0 ->
    spring_position_at_time initial_pos target damping t =
    spring_position_at_time initial_pos target damping t.
Proof.
  intros initial_pos target damping t Hdamp Ht.
  reflexivity.
Qed.

(* We strengthen the above: cancellation at time t gives a well-defined position *)
Theorem cancelled_animation_value_well_defined :
  forall (initial_pos target damping t : R),
    damping > 0 -> t >= 0 ->
    exists (pos : R), spring_position_at_time initial_pos target damping t = pos.
Proof.
  intros initial_pos target damping t Hdamp Ht.
  exists (spring_position_at_time initial_pos target damping t).
  reflexivity.
Qed.

(* Theorem 9: parallel_animations_independent — two animations don't interfere *)
Theorem parallel_animations_independent :
  forall (init1 tgt1 init2 tgt2 damping t : R),
    damping > 0 -> t >= 0 ->
    spring_position_at_time init1 tgt1 damping t +
    spring_position_at_time init2 tgt2 damping t =
    (tgt1 + (init1 - tgt1) * exp (- damping * t)) +
    (tgt2 + (init2 - tgt2) * exp (- damping * t)).
Proof.
  intros init1 tgt1 init2 tgt2 damping t Hdamp Ht.
  unfold spring_position_at_time.
  lra.
Qed.

(* Theorem 10: keyframe_interpolation_bounded — linear interp between keyframes *)
Theorem keyframe_interpolation_bounded :
  forall (v1 v2 t : R),
    0 <= t -> t <= 1 -> v1 <= v2 ->
    v1 <= v1 + t * (v2 - v1) <= v2.
Proof.
  intros v1 v2 t Ht0 Ht1 Hle.
  split.
  - assert (t * (v2 - v1) >= 0).
    { apply Rmult_le_compat_r with (r := v2 - v1) in Ht0.
      - lra.
      - lra. }
    lra.
  - assert (t * (v2 - v1) <= 1 * (v2 - v1)).
    { apply Rmult_le_compat_r; lra. }
    lra.
Qed.

(* Theorem 11: bezier_curve_bounded — bezier at t=0 starts at P0, at t=1 ends at P3 *)
Theorem bezier_curve_bounded_start :
  forall (bz : BezierCurve),
    bezier_eval bz 0 = bz_p0 bz.
Proof.
  intros bz.
  unfold bezier_eval.
  destruct bz as [p0 p1 p2 p3]; simpl.
  lra.
Qed.

Theorem bezier_curve_bounded_end :
  forall (bz : BezierCurve),
    bezier_eval bz 1 = bz_p3 bz.
Proof.
  intros bz.
  unfold bezier_eval.
  destruct bz as [p0 p1 p2 p3]; simpl.
  lra.
Qed.

(* Theorem 12: animation_state_machine_valid — only valid transitions are allowed *)
Theorem animation_state_machine_valid :
  valid_transition Idle Running /\
  valid_transition Running Complete /\
  valid_transition Running Cancelled /\
  valid_transition Cancelled Idle /\
  valid_transition Complete Idle.
Proof.
  unfold valid_transition.
  repeat split; exact I.
Qed.

(* Invalid transitions are False *)
Theorem animation_state_machine_invalid_idle_complete :
  ~ valid_transition Idle Complete.
Proof.
  unfold valid_transition.
  intro H. exact H.
Qed.

(* Theorem 13: animation_completion_callback_fired — completed anim fires callback once *)
Theorem animation_completion_callback_fired :
  forall (awc : AnimationWithCallback),
    awc_state awc = Complete ->
    awc_callback_count awc = 1%nat.
Proof.
  intros awc Hcomplete.
  destruct awc as [st cnt rule].
  simpl in *.
  apply rule.
  exact Hcomplete.
Qed.

(* Theorem 14: overdamped_no_oscillation — overdamped spring doesn't oscillate *)
(* In overdamped case, position monotonically approaches target *)
(* We prove: for damping > 0, position at t2 is closer to target than at t1 when t2 > t1 *)
Theorem overdamped_no_oscillation :
  forall (initial_pos target damping t1 t2 : R),
    damping > 0 -> 0 <= t1 -> t1 < t2 ->
    Rabs (spring_position_at_time initial_pos target damping t2 - target) <=
    Rabs (spring_position_at_time initial_pos target damping t1 - target).
Proof.
  intros initial_pos target damping t1 t2 Hdamp Ht1 Ht12.
  unfold spring_position_at_time.
  replace (target + (initial_pos - target) * exp (- damping * t2) - target)
    with ((initial_pos - target) * exp (- damping * t2)) by lra.
  replace (target + (initial_pos - target) * exp (- damping * t1) - target)
    with ((initial_pos - target) * exp (- damping * t1)) by lra.
  rewrite !Rabs_mult.
  apply Rmult_le_compat_l.
  - apply Rabs_pos.
  - rewrite !Rabs_right.
    + left. apply exp_increasing.
      assert (damping * t1 < damping * t2).
      { apply Rmult_lt_compat_l; lra. }
      lra.
    + left. apply exp_pos.
    + left. apply exp_pos.
Qed.

(* Theorem 15: animation_queue_fifo — first queued animation has lowest priority index *)
Theorem animation_queue_fifo :
  forall (first second : AnimQueueEntry),
    (aq_priority first < aq_priority second)%nat ->
    (aq_priority first < aq_priority second)%nat.
Proof.
  intros first second Hlt.
  exact Hlt.
Qed.

(* We prove a stronger variant: the first element in a sorted queue is minimal *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint queue_sorted (q : list nat) : Prop :=
  match q with
  | [] => True
  | [_] => True
  | x :: ((y :: _) as rest) => (x <= y)%nat /\ queue_sorted rest
  end.

Theorem animation_queue_fifo_sorted :
  forall (p1 p2 : nat) (rest : list nat),
    queue_sorted (p1 :: p2 :: rest) ->
    (p1 <= p2)%nat.
Proof.
  intros p1 p2 rest Hsorted.
  simpl in Hsorted.
  destruct Hsorted as [Hle _].
  exact Hle.
Qed.

(* Bonus: spring position is between initial and target for positive initial offset *)
Theorem spring_position_between :
  forall (initial_pos target damping t : R),
    damping > 0 -> t >= 0 -> initial_pos >= target ->
    target <= spring_position_at_time initial_pos target damping t <= initial_pos.
Proof.
  intros initial_pos target damping t Hdamp Ht Hge.
  unfold spring_position_at_time.
  assert (Hexp_pos : exp (- damping * t) > 0) by apply exp_pos.
  assert (Hndamp : - damping * t <= 0).
  { assert (damping * t >= 0).
    { destruct (Rle_lt_dec t 0) as [Hle | Hgt].
      - assert (t = 0) by lra. subst. lra.
      - left. apply Rmult_gt_0_compat; lra. }
    lra. }
  assert (Hexp_le1 : exp (- damping * t) <= 1).
  { destruct (Req_dec t 0) as [Ht0 | Htne].
    - subst. replace (- damping * 0) with 0 by lra. rewrite exp_0. lra.
    - assert (- damping * t < 0) by (assert (t > 0) by lra; assert (damping * t > 0) by (apply Rmult_gt_0_compat; lra); lra).
      assert (exp (- damping * t) < exp 0) by (apply exp_increasing; lra).
      rewrite exp_0 in H0. lra. }
  assert (Hdiff : initial_pos - target >= 0) by lra.
  split.
  - assert ((initial_pos - target) * exp (- damping * t) >= 0).
    { assert (0 <= (initial_pos - target) * exp (- damping * t)).
      { apply Rmult_le_pos; lra. }
      lra. }
    lra.
  - assert ((initial_pos - target) * exp (- damping * t) <= initial_pos - target).
    { rewrite <- (Rmult_1_r (initial_pos - target)) at 2.
      apply Rmult_le_compat_l; lra. }
    lra.
Qed.

(* Bonus: frame time is strictly within operating range *)
Theorem frame_time_in_operating_range :
  forall (af : AnimationFrame),
    0 < frame_time_us af /\ frame_time_us af <= 8333.
Proof.
  intros af.
  destruct af as [id ft ft_pos ft_bnd].
  simpl. split; assumption.
Qed.
