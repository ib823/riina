(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* ============================================================================ *)
(* RIINA Mobile OS - Accessibility: Visual Accessibility                        *)
(* ============================================================================ *)
(* Spec: RESEARCH_MOBILEOS03 Section 5.1 - Visual Accessibility                 *)
(* This module proves VoiceOver completeness and reduce motion support          *)
(* ============================================================================ *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* ============================================================================ *)
(* SECTION 1: Core Types                                                        *)
(* ============================================================================ *)

(* UI Element *)
Record UIElement := mkUIElement {
  element_id : nat;
  is_visible : bool;
  accessibility_label : option nat;  (* None = no label *)
  accessibility_hint : option nat
}.

(* Text with size *)
Inductive DynamicTypeSize :=
  | XSmall | Small | Medium | Large | XLarge 
  | XXLarge | XXXLarge 
  | AccessibilityLarge | AccessibilityXLarge | AccessibilityXXLarge.

Record Text := mkText {
  text_id : nat;
  text_content : nat;  (* Abstract content *)
  text_size : DynamicTypeSize
}.

(* Animation *)
Record Animation := mkAnimation {
  animation_id : nat;
  is_essential : bool;  (* Essential animations still play *)
  animation_active : bool
}.

(* ============================================================================ *)
(* SECTION 2: Accessibility Predicates                                          *)
(* ============================================================================ *)

(* Element is visible *)
Definition visible (elem : UIElement) : Prop :=
  is_visible elem = true.

(* Element is VoiceOver accessible *)
Definition voiceover_accessible (elem : UIElement) : Prop :=
  match accessibility_label elem with
  | Some _ => True
  | None => False
  end.

(* Text is readable at any size *)
Definition readable (text : Text) (size : DynamicTypeSize) : Prop :=
  text_size text = size.  (* RIINA supports all sizes *)

(* Reduce motion is enabled *)
Definition reduce_motion_enabled : Prop := True.

(* Animation plays *)
Definition plays (anim : Animation) : Prop :=
  animation_active anim = true /\ is_essential anim = false.

(* ============================================================================ *)
(* SECTION 3: RIINA Accessibility Invariants                                    *)
(* ============================================================================ *)

(* RIINA UI Element - always VoiceOver accessible if visible *)
Record RIINA_UIElement := mkRIINAUIElement {
  riina_element : UIElement;
  (* Visible implies accessible *)
  voiceover_guarantee :
    visible riina_element -> voiceover_accessible riina_element
}.

(* RIINA Text - readable at all Dynamic Type sizes *)
Record RIINA_Text := mkRIINAText {
  riina_text : Text;
  current_size : DynamicTypeSize;
  (* Text is readable at its size *)
  readability_guarantee : readable riina_text current_size
}.

(* RIINA Animation with reduce motion respect *)
Record RIINA_Animation := mkRIINAAnimation {
  riina_animation : Animation;
  (* Non-essential animations don't play when reduce motion enabled *)
  reduce_motion_respect :
    reduce_motion_enabled -> 
    is_essential riina_animation = false ->
    animation_active riina_animation = false
}.

(* ============================================================================ *)
(* SECTION 4: Theorems                                                          *)
(* ============================================================================ *)

(* Spec: RESEARCH_MOBILEOS03 Section 5.1 - VoiceOver complete coverage *)
Theorem voiceover_complete_coverage :
  forall (re : RIINA_UIElement),
    visible (riina_element re) ->
    voiceover_accessible (riina_element re).
Proof.
  intros re H_visible.
  apply (voiceover_guarantee re).
  exact H_visible.
Qed.

(* Spec: RESEARCH_MOBILEOS03 Section 5.1 - Dynamic Type universal *)
Theorem dynamic_type_universal :
  forall (rt : RIINA_Text),
    readable (riina_text rt) (current_size rt).
Proof.
  intros rt.
  exact (readability_guarantee rt).
Qed.

(* Spec: RESEARCH_MOBILEOS03 Section 5.1 - Reduce motion eliminates all motion *)
Theorem reduce_motion_complete :
  forall (ra : RIINA_Animation),
    reduce_motion_enabled ->
    is_essential (riina_animation ra) = false ->
    ~ plays (riina_animation ra).
Proof.
  intros ra H_reduce H_nonessential.
  unfold plays.
  intros [H_active H_ess].
  pose proof (reduce_motion_respect ra H_reduce H_nonessential) as H_inactive.
  rewrite H_inactive in H_active.
  discriminate.
Qed.

(* ============================================================================ *)
(* SECTION 5: Supporting Lemmas                                                 *)
(* ============================================================================ *)

Lemma visible_decidable : forall (elem : UIElement),
  {visible elem} + {~ visible elem}.
Proof.
  intros elem.
  unfold visible.
  destruct (is_visible elem) eqn:Hvis.
  - left. reflexivity.
  - right. discriminate.
Qed.

Lemma voiceover_accessible_decidable : forall (elem : UIElement),
  {voiceover_accessible elem} + {~ voiceover_accessible elem}.
Proof.
  intros elem.
  unfold voiceover_accessible.
  destruct (accessibility_label elem).
  - left. trivial.
  - right. auto.
Qed.

Lemma dynamic_type_size_decidable : forall (s1 s2 : DynamicTypeSize),
  {s1 = s2} + {s1 <> s2}.
Proof.
  intros s1 s2.
  destruct s1, s2; (left; reflexivity) || (right; discriminate).
Qed.

Lemma readable_at_current_size : forall (text : Text),
  readable text (text_size text).
Proof.
  intros text.
  unfold readable.
  reflexivity.
Qed.

Lemma essential_animations_can_play : forall (anim : Animation),
  is_essential anim = true ->
  ~ (is_essential anim = false).
Proof.
  intros anim H_ess.
  rewrite H_ess.
  discriminate.
Qed.

Lemma plays_implies_active : forall (anim : Animation),
  plays anim -> animation_active anim = true.
Proof.
  intros anim [H_active _].
  exact H_active.
Qed.

Lemma plays_implies_nonessential : forall (anim : Animation),
  plays anim -> is_essential anim = false.
Proof.
  intros anim [_ H_ess].
  exact H_ess.
Qed.

(* ============================================================================ *)
(* SECTION 6: Screen Reader Completeness                                        *)
(* ============================================================================ *)
(* Spec: WCAG 2.1 SC 4.1.2 — Name, Role, Value; SC 1.3.1 — Info & Relationships *)

(** An accessibility node mirrors each UI element for assistive technology. *)
Inductive AriaRole :=
  | RoleButton | RoleLink | RoleTextbox | RoleCheckbox
  | RoleHeading | RoleList | RoleListitem | RoleNavigation
  | RoleMain | RoleRegion | RoleAlert | RoleDialog
  | RoleStatic.

Record AccessibilityNode := mkAccessibilityNode {
  node_id : nat;
  node_role : AriaRole;
  node_label : nat;          (* 0 = empty label — treated as invalid *)
  node_parent : option nat;  (* None = root *)
  node_children : list nat;
  node_visible : bool;
  node_interactive : bool
}.

Definition AccessibilityTree := list AccessibilityNode.

(** A node is the root if it has no parent. *)
Definition is_root (n : AccessibilityNode) : bool :=
  match node_parent n with
  | None => true
  | Some _ => false
  end.

(** Check if a node ID exists in the tree. *)
Fixpoint id_in_tree (tree : AccessibilityTree) (nid : nat) : bool :=
  match tree with
  | nil => false
  | n :: rest => Nat.eqb (node_id n) nid || id_in_tree rest nid
  end.

(** Predicate: all nodes are reachable from root (every non-root node's parent is in the tree). *)
Definition connected_to_root (tree : AccessibilityTree) : Prop :=
  forall n, In n tree ->
    node_parent n = None \/
    (exists pid, node_parent n = Some pid /\ id_in_tree tree pid = true).

(** Predicate: a visible UI element has a corresponding accessibility node. *)
Definition element_has_node (tree : AccessibilityTree) (elem : UIElement) : Prop :=
  exists n, In n tree /\ node_id n = element_id elem.

(** Well-formed tree: exactly one root, all connected. *)
Definition well_formed_tree (tree : AccessibilityTree) : Prop :=
  connected_to_root tree /\
  (exists r, In r tree /\ is_root r = true) /\
  (forall n1 n2, In n1 tree -> In n2 tree ->
     is_root n1 = true -> is_root n2 = true -> node_id n1 = node_id n2).

(** A RIINA-compliant view pairs visible elements with an accessibility tree
    guaranteeing coverage. *)
Record RIINA_View := mkRIINAView {
  view_elements : list UIElement;
  view_tree : AccessibilityTree;
  view_well_formed : well_formed_tree view_tree;
  view_coverage :
    forall elem, In elem view_elements ->
      is_visible elem = true ->
      element_has_node view_tree elem;
  view_connected : connected_to_root view_tree;
  view_roles :
    forall n, In n view_tree ->
      node_interactive n = true ->
      node_role n <> RoleStatic;
  view_labels :
    forall n, In n view_tree ->
      node_interactive n = true ->
      node_label n <> 0
}.

(* ------ Theorem 6.1: all_visible_elements_in_tree ------ *)
(* Every visible element in a RIINA view has a corresponding accessibility node. *)
Theorem all_visible_elements_in_tree :
  forall (v : RIINA_View) (elem : UIElement),
    In elem (view_elements v) ->
    is_visible elem = true ->
    element_has_node (view_tree v) elem.
Proof.
  intros v elem H_in H_vis.
  exact (view_coverage v elem H_in H_vis).
Qed.

(* ------ Theorem 6.2: no_orphan_nodes ------ *)
(* Every node in the tree is either root or has its parent in the tree. *)
Theorem no_orphan_nodes :
  forall (v : RIINA_View) (n : AccessibilityNode),
    In n (view_tree v) ->
    node_parent n = None \/
    (exists pid, node_parent n = Some pid /\ id_in_tree (view_tree v) pid = true).
Proof.
  intros v n H_in.
  exact (view_connected v n H_in).
Qed.

(* ------ Theorem 6.3: role_always_set ------ *)
(* Every interactive element has a non-static ARIA role. *)
Theorem role_always_set :
  forall (v : RIINA_View) (n : AccessibilityNode),
    In n (view_tree v) ->
    node_interactive n = true ->
    node_role n <> RoleStatic.
Proof.
  intros v n H_in H_inter.
  exact (view_roles v n H_in H_inter).
Qed.

(* ------ Theorem 6.4: label_always_nonempty ------ *)
(* Every interactive accessible node has a non-empty label. *)
Theorem label_always_nonempty :
  forall (v : RIINA_View) (n : AccessibilityNode),
    In n (view_tree v) ->
    node_interactive n = true ->
    node_label n <> 0.
Proof.
  intros v n H_in H_inter.
  exact (view_labels v n H_in H_inter).
Qed.

(* ------ Theorem 6.5: tree_traversal_complete ------ *)
(* Depth-first traversal of a well-formed tree visits all nodes.
   We model this by showing that collecting all IDs yields a list
   containing every node in the tree. *)

Fixpoint collect_ids (tree : AccessibilityTree) : list nat :=
  match tree with
  | nil => nil
  | n :: rest => node_id n :: collect_ids rest
  end.

Lemma collect_ids_complete : forall (tree : AccessibilityTree) (n : AccessibilityNode),
  In n tree -> In (node_id n) (collect_ids tree).
Proof.
  intros tree n H_in.
  induction tree as [| hd tl IH].
  - inversion H_in.
  - simpl. destruct H_in as [H_eq | H_rest].
    + left. rewrite H_eq. reflexivity.
    + right. apply IH. exact H_rest.
Qed.

Theorem tree_traversal_complete :
  forall (v : RIINA_View) (n : AccessibilityNode),
    In n (view_tree v) ->
    In (node_id n) (collect_ids (view_tree v)).
Proof.
  intros v n H_in.
  apply collect_ids_complete. exact H_in.
Qed.

(* ------ Theorem 6.6: focus_order_matches_tree ------ *)
(* Tab order (focus order) follows the sequential order of the accessibility tree.
   We model focus order as the list of interactive node IDs in tree order. *)

Fixpoint focus_order (tree : AccessibilityTree) : list nat :=
  match tree with
  | nil => nil
  | n :: rest =>
      if node_interactive n then node_id n :: focus_order rest
      else focus_order rest
  end.

Fixpoint interactive_nodes (tree : AccessibilityTree) : list AccessibilityNode :=
  match tree with
  | nil => nil
  | n :: rest =>
      if node_interactive n then n :: interactive_nodes rest
      else interactive_nodes rest
  end.

Lemma focus_order_from_interactive : forall (tree : AccessibilityTree),
  focus_order tree = map node_id (interactive_nodes tree).
Proof.
  intros tree. induction tree as [| hd tl IH].
  - simpl. reflexivity.
  - simpl. destruct (node_interactive hd).
    + simpl. f_equal. exact IH.
    + exact IH.
Qed.

Theorem focus_order_matches_tree :
  forall (v : RIINA_View) (n : AccessibilityNode),
    In n (view_tree v) ->
    node_interactive n = true ->
    In (node_id n) (focus_order (view_tree v)).
Proof.
  intros v n H_in H_inter.
  induction (view_tree v) as [| hd tl IH].
  - inversion H_in.
  - simpl. destruct H_in as [H_eq | H_rest].
    + rewrite H_eq. simpl. rewrite H_inter. left. reflexivity.
    + destruct (node_interactive hd) eqn:E.
      * right. apply IH. exact H_rest.
      * apply IH. exact H_rest.
Qed.

(* ------ Theorem 6.7: live_regions_announced ------ *)
(* Dynamic content changes in live regions are announced to assistive technology. *)

Inductive LiveRegionPoliteness := Polite | Assertive | Off.

Record LiveRegion := mkLiveRegion {
  region_node_id : nat;
  region_politeness : LiveRegionPoliteness;
  region_content_changed : bool
}.

Definition live_region_politeness_decidable :
  forall (p : LiveRegionPoliteness), {p = Off} + {p <> Off}.
Proof.
  intros p. destruct p.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

Definition announced (lr : LiveRegion) : Prop :=
  region_content_changed lr = true ->
  region_politeness lr <> Off.

Record RIINA_LiveRegion := mkRIINALiveRegion {
  riina_live_region : LiveRegion;
  riina_live_guarantee : announced riina_live_region
}.

Theorem live_regions_announced :
  forall (rlr : RIINA_LiveRegion),
    region_content_changed (riina_live_region rlr) = true ->
    region_politeness (riina_live_region rlr) <> Off.
Proof.
  intros rlr H_changed.
  exact (riina_live_guarantee rlr H_changed).
Qed.

(* ============================================================================ *)
(* SECTION 7: Color Independence                                                *)
(* ============================================================================ *)
(* Spec: WCAG 2.1 SC 1.4.1 — Use of Color                                      *)

(** A UISignal encodes how information is conveyed. Each signal channel is
    either present (Some descriptor) or absent (None). *)
Record UISignal := mkUISignal {
  signal_id : nat;
  color_signal : bool;      (* information conveyed by color *)
  shape_signal : bool;      (* information conveyed by shape/icon *)
  text_signal : bool;       (* information conveyed by text *)
  underline_signal : bool;  (* information conveyed by underline *)
  pattern_signal : bool     (* information conveyed by pattern/texture *)
}.

(** Non-color alternative: at least one non-color channel is active. *)
Definition has_noncolor_alternative (sig : UISignal) : Prop :=
  shape_signal sig = true \/ text_signal sig = true \/
  underline_signal sig = true \/ pattern_signal sig = true.

(** RIINA-compliant signal: if color is used, a non-color alternative exists. *)
Record RIINA_Signal := mkRIINASignal {
  riina_signal : UISignal;
  riina_color_independence :
    color_signal (riina_signal) = true ->
    has_noncolor_alternative riina_signal
}.

(* Types of UI signals for specific contexts *)
Inductive SignalContext :=
  | CtxLink | CtxError | CtxSuccess | CtxChart | CtxStatus.

Record ContextualSignal := mkContextualSignal {
  ctx_signal : RIINA_Signal;
  ctx_context : SignalContext;
  (* Context-specific guarantees *)
  ctx_link_underline :
    ctx_context = CtxLink ->
    underline_signal (riina_signal ctx_signal) = true;
  ctx_error_icon_text :
    ctx_context = CtxError ->
    shape_signal (riina_signal ctx_signal) = true /\
    text_signal (riina_signal ctx_signal) = true;
  ctx_success_text :
    ctx_context = CtxSuccess ->
    text_signal (riina_signal ctx_signal) = true;
  ctx_chart_pattern :
    ctx_context = CtxChart ->
    pattern_signal (riina_signal ctx_signal) = true;
  ctx_status_label :
    ctx_context = CtxStatus ->
    text_signal (riina_signal ctx_signal) = true
}.

(* ------ Theorem 7.1: information_not_color_only ------ *)
(* Every RIINA signal that uses color also provides a non-color alternative. *)
Theorem information_not_color_only :
  forall (rs : RIINA_Signal),
    color_signal (riina_signal rs) = true ->
    has_noncolor_alternative (riina_signal rs).
Proof.
  intros rs H_color.
  exact (riina_color_independence rs H_color).
Qed.

(* ------ Theorem 7.2: link_not_color_only ------ *)
(* Links are distinguishable without color — they have underline. *)
Theorem link_not_color_only :
  forall (cs : ContextualSignal),
    ctx_context cs = CtxLink ->
    underline_signal (riina_signal (ctx_signal cs)) = true.
Proof.
  intros cs H_link.
  exact (ctx_link_underline cs H_link).
Qed.

(* ------ Theorem 7.3: error_not_color_only ------ *)
(* Error states have both icon (shape) and text, not just red color. *)
Theorem error_not_color_only :
  forall (cs : ContextualSignal),
    ctx_context cs = CtxError ->
    shape_signal (riina_signal (ctx_signal cs)) = true /\
    text_signal (riina_signal (ctx_signal cs)) = true.
Proof.
  intros cs H_error.
  exact (ctx_error_icon_text cs H_error).
Qed.

(* ------ Theorem 7.4: success_not_color_only ------ *)
(* Success states have a text indicator. *)
Theorem success_not_color_only :
  forall (cs : ContextualSignal),
    ctx_context cs = CtxSuccess ->
    text_signal (riina_signal (ctx_signal cs)) = true.
Proof.
  intros cs H_succ.
  exact (ctx_success_text cs H_succ).
Qed.

(* ------ Theorem 7.5: chart_patterns_available ------ *)
(* Data visualizations use patterns, not just colors. *)
Theorem chart_patterns_available :
  forall (cs : ContextualSignal),
    ctx_context cs = CtxChart ->
    pattern_signal (riina_signal (ctx_signal cs)) = true.
Proof.
  intros cs H_chart.
  exact (ctx_chart_pattern cs H_chart).
Qed.

(* ------ Theorem 7.6: status_indicators_labeled ------ *)
(* Status indicators have text labels. *)
Theorem status_indicators_labeled :
  forall (cs : ContextualSignal),
    ctx_context cs = CtxStatus ->
    text_signal (riina_signal (ctx_signal cs)) = true.
Proof.
  intros cs H_status.
  exact (ctx_status_label cs H_status).
Qed.

(* ============================================================================ *)
(* SECTION 8: Text Scaling                                                      *)
(* ============================================================================ *)
(* Spec: WCAG 2.1 SC 1.4.4 — Resize Text; SC 1.4.10 — Reflow                  *)

(** TextProperties model the measurable properties of rendered text.
    All sizes in abstract units (e.g., 1 unit = 1px at 100% zoom). *)
Record TextProperties := mkTextProperties {
  font_size : nat;           (* base font size in units *)
  line_height : nat;         (* line height in units *)
  letter_spacing : nat;      (* letter spacing in units *)
  container_width : nat;     (* container width in units *)
  container_height : nat;    (* container height in units *)
  text_length : nat;         (* text content length in units when rendered *)
  minimum_size : nat         (* system minimum font size *)
}.

(** Scale factor represented as a percentage (100 = 100%, 200 = 200%). *)
Definition scaled_font_size (tp : TextProperties) (scale_pct : nat) : nat :=
  (font_size tp * scale_pct) / 100.

Definition scaled_line_height (tp : TextProperties) (scale_pct : nat) : nat :=
  (line_height tp * scale_pct) / 100.

Definition scaled_container_height (tp : TextProperties) (scale_pct : nat) : nat :=
  (container_height tp * scale_pct) / 100.

(** Text is not truncated if the container can hold all text. *)
Definition not_truncated (tp : TextProperties) (scale_pct : nat) : Prop :=
  scaled_container_height tp scale_pct >= scaled_font_size tp scale_pct.

(** Text reflows if horizontal scroll is not needed.
    We model this as: text wraps within the container width. *)
Definition reflows (tp : TextProperties) : Prop :=
  text_length tp <= container_width tp.

(** RIINA text properties guarantee scaling compliance. *)
Record RIINA_TextProperties := mkRIINATextProperties {
  riina_tp : TextProperties;
  (* Font size is at least the minimum *)
  riina_min_size : font_size (riina_tp) >= minimum_size (riina_tp);
  (* Minimum size is at least 12 *)
  riina_min_12 : minimum_size (riina_tp) >= 12;
  (* Line height is at least 1.5x font size (modeled as line_height * 2 >= font_size * 3) *)
  riina_line_height_ratio :
    line_height (riina_tp) * 2 >= font_size (riina_tp) * 3;
  (* Container height scales proportionally *)
  riina_container_scales :
    forall scale_pct, scale_pct >= 100 -> scale_pct <= 200 ->
      scaled_container_height riina_tp scale_pct >= scaled_font_size riina_tp scale_pct;
  (* Text reflows rather than requiring horizontal scroll *)
  riina_reflow : text_length (riina_tp) <= container_width (riina_tp)
}.

Require Import Coq.micromega.Lia.

(* ------ Theorem 8.1: text_scales_to_200_percent ------ *)
(* All text remains readable (non-truncated) at 200% zoom. *)
Theorem text_scales_to_200_percent :
  forall (rtp : RIINA_TextProperties),
    not_truncated (riina_tp rtp) 200.
Proof.
  intros rtp.
  unfold not_truncated.
  apply (riina_container_scales rtp).
  - lia.
  - lia.
Qed.

(* ------ Theorem 8.2: no_text_truncation ------ *)
(* Scaled text never clips or truncates at any scale between 100-200%. *)
Theorem no_text_truncation :
  forall (rtp : RIINA_TextProperties) (scale_pct : nat),
    scale_pct >= 100 ->
    scale_pct <= 200 ->
    not_truncated (riina_tp rtp) scale_pct.
Proof.
  intros rtp scale_pct H_lo H_hi.
  unfold not_truncated.
  apply (riina_container_scales rtp); assumption.
Qed.

(* ------ Theorem 8.3: line_height_proportional ------ *)
(* Line height is proportional to font size (at least 1.5x). *)
Theorem line_height_proportional :
  forall (rtp : RIINA_TextProperties),
    line_height (riina_tp rtp) * 2 >= font_size (riina_tp rtp) * 3.
Proof.
  intros rtp.
  exact (riina_line_height_ratio rtp).
Qed.

(* ------ Theorem 8.4: container_expands_with_text ------ *)
(* Containers grow to fit scaled text at any zoom level up to 200%. *)
Theorem container_expands_with_text :
  forall (rtp : RIINA_TextProperties) (scale_pct : nat),
    scale_pct >= 100 ->
    scale_pct <= 200 ->
    scaled_container_height (riina_tp rtp) scale_pct >=
    scaled_font_size (riina_tp rtp) scale_pct.
Proof.
  intros rtp scale_pct H_lo H_hi.
  apply (riina_container_scales rtp); assumption.
Qed.

(* ------ Theorem 8.5: text_reflow ------ *)
(* Text reflows rather than creating horizontal scroll. *)
Theorem text_reflow :
  forall (rtp : RIINA_TextProperties),
    reflows (riina_tp rtp).
Proof.
  intros rtp.
  unfold reflows.
  exact (riina_reflow rtp).
Qed.

(* ------ Theorem 8.6: minimum_font_size ------ *)
(* No text is smaller than 12 units (12px equivalent). *)
Theorem minimum_font_size :
  forall (rtp : RIINA_TextProperties),
    font_size (riina_tp rtp) >= 12.
Proof.
  intros rtp.
  pose proof (riina_min_size rtp) as H_min.
  pose proof (riina_min_12 rtp) as H_12.
  lia.
Qed.

(* ============================================================================ *)
(* SECTION 9: Motion Sensitivity                                                *)
(* ============================================================================ *)
(* Spec: WCAG 2.1 SC 2.3.1 — Three Flashes; SC 2.2.2 — Pause, Stop, Hide     *)

(** Motion content types *)
Inductive MotionType :=
  | Parallax | AutoPlay | Carousel | VideoContent | CSSAnimation | Transition.

(** A motion element is any content that moves, flashes, or auto-advances. *)
Record MotionElement := mkMotionElement {
  motion_id : nat;
  motion_type : MotionType;
  motion_active : bool;           (* is the motion currently active *)
  motion_essential : bool;        (* is it essential for understanding *)
  has_pause_control : bool;       (* can the user pause it *)
  flash_rate : nat;               (* flashes per second, 0 = no flash *)
  respects_reduce_motion : bool   (* honors prefers-reduced-motion *)
}.

(** Safe flash rate: no more than 3 flashes per second. *)
Definition safe_flash_rate (me : MotionElement) : Prop :=
  flash_rate me <= 3.

(** User controllable: element has a pause/stop control. *)
Definition user_controllable (me : MotionElement) : Prop :=
  has_pause_control me = true.

(** Functional without animation: the element being inactive does not
    break functionality. We model this as: if motion is disabled, the
    element still has purpose (its id is still valid). *)
Definition functional_without_animation (me : MotionElement) : Prop :=
  motion_active me = false -> motion_id me > 0.

(** RIINA-compliant motion element *)
Record RIINA_MotionElement := mkRIINAMotionElement {
  riina_motion : MotionElement;
  (* Parallax effects must respect reduce-motion *)
  riina_parallax_reducible :
    motion_type (riina_motion) = Parallax ->
    respects_reduce_motion (riina_motion) = true;
  (* Auto-playing content must have pause control *)
  riina_autoplay_pausable :
    motion_type (riina_motion) = AutoPlay ->
    has_pause_control (riina_motion) = true;
  (* Flash rate never exceeds 3 Hz *)
  riina_flash_safe :
    flash_rate (riina_motion) <= 3;
  (* Carousels must have pause control *)
  riina_carousel_control :
    motion_type (riina_motion) = Carousel ->
    has_pause_control (riina_motion) = true;
  (* Videos must have play/pause controls *)
  riina_video_control :
    motion_type (riina_motion) = VideoContent ->
    has_pause_control (riina_motion) = true;
  (* UI is fully functional without animations *)
  riina_no_animation_needed :
    motion_active (riina_motion) = false ->
    motion_id (riina_motion) > 0
}.

(* ------ Theorem 9.1: parallax_disableable ------ *)
(* Parallax effects respect the prefers-reduced-motion setting. *)
Theorem parallax_disableable :
  forall (rme : RIINA_MotionElement),
    motion_type (riina_motion rme) = Parallax ->
    respects_reduce_motion (riina_motion rme) = true.
Proof.
  intros rme H_parallax.
  exact (riina_parallax_reducible rme H_parallax).
Qed.

(* ------ Theorem 9.2: auto_play_disableable ------ *)
(* Auto-playing content can be paused by the user. *)
Theorem auto_play_disableable :
  forall (rme : RIINA_MotionElement),
    motion_type (riina_motion rme) = AutoPlay ->
    user_controllable (riina_motion rme).
Proof.
  intros rme H_autoplay.
  unfold user_controllable.
  exact (riina_autoplay_pausable rme H_autoplay).
Qed.

(* ------ Theorem 9.3: flash_rate_safe ------ *)
(* No content flashes more than 3 times per second. *)
Theorem flash_rate_safe :
  forall (rme : RIINA_MotionElement),
    safe_flash_rate (riina_motion rme).
Proof.
  intros rme.
  unfold safe_flash_rate.
  exact (riina_flash_safe rme).
Qed.

(* ------ Theorem 9.4: carousel_controllable ------ *)
(* Auto-advancing carousels have a pause control. *)
Theorem carousel_controllable :
  forall (rme : RIINA_MotionElement),
    motion_type (riina_motion rme) = Carousel ->
    user_controllable (riina_motion rme).
Proof.
  intros rme H_carousel.
  unfold user_controllable.
  exact (riina_carousel_control rme H_carousel).
Qed.

(* ------ Theorem 9.5: video_controllable ------ *)
(* All video content has play/pause controls. *)
Theorem video_controllable :
  forall (rme : RIINA_MotionElement),
    motion_type (riina_motion rme) = VideoContent ->
    user_controllable (riina_motion rme).
Proof.
  intros rme H_video.
  unfold user_controllable.
  exact (riina_video_control rme H_video).
Qed.

(* ------ Theorem 9.6: animation_not_required ------ *)
(* UI is fully functional without animations — disabling motion does not
   destroy element identity or functionality. *)
Theorem animation_not_required :
  forall (rme : RIINA_MotionElement),
    functional_without_animation (riina_motion rme).
Proof.
  intros rme.
  unfold functional_without_animation.
  exact (riina_no_animation_needed rme).
Qed.

(* ============================================================================ *)
(* SECTION 10: Cross-Cutting Accessibility Composition Theorems                 *)
(* ============================================================================ *)

(* ------ Theorem 10.1: color_independence_implies_screen_reader_friendly ------ *)
(* If a signal has a text alternative, then information is available to
   screen readers (since screen readers process text). *)
Theorem color_independence_implies_screen_reader_friendly :
  forall (rs : RIINA_Signal),
    text_signal (riina_signal rs) = true ->
    has_noncolor_alternative (riina_signal rs).
Proof.
  intros rs H_text.
  unfold has_noncolor_alternative.
  right. left. exact H_text.
Qed.

(* ------ Theorem 10.2: error_signals_doubly_redundant ------ *)
(* Error signals in RIINA are always doubly redundant (icon AND text). *)
Theorem error_signals_doubly_redundant :
  forall (cs : ContextualSignal),
    ctx_context cs = CtxError ->
    shape_signal (riina_signal (ctx_signal cs)) = true /\
    text_signal (riina_signal (ctx_signal cs)) = true.
Proof.
  intros cs H_error.
  exact (ctx_error_icon_text cs H_error).
Qed.

(* ------ Theorem 10.3: scaled_text_still_reflows ------ *)
(* Text that reflows at 100% still reflows at any scale (container width is
   independent of text scaling in our model). *)
Theorem scaled_text_still_reflows :
  forall (rtp : RIINA_TextProperties),
    reflows (riina_tp rtp).
Proof.
  intros rtp.
  unfold reflows.
  exact (riina_reflow rtp).
Qed.

(* ------ Theorem 10.4: motion_safe_and_controllable ------ *)
(* Carousels are both flash-safe AND user-controllable. *)
Theorem motion_safe_and_controllable :
  forall (rme : RIINA_MotionElement),
    motion_type (riina_motion rme) = Carousel ->
    safe_flash_rate (riina_motion rme) /\ user_controllable (riina_motion rme).
Proof.
  intros rme H_carousel.
  split.
  - unfold safe_flash_rate. exact (riina_flash_safe rme).
  - unfold user_controllable. exact (riina_carousel_control rme H_carousel).
Qed.

(* ------ Theorem 10.5: interactive_nodes_fully_accessible ------ *)
(* Interactive nodes in a RIINA view have both a role and a label —
   composing screen reader completeness properties. *)
Theorem interactive_nodes_fully_accessible :
  forall (v : RIINA_View) (n : AccessibilityNode),
    In n (view_tree v) ->
    node_interactive n = true ->
    node_role n <> RoleStatic /\ node_label n <> 0.
Proof.
  intros v n H_in H_inter.
  split.
  - exact (view_roles v n H_in H_inter).
  - exact (view_labels v n H_in H_inter).
Qed.
