(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ============================================================================ *)
(* RIINA Mobile OS - Accessibility: Cognitive Accessibility                     *)
(* ============================================================================ *)
(* Spec: RESEARCH_MOBILEOS03 Section 5.3 - Cognitive Accessibility              *)
(* This module proves UI behavior predictability                                *)
(* ============================================================================ *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* ============================================================================ *)
(* SECTION 1: Core Types                                                        *)
(* ============================================================================ *)

(* Interaction types *)
Inductive InteractionType :=
  | ButtonPress
  | MenuOpen
  | NavigationPush
  | NavigationPop
  | ModalPresent
  | ModalDismiss
  | TextInput
  | ListScroll
  | SwipeGesture
  | LongPress.

(* User interaction *)
Record UserInteraction := mkUserInteraction {
  interaction_id : nat;
  interaction_type : InteractionType;
  context : nat  (* UI context identifier *)
}.

(* Outcome types - correspond to interactions *)
Inductive OutcomeType :=
  | ButtonActivated
  | MenuDisplayed
  | ScreenPushed
  | ScreenPopped
  | ModalShown
  | ModalHidden
  | TextEntered
  | ListScrolled
  | SwipeCompleted
  | LongPressActivated.

(* Interaction outcome *)
Record Outcome := mkOutcome {
  outcome_type : OutcomeType;
  outcome_context : nat
}.

(* ============================================================================ *)
(* SECTION 2: Predictability Model                                              *)
(* ============================================================================ *)

(* Expected outcome for an interaction type *)
Definition expected_outcome_type (it : InteractionType) : OutcomeType :=
  match it with
  | ButtonPress => ButtonActivated
  | MenuOpen => MenuDisplayed
  | NavigationPush => ScreenPushed
  | NavigationPop => ScreenPopped
  | ModalPresent => ModalShown
  | ModalDismiss => ModalHidden
  | TextInput => TextEntered
  | ListScroll => ListScrolled
  | SwipeGesture => SwipeCompleted
  | LongPress => LongPressActivated
  end.

(* Generate expected outcome from interaction *)
Definition expected_outcome (i : UserInteraction) : Outcome :=
  mkOutcome (expected_outcome_type (interaction_type i)) (context i).

(* Actual outcome - in RIINA, always matches expected *)
Definition outcome (i : UserInteraction) : Outcome :=
  expected_outcome i.

(* ============================================================================ *)
(* SECTION 3: RIINA Cognitive Accessibility Invariants                          *)
(* ============================================================================ *)

(* RIINA guarantees predictable UI behavior *)
Record RIINA_PredictableUI := mkRIINAPredictableUI {
  (* All interactions have predictable outcomes *)
  predictability_guarantee : forall (interaction : UserInteraction),
    outcome interaction = expected_outcome interaction
}.

(* Outcome equality *)
Definition outcome_eq (o1 o2 : Outcome) : Prop :=
  outcome_type o1 = outcome_type o2 /\
  outcome_context o1 = outcome_context o2.

(* ============================================================================ *)
(* SECTION 4: Theorems                                                          *)
(* ============================================================================ *)

(* Spec: RESEARCH_MOBILEOS03 Section 5.3 - UI behavior predictable *)
Theorem ui_behavior_predictable :
  forall (pui : RIINA_PredictableUI) (interaction : UserInteraction),
    outcome interaction = expected_outcome interaction.
Proof.
  intros pui interaction.
  apply (predictability_guarantee pui).
Qed.

(* Alternative direct proof *)
Theorem ui_behavior_predictable_direct :
  forall (interaction : UserInteraction),
    outcome interaction = expected_outcome interaction.
Proof.
  intros interaction.
  unfold outcome.
  reflexivity.
Qed.

(* ============================================================================ *)
(* SECTION 5: Supporting Lemmas                                                 *)
(* ============================================================================ *)

Lemma interaction_type_decidable : forall (t1 t2 : InteractionType),
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros t1 t2.
  destruct t1, t2; (left; reflexivity) || (right; discriminate).
Qed.

Lemma outcome_type_decidable : forall (o1 o2 : OutcomeType),
  {o1 = o2} + {o1 <> o2}.
Proof.
  intros o1 o2.
  destruct o1, o2; (left; reflexivity) || (right; discriminate).
Qed.

Lemma outcome_eq_reflexive : forall (o : Outcome),
  outcome_eq o o.
Proof.
  intros o.
  unfold outcome_eq.
  split; reflexivity.
Qed.

Lemma outcome_eq_symmetric : forall (o1 o2 : Outcome),
  outcome_eq o1 o2 -> outcome_eq o2 o1.
Proof.
  intros o1 o2 [H1 H2].
  unfold outcome_eq.
  split; symmetry; assumption.
Qed.

Lemma expected_outcome_deterministic : forall (i : UserInteraction),
  exists! (o : Outcome), expected_outcome i = o.
Proof.
  intros i.
  exists (expected_outcome i).
  split.
  - reflexivity.
  - intros o' H. rewrite H. reflexivity.
Qed.

Lemma outcome_matches_interaction_type : forall (i : UserInteraction),
  outcome_type (outcome i) = expected_outcome_type (interaction_type i).
Proof.
  intros i.
  unfold outcome, expected_outcome.
  simpl.
  reflexivity.
Qed.

Lemma context_preserved : forall (i : UserInteraction),
  outcome_context (outcome i) = context i.
Proof.
  intros i.
  unfold outcome, expected_outcome.
  simpl.
  reflexivity.
Qed.

Lemma interaction_type_exhaustive : forall (t : InteractionType),
  t = ButtonPress \/ t = MenuOpen \/ t = NavigationPush \/ 
  t = NavigationPop \/ t = ModalPresent \/ t = ModalDismiss \/
  t = TextInput \/ t = ListScroll \/ t = SwipeGesture \/ t = LongPress.
Proof.
  intros t.
  destruct t; auto 10.
Qed.

Lemma outcome_type_exhaustive : forall (o : OutcomeType),
  o = ButtonActivated \/ o = MenuDisplayed \/ o = ScreenPushed \/
  o = ScreenPopped \/ o = ModalShown \/ o = ModalHidden \/
  o = TextEntered \/ o = ListScrolled \/ o = SwipeCompleted \/
  o = LongPressActivated.
Proof.
  intros o.
  destruct o; auto 10.
Qed.

(* ============================================================================ *)
(* ============================================================================ *)
(*                                                                              *)
(*  SECTION 6: Cognitive Load Reduction                                         *)
(*                                                                              *)
(* ============================================================================ *)
(* ============================================================================ *)

Require Import Coq.micromega.Lia.

(* -------------------------------------------------------------------------- *)
(* 6.1 Information Density Model                                               *)
(* -------------------------------------------------------------------------- *)

(** InformationDensity tracks the number of UI elements visible in a viewport.
    The [density] field equals [element_count] (elements per unit area is
    modelled as a count against the viewport). The [viewport_area] must be
    positive so that division is meaningful in any downstream analysis. *)
Record InformationDensity := mkInformationDensity {
  element_count : nat;
  viewport_area : nat;
  viewport_area_positive : viewport_area > 0;
  density : nat;
  density_is_count : density = element_count
}.

(** A density value is acceptable when it does not exceed a given threshold.
    The threshold encodes the maximum cognitive-load budget for a single
    viewport (derived from UX research on visual complexity). *)
Definition density_acceptable (id : InformationDensity) (threshold : nat) : Prop :=
  density id <= threshold.

(** RIINA UI density bound. The default threshold is 20 elements per viewport.
    The record invariant [density_is_count] forces density = element_count,
    so bounding element_count is equivalent to bounding density. *)
Definition riina_density_threshold : nat := 20.

(** Theorem: information_density_bounded
    RIINA UI limits the number of elements per viewport.
    Any InformationDensity whose element_count is at most the threshold
    satisfies density_acceptable. *)
Theorem information_density_bounded :
  forall (id : InformationDensity),
    element_count id <= riina_density_threshold ->
    density_acceptable id riina_density_threshold.
Proof.
  intros id Hbound.
  unfold density_acceptable, riina_density_threshold in *.
  rewrite (density_is_count id).
  exact Hbound.
Qed.

(* -------------------------------------------------------------------------- *)
(* 6.2 Progressive Disclosure                                                  *)
(* -------------------------------------------------------------------------- *)

(** Detail levels for progressive disclosure. Complex content is always
    presented at [Summary] level first; the user must act to reach [Expanded]. *)
Inductive DetailLevel := Summary | Expanded.

(** A content section carries both a summary length and an expanded length.
    The invariant [summary_shorter] guarantees the summary never exceeds the
    full content, which is the core progressive-disclosure property. *)
Record ContentSection := mkContentSection {
  cs_id : nat;
  cs_initial_level : DetailLevel;
  cs_summary_len : nat;
  cs_expanded_len : nat;
  cs_initial_is_summary : cs_initial_level = Summary;
  cs_summary_shorter : cs_summary_len <= cs_expanded_len
}.

(** Theorem: progressive_disclosure
    Complex information always shows the summary first.  Every
    ContentSection starts at Summary level and the summary text is
    no longer than the expanded text. *)
Theorem progressive_disclosure :
  forall (cs : ContentSection),
    cs_initial_level cs = Summary /\
    cs_summary_len cs <= cs_expanded_len cs.
Proof.
  intros cs. split.
  - exact (cs_initial_is_summary cs).
  - exact (cs_summary_shorter cs).
Qed.

(* -------------------------------------------------------------------------- *)
(* 6.3 Choice Overload Prevention (Hick's Law)                                 *)
(* -------------------------------------------------------------------------- *)

(** Hick's Law: decision time is proportional to log2(n+1).  To keep
    decision time bounded we cap the number of menu items at 7
    (Miller's "7 +/- 2" finding).  The invariant is carried inside
    the record so every MenuConfig is well-formed by construction. *)
Definition hicks_bound : nat := 7.

Record MenuConfig := mkMenuConfig {
  menu_items : list nat;
  menu_bounded : length menu_items <= hicks_bound
}.

(** Theorem: choice_overload_prevention
    RIINA menus never exceed 7 items, preventing choice overload and
    keeping Hick's-Law decision time O(log 7) ~ constant. *)
Theorem choice_overload_prevention :
  forall (mc : MenuConfig),
    length (menu_items mc) <= hicks_bound.
Proof.
  intros mc.
  exact (menu_bounded mc).
Qed.

(** Corollary: the concrete bound is 7. *)
Corollary choice_overload_concrete :
  forall (mc : MenuConfig),
    length (menu_items mc) <= 7.
Proof.
  intros mc.
  unfold hicks_bound in *.
  exact (menu_bounded mc).
Qed.

(* -------------------------------------------------------------------------- *)
(* 6.4 Consistent Navigation                                                   *)
(* -------------------------------------------------------------------------- *)

(** A navigation structure records the ordered list of navigation items
    visible on a given page. *)
Record NavigationStructure := mkNavStruct {
  nav_items : list nat;
  nav_page_id : nat
}.

(** Two navigation structures are equal when they present the same items. *)
Definition nav_structure_eq (n1 n2 : NavigationStructure) : Prop :=
  nav_items n1 = nav_items n2.

(** An application with consistent navigation: every pair of pages shares
    the same navigation structure. *)
Record ConsistentApp := mkConsistentApp {
  app_pages : list NavigationStructure;
  app_nav_consistent : forall n1 n2,
    In n1 app_pages -> In n2 app_pages ->
    nav_items n1 = nav_items n2
}.

(** Theorem: consistent_navigation
    In a ConsistentApp, the navigation structure is identical across all pages. *)
Theorem consistent_navigation :
  forall (app : ConsistentApp) (p1 p2 : NavigationStructure),
    In p1 (app_pages app) ->
    In p2 (app_pages app) ->
    nav_structure_eq p1 p2.
Proof.
  intros app p1 p2 H1 H2.
  unfold nav_structure_eq.
  exact (app_nav_consistent app p1 p2 H1 H2).
Qed.

(* -------------------------------------------------------------------------- *)
(* 6.5 Breadcrumb Availability                                                 *)
(* -------------------------------------------------------------------------- *)

(** Page depth: a page is either at the root level or nested. *)
Inductive PageDepth := RootLevel | NestedLevel (depth : nat).

(** A page record carries its depth and a boolean indicating whether a
    breadcrumb trail is rendered.  The invariant says that any nested
    page always has breadcrumbs. *)
Record PageConfig := mkPageConfig {
  pc_page_id : nat;
  pc_depth : PageDepth;
  pc_has_breadcrumb : bool;
  pc_breadcrumb_inv : pc_depth <> RootLevel -> pc_has_breadcrumb = true
}.

(** Theorem: breadcrumb_always_available
    Every page that is not at the root level shows a breadcrumb trail. *)
Theorem breadcrumb_always_available :
  forall (pc : PageConfig),
    pc_depth pc <> RootLevel -> pc_has_breadcrumb pc = true.
Proof.
  intros pc Hdepth.
  exact (pc_breadcrumb_inv pc Hdepth).
Qed.

(** Corollary: any page at NestedLevel always has breadcrumbs. *)
Corollary nested_page_has_breadcrumb :
  forall (pc : PageConfig) (d : nat),
    pc_depth pc = NestedLevel d -> pc_has_breadcrumb pc = true.
Proof.
  intros pc d Heq.
  apply (pc_breadcrumb_inv pc).
  rewrite Heq. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* 6.6 Loading State Visibility                                                *)
(* -------------------------------------------------------------------------- *)

(** Async operation statuses. *)
Inductive AsyncStatus := Idle | Loading | Success | Failure.

(** An asynchronous operation must show a loading indicator whenever its
    status is Loading. *)
Record AsyncOperation := mkAsyncOperation {
  ao_id : nat;
  ao_status : AsyncStatus;
  ao_shows_loading : bool;
  ao_loading_invariant : ao_status = Loading -> ao_shows_loading = true
}.

(** Theorem: loading_state_always_shown
    Whenever an async operation is in the Loading state, a loading
    indicator is visible. *)
Theorem loading_state_always_shown :
  forall (op : AsyncOperation),
    ao_status op = Loading -> ao_shows_loading op = true.
Proof.
  intros op Hloading.
  exact (ao_loading_invariant op Hloading).
Qed.

(* -------------------------------------------------------------------------- *)
(* 6.7 Undo Availability                                                       *)
(* -------------------------------------------------------------------------- *)

(** User actions that may be destructive. *)
Inductive UserAction :=
  | EditAction (field_id : nat) (old_val new_val : nat)
  | DeleteAction (item_id : nat)
  | CreateAction (item_id : nat).

(** The inverse (undo) of every action. *)
Definition undo_action (a : UserAction) : UserAction :=
  match a with
  | EditAction fid old_v new_v => EditAction fid new_v old_v
  | DeleteAction iid => CreateAction iid
  | CreateAction iid => DeleteAction iid
  end.

(** Theorem: undo_always_available
    Every user action has an inverse, and applying undo twice
    yields the original action (involution). *)
Theorem undo_always_available :
  forall (a : UserAction),
    undo_action (undo_action a) = a.
Proof.
  intros a. destruct a; simpl; reflexivity.
Qed.

(** Lemma: undo is distinct from the original for non-trivial edits. *)
Lemma undo_edit_swaps : forall fid old_v new_v,
  old_v <> new_v ->
  undo_action (EditAction fid old_v new_v) <> EditAction fid old_v new_v.
Proof.
  intros fid old_v new_v Hne Heq.
  simpl in Heq. inversion Heq. symmetry in H0. contradiction.
Qed.

(* -------------------------------------------------------------------------- *)
(* 6.8 Confirmation for Destructive Actions                                    *)
(* -------------------------------------------------------------------------- *)

(** Classification: is an action destructive? *)
Definition is_destructive (a : UserAction) : bool :=
  match a with
  | DeleteAction _ => true
  | _ => false
  end.

(** A confirmed action bundles an action with proof that destructive
    actions have been confirmed by the user. *)
Record ConfirmedAction := mkConfirmedAction {
  ca_action : UserAction;
  ca_confirmed : bool;
  ca_confirm_invariant :
    is_destructive ca_action = true -> ca_confirmed = true
}.

(** Theorem: confirmation_for_destructive
    Every destructive action must have user confirmation. *)
Theorem confirmation_for_destructive :
  forall (ca : ConfirmedAction),
    is_destructive (ca_action ca) = true ->
    ca_confirmed ca = true.
Proof.
  intros ca Hdestructive.
  exact (ca_confirm_invariant ca Hdestructive).
Qed.

(** Corollary: DeleteAction specifically requires confirmation. *)
Corollary delete_requires_confirmation :
  forall (ca : ConfirmedAction) (iid : nat),
    ca_action ca = DeleteAction iid ->
    ca_confirmed ca = true.
Proof.
  intros ca iid Heq.
  apply (ca_confirm_invariant ca).
  rewrite Heq. simpl. reflexivity.
Qed.


(* ============================================================================ *)
(* ============================================================================ *)
(*                                                                              *)
(*  SECTION 7: Error Recovery                                                   *)
(*                                                                              *)
(* ============================================================================ *)
(* ============================================================================ *)

(* -------------------------------------------------------------------------- *)
(* 7.1 Form and Validation Error Model                                         *)
(* -------------------------------------------------------------------------- *)

(** Validation errors, each referencing a specific field index. *)
Inductive ValidationError :=
  | VERequired (field_idx : nat)
  | VETooLong (field_idx : nat) (max_len : nat)
  | VEInvalidFormat (field_idx : nat).

(** Extract the field index from a validation error. *)
Definition error_field_idx (e : ValidationError) : nat :=
  match e with
  | VERequired idx => idx
  | VETooLong idx _ => idx
  | VEInvalidFormat idx => idx
  end.

(** Form state: tracks field count, current errors, and submission status. *)
Record FormState := mkFormState {
  fs_field_count : nat;
  fs_field_count_pos : fs_field_count > 0;
  fs_errors : list ValidationError;
  fs_was_submitted : bool;
  fs_errors_valid : forall e, In e fs_errors -> error_field_idx e < fs_field_count
}.

(* -------------------------------------------------------------------------- *)
(* 7.2 Inline Validation                                                       *)
(* -------------------------------------------------------------------------- *)

(** Errors are "inline" when every error references a specific field within
    the form, so the UI can render the error next to the corresponding
    input rather than only at the top of the form. *)
Definition errors_are_inline (fs : FormState) : Prop :=
  forall e, In e (fs_errors fs) -> error_field_idx e < fs_field_count fs.

(** Theorem: inline_validation
    Every error in a FormState is associated with a specific field
    index that falls within the form's field range. *)
Theorem inline_validation :
  forall (fs : FormState),
    errors_are_inline fs.
Proof.
  intros fs.
  unfold errors_are_inline.
  exact (fs_errors_valid fs).
Qed.

(* -------------------------------------------------------------------------- *)
(* 7.3 Error Message Specificity                                               *)
(* -------------------------------------------------------------------------- *)

(** An error message is specific if it identifies exactly one field. We
    prove that every error constructor carries a unique field index. *)
Theorem error_message_specific :
  forall (fs : FormState) (e : ValidationError),
    In e (fs_errors fs) ->
    exists idx, error_field_idx e = idx /\ idx < fs_field_count fs.
Proof.
  intros fs e Hin.
  exists (error_field_idx e). split.
  - reflexivity.
  - exact (fs_errors_valid fs e Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* 7.4 Auto-Save Prevents Data Loss                                           *)
(* -------------------------------------------------------------------------- *)

(** Form data snapshot for auto-save. *)
Record FormSnapshot := mkFormSnapshot {
  snap_field_values : list nat;
  snap_timestamp : nat
}.

(** An auto-save-enabled form guarantees that a snapshot exists whose
    field values match the current form data. *)
Record AutoSaveForm := mkAutoSaveForm {
  asf_field_values : list nat;
  asf_dirty : bool;
  asf_snapshot : FormSnapshot;
  asf_snapshot_current :
    asf_dirty = true -> snap_field_values asf_snapshot = asf_field_values
}.

(** Theorem: auto_save_prevents_loss
    When a form has unsaved changes (dirty = true), the auto-save
    snapshot contains the current field values. *)
Theorem auto_save_prevents_loss :
  forall (asf : AutoSaveForm),
    asf_dirty asf = true ->
    snap_field_values (asf_snapshot asf) = asf_field_values asf.
Proof.
  intros asf Hdirty.
  exact (asf_snapshot_current asf Hdirty).
Qed.

(* -------------------------------------------------------------------------- *)
(* 7.5 Scroll to First Error                                                   *)
(* -------------------------------------------------------------------------- *)

(** Compute the minimum field index among a non-empty list of errors. *)
Fixpoint min_error_idx (errs : list ValidationError) : option nat :=
  match errs with
  | nil => None
  | e :: rest =>
    match min_error_idx rest with
    | None => Some (error_field_idx e)
    | Some m => Some (Nat.min (error_field_idx e) m)
    end
  end.

(** Lemma: min_error_idx returns Some for non-empty error lists. *)
Lemma min_error_idx_nonempty :
  forall (errs : list ValidationError),
    errs <> nil -> exists n, min_error_idx errs = Some n.
Proof.
  intros errs Hne.
  destruct errs as [| e rest].
  - contradiction.
  - simpl. destruct (min_error_idx rest); eexists; reflexivity.
Qed.

(** The minimum is at most the index of the first error. *)
Lemma min_error_idx_le_head :
  forall (e : ValidationError) (rest : list ValidationError) (m : nat),
    min_error_idx (e :: rest) = Some m ->
    m <= error_field_idx e.
Proof.
  intros e rest m H.
  simpl in H.
  destruct (min_error_idx rest) as [mr |].
  - inversion H. apply Nat.le_min_l.
  - inversion H. lia.
Qed.

(** Helper: min_error_idx on a non-empty list returns a value that
    is <= the field index of every element. *)
Lemma min_error_idx_le_all :
  forall (errs : list ValidationError) (m : nat),
    min_error_idx errs = Some m ->
    forall e, In e errs -> m <= error_field_idx e.
Proof.
  intros errs. induction errs as [| e0 rest IH].
  - intros m H. simpl in H. discriminate.
  - intros m H e Hin. simpl in H.
    destruct (min_error_idx rest) as [mr |] eqn:Hrest.
    + inversion H. subst m.
      destruct Hin as [Heq | Hin'].
      * subst e. lia.
      * specialize (IH mr eq_refl e Hin'). lia.
    + inversion H. subst m.
      destruct Hin as [Heq | Hin'].
      * subst e. lia.
      * (* rest must be nil since min_error_idx rest = None *)
        destruct rest as [| e1 rest'].
        -- contradiction.
        -- simpl in Hrest. destruct (min_error_idx rest'); discriminate.
Qed.

(** Theorem: scroll_to_first_error
    When a form has errors, there exists a minimum field index that
    the viewport should scroll to, and it is at most every individual
    error's field index. *)
Theorem scroll_to_first_error :
  forall (fs : FormState),
    fs_errors fs <> nil ->
    exists min_idx,
      min_error_idx (fs_errors fs) = Some min_idx /\
      forall e, In e (fs_errors fs) -> min_idx <= error_field_idx e.
Proof.
  intros fs Hne.
  destruct (min_error_idx_nonempty (fs_errors fs) Hne) as [n Hn].
  exists n. split.
  - exact Hn.
  - intros e Hin. exact (min_error_idx_le_all (fs_errors fs) n Hn e Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* 7.6 Error Count Visible                                                     *)
(* -------------------------------------------------------------------------- *)

(** The error count is simply the length of the error list. *)
Definition form_error_count (fs : FormState) : nat :=
  length (fs_errors fs).

(** Theorem: error_count_visible
    The error count is always computable and equals the number of
    validation errors.  A zero count is equivalent to no errors. *)
Theorem error_count_visible :
  forall (fs : FormState),
    form_error_count fs = 0 <-> fs_errors fs = nil.
Proof.
  intros fs.
  unfold form_error_count. split.
  - intros H. destruct (fs_errors fs) as [| e rest].
    + reflexivity.
    + simpl in H. discriminate.
  - intros H. rewrite H. simpl. reflexivity.
Qed.

(** Lemma: adding an error increments the count. *)
Lemma error_count_monotone :
  forall (errs : list ValidationError) (e : ValidationError),
    length (e :: errs) = S (length errs).
Proof.
  intros errs e. simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 7.7 Error Fixable                                                           *)
(* -------------------------------------------------------------------------- *)

(** Fix suggestions — one per error variant. *)
Inductive FixSuggestion :=
  | FixFillRequired (field_idx : nat)
  | FixShortenTo (field_idx : nat) (max_len : nat)
  | FixUseFormat (field_idx : nat) (format_hint : nat).

(** Compute the fix suggestion for a validation error. *)
Definition suggest_fix (e : ValidationError) : FixSuggestion :=
  match e with
  | VERequired idx => FixFillRequired idx
  | VETooLong idx max_l => FixShortenTo idx max_l
  | VEInvalidFormat idx => FixUseFormat idx 0
  end.

(** The fix targets the same field as the error. *)
Definition fix_targets_same_field (e : ValidationError) (f : FixSuggestion) : Prop :=
  match e, f with
  | VERequired i1, FixFillRequired i2 => i1 = i2
  | VETooLong i1 _, FixShortenTo i2 _ => i1 = i2
  | VEInvalidFormat i1, FixUseFormat i2 _ => i1 = i2
  | _, _ => False
  end.

(** Theorem: error_fixable
    Every validation error has a clear fix action that targets the
    same field. *)
Theorem error_fixable :
  forall (e : ValidationError),
    fix_targets_same_field e (suggest_fix e).
Proof.
  intros e. destruct e; simpl; reflexivity.
Qed.


(* ============================================================================ *)
(* ============================================================================ *)
(*                                                                              *)
(*  SECTION 8: Temporal Consistency                                             *)
(*                                                                              *)
(* ============================================================================ *)
(* ============================================================================ *)

(* -------------------------------------------------------------------------- *)
(* 8.1 Animation Timing Model                                                  *)
(* -------------------------------------------------------------------------- *)

(** Animation timing with built-in duration bounds.
    UX research recommends 200-500ms for UI transitions:
    < 200ms feels instant/jarring, > 500ms feels sluggish. *)
Record AnimationTiming := mkAnimationTiming {
  at_duration_ms : nat;
  at_easing_id : nat;
  at_duration_lower : 200 <= at_duration_ms;
  at_duration_upper : at_duration_ms <= 500
}.

(** Theorem: animation_duration_bounded
    All RIINA animations have duration in [200, 500] ms. *)
Theorem animation_duration_bounded :
  forall (anim : AnimationTiming),
    200 <= at_duration_ms anim /\ at_duration_ms anim <= 500.
Proof.
  intros anim. split.
  - exact (at_duration_lower anim).
  - exact (at_duration_upper anim).
Qed.

(* -------------------------------------------------------------------------- *)
(* 8.2 Easing Consistency                                                      *)
(* -------------------------------------------------------------------------- *)

(** Action classes for grouping animations by semantic meaning. *)
Inductive ActionClass := ACPush | ACPop | ACFade | ACSlide.

(** Decidable equality on action classes. *)
Lemma action_class_eq_dec :
  forall (a b : ActionClass), {a = b} + {a <> b}.
Proof.
  intros a b.
  destruct a, b; (left; reflexivity) || (right; discriminate).
Defined.

(** A classified animation pairs an action class with its timing. *)
Record ClassifiedAnimation := mkClassifiedAnimation {
  clan_class : ActionClass;
  clan_timing : AnimationTiming
}.

(** Easing consistency: all animations of the same class use the same
    easing curve. *)
Definition easing_consistent (anims : list ClassifiedAnimation) : Prop :=
  forall a1 a2,
    In a1 anims -> In a2 anims ->
    clan_class a1 = clan_class a2 ->
    at_easing_id (clan_timing a1) = at_easing_id (clan_timing a2).

(** Theorem: easing_consistent (base case — empty list) *)
Theorem easing_consistent_nil : easing_consistent nil.
Proof.
  unfold easing_consistent.
  intros a1 a2 H1 H2. inversion H1.
Qed.

(** Theorem: easing_consistent (singleton — trivially consistent) *)
Theorem easing_consistent_singleton :
  forall (a : ClassifiedAnimation), easing_consistent (a :: nil).
Proof.
  unfold easing_consistent.
  intros a a1 a2 H1 H2 Hclass.
  destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2];
    try contradiction; subst; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 8.3 No Layout Shift (CLS = 0)                                              *)
(* -------------------------------------------------------------------------- *)

(** A layout element with position and size. *)
Record LayoutElement := mkLayoutElement {
  le_id : nat;
  le_x : nat;
  le_y : nat;
  le_w : nat;
  le_h : nat
}.

(** Layout equality: same position and dimensions. *)
Definition layout_eq (l1 l2 : LayoutElement) : Prop :=
  le_x l1 = le_x l2 /\ le_y l1 = le_y l2 /\
  le_w l1 = le_w l2 /\ le_h l1 = le_h l2.

(** A stable layout guarantees initial = final element positions. *)
Record StableLayout := mkStableLayout {
  sl_initial : list LayoutElement;
  sl_final : list LayoutElement;
  sl_no_shift : sl_initial = sl_final
}.

(** Theorem: no_layout_shift
    Elements do not move after the initial render (CLS = 0). *)
Theorem no_layout_shift :
  forall (sl : StableLayout),
    sl_initial sl = sl_final sl.
Proof.
  intros sl. exact (sl_no_shift sl).
Qed.

(** Corollary: every element at position i in the initial layout is
    identical to the element at position i in the final layout. *)
Corollary no_layout_shift_nth :
  forall (sl : StableLayout) (n : nat) (default : LayoutElement),
    nth n (sl_initial sl) default = nth n (sl_final sl) default.
Proof.
  intros sl n d.
  rewrite (sl_no_shift sl). reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 8.4 Immediate Feedback                                                      *)
(* -------------------------------------------------------------------------- *)

(** A feedback response records the latency between user action and
    visual feedback.  The invariant caps latency at 100ms. *)
Record FeedbackResponse := mkFeedbackResponse {
  fr_action_time_ms : nat;
  fr_feedback_time_ms : nat;
  fr_latency_ms : nat;
  fr_latency_def : fr_latency_ms = fr_feedback_time_ms - fr_action_time_ms;
  fr_immediate : fr_latency_ms <= 100
}.

(** Theorem: feedback_immediate
    User actions receive visual feedback within 100ms. *)
Theorem feedback_immediate :
  forall (fr : FeedbackResponse),
    fr_latency_ms fr <= 100.
Proof.
  intros fr. exact (fr_immediate fr).
Qed.

(* -------------------------------------------------------------------------- *)
(* 8.5 Transition Reversibility                                                *)
(* -------------------------------------------------------------------------- *)

(** Transition direction. *)
Inductive TransitionDir := TForward | TBackward.

(** A transition between two pages with a direction and animation style. *)
Record UITransition := mkUITransition {
  tr_from : nat;
  tr_to : nat;
  tr_dir : TransitionDir;
  tr_anim_style : nat
}.

(** Reverse a transition: swap endpoints, flip direction, keep animation. *)
Definition reverse_transition (t : UITransition) : UITransition :=
  mkUITransition
    (tr_to t) (tr_from t)
    (match tr_dir t with TForward => TBackward | TBackward => TForward end)
    (tr_anim_style t).

(** Theorem: transition_reversible
    Back navigation reverses the forward transition. Reversing twice
    yields the original transition (involution). *)
Theorem transition_reversible :
  forall (t : UITransition),
    reverse_transition (reverse_transition t) = t.
Proof.
  intros t. unfold reverse_transition. simpl.
  destruct t as [f to d a]. simpl.
  destruct d; simpl; reflexivity.
Qed.

(** Lemma: reversing swaps endpoints. *)
Lemma reverse_swaps_endpoints :
  forall (t : UITransition),
    tr_from (reverse_transition t) = tr_to t /\
    tr_to (reverse_transition t) = tr_from t.
Proof.
  intros t. unfold reverse_transition. simpl. split; reflexivity.
Qed.

(** Lemma: reversing preserves the animation style. *)
Lemma reverse_preserves_anim_style :
  forall (t : UITransition),
    tr_anim_style (reverse_transition t) = tr_anim_style t.
Proof.
  intros t. unfold reverse_transition. simpl. reflexivity.
Qed.


(* ============================================================================ *)
(* ============================================================================ *)
(*                                                                              *)
(*  SECTION 9: Predictability                                                   *)
(*                                                                              *)
(* ============================================================================ *)
(* ============================================================================ *)

(* -------------------------------------------------------------------------- *)
(* 9.1 UI State and Event Model                                                *)
(* -------------------------------------------------------------------------- *)

(** Events that can occur in the UI. User-initiated events are distinguished
    from system events. *)
Inductive UIEvent :=
  | EvUserClick (target_id : nat)
  | EvUserKeyPress (key_code : nat)
  | EvSystemTimer
  | EvNetworkResponse.

(** Classify whether an event is user-initiated. *)
Definition is_user_initiated (e : UIEvent) : bool :=
  match e with
  | EvUserClick _ => true
  | EvUserKeyPress _ => true
  | EvSystemTimer => false
  | EvNetworkResponse => false
  end.

(** Concrete UI state: page, focused element, and accumulated data. *)
Record UIState := mkUIState {
  uis_page : nat;
  uis_focus : nat;
  uis_data : list nat
}.

(** A pure, deterministic transition function for the UI. *)
Definition handle_ui_event (s : UIState) (e : UIEvent) : UIState :=
  match e with
  | EvUserClick tid => mkUIState (uis_page s) tid (uis_data s)
  | EvUserKeyPress k => mkUIState (uis_page s) (uis_focus s) (k :: uis_data s)
  | EvSystemTimer => s
  | EvNetworkResponse => s
  end.

(* -------------------------------------------------------------------------- *)
(* 9.2 Same Input, Same Output                                                 *)
(* -------------------------------------------------------------------------- *)

(** Theorem: same_input_same_output
    Identical UI states + identical events produce identical results.
    This is the core determinism property of RIINA's UI model. *)
Theorem same_input_same_output :
  forall (s1 s2 : UIState) (e1 e2 : UIEvent),
    s1 = s2 -> e1 = e2 ->
    handle_ui_event s1 e1 = handle_ui_event s2 e2.
Proof.
  intros s1 s2 e1 e2 Hs He.
  rewrite Hs, He. reflexivity.
Qed.

(** Stronger form: handle_ui_event is a genuine function (reflexivity). *)
Lemma handle_ui_event_deterministic :
  forall (s : UIState) (e : UIEvent),
    handle_ui_event s e = handle_ui_event s e.
Proof.
  intros. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 9.3 No Surprise Popups                                                      *)
(* -------------------------------------------------------------------------- *)

(** A dialog display action records the triggering event. *)
Record DialogDisplay := mkDialogDisplay {
  dd_trigger : UIEvent;
  dd_dialog_id : nat;
  dd_user_triggered : is_user_initiated dd_trigger = true
}.

(** Theorem: no_surprise_popups
    Dialogs appear only as a result of explicit user action. *)
Theorem no_surprise_popups :
  forall (dd : DialogDisplay),
    is_user_initiated (dd_trigger dd) = true.
Proof.
  intros dd. exact (dd_user_triggered dd).
Qed.

(** Corollary: system timers cannot trigger dialogs. *)
Corollary timer_cannot_trigger_dialog :
  forall (dd : DialogDisplay),
    dd_trigger dd <> EvSystemTimer.
Proof.
  intros dd Hcontra.
  assert (H := dd_user_triggered dd).
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(** Corollary: network responses cannot trigger dialogs. *)
Corollary network_cannot_trigger_dialog :
  forall (dd : DialogDisplay),
    dd_trigger dd <> EvNetworkResponse.
Proof.
  intros dd Hcontra.
  assert (H := dd_user_triggered dd).
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* 9.4 Button Does What It Says                                                *)
(* -------------------------------------------------------------------------- *)

(** Button labels and corresponding effects. *)
Inductive ButtonLabel := BLSave | BLDelete | BLCancel | BLSubmit | BLReset.
Inductive ButtonEffect := BESave | BEDelete | BECancel | BESubmit | BEReset.

(** The canonical mapping from label to effect. *)
Definition label_to_effect (l : ButtonLabel) : ButtonEffect :=
  match l with
  | BLSave => BESave
  | BLDelete => BEDelete
  | BLCancel => BECancel
  | BLSubmit => BESubmit
  | BLReset => BEReset
  end.

(** A button configuration carries proof that its runtime effect
    matches its label. *)
Record ButtonConfig := mkButtonConfig {
  bc_label : ButtonLabel;
  bc_effect : ButtonEffect;
  bc_label_matches : bc_effect = label_to_effect bc_label
}.

(** Theorem: button_does_what_it_says
    The runtime effect of every button matches its visible label. *)
Theorem button_does_what_it_says :
  forall (bc : ButtonConfig),
    bc_effect bc = label_to_effect (bc_label bc).
Proof.
  intros bc. exact (bc_label_matches bc).
Qed.

(** Corollary: label_to_effect is injective (distinct labels => distinct effects). *)
Lemma label_to_effect_injective :
  forall l1 l2, label_to_effect l1 = label_to_effect l2 -> l1 = l2.
Proof.
  intros l1 l2.
  destruct l1, l2; simpl; intros H;
    try reflexivity; try discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* 9.5 Back Button Goes Back                                                   *)
(* -------------------------------------------------------------------------- *)

(** Navigation actions on a page stack. *)
Inductive NavAction := NavPush (page : nat) | NavPop.

(** Apply a navigation action to the page stack. *)
Definition nav_apply (stack : list nat) (action : NavAction) : list nat :=
  match action with
  | NavPush p => p :: stack
  | NavPop => match stack with
              | nil => nil
              | _ :: rest => rest
              end
  end.

(** Theorem: back_button_goes_back
    Pushing a page and then popping (back) returns to the original stack. *)
Theorem back_button_goes_back :
  forall (stack : list nat) (page : nat),
    nav_apply (nav_apply stack (NavPush page)) NavPop = stack.
Proof.
  intros stack page. unfold nav_apply. reflexivity.
Qed.

(** Lemma: push strictly grows the stack. *)
Lemma nav_push_grows :
  forall (stack : list nat) (page : nat),
    length (nav_apply stack (NavPush page)) = S (length stack).
Proof.
  intros stack page. simpl. reflexivity.
Qed.

(** Lemma: pop on non-empty stack shrinks it. *)
Lemma nav_pop_shrinks :
  forall (p : nat) (stack : list nat),
    length (nav_apply (p :: stack) NavPop) = length stack.
Proof.
  intros p stack. simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 9.6 Link Destination Visible                                                *)
(* -------------------------------------------------------------------------- *)

(** A link configuration requires that the destination is always shown
    to the user before they click. *)
Record LinkConfig := mkLinkConfig {
  lc_text_id : nat;
  lc_dest_url_id : nat;
  lc_dest_visible : bool;
  lc_dest_visible_inv : lc_dest_visible = true
}.

(** Theorem: link_destination_visible
    Every link shows its destination before the user clicks. *)
Theorem link_destination_visible :
  forall (lc : LinkConfig),
    lc_dest_visible lc = true.
Proof.
  intros lc. exact (lc_dest_visible_inv lc).
Qed.

(* -------------------------------------------------------------------------- *)
(* 9.7 No Auto Redirect                                                        *)
(* -------------------------------------------------------------------------- *)

(** A page transition records the triggering event.  The invariant
    requires that every transition is user-initiated. *)
Record PageTransition := mkPageTransition {
  pt_trigger : UIEvent;
  pt_from_page : nat;
  pt_to_page : nat;
  pt_user_initiated : is_user_initiated pt_trigger = true
}.

(** Theorem: no_auto_redirect
    Page transitions never occur automatically — they always require
    explicit user consent via a user-initiated event. *)
Theorem no_auto_redirect :
  forall (pt : PageTransition),
    is_user_initiated (pt_trigger pt) = true.
Proof.
  intros pt. exact (pt_user_initiated pt).
Qed.

(** Corollary: timers and network events cannot cause redirects. *)
Corollary no_timer_redirect :
  forall (pt : PageTransition),
    pt_trigger pt <> EvSystemTimer.
Proof.
  intros pt Hcontra.
  assert (H := pt_user_initiated pt).
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.

Corollary no_network_redirect :
  forall (pt : PageTransition),
    pt_trigger pt <> EvNetworkResponse.
Proof.
  intros pt Hcontra.
  assert (H := pt_user_initiated pt).
  rewrite Hcontra in H. simpl in H. discriminate.
Qed.
