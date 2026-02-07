(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** ============================================================================
    RIINA FORMAL VERIFICATION - CSRF PROTECTION
    
    File: CSRFProtection.v
    Part of: Phase 3, Batch 2
    Theorems: 20
    
    Zero admits. Zero axioms. All theorems proven.
    ============================================================================ *)

Require Import Coq.Bool.Bool.

Lemma andb_true_iff : forall a b : bool, a && b = true <-> a = true /\ b = true.
Proof. intros a b. split.
  - intro H. destruct a; destruct b; simpl in *; split; try reflexivity; discriminate.
  - intros [Ha Hb]. rewrite Ha, Hb. reflexivity.
Qed.

Record CSRFConfig : Type := mkCSRF {
  csrf_token_validation : bool;
  csrf_same_site_cookies : bool;
  csrf_origin_check : bool;
  csrf_referer_check : bool;
  csrf_double_submit : bool;
}.

Definition csrf_protected (c : CSRFConfig) : bool :=
  csrf_token_validation c && csrf_same_site_cookies c && csrf_origin_check c &&
  csrf_referer_check c && csrf_double_submit c.

Definition riina_csrf : CSRFConfig := mkCSRF true true true true true.

Theorem CSRF_001 : csrf_protected riina_csrf = true. Proof. reflexivity. Qed.
Theorem CSRF_002 : csrf_token_validation riina_csrf = true. Proof. reflexivity. Qed.
Theorem CSRF_003 : csrf_same_site_cookies riina_csrf = true. Proof. reflexivity. Qed.
Theorem CSRF_004 : csrf_origin_check riina_csrf = true. Proof. reflexivity. Qed.
Theorem CSRF_005 : csrf_double_submit riina_csrf = true. Proof. reflexivity. Qed.

Theorem CSRF_006 : forall c, csrf_protected c = true -> csrf_token_validation c = true.
Proof. intros c H. unfold csrf_protected in H. repeat (apply andb_true_iff in H; destruct H as [H _]). exact H. Qed.

Theorem CSRF_007 : forall c, csrf_protected c = true -> csrf_same_site_cookies c = true.
Proof. intros c H. unfold csrf_protected in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

Theorem CSRF_008 : forall c, csrf_protected c = true -> csrf_origin_check c = true.
Proof. intros c H. unfold csrf_protected in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

Theorem CSRF_009 : forall c, csrf_protected c = true -> csrf_referer_check c = true.
Proof. intros c H. unfold csrf_protected in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

Theorem CSRF_010 : forall c, csrf_protected c = true -> csrf_double_submit c = true.
Proof. intros c H. unfold csrf_protected in H. apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

Theorem CSRF_011 : csrf_token_validation riina_csrf = true /\ csrf_same_site_cookies riina_csrf = true.
Proof. split; reflexivity. Qed.

Theorem CSRF_012 : csrf_origin_check riina_csrf = true /\ csrf_referer_check riina_csrf = true.
Proof. split; reflexivity. Qed.

Theorem CSRF_013 : csrf_protected riina_csrf = true /\ csrf_double_submit riina_csrf = true.
Proof. split; reflexivity. Qed.

Theorem CSRF_014 : forall c, csrf_protected c = true -> csrf_token_validation c = true /\ csrf_same_site_cookies c = true.
Proof. intros c H. split. apply CSRF_006. exact H. apply CSRF_007. exact H. Qed.

Theorem CSRF_015 : forall c, csrf_protected c = true -> csrf_origin_check c = true /\ csrf_referer_check c = true.
Proof. intros c H. split. apply CSRF_008. exact H. apply CSRF_009. exact H. Qed.

Theorem CSRF_016 : forall c, csrf_protected c = true ->
  csrf_token_validation c = true /\ csrf_origin_check c = true.
Proof. intros c H. split. apply CSRF_006. exact H. apply CSRF_008. exact H. Qed.

Theorem CSRF_017 : forall c, csrf_protected c = true ->
  csrf_same_site_cookies c = true /\ csrf_double_submit c = true.
Proof. intros c H. split. apply CSRF_007. exact H. apply CSRF_010. exact H. Qed.

Theorem CSRF_018 : csrf_token_validation riina_csrf = true /\ csrf_origin_check riina_csrf = true /\ csrf_double_submit riina_csrf = true.
Proof. split. reflexivity. split; reflexivity. Qed.

Theorem CSRF_019 : forall c, csrf_protected c = true ->
  csrf_token_validation c = true /\ csrf_same_site_cookies c = true /\ csrf_origin_check c = true.
Proof. intros c H.
  split. apply CSRF_006. exact H.
  split. apply CSRF_007. exact H.
  apply CSRF_008. exact H.
Qed.

Theorem CSRF_020_complete : forall c, csrf_protected c = true ->
  csrf_token_validation c = true /\ csrf_same_site_cookies c = true /\
  csrf_origin_check c = true /\ csrf_double_submit c = true.
Proof. intros c H.
  split. apply CSRF_006. exact H.
  split. apply CSRF_007. exact H.
  split. apply CSRF_008. exact H.
  apply CSRF_010. exact H.
Qed.

(** ============================================================================
    SECTION 5: EXTENDED CSRF PROTECTION THEOREMS (CSRF_021 - CSRF_035)
    ============================================================================ *)

(** CSRF request validation model *)
Record CSRFRequest : Type := mkCSRFRequest {
  req_has_token : bool;
  req_token_matches : bool;
  req_same_origin : bool;
  req_valid_referer : bool;
  req_cookie_present : bool;
}.

Definition csrf_request_safe (r : CSRFRequest) : bool :=
  req_has_token r && req_token_matches r && req_same_origin r.

Definition csrf_request_fully_validated (r : CSRFRequest) : bool :=
  csrf_request_safe r && req_valid_referer r && req_cookie_present r.

Definition riina_csrf_request : CSRFRequest := mkCSRFRequest true true true true true.

(** CSRF_021: RIINA CSRF request is safe *)
Theorem CSRF_021_riina_request_safe :
  csrf_request_safe riina_csrf_request = true.
Proof. reflexivity. Qed.

(** CSRF_022: RIINA CSRF request is fully validated *)
Theorem CSRF_022_riina_request_fully_validated :
  csrf_request_fully_validated riina_csrf_request = true.
Proof. reflexivity. Qed.

(** CSRF_023: Safe request has token *)
Theorem CSRF_023_safe_has_token :
  forall r, csrf_request_safe r = true -> req_has_token r = true.
Proof. intros r H. unfold csrf_request_safe in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [H _]. exact H. Qed.

(** CSRF_024: Safe request has matching token *)
Theorem CSRF_024_safe_token_matches :
  forall r, csrf_request_safe r = true -> req_token_matches r = true.
Proof. intros r H. unfold csrf_request_safe in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

(** CSRF_025: Safe request is same origin *)
Theorem CSRF_025_safe_same_origin :
  forall r, csrf_request_safe r = true -> req_same_origin r = true.
Proof. intros r H. unfold csrf_request_safe in H.
  apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

(** CSRF_026: Fully validated implies safe *)
Theorem CSRF_026_fully_validated_implies_safe :
  forall r, csrf_request_fully_validated r = true -> csrf_request_safe r = true.
Proof. intros r H. unfold csrf_request_fully_validated in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [H _]. exact H. Qed.

(** CSRF_027: Fully validated implies valid referer *)
Theorem CSRF_027_fully_validated_referer :
  forall r, csrf_request_fully_validated r = true -> req_valid_referer r = true.
Proof. intros r H. unfold csrf_request_fully_validated in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

(** CSRF_028: Fully validated implies cookie present *)
Theorem CSRF_028_fully_validated_cookie :
  forall r, csrf_request_fully_validated r = true -> req_cookie_present r = true.
Proof. intros r H. unfold csrf_request_fully_validated in H.
  apply andb_true_iff in H; destruct H as [_ H]. exact H. Qed.

(** CSRF_029: Full validation implies token and origin *)
Theorem CSRF_029_full_implies_token_and_origin :
  forall r, csrf_request_fully_validated r = true ->
  req_has_token r = true /\ req_same_origin r = true.
Proof. intros r H.
  assert (Hs := CSRF_026_fully_validated_implies_safe r H).
  split. apply CSRF_023_safe_has_token. exact Hs.
  apply CSRF_025_safe_same_origin. exact Hs. Qed.

(** CSRF_030: Config protection implies all request checks available *)
Theorem CSRF_030_config_enables_request_checks :
  forall c, csrf_protected c = true ->
  csrf_token_validation c = true /\ csrf_referer_check c = true /\ csrf_double_submit c = true.
Proof. intros c H.
  split. apply CSRF_006. exact H.
  split. apply CSRF_009. exact H.
  apply CSRF_010. exact H. Qed.

(** CSRF_031: Referer check is part of csrf_protected *)
Theorem CSRF_031_referer_in_protection :
  csrf_referer_check riina_csrf = true.
Proof. reflexivity. Qed.

(** CSRF_032: Complete request validation *)
Theorem CSRF_032_complete_request_validation :
  forall r, csrf_request_fully_validated r = true ->
  req_has_token r = true /\ req_token_matches r = true /\
  req_same_origin r = true /\ req_valid_referer r = true /\
  req_cookie_present r = true.
Proof. intros r H.
  assert (Hs := CSRF_026_fully_validated_implies_safe r H).
  split. apply CSRF_023_safe_has_token. exact Hs.
  split. apply CSRF_024_safe_token_matches. exact Hs.
  split. apply CSRF_025_safe_same_origin. exact Hs.
  split. apply CSRF_027_fully_validated_referer. exact H.
  apply CSRF_028_fully_validated_cookie. exact H. Qed.

(** CSRF_033: Config with all false is not protected *)
Theorem CSRF_033_all_false_not_protected :
  csrf_protected (mkCSRF false false false false false) = false.
Proof. reflexivity. Qed.

(** CSRF_034: Missing token validation breaks protection *)
Theorem CSRF_034_missing_token_breaks :
  csrf_protected (mkCSRF false true true true true) = false.
Proof. reflexivity. Qed.

(** CSRF_035: Protection reconstruction from components *)
Theorem CSRF_035_protection_reconstruction :
  forall c,
  csrf_token_validation c = true ->
  csrf_same_site_cookies c = true ->
  csrf_origin_check c = true ->
  csrf_referer_check c = true ->
  csrf_double_submit c = true ->
  csrf_protected c = true.
Proof. intros c H1 H2 H3 H4 H5.
  unfold csrf_protected. rewrite H1, H2, H3, H4, H5. reflexivity. Qed.
