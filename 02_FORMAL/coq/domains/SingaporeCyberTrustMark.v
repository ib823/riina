(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* SingaporeCyberTrustMark.v - Cyber Trust Mark (SS 712:2025) *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Legal Requirement: SS 712:2025 (Singapore Standard) *)
(* Governing Body: CSA / IMDA *)
(* Note: Mandatory for CSSP from January 1, 2027 *)

(* ========================================================================= *)
(* Cyber Trust Mark covers 5 domains across 4 tiers:                         *)
(*   Domain 1: Cyber Governance                                              *)
(*   Domain 2: Cyber Protection                                              *)
(*   Domain 3: Cyber Resilience                                              *)
(*   Domain 4: Cyber Assurance (AI + Cloud + OT extensions in 2025)          *)
(*   Domain 5: Cyber Education                                               *)
(*                                                                           *)
(* Tiers: Essential, Intermediate, Advanced, Expert                          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* ================================================================ *)
(* Tier Model                                                        *)
(* ================================================================ *)

Inductive CTMTier : Type :=
  | Essential : CTMTier
  | Intermediate : CTMTier
  | Advanced : CTMTier
  | Expert : CTMTier.

Definition tier_level (t : CTMTier) : nat :=
  match t with
  | Essential => 1
  | Intermediate => 2
  | Advanced => 3
  | Expert => 4
  end.

(* ================================================================ *)
(* Domain Scores                                                     *)
(* ================================================================ *)

Record CTMAssessment := mkCTM {
  ctm_governance : nat;      (* Domain 1 score 0-100 *)
  ctm_protection : nat;      (* Domain 2 score 0-100 *)
  ctm_resilience : nat;      (* Domain 3 score 0-100 *)
  ctm_assurance : nat;       (* Domain 4 score 0-100 *)
  ctm_education : nat;       (* Domain 5 score 0-100 *)
  ctm_ai_security : bool;    (* 2025 extension: AI controls *)
  ctm_cloud_security : bool; (* 2025 extension: Cloud controls *)
  ctm_ot_security : bool;    (* 2025 extension: OT controls *)
}.

(* Minimum threshold per tier *)
Definition tier_threshold (t : CTMTier) : nat :=
  match t with
  | Essential => 30
  | Intermediate => 50
  | Advanced => 70
  | Expert => 90
  end.

(* ================================================================ *)
(* Domain 1: Cyber Governance                                        *)
(* ================================================================ *)

Definition governance_meets_tier (a : CTMAssessment) (t : CTMTier) : Prop :=
  tier_threshold t <= ctm_governance a.

Theorem ctm_governance_check :
  forall (a : CTMAssessment) (t : CTMTier),
  tier_threshold t <= ctm_governance a ->
  governance_meets_tier a t.
Proof.
  intros a t H. unfold governance_meets_tier. exact H.
Qed.

(* ================================================================ *)
(* Domain 2: Cyber Protection                                        *)
(* ================================================================ *)

Definition protection_meets_tier (a : CTMAssessment) (t : CTMTier) : Prop :=
  tier_threshold t <= ctm_protection a.

Theorem ctm_protection_check :
  forall (a : CTMAssessment) (t : CTMTier),
  tier_threshold t <= ctm_protection a ->
  protection_meets_tier a t.
Proof.
  intros a t H. unfold protection_meets_tier. exact H.
Qed.

(* ================================================================ *)
(* Domain 3: Cyber Resilience                                        *)
(* ================================================================ *)

Definition resilience_meets_tier (a : CTMAssessment) (t : CTMTier) : Prop :=
  tier_threshold t <= ctm_resilience a.

Theorem ctm_resilience_check :
  forall (a : CTMAssessment) (t : CTMTier),
  tier_threshold t <= ctm_resilience a ->
  resilience_meets_tier a t.
Proof.
  intros a t H. unfold resilience_meets_tier. exact H.
Qed.

(* ================================================================ *)
(* Domain 4: Cyber Assurance (+ 2025 AI/Cloud/OT extensions)         *)
(* ================================================================ *)

Definition assurance_meets_tier (a : CTMAssessment) (t : CTMTier) : Prop :=
  tier_threshold t <= ctm_assurance a.

Theorem ctm_assurance_check :
  forall (a : CTMAssessment) (t : CTMTier),
  tier_threshold t <= ctm_assurance a ->
  assurance_meets_tier a t.
Proof.
  intros a t H. unfold assurance_meets_tier. exact H.
Qed.

(* ================================================================ *)
(* Domain 5: Cyber Education                                         *)
(* ================================================================ *)

Definition education_meets_tier (a : CTMAssessment) (t : CTMTier) : Prop :=
  tier_threshold t <= ctm_education a.

Theorem ctm_education_check :
  forall (a : CTMAssessment) (t : CTMTier),
  tier_threshold t <= ctm_education a ->
  education_meets_tier a t.
Proof.
  intros a t H. unfold education_meets_tier. exact H.
Qed.

(* ================================================================ *)
(* 2025 Extension: AI Security                                       *)
(* ================================================================ *)

Definition ai_security_assessed (a : CTMAssessment) : Prop :=
  ctm_ai_security a = true.

Theorem ctm_ai_check :
  forall (a : CTMAssessment),
  ctm_ai_security a = true ->
  ai_security_assessed a.
Proof.
  intros a H. unfold ai_security_assessed. exact H.
Qed.

(* ================================================================ *)
(* Tier Certification                                                *)
(* All 5 domains must meet the tier threshold                        *)
(* ================================================================ *)

Definition ctm_certified_at_tier (a : CTMAssessment) (t : CTMTier) : Prop :=
  governance_meets_tier a t /\
  protection_meets_tier a t /\
  resilience_meets_tier a t /\
  assurance_meets_tier a t /\
  education_meets_tier a t.

Theorem ctm_certification :
  forall (a : CTMAssessment) (t : CTMTier),
  governance_meets_tier a t ->
  protection_meets_tier a t ->
  resilience_meets_tier a t ->
  assurance_meets_tier a t ->
  education_meets_tier a t ->
  ctm_certified_at_tier a t.
Proof.
  intros a t H1 H2 H3 H4 H5. unfold ctm_certified_at_tier.
  split. exact H1. split. exact H2. split. exact H3.
  split. exact H4. exact H5.
Qed.

(* Higher tier subsumes lower *)
Theorem tier_monotonicity :
  forall (t1 t2 : CTMTier),
  tier_level t1 <= tier_level t2 ->
  tier_threshold t1 <= tier_threshold t2.
Proof.
  intros t1 t2. destruct t1, t2; simpl; intro H; lia.
Qed.

(* Tier coverage *)
Definition all_ctm_tiers : list CTMTier :=
  [Essential; Intermediate; Advanced; Expert].

Theorem ctm_tier_coverage :
  forall (t : CTMTier), In t all_ctm_tiers.
Proof.
  intros t. destruct t; simpl; auto 5.
Qed.

(* ================================================================ *)
(* Extended Singapore Cyber Trust Mark Theorems                      *)
(* ================================================================ *)

(* --- Tier Level Properties --- *)

Theorem essential_is_tier_1 :
  tier_level Essential = 1.
Proof.
  simpl. reflexivity.
Qed.

Theorem expert_is_tier_4 :
  tier_level Expert = 4.
Proof.
  simpl. reflexivity.
Qed.

Theorem tier_level_positive :
  forall (t : CTMTier),
  tier_level t >= 1.
Proof.
  intros t. destruct t; simpl; lia.
Qed.

Theorem tier_level_bounded :
  forall (t : CTMTier),
  tier_level t <= 4.
Proof.
  intros t. destruct t; simpl; lia.
Qed.

(* --- Threshold Properties --- *)

Theorem essential_threshold_30 :
  tier_threshold Essential = 30.
Proof.
  simpl. reflexivity.
Qed.

Theorem expert_threshold_90 :
  tier_threshold Expert = 90.
Proof.
  simpl. reflexivity.
Qed.

Theorem threshold_positive :
  forall (t : CTMTier),
  tier_threshold t >= 30.
Proof.
  intros t. destruct t; simpl; lia.
Qed.

Theorem threshold_bounded :
  forall (t : CTMTier),
  tier_threshold t <= 90.
Proof.
  intros t. destruct t; simpl; lia.
Qed.

(* --- Higher Tier Subsumption --- *)
(* If certified at a higher tier, all lower tiers are met *)

Theorem certified_expert_implies_advanced :
  forall (a : CTMAssessment),
  ctm_certified_at_tier a Expert ->
  ctm_certified_at_tier a Advanced.
Proof.
  intros a [Hg [Hp [Hr [Ha He]]]].
  unfold ctm_certified_at_tier.
  unfold governance_meets_tier, protection_meets_tier,
         resilience_meets_tier, assurance_meets_tier,
         education_meets_tier in *.
  repeat split; lia.
Qed.

Theorem certified_advanced_implies_intermediate :
  forall (a : CTMAssessment),
  ctm_certified_at_tier a Advanced ->
  ctm_certified_at_tier a Intermediate.
Proof.
  intros a [Hg [Hp [Hr [Ha He]]]].
  unfold ctm_certified_at_tier.
  unfold governance_meets_tier, protection_meets_tier,
         resilience_meets_tier, assurance_meets_tier,
         education_meets_tier in *.
  repeat split; lia.
Qed.

Theorem certified_intermediate_implies_essential :
  forall (a : CTMAssessment),
  ctm_certified_at_tier a Intermediate ->
  ctm_certified_at_tier a Essential.
Proof.
  intros a [Hg [Hp [Hr [Ha He]]]].
  unfold ctm_certified_at_tier.
  unfold governance_meets_tier, protection_meets_tier,
         resilience_meets_tier, assurance_meets_tier,
         education_meets_tier in *.
  repeat split; lia.
Qed.

(* --- 2025 Extension: Cloud Security Assessment --- *)

Definition cloud_security_assessed (a : CTMAssessment) : Prop :=
  ctm_cloud_security a = true.

Theorem ctm_cloud_check :
  forall (a : CTMAssessment),
  ctm_cloud_security a = true ->
  cloud_security_assessed a.
Proof.
  intros a H. unfold cloud_security_assessed. exact H.
Qed.

(* --- 2025 Extension: OT Security Assessment --- *)

Definition ot_security_assessed (a : CTMAssessment) : Prop :=
  ctm_ot_security a = true.

Theorem ctm_ot_check :
  forall (a : CTMAssessment),
  ctm_ot_security a = true ->
  ot_security_assessed a.
Proof.
  intros a H. unfold ot_security_assessed. exact H.
Qed.

(* --- Full 2025 Extension Compliance --- *)

Definition ctm_2025_extensions_compliant (a : CTMAssessment) : Prop :=
  ai_security_assessed a /\
  cloud_security_assessed a /\
  ot_security_assessed a.

Theorem ctm_2025_full :
  forall (a : CTMAssessment),
  ctm_ai_security a = true ->
  ctm_cloud_security a = true ->
  ctm_ot_security a = true ->
  ctm_2025_extensions_compliant a.
Proof.
  intros a H1 H2 H3.
  unfold ctm_2025_extensions_compliant.
  split. unfold ai_security_assessed. exact H1.
  split. unfold cloud_security_assessed. exact H2.
  unfold ot_security_assessed. exact H3.
Qed.

(* --- Domain Score Minimum Check --- *)

Definition all_domains_above (a : CTMAssessment) (min : nat) : Prop :=
  ctm_governance a >= min /\
  ctm_protection a >= min /\
  ctm_resilience a >= min /\
  ctm_assurance a >= min /\
  ctm_education a >= min.

Theorem all_domains_above_implies_tier :
  forall (a : CTMAssessment) (t : CTMTier),
  all_domains_above a (tier_threshold t) ->
  ctm_certified_at_tier a t.
Proof.
  intros a t [Hg [Hp [Hr [Ha He]]]].
  unfold ctm_certified_at_tier.
  unfold governance_meets_tier, protection_meets_tier,
         resilience_meets_tier, assurance_meets_tier,
         education_meets_tier.
  repeat split; lia.
Qed.

(* --- CSSP Mandatory CTM (from Jan 2027) --- *)

Record CSSPEntity := mkCSSPEntity {
  cssp_entity_id : nat;
  cssp_ctm_tier : CTMTier;
  cssp_ctm_certified : bool;
  cssp_license_valid : bool;
}.

Definition cssp_ctm_requirement (e : CSSPEntity) : Prop :=
  cssp_ctm_certified e = true /\
  cssp_license_valid e = true.

Theorem cssp_must_have_ctm :
  forall (e : CSSPEntity),
  cssp_ctm_certified e = true ->
  cssp_license_valid e = true ->
  cssp_ctm_requirement e.
Proof.
  intros e H1 H2. unfold cssp_ctm_requirement. split; assumption.
Qed.

Theorem cssp_without_ctm_non_compliant :
  forall (e : CSSPEntity),
  cssp_ctm_certified e = false ->
  ~ cssp_ctm_requirement e.
Proof.
  intros e Hfalse [Hctm _].
  rewrite Hfalse in Hctm. discriminate.
Qed.

(* --- Expert Tier: Maximum Certification Properties --- *)

Theorem expert_requires_90_all_domains :
  forall (a : CTMAssessment),
  ctm_certified_at_tier a Expert ->
  ctm_governance a >= 90 /\ ctm_protection a >= 90 /\
  ctm_resilience a >= 90 /\ ctm_assurance a >= 90 /\
  ctm_education a >= 90.
Proof.
  intros a [Hg [Hp [Hr [Ha He]]]].
  unfold governance_meets_tier, protection_meets_tier,
         resilience_meets_tier, assurance_meets_tier,
         education_meets_tier in *.
  simpl in *. repeat split; lia.
Qed.
