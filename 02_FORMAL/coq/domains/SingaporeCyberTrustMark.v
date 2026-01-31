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
