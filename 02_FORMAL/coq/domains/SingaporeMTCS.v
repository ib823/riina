(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* SingaporeMTCS.v - Multi-Tier Cloud Security (SS 584:2020) *)
(* and GovTech IM8 (Instruction Manual 8) *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Governing Body: IMDA (MTCS) / GovTech (IM8) *)

(* ========================================================================= *)
(* MTCS (SS 584:2020) — 3 security tiers for cloud services:                *)
(*   Level 1: Basic security (non-sensitive data)                            *)
(*   Level 2: More stringent (sensitive business data)                       *)
(*   Level 3: Most stringent (regulated data requiring sovereignty)          *)
(*                                                                           *)
(* GovTech IM8 — ICT security policies for Singapore government:             *)
(*   - Data classification (Official, Restricted, Confidential, Secret)      *)
(*   - Government cloud (GCC) security requirements                          *)
(*   - Security assessment for government systems                            *)
(*   - Vendor security requirements                                          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================ *)
(* MTCS Tier Model                                                   *)
(* ================================================================ *)

Inductive MTCSLevel : Type :=
  | MTCS_Level1 : MTCSLevel     (* Non-sensitive *)
  | MTCS_Level2 : MTCSLevel     (* Sensitive business *)
  | MTCS_Level3 : MTCSLevel.    (* Regulated/sovereign *)

Definition mtcs_level_nat (l : MTCSLevel) : nat :=
  match l with MTCS_Level1 => 1 | MTCS_Level2 => 2 | MTCS_Level3 => 3 end.

Record CloudService := mkCloudService {
  cs_id : nat;
  cs_mtcs_level : MTCSLevel;
  cs_data_encrypted_at_rest : bool;
  cs_data_encrypted_in_transit : bool;
  cs_access_controlled : bool;
  cs_audit_logged : bool;
  cs_pen_tested : bool;
  cs_data_sovereign : bool;         (* Data stays in Singapore *)
  cs_iso27001_certified : bool;
}.

(* ================================================================ *)
(* MTCS Level 1: Basic Security                                      *)
(* ================================================================ *)

Definition mtcs_l1_compliant (s : CloudService) : Prop :=
  cs_data_encrypted_in_transit s = true /\
  cs_access_controlled s = true.

Theorem mtcs_level_1 :
  forall (s : CloudService),
  cs_data_encrypted_in_transit s = true ->
  cs_access_controlled s = true ->
  mtcs_l1_compliant s.
Proof.
  intros s H1 H2. unfold mtcs_l1_compliant. split; assumption.
Qed.

(* ================================================================ *)
(* MTCS Level 2: Enhanced Security                                   *)
(* ================================================================ *)

Definition mtcs_l2_compliant (s : CloudService) : Prop :=
  mtcs_l1_compliant s /\
  cs_data_encrypted_at_rest s = true /\
  cs_audit_logged s = true /\
  cs_pen_tested s = true.

Theorem mtcs_level_2 :
  forall (s : CloudService),
  mtcs_l1_compliant s ->
  cs_data_encrypted_at_rest s = true ->
  cs_audit_logged s = true ->
  cs_pen_tested s = true ->
  mtcs_l2_compliant s.
Proof.
  intros s H1 H2 H3 H4. unfold mtcs_l2_compliant.
  split. exact H1. split. exact H2. split. exact H3. exact H4.
Qed.

(* ================================================================ *)
(* MTCS Level 3: Maximum Security (Sovereign)                        *)
(* ================================================================ *)

Definition mtcs_l3_compliant (s : CloudService) : Prop :=
  mtcs_l2_compliant s /\
  cs_data_sovereign s = true /\
  cs_iso27001_certified s = true.

Theorem mtcs_level_3 :
  forall (s : CloudService),
  mtcs_l2_compliant s ->
  cs_data_sovereign s = true ->
  cs_iso27001_certified s = true ->
  mtcs_l3_compliant s.
Proof.
  intros s H1 H2 H3. unfold mtcs_l3_compliant.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* Level 3 implies Level 2 implies Level 1 *)
Theorem mtcs_l3_implies_l2 :
  forall (s : CloudService),
  mtcs_l3_compliant s ->
  mtcs_l2_compliant s.
Proof.
  intros s [H _]. exact H.
Qed.

Theorem mtcs_l2_implies_l1 :
  forall (s : CloudService),
  mtcs_l2_compliant s ->
  mtcs_l1_compliant s.
Proof.
  intros s [H _]. exact H.
Qed.

Theorem mtcs_l3_implies_l1 :
  forall (s : CloudService),
  mtcs_l3_compliant s ->
  mtcs_l1_compliant s.
Proof.
  intros s H. apply mtcs_l2_implies_l1. apply mtcs_l3_implies_l2. exact H.
Qed.

(* ================================================================ *)
(* GovTech IM8: Government Data Classification                       *)
(* ================================================================ *)

Inductive IM8Classification : Type :=
  | IM8_Official : IM8Classification       (* Default *)
  | IM8_Restricted : IM8Classification
  | IM8_Confidential : IM8Classification
  | IM8_Secret : IM8Classification.

Definition im8_level (c : IM8Classification) : nat :=
  match c with
  | IM8_Official => 0
  | IM8_Restricted => 1
  | IM8_Confidential => 2
  | IM8_Secret => 3
  end.

Record GovTechSystem := mkGovTech {
  gt_id : nat;
  gt_classification : IM8Classification;
  gt_on_gcc : bool;                  (* Government Commercial Cloud *)
  gt_security_assessed : bool;
  gt_vendor_cleared : bool;
  gt_encrypted : bool;
  gt_access_controlled_gt : bool;
  gt_audit_logged_gt : bool;
}.

(* ================================================================ *)
(* IM8: Classification-Based Controls                                *)
(* ================================================================ *)

Definition im8_controls_adequate (s : GovTechSystem) : Prop :=
  match gt_classification s with
  | IM8_Official => True
  | IM8_Restricted => gt_access_controlled_gt s = true
  | IM8_Confidential => gt_encrypted s = true /\ gt_access_controlled_gt s = true
  | IM8_Secret => gt_encrypted s = true /\ gt_access_controlled_gt s = true
                  /\ gt_audit_logged_gt s = true
  end.

Theorem im8_official :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Official ->
  im8_controls_adequate s.
Proof.
  intros s H. unfold im8_controls_adequate. rewrite H. exact I.
Qed.

Theorem im8_secret :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Secret ->
  gt_encrypted s = true ->
  gt_access_controlled_gt s = true ->
  gt_audit_logged_gt s = true ->
  im8_controls_adequate s.
Proof.
  intros s Hc He Ha Hau. unfold im8_controls_adequate.
  rewrite Hc. split. exact He. split. exact Ha. exact Hau.
Qed.

(* ================================================================ *)
(* IM8: Security Assessment Requirement                              *)
(* ================================================================ *)

Definition im8_assessed (s : GovTechSystem) : Prop :=
  gt_security_assessed s = true /\ gt_vendor_cleared s = true.

Theorem im8_assessment :
  forall (s : GovTechSystem),
  gt_security_assessed s = true ->
  gt_vendor_cleared s = true ->
  im8_assessed s.
Proof.
  intros s H1 H2. unfold im8_assessed. split; assumption.
Qed.

(* ================================================================ *)
(* Full IM8 Compliance                                               *)
(* ================================================================ *)

Definition im8_fully_compliant (s : GovTechSystem) : Prop :=
  im8_controls_adequate s /\
  im8_assessed s.

Theorem im8_composition :
  forall (s : GovTechSystem),
  im8_controls_adequate s ->
  im8_assessed s ->
  im8_fully_compliant s.
Proof.
  intros s H1 H2. unfold im8_fully_compliant. split; assumption.
Qed.

(* Classification ordering *)
Theorem im8_secret_highest :
  forall (c : IM8Classification),
  im8_level c <= im8_level IM8_Secret.
Proof.
  intros c. destruct c; simpl; auto with arith.
Qed.

(* Coverage *)
Definition all_mtcs_levels : list MTCSLevel :=
  [MTCS_Level1; MTCS_Level2; MTCS_Level3].

Theorem mtcs_level_coverage :
  forall (l : MTCSLevel), In l all_mtcs_levels.
Proof.
  intros l. destruct l; simpl; auto 4.
Qed.

Definition all_im8_classifications : list IM8Classification :=
  [IM8_Official; IM8_Restricted; IM8_Confidential; IM8_Secret].

Theorem im8_classification_coverage :
  forall (c : IM8Classification), In c all_im8_classifications.
Proof.
  intros c. destruct c; simpl; auto 5.
Qed.

(* ================================================================ *)
(* Extended MTCS / IM8 Compliance Theorems                           *)
(* ================================================================ *)

Require Import Lia.

(* --- MTCS Level Numerical Properties --- *)

Theorem mtcs_level_positive :
  forall (l : MTCSLevel),
  mtcs_level_nat l >= 1.
Proof.
  intros l. destruct l; simpl; lia.
Qed.

Theorem mtcs_level_bounded :
  forall (l : MTCSLevel),
  mtcs_level_nat l <= 3.
Proof.
  intros l. destruct l; simpl; lia.
Qed.

Theorem mtcs_level_ordering :
  forall (l1 l2 : MTCSLevel),
  mtcs_level_nat l1 <= mtcs_level_nat l2 \/
  mtcs_level_nat l2 <= mtcs_level_nat l1.
Proof.
  intros l1 l2.
  destruct (Nat.le_ge_cases (mtcs_level_nat l1) (mtcs_level_nat l2)).
  - left. exact H.
  - right. exact H.
Qed.

(* --- MTCS Data-at-Rest Encryption Requirement for L2+ --- *)

Theorem mtcs_l2_requires_encryption :
  forall (s : CloudService),
  mtcs_l2_compliant s ->
  cs_data_encrypted_at_rest s = true.
Proof.
  intros s [_ [Henc _]]. exact Henc.
Qed.

Theorem mtcs_l3_requires_sovereignty :
  forall (s : CloudService),
  mtcs_l3_compliant s ->
  cs_data_sovereign s = true.
Proof.
  intros s [_ [Hsov _]]. exact Hsov.
Qed.

Theorem mtcs_l3_requires_iso27001 :
  forall (s : CloudService),
  mtcs_l3_compliant s ->
  cs_iso27001_certified s = true.
Proof.
  intros s [_ [_ Hiso]]. exact Hiso.
Qed.

(* --- MTCS Level Minimum Data Protection --- *)

Definition mtcs_min_controls (l : MTCSLevel) : nat :=
  match l with
  | MTCS_Level1 => 2  (* transit encryption + access control *)
  | MTCS_Level2 => 5  (* + at-rest encryption + audit + pentest *)
  | MTCS_Level3 => 7  (* + sovereignty + ISO 27001 *)
  end.

Theorem mtcs_controls_monotonic :
  forall (l1 l2 : MTCSLevel),
  mtcs_level_nat l1 <= mtcs_level_nat l2 ->
  mtcs_min_controls l1 <= mtcs_min_controls l2.
Proof.
  intros l1 l2. destruct l1, l2; simpl; intro H; lia.
Qed.

(* --- IM8 Classification Level Properties --- *)

Theorem im8_level_bounded :
  forall (c : IM8Classification),
  im8_level c <= 3.
Proof.
  intros c. destruct c; simpl; lia.
Qed.

Theorem im8_official_lowest :
  forall (c : IM8Classification),
  im8_level IM8_Official <= im8_level c.
Proof.
  intros c. destruct c; simpl; lia.
Qed.

(* --- IM8 Controls Escalation --- *)

Theorem im8_confidential :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Confidential ->
  gt_encrypted s = true ->
  gt_access_controlled_gt s = true ->
  im8_controls_adequate s.
Proof.
  intros s Hc He Ha. unfold im8_controls_adequate.
  rewrite Hc. split; assumption.
Qed.

Theorem im8_restricted :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Restricted ->
  gt_access_controlled_gt s = true ->
  im8_controls_adequate s.
Proof.
  intros s Hc Ha. unfold im8_controls_adequate. rewrite Hc. exact Ha.
Qed.

(* --- IM8 Secret Requires All Controls --- *)

Theorem im8_secret_requires_encryption :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Secret ->
  im8_controls_adequate s ->
  gt_encrypted s = true.
Proof.
  intros s Hc Hctl. unfold im8_controls_adequate in Hctl.
  rewrite Hc in Hctl. destruct Hctl as [He _]. exact He.
Qed.

Theorem im8_secret_requires_access_control :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Secret ->
  im8_controls_adequate s ->
  gt_access_controlled_gt s = true.
Proof.
  intros s Hc Hctl. unfold im8_controls_adequate in Hctl.
  rewrite Hc in Hctl. destruct Hctl as [_ [Ha _]]. exact Ha.
Qed.

Theorem im8_secret_requires_audit :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Secret ->
  im8_controls_adequate s ->
  gt_audit_logged_gt s = true.
Proof.
  intros s Hc Hctl. unfold im8_controls_adequate in Hctl.
  rewrite Hc in Hctl. destruct Hctl as [_ [_ Hau]]. exact Hau.
Qed.

(* --- GCC Cloud Mandate --- *)
(* Government systems should be on Government Commercial Cloud *)

Definition gcc_required (s : GovTechSystem) : Prop :=
  im8_level (gt_classification s) >= 1 ->
  gt_on_gcc s = true.

Theorem gcc_required_for_restricted :
  forall (s : GovTechSystem),
  gt_classification s = IM8_Restricted ->
  gt_on_gcc s = true ->
  gcc_required s.
Proof.
  intros s _ Hgcc. unfold gcc_required. intros _. exact Hgcc.
Qed.

(* --- MTCS and IM8 Cross-Mapping --- *)
(* IM8 Restricted maps to MTCS Level 2; Secret maps to Level 3 *)

Definition im8_to_mtcs_level (c : IM8Classification) : MTCSLevel :=
  match c with
  | IM8_Official => MTCS_Level1
  | IM8_Restricted => MTCS_Level2
  | IM8_Confidential => MTCS_Level2
  | IM8_Secret => MTCS_Level3
  end.

Theorem im8_secret_maps_to_mtcs3 :
  im8_to_mtcs_level IM8_Secret = MTCS_Level3.
Proof.
  simpl. reflexivity.
Qed.

Theorem im8_to_mtcs_monotonic :
  forall (c1 c2 : IM8Classification),
  im8_level c1 <= im8_level c2 ->
  mtcs_level_nat (im8_to_mtcs_level c1) <= mtcs_level_nat (im8_to_mtcs_level c2).
Proof.
  intros c1 c2. destruct c1, c2; simpl; intro H; lia.
Qed.

(* --- Full IM8 + MTCS Integrated Compliance --- *)

Definition integrated_sg_cloud_compliant
  (cs : CloudService) (gs : GovTechSystem) : Prop :=
  mtcs_l2_compliant cs /\
  im8_fully_compliant gs.

Theorem integrated_compliance :
  forall (cs : CloudService) (gs : GovTechSystem),
  mtcs_l2_compliant cs ->
  im8_fully_compliant gs ->
  integrated_sg_cloud_compliant cs gs.
Proof.
  intros cs gs Hmtcs Him8.
  unfold integrated_sg_cloud_compliant. split; assumption.
Qed.

Theorem integrated_implies_encrypted :
  forall (cs : CloudService) (gs : GovTechSystem),
  integrated_sg_cloud_compliant cs gs ->
  cs_data_encrypted_at_rest cs = true.
Proof.
  intros cs gs [Hmtcs _].
  apply mtcs_l2_requires_encryption. exact Hmtcs.
Qed.
