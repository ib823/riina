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
