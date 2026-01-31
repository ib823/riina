(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* SingaporeCybersecurityAct.v - Singapore Cybersecurity Act 2018 (Amended 2025) *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md §B2 *)
(* Legal Requirement: Cybersecurity Act 2018 (No. 9 of 2018), *)
(*   Amendments effective October 31, 2025 *)
(* Governing Body: Cyber Security Agency of Singapore (CSA) *)
(* Penalties: Up to 10% of annual turnover or S$500,000 *)

(* ========================================================================= *)
(* Singapore Cybersecurity Act establishes:                                   *)
(*   - Critical Information Infrastructure (CII) framework                    *)
(*   - CII owner obligations (risk assessment, audit, incident reporting)     *)
(*   - 2-hour incident notification requirement                               *)
(*   - Cybersecurity Service Provider (CSSP) licensing                        *)
(*   - 2025 amendments: Systems of Temporary Cybersecurity Concern (STCC)    *)
(*   - 2025 amendments: Entities of Special Cybersecurity Interest (ESCI)    *)
(*   - Cyber Trust Mark (SS 712:2025) integration                            *)
(*                                                                           *)
(* CII Sectors (11):                                                         *)
(*   Energy, Water, Banking & Finance, Healthcare, Transport (Land),          *)
(*   Transport (Maritime), Transport (Aviation), Infocomm,                    *)
(*   Media, Security & Emergency, Government                                  *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================ *)
(* CII Sector Model                                                  *)
(* ================================================================ *)

Inductive CIISector : Type :=
  | SGEnergy : CIISector
  | SGWater : CIISector
  | SGBankingFinance : CIISector
  | SGHealthcare : CIISector
  | SGTransportLand : CIISector
  | SGTransportMaritime : CIISector
  | SGTransportAviation : CIISector
  | SGInfocomm : CIISector
  | SGMedia : CIISector
  | SGSecurityEmergency : CIISector
  | SGGovernment : CIISector.

(* Entity classification under 2025 amendments *)
Inductive EntityClassification : Type :=
  | CIIOwner : EntityClassification            (* Critical Information Infrastructure *)
  | ESCI : EntityClassification                 (* Entity of Special Cybersecurity Interest *)
  | STCC : EntityClassification                 (* System of Temporary Cybersecurity Concern *)
  | RegularEntity : EntityClassification.

(* ================================================================ *)
(* CII Owner Model                                                   *)
(* ================================================================ *)

Record CIIOwnerEntity := mkCIIOwner {
  cii_id : nat;
  cii_sector : CIISector;
  cii_classification : EntityClassification;
  cii_risk_assessed : bool;
  cii_audit_completed : bool;
  cii_last_audit : nat;
  cii_incident_response_plan : bool;
  cii_security_controls : nat;
  cii_min_controls : nat;
  cii_cssp_licensed : bool;
}.

(* Incident *)
Record SGCyberIncident := mkSGIncident {
  sg_incident_id : nat;
  sg_incident_detected_at : nat;
  sg_incident_reported_at : nat;
  sg_incident_cii_id : nat;
  sg_incident_significant : bool;  (* Significant cybersecurity incident *)
}.

(* ================================================================ *)
(* Obligation 1: Risk Assessment                                     *)
(* CII owners must conduct regular risk assessments                  *)
(* ================================================================ *)

Definition cii_risk_current (e : CIIOwnerEntity) : Prop :=
  cii_risk_assessed e = true.

Theorem cii_obligation_1 :
  forall (e : CIIOwnerEntity),
  cii_risk_assessed e = true ->
  cii_risk_current e.
Proof.
  intros e H. unfold cii_risk_current. exact H.
Qed.

(* ================================================================ *)
(* Obligation 2: Compliance Audit                                    *)
(* ================================================================ *)

Definition cii_audit_current (e : CIIOwnerEntity) (t : nat) : Prop :=
  cii_audit_completed e = true /\ t <= cii_last_audit e + 365.  (* Annual *)

Theorem cii_obligation_2 :
  forall (e : CIIOwnerEntity) (t : nat),
  cii_audit_completed e = true ->
  t <= cii_last_audit e + 365 ->
  cii_audit_current e t.
Proof.
  intros e t H1 H2. unfold cii_audit_current. split; assumption.
Qed.

(* ================================================================ *)
(* Obligation 3: Incident Notification (2 hours!)                    *)
(* This is the strictest incident reporting in ASEAN                  *)
(* ================================================================ *)

Definition sg_incident_reported_in_time (i : SGCyberIncident) : Prop :=
  sg_incident_reported_at i <= sg_incident_detected_at i + 2.  (* 2 hours *)

Theorem cii_obligation_3 :
  forall (i : SGCyberIncident),
  sg_incident_reported_at i <= sg_incident_detected_at i + 2 ->
  sg_incident_reported_in_time i.
Proof.
  intros i H. unfold sg_incident_reported_in_time. exact H.
Qed.

(* Singapore's 2-hour deadline is stricter than Malaysia's 6-hour *)
Theorem sg_stricter_than_my :
  forall (detected_at reported_at : nat),
  reported_at <= detected_at + 2 ->
  reported_at <= detected_at + 6.
Proof.
  intros d r H. apply (Nat.le_trans _ _ _ H).
  apply Nat.add_le_mono_l. auto with arith.
Qed.

(* ================================================================ *)
(* Obligation 4: Security Controls                                   *)
(* ================================================================ *)

Definition cii_controls_adequate (e : CIIOwnerEntity) : Prop :=
  cii_min_controls e <= cii_security_controls e.

Theorem cii_obligation_4 :
  forall (e : CIIOwnerEntity),
  cii_min_controls e <= cii_security_controls e ->
  cii_controls_adequate e.
Proof.
  intros e H. unfold cii_controls_adequate. exact H.
Qed.

(* ================================================================ *)
(* 2025 Amendment: ESCI Obligations                                  *)
(* Entities of Special Cybersecurity Interest                         *)
(* ================================================================ *)

Definition esci_obligations_met (e : CIIOwnerEntity) : Prop :=
  cii_classification e = ESCI ->
  cii_risk_assessed e = true /\ cii_incident_response_plan e = true.

Theorem esci_compliance :
  forall (e : CIIOwnerEntity),
  cii_classification e = ESCI ->
  cii_risk_assessed e = true ->
  cii_incident_response_plan e = true ->
  esci_obligations_met e.
Proof.
  intros e _ H1 H2. unfold esci_obligations_met. intros _. split; assumption.
Qed.

(* ================================================================ *)
(* 2025 Amendment: CSSP Licensing                                    *)
(* Mandatory from Jan 1, 2027 (Cyber Trust Mark / CTM certification) *)
(* ================================================================ *)

Definition cssp_licensed_sg (e : CIIOwnerEntity) : Prop :=
  cii_cssp_licensed e = true.

Theorem cssp_obligation :
  forall (e : CIIOwnerEntity),
  cii_cssp_licensed e = true ->
  cssp_licensed_sg e.
Proof.
  intros e H. unfold cssp_licensed_sg. exact H.
Qed.

(* ================================================================ *)
(* Full Singapore Cybersecurity Act Compliance                       *)
(* ================================================================ *)

Definition sg_cybersecurity_act_compliant (e : CIIOwnerEntity) (t : nat) : Prop :=
  cii_risk_current e /\
  cii_audit_current e t /\
  cii_controls_adequate e /\
  cii_incident_response_plan e = true.

Theorem sg_cybersecurity_composition :
  forall (e : CIIOwnerEntity) (t : nat),
  cii_risk_current e ->
  cii_audit_current e t ->
  cii_controls_adequate e ->
  cii_incident_response_plan e = true ->
  sg_cybersecurity_act_compliant e t.
Proof.
  intros e t H1 H2 H3 H4.
  unfold sg_cybersecurity_act_compliant.
  split. exact H1.
  split. exact H2.
  split. exact H3.
  exact H4.
Qed.

(* ================================================================ *)
(* CII Sector Coverage                                               *)
(* ================================================================ *)

Definition all_cii_sectors : list CIISector :=
  [SGEnergy; SGWater; SGBankingFinance; SGHealthcare;
   SGTransportLand; SGTransportMaritime; SGTransportAviation;
   SGInfocomm; SGMedia; SGSecurityEmergency; SGGovernment].

Theorem cii_sector_coverage :
  forall (s : CIISector), In s all_cii_sectors.
Proof.
  intros s. destruct s; simpl; auto 12.
Qed.

(* Entity classification coverage *)
Definition all_entity_classifications : list EntityClassification :=
  [CIIOwner; ESCI; STCC; RegularEntity].

Theorem entity_classification_coverage :
  forall (c : EntityClassification), In c all_entity_classifications.
Proof.
  intros c. destruct c; simpl; auto 5.
Qed.
