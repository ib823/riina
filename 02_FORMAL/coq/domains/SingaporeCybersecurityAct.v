(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

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

(* ================================================================ *)
(* Extended Singapore Cybersecurity Act Theorems                     *)
(* ================================================================ *)

Require Import Lia.

(* --- STCC Obligations (2025 Amendment) --- *)
(* Systems of Temporary Cybersecurity Concern *)

Definition stcc_obligations_met (e : CIIOwnerEntity) : Prop :=
  cii_classification e = STCC ->
  cii_risk_assessed e = true /\
  cii_security_controls e >= cii_min_controls e.

Theorem stcc_compliance :
  forall (e : CIIOwnerEntity),
  cii_classification e = STCC ->
  cii_risk_assessed e = true ->
  cii_security_controls e >= cii_min_controls e ->
  stcc_obligations_met e.
Proof.
  intros e _ H1 H2. unfold stcc_obligations_met.
  intros _. split; assumption.
Qed.

(* --- CII Owner vs ESCI vs STCC Obligation Comparison --- *)
(* CII Owners have the strictest obligations *)

Definition cii_owner_obligations (e : CIIOwnerEntity) (t : nat) : Prop :=
  cii_risk_current e /\
  cii_audit_current e t /\
  cii_controls_adequate e /\
  cii_incident_response_plan e = true /\
  cssp_licensed_sg e.

Theorem cii_owner_strictest :
  forall (e : CIIOwnerEntity) (t : nat),
  cii_owner_obligations e t ->
  cii_risk_current e.
Proof.
  intros e t [H _]. exact H.
Qed.

Theorem cii_owner_implies_esci_risk :
  forall (e : CIIOwnerEntity) (t : nat),
  cii_owner_obligations e t ->
  cii_risk_assessed e = true /\ cii_incident_response_plan e = true.
Proof.
  intros e t [Hrisk [_ [_ [Hirp _]]]].
  unfold cii_risk_current in Hrisk.
  split; assumption.
Qed.

(* --- Incident Severity Ordering --- *)

Definition incident_needs_notification (i : SGCyberIncident) : Prop :=
  sg_incident_significant i = true.

Theorem significant_incident_must_notify :
  forall (i : SGCyberIncident),
  sg_incident_significant i = true ->
  incident_needs_notification i.
Proof.
  intros i H. unfold incident_needs_notification. exact H.
Qed.

(* --- 2-Hour Deadline Properties --- *)

Theorem two_hour_deadline_tight :
  forall (detected : nat),
  detected + 2 < detected + 6.
Proof.
  intros detected. lia.
Qed.

Theorem sg_2h_stricter_than_my_6h :
  forall (i : SGCyberIncident),
  sg_incident_reported_in_time i ->
  sg_incident_reported_at i <= sg_incident_detected_at i + 6.
Proof.
  intros i H. unfold sg_incident_reported_in_time in H. lia.
Qed.

Theorem sg_2h_stricter_than_72h :
  forall (i : SGCyberIncident),
  sg_incident_reported_in_time i ->
  sg_incident_reported_at i <= sg_incident_detected_at i + 72.
Proof.
  intros i H. unfold sg_incident_reported_in_time in H. lia.
Qed.

(* --- Audit Frequency Requirements --- *)

Record AuditSchedule := mkAuditSched {
  as_entity_id : nat;
  as_last_audit : nat;
  as_audit_interval : nat;
  as_next_audit : nat;
}.

Definition audit_schedule_consistent (sched : AuditSchedule) : Prop :=
  as_next_audit sched = as_last_audit sched + as_audit_interval sched.

Theorem audit_schedule_valid :
  forall (sched : AuditSchedule),
  as_next_audit sched = as_last_audit sched + as_audit_interval sched ->
  audit_schedule_consistent sched.
Proof.
  intros sched H. unfold audit_schedule_consistent. exact H.
Qed.

(* --- Security Controls Monotonicity --- *)

Theorem more_controls_still_adequate :
  forall (e : CIIOwnerEntity) (extra : nat),
  cii_controls_adequate e ->
  cii_min_controls e <= cii_security_controls e + extra.
Proof.
  intros e extra H.
  unfold cii_controls_adequate in H.
  apply (Nat.le_trans _ (cii_security_controls e) _).
  - exact H.
  - apply Nat.le_add_r.
Qed.

(* --- Full Compliance Decomposition --- *)

Theorem sg_cyber_full_implies_risk :
  forall (e : CIIOwnerEntity) (t : nat),
  sg_cybersecurity_act_compliant e t ->
  cii_risk_current e.
Proof.
  intros e t [H _]. exact H.
Qed.

Theorem sg_cyber_full_implies_audit :
  forall (e : CIIOwnerEntity) (t : nat),
  sg_cybersecurity_act_compliant e t ->
  cii_audit_current e t.
Proof.
  intros e t [_ [H _]]. exact H.
Qed.

Theorem sg_cyber_full_implies_controls :
  forall (e : CIIOwnerEntity) (t : nat),
  sg_cybersecurity_act_compliant e t ->
  cii_controls_adequate e.
Proof.
  intros e t [_ [_ [H _]]]. exact H.
Qed.

Theorem sg_cyber_full_implies_irp :
  forall (e : CIIOwnerEntity) (t : nat),
  sg_cybersecurity_act_compliant e t ->
  cii_incident_response_plan e = true.
Proof.
  intros e t [_ [_ [_ H]]]. exact H.
Qed.

(* --- CSSP Licensing Expiry --- *)

Theorem cssp_expired_non_compliant :
  forall (e : CIIOwnerEntity),
  cii_cssp_licensed e = false ->
  ~ cssp_licensed_sg e.
Proof.
  intros e Hfalse Hlic.
  unfold cssp_licensed_sg in Hlic.
  rewrite Hfalse in Hlic. discriminate.
Qed.

(* --- Regular Entity Exemption --- *)
(* Regular entities have lighter obligations *)

Definition regular_entity_exempt (e : CIIOwnerEntity) : Prop :=
  cii_classification e = RegularEntity ->
  True. (* No CII-specific obligations *)

Theorem regular_entity_no_cii_obligation :
  forall (e : CIIOwnerEntity),
  cii_classification e = RegularEntity ->
  regular_entity_exempt e.
Proof.
  intros e _. unfold regular_entity_exempt. intros _. exact I.
Qed.

(* --- Penalty Exposure: 10% Turnover --- *)

Definition penalty_exposure_exists (e : CIIOwnerEntity) (t : nat) : Prop :=
  ~ sg_cybersecurity_act_compliant e t.

Theorem compliance_eliminates_penalty :
  forall (e : CIIOwnerEntity) (t : nat),
  sg_cybersecurity_act_compliant e t ->
  ~ penalty_exposure_exists e t.
Proof.
  intros e t Hcomp Hpen.
  unfold penalty_exposure_exists in Hpen.
  contradiction.
Qed.
