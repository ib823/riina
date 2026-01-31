(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* MalaysiaKKMHealthcare.v - Ministry of Health Malaysia Healthcare Data Security *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Governing Body: Kementerian Kesihatan Malaysia (KKM / MOH) *)

(* ========================================================================= *)
(* KKM healthcare data requirements:                                         *)
(*   - Electronic Medical Record (EMR) security (2026 nationwide rollout)    *)
(*   - Total Hospital Information System (THIS) data protection              *)
(*   - Patient data confidentiality (Doctor-patient privilege)               *)
(*   - CCMS (Clinic Management System) security for 2,489 facilities        *)
(*   - Cross-facility data sharing authorization                             *)
(*   - Medical Device Integration Standards (IEC 62443 alignment)            *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* ================================================================ *)
(* Healthcare Facility Model                                         *)
(* ================================================================ *)

Inductive FacilityType : Type :=
  | Hospital : FacilityType
  | Clinic : FacilityType
  | SpecialistCenter : FacilityType
  | Laboratory : FacilityType
  | Pharmacy : FacilityType.

Inductive EMRClassification : Type :=
  | PatientDemographics : EMRClassification
  | ClinicalNotes : EMRClassification
  | DiagnosticResults : EMRClassification
  | Prescriptions : EMRClassification
  | MentalHealth : EMRClassification     (* Higher protection *)
  | HIV_STI : EMRClassification.         (* Highest protection *)

Record HealthcareRecord := mkHCRecord {
  hc_patient_id : nat;
  hc_classification : EMRClassification;
  hc_facility_id : nat;
  hc_facility_type : FacilityType;
  hc_encrypted : bool;
  hc_access_controlled : bool;
  hc_audit_logged : bool;
  hc_consent_obtained : bool;
}.

(* ================================================================ *)
(* Requirement 1: Patient Data Confidentiality                       *)
(* Doctor-patient privilege — no access without consent               *)
(* ================================================================ *)

Definition patient_confidentiality (r : HealthcareRecord) : Prop :=
  hc_encrypted r = true /\ hc_access_controlled r = true.

Theorem kkm_confidentiality :
  forall (r : HealthcareRecord),
  hc_encrypted r = true ->
  hc_access_controlled r = true ->
  patient_confidentiality r.
Proof.
  intros r H1 H2. unfold patient_confidentiality. split; assumption.
Qed.

(* ================================================================ *)
(* Requirement 2: EMR Access Control                                 *)
(* Access requires patient consent except emergency                  *)
(* ================================================================ *)

Definition emr_access_authorized (r : HealthcareRecord) (is_emergency : bool) : Prop :=
  hc_consent_obtained r = true \/ is_emergency = true.

Theorem kkm_consent_access :
  forall (r : HealthcareRecord),
  hc_consent_obtained r = true ->
  emr_access_authorized r false.
Proof.
  intros r H. unfold emr_access_authorized. left. exact H.
Qed.

Theorem kkm_emergency_access :
  forall (r : HealthcareRecord),
  emr_access_authorized r true.
Proof.
  intros r. unfold emr_access_authorized. right. reflexivity.
Qed.

(* ================================================================ *)
(* Requirement 3: Sensitive Category Enhanced Protection             *)
(* Mental health and HIV/STI require additional safeguards            *)
(* ================================================================ *)

Definition is_sensitive (c : EMRClassification) : Prop :=
  c = MentalHealth \/ c = HIV_STI.

Definition sensitive_protection (r : HealthcareRecord) : Prop :=
  is_sensitive (hc_classification r) ->
  hc_encrypted r = true /\ hc_access_controlled r = true /\ hc_audit_logged r = true.

Theorem kkm_sensitive_protected :
  forall (r : HealthcareRecord),
  hc_encrypted r = true ->
  hc_access_controlled r = true ->
  hc_audit_logged r = true ->
  sensitive_protection r.
Proof.
  intros r H1 H2 H3. unfold sensitive_protection.
  intros _. split. exact H1. split. exact H2. exact H3.
Qed.

(* ================================================================ *)
(* Requirement 4: Audit Trail                                        *)
(* All EMR access must be logged                                     *)
(* ================================================================ *)

Definition emr_audit_compliant (r : HealthcareRecord) : Prop :=
  hc_audit_logged r = true.

Theorem kkm_audit :
  forall (r : HealthcareRecord),
  hc_audit_logged r = true ->
  emr_audit_compliant r.
Proof.
  intros r H. unfold emr_audit_compliant. exact H.
Qed.

(* ================================================================ *)
(* Requirement 5: Cross-Facility Data Sharing                        *)
(* Sharing between facilities requires consent + encryption           *)
(* ================================================================ *)

Definition cross_facility_authorized
  (r : HealthcareRecord) (target_facility : nat) : Prop :=
  hc_consent_obtained r = true /\
  hc_encrypted r = true /\
  hc_facility_id r <> target_facility.

Theorem kkm_cross_facility :
  forall (r : HealthcareRecord) (target : nat),
  hc_consent_obtained r = true ->
  hc_encrypted r = true ->
  hc_facility_id r <> target ->
  cross_facility_authorized r target.
Proof.
  intros r target H1 H2 H3. unfold cross_facility_authorized.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* ================================================================ *)
(* Full KKM Compliance                                               *)
(* ================================================================ *)

Definition kkm_fully_compliant (r : HealthcareRecord) : Prop :=
  patient_confidentiality r /\
  emr_audit_compliant r /\
  hc_consent_obtained r = true.

Theorem kkm_composition :
  forall (r : HealthcareRecord),
  patient_confidentiality r ->
  emr_audit_compliant r ->
  hc_consent_obtained r = true ->
  kkm_fully_compliant r.
Proof.
  intros r H1 H2 H3. unfold kkm_fully_compliant.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* Facility type coverage *)
Definition all_facility_types : list FacilityType :=
  [Hospital; Clinic; SpecialistCenter; Laboratory; Pharmacy].

Theorem facility_coverage :
  forall (f : FacilityType), In f all_facility_types.
Proof.
  intros f. destruct f; simpl; auto 6.
Qed.

(* EMR classification coverage *)
Definition all_emr_classifications : list EMRClassification :=
  [PatientDemographics; ClinicalNotes; DiagnosticResults;
   Prescriptions; MentalHealth; HIV_STI].

Theorem emr_classification_coverage :
  forall (c : EMRClassification), In c all_emr_classifications.
Proof.
  intros c. destruct c; simpl; auto 7.
Qed.
