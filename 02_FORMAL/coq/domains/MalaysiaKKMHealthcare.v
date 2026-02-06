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

(* ================================================================ *)
(* Extended KKM Healthcare Compliance Theorems                       *)
(* ================================================================ *)

Require Import Coq.Arith.PeanoNat.
Require Import Lia.

(* --- Patient Demographics Not Sensitive --- *)

Theorem demographics_not_sensitive :
  ~ is_sensitive PatientDemographics.
Proof.
  intros [H | H]; discriminate.
Qed.

Theorem clinical_notes_not_sensitive :
  ~ is_sensitive ClinicalNotes.
Proof.
  intros [H | H]; discriminate.
Qed.

Theorem mental_health_is_sensitive_kkm :
  is_sensitive MentalHealth.
Proof.
  unfold is_sensitive. left. reflexivity.
Qed.

Theorem hiv_sti_is_sensitive_kkm :
  is_sensitive HIV_STI.
Proof.
  unfold is_sensitive. right. reflexivity.
Qed.

(* --- Compliance Decomposition --- *)

Theorem kkm_full_implies_confidentiality :
  forall (r : HealthcareRecord),
  kkm_fully_compliant r ->
  patient_confidentiality r.
Proof.
  intros r [H _]. exact H.
Qed.

Theorem kkm_full_implies_audit :
  forall (r : HealthcareRecord),
  kkm_fully_compliant r ->
  emr_audit_compliant r.
Proof.
  intros r [_ [H _]]. exact H.
Qed.

Theorem kkm_full_implies_consent :
  forall (r : HealthcareRecord),
  kkm_fully_compliant r ->
  hc_consent_obtained r = true.
Proof.
  intros r [_ [_ H]]. exact H.
Qed.

(* --- Confidentiality Implies Individual Controls --- *)

Theorem confidentiality_implies_encrypted :
  forall (r : HealthcareRecord),
  patient_confidentiality r ->
  hc_encrypted r = true.
Proof.
  intros r [He _]. exact He.
Qed.

Theorem confidentiality_implies_access_controlled :
  forall (r : HealthcareRecord),
  patient_confidentiality r ->
  hc_access_controlled r = true.
Proof.
  intros r [_ Ha]. exact Ha.
Qed.

(* --- EMR Access: Emergency Override Properties --- *)

Theorem emergency_always_authorized :
  forall (r : HealthcareRecord),
  emr_access_authorized r true.
Proof.
  intros r. unfold emr_access_authorized. right. reflexivity.
Qed.

Theorem non_emergency_requires_consent :
  forall (r : HealthcareRecord),
  hc_consent_obtained r = false ->
  ~ emr_access_authorized r false.
Proof.
  intros r Hno [Hcons | Hemerg].
  - rewrite Hno in Hcons. discriminate.
  - discriminate.
Qed.

(* --- THIS (Total Hospital Information System) Security --- *)

Record THISCompliance := mkTHIS {
  this_hospital_id : nat;
  this_network_segmented : bool;
  this_data_encrypted : bool;
  this_backup_tested : bool;
  this_access_logged : bool;
  this_staff_trained : bool;
}.

Definition this_security_adequate (tc : THISCompliance) : Prop :=
  this_network_segmented tc = true /\
  this_data_encrypted tc = true /\
  this_backup_tested tc = true /\
  this_access_logged tc = true /\
  this_staff_trained tc = true.

Theorem this_compliance :
  forall (tc : THISCompliance),
  this_network_segmented tc = true ->
  this_data_encrypted tc = true ->
  this_backup_tested tc = true ->
  this_access_logged tc = true ->
  this_staff_trained tc = true ->
  this_security_adequate tc.
Proof.
  intros tc H1 H2 H3 H4 H5.
  unfold this_security_adequate.
  split. exact H1. split. exact H2. split. exact H3.
  split. exact H4. exact H5.
Qed.

Theorem this_missing_backup_non_compliant :
  forall (tc : THISCompliance),
  this_backup_tested tc = false ->
  ~ this_security_adequate tc.
Proof.
  intros tc Hf [_ [_ [Hb _]]].
  rewrite Hf in Hb. discriminate.
Qed.

(* --- CCMS (Clinic Management System) Requirements --- *)
(* 2,489 government clinics must comply *)

Record CCMSCompliance := mkCCMS {
  ccms_clinic_id : nat;
  ccms_patient_data_encrypted : bool;
  ccms_prescription_secured : bool;
  ccms_audit_trail : bool;
  ccms_network_secured : bool;
}.

Definition ccms_compliant (cc : CCMSCompliance) : Prop :=
  ccms_patient_data_encrypted cc = true /\
  ccms_prescription_secured cc = true /\
  ccms_audit_trail cc = true /\
  ccms_network_secured cc = true.

Theorem ccms_full_compliance :
  forall (cc : CCMSCompliance),
  ccms_patient_data_encrypted cc = true ->
  ccms_prescription_secured cc = true ->
  ccms_audit_trail cc = true ->
  ccms_network_secured cc = true ->
  ccms_compliant cc.
Proof.
  intros cc H1 H2 H3 H4.
  unfold ccms_compliant.
  split. exact H1. split. exact H2. split. exact H3. exact H4.
Qed.

(* --- Medical Device Integration (IEC 62443 Alignment) --- *)

Record MedicalDeviceSecurity := mkMedDevice {
  md_device_id : nat;
  md_authenticated : bool;
  md_data_encrypted : bool;
  md_firmware_signed : bool;
  md_network_isolated : bool;
  md_security_level : nat;  (* IEC 62443 SL 1-4 *)
}.

Definition md_security_adequate (md : MedicalDeviceSecurity) (min_sl : nat) : Prop :=
  md_authenticated md = true /\
  md_data_encrypted md = true /\
  md_firmware_signed md = true /\
  md_security_level md >= min_sl.

Theorem medical_device_sl2 :
  forall (md : MedicalDeviceSecurity),
  md_authenticated md = true ->
  md_data_encrypted md = true ->
  md_firmware_signed md = true ->
  md_security_level md >= 2 ->
  md_security_adequate md 2.
Proof.
  intros md H1 H2 H3 H4.
  unfold md_security_adequate.
  split. exact H1. split. exact H2. split. exact H3. exact H4.
Qed.

Theorem higher_sl_subsumes :
  forall (md : MedicalDeviceSecurity) (sl1 sl2 : nat),
  sl1 <= sl2 ->
  md_security_adequate md sl2 ->
  md_security_adequate md sl1.
Proof.
  intros md sl1 sl2 Hle [H1 [H2 [H3 H4]]].
  unfold md_security_adequate.
  split. exact H1. split. exact H2. split. exact H3. lia.
Qed.

(* --- Cross-Facility Sharing Requires Encryption --- *)

Theorem cross_facility_requires_encryption :
  forall (r : HealthcareRecord) (target : nat),
  cross_facility_authorized r target ->
  hc_encrypted r = true.
Proof.
  intros r target [_ [He _]]. exact He.
Qed.

Theorem cross_facility_requires_consent :
  forall (r : HealthcareRecord) (target : nat),
  cross_facility_authorized r target ->
  hc_consent_obtained r = true.
Proof.
  intros r target [Hc _]. exact Hc.
Qed.
