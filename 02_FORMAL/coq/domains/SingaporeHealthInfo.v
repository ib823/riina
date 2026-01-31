(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* SingaporeHealthInfo.v - Health Information Bill (passed Jan 12, 2026) *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Legal Requirement: Health Information Bill, effective early 2027 *)
(* Governing Body: Ministry of Health Singapore (MOH) *)
(* Penalties: Up to S$1,000,000 for inadequate cybersecurity *)

(* ========================================================================= *)
(* The Health Information Bill establishes:                                   *)
(*   - National Electronic Health Record (NEHR) mandatory data sharing       *)
(*   - Healthcare provider cybersecurity obligations                          *)
(*   - Patient data access rights                                            *)
(*   - Data correction and audit trail requirements                          *)
(*   - Prohibited uses of health information                                 *)
(*   - Cross-institutional health data exchange framework                    *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* ================================================================ *)
(* Healthcare Provider Model                                         *)
(* ================================================================ *)

Inductive SGHealthcareProvider : Type :=
  | PublicHospital : SGHealthcareProvider
  | PrivateHospital : SGHealthcareProvider
  | GPClinic : SGHealthcareProvider
  | SpecialistClinic : SGHealthcareProvider
  | Polyclinic : SGHealthcareProvider
  | Pharmacy_SG : SGHealthcareProvider.

Inductive HealthInfoCategory : Type :=
  | GeneralHealth : HealthInfoCategory
  | MentalHealthSG : HealthInfoCategory
  | HIV_STI_SG : HealthInfoCategory
  | GeneticInfo : HealthInfoCategory
  | SubstanceAbuse : HealthInfoCategory.

Record SGHealthRecord := mkSGHealth {
  sgh_patient_id : nat;
  sgh_category : HealthInfoCategory;
  sgh_provider_type : SGHealthcareProvider;
  sgh_encrypted : bool;
  sgh_access_controlled : bool;
  sgh_audit_logged : bool;
  sgh_nehr_shared : bool;         (* Shared to National EHR *)
  sgh_cybersecurity_adequate : bool;
}.

(* ================================================================ *)
(* Requirement 1: Cybersecurity Obligations                          *)
(* Providers must implement adequate cybersecurity measures           *)
(* Failure: S$1,000,000 penalty                                      *)
(* ================================================================ *)

Definition hib_cybersecurity (r : SGHealthRecord) : Prop :=
  sgh_encrypted r = true /\
  sgh_access_controlled r = true /\
  sgh_cybersecurity_adequate r = true.

Theorem hib_req_1 :
  forall (r : SGHealthRecord),
  sgh_encrypted r = true ->
  sgh_access_controlled r = true ->
  sgh_cybersecurity_adequate r = true ->
  hib_cybersecurity r.
Proof.
  intros r H1 H2 H3. unfold hib_cybersecurity.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* ================================================================ *)
(* Requirement 2: NEHR Data Sharing                                  *)
(* Mandatory contribution to National Electronic Health Record        *)
(* ================================================================ *)

Definition nehr_sharing_compliant (r : SGHealthRecord) : Prop :=
  sgh_nehr_shared r = true /\ sgh_encrypted r = true.

Theorem hib_req_2 :
  forall (r : SGHealthRecord),
  sgh_nehr_shared r = true ->
  sgh_encrypted r = true ->
  nehr_sharing_compliant r.
Proof.
  intros r H1 H2. unfold nehr_sharing_compliant. split; assumption.
Qed.

(* ================================================================ *)
(* Requirement 3: Audit Trail                                        *)
(* All access to health information must be logged                   *)
(* ================================================================ *)

Definition hib_audit_compliant (r : SGHealthRecord) : Prop :=
  sgh_audit_logged r = true.

Theorem hib_req_3 :
  forall (r : SGHealthRecord),
  sgh_audit_logged r = true ->
  hib_audit_compliant r.
Proof.
  intros r H. unfold hib_audit_compliant. exact H.
Qed.

(* ================================================================ *)
(* Requirement 4: Sensitive Category Protection                      *)
(* Mental health, HIV/STI, genetic, substance abuse — enhanced       *)
(* ================================================================ *)

Definition sg_health_sensitive (c : HealthInfoCategory) : Prop :=
  c = MentalHealthSG \/ c = HIV_STI_SG \/ c = GeneticInfo \/ c = SubstanceAbuse.

Definition sensitive_health_protected (r : SGHealthRecord) : Prop :=
  sg_health_sensitive (sgh_category r) ->
  hib_cybersecurity r /\ hib_audit_compliant r.

Theorem hib_req_4 :
  forall (r : SGHealthRecord),
  hib_cybersecurity r ->
  hib_audit_compliant r ->
  sensitive_health_protected r.
Proof.
  intros r Hcyber Haudit. unfold sensitive_health_protected.
  intros _. split; assumption.
Qed.

(* ================================================================ *)
(* Requirement 5: Prohibited Uses                                    *)
(* Health info cannot be used for insurance underwriting denial, etc. *)
(* ================================================================ *)

Inductive UseType : Type :=
  | Treatment : UseType
  | Research : UseType
  | PublicHealth : UseType
  | InsuranceUnderwriting : UseType   (* PROHIBITED *)
  | Employment : UseType.             (* PROHIBITED *)

Definition use_permitted (u : UseType) : Prop :=
  match u with
  | Treatment => True
  | Research => True
  | PublicHealth => True
  | InsuranceUnderwriting => False
  | Employment => False
  end.

Theorem hib_prohibited_insurance :
  ~ use_permitted InsuranceUnderwriting.
Proof.
  simpl. auto.
Qed.

Theorem hib_prohibited_employment :
  ~ use_permitted Employment.
Proof.
  simpl. auto.
Qed.

Theorem hib_treatment_allowed :
  use_permitted Treatment.
Proof.
  simpl. exact I.
Qed.

(* ================================================================ *)
(* Full HIB Compliance                                               *)
(* ================================================================ *)

Definition hib_fully_compliant (r : SGHealthRecord) : Prop :=
  hib_cybersecurity r /\
  hib_audit_compliant r /\
  nehr_sharing_compliant r.

Theorem hib_composition :
  forall (r : SGHealthRecord),
  hib_cybersecurity r ->
  hib_audit_compliant r ->
  nehr_sharing_compliant r ->
  hib_fully_compliant r.
Proof.
  intros r H1 H2 H3. unfold hib_fully_compliant.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* Provider coverage *)
Definition all_sg_providers : list SGHealthcareProvider :=
  [PublicHospital; PrivateHospital; GPClinic; SpecialistClinic;
   Polyclinic; Pharmacy_SG].

Theorem sg_provider_coverage :
  forall (p : SGHealthcareProvider), In p all_sg_providers.
Proof.
  intros p. destruct p; simpl; auto 7.
Qed.

(* Health info category coverage *)
Definition all_health_categories : list HealthInfoCategory :=
  [GeneralHealth; MentalHealthSG; HIV_STI_SG; GeneticInfo; SubstanceAbuse].

Theorem health_category_coverage :
  forall (c : HealthInfoCategory), In c all_health_categories.
Proof.
  intros c. destruct c; simpl; auto 6.
Qed.
