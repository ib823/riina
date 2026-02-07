(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

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

(* ================================================================ *)
(* Extended Singapore Health Information Bill Theorems               *)
(* ================================================================ *)

Require Import Coq.Arith.PeanoNat.
Require Import Lia.

(* --- Patient Data Access Rights --- *)
(* HIB: Patients have right to access their health records *)

Record PatientAccessRequest := mkPatAccess {
  par_patient_id : nat;
  par_requested_at : nat;
  par_responded_at : nat;
  par_data_provided : bool;
  par_provider : SGHealthcareProvider;
}.

Definition hib_access_deadline : nat := 504. (* 21 days in hours *)

Definition patient_access_fulfilled (req : PatientAccessRequest) : Prop :=
  par_responded_at req <= par_requested_at req + hib_access_deadline /\
  par_data_provided req = true.

Theorem patient_access_right :
  forall (req : PatientAccessRequest),
  par_responded_at req <= par_requested_at req + hib_access_deadline ->
  par_data_provided req = true ->
  patient_access_fulfilled req.
Proof.
  intros req Htime Hdata.
  unfold patient_access_fulfilled.
  split; assumption.
Qed.

Theorem patient_access_late_violation :
  forall (req : PatientAccessRequest),
  par_requested_at req + hib_access_deadline < par_responded_at req ->
  ~ (par_responded_at req <= par_requested_at req + hib_access_deadline).
Proof.
  intros req Hlate Hle.
  apply (Nat.lt_irrefl (par_requested_at req + hib_access_deadline)).
  apply (Nat.lt_le_trans _ _ _ Hlate Hle).
Qed.

(* --- Data Correction and Audit Trail --- *)
(* HIB: Corrections must be logged *)

Record HealthDataCorrection := mkHDCorrection {
  hdc_patient_id : nat;
  hdc_field_corrected : nat;
  hdc_old_value_hash : nat;
  hdc_new_value_hash : nat;
  hdc_corrected_at : nat;
  hdc_corrected_by : nat;
  hdc_audit_logged : bool;
}.

Definition correction_properly_logged (c : HealthDataCorrection) : Prop :=
  hdc_audit_logged c = true /\
  hdc_old_value_hash c <> hdc_new_value_hash c.

Theorem data_correction_logged :
  forall (c : HealthDataCorrection),
  hdc_audit_logged c = true ->
  hdc_old_value_hash c <> hdc_new_value_hash c ->
  correction_properly_logged c.
Proof.
  intros c Hlog Hdiff.
  unfold correction_properly_logged.
  split; assumption.
Qed.

(* --- Cross-Institutional Health Data Exchange --- *)
(* HIB: Data exchange between providers requires framework *)

Record HealthDataExchange := mkHDExchange {
  hde_source_provider : SGHealthcareProvider;
  hde_target_provider : SGHealthcareProvider;
  hde_patient_consent : bool;
  hde_encrypted : bool;
  hde_purpose_treatment : bool;
  hde_audit_logged_exchange : bool;
}.

Definition exchange_authorized (ex : HealthDataExchange) : Prop :=
  hde_patient_consent ex = true /\
  hde_encrypted ex = true /\
  hde_purpose_treatment ex = true /\
  hde_audit_logged_exchange ex = true.

Theorem cross_institutional_exchange :
  forall (ex : HealthDataExchange),
  hde_patient_consent ex = true ->
  hde_encrypted ex = true ->
  hde_purpose_treatment ex = true ->
  hde_audit_logged_exchange ex = true ->
  exchange_authorized ex.
Proof.
  intros ex H1 H2 H3 H4.
  unfold exchange_authorized.
  split. exact H1. split. exact H2. split. exact H3. exact H4.
Qed.

(* --- Sensitive Category Enumeration Properties --- *)

Theorem general_health_not_sensitive :
  ~ sg_health_sensitive GeneralHealth.
Proof.
  intros [H | [H | [H | H]]]; discriminate.
Qed.

Theorem mental_health_is_sensitive :
  sg_health_sensitive MentalHealthSG.
Proof.
  unfold sg_health_sensitive. left. reflexivity.
Qed.

Theorem hiv_sti_is_sensitive :
  sg_health_sensitive HIV_STI_SG.
Proof.
  unfold sg_health_sensitive. right. left. reflexivity.
Qed.

Theorem genetic_info_is_sensitive :
  sg_health_sensitive GeneticInfo.
Proof.
  unfold sg_health_sensitive. right. right. left. reflexivity.
Qed.

(* --- NEHR Mandatory Sharing Compliance --- *)
(* All providers must contribute to NEHR *)

Theorem nehr_requires_encryption :
  forall (r : SGHealthRecord),
  nehr_sharing_compliant r ->
  sgh_encrypted r = true.
Proof.
  intros r [_ Henc]. exact Henc.
Qed.

Theorem nehr_requires_sharing :
  forall (r : SGHealthRecord),
  nehr_sharing_compliant r ->
  sgh_nehr_shared r = true.
Proof.
  intros r [Hshared _]. exact Hshared.
Qed.

(* --- Use Type Exhaustiveness --- *)

Definition all_use_types : list UseType :=
  [Treatment; Research; PublicHealth; InsuranceUnderwriting; Employment].

Theorem use_type_coverage :
  forall (u : UseType), In u all_use_types.
Proof.
  intros u. destruct u; simpl; auto 6.
Qed.

(* --- Permitted Use Properties --- *)

Theorem research_allowed :
  use_permitted Research.
Proof.
  simpl. exact I.
Qed.

Theorem public_health_allowed :
  use_permitted PublicHealth.
Proof.
  simpl. exact I.
Qed.

(* --- Full HIB Compliance Decomposition --- *)

Theorem hib_full_implies_cybersecurity :
  forall (r : SGHealthRecord),
  hib_fully_compliant r ->
  hib_cybersecurity r.
Proof.
  intros r [H _]. exact H.
Qed.

Theorem hib_full_implies_audit :
  forall (r : SGHealthRecord),
  hib_fully_compliant r ->
  hib_audit_compliant r.
Proof.
  intros r [_ [H _]]. exact H.
Qed.

Theorem hib_full_implies_nehr :
  forall (r : SGHealthRecord),
  hib_fully_compliant r ->
  nehr_sharing_compliant r.
Proof.
  intros r [_ [_ H]]. exact H.
Qed.

(* --- Cybersecurity Penalty Threshold --- *)
(* HIB: Penalty up to S$1,000,000 for inadequate cybersecurity *)

Definition hib_penalty_exposure (r : SGHealthRecord) : Prop :=
  ~ hib_cybersecurity r.

Theorem cybersecurity_eliminates_penalty :
  forall (r : SGHealthRecord),
  hib_cybersecurity r ->
  ~ hib_penalty_exposure r.
Proof.
  intros r Hcyber Hpen.
  unfold hib_penalty_exposure in Hpen.
  contradiction.
Qed.

(* --- Provider-Specific Obligations --- *)
(* Public hospitals have mandatory NEHR sharing *)

Definition public_hospital_nehr_mandatory (r : SGHealthRecord) : Prop :=
  sgh_provider_type r = PublicHospital ->
  sgh_nehr_shared r = true.

Theorem public_hospital_must_share :
  forall (r : SGHealthRecord),
  sgh_provider_type r = PublicHospital ->
  sgh_nehr_shared r = true ->
  public_hospital_nehr_mandatory r.
Proof.
  intros r _ Hshared. unfold public_hospital_nehr_mandatory.
  intros _. exact Hshared.
Qed.
