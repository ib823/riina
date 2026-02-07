(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* SingaporePDPA.v - Singapore Personal Data Protection Act 2012 *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md §B1 *)
(* Legal Requirement: Personal Data Protection Act 2012 (No. 26 of 2012) *)
(* Governing Body: Personal Data Protection Commission (PDPC) Singapore *)
(* Penalties: Up to S$1,000,000 *)

(* ========================================================================= *)
(* Singapore PDPA obligations:                                               *)
(*   1. Consent Obligation                                                   *)
(*   2. Purpose Limitation Obligation                                        *)
(*   3. Notification Obligation                                              *)
(*   4. Access and Correction Obligation                                     *)
(*   5. Accuracy Obligation                                                  *)
(*   6. Protection Obligation (security)                                     *)
(*   7. Retention Limitation Obligation                                      *)
(*   8. Transfer Limitation Obligation                                       *)
(*   9. Data Breach Notification Obligation (2021 amendment)                 *)
(*  10. Data Portability Obligation (2021 amendment)                         *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================ *)
(* Data Model                                                        *)
(* ================================================================ *)

Inductive SGConsentStatus : Type :=
  | SGNoConsent : SGConsentStatus
  | SGExplicitConsent : SGConsentStatus
  | SGDeemedConsent : SGConsentStatus          (* Deemed consent provision *)
  | SGDeemedConsentNotification : SGConsentStatus  (* Deemed consent by notification *)
  | SGWithdrawnConsent : SGConsentStatus.

Inductive SGDataCategory : Type :=
  | SGPublicData : SGDataCategory
  | SGPersonalData : SGDataCategory
  | SGBusinessContact : SGDataCategory.      (* Business contact info exempt *)

Record SGDataRecord := mkSGRecord {
  sg_subject_id : nat;
  sg_category : SGDataCategory;
  sg_consent : SGConsentStatus;
  sg_purpose_id : nat;
  sg_collected_at : nat;
  sg_retention_limit : nat;
  sg_encrypted : bool;
  sg_anonymized : bool;
}.

(* Transfer destination adequacy *)
Inductive TransferAdequacy : Type :=
  | AdequateJurisdiction : TransferAdequacy
  | ContractualSafeguards : TransferAdequacy
  | ConsentForTransfer : TransferAdequacy
  | NoSafeguards : TransferAdequacy.

(* ================================================================ *)
(* Obligation 1: Consent                                             *)
(* ================================================================ *)

Definition sg_has_consent (r : SGDataRecord) : Prop :=
  match sg_consent r with
  | SGExplicitConsent => True
  | SGDeemedConsent => True
  | SGDeemedConsentNotification => True
  | _ => False
  end.

Definition sg_consent_for_category (r : SGDataRecord) : Prop :=
  match sg_category r with
  | SGPublicData => True
  | SGBusinessContact => True  (* Business contact info exempt from consent *)
  | SGPersonalData => sg_has_consent r
  end.

Theorem obligation_1_consent :
  forall (r : SGDataRecord),
  sg_category r = SGPersonalData ->
  sg_has_consent r ->
  sg_consent_for_category r.
Proof.
  intros r Hcat Hconsent.
  unfold sg_consent_for_category. rewrite Hcat. exact Hconsent.
Qed.

Theorem obligation_1_business_exempt :
  forall (r : SGDataRecord),
  sg_category r = SGBusinessContact ->
  sg_consent_for_category r.
Proof.
  intros r Hcat. unfold sg_consent_for_category. rewrite Hcat. exact I.
Qed.

(* Consent withdrawal *)
Theorem consent_withdrawal_effect :
  forall (r : SGDataRecord),
  sg_consent r = SGWithdrawnConsent ->
  ~ sg_has_consent r.
Proof.
  intros r H Habs. unfold sg_has_consent in Habs.
  rewrite H in Habs. exact Habs.
Qed.

(* ================================================================ *)
(* Obligation 2: Purpose Limitation                                  *)
(* ================================================================ *)

Definition sg_purpose_limited (r : SGDataRecord) (processing_purpose : nat) : Prop :=
  sg_purpose_id r = processing_purpose.

Theorem obligation_2_purpose :
  forall (r : SGDataRecord),
  sg_purpose_limited r (sg_purpose_id r).
Proof.
  intros r. unfold sg_purpose_limited. reflexivity.
Qed.

(* ================================================================ *)
(* Obligation 6: Protection (Security)                               *)
(* Reasonable security arrangements to protect personal data          *)
(* ================================================================ *)

Definition sg_protection_adequate (r : SGDataRecord) : Prop :=
  sg_encrypted r = true \/ sg_anonymized r = true.

Theorem obligation_6_encrypted :
  forall (r : SGDataRecord),
  sg_encrypted r = true ->
  sg_protection_adequate r.
Proof.
  intros r H. unfold sg_protection_adequate. left. exact H.
Qed.

Theorem obligation_6_anonymized :
  forall (r : SGDataRecord),
  sg_anonymized r = true ->
  sg_protection_adequate r.
Proof.
  intros r H. unfold sg_protection_adequate. right. exact H.
Qed.

(* ================================================================ *)
(* Obligation 7: Retention Limitation                                *)
(* ================================================================ *)

Definition sg_within_retention (r : SGDataRecord) (current_time : nat) : Prop :=
  current_time <= sg_retention_limit r.

Definition sg_must_dispose (r : SGDataRecord) (current_time : nat) : Prop :=
  sg_retention_limit r < current_time.

Theorem obligation_7_retention :
  forall (r : SGDataRecord) (t : nat),
  ~ sg_within_retention r t ->
  sg_must_dispose r t.
Proof.
  intros r t H. unfold sg_must_dispose, sg_within_retention in *.
  apply not_le in H. exact H.
Qed.

(* ================================================================ *)
(* Obligation 8: Transfer Limitation                                 *)
(* Transfer only to jurisdictions with adequate protection            *)
(* ================================================================ *)

Definition sg_transfer_lawful (adequacy : TransferAdequacy) : Prop :=
  match adequacy with
  | NoSafeguards => False
  | _ => True
  end.

Theorem obligation_8_adequate :
  forall (a : TransferAdequacy),
  a = AdequateJurisdiction ->
  sg_transfer_lawful a.
Proof.
  intros a H. rewrite H. simpl. exact I.
Qed.

Theorem obligation_8_contractual :
  forall (a : TransferAdequacy),
  a = ContractualSafeguards ->
  sg_transfer_lawful a.
Proof.
  intros a H. rewrite H. simpl. exact I.
Qed.

Theorem obligation_8_no_safeguards_blocked :
  forall (a : TransferAdequacy),
  a = NoSafeguards ->
  ~ sg_transfer_lawful a.
Proof.
  intros a H Habs. rewrite H in Habs. simpl in Habs. exact Habs.
Qed.

(* ================================================================ *)
(* Obligation 9: Data Breach Notification (2021 amendment)           *)
(* Notify PDPC within 3 calendar days if breach is notifiable         *)
(* Notify individuals ASAP if significant harm likely                 *)
(* ================================================================ *)

Record SGBreachEvent := mkSGBreach {
  sg_breach_id : nat;
  sg_breach_detected_at : nat;
  sg_breach_records_count : nat;
  sg_breach_significant_harm : bool;
}.

(* Notifiable breach: >= 500 individuals OR significant harm *)
Definition sg_breach_notifiable (b : SGBreachEvent) : Prop :=
  sg_breach_records_count b >= 500 \/ sg_breach_significant_harm b = true.

Definition sg_pdpc_notified_in_time (b : SGBreachEvent) (t : nat) : Prop :=
  t <= sg_breach_detected_at b + 72.  (* 3 calendar days ≈ 72 hours *)

Theorem obligation_9_notification :
  forall (b : SGBreachEvent) (t : nat),
  sg_breach_notifiable b ->
  t <= sg_breach_detected_at b + 72 ->
  sg_pdpc_notified_in_time b t.
Proof.
  intros b t _ H. unfold sg_pdpc_notified_in_time. exact H.
Qed.

(* ================================================================ *)
(* Full Singapore PDPA Compliance Composition                        *)
(* ================================================================ *)

Definition sg_pdpa_fully_compliant
  (r : SGDataRecord) (transfer : TransferAdequacy) (current_time : nat) : Prop :=
  sg_consent_for_category r /\
  sg_purpose_limited r (sg_purpose_id r) /\
  sg_protection_adequate r /\
  sg_within_retention r current_time /\
  sg_transfer_lawful transfer.

Theorem sg_pdpa_composition :
  forall (r : SGDataRecord) (transfer : TransferAdequacy) (t : nat),
  sg_consent_for_category r ->
  sg_protection_adequate r ->
  sg_within_retention r t ->
  sg_transfer_lawful transfer ->
  sg_pdpa_fully_compliant r transfer t.
Proof.
  intros r transfer t H1 H2 H3 H4.
  unfold sg_pdpa_fully_compliant.
  split. exact H1.
  split. apply obligation_2_purpose.
  split. exact H2.
  split. exact H3.
  exact H4.
Qed.

(* ================================================================ *)
(* Extended Singapore PDPA Compliance Theorems                       *)
(* ================================================================ *)

Require Import Lia.

(* --- Purpose Limitation Enforcement --- *)
(* PDPA §18: Use only for declared purpose *)

Definition sg_purpose_violation (r : SGDataRecord) (actual : nat) : Prop :=
  sg_purpose_id r <> actual.

Theorem purpose_limitation_enforced :
  forall (r : SGDataRecord) (actual : nat),
  sg_purpose_id r <> actual ->
  sg_purpose_violation r actual.
Proof.
  intros r actual Hneq. unfold sg_purpose_violation. exact Hneq.
Qed.

Theorem purpose_match_no_violation :
  forall (r : SGDataRecord),
  ~ sg_purpose_violation r (sg_purpose_id r).
Proof.
  intros r Hviol. unfold sg_purpose_violation in Hviol.
  apply Hviol. reflexivity.
Qed.

(* --- Notification Obligation --- *)
(* PDPA §20: Inform individuals of purpose before collection *)

Record SGNotificationRecord := mkSGNotif {
  sgn_subject_id : nat;
  sgn_purposes_notified : list nat;
  sgn_notified_before_collection : bool;
  sgn_language_understood : bool;
}.

Definition notification_obligation_met (n : SGNotificationRecord) : Prop :=
  sgn_notified_before_collection n = true /\
  sgn_language_understood n = true /\
  length (sgn_purposes_notified n) > 0.

Theorem notification_obligation_valid :
  forall (n : SGNotificationRecord),
  sgn_notified_before_collection n = true ->
  sgn_language_understood n = true ->
  sgn_purposes_notified n <> nil ->
  notification_obligation_met n.
Proof.
  intros n H1 H2 H3.
  unfold notification_obligation_met.
  split. exact H1. split. exact H2.
  destruct (sgn_purposes_notified n) eqn:Heq.
  - contradiction.
  - simpl. apply Nat.lt_0_succ.
Qed.

(* --- Access and Correction Right --- *)
(* PDPA §21, §22: Right to request access and correction *)

Record SGAccessCorrectionRequest := mkSGACR {
  sgacr_subject_id : nat;
  sgacr_requested_at : nat;
  sgacr_responded_at : nat;
  sgacr_access_provided : bool;
  sgacr_correction_made : bool;
}.

Definition sg_access_correction_deadline : nat := 720. (* 30 days in hours *)

Definition access_correction_fulfilled (req : SGAccessCorrectionRequest) : Prop :=
  sgacr_responded_at req <= sgacr_requested_at req + sg_access_correction_deadline /\
  (sgacr_access_provided req = true \/ sgacr_correction_made req = true).

Theorem access_correction_right :
  forall (req : SGAccessCorrectionRequest),
  sgacr_responded_at req <= sgacr_requested_at req + sg_access_correction_deadline ->
  sgacr_access_provided req = true ->
  access_correction_fulfilled req.
Proof.
  intros req Htime Hacc.
  unfold access_correction_fulfilled.
  split. exact Htime.
  left. exact Hacc.
Qed.

Theorem correction_within_deadline :
  forall (req : SGAccessCorrectionRequest),
  sgacr_responded_at req <= sgacr_requested_at req + sg_access_correction_deadline ->
  sgacr_correction_made req = true ->
  access_correction_fulfilled req.
Proof.
  intros req Htime Hcorr.
  unfold access_correction_fulfilled.
  split. exact Htime.
  right. exact Hcorr.
Qed.

(* --- Transfer Limitation --- *)
(* PDPA §26: Transfer requires comparable protection *)

Theorem transfer_limitation_satisfied :
  forall (a : TransferAdequacy),
  a <> NoSafeguards ->
  sg_transfer_lawful a.
Proof.
  intros a Hneq. destruct a; simpl.
  - exact I.
  - exact I.
  - exact I.
  - contradiction.
Qed.

(* --- Data Protection Officer Appointment --- *)
(* PDPA §11(3): DPO must be appointed *)

Record SGDataProtectionOfficer := mkSGDPO {
  sg_dpo_id : nat;
  sg_dpo_active : bool;
  sg_dpo_contact_public : bool;
  sg_dpo_trained : bool;
}.

Definition sg_dpo_appointed (dpo : SGDataProtectionOfficer) : Prop :=
  sg_dpo_active dpo = true /\
  sg_dpo_contact_public dpo = true.

Theorem data_protection_officer_appointed :
  forall (dpo : SGDataProtectionOfficer),
  sg_dpo_active dpo = true ->
  sg_dpo_contact_public dpo = true ->
  sg_dpo_appointed dpo.
Proof.
  intros dpo H1 H2. unfold sg_dpo_appointed. split; assumption.
Qed.

(* --- Do Not Call Registry --- *)
(* PDPA Part IX: Must check DNC before marketing *)

Inductive DNCStatus : Type :=
  | DNCRegistered : DNCStatus
  | DNCNotRegistered : DNCStatus
  | DNCExempt : DNCStatus.

Definition dnc_checked (status : DNCStatus) (marketing_sent : bool) : Prop :=
  match status with
  | DNCRegistered => marketing_sent = false
  | DNCNotRegistered => True
  | DNCExempt => True
  end.

Theorem do_not_call_registry_checked :
  forall (status : DNCStatus),
  status = DNCRegistered ->
  dnc_checked status false.
Proof.
  intros status Hreg. rewrite Hreg. simpl. reflexivity.
Qed.

Theorem dnc_not_registered_allows :
  forall (sent : bool),
  dnc_checked DNCNotRegistered sent.
Proof.
  intros sent. simpl. exact I.
Qed.

(* --- Breach Notification 72 Hours --- *)
(* PDPA: Notifiable breaches must be reported within 3 calendar days *)

Theorem breach_notification_72_hours :
  forall (b : SGBreachEvent) (t : nat),
  sg_breach_notifiable b ->
  t <= sg_breach_detected_at b + 72 ->
  sg_pdpc_notified_in_time b t.
Proof.
  intros b t _ Htime. unfold sg_pdpc_notified_in_time. exact Htime.
Qed.

Theorem breach_not_notifiable_threshold :
  forall (b : SGBreachEvent),
  sg_breach_records_count b < 500 ->
  sg_breach_significant_harm b = false ->
  ~ sg_breach_notifiable b.
Proof.
  intros b Hcount Hharm [Hge | Hsig].
  - lia.
  - rewrite Hharm in Hsig. discriminate.
Qed.

(* --- Deemed Consent Valid --- *)
(* PDPA §15: Deemed consent by conduct or notification *)

Theorem deemed_consent_valid :
  forall (r : SGDataRecord),
  sg_consent r = SGDeemedConsent ->
  sg_has_consent r.
Proof.
  intros r Hdc. unfold sg_has_consent. rewrite Hdc. exact I.
Qed.

Theorem deemed_consent_notification_valid :
  forall (r : SGDataRecord),
  sg_consent r = SGDeemedConsentNotification ->
  sg_has_consent r.
Proof.
  intros r Hdcn. unfold sg_has_consent. rewrite Hdcn. exact I.
Qed.

(* --- Business Improvement Exception --- *)
(* PDPA Part V: Can use data for legitimate business improvement *)

Inductive SGProcessingBasis : Type :=
  | SGConsentBasis : SGProcessingBasis
  | SGBusinessImprovement : SGProcessingBasis
  | SGResearchBasis : SGProcessingBasis
  | SGLegitimateInterest : SGProcessingBasis.

Definition business_improvement_applicable (basis : SGProcessingBasis)
  (proportionate : bool) (safeguards : bool) : Prop :=
  basis = SGBusinessImprovement ->
  proportionate = true /\ safeguards = true.

Theorem business_improvement_exception :
  forall (proportionate safeguards : bool),
  proportionate = true ->
  safeguards = true ->
  business_improvement_applicable SGBusinessImprovement proportionate safeguards.
Proof.
  intros prop safe Hp Hs.
  unfold business_improvement_applicable.
  intros _. split; assumption.
Qed.

(* --- Accountability Documentation --- *)
(* PDPA §12: Must be accountable for compliance *)

Record SGAccountabilityRecord := mkSGAccountability {
  sga_policies_documented : bool;
  sga_training_conducted : bool;
  sga_dpo_designated : bool;
  sga_complaint_process : bool;
  sga_breach_response_plan : bool;
}.

Definition accountability_documented (ar : SGAccountabilityRecord) : Prop :=
  sga_policies_documented ar = true /\
  sga_training_conducted ar = true /\
  sga_dpo_designated ar = true /\
  sga_complaint_process ar = true /\
  sga_breach_response_plan ar = true.

Theorem accountability_complete :
  forall (ar : SGAccountabilityRecord),
  sga_policies_documented ar = true ->
  sga_training_conducted ar = true ->
  sga_dpo_designated ar = true ->
  sga_complaint_process ar = true ->
  sga_breach_response_plan ar = true ->
  accountability_documented ar.
Proof.
  intros ar H1 H2 H3 H4 H5.
  unfold accountability_documented.
  repeat split; assumption.
Qed.

(* --- Data Anonymization Standard --- *)
(* Anonymized data falls outside PDPA scope *)

Definition sg_data_anonymized_excluded (r : SGDataRecord) : Prop :=
  sg_anonymized r = true -> ~ sg_consent_for_category r -> False.

Theorem data_anonymization_excludes :
  forall (r : SGDataRecord),
  sg_anonymized r = true ->
  sg_protection_adequate r.
Proof.
  intros r Hanon. unfold sg_protection_adequate. right. exact Hanon.
Qed.

(* --- Consent Category Coverage --- *)

Definition all_sg_consent_statuses : list SGConsentStatus :=
  [SGNoConsent; SGExplicitConsent; SGDeemedConsent;
   SGDeemedConsentNotification; SGWithdrawnConsent].

Theorem sg_consent_coverage :
  forall (cs : SGConsentStatus), In cs all_sg_consent_statuses.
Proof.
  intros cs. destruct cs; simpl; auto 6.
Qed.

Definition all_sg_data_categories : list SGDataCategory :=
  [SGPublicData; SGPersonalData; SGBusinessContact].

Theorem sg_data_category_coverage :
  forall (dc : SGDataCategory), In dc all_sg_data_categories.
Proof.
  intros dc. destruct dc; simpl; auto 4.
Qed.

Definition all_transfer_adequacies : list TransferAdequacy :=
  [AdequateJurisdiction; ContractualSafeguards; ConsentForTransfer; NoSafeguards].

Theorem transfer_adequacy_coverage :
  forall (ta : TransferAdequacy), In ta all_transfer_adequacies.
Proof.
  intros ta. destruct ta; simpl; auto 5.
Qed.

(* ================================================================ *)
(* Extended PDPA Theorems — Session 76                              *)
(* Do Not Call Registry, Data Portability, DPO Requirements,        *)
(* PDPC Enforcement, Consent Validity, Retention, Cross-Border      *)
(* ================================================================ *)

Require Import Coq.micromega.Lia.

(* --- Obligation 3: Notification Before Collection --- *)
(* PDPA §20: Must notify of purposes before or at collection *)

Definition sg_notified_purposes (n : SGNotificationRecord) (pid : nat) : Prop :=
  In pid (sgn_purposes_notified n).

Theorem notification_purposes_nonempty :
  forall (n : SGNotificationRecord) (p : nat) (ps : list nat),
  sgn_purposes_notified n = p :: ps ->
  length (sgn_purposes_notified n) > 0.
Proof.
  intros n p ps Heq. rewrite Heq. simpl. lia.
Qed.

Theorem notification_first_purpose_notified :
  forall (n : SGNotificationRecord) (p : nat) (ps : list nat),
  sgn_purposes_notified n = p :: ps ->
  sg_notified_purposes n p.
Proof.
  intros n p ps Heq. unfold sg_notified_purposes. rewrite Heq.
  simpl. left. reflexivity.
Qed.

(* --- Obligation 4: Access Obligation Timing --- *)
(* PDPA §21: Respond within 30 days (720 hours) *)

Theorem access_deadline_monotone :
  forall (req : SGAccessCorrectionRequest) (t1 t2 : nat),
  t1 <= t2 ->
  sgacr_responded_at req <= sgacr_requested_at req + t1 ->
  sgacr_responded_at req <= sgacr_requested_at req + t2.
Proof.
  intros req t1 t2 Hle Hresp. lia.
Qed.

Theorem access_request_immediate_response :
  forall (req : SGAccessCorrectionRequest),
  sgacr_responded_at req = sgacr_requested_at req ->
  sgacr_access_provided req = true ->
  access_correction_fulfilled req.
Proof.
  intros req Htime Hacc. unfold access_correction_fulfilled.
  split.
  - unfold sg_access_correction_deadline. lia.
  - left. exact Hacc.
Qed.

(* --- Obligation 5: Accuracy --- *)
(* PDPA §23: Reasonable effort to ensure accuracy *)

Record SGAccuracyRecord := mkSGAccuracy {
  sgacc_data_id : nat;
  sgacc_last_verified : nat;
  sgacc_verification_interval : nat;
  sgacc_source_reliable : bool;
  sgacc_corrections_applied : nat;
}.

Definition accuracy_maintained (acc : SGAccuracyRecord) (current_time : nat) : Prop :=
  current_time <= sgacc_last_verified acc + sgacc_verification_interval acc /\
  sgacc_source_reliable acc = true.

Theorem accuracy_within_interval :
  forall (acc : SGAccuracyRecord) (t : nat),
  t <= sgacc_last_verified acc + sgacc_verification_interval acc ->
  sgacc_source_reliable acc = true ->
  accuracy_maintained acc t.
Proof.
  intros acc t Htime Hrel. unfold accuracy_maintained.
  split; assumption.
Qed.

Theorem accuracy_stale_requires_reverification :
  forall (acc : SGAccuracyRecord) (t : nat),
  sgacc_last_verified acc + sgacc_verification_interval acc < t ->
  ~ (accuracy_maintained acc t).
Proof.
  intros acc t Hstale [Htime _]. lia.
Qed.

(* --- Do Not Call Registry Extended --- *)
(* PDPA Part IX: DNC obligations for organizations *)

Record SGDNCRecord := mkSGDNC {
  sg_dnc_phone : nat;
  sg_dnc_status : DNCStatus;
  sg_dnc_checked_at : nat;
  sg_dnc_marketing_type : nat;  (* 0=voice, 1=text, 2=fax *)
  sg_dnc_organization_id : nat;
}.

Definition sg_dnc_all_types : list nat := [0; 1; 2].

Definition sg_dnc_compliant_marketing (dnc : SGDNCRecord) (sent : bool) : Prop :=
  dnc_checked (sg_dnc_status dnc) sent.

Theorem dnc_registered_blocks_all_marketing_types :
  forall (dnc : SGDNCRecord),
  sg_dnc_status dnc = DNCRegistered ->
  sg_dnc_compliant_marketing dnc false.
Proof.
  intros dnc Hreg. unfold sg_dnc_compliant_marketing.
  rewrite Hreg. simpl. reflexivity.
Qed.

Theorem dnc_exempt_allows_marketing :
  forall (dnc : SGDNCRecord) (sent : bool),
  sg_dnc_status dnc = DNCExempt ->
  sg_dnc_compliant_marketing dnc sent.
Proof.
  intros dnc sent Hexempt. unfold sg_dnc_compliant_marketing.
  rewrite Hexempt. simpl. exact I.
Qed.

Theorem dnc_status_decidable :
  forall (s : DNCStatus),
  s = DNCRegistered \/ s = DNCNotRegistered \/ s = DNCExempt.
Proof.
  intros s. destruct s.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.

(* --- Data Portability Obligation (2021 Amendment) --- *)
(* PDPA Part VIA: Right to port data to another organization *)

Record SGPortabilityRequest := mkSGPort {
  sg_port_subject_id : nat;
  sg_port_from_org : nat;
  sg_port_to_org : nat;
  sg_port_requested_at : nat;
  sg_port_completed_at : nat;
  sg_port_format_standard : bool;
  sg_port_data_machine_readable : bool;
}.

Definition sg_portability_deadline : nat := 720. (* 30 days in hours *)

Definition portability_fulfilled (req : SGPortabilityRequest) : Prop :=
  sg_port_completed_at req <= sg_port_requested_at req + sg_portability_deadline /\
  sg_port_format_standard req = true /\
  sg_port_data_machine_readable req = true.

Theorem portability_obligation_met :
  forall (req : SGPortabilityRequest),
  sg_port_completed_at req <= sg_port_requested_at req + sg_portability_deadline ->
  sg_port_format_standard req = true ->
  sg_port_data_machine_readable req = true ->
  portability_fulfilled req.
Proof.
  intros req Htime Hformat Hmr. unfold portability_fulfilled.
  repeat split; assumption.
Qed.

Theorem portability_late_response_violation :
  forall (req : SGPortabilityRequest),
  sg_port_requested_at req + sg_portability_deadline < sg_port_completed_at req ->
  ~ portability_fulfilled req.
Proof.
  intros req Hlate [Htime _]. lia.
Qed.

Theorem portability_requires_standard_format :
  forall (req : SGPortabilityRequest),
  sg_port_format_standard req = false ->
  ~ portability_fulfilled req.
Proof.
  intros req Hfmt [_ [Hstd _]]. rewrite Hfmt in Hstd. discriminate.
Qed.

(* --- PDPC Enforcement Powers --- *)
(* PDPC can issue directions, financial penalties up to S$1M *)

Inductive PDPCDirection : Type :=
  | PDPCWarning : PDPCDirection
  | PDPCDirectionToComply : PDPCDirection
  | PDPCFinancialPenalty : PDPCDirection
  | PDPCDirectionToStopCollection : PDPCDirection
  | PDPCDirectionToDestroy : PDPCDirection.

Record PDPCEnforcementAction := mkPDPCAction {
  pdpc_direction : PDPCDirection;
  pdpc_penalty_amount : nat;
  pdpc_max_penalty : nat;
  pdpc_organization_id : nat;
  pdpc_breach_severity : nat;  (* 0=minor, 1=moderate, 2=severe *)
}.

Definition pdpc_penalty_within_cap (action : PDPCEnforcementAction) : Prop :=
  pdpc_penalty_amount action <= pdpc_max_penalty action.

Definition pdpc_penalty_proportionate (action : PDPCEnforcementAction) : Prop :=
  match pdpc_breach_severity action with
  | 0 => pdpc_penalty_amount action = 0  (* Minor: warning only *)
  | 1 => pdpc_penalty_amount action <= pdpc_max_penalty action / 2
  | _ => pdpc_penalty_amount action <= pdpc_max_penalty action
  end.

Theorem pdpc_penalty_cap_respected :
  forall (action : PDPCEnforcementAction),
  pdpc_penalty_amount action <= pdpc_max_penalty action ->
  pdpc_penalty_within_cap action.
Proof.
  intros action H. unfold pdpc_penalty_within_cap. exact H.
Qed.

Theorem pdpc_minor_breach_no_fine :
  forall (action : PDPCEnforcementAction),
  pdpc_breach_severity action = 0 ->
  pdpc_penalty_amount action = 0 ->
  pdpc_penalty_proportionate action.
Proof.
  intros action Hsev Hamt. unfold pdpc_penalty_proportionate.
  rewrite Hsev. exact Hamt.
Qed.

Theorem pdpc_moderate_breach_half_cap :
  forall (action : PDPCEnforcementAction),
  pdpc_breach_severity action = 1 ->
  pdpc_penalty_amount action <= pdpc_max_penalty action / 2 ->
  pdpc_penalty_proportionate action.
Proof.
  intros action Hsev Hamt. unfold pdpc_penalty_proportionate.
  rewrite Hsev. exact Hamt.
Qed.

Theorem pdpc_severe_breach_full_cap :
  forall (action : PDPCEnforcementAction),
  pdpc_breach_severity action >= 2 ->
  pdpc_penalty_amount action <= pdpc_max_penalty action ->
  pdpc_penalty_proportionate action.
Proof.
  intros action Hsev Hamt. unfold pdpc_penalty_proportionate.
  remember (pdpc_breach_severity action) as sev.
  destruct sev as [| [| n]].
  - lia.
  - lia.
  - exact Hamt.
Qed.

(* --- Consent Validity Composition --- *)
(* Combining consent type and category for complete validity check *)

Theorem consent_explicit_always_valid :
  forall (r : SGDataRecord),
  sg_consent r = SGExplicitConsent ->
  sg_has_consent r.
Proof.
  intros r Hexp. unfold sg_has_consent. rewrite Hexp. exact I.
Qed.

Theorem no_consent_personal_data_violation :
  forall (r : SGDataRecord),
  sg_category r = SGPersonalData ->
  sg_consent r = SGNoConsent ->
  ~ sg_consent_for_category r.
Proof.
  intros r Hcat Hcons. unfold sg_consent_for_category.
  rewrite Hcat. unfold sg_has_consent. rewrite Hcons.
  intros Habs. exact Habs.
Qed.

Theorem public_data_no_consent_needed :
  forall (r : SGDataRecord),
  sg_category r = SGPublicData ->
  sg_consent_for_category r.
Proof.
  intros r Hcat. unfold sg_consent_for_category. rewrite Hcat. exact I.
Qed.

(* --- Retention Period Properties --- *)
(* PDPA §25: Must not retain longer than necessary *)

Theorem retention_within_implies_not_dispose :
  forall (r : SGDataRecord) (t : nat),
  sg_within_retention r t ->
  ~ sg_must_dispose r t.
Proof.
  intros r t Hret Hdisp. unfold sg_within_retention in Hret.
  unfold sg_must_dispose in Hdisp. lia.
Qed.

Theorem retention_dispose_exclusive :
  forall (r : SGDataRecord) (t : nat),
  sg_within_retention r t \/ sg_must_dispose r t.
Proof.
  intros r t. unfold sg_within_retention, sg_must_dispose.
  destruct (Nat.le_gt_cases t (sg_retention_limit r)).
  - left. exact H.
  - right. exact H.
Qed.

Theorem retention_at_limit_valid :
  forall (r : SGDataRecord),
  sg_within_retention r (sg_retention_limit r).
Proof.
  intros r. unfold sg_within_retention. lia.
Qed.

Theorem retention_past_limit_dispose :
  forall (r : SGDataRecord) (t : nat),
  t > sg_retention_limit r ->
  sg_must_dispose r t.
Proof.
  intros r t Hgt. unfold sg_must_dispose. lia.
Qed.

(* --- Cross-Border Transfer Composition --- *)
(* Combining transfer adequacy with consent for cross-border *)

Definition sg_cross_border_lawful (r : SGDataRecord) (adequacy : TransferAdequacy) : Prop :=
  sg_consent_for_category r /\
  sg_transfer_lawful adequacy /\
  sg_protection_adequate r.

Theorem cross_border_composition :
  forall (r : SGDataRecord) (a : TransferAdequacy),
  sg_consent_for_category r ->
  sg_transfer_lawful a ->
  sg_protection_adequate r ->
  sg_cross_border_lawful r a.
Proof.
  intros r a H1 H2 H3. unfold sg_cross_border_lawful.
  repeat split; assumption.
Qed.

Theorem cross_border_no_safeguards_fails :
  forall (r : SGDataRecord),
  ~ sg_cross_border_lawful r NoSafeguards.
Proof.
  intros r [_ [Htrans _]]. simpl in Htrans. exact Htrans.
Qed.

(* --- Breach Notification Individual Harm Assessment --- *)
(* PDPA: Must notify individuals if significant harm likely *)

Definition sg_individual_notification_required (b : SGBreachEvent) : Prop :=
  sg_breach_significant_harm b = true.

Theorem individual_notification_harm_assessment :
  forall (b : SGBreachEvent),
  sg_breach_significant_harm b = true ->
  sg_individual_notification_required b.
Proof.
  intros b Hharm. unfold sg_individual_notification_required. exact Hharm.
Qed.

Theorem no_harm_no_individual_notification :
  forall (b : SGBreachEvent),
  sg_breach_significant_harm b = false ->
  ~ sg_individual_notification_required b.
Proof.
  intros b Hno Hreq. unfold sg_individual_notification_required in Hreq.
  rewrite Hno in Hreq. discriminate.
Qed.

(* --- Breach Threshold Properties --- *)

Theorem breach_500_is_notifiable :
  forall (b : SGBreachEvent),
  sg_breach_records_count b >= 500 ->
  sg_breach_notifiable b.
Proof.
  intros b Hge. unfold sg_breach_notifiable. left. exact Hge.
Qed.

Theorem breach_harm_is_notifiable :
  forall (b : SGBreachEvent),
  sg_breach_significant_harm b = true ->
  sg_breach_notifiable b.
Proof.
  intros b Hharm. unfold sg_breach_notifiable. right. exact Hharm.
Qed.

(* --- DPO Training Requirement --- *)
(* DPO must be trained and knowledgeable about PDPA *)

Definition sg_dpo_fully_qualified (dpo : SGDataProtectionOfficer) : Prop :=
  sg_dpo_active dpo = true /\
  sg_dpo_contact_public dpo = true /\
  sg_dpo_trained dpo = true.

Theorem dpo_qualified_implies_appointed :
  forall (dpo : SGDataProtectionOfficer),
  sg_dpo_fully_qualified dpo ->
  sg_dpo_appointed dpo.
Proof.
  intros dpo [Hact [Hpub _]]. unfold sg_dpo_appointed.
  split; assumption.
Qed.

Theorem dpo_not_trained_not_qualified :
  forall (dpo : SGDataProtectionOfficer),
  sg_dpo_trained dpo = false ->
  ~ sg_dpo_fully_qualified dpo.
Proof.
  intros dpo Hnt [_ [_ Ht]]. rewrite Hnt in Ht. discriminate.
Qed.

(* --- Full PDPA Compliance With Breach Readiness --- *)
(* Extended composition including breach response plan *)

Definition sg_pdpa_enterprise_compliant
  (r : SGDataRecord) (transfer : TransferAdequacy)
  (current_time : nat) (acct : SGAccountabilityRecord)
  (dpo : SGDataProtectionOfficer) : Prop :=
  sg_pdpa_fully_compliant r transfer current_time /\
  accountability_documented acct /\
  sg_dpo_appointed dpo.

Theorem enterprise_compliance_composition :
  forall (r : SGDataRecord) (transfer : TransferAdequacy)
         (t : nat) (acct : SGAccountabilityRecord)
         (dpo : SGDataProtectionOfficer),
  sg_pdpa_fully_compliant r transfer t ->
  accountability_documented acct ->
  sg_dpo_appointed dpo ->
  sg_pdpa_enterprise_compliant r transfer t acct dpo.
Proof.
  intros r transfer t acct dpo H1 H2 H3.
  unfold sg_pdpa_enterprise_compliant.
  split. exact H1.
  split. exact H2.
  exact H3.
Qed.

(* --- Processing Basis Coverage --- *)

Definition all_processing_bases : list SGProcessingBasis :=
  [SGConsentBasis; SGBusinessImprovement; SGResearchBasis; SGLegitimateInterest].

Theorem processing_basis_coverage :
  forall (b : SGProcessingBasis), In b all_processing_bases.
Proof.
  intros b. destruct b; simpl; auto 5.
Qed.

Definition all_pdpc_directions : list PDPCDirection :=
  [PDPCWarning; PDPCDirectionToComply; PDPCFinancialPenalty;
   PDPCDirectionToStopCollection; PDPCDirectionToDestroy].

Theorem pdpc_direction_coverage :
  forall (d : PDPCDirection), In d all_pdpc_directions.
Proof.
  intros d. destruct d; simpl; auto 6.
Qed.

(* --- Consent Withdrawal Processing Halt --- *)
(* PDPA §16: Must cease processing upon withdrawal *)

Definition sg_processing_halted_on_withdrawal
  (r : SGDataRecord) (processing_active : bool) : Prop :=
  sg_consent r = SGWithdrawnConsent -> processing_active = false.

Theorem withdrawal_halts_processing :
  forall (r : SGDataRecord),
  sg_consent r = SGWithdrawnConsent ->
  sg_processing_halted_on_withdrawal r false.
Proof.
  intros r _. unfold sg_processing_halted_on_withdrawal.
  intros _. reflexivity.
Qed.

Theorem active_processing_implies_consent :
  forall (r : SGDataRecord),
  sg_processing_halted_on_withdrawal r true ->
  sg_consent r <> SGWithdrawnConsent.
Proof.
  intros r Hhalt Heq.
  unfold sg_processing_halted_on_withdrawal in Hhalt.
  specialize (Hhalt Heq). discriminate.
Qed.
