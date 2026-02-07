(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* MalaysiaSCGTRM.v - Securities Commission Malaysia *)
(* Guidelines on Technology Risk Management (GTRM) *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Legal Requirement: SC GTRM, effective August 19, 2024 *)
(* Governing Body: Securities Commission Malaysia (SC) *)
(* Applies to: Capital market intermediaries, exchanges, depositories *)

(* ========================================================================= *)
(* SC GTRM covers:                                                           *)
(*   1. Board and senior management accountability                           *)
(*   2. Technology risk management framework                                 *)
(*   3. Cybersecurity assessments and penetration testing                     *)
(*   4. AI/ML technology risk management                                     *)
(*   5. Third-party/cloud risk management                                    *)
(*   6. Incident response and reporting                                      *)
(*   7. Data protection and privacy                                          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================ *)
(* Capital Market Entity Model                                       *)
(* ================================================================ *)

Inductive CMEntityType : Type :=
  | BrokerDealer : CMEntityType
  | FundManager : CMEntityType
  | Exchange : CMEntityType
  | ClearingHouse : CMEntityType
  | Depository : CMEntityType
  | CreditRatingAgency : CMEntityType.

Record CMEntity := mkCMEntity {
  cm_id : nat;
  cm_type : CMEntityType;
  cm_board_accountability : bool;
  cm_risk_framework : bool;
  cm_pentest_done : bool;
  cm_pentest_interval : nat;       (* max days between pentests *)
  cm_last_pentest : nat;
  cm_ai_risk_assessed : bool;
  cm_third_party_assessed : bool;
  cm_cloud_risk_assessed : bool;
  cm_incident_response_plan : bool;
  cm_data_protection : bool;
}.

(* ================================================================ *)
(* Requirement 1: Board Accountability                               *)
(* ================================================================ *)

Definition gtrm_board_accountable (e : CMEntity) : Prop :=
  cm_board_accountability e = true.

Theorem gtrm_req_1 :
  forall (e : CMEntity),
  cm_board_accountability e = true ->
  gtrm_board_accountable e.
Proof.
  intros e H. unfold gtrm_board_accountable. exact H.
Qed.

(* ================================================================ *)
(* Requirement 2: Technology Risk Framework                          *)
(* ================================================================ *)

Definition gtrm_risk_framework (e : CMEntity) : Prop :=
  cm_risk_framework e = true.

Theorem gtrm_req_2 :
  forall (e : CMEntity),
  cm_risk_framework e = true ->
  gtrm_risk_framework e.
Proof.
  intros e H. unfold gtrm_risk_framework. exact H.
Qed.

(* ================================================================ *)
(* Requirement 3: Cybersecurity Assessment / Penetration Testing     *)
(* ================================================================ *)

Definition gtrm_pentest_current (e : CMEntity) (current_time : nat) : Prop :=
  cm_pentest_done e = true /\
  current_time <= cm_last_pentest e + cm_pentest_interval e.

Theorem gtrm_req_3 :
  forall (e : CMEntity) (t : nat),
  cm_pentest_done e = true ->
  t <= cm_last_pentest e + cm_pentest_interval e ->
  gtrm_pentest_current e t.
Proof.
  intros e t H1 H2. unfold gtrm_pentest_current. split; assumption.
Qed.

(* ================================================================ *)
(* Requirement 4: AI/ML Risk Assessment                              *)
(* ================================================================ *)

Definition gtrm_ai_assessed (e : CMEntity) : Prop :=
  cm_ai_risk_assessed e = true.

Theorem gtrm_req_4 :
  forall (e : CMEntity),
  cm_ai_risk_assessed e = true ->
  gtrm_ai_assessed e.
Proof.
  intros e H. unfold gtrm_ai_assessed. exact H.
Qed.

(* ================================================================ *)
(* Requirement 5: Third-Party and Cloud Risk                         *)
(* ================================================================ *)

Definition gtrm_vendor_compliant (e : CMEntity) : Prop :=
  cm_third_party_assessed e = true /\ cm_cloud_risk_assessed e = true.

Theorem gtrm_req_5 :
  forall (e : CMEntity),
  cm_third_party_assessed e = true ->
  cm_cloud_risk_assessed e = true ->
  gtrm_vendor_compliant e.
Proof.
  intros e H1 H2. unfold gtrm_vendor_compliant. split; assumption.
Qed.

(* ================================================================ *)
(* Requirement 6: Incident Response                                  *)
(* ================================================================ *)

Definition gtrm_incident_ready (e : CMEntity) : Prop :=
  cm_incident_response_plan e = true.

Theorem gtrm_req_6 :
  forall (e : CMEntity),
  cm_incident_response_plan e = true ->
  gtrm_incident_ready e.
Proof.
  intros e H. unfold gtrm_incident_ready. exact H.
Qed.

(* ================================================================ *)
(* Requirement 7: Data Protection                                    *)
(* ================================================================ *)

Definition gtrm_data_protected (e : CMEntity) : Prop :=
  cm_data_protection e = true.

Theorem gtrm_req_7 :
  forall (e : CMEntity),
  cm_data_protection e = true ->
  gtrm_data_protected e.
Proof.
  intros e H. unfold gtrm_data_protected. exact H.
Qed.

(* ================================================================ *)
(* Full SC GTRM Compliance                                           *)
(* ================================================================ *)

Definition gtrm_fully_compliant (e : CMEntity) (t : nat) : Prop :=
  gtrm_board_accountable e /\
  gtrm_risk_framework e /\
  gtrm_pentest_current e t /\
  gtrm_ai_assessed e /\
  gtrm_vendor_compliant e /\
  gtrm_incident_ready e /\
  gtrm_data_protected e.

Theorem gtrm_composition :
  forall (e : CMEntity) (t : nat),
  gtrm_board_accountable e ->
  gtrm_risk_framework e ->
  gtrm_pentest_current e t ->
  gtrm_ai_assessed e ->
  gtrm_vendor_compliant e ->
  gtrm_incident_ready e ->
  gtrm_data_protected e ->
  gtrm_fully_compliant e t.
Proof.
  intros e t H1 H2 H3 H4 H5 H6 H7.
  unfold gtrm_fully_compliant.
  split. exact H1. split. exact H2. split. exact H3.
  split. exact H4. split. exact H5. split. exact H6. exact H7.
Qed.

(* Entity type coverage *)
Definition all_cm_entity_types : list CMEntityType :=
  [BrokerDealer; FundManager; Exchange; ClearingHouse;
   Depository; CreditRatingAgency].

Theorem cm_entity_coverage :
  forall (t : CMEntityType), In t all_cm_entity_types.
Proof.
  intros t. destruct t; simpl; auto 7.
Qed.

(* ================================================================ *)
(* Extended SC GTRM Compliance Theorems                              *)
(* ================================================================ *)

Require Import Lia.

(* --- Pentest Interval Properties --- *)

Theorem pentest_expired :
  forall (e : CMEntity) (t : nat),
  cm_last_pentest e + cm_pentest_interval e < t ->
  ~ gtrm_pentest_current e t.
Proof.
  intros e t Hexp [_ Hle]. lia.
Qed.

Theorem pentest_recently_done :
  forall (e : CMEntity),
  cm_pentest_done e = true ->
  gtrm_pentest_current e (cm_last_pentest e).
Proof.
  intros e Hdone.
  unfold gtrm_pentest_current.
  split. exact Hdone. lia.
Qed.

(* --- Full Compliance Decomposition --- *)

Theorem gtrm_full_implies_board :
  forall (e : CMEntity) (t : nat),
  gtrm_fully_compliant e t ->
  gtrm_board_accountable e.
Proof.
  intros e t [H _]. exact H.
Qed.

Theorem gtrm_full_implies_risk :
  forall (e : CMEntity) (t : nat),
  gtrm_fully_compliant e t ->
  gtrm_risk_framework e.
Proof.
  intros e t [_ [H _]]. exact H.
Qed.

Theorem gtrm_full_implies_pentest :
  forall (e : CMEntity) (t : nat),
  gtrm_fully_compliant e t ->
  gtrm_pentest_current e t.
Proof.
  intros e t [_ [_ [H _]]]. exact H.
Qed.

Theorem gtrm_full_implies_ai :
  forall (e : CMEntity) (t : nat),
  gtrm_fully_compliant e t ->
  gtrm_ai_assessed e.
Proof.
  intros e t [_ [_ [_ [H _]]]]. exact H.
Qed.

Theorem gtrm_full_implies_vendor :
  forall (e : CMEntity) (t : nat),
  gtrm_fully_compliant e t ->
  gtrm_vendor_compliant e.
Proof.
  intros e t [_ [_ [_ [_ [H _]]]]]. exact H.
Qed.

Theorem gtrm_full_implies_incident :
  forall (e : CMEntity) (t : nat),
  gtrm_fully_compliant e t ->
  gtrm_incident_ready e.
Proof.
  intros e t [_ [_ [_ [_ [_ [H _]]]]]]. exact H.
Qed.

Theorem gtrm_full_implies_data :
  forall (e : CMEntity) (t : nat),
  gtrm_fully_compliant e t ->
  gtrm_data_protected e.
Proof.
  intros e t [_ [_ [_ [_ [_ [_ H]]]]]]. exact H.
Qed.

(* --- SC Incident Reporting --- *)
(* GTRM requires incident reporting to SC Malaysia *)

Record SCIncident := mkSCIncident {
  sci_id : nat;
  sci_entity_id : nat;
  sci_detected_at : nat;
  sci_reported_at : nat;
  sci_impact_level : nat;  (* 0=low, 1=medium, 2=high, 3=critical *)
}.

Definition sc_incident_deadline : nat := 24. (* 24 hours for initial report *)

Definition sc_incident_timely (inc : SCIncident) : Prop :=
  sci_reported_at inc <= sci_detected_at inc + sc_incident_deadline.

Theorem sc_incident_reporting :
  forall (inc : SCIncident),
  sci_reported_at inc <= sci_detected_at inc + 24 ->
  sc_incident_timely inc.
Proof.
  intros inc H. unfold sc_incident_timely, sc_incident_deadline. exact H.
Qed.

Theorem sc_incident_late :
  forall (inc : SCIncident),
  sci_detected_at inc + sc_incident_deadline < sci_reported_at inc ->
  ~ sc_incident_timely inc.
Proof.
  intros inc Hlate Htimely.
  unfold sc_incident_timely, sc_incident_deadline in Htimely. lia.
Qed.

(* --- AI/ML Model Risk Governance --- *)
(* GTRM: AI/ML-specific risk management requirements *)

Record AIModelRisk := mkAIRisk {
  ai_model_id : nat;
  ai_bias_assessed : bool;
  ai_explainability_documented : bool;
  ai_data_quality_verified : bool;
  ai_model_validated : bool;
  ai_monitoring_active : bool;
}.

Definition ai_risk_managed (ar : AIModelRisk) : Prop :=
  ai_bias_assessed ar = true /\
  ai_explainability_documented ar = true /\
  ai_data_quality_verified ar = true /\
  ai_model_validated ar = true /\
  ai_monitoring_active ar = true.

Theorem ai_model_risk_complete :
  forall (ar : AIModelRisk),
  ai_bias_assessed ar = true ->
  ai_explainability_documented ar = true ->
  ai_data_quality_verified ar = true ->
  ai_model_validated ar = true ->
  ai_monitoring_active ar = true ->
  ai_risk_managed ar.
Proof.
  intros ar H1 H2 H3 H4 H5.
  unfold ai_risk_managed.
  split. exact H1. split. exact H2. split. exact H3.
  split. exact H4. exact H5.
Qed.

Theorem ai_not_validated_not_managed :
  forall (ar : AIModelRisk),
  ai_model_validated ar = false ->
  ~ ai_risk_managed ar.
Proof.
  intros ar Hf [_ [_ [_ [Hv _]]]].
  rewrite Hf in Hv. discriminate.
Qed.

(* --- Cloud Risk Assessment for Capital Markets --- *)

Record CMCloudRisk := mkCMCloud {
  cmc_provider_id : nat;
  cmc_data_residency_compliant : bool;
  cmc_encryption_at_rest : bool;
  cmc_encryption_in_transit : bool;
  cmc_access_controls : bool;
  cmc_exit_strategy : bool;
}.

Definition cm_cloud_risk_assessed (cr : CMCloudRisk) : Prop :=
  cmc_data_residency_compliant cr = true /\
  cmc_encryption_at_rest cr = true /\
  cmc_encryption_in_transit cr = true /\
  cmc_access_controls cr = true /\
  cmc_exit_strategy cr = true.

Theorem cm_cloud_fully_assessed :
  forall (cr : CMCloudRisk),
  cmc_data_residency_compliant cr = true ->
  cmc_encryption_at_rest cr = true ->
  cmc_encryption_in_transit cr = true ->
  cmc_access_controls cr = true ->
  cmc_exit_strategy cr = true ->
  cm_cloud_risk_assessed cr.
Proof.
  intros cr H1 H2 H3 H4 H5.
  unfold cm_cloud_risk_assessed.
  split. exact H1. split. exact H2. split. exact H3.
  split. exact H4. exact H5.
Qed.

Theorem cm_cloud_missing_exit_strategy :
  forall (cr : CMCloudRisk),
  cmc_exit_strategy cr = false ->
  ~ cm_cloud_risk_assessed cr.
Proof.
  intros cr Hf [_ [_ [_ [_ He]]]].
  rewrite Hf in He. discriminate.
Qed.
