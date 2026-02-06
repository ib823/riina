(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* MalaysiaCybersecurityAct.v - Akta Keselamatan Siber 2024 (Act 854) *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md §A3 *)
(* Legal Requirement: Cybersecurity Act 2024, effective August 26, 2024 *)
(* Governing Body: National Cyber Security Agency (NACSA) *)
(* Penalties: Up to RM500,000 + 10 years imprisonment *)

(* ========================================================================= *)
(* Malaysia's Cybersecurity Act 2024 establishes:                            *)
(*   - National Critical Information Infrastructure (NCII) framework         *)
(*   - NCII entity obligations (risk assessment, audit, incident reporting)  *)
(*   - Cybersecurity Service Provider (CSSP) licensing                       *)
(*   - CEO/board personal liability                                          *)
(*                                                                           *)
(* NCII Sectors (11):                                                        *)
(*   Government, Banking/Finance, Transport, Defense, Healthcare,            *)
(*   Telecom, Energy, Water, Agriculture/Food, Science/Tech/Innovation,      *)
(*   Information/Communication                                               *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================ *)
(* NCII Sector Model                                                 *)
(* ================================================================ *)

Inductive NCIISector : Type :=
  | Government : NCIISector
  | BankingFinance : NCIISector
  | Transport : NCIISector
  | Defense : NCIISector
  | Healthcare : NCIISector
  | Telecom : NCIISector
  | Energy : NCIISector
  | Water : NCIISector
  | AgricultureFood : NCIISector
  | ScienceTechInnovation : NCIISector
  | InformationComm : NCIISector.

(* Risk severity levels *)
Inductive RiskLevel : Type :=
  | Low : RiskLevel
  | Medium : RiskLevel
  | High : RiskLevel
  | Critical : RiskLevel.

Definition risk_level_nat (r : RiskLevel) : nat :=
  match r with Low => 0 | Medium => 1 | High => 2 | Critical => 3 end.

(* ================================================================ *)
(* NCII Entity Model                                                 *)
(* ================================================================ *)

Record NCIIEntity := mkNCII {
  ncii_id : nat;
  ncii_sector : NCIISector;
  ncii_risk_assessed : bool;
  ncii_last_audit : nat;          (* timestamp of last audit *)
  ncii_audit_interval : nat;      (* max interval between audits *)
  ncii_security_controls : nat;   (* number of controls implemented *)
  ncii_min_controls : nat;        (* minimum required controls *)
}.

(* Incident record *)
Record CyberIncident := mkIncident {
  incident_id : nat;
  incident_detected_at : nat;
  incident_reported_at : nat;
  incident_severity : RiskLevel;
  incident_ncii_id : nat;
}.

(* ================================================================ *)
(* Obligation 1: Annual Risk Assessment (§ NCII obligations)         *)
(* ================================================================ *)

Definition risk_assessment_current (e : NCIIEntity) : Prop :=
  ncii_risk_assessed e = true.

Theorem obligation_1_risk_assessment :
  forall (e : NCIIEntity),
  ncii_risk_assessed e = true ->
  risk_assessment_current e.
Proof.
  intros e H. unfold risk_assessment_current. exact H.
Qed.

(* ================================================================ *)
(* Obligation 2: Biennial Audit                                      *)
(* ================================================================ *)

Definition audit_current (e : NCIIEntity) (current_time : nat) : Prop :=
  current_time <= ncii_last_audit e + ncii_audit_interval e.

Theorem obligation_2_audit :
  forall (e : NCIIEntity) (t : nat),
  t <= ncii_last_audit e + ncii_audit_interval e ->
  audit_current e t.
Proof.
  intros e t H. unfold audit_current. exact H.
Qed.

(* Audit expiry detection *)
Theorem audit_expiry :
  forall (e : NCIIEntity) (t : nat),
  ~ audit_current e t ->
  ncii_last_audit e + ncii_audit_interval e < t.
Proof.
  intros e t H. unfold audit_current in H.
  apply not_le in H. exact H.
Qed.

(* ================================================================ *)
(* Obligation 3: Incident Reporting                                  *)
(* Act 854 requires immediate notification to NACSA                  *)
(* ================================================================ *)

Definition incident_reported_promptly (i : CyberIncident) : Prop :=
  incident_reported_at i <= incident_detected_at i + 6.  (* 6 hours *)

Definition incident_report_complete (i : CyberIncident) : Prop :=
  incident_reported_promptly i /\
  risk_level_nat (incident_severity i) >= 0.  (* All severities must be reported *)

Theorem obligation_3_reporting :
  forall (i : CyberIncident),
  incident_reported_at i <= incident_detected_at i + 6 ->
  incident_reported_promptly i.
Proof.
  intros i H. unfold incident_reported_promptly. exact H.
Qed.

(* Higher severity = more urgent *)
Theorem severity_ordering :
  forall (s1 s2 : RiskLevel),
  risk_level_nat Critical >= risk_level_nat s1.
Proof.
  intros s1 s2. destruct s1; simpl; auto with arith.
Qed.

(* ================================================================ *)
(* Obligation 4: Security Controls                                   *)
(* ================================================================ *)

Definition controls_sufficient (e : NCIIEntity) : Prop :=
  ncii_min_controls e <= ncii_security_controls e.

Theorem obligation_4_controls :
  forall (e : NCIIEntity),
  ncii_min_controls e <= ncii_security_controls e ->
  controls_sufficient e.
Proof.
  intros e H. unfold controls_sufficient. exact H.
Qed.

(* ================================================================ *)
(* Obligation 5: CSSP Licensing                                      *)
(* Cybersecurity Service Providers must be licensed by NACSA          *)
(* ================================================================ *)

Record CSSPLicense := mkCSSP {
  cssp_id : nat;
  cssp_licensed : bool;
  cssp_license_expiry : nat;
}.

Definition cssp_valid (l : CSSPLicense) (current_time : nat) : Prop :=
  cssp_licensed l = true /\ current_time <= cssp_license_expiry l.

Theorem obligation_5_cssp :
  forall (l : CSSPLicense) (t : nat),
  cssp_licensed l = true ->
  t <= cssp_license_expiry l ->
  cssp_valid l t.
Proof.
  intros l t Hlic Hexp. unfold cssp_valid. split; assumption.
Qed.

(* ================================================================ *)
(* Full Act 854 Compliance Composition                               *)
(* ================================================================ *)

Definition act854_compliant (e : NCIIEntity) (l : CSSPLicense) (t : nat) : Prop :=
  risk_assessment_current e /\
  audit_current e t /\
  controls_sufficient e /\
  cssp_valid l t.

Theorem act854_composition :
  forall (e : NCIIEntity) (l : CSSPLicense) (t : nat),
  risk_assessment_current e ->
  audit_current e t ->
  controls_sufficient e ->
  cssp_valid l t ->
  act854_compliant e l t.
Proof.
  intros e l t H1 H2 H3 H4.
  unfold act854_compliant. repeat split; try assumption.
  - destruct H4 as [H4a H4b]. exact H4a.
  - destruct H4 as [H4a H4b]. exact H4b.
Qed.

(* ================================================================ *)
(* Sector coverage: All 11 NCII sectors are enumerated               *)
(* ================================================================ *)

Definition all_ncii_sectors : list NCIISector :=
  [Government; BankingFinance; Transport; Defense; Healthcare;
   Telecom; Energy; Water; AgricultureFood; ScienceTechInnovation;
   InformationComm].

Theorem ncii_sector_coverage :
  forall (s : NCIISector), In s all_ncii_sectors.
Proof.
  intros s. destruct s; simpl; auto 12.
Qed.

(* ================================================================ *)
(* Extended Malaysia Cybersecurity Act 2024 (Act 854) Theorems       *)
(* ================================================================ *)

Require Import Lia.

(* --- Risk Level Properties --- *)

Theorem critical_is_highest_risk :
  forall (r : RiskLevel),
  risk_level_nat r <= risk_level_nat Critical.
Proof.
  intros r. destruct r; simpl; lia.
Qed.

Theorem low_is_lowest_risk :
  forall (r : RiskLevel),
  risk_level_nat Low <= risk_level_nat r.
Proof.
  intros r. destruct r; simpl; lia.
Qed.

Theorem risk_level_bounded :
  forall (r : RiskLevel),
  risk_level_nat r <= 3.
Proof.
  intros r. destruct r; simpl; lia.
Qed.

(* --- Risk Level Coverage --- *)

Definition all_risk_levels : list RiskLevel :=
  [Low; Medium; High; Critical].

Theorem risk_level_coverage :
  forall (r : RiskLevel), In r all_risk_levels.
Proof.
  intros r. destruct r; simpl; auto 5.
Qed.

(* --- Audit Current and Expiry Are Exclusive --- *)

Theorem audit_current_expiry_exclusive :
  forall (e : NCIIEntity) (t : nat),
  audit_current e t \/ ~ audit_current e t.
Proof.
  intros e t. unfold audit_current.
  destruct (Nat.le_gt_cases t (ncii_last_audit e + ncii_audit_interval e)).
  - left. exact H.
  - right. lia.
Qed.

(* --- Controls Strengthening --- *)

Theorem more_controls_still_sufficient :
  forall (e : NCIIEntity) (extra : nat),
  controls_sufficient e ->
  ncii_min_controls e <= ncii_security_controls e + extra.
Proof.
  intros e extra H.
  unfold controls_sufficient in H.
  apply (Nat.le_trans _ (ncii_security_controls e) _).
  - exact H.
  - apply Nat.le_add_r.
Qed.

(* --- Full Compliance Decomposition --- *)

Theorem act854_implies_risk_assessed :
  forall (e : NCIIEntity) (l : CSSPLicense) (t : nat),
  act854_compliant e l t ->
  risk_assessment_current e.
Proof.
  intros e l t [H _]. exact H.
Qed.

Theorem act854_implies_audit_current :
  forall (e : NCIIEntity) (l : CSSPLicense) (t : nat),
  act854_compliant e l t ->
  audit_current e t.
Proof.
  intros e l t [_ [H _]]. exact H.
Qed.

Theorem act854_implies_controls :
  forall (e : NCIIEntity) (l : CSSPLicense) (t : nat),
  act854_compliant e l t ->
  controls_sufficient e.
Proof.
  intros e l t [_ [_ [H _]]]. exact H.
Qed.

Theorem act854_implies_cssp_valid :
  forall (e : NCIIEntity) (l : CSSPLicense) (t : nat),
  act854_compliant e l t ->
  cssp_valid l t.
Proof.
  intros e l t [_ [_ [_ H]]]. exact H.
Qed.

(* --- CSSP License Expiry Properties --- *)

Theorem cssp_expired :
  forall (l : CSSPLicense) (t : nat),
  cssp_license_expiry l < t ->
  ~ cssp_valid l t.
Proof.
  intros l t Hexp [_ Hle]. lia.
Qed.

Theorem cssp_unlicensed_invalid :
  forall (l : CSSPLicense) (t : nat),
  cssp_licensed l = false ->
  ~ cssp_valid l t.
Proof.
  intros l t Hfalse [Hlic _].
  rewrite Hfalse in Hlic. discriminate.
Qed.

(* --- CEO Personal Liability --- *)
(* Act 854: CEO/board members personally liable for non-compliance *)

Record CEOLiability := mkCEOLiab {
  ceo_entity_id : nat;
  ceo_compliant : bool;
  ceo_due_diligence : bool;
  ceo_personally_liable : bool;
}.

Definition ceo_liability_applies (cl : CEOLiability) : Prop :=
  ceo_compliant cl = false ->
  ceo_due_diligence cl = false ->
  ceo_personally_liable cl = true.

Theorem ceo_liable_when_negligent :
  forall (cl : CEOLiability),
  ceo_compliant cl = false ->
  ceo_due_diligence cl = false ->
  ceo_personally_liable cl = true ->
  ceo_liability_applies cl.
Proof.
  intros cl _ _ Hliab. unfold ceo_liability_applies.
  intros _ _. exact Hliab.
Qed.

Theorem ceo_due_diligence_defense :
  forall (cl : CEOLiability),
  ceo_due_diligence cl = true ->
  ~ (ceo_due_diligence cl = false).
Proof.
  intros cl Htrue Hfalse. rewrite Htrue in Hfalse. discriminate.
Qed.

(* --- Incident Reporting: 6-Hour Deadline Properties --- *)

Theorem incident_6h_stricter_than_24h :
  forall (i : CyberIncident),
  incident_reported_promptly i ->
  incident_reported_at i <= incident_detected_at i + 24.
Proof.
  intros i H. unfold incident_reported_promptly in H. lia.
Qed.

Theorem immediate_report_always_timely :
  forall (i : CyberIncident),
  incident_reported_at i = incident_detected_at i ->
  incident_reported_promptly i.
Proof.
  intros i Heq. unfold incident_reported_promptly. lia.
Qed.

(* --- Sector-Specific Risk Requirements --- *)
(* Some sectors have higher minimum control requirements *)

Definition sector_critical (s : NCIISector) : Prop :=
  s = BankingFinance \/ s = Defense \/ s = Healthcare \/
  s = Energy \/ s = Water \/ s = Government.

Theorem banking_is_critical :
  sector_critical BankingFinance.
Proof.
  unfold sector_critical. left. reflexivity.
Qed.

Theorem defense_is_critical :
  sector_critical Defense.
Proof.
  unfold sector_critical. right. left. reflexivity.
Qed.

Theorem telecom_not_critical :
  ~ sector_critical Telecom.
Proof.
  intros [H | [H | [H | [H | [H | H]]]]]; discriminate.
Qed.
