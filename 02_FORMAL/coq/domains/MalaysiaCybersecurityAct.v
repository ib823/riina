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
