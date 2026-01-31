(* SingaporeMAS_TRM.v - MAS Technology Risk Management Guidelines *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md §B3 *)
(* Legal Requirement: MAS TRM Guidelines (revised Jan 2021), *)
(*   MAS Notice on Cyber Hygiene (FSM-N06, effective May/Aug 2024) *)
(* Governing Body: Monetary Authority of Singapore (MAS) *)

(* ========================================================================= *)
(* MAS TRM covers:                                                           *)
(*   1. Board and senior management oversight                                *)
(*   2. Technology risk governance                                           *)
(*   3. IT project management                                                *)
(*   4. Software application development and management                      *)
(*   5. IT service management                                                *)
(*   6. Cyber surveillance and security operations                           *)
(*   7. Data loss prevention                                                 *)
(*   8. Online financial services                                            *)
(*   9. Payment card security                                                *)
(*  10. IT resilience                                                        *)
(*                                                                           *)
(* MAS Cyber Hygiene Notice (legally binding):                               *)
(*   - Multi-factor authentication (MFA)                                     *)
(*   - Security patching (≤14 days for critical)                            *)
(*   - Network perimeter defense                                             *)
(*   - Anti-malware protection                                               *)
(*   - Privileged access management                                          *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* ================================================================ *)
(* Financial Institution Model (Singapore-regulated)                 *)
(* ================================================================ *)

Inductive MASLicenseType : Type :=
  | FullBank : MASLicenseType
  | WholesaleBank : MASLicenseType
  | MerchantBank : MASLicenseType
  | InsuranceCo : MASLicenseType
  | CapitalMarketsServices : MASLicenseType
  | PaymentInstitution : MASLicenseType
  | MajorPaymentInstitution : MASLicenseType.

Inductive PatchCriticality : Type :=
  | PatchCritical : PatchCriticality    (* ≤14 days *)
  | PatchHigh : PatchCriticality        (* ≤30 days *)
  | PatchMedium : PatchCriticality      (* ≤60 days *)
  | PatchLow : PatchCriticality.        (* ≤90 days *)

Definition patch_deadline (p : PatchCriticality) : nat :=
  match p with
  | PatchCritical => 14
  | PatchHigh => 30
  | PatchMedium => 60
  | PatchLow => 90
  end.

Record MASRegulatedEntity := mkMASEntity {
  mas_id : nat;
  mas_license : MASLicenseType;
  mas_mfa_enabled : bool;           (* Cyber Hygiene: MFA *)
  mas_patching_current : bool;      (* Cyber Hygiene: Patching *)
  mas_network_secured : bool;       (* Cyber Hygiene: Network security *)
  mas_antimalware : bool;           (* Cyber Hygiene: Anti-malware *)
  mas_privileged_access_managed : bool; (* Cyber Hygiene: PAM *)
  mas_board_oversight : bool;       (* TRM: Board oversight *)
  mas_risk_assessment_done : bool;  (* TRM: Risk assessment *)
  mas_pen_test_done : bool;         (* TRM: Penetration testing *)
  mas_incident_response_plan : bool;(* TRM: IR plan *)
  mas_bcp_tested : bool;            (* TRM: BCP/DR *)
}.

(* ================================================================ *)
(* MAS Cyber Hygiene Notice (FSM-N06) — Legally Binding              *)
(* ================================================================ *)

Definition cyber_hygiene_mfa (e : MASRegulatedEntity) : Prop :=
  mas_mfa_enabled e = true.

Definition cyber_hygiene_patching (e : MASRegulatedEntity) : Prop :=
  mas_patching_current e = true.

Definition cyber_hygiene_network (e : MASRegulatedEntity) : Prop :=
  mas_network_secured e = true.

Definition cyber_hygiene_antimalware (e : MASRegulatedEntity) : Prop :=
  mas_antimalware e = true.

Definition cyber_hygiene_pam (e : MASRegulatedEntity) : Prop :=
  mas_privileged_access_managed e = true.

Definition cyber_hygiene_compliant (e : MASRegulatedEntity) : Prop :=
  cyber_hygiene_mfa e /\
  cyber_hygiene_patching e /\
  cyber_hygiene_network e /\
  cyber_hygiene_antimalware e /\
  cyber_hygiene_pam e.

Theorem mas_cyber_hygiene :
  forall (e : MASRegulatedEntity),
  mas_mfa_enabled e = true ->
  mas_patching_current e = true ->
  mas_network_secured e = true ->
  mas_antimalware e = true ->
  mas_privileged_access_managed e = true ->
  cyber_hygiene_compliant e.
Proof.
  intros e H1 H2 H3 H4 H5.
  unfold cyber_hygiene_compliant.
  unfold cyber_hygiene_mfa, cyber_hygiene_patching,
         cyber_hygiene_network, cyber_hygiene_antimalware,
         cyber_hygiene_pam.
  repeat split; assumption.
Qed.

(* ================================================================ *)
(* Patching Deadline Compliance                                      *)
(* ================================================================ *)

Definition patch_applied_in_time (criticality : PatchCriticality)
  (discovered_at applied_at : nat) : Prop :=
  applied_at <= discovered_at + patch_deadline criticality.

Theorem critical_patch_14_days :
  forall (d a : nat),
  a <= d + 14 ->
  patch_applied_in_time PatchCritical d a.
Proof.
  intros d a H. unfold patch_applied_in_time. simpl. exact H.
Qed.

(* Critical deadline is strictest *)
Theorem critical_strictest :
  forall (d a : nat),
  patch_applied_in_time PatchCritical d a ->
  patch_applied_in_time PatchHigh d a.
Proof.
  intros d a H. unfold patch_applied_in_time in *.
  simpl in *. lia.
Qed.

(* ================================================================ *)
(* TRM Guidelines: Board and Risk Governance                         *)
(* ================================================================ *)

Definition trm_governance (e : MASRegulatedEntity) : Prop :=
  mas_board_oversight e = true /\
  mas_risk_assessment_done e = true.

Definition trm_security_testing (e : MASRegulatedEntity) : Prop :=
  mas_pen_test_done e = true.

Definition trm_resilience (e : MASRegulatedEntity) : Prop :=
  mas_incident_response_plan e = true /\
  mas_bcp_tested e = true.

Theorem trm_governance_proof :
  forall (e : MASRegulatedEntity),
  mas_board_oversight e = true ->
  mas_risk_assessment_done e = true ->
  trm_governance e.
Proof.
  intros e H1 H2. unfold trm_governance. split; assumption.
Qed.

(* ================================================================ *)
(* Full MAS Compliance (Cyber Hygiene + TRM)                         *)
(* ================================================================ *)

Definition mas_fully_compliant (e : MASRegulatedEntity) : Prop :=
  cyber_hygiene_compliant e /\
  trm_governance e /\
  trm_security_testing e /\
  trm_resilience e.

Theorem mas_composition :
  forall (e : MASRegulatedEntity),
  cyber_hygiene_compliant e ->
  trm_governance e ->
  trm_security_testing e ->
  trm_resilience e ->
  mas_fully_compliant e.
Proof.
  intros e H1 H2 H3 H4.
  unfold mas_fully_compliant.
  split. exact H1.
  split. exact H2.
  split. exact H3.
  exact H4.
Qed.

(* ================================================================ *)
(* License Type Coverage                                             *)
(* ================================================================ *)

Definition all_mas_license_types : list MASLicenseType :=
  [FullBank; WholesaleBank; MerchantBank; InsuranceCo;
   CapitalMarketsServices; PaymentInstitution; MajorPaymentInstitution].

Theorem mas_license_coverage :
  forall (l : MASLicenseType), In l all_mas_license_types.
Proof.
  intros l. destruct l; simpl; auto 8.
Qed.
