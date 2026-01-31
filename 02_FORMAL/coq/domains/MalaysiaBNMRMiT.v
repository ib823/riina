(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* MalaysiaBNMRMiT.v - Bank Negara Malaysia Risk Management in Technology *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md §A2 *)
(* Legal Requirement: BNM/RH/PD 028-16 (RMiT), updated November 28, 2025 *)
(* Governing Body: Bank Negara Malaysia (BNM) *)

(* ========================================================================= *)
(* RMiT covers 8 domains for Malaysian financial institutions:               *)
(*   1. Governance and oversight                                             *)
(*   2. Technology risk management                                           *)
(*   3. Cybersecurity                                                        *)
(*   4. Technology operations                                                *)
(*   5. Audit and internal training                                          *)
(*   6. Cloud security governance                                            *)
(*   7. Third-party risk management                                          *)
(*   8. Operational resilience                                               *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================ *)
(* Financial Institution Model                                       *)
(* ================================================================ *)

Inductive FIType : Type :=
  | Bank : FIType
  | Insurer : FIType
  | TakafulOperator : FIType
  | PaymentSystemOperator : FIType
  | DesignatedPaymentInstrument : FIType
  | ApprovedElectronicMoney : FIType.

Inductive CloudDeployment : Type :=
  | OnPremise : CloudDeployment
  | PrivateCloud : CloudDeployment
  | PublicCloud : CloudDeployment
  | HybridCloud : CloudDeployment.

Record FinancialInstitution := mkFI {
  fi_id : nat;
  fi_type : FIType;
  fi_board_oversight : bool;       (* Domain 1: Board-level tech governance *)
  fi_risk_framework : bool;        (* Domain 2: Technology risk framework *)
  fi_cyber_controls : nat;         (* Domain 3: Number of cyber controls *)
  fi_min_cyber_controls : nat;     (* Domain 3: Minimum required *)
  fi_ops_resilience_tested : bool; (* Domain 4: Operations tested *)
  fi_audit_completed : bool;       (* Domain 5: Audit done *)
  fi_cloud_model : CloudDeployment;(* Domain 6: Cloud deployment *)
  fi_cloud_risk_assessed : bool;   (* Domain 6: Cloud risk assessed *)
  fi_third_party_assessed : bool;  (* Domain 7: Vendor assessments done *)
  fi_bcp_tested : bool;            (* Domain 8: BCP/DR tested *)
}.

(* ================================================================ *)
(* Domain 1: Governance and Oversight                                *)
(* Board must have technology risk oversight capability               *)
(* ================================================================ *)

Definition governance_compliant (fi : FinancialInstitution) : Prop :=
  fi_board_oversight fi = true.

Theorem rmit_domain_1 :
  forall (fi : FinancialInstitution),
  fi_board_oversight fi = true ->
  governance_compliant fi.
Proof.
  intros fi H. unfold governance_compliant. exact H.
Qed.

(* ================================================================ *)
(* Domain 2: Technology Risk Management                              *)
(* Comprehensive technology risk framework mandatory                  *)
(* ================================================================ *)

Definition risk_framework_established (fi : FinancialInstitution) : Prop :=
  fi_risk_framework fi = true.

Theorem rmit_domain_2 :
  forall (fi : FinancialInstitution),
  fi_risk_framework fi = true ->
  risk_framework_established fi.
Proof.
  intros fi H. unfold risk_framework_established. exact H.
Qed.

(* ================================================================ *)
(* Domain 3: Cybersecurity                                           *)
(* Cyber resilience measures must meet minimum threshold              *)
(* This is where RIINA's formal verification adds most value          *)
(* ================================================================ *)

Definition cyber_controls_adequate (fi : FinancialInstitution) : Prop :=
  fi_min_cyber_controls fi <= fi_cyber_controls fi.

Theorem rmit_domain_3 :
  forall (fi : FinancialInstitution),
  fi_min_cyber_controls fi <= fi_cyber_controls fi ->
  cyber_controls_adequate fi.
Proof.
  intros fi H. unfold cyber_controls_adequate. exact H.
Qed.

(* ================================================================ *)
(* Domain 4: Technology Operations                                   *)
(* ================================================================ *)

Definition ops_resilience_verified (fi : FinancialInstitution) : Prop :=
  fi_ops_resilience_tested fi = true.

Theorem rmit_domain_4 :
  forall (fi : FinancialInstitution),
  fi_ops_resilience_tested fi = true ->
  ops_resilience_verified fi.
Proof.
  intros fi H. unfold ops_resilience_verified. exact H.
Qed.

(* ================================================================ *)
(* Domain 5: Audit and Internal Training                             *)
(* ================================================================ *)

Definition audit_compliant (fi : FinancialInstitution) : Prop :=
  fi_audit_completed fi = true.

Theorem rmit_domain_5 :
  forall (fi : FinancialInstitution),
  fi_audit_completed fi = true ->
  audit_compliant fi.
Proof.
  intros fi H. unfold audit_compliant. exact H.
Qed.

(* ================================================================ *)
(* Domain 6: Cloud Security Governance                               *)
(* Cloud deployments require explicit risk assessment                  *)
(* ================================================================ *)

Definition cloud_compliant (fi : FinancialInstitution) : Prop :=
  match fi_cloud_model fi with
  | OnPremise => True  (* No cloud risk assessment needed *)
  | _ => fi_cloud_risk_assessed fi = true
  end.

Theorem rmit_domain_6_onprem :
  forall (fi : FinancialInstitution),
  fi_cloud_model fi = OnPremise ->
  cloud_compliant fi.
Proof.
  intros fi H. unfold cloud_compliant. rewrite H. exact I.
Qed.

Theorem rmit_domain_6_cloud :
  forall (fi : FinancialInstitution),
  fi_cloud_model fi <> OnPremise ->
  fi_cloud_risk_assessed fi = true ->
  cloud_compliant fi.
Proof.
  intros fi Hnotop Hassessed. unfold cloud_compliant.
  destruct (fi_cloud_model fi); try exact Hassessed. contradiction.
Qed.

(* ================================================================ *)
(* Domain 7: Third-Party Risk Management                             *)
(* ================================================================ *)

Definition third_party_compliant (fi : FinancialInstitution) : Prop :=
  fi_third_party_assessed fi = true.

Theorem rmit_domain_7 :
  forall (fi : FinancialInstitution),
  fi_third_party_assessed fi = true ->
  third_party_compliant fi.
Proof.
  intros fi H. unfold third_party_compliant. exact H.
Qed.

(* ================================================================ *)
(* Domain 8: Operational Resilience                                  *)
(* BCP/DR must be tested                                              *)
(* ================================================================ *)

Definition bcp_compliant (fi : FinancialInstitution) : Prop :=
  fi_bcp_tested fi = true.

Theorem rmit_domain_8 :
  forall (fi : FinancialInstitution),
  fi_bcp_tested fi = true ->
  bcp_compliant fi.
Proof.
  intros fi H. unfold bcp_compliant. exact H.
Qed.

(* ================================================================ *)
(* Full RMiT Compliance Composition (all 8 domains)                  *)
(* ================================================================ *)

Definition rmit_fully_compliant (fi : FinancialInstitution) : Prop :=
  governance_compliant fi /\
  risk_framework_established fi /\
  cyber_controls_adequate fi /\
  ops_resilience_verified fi /\
  audit_compliant fi /\
  cloud_compliant fi /\
  third_party_compliant fi /\
  bcp_compliant fi.

Theorem rmit_composition :
  forall (fi : FinancialInstitution),
  governance_compliant fi ->
  risk_framework_established fi ->
  cyber_controls_adequate fi ->
  ops_resilience_verified fi ->
  audit_compliant fi ->
  cloud_compliant fi ->
  third_party_compliant fi ->
  bcp_compliant fi ->
  rmit_fully_compliant fi.
Proof.
  intros fi H1 H2 H3 H4 H5 H6 H7 H8.
  unfold rmit_fully_compliant. repeat split; assumption.
Qed.

(* ================================================================ *)
(* FI Type Coverage: All institution types enumerated                 *)
(* ================================================================ *)

Definition all_fi_types : list FIType :=
  [Bank; Insurer; TakafulOperator; PaymentSystemOperator;
   DesignatedPaymentInstrument; ApprovedElectronicMoney].

Theorem fi_type_coverage :
  forall (ft : FIType), In ft all_fi_types.
Proof.
  intros ft. destruct ft; simpl; auto 7.
Qed.
