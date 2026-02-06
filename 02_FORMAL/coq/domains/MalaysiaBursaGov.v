(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* MalaysiaBursaGov.v - Bursa Malaysia IT Governance Requirements *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Governing Body: Bursa Malaysia Berhad *)

(* ========================================================================= *)
(* Bursa Malaysia Listing Requirements relevant to IT governance:            *)
(*   - Corporate Governance Code (MCCG 2021) IT provisions                   *)
(*   - Listed entity technology risk management                              *)
(*   - Trading system integrity and availability                             *)
(*   - Market data protection                                                *)
(*   - Participant connectivity security                                     *)
(*   - Business continuity for market operations                             *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* ================================================================ *)
(* Market Participant Model                                          *)
(* ================================================================ *)

Inductive ParticipantType : Type :=
  | TradingParticipant : ParticipantType
  | ClearingParticipant : ParticipantType
  | Depository : ParticipantType
  | AuthorisedDepositoryAgent : ParticipantType.

Record MarketParticipant := mkParticipant {
  mp_id : nat;
  mp_type : ParticipantType;
  mp_it_governance : bool;
  mp_risk_managed : bool;
  mp_system_integrity : bool;
  mp_data_protected : bool;
  mp_connectivity_secured : bool;
  mp_bcp_tested : bool;
}.

(* ================================================================ *)
(* Requirement 1: IT Governance (MCCG 2021 Practice 11.2)            *)
(* Board must ensure adequate IT governance framework                 *)
(* ================================================================ *)

Definition it_governance_established (p : MarketParticipant) : Prop :=
  mp_it_governance p = true.

Theorem bursa_governance :
  forall (p : MarketParticipant),
  mp_it_governance p = true ->
  it_governance_established p.
Proof.
  intros p H. unfold it_governance_established. exact H.
Qed.

(* ================================================================ *)
(* Requirement 2: Trading System Integrity                           *)
(* Systems must maintain integrity and availability                   *)
(* ================================================================ *)

Definition system_integrity (p : MarketParticipant) : Prop :=
  mp_system_integrity p = true.

Theorem bursa_integrity :
  forall (p : MarketParticipant),
  mp_system_integrity p = true ->
  system_integrity p.
Proof.
  intros p H. unfold system_integrity. exact H.
Qed.

(* ================================================================ *)
(* Requirement 3: Market Data Protection                             *)
(* ================================================================ *)

Definition data_protected (p : MarketParticipant) : Prop :=
  mp_data_protected p = true.

Theorem bursa_data_protection :
  forall (p : MarketParticipant),
  mp_data_protected p = true ->
  data_protected p.
Proof.
  intros p H. unfold data_protected. exact H.
Qed.

(* ================================================================ *)
(* Requirement 4: Connectivity Security                              *)
(* ================================================================ *)

Definition connectivity_secured (p : MarketParticipant) : Prop :=
  mp_connectivity_secured p = true.

Theorem bursa_connectivity :
  forall (p : MarketParticipant),
  mp_connectivity_secured p = true ->
  connectivity_secured p.
Proof.
  intros p H. unfold connectivity_secured. exact H.
Qed.

(* ================================================================ *)
(* Requirement 5: Business Continuity                                *)
(* ================================================================ *)

Definition bcp_ready (p : MarketParticipant) : Prop :=
  mp_bcp_tested p = true.

Theorem bursa_bcp :
  forall (p : MarketParticipant),
  mp_bcp_tested p = true ->
  bcp_ready p.
Proof.
  intros p H. unfold bcp_ready. exact H.
Qed.

(* ================================================================ *)
(* Full Bursa Compliance                                             *)
(* ================================================================ *)

Definition bursa_fully_compliant (p : MarketParticipant) : Prop :=
  it_governance_established p /\
  system_integrity p /\
  data_protected p /\
  connectivity_secured p /\
  bcp_ready p.

Theorem bursa_composition :
  forall (p : MarketParticipant),
  it_governance_established p ->
  system_integrity p ->
  data_protected p ->
  connectivity_secured p ->
  bcp_ready p ->
  bursa_fully_compliant p.
Proof.
  intros p H1 H2 H3 H4 H5. unfold bursa_fully_compliant.
  split. exact H1. split. exact H2. split. exact H3.
  split. exact H4. exact H5.
Qed.

(* Participant type coverage *)
Definition all_participant_types : list ParticipantType :=
  [TradingParticipant; ClearingParticipant; Depository; AuthorisedDepositoryAgent].

Theorem participant_coverage :
  forall (t : ParticipantType), In t all_participant_types.
Proof.
  intros t. destruct t; simpl; auto 5.
Qed.

Require Import Coq.micromega.Lia.

(* ================================================================ *)
(* Risk Management                                                   *)
(* ================================================================ *)

Definition risk_managed (p : MarketParticipant) : Prop :=
  mp_risk_managed p = true.

Theorem bursa_risk :
  forall (p : MarketParticipant),
  mp_risk_managed p = true ->
  risk_managed p.
Proof.
  intros p H. unfold risk_managed. exact H.
Qed.

(* ================================================================ *)
(* Compliance Decomposition Theorems                                 *)
(* ================================================================ *)

Theorem bursa_compliant_implies_governance :
  forall (p : MarketParticipant),
  bursa_fully_compliant p ->
  it_governance_established p.
Proof.
  intros p [H _]. exact H.
Qed.

Theorem bursa_compliant_implies_integrity :
  forall (p : MarketParticipant),
  bursa_fully_compliant p ->
  system_integrity p.
Proof.
  intros p [_ [H _]]. exact H.
Qed.

Theorem bursa_compliant_implies_data_protection :
  forall (p : MarketParticipant),
  bursa_fully_compliant p ->
  data_protected p.
Proof.
  intros p [_ [_ [H _]]]. exact H.
Qed.

Theorem bursa_compliant_implies_connectivity :
  forall (p : MarketParticipant),
  bursa_fully_compliant p ->
  connectivity_secured p.
Proof.
  intros p [_ [_ [_ [H _]]]]. exact H.
Qed.

Theorem bursa_compliant_implies_bcp :
  forall (p : MarketParticipant),
  bursa_fully_compliant p ->
  bcp_ready p.
Proof.
  intros p [_ [_ [_ [_ H]]]]. exact H.
Qed.

(* ================================================================ *)
(* Violation Detection Theorems                                      *)
(* ================================================================ *)

Theorem governance_violation_blocks_compliance :
  forall (p : MarketParticipant),
  mp_it_governance p = false ->
  ~ it_governance_established p.
Proof.
  intros p Hf Hc. unfold it_governance_established in Hc.
  rewrite Hf in Hc. discriminate.
Qed.

Theorem integrity_violation_blocks_compliance :
  forall (p : MarketParticipant),
  mp_system_integrity p = false ->
  ~ system_integrity p.
Proof.
  intros p Hf Hc. unfold system_integrity in Hc.
  rewrite Hf in Hc. discriminate.
Qed.

Theorem data_violation_blocks_compliance :
  forall (p : MarketParticipant),
  mp_data_protected p = false ->
  ~ data_protected p.
Proof.
  intros p Hf Hc. unfold data_protected in Hc.
  rewrite Hf in Hc. discriminate.
Qed.

Theorem connectivity_violation_blocks_compliance :
  forall (p : MarketParticipant),
  mp_connectivity_secured p = false ->
  ~ connectivity_secured p.
Proof.
  intros p Hf Hc. unfold connectivity_secured in Hc.
  rewrite Hf in Hc. discriminate.
Qed.

Theorem bcp_violation_blocks_compliance :
  forall (p : MarketParticipant),
  mp_bcp_tested p = false ->
  ~ bcp_ready p.
Proof.
  intros p Hf Hc. unfold bcp_ready in Hc.
  rewrite Hf in Hc. discriminate.
Qed.

(* ================================================================ *)
(* Trading System Availability Model                                 *)
(* ================================================================ *)

Record TradingSystem := mkTradingSystem {
  ts_participant_id : nat;
  ts_uptime_pct : nat;         (* percentage, 0-100 *)
  ts_min_uptime : nat;         (* minimum required uptime *)
  ts_redundant : bool;
  ts_failover_tested : bool;
}.

Definition ts_availability_adequate (ts : TradingSystem) : Prop :=
  ts_min_uptime ts <= ts_uptime_pct ts.

Definition ts_resilient (ts : TradingSystem) : Prop :=
  ts_redundant ts = true /\ ts_failover_tested ts = true.

Theorem trading_system_availability :
  forall (ts : TradingSystem),
  ts_min_uptime ts <= ts_uptime_pct ts ->
  ts_availability_adequate ts.
Proof.
  intros ts H. unfold ts_availability_adequate. exact H.
Qed.

Theorem trading_system_resilience :
  forall (ts : TradingSystem),
  ts_redundant ts = true ->
  ts_failover_tested ts = true ->
  ts_resilient ts.
Proof.
  intros ts H1 H2. unfold ts_resilient. split; assumption.
Qed.

Theorem insufficient_uptime :
  forall (ts : TradingSystem),
  ts_uptime_pct ts < ts_min_uptime ts ->
  ~ ts_availability_adequate ts.
Proof.
  intros ts Hlt Hge. unfold ts_availability_adequate in Hge. lia.
Qed.

(* ================================================================ *)
(* Full Compliance with Risk Management                              *)
(* ================================================================ *)

Definition bursa_fully_compliant_v2 (p : MarketParticipant) : Prop :=
  bursa_fully_compliant p /\ risk_managed p.

Theorem bursa_composition_v2 :
  forall (p : MarketParticipant),
  bursa_fully_compliant p ->
  risk_managed p ->
  bursa_fully_compliant_v2 p.
Proof.
  intros p H1 H2. unfold bursa_fully_compliant_v2. split; assumption.
Qed.

Theorem bursa_v2_implies_v1 :
  forall (p : MarketParticipant),
  bursa_fully_compliant_v2 p ->
  bursa_fully_compliant p.
Proof.
  intros p [H _]. exact H.
Qed.
