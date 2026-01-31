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
