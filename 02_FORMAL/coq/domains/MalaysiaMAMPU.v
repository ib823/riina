(* MalaysiaMAMPU.v - MAMPU / MyGovCloud Security Requirements *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Governing Body: MAMPU (Malaysian Administrative Modernisation and *)
(*   Management Planning Unit, Prime Minister's Department) *)

(* ========================================================================= *)
(* MAMPU requirements for government ICT systems:                            *)
(*   - MyGovCloud security classification (Rahsia/Sulit/Terhad/Terbuka)     *)
(*   - RAKKSSA (Rangka Kerja Keselamatan Siber Sektor Awam)                  *)
(*   - Government data sovereignty (data must reside in Malaysia)            *)
(*   - Compliance with DKICT (Dasar Keselamatan ICT)                         *)
(*   - Security assessment before deployment on government infrastructure    *)
(*   - ISMS (Information Security Management System) requirements            *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* ================================================================ *)
(* Government Data Classification (Peringkat Keselamatan)            *)
(* ================================================================ *)

Inductive GovClassification : Type :=
  | Terbuka : GovClassification      (* Open / Public *)
  | Terhad : GovClassification       (* Restricted *)
  | Sulit : GovClassification        (* Confidential *)
  | Rahsia : GovClassification       (* Secret *)
  | RahsiaBesar : GovClassification. (* Top Secret *)

Definition classification_level (c : GovClassification) : nat :=
  match c with
  | Terbuka => 0
  | Terhad => 1
  | Sulit => 2
  | Rahsia => 3
  | RahsiaBesar => 4
  end.

(* ================================================================ *)
(* Government System Model                                           *)
(* ================================================================ *)

Record GovSystem := mkGovSystem {
  gov_id : nat;
  gov_classification : GovClassification;
  gov_data_in_malaysia : bool;        (* Data sovereignty *)
  gov_isms_certified : bool;          (* ISO 27001 / ISMS *)
  gov_security_assessed : bool;       (* Pre-deployment assessment *)
  gov_encrypted : bool;
  gov_access_controlled : bool;
  gov_audit_logged : bool;
  gov_on_mygovcloud : bool;
}.

(* ================================================================ *)
(* Requirement 1: Data Sovereignty                                   *)
(* Government data MUST reside within Malaysian borders              *)
(* ================================================================ *)

Definition data_sovereign (s : GovSystem) : Prop :=
  gov_data_in_malaysia s = true.

Theorem mampu_sovereignty :
  forall (s : GovSystem),
  gov_data_in_malaysia s = true ->
  data_sovereign s.
Proof.
  intros s H. unfold data_sovereign. exact H.
Qed.

(* ================================================================ *)
(* Requirement 2: Classification-Based Controls                      *)
(* Higher classification requires stronger controls                   *)
(* ================================================================ *)

Definition controls_match_classification (s : GovSystem) : Prop :=
  match gov_classification s with
  | Terbuka => True
  | Terhad => gov_access_controlled s = true
  | Sulit => gov_encrypted s = true /\ gov_access_controlled s = true
  | Rahsia => gov_encrypted s = true /\ gov_access_controlled s = true
              /\ gov_audit_logged s = true
  | RahsiaBesar => gov_encrypted s = true /\ gov_access_controlled s = true
              /\ gov_audit_logged s = true /\ gov_isms_certified s = true
  end.

Theorem mampu_terbuka :
  forall (s : GovSystem),
  gov_classification s = Terbuka ->
  controls_match_classification s.
Proof.
  intros s H. unfold controls_match_classification. rewrite H. exact I.
Qed.

Theorem mampu_rahsia :
  forall (s : GovSystem),
  gov_classification s = Rahsia ->
  gov_encrypted s = true ->
  gov_access_controlled s = true ->
  gov_audit_logged s = true ->
  controls_match_classification s.
Proof.
  intros s Hc He Ha Hau. unfold controls_match_classification.
  rewrite Hc. split. exact He. split. exact Ha. exact Hau.
Qed.

Theorem mampu_rahsia_besar :
  forall (s : GovSystem),
  gov_classification s = RahsiaBesar ->
  gov_encrypted s = true ->
  gov_access_controlled s = true ->
  gov_audit_logged s = true ->
  gov_isms_certified s = true ->
  controls_match_classification s.
Proof.
  intros s Hc He Ha Hau Hi. unfold controls_match_classification.
  rewrite Hc. split. exact He. split. exact Ha. split. exact Hau. exact Hi.
Qed.

(* ================================================================ *)
(* Requirement 3: Security Assessment (Pre-deployment)               *)
(* RAKKSSA mandates assessment before government deployment          *)
(* ================================================================ *)

Definition security_assessed (s : GovSystem) : Prop :=
  gov_security_assessed s = true.

Theorem mampu_assessment :
  forall (s : GovSystem),
  gov_security_assessed s = true ->
  security_assessed s.
Proof.
  intros s H. unfold security_assessed. exact H.
Qed.

(* ================================================================ *)
(* Requirement 4: ISMS Certification                                 *)
(* ================================================================ *)

Definition isms_compliant (s : GovSystem) : Prop :=
  gov_isms_certified s = true.

Theorem mampu_isms :
  forall (s : GovSystem),
  gov_isms_certified s = true ->
  isms_compliant s.
Proof.
  intros s H. unfold isms_compliant. exact H.
Qed.

(* ================================================================ *)
(* Classification level ordering                                     *)
(* ================================================================ *)

Theorem classification_ordering :
  forall (c1 c2 : GovClassification),
  classification_level c1 <= classification_level c2 \/
  classification_level c2 <= classification_level c1.
Proof.
  intros c1 c2.
  destruct (Nat.le_ge_cases (classification_level c1) (classification_level c2)).
  - left. exact H.
  - right. exact H.
Qed.

(* Higher classification strictly dominates *)
Theorem rahsia_besar_highest :
  forall (c : GovClassification),
  classification_level c <= classification_level RahsiaBesar.
Proof.
  intros c. destruct c; simpl; auto with arith.
Qed.

(* ================================================================ *)
(* Full MAMPU Compliance                                             *)
(* ================================================================ *)

Definition mampu_fully_compliant (s : GovSystem) : Prop :=
  data_sovereign s /\
  controls_match_classification s /\
  security_assessed s.

Theorem mampu_composition :
  forall (s : GovSystem),
  data_sovereign s ->
  controls_match_classification s ->
  security_assessed s ->
  mampu_fully_compliant s.
Proof.
  intros s H1 H2 H3. unfold mampu_fully_compliant.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* Classification coverage *)
Definition all_gov_classifications : list GovClassification :=
  [Terbuka; Terhad; Sulit; Rahsia; RahsiaBesar].

Theorem gov_classification_coverage :
  forall (c : GovClassification), In c all_gov_classifications.
Proof.
  intros c. destruct c; simpl; auto 6.
Qed.
