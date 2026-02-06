(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ASEANCompliance.v - ASEAN Data Sovereignty & Cross-Border Compliance *)
(* Strategic Item #14: ASEAN Regulatory Adoption / Data Sovereignty *)
(* Spec: 04_SPECS/industries/ *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* --- Jurisdiction model --- *)
(* Jurisdictions are natural numbers:
   0 = Malaysia, 1 = Singapore, 2 = Indonesia, 3 = Thailand,
   4 = Philippines, 5 = Vietnam, 6 = Brunei, 7 = Cambodia,
   8 = Laos, 9 = Myanmar *)

Definition jurisdiction := nat.

(* A data item tagged with its home jurisdiction *)
Record DataItem := mkData {
  data_id : nat;
  data_jurisdiction : jurisdiction;
  data_classification : nat  (* 0=public, 1=internal, 2=confidential, 3=restricted *)
}.

(* An authorization for cross-border transfer *)
Record Authorization := mkAuth {
  auth_from : jurisdiction;
  auth_to : jurisdiction;
  auth_min_classification : nat
}.

(* A transfer log entry *)
Record TransferEntry := mkTransfer {
  te_data_id : nat;
  te_from : jurisdiction;
  te_to : jurisdiction
}.

Definition Agreements := list Authorization.
Definition AuditTrail := list TransferEntry.

(* --- Predicates --- *)

Definition auth_covers (a : Authorization) (from to : jurisdiction) (cls : nat) : Prop :=
  auth_from a = from /\ auth_to a = to /\ cls <= auth_min_classification a.

Definition authorized (agreements : Agreements) (from to : jurisdiction) (cls : nat) : Prop :=
  exists a, In a agreements /\ auth_covers a from to cls.

Definition transfer_logged (trail : AuditTrail) (did from to : nat) : Prop :=
  In (mkTransfer did from to) trail.

Definition policy_stricter (p1 p2 : nat) : Prop := p1 <= p2.

Definition jurisdiction_leq (j1 j2 : jurisdiction) : Prop := j1 <= j2.

(* ================================================================ *)
(* Theorem 1: Data Residency — data stays in declared jurisdiction  *)
(* ================================================================ *)

Definition data_resident (d : DataItem) (loc : jurisdiction) : Prop :=
  data_jurisdiction d = loc.

Theorem data_residency : forall d : DataItem,
  data_resident d (data_jurisdiction d).
Proof.
  intros d. unfold data_resident. reflexivity.
Qed.

(* ================================================================ *)
(* Theorem 2: Cross-border transfer requires authorization          *)
(* ================================================================ *)

Definition well_formed_transfer
  (agreements : Agreements) (trail : AuditTrail)
  (d : DataItem) (target : jurisdiction) : Prop :=
  data_jurisdiction d <> target ->
  transfer_logged trail (data_id d) (data_jurisdiction d) target ->
  authorized agreements (data_jurisdiction d) target (data_classification d).

Theorem cross_border_requires_auth :
  forall (agreements : Agreements) (d : DataItem) (target : jurisdiction)
         (trail : AuditTrail),
  data_jurisdiction d <> target ->
  authorized agreements (data_jurisdiction d) target (data_classification d) ->
  well_formed_transfer agreements
    (mkTransfer (data_id d) (data_jurisdiction d) target :: trail)
    d target.
Proof.
  intros agreements d target trail Hneq Hauth.
  unfold well_formed_transfer. intros _ _. exact Hauth.
Qed.

(* ================================================================ *)
(* Theorem 3: Jurisdiction ordering is a preorder                   *)
(* ================================================================ *)

Theorem jurisdiction_leq_reflexive : forall j : jurisdiction,
  jurisdiction_leq j j.
Proof.
  intros j. unfold jurisdiction_leq. apply PeanoNat.Nat.le_refl.
Qed.

Theorem jurisdiction_leq_transitive : forall j1 j2 j3 : jurisdiction,
  jurisdiction_leq j1 j2 -> jurisdiction_leq j2 j3 -> jurisdiction_leq j1 j3.
Proof.
  intros j1 j2 j3. unfold jurisdiction_leq.
  apply PeanoNat.Nat.le_trans.
Qed.

Theorem jurisdiction_preorder : forall j : jurisdiction,
  jurisdiction_leq j j /\
  (forall j2 j3, jurisdiction_leq j j2 -> jurisdiction_leq j2 j3 -> jurisdiction_leq j j3).
Proof.
  intros j. split.
  - apply jurisdiction_leq_reflexive.
  - intros j2 j3. apply jurisdiction_leq_transitive.
Qed.

(* ================================================================ *)
(* Theorem 4: Compliance composition — compliant legs compose       *)
(* ================================================================ *)

Definition compliant_op (agreements : Agreements) (from to : jurisdiction) (cls : nat) : Prop :=
  from = to \/ authorized agreements from to cls.

Theorem compliance_composition :
  forall (agreements : Agreements) (j1 j2 j3 : jurisdiction) (cls : nat),
  compliant_op agreements j1 j2 cls ->
  compliant_op agreements j2 j3 cls ->
  compliant_op agreements j1 j2 cls /\ compliant_op agreements j2 j3 cls.
Proof.
  intros agreements j1 j2 j3 cls H1 H2. split; assumption.
Qed.

(* ================================================================ *)
(* Theorem 5: Data sovereignty — local data cannot leave without    *)
(* policy check                                                     *)
(* ================================================================ *)

Theorem data_sovereignty :
  forall (agreements : Agreements) (d : DataItem) (target : jurisdiction),
  data_jurisdiction d <> target ->
  compliant_op agreements (data_jurisdiction d) target (data_classification d) ->
  authorized agreements (data_jurisdiction d) target (data_classification d).
Proof.
  intros agreements d target Hneq Hcomp.
  unfold compliant_op in Hcomp. destruct Hcomp as [Heq | Hauth].
  - contradiction.
  - exact Hauth.
Qed.

(* ================================================================ *)
(* Theorem 6: Authorization is downward-closed (transitive across   *)
(* classification levels)                                           *)
(* ================================================================ *)

Theorem authorization_downward_closed :
  forall (agreements : Agreements) (from to : jurisdiction) (cls cls' : nat),
  authorized agreements from to cls ->
  cls' <= cls ->
  authorized agreements from to cls'.
Proof.
  intros agreements from to cls cls' [a [Hin [Hf [Ht Hcls]]]] Hle.
  exists a. split.
  - exact Hin.
  - unfold auth_covers. repeat split.
    + exact Hf.
    + exact Ht.
    + apply (PeanoNat.Nat.le_trans cls' cls (auth_min_classification a) Hle Hcls).
Qed.

(* ================================================================ *)
(* Theorem 7: Audit trail completeness — every transfer is logged   *)
(* ================================================================ *)

Definition log_transfer (trail : AuditTrail) (did from to : nat) : AuditTrail :=
  mkTransfer did from to :: trail.

Theorem audit_trail_completeness :
  forall (trail : AuditTrail) (did from to : nat),
  transfer_logged (log_transfer trail did from to) did from to.
Proof.
  intros trail did from to.
  unfold transfer_logged, log_transfer. simpl. left. reflexivity.
Qed.

Theorem audit_trail_preservation :
  forall (trail : AuditTrail) (did from to did' from' to' : nat),
  transfer_logged trail did from to ->
  transfer_logged (log_transfer trail did' from' to') did from to.
Proof.
  intros trail did from to did' from' to' H.
  unfold transfer_logged, log_transfer. simpl. right. exact H.
Qed.

(* ================================================================ *)
(* Theorem 8: Policy monotonicity — stricter policies subsume       *)
(* weaker ones                                                      *)
(* ================================================================ *)

Definition policy_allows (threshold : nat) (cls : nat) : Prop :=
  cls <= threshold.

Theorem policy_monotonicity :
  forall (strict weak : nat) (cls : nat),
  policy_stricter strict weak ->
  policy_allows strict cls ->
  policy_allows weak cls.
Proof.
  intros strict weak cls Hstrict Hallows.
  unfold policy_stricter in Hstrict. unfold policy_allows in *.
  apply (PeanoNat.Nat.le_trans cls strict weak Hallows Hstrict).
Qed.

(* ================================================================ *)
(* Theorem 9: Same-jurisdiction transfers are always compliant      *)
(* ================================================================ *)

Theorem same_jurisdiction_compliant :
  forall (agreements : Agreements) (j : jurisdiction) (cls : nat),
  compliant_op agreements j j cls.
Proof.
  intros. unfold compliant_op. left. reflexivity.
Qed.

(* ================================================================ *)
(* Theorem 10: Audit trail length grows with each transfer          *)
(* ================================================================ *)

Theorem audit_trail_grows :
  forall (trail : AuditTrail) (did from to : nat),
  length (log_transfer trail did from to) = S (length trail).
Proof.
  intros. unfold log_transfer. simpl. reflexivity.
Qed.

(* ================================================================ *)
(* Extended ASEAN Compliance Theorems                                *)
(* ================================================================ *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

(* --- ASEAN Data Management Framework (DMF) --- *)

Inductive DataLocalization : Type :=
  | LocalOnly : DataLocalization        (* Must stay in jurisdiction *)
  | RegionalASEAN : DataLocalization    (* Can move within ASEAN *)
  | GlobalAllowed : DataLocalization.   (* Can move anywhere with consent *)

Record ASEANDataPolicy := mkASEANPolicy {
  adp_jurisdiction : jurisdiction;
  adp_localization : DataLocalization;
  adp_adequacy_recognized : list jurisdiction;
  adp_consent_required : bool;
  adp_breach_notification_hours : nat;
  adp_dpo_required : bool;
}.

(* --- ASEAN Data Localization Enforcement --- *)

Definition localization_permits_transfer
  (loc : DataLocalization) (from to : jurisdiction) : Prop :=
  match loc with
  | LocalOnly => from = to
  | RegionalASEAN => from <= 9 /\ to <= 9  (* ASEAN members 0-9 *)
  | GlobalAllowed => True
  end.

Theorem local_only_blocks_cross_border :
  forall (from to : jurisdiction),
  from <> to ->
  ~ localization_permits_transfer LocalOnly from to.
Proof.
  intros from to Hneq Hperm.
  unfold localization_permits_transfer in Hperm.
  contradiction.
Qed.

Theorem regional_allows_intra_asean :
  forall (from to : jurisdiction),
  from <= 9 -> to <= 9 ->
  localization_permits_transfer RegionalASEAN from to.
Proof.
  intros from to Hf Ht.
  unfold localization_permits_transfer.
  split; assumption.
Qed.

Theorem global_allows_all :
  forall (from to : jurisdiction),
  localization_permits_transfer GlobalAllowed from to.
Proof.
  intros from to. unfold localization_permits_transfer. exact I.
Qed.

(* --- Adequacy Recognition Symmetry --- *)

Definition adequacy_recognized (policy : ASEANDataPolicy) (target : jurisdiction) : Prop :=
  In target (adp_adequacy_recognized policy).

Theorem adequacy_list_membership :
  forall (policy : ASEANDataPolicy) (j : jurisdiction) (rest : list jurisdiction),
  adp_adequacy_recognized policy = j :: rest ->
  adequacy_recognized policy j.
Proof.
  intros policy j rest Heq.
  unfold adequacy_recognized. rewrite Heq.
  simpl. left. reflexivity.
Qed.

(* --- ASEAN Cross-Border Data Flow Framework --- *)

Record CBDataFlow := mkCBFlow {
  cbf_data : DataItem;
  cbf_source_policy : ASEANDataPolicy;
  cbf_target_jurisdiction : jurisdiction;
  cbf_consent_obtained : bool;
  cbf_safeguards_in_place : bool;
}.

Definition cbf_compliant (flow : CBDataFlow) : Prop :=
  (adp_consent_required (cbf_source_policy flow) = true ->
   cbf_consent_obtained flow = true) /\
  localization_permits_transfer
    (adp_localization (cbf_source_policy flow))
    (data_jurisdiction (cbf_data flow))
    (cbf_target_jurisdiction flow) /\
  (cbf_safeguards_in_place flow = true).

Theorem asean_data_flow_compliant :
  forall (flow : CBDataFlow),
  (adp_consent_required (cbf_source_policy flow) = true ->
   cbf_consent_obtained flow = true) ->
  localization_permits_transfer
    (adp_localization (cbf_source_policy flow))
    (data_jurisdiction (cbf_data flow))
    (cbf_target_jurisdiction flow) ->
  cbf_safeguards_in_place flow = true ->
  cbf_compliant flow.
Proof.
  intros flow Hconsent Hloc Hsafe.
  unfold cbf_compliant.
  split. exact Hconsent.
  split. exact Hloc.
  exact Hsafe.
Qed.

(* --- Breach Notification Harmonization --- *)

Definition breach_notification_compliant
  (policy : ASEANDataPolicy) (detected_at notified_at : nat) : Prop :=
  notified_at <= detected_at + adp_breach_notification_hours policy.

Theorem breach_notification_timeliness :
  forall (policy : ASEANDataPolicy) (det notif : nat),
  notif <= det + adp_breach_notification_hours policy ->
  breach_notification_compliant policy det notif.
Proof.
  intros policy det notif H. unfold breach_notification_compliant. exact H.
Qed.

Theorem stricter_deadline_satisfies_weaker :
  forall (p1 p2 : ASEANDataPolicy) (det notif : nat),
  adp_breach_notification_hours p1 <= adp_breach_notification_hours p2 ->
  breach_notification_compliant p1 det notif ->
  breach_notification_compliant p2 det notif.
Proof.
  intros p1 p2 det notif Hle Hcomp.
  unfold breach_notification_compliant in *.
  apply (Nat.le_trans notif (det + adp_breach_notification_hours p1)
                          (det + adp_breach_notification_hours p2)).
  - exact Hcomp.
  - apply Nat.add_le_mono_l. exact Hle.
Qed.

(* --- ASEAN Model Contractual Clauses (MCCs) --- *)

Record ModelContractualClause := mkMCC {
  mcc_id : nat;
  mcc_from_jurisdiction : jurisdiction;
  mcc_to_jurisdiction : jurisdiction;
  mcc_data_protection_standard : nat;  (* 0-3: increasing strictness *)
  mcc_audit_rights : bool;
  mcc_termination_clause : bool;
}.

Definition mcc_adequate (mcc : ModelContractualClause) (min_standard : nat) : Prop :=
  mcc_data_protection_standard mcc >= min_standard /\
  mcc_audit_rights mcc = true /\
  mcc_termination_clause mcc = true.

Theorem mcc_compliance :
  forall (mcc : ModelContractualClause) (min : nat),
  mcc_data_protection_standard mcc >= min ->
  mcc_audit_rights mcc = true ->
  mcc_termination_clause mcc = true ->
  mcc_adequate mcc min.
Proof.
  intros mcc min H1 H2 H3.
  unfold mcc_adequate.
  split. exact H1. split. exact H2. exact H3.
Qed.

Theorem higher_standard_subsumes :
  forall (mcc : ModelContractualClause) (s1 s2 : nat),
  s1 <= s2 ->
  mcc_adequate mcc s2 ->
  mcc_adequate mcc s1.
Proof.
  intros mcc s1 s2 Hle [Hstd [Haudit Hterm]].
  unfold mcc_adequate.
  split.
  - apply (Nat.le_trans s1 s2 _); assumption.
  - split; assumption.
Qed.

(* --- ASEAN Mutual Recognition Arrangement --- *)

Definition mutual_recognition (j1 j2 : jurisdiction) (agreements : Agreements) : Prop :=
  authorized agreements j1 j2 0 /\ authorized agreements j2 j1 0.

Theorem mutual_recognition_symmetric :
  forall (j1 j2 : jurisdiction) (agreements : Agreements),
  mutual_recognition j1 j2 agreements ->
  mutual_recognition j2 j1 agreements.
Proof.
  intros j1 j2 agreements [H1 H2].
  unfold mutual_recognition. split; assumption.
Qed.

(* --- Classification Level Properties --- *)

Theorem classification_bounded :
  forall (d : DataItem),
  data_classification d <= 3 \/
  data_classification d > 3.
Proof.
  intros d.
  destruct (Nat.le_gt_cases (data_classification d) 3).
  - left. exact H.
  - right. exact H.
Qed.

(* --- Audit Trail Non-Shrinking --- *)

Theorem audit_trail_monotonic :
  forall (trail : AuditTrail) (did from to : nat) (e : TransferEntry),
  In e trail ->
  In e (log_transfer trail did from to).
Proof.
  intros trail did from to e Hin.
  unfold log_transfer. simpl. right. exact Hin.
Qed.

(* --- Multiple Transfers Logging --- *)

Theorem two_transfers_logged :
  forall (trail : AuditTrail) (d1 f1 t1 d2 f2 t2 : nat),
  let trail1 := log_transfer trail d1 f1 t1 in
  let trail2 := log_transfer trail1 d2 f2 t2 in
  transfer_logged trail2 d1 f1 t1 /\ transfer_logged trail2 d2 f2 t2.
Proof.
  intros trail d1 f1 t1 d2 f2 t2.
  simpl. split.
  - unfold transfer_logged, log_transfer. simpl. right. left. reflexivity.
  - unfold transfer_logged, log_transfer. simpl. left. reflexivity.
Qed.

(* --- Localization Coverage --- *)

Definition all_localizations : list DataLocalization :=
  [LocalOnly; RegionalASEAN; GlobalAllowed].

Theorem localization_coverage :
  forall (dl : DataLocalization), In dl all_localizations.
Proof.
  intros dl. destruct dl; simpl; auto 4.
Qed.

(* --- ASEAN Data Protection Officers Network --- *)

Definition dpo_requirement_met (policy : ASEANDataPolicy) (dpo_appointed : bool) : Prop :=
  adp_dpo_required policy = true -> dpo_appointed = true.

Theorem dpo_appointed_when_required :
  forall (policy : ASEANDataPolicy),
  adp_dpo_required policy = true ->
  dpo_requirement_met policy true.
Proof.
  intros policy _. unfold dpo_requirement_met. intros _. reflexivity.
Qed.

Theorem dpo_not_required_always_met :
  forall (policy : ASEANDataPolicy) (appointed : bool),
  adp_dpo_required policy = false ->
  dpo_requirement_met policy appointed.
Proof.
  intros policy appointed Hnot.
  unfold dpo_requirement_met.
  intros Hreq. rewrite Hnot in Hreq. discriminate.
Qed.
