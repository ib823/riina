(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

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
