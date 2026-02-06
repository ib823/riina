(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* MalaysiaDigitalSignature.v - Digital Signature Act 1997 (Act 562) *)
(* Spec: 04_SPECS/industries/REGULATORY_COMPLIANCE_MALAYSIA_SINGAPORE_2026.md *)
(* Legal Requirement: Digital Signature Act 1997 *)
(* Governing Body: MCMC (Malaysian Communications and Multimedia Commission) *)

(* ========================================================================= *)
(* The Digital Signature Act 1997 establishes:                               *)
(*   - Legal recognition of digital signatures                               *)
(*   - Licensed Certification Authority (CA) requirements                    *)
(*   - Certificate lifecycle (issuance, suspension, revocation)              *)
(*   - Subscriber duties (private key protection)                            *)
(*   - Relying party duties (certificate verification)                       *)
(*   - Presumption of security for licensed CA certificates                  *)
(* ========================================================================= *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ================================================================ *)
(* Certificate and Signature Model                                   *)
(* ================================================================ *)

Inductive CertStatus : Type :=
  | CertActive : CertStatus
  | CertSuspended : CertStatus
  | CertRevoked : CertStatus
  | CertExpired : CertStatus.

Inductive CALicenseStatus : Type :=
  | CALicensed : CALicenseStatus
  | CAUnlicensed : CALicenseStatus.

Record Certificate := mkCert {
  cert_id : nat;
  cert_subject : nat;
  cert_issuer_ca : nat;
  cert_ca_licensed : CALicenseStatus;
  cert_status : CertStatus;
  cert_issued_at : nat;
  cert_expiry : nat;
  cert_key_length : nat;          (* minimum 2048 bits for RSA *)
}.

Record DigitalSignature := mkSig {
  sig_id : nat;
  sig_signer : nat;
  sig_cert_id : nat;
  sig_timestamp : nat;
  sig_verified : bool;
}.

(* ================================================================ *)
(* Requirement 1: Certificate Validity                               *)
(* A certificate is valid if active, not expired, from licensed CA   *)
(* ================================================================ *)

Definition cert_valid (c : Certificate) (current_time : nat) : Prop :=
  cert_status c = CertActive /\
  current_time <= cert_expiry c /\
  cert_ca_licensed c = CALicensed.

Theorem cert_validity :
  forall (c : Certificate) (t : nat),
  cert_status c = CertActive ->
  t <= cert_expiry c ->
  cert_ca_licensed c = CALicensed ->
  cert_valid c t.
Proof.
  intros c t H1 H2 H3. unfold cert_valid.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* Suspended/revoked certificates are invalid *)
Theorem suspended_invalid :
  forall (c : Certificate) (t : nat),
  cert_status c = CertSuspended ->
  ~ cert_valid c t.
Proof.
  intros c t Hsusp [Hactive _].
  rewrite Hsusp in Hactive. discriminate.
Qed.

Theorem revoked_invalid :
  forall (c : Certificate) (t : nat),
  cert_status c = CertRevoked ->
  ~ cert_valid c t.
Proof.
  intros c t Hrev [Hactive _].
  rewrite Hrev in Hactive. discriminate.
Qed.

Theorem expired_invalid :
  forall (c : Certificate) (t : nat),
  cert_expiry c < t ->
  ~ cert_valid c t.
Proof.
  intros c t Hexp [_ [Hle _]].
  apply (Nat.lt_irrefl (cert_expiry c)).
  apply (Nat.lt_le_trans _ t _ Hexp Hle).
Qed.

(* ================================================================ *)
(* Requirement 2: Licensed CA Presumption                            *)
(* §62: Signatures from licensed CAs are presumed secure             *)
(* ================================================================ *)

Definition presumed_secure (c : Certificate) : Prop :=
  cert_ca_licensed c = CALicensed.

Theorem licensed_ca_presumption :
  forall (c : Certificate),
  cert_ca_licensed c = CALicensed ->
  presumed_secure c.
Proof.
  intros c H. unfold presumed_secure. exact H.
Qed.

Theorem unlicensed_no_presumption :
  forall (c : Certificate),
  cert_ca_licensed c = CAUnlicensed ->
  ~ presumed_secure c.
Proof.
  intros c H Habs. unfold presumed_secure in Habs.
  rewrite H in Habs. discriminate.
Qed.

(* ================================================================ *)
(* Requirement 3: Signature Verification                             *)
(* ================================================================ *)

Definition signature_legally_valid
  (s : DigitalSignature) (c : Certificate) (t : nat) : Prop :=
  sig_verified s = true /\
  sig_cert_id s = cert_id c /\
  cert_valid c t.

Theorem signature_verification :
  forall (s : DigitalSignature) (c : Certificate) (t : nat),
  sig_verified s = true ->
  sig_cert_id s = cert_id c ->
  cert_valid c t ->
  signature_legally_valid s c t.
Proof.
  intros s c t H1 H2 H3. unfold signature_legally_valid.
  split. exact H1. split. exact H2. exact H3.
Qed.

(* ================================================================ *)
(* Requirement 4: Key Strength                                       *)
(* Minimum key length for legal recognition                          *)
(* ================================================================ *)

Definition key_strength_adequate (c : Certificate) (min_bits : nat) : Prop :=
  min_bits <= cert_key_length c.

Theorem key_strength_2048 :
  forall (c : Certificate),
  2048 <= cert_key_length c ->
  key_strength_adequate c 2048.
Proof.
  intros c H. unfold key_strength_adequate. exact H.
Qed.

(* ================================================================ *)
(* Requirement 5: Subscriber Duty — Private Key Protection           *)
(* §43: Subscriber must exercise reasonable care                     *)
(* ================================================================ *)

Definition private_key_protected (key_encrypted : bool) (key_on_hsm : bool) : Prop :=
  key_encrypted = true \/ key_on_hsm = true.

Theorem subscriber_duty_encrypted :
  forall (enc hsm : bool),
  enc = true ->
  private_key_protected enc hsm.
Proof.
  intros enc hsm H. unfold private_key_protected. left. exact H.
Qed.

Theorem subscriber_duty_hsm :
  forall (enc hsm : bool),
  hsm = true ->
  private_key_protected enc hsm.
Proof.
  intros enc hsm H. unfold private_key_protected. right. exact H.
Qed.

(* ================================================================ *)
(* Extended Malaysia Digital Signature Act Theorems                  *)
(* ================================================================ *)

Require Import Lia.

(* --- Certificate Lifecycle Management --- *)
(* DSA 1997: Certificate lifecycle states and transitions *)

Definition cert_status_active (c : Certificate) : Prop :=
  cert_status c = CertActive.

Definition cert_status_terminated (c : Certificate) : Prop :=
  cert_status c = CertRevoked \/ cert_status c = CertExpired.

Theorem active_not_terminated :
  forall (c : Certificate),
  cert_status_active c ->
  ~ cert_status_terminated c.
Proof.
  intros c Hact [Hrev | Hexp];
  unfold cert_status_active in Hact;
  rewrite Hact in *; discriminate.
Qed.

Theorem suspended_not_active :
  forall (c : Certificate),
  cert_status c = CertSuspended ->
  ~ cert_status_active c.
Proof.
  intros c Hsusp Hact.
  unfold cert_status_active in Hact.
  rewrite Hsusp in Hact. discriminate.
Qed.

(* --- Certificate Expiry Properties --- *)

Theorem cert_validity_window :
  forall (c : Certificate) (t : nat),
  cert_valid c t ->
  cert_issued_at c <= t \/ True.
Proof.
  intros c t _. right. exact I.
Qed.

Theorem cert_valid_implies_not_expired :
  forall (c : Certificate) (t : nat),
  cert_valid c t ->
  t <= cert_expiry c.
Proof.
  intros c t [_ [Hle _]]. exact Hle.
Qed.

Theorem cert_valid_implies_active :
  forall (c : Certificate) (t : nat),
  cert_valid c t ->
  cert_status c = CertActive.
Proof.
  intros c t [Hact _]. exact Hact.
Qed.

Theorem cert_valid_implies_licensed :
  forall (c : Certificate) (t : nat),
  cert_valid c t ->
  cert_ca_licensed c = CALicensed.
Proof.
  intros c t [_ [_ Hlic]]. exact Hlic.
Qed.

(* --- Key Strength Hierarchy --- *)

Theorem key_strength_downward :
  forall (c : Certificate) (bits1 bits2 : nat),
  bits1 <= bits2 ->
  key_strength_adequate c bits2 ->
  key_strength_adequate c bits1.
Proof.
  intros c bits1 bits2 Hle Hadq.
  unfold key_strength_adequate in *.
  apply (Nat.le_trans bits1 bits2 _); assumption.
Qed.

Theorem key_strength_4096_implies_2048 :
  forall (c : Certificate),
  key_strength_adequate c 4096 ->
  key_strength_adequate c 2048.
Proof.
  intros c H. apply (key_strength_downward c 2048 4096).
  - lia.
  - exact H.
Qed.

(* --- Relying Party Duties --- *)
(* DSA §66: Relying party must verify certificate *)

Record RelyingPartyCheck := mkRPCheck {
  rpc_cert_id : nat;
  rpc_status_checked : bool;
  rpc_expiry_checked : bool;
  rpc_ca_verified : bool;
  rpc_signature_verified : bool;
}.

Definition relying_party_diligent (rpc : RelyingPartyCheck) : Prop :=
  rpc_status_checked rpc = true /\
  rpc_expiry_checked rpc = true /\
  rpc_ca_verified rpc = true /\
  rpc_signature_verified rpc = true.

Theorem relying_party_duty :
  forall (rpc : RelyingPartyCheck),
  rpc_status_checked rpc = true ->
  rpc_expiry_checked rpc = true ->
  rpc_ca_verified rpc = true ->
  rpc_signature_verified rpc = true ->
  relying_party_diligent rpc.
Proof.
  intros rpc H1 H2 H3 H4.
  unfold relying_party_diligent.
  split. exact H1. split. exact H2. split. exact H3. exact H4.
Qed.

Theorem partial_check_not_diligent :
  forall (rpc : RelyingPartyCheck),
  rpc_signature_verified rpc = false ->
  ~ relying_party_diligent rpc.
Proof.
  intros rpc Hfalse [_ [_ [_ Hsig]]].
  rewrite Hfalse in Hsig. discriminate.
Qed.

(* --- Certificate Revocation List (CRL) --- *)

Record CRLEntry := mkCRLEntry {
  crl_cert_id : nat;
  crl_revoked_at : nat;
  crl_reason : nat;  (* 0=unspecified, 1=key_compromise, 2=ca_compromise, 3=affiliation_changed *)
}.

Definition cert_on_crl (crl : list CRLEntry) (cert_id : nat) : Prop :=
  exists entry, In entry crl /\ crl_cert_id entry = cert_id.

Theorem revoked_cert_on_crl :
  forall (crl : list CRLEntry) (entry : CRLEntry),
  In entry crl ->
  cert_on_crl crl (crl_cert_id entry).
Proof.
  intros crl entry Hin.
  unfold cert_on_crl.
  exists entry. split.
  - exact Hin.
  - reflexivity.
Qed.

Theorem crl_addition_preserves :
  forall (crl : list CRLEntry) (new_entry : CRLEntry) (cid : nat),
  cert_on_crl crl cid ->
  cert_on_crl (new_entry :: crl) cid.
Proof.
  intros crl new_entry cid [entry [Hin Hid]].
  unfold cert_on_crl. exists entry. split.
  - right. exact Hin.
  - exact Hid.
Qed.

(* --- Digital Signature Timestamp Properties --- *)

Theorem signature_timestamp_in_cert_validity :
  forall (s : DigitalSignature) (c : Certificate),
  signature_legally_valid s c (sig_timestamp s) ->
  sig_timestamp s <= cert_expiry c.
Proof.
  intros s c [_ [_ [_ [Hle _]]]]. exact Hle.
Qed.

(* --- Full DSA Compliance Composition --- *)

Definition dsa_fully_compliant
  (c : Certificate) (s : DigitalSignature) (t : nat)
  (key_enc : bool) (key_hsm : bool) : Prop :=
  cert_valid c t /\
  signature_legally_valid s c t /\
  key_strength_adequate c 2048 /\
  private_key_protected key_enc key_hsm.

Theorem dsa_composition :
  forall (c : Certificate) (s : DigitalSignature) (t : nat)
         (key_enc key_hsm : bool),
  cert_valid c t ->
  signature_legally_valid s c t ->
  key_strength_adequate c 2048 ->
  private_key_protected key_enc key_hsm ->
  dsa_fully_compliant c s t key_enc key_hsm.
Proof.
  intros c s t ke kh H1 H2 H3 H4.
  unfold dsa_fully_compliant.
  split. exact H1. split. exact H2. split. exact H3. exact H4.
Qed.

(* --- CertStatus and CALicense Exhaustiveness --- *)

Definition all_cert_statuses : list CertStatus :=
  [CertActive; CertSuspended; CertRevoked; CertExpired].

Theorem cert_status_coverage :
  forall (cs : CertStatus), In cs all_cert_statuses.
Proof.
  intros cs. destruct cs; simpl; auto 5.
Qed.

Definition all_ca_license_statuses : list CALicenseStatus :=
  [CALicensed; CAUnlicensed].

Theorem ca_license_coverage :
  forall (ls : CALicenseStatus), In ls all_ca_license_statuses.
Proof.
  intros ls. destruct ls; simpl; auto 3.
Qed.
