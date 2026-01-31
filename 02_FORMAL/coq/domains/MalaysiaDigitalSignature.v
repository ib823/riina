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
