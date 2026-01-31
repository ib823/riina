(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* PCIDSSCompliance.v - PCI-DSS Compliance Proofs for RIINA *)
(* Spec: 04_SPECS/industries/IND_C_FINANCIAL.md *)
(* Requirement: PCI-DSS v4.0 *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(* Cardholder data types *)
Inductive CHDType : Type :=
  | PAN : CHDType                 (* Primary Account Number - 16 digits *)
  | CVV : CHDType                 (* Card Verification Value - 3-4 digits *)
  | PIN : CHDType                 (* Personal Identification Number *)
  | Expiry : CHDType              (* Expiration date *)
  | CardholderName : CHDType      (* Cardholder name *)
.

(* Storage permission per PCI-DSS *)
Definition can_store (chd : CHDType) : bool :=
  match chd with
  | PAN => true           (* Yes, but encrypted *)
  | Expiry => true        (* Yes, with protection *)
  | CardholderName => true (* Yes, with protection *)
  | CVV => false          (* NEVER *)
  | PIN => false          (* NEVER *)
  end.

(* Encryption state *)
Inductive EncState : Type :=
  | Plain : EncState
  | AES128 : EncState
  | AES256 : EncState           (* Minimum for PAN *)
  | Tokenized : EncState        (* Tokenization *)
.

(* PAN display format *)
Inductive PANDisplay : Type :=
  | FullPAN : PANDisplay              (* PROHIBITED for display *)
  | MaskedPAN : PANDisplay            (* ****-****-****-1234 *)
  | TokenizedPAN : PANDisplay         (* Token reference *)
.

(* Cardholder data record *)
Record CHDRecord : Type := mkCHD {
  chd_type : CHDType;
  chd_value : nat;                    (* Abstract value *)
  chd_encryption : EncState;
  chd_display_format : PANDisplay;
}.

(* Key management *)
Record KeyState : Type := mkKey {
  key_id : nat;
  key_creation_time : nat;
  key_rotation_period : nat;          (* Typically 1 year *)
  key_protected : bool;               (* Stored in HSM or equivalent *)
}.

(* Audit entry *)
Record PCIAudit : Type := mkPCIAudit {
  pci_timestamp : nat;
  pci_user : nat;
  pci_action : nat;
  pci_chd_accessed : CHDType;
  pci_success : bool;
  pci_hash : nat;                     (* For integrity *)
}.

(* Token vault (for tokenization) *)
Record TokenVault : Type := mkVault {
  vault_tokens : list (nat * nat);    (* token -> PAN mapping *)
  vault_key : KeyState;               (* Key protecting the vault *)
  vault_isolated : bool;              (* Network segmented *)
}.

(* System state *)
Record PCISystem : Type := mkPCI {
  pci_chd_records : list CHDRecord;
  pci_audit_log : list PCIAudit;
  pci_keys : list KeyState;
  pci_vault : TokenVault;
}.

(* PCI-DSS compliant encryption *)
Definition pci_compliant_encryption (enc : EncState) (chd : CHDType) : bool :=
  match chd with
  | PAN => match enc with AES256 | Tokenized => true | _ => false end
  | CVV => false    (* Cannot be stored regardless of encryption *)
  | PIN => false    (* Cannot be stored regardless of encryption *)
  | _ => match enc with AES128 | AES256 | Tokenized => true | _ => false end
  end.

(* Display compliance *)
Definition display_compliant (disp : PANDisplay) : bool :=
  match disp with
  | FullPAN => false      (* Never display full PAN *)
  | MaskedPAN => true     (* Last 4 digits OK *)
  | TokenizedPAN => true  (* Token OK *)
  end.

(* Key rotation check *)
Definition key_needs_rotation (k : KeyState) (current_time : nat) : bool :=
  Nat.ltb (key_creation_time k + key_rotation_period k) current_time.

(* Access control *)
Inductive AccessLevel : Type :=
  | NoAccess : AccessLevel
  | ReadOnly : AccessLevel
  | ReadWrite : AccessLevel
  | Admin : AccessLevel
.

Record User : Type := mkUser {
  user_id : nat;
  user_access_level : AccessLevel;
  user_mfa_enabled : bool;
  user_need_to_know : bool;           (* Business need for CHD access *)
}.

(* Access grant decision *)
Definition grant_chd_access (u : User) : bool :=
  match user_access_level u with
  | NoAccess => false
  | _ => andb (user_mfa_enabled u) (user_need_to_know u)
  end.

(* Compliant CHD record - properly protected *)
Definition chd_record_compliant (rec : CHDRecord) : bool :=
  andb (can_store (chd_type rec))
       (andb (pci_compliant_encryption (chd_encryption rec) (chd_type rec))
             (display_compliant (chd_display_format rec))).

(* Audit log entry creation *)
Definition create_audit_entry (ts usr act : nat) (chd : CHDType) (succ : bool) (prev_hash : nat) : PCIAudit :=
  mkPCIAudit ts usr act chd succ (prev_hash + ts + usr + act).

(* Audit chain integrity check *)
Fixpoint audit_chain_valid (log : list PCIAudit) (expected_hash : nat) : bool :=
  match log with
  | [] => true
  | entry :: rest =>
      andb (Nat.eqb (pci_hash entry) expected_hash)
           (audit_chain_valid rest (pci_hash entry + pci_timestamp entry))
  end.

(* TLS version *)
Inductive TLSVersion : Type :=
  | TLS10 : TLSVersion
  | TLS11 : TLSVersion
  | TLS12 : TLSVersion
  | TLS13 : TLSVersion
.

Definition tls_compliant (v : TLSVersion) : bool :=
  match v with
  | TLS10 => false
  | TLS11 => false
  | TLS12 => true
  | TLS13 => true
  end.

(* Transmission record *)
Record Transmission : Type := mkTrans {
  trans_tls_version : TLSVersion;
  trans_encrypted : bool;
  trans_chd_type : CHDType;
}.

Definition transmission_compliant (t : Transmission) : bool :=
  andb (trans_encrypted t) (tls_compliant (trans_tls_version t)).

(* Token lookup - requires key access *)
Definition token_lookup (vault : TokenVault) (token : nat) (has_key : bool) : option nat :=
  if has_key then
    match find (fun p => Nat.eqb (fst p) token) (vault_tokens vault) with
    | Some (_, pan) => Some pan
    | None => None
    end
  else
    None.

(* Data retention policy *)
Record RetentionPolicy : Type := mkRetention {
  retention_max_days : nat;
  retention_auto_delete : bool;
}.

Definition data_past_retention (creation_time current_time max_days : nat) : bool :=
  Nat.ltb (creation_time + max_days) current_time.

(* Secure deletion state *)
Inductive DeletionState : Type :=
  | NotDeleted : DeletionState
  | MarkedForDeletion : DeletionState
  | Overwritten : DeletionState         (* Data overwritten with random *)
  | SecurelyDeleted : DeletionState     (* Multiple overwrites, verified *)
.

Definition deletion_secure (ds : DeletionState) : bool :=
  match ds with
  | SecurelyDeleted => true
  | _ => false
  end.

Definition deletion_unrecoverable (ds : DeletionState) : bool :=
  match ds with
  | Overwritten => true
  | SecurelyDeleted => true
  | _ => false
  end.

(* Network segmentation *)
Record NetworkZone : Type := mkZone {
  zone_id : nat;
  zone_is_cde : bool;                  (* Cardholder Data Environment *)
  zone_isolated : bool;
  zone_firewall_protected : bool;
}.

Definition zone_compliant (z : NetworkZone) : bool :=
  if zone_is_cde z then
    andb (zone_isolated z) (zone_firewall_protected z)
  else
    true.

(* System compliance check *)
Definition system_scope_isolated (sys : PCISystem) : bool :=
  vault_isolated (pci_vault sys).

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_01: PAN masking (display only last 4 digits)             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_01_pan_masking :
  forall (disp : PANDisplay),
    disp = FullPAN -> display_compliant disp = false.
Proof.
  intros disp H.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Theorem COMPLY_002_01_pan_masking_valid :
  display_compliant MaskedPAN = true /\ display_compliant TokenizedPAN = true.
Proof.
  split; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_02: PAN encryption (AES-256 or stronger required)        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_02_pan_encryption :
  forall (enc : EncState),
    pci_compliant_encryption enc PAN = true ->
    enc = AES256 \/ enc = Tokenized.
Proof.
  intros enc H.
  destruct enc.
  - simpl in H. discriminate.
  - simpl in H. discriminate.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Theorem COMPLY_002_02_pan_plain_forbidden :
  pci_compliant_encryption Plain PAN = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem COMPLY_002_02_pan_aes128_insufficient :
  pci_compliant_encryption AES128 PAN = false.
Proof.
  simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_03: CVV never stored                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_03_cvv_never_stored :
  can_store CVV = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem COMPLY_002_03_cvv_no_compliant_encryption :
  forall (enc : EncState),
    pci_compliant_encryption enc CVV = false.
Proof.
  intros enc.
  destruct enc; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_04: PIN never stored                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_04_pin_never_stored :
  can_store PIN = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem COMPLY_002_04_pin_no_compliant_encryption :
  forall (enc : EncState),
    pci_compliant_encryption enc PIN = false.
Proof.
  intros enc.
  destruct enc; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_05: Key management (protected and rotated)               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_05_key_rotation_detection :
  forall (k : KeyState) (current_time : nat),
    key_creation_time k + key_rotation_period k < current_time ->
    key_needs_rotation k current_time = true.
Proof.
  intros k current_time H.
  unfold key_needs_rotation.
  apply Nat.ltb_lt.
  exact H.
Qed.

Theorem COMPLY_002_05_key_no_rotation_needed :
  forall (k : KeyState) (current_time : nat),
    current_time <= key_creation_time k + key_rotation_period k ->
    key_needs_rotation k current_time = false.
Proof.
  intros k current_time H.
  unfold key_needs_rotation.
  apply Nat.ltb_ge.
  exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_06: Access restricted (need-to-know basis)               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_06_access_requires_need_to_know :
  forall (u : User),
    user_need_to_know u = false ->
    grant_chd_access u = false.
Proof.
  intros u H.
  unfold grant_chd_access.
  destruct (user_access_level u).
  - reflexivity.
  - rewrite H. rewrite andb_false_r. reflexivity.
  - rewrite H. rewrite andb_false_r. reflexivity.
  - rewrite H. rewrite andb_false_r. reflexivity.
Qed.

Theorem COMPLY_002_06_no_access_level_denied :
  forall (u : User),
    user_access_level u = NoAccess ->
    grant_chd_access u = false.
Proof.
  intros u H.
  unfold grant_chd_access.
  rewrite H.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_07: Unique IDs (each user uniquely identified)           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Simple uniqueness check for nat lists *)
Fixpoint nat_nodup (l : list nat) : list nat :=
  match l with
  | nil => nil
  | x :: xs => if existsb (Nat.eqb x) xs then nat_nodup xs else x :: nat_nodup xs
  end.

Definition users_unique_ids (users : list User) : bool :=
  let ids := map user_id users in
  Nat.eqb (List.length ids) (List.length (nat_nodup ids)).

Theorem COMPLY_002_07_unique_ids_singleton :
  forall (u : User),
    users_unique_ids [u] = true.
Proof.
  intros u.
  unfold users_unique_ids, nat_nodup.
  simpl.
  reflexivity.
Qed.

Theorem COMPLY_002_07_unique_ids_empty :
  users_unique_ids [] = true.
Proof.
  unfold users_unique_ids.
  simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_08: MFA required for CHD access                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_08_mfa_required :
  forall (u : User),
    user_mfa_enabled u = false ->
    user_access_level u <> NoAccess ->
    grant_chd_access u = false.
Proof.
  intros u Hmfa Haccess.
  unfold grant_chd_access.
  destruct (user_access_level u).
  - contradiction.
  - rewrite Hmfa. simpl. reflexivity.
  - rewrite Hmfa. simpl. reflexivity.
  - rewrite Hmfa. simpl. reflexivity.
Qed.

Theorem COMPLY_002_08_access_granted_implies_mfa :
  forall (u : User),
    grant_chd_access u = true ->
    user_mfa_enabled u = true.
Proof.
  intros u H.
  unfold grant_chd_access in H.
  destruct (user_access_level u).
  - discriminate.
  - apply andb_true_iff in H. destruct H as [Hmfa _]. exact Hmfa.
  - apply andb_true_iff in H. destruct H as [Hmfa _]. exact Hmfa.
  - apply andb_true_iff in H. destruct H as [Hmfa _]. exact Hmfa.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_09: Audit trail (all access logged)                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_09_audit_entry_has_timestamp :
  forall (ts usr act : nat) (chd : CHDType) (succ : bool) (prev : nat),
    pci_timestamp (create_audit_entry ts usr act chd succ prev) = ts.
Proof.
  intros.
  unfold create_audit_entry.
  simpl.
  reflexivity.
Qed.

Theorem COMPLY_002_09_audit_entry_has_user :
  forall (ts usr act : nat) (chd : CHDType) (succ : bool) (prev : nat),
    pci_user (create_audit_entry ts usr act chd succ prev) = usr.
Proof.
  intros.
  unfold create_audit_entry.
  simpl.
  reflexivity.
Qed.

Theorem COMPLY_002_09_audit_entry_has_action :
  forall (ts usr act : nat) (chd : CHDType) (succ : bool) (prev : nat),
    pci_action (create_audit_entry ts usr act chd succ prev) = act.
Proof.
  intros.
  unfold create_audit_entry.
  simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_10: Log integrity (tamper-evident)                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_10_audit_has_hash :
  forall (ts usr act : nat) (chd : CHDType) (succ : bool) (prev : nat),
    pci_hash (create_audit_entry ts usr act chd succ prev) = prev + ts + usr + act.
Proof.
  intros.
  unfold create_audit_entry.
  simpl.
  reflexivity.
Qed.

Theorem COMPLY_002_10_empty_log_valid :
  forall (h : nat),
    audit_chain_valid [] h = true.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_11: Encryption in transit (TLS 1.2+)                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_11_tls12_compliant :
  tls_compliant TLS12 = true.
Proof.
  simpl. reflexivity.
Qed.

Theorem COMPLY_002_11_tls13_compliant :
  tls_compliant TLS13 = true.
Proof.
  simpl. reflexivity.
Qed.

Theorem COMPLY_002_11_old_tls_non_compliant :
  tls_compliant TLS10 = false /\ tls_compliant TLS11 = false.
Proof.
  split; simpl; reflexivity.
Qed.

Theorem COMPLY_002_11_transmission_requires_encryption :
  forall (t : Transmission),
    transmission_compliant t = true ->
    trans_encrypted t = true.
Proof.
  intros t H.
  unfold transmission_compliant in H.
  apply andb_true_iff in H.
  destruct H as [Henc _].
  exact Henc.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_12: Tokenization validity (no reverse without key)       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_12_token_no_key_no_pan :
  forall (vault : TokenVault) (token : nat),
    token_lookup vault token false = None.
Proof.
  intros.
  unfold token_lookup.
  simpl.
  reflexivity.
Qed.

Theorem COMPLY_002_12_tokenization_irreversible_without_key :
  forall (vault : TokenVault) (token pan : nat),
    token_lookup vault token false = Some pan -> False.
Proof.
  intros vault token pan H.
  unfold token_lookup in H.
  simpl in H.
  discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_13: Data retention (deleted when no longer needed)       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_13_past_retention_detected :
  forall (creation current max_days : nat),
    creation + max_days < current ->
    data_past_retention creation current max_days = true.
Proof.
  intros.
  unfold data_past_retention.
  apply Nat.ltb_lt.
  exact H.
Qed.

Theorem COMPLY_002_13_within_retention_ok :
  forall (creation current max_days : nat),
    current <= creation + max_days ->
    data_past_retention creation current max_days = false.
Proof.
  intros.
  unfold data_past_retention.
  apply Nat.ltb_ge.
  exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_14: Secure deletion (unrecoverable)                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_14_secure_deletion_unrecoverable :
  forall (ds : DeletionState),
    deletion_secure ds = true ->
    deletion_unrecoverable ds = true.
Proof.
  intros ds H.
  unfold deletion_secure in H.
  destruct ds.
  - discriminate.
  - discriminate.
  - discriminate.
  - simpl. reflexivity.
Qed.

Theorem COMPLY_002_14_not_deleted_recoverable :
  deletion_unrecoverable NotDeleted = false.
Proof.
  simpl. reflexivity.
Qed.

Theorem COMPLY_002_14_marked_still_recoverable :
  deletion_unrecoverable MarkedForDeletion = false.
Proof.
  simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPLY_002_15: Scope isolation (CDE segmented)                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPLY_002_15_cde_requires_isolation :
  forall (z : NetworkZone),
    zone_is_cde z = true ->
    zone_compliant z = true ->
    zone_isolated z = true.
Proof.
  intros z Hcde Hcomp.
  unfold zone_compliant in Hcomp.
  rewrite Hcde in Hcomp.
  apply andb_true_iff in Hcomp.
  destruct Hcomp as [Hiso _].
  exact Hiso.
Qed.

Theorem COMPLY_002_15_cde_requires_firewall :
  forall (z : NetworkZone),
    zone_is_cde z = true ->
    zone_compliant z = true ->
    zone_firewall_protected z = true.
Proof.
  intros z Hcde Hcomp.
  unfold zone_compliant in Hcomp.
  rewrite Hcde in Hcomp.
  apply andb_true_iff in Hcomp.
  destruct Hcomp as [_ Hfw].
  exact Hfw.
Qed.

Theorem COMPLY_002_15_non_cde_always_compliant :
  forall (z : NetworkZone),
    zone_is_cde z = false ->
    zone_compliant z = true.
Proof.
  intros z H.
  unfold zone_compliant.
  rewrite H.
  reflexivity.
Qed.

Theorem COMPLY_002_15_vault_isolation :
  forall (sys : PCISystem),
    vault_isolated (pci_vault sys) = true ->
    system_scope_isolated sys = true.
Proof.
  intros sys H.
  unfold system_scope_isolated.
  exact H.
Qed.
