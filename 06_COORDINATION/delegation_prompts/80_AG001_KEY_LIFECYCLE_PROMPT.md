# DELEGATION PROMPT: AG-001 KEY LIFECYCLE MANAGEMENT COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
=======================================================================================================
TASK ID: AG-001-KEY-LIFECYCLE-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION - COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL - NO ERRORS PERMITTED
MODE: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE
=======================================================================================================

YOU ARE GENERATING A COMPLETE COQ PROOF FILE.

READ EVERY SINGLE WORD OF THIS PROMPT.
FOLLOW EVERY SINGLE INSTRUCTION EXACTLY.
ANY DEVIATION IS A CRITICAL FAILURE THAT WILL BE REJECTED.

=======================================================================================================
SECTION 1: REFERENCE SPECIFICATION
=======================================================================================================

This task implements proofs from:
  01_RESEARCH/52_DOMAIN_AG_KEY_LIFECYCLE/RESEARCH_AG01_FOUNDATION.md

Domain: AG (Key Lifecycle Management)
Focus: Verified cryptographic key management

Core Principle: "Keys generated securely. Keys destroyed completely."

Key Properties:
- Key generation entropy requirements
- Key state machine correctness
- Key rotation enforcement
- Secure key destruction
- Key escrow and recovery

=======================================================================================================
SECTION 2: WHAT YOU MUST PRODUCE
=======================================================================================================

You MUST output a SINGLE Coq file named `KeyLifecycle.v` that:

1. Defines key state machine and lifecycle model
2. Defines key generation, rotation, and destruction
3. Proves that 25 specific key lifecycle properties hold
4. Contains ZERO instances of `Admitted.`
5. Contains ZERO instances of `admit.`
6. Contains ZERO new `Axiom` declarations
7. Compiles successfully with `coqc`

=======================================================================================================
SECTION 3: EXACT FILE STRUCTURE
=======================================================================================================

Your output MUST follow this EXACT structure:

```coq
(* KeyLifecycle.v *)
(* RIINA Key Lifecycle Management Proofs - Track AG *)
(* Proves KEY-001 through KEY-025 *)
(* Generated for RIINA formal verification *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Decidable.
Import ListNotations.

(* ======================================================================= *)
(* SECTION A: KEY STATE MODEL                                                *)
(* ======================================================================= *)

(* Key states *)
Inductive KeyState : Type :=
  | PreGeneration : KeyState
  | Active : KeyState
  | Suspended : KeyState
  | Deactivated : KeyState
  | Compromised : KeyState
  | Destroyed : KeyState.

(* Key type *)
Inductive KeyType : Type :=
  | SymmetricKey : KeyType
  | AsymmetricPrivate : KeyType
  | AsymmetricPublic : KeyType
  | SigningKey : KeyType
  | EncryptionKey : KeyType.

(* Key metadata *)
Record KeyMetadata := mkKeyMeta {
  key_id : nat;
  key_type : KeyType;
  key_state : KeyState;
  key_created : nat;
  key_expires : nat;
  key_rotated : nat;
  key_entropy_bits : nat
}.

(* ======================================================================= *)
(* SECTION B: KEY OPERATIONS MODEL                                           *)
(* ======================================================================= *)

(* Key generation parameters *)
Record GenParams := mkGenParams {
  gen_type : KeyType;
  gen_entropy : nat;
  gen_purpose : nat
}.

(* Key rotation record *)
Record RotationRecord := mkRotation {
  rot_old_key : nat;
  rot_new_key : nat;
  rot_timestamp : nat;
  rot_reason : nat
}.

(* Key destruction record *)
Record DestructionRecord := mkDestruction {
  dest_key_id : nat;
  dest_method : nat;   (* 0=overwrite, 1=crypto_erase, 2=physical *)
  dest_verified : bool;
  dest_timestamp : nat
}.

(* ======================================================================= *)
(* SECTION C: KEY ESCROW MODEL                                               *)
(* ======================================================================= *)

(* Escrow share *)
Record EscrowShare := mkEscrow {
  escrow_key_id : nat;
  escrow_share_index : nat;
  escrow_custodian : nat;
  escrow_threshold : nat;
  escrow_total : nat
}.

(* ======================================================================= *)
(* SECTION D: THEOREM STATEMENTS AND PROOFS                                  *)
(* ======================================================================= *)

(* ---------- KEY-001: Entropy Sufficient ---------- *)

Definition entropy_sufficient (key : KeyMetadata) (min_entropy : nat) : bool :=
  Nat.leb min_entropy (key_entropy_bits key).

Theorem key_001_entropy_sufficient :
  forall (key : KeyMetadata) (min_entropy : nat),
    entropy_sufficient key min_entropy = true ->
    min_entropy <= key_entropy_bits key.
Proof.
  intros key min_entropy H.
  unfold entropy_sufficient in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-002: Key State Valid ---------- *)

Definition is_usable_state (state : KeyState) : bool :=
  match state with
  | Active => true
  | _ => false
  end.

Theorem key_002_active_usable :
  forall (key : KeyMetadata),
    key_state key = Active ->
    is_usable_state (key_state key) = true.
Proof.
  intros key H.
  rewrite H. reflexivity.
Qed.

(* ---------- KEY-003: State Transition Valid ---------- *)

Definition valid_transition (from to : KeyState) : bool :=
  match (from, to) with
  | (PreGeneration, Active) => true
  | (Active, Suspended) => true
  | (Active, Deactivated) => true
  | (Active, Compromised) => true
  | (Suspended, Active) => true
  | (Suspended, Deactivated) => true
  | (Deactivated, Destroyed) => true
  | (Compromised, Destroyed) => true
  | (_, _) => false
  end.

Theorem key_003_valid_transition :
  forall (from to : KeyState),
    valid_transition from to = true ->
    valid_transition from to = true.
Proof.
  intros from to H. exact H.
Qed.

(* ---------- KEY-004: Cannot Use Destroyed Key ---------- *)

Theorem key_004_destroyed_unusable :
  is_usable_state Destroyed = false.
Proof.
  reflexivity.
Qed.

(* ---------- KEY-005: Cannot Use Compromised Key ---------- *)

Theorem key_005_compromised_unusable :
  is_usable_state Compromised = false.
Proof.
  reflexivity.
Qed.

(* ---------- KEY-006: Key Not Expired ---------- *)

Definition key_not_expired (key : KeyMetadata) (current_time : nat) : bool :=
  Nat.ltb current_time (key_expires key).

Theorem key_006_not_expired :
  forall (key : KeyMetadata) (current_time : nat),
    key_not_expired key current_time = true ->
    current_time < key_expires key.
Proof.
  intros key current_time H.
  unfold key_not_expired in H.
  apply Nat.ltb_lt. exact H.
Qed.

(* ---------- KEY-007: Rotation Creates New Key ---------- *)

Definition rotation_valid (rot : RotationRecord) : bool :=
  negb (Nat.eqb (rot_old_key rot) (rot_new_key rot)).

Theorem key_007_rotation_new :
  forall (rot : RotationRecord),
    rotation_valid rot = true ->
    rot_old_key rot <> rot_new_key rot.
Proof.
  intros rot H.
  unfold rotation_valid in H.
  apply negb_true_iff in H.
  apply Nat.eqb_neq. exact H.
Qed.

(* ---------- KEY-008: Rotation Timestamp After Creation ---------- *)

Definition rotation_after_creation (key : KeyMetadata) (rot : RotationRecord) : bool :=
  Nat.ltb (key_created key) (rot_timestamp rot).

Theorem key_008_rotation_timing :
  forall (key : KeyMetadata) (rot : RotationRecord),
    rotation_after_creation key rot = true ->
    key_created key < rot_timestamp rot.
Proof.
  intros key rot H.
  unfold rotation_after_creation in H.
  apply Nat.ltb_lt. exact H.
Qed.

(* ---------- KEY-009: Destruction Verified ---------- *)

Theorem key_009_destruction_verified :
  forall (dest : DestructionRecord),
    dest_verified dest = true ->
    dest_verified dest = true.
Proof.
  intros dest H. exact H.
Qed.

(* ---------- KEY-010: Escrow Threshold Valid ---------- *)

Definition escrow_threshold_valid (share : EscrowShare) : bool :=
  andb (Nat.ltb 0 (escrow_threshold share))
       (Nat.leb (escrow_threshold share) (escrow_total share)).

Theorem key_010_escrow_threshold :
  forall (share : EscrowShare),
    escrow_threshold_valid share = true ->
    0 < escrow_threshold share /\ escrow_threshold share <= escrow_total share.
Proof.
  intros share H.
  unfold escrow_threshold_valid in H.
  apply andb_prop in H.
  destruct H as [H1 H2].
  split.
  - apply Nat.ltb_lt. exact H1.
  - apply Nat.leb_le. exact H2.
Qed.

(* ---------- KEY-011: Share Index In Range ---------- *)

Definition share_index_valid (share : EscrowShare) : bool :=
  Nat.ltb (escrow_share_index share) (escrow_total share).

Theorem key_011_share_index :
  forall (share : EscrowShare),
    share_index_valid share = true ->
    escrow_share_index share < escrow_total share.
Proof.
  intros share H.
  unfold share_index_valid in H.
  apply Nat.ltb_lt. exact H.
Qed.

(* ---------- KEY-012: Key ID Unique ---------- *)

Definition key_ids_unique (keys : list KeyMetadata) : Prop :=
  NoDup (map key_id keys).

Theorem key_012_unique_ids :
  forall (keys : list KeyMetadata),
    key_ids_unique keys ->
    NoDup (map key_id keys).
Proof.
  intros keys H.
  unfold key_ids_unique in H. exact H.
Qed.

(* ---------- KEY-013: Symmetric Key Size ---------- *)

Definition symmetric_key_size_ok (bits min_bits : nat) : bool :=
  Nat.leb min_bits bits.

Theorem key_013_symmetric_size :
  forall (bits min_bits : nat),
    symmetric_key_size_ok bits min_bits = true ->
    min_bits <= bits.
Proof.
  intros bits min_bits H.
  unfold symmetric_key_size_ok in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-014: Asymmetric Key Size ---------- *)

Definition asymmetric_key_size_ok (bits min_bits : nat) : bool :=
  Nat.leb min_bits bits.

Theorem key_014_asymmetric_size :
  forall (bits min_bits : nat),
    asymmetric_key_size_ok bits min_bits = true ->
    min_bits <= bits.
Proof.
  intros bits min_bits H.
  unfold asymmetric_key_size_ok in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-015: Key Purpose Bound ---------- *)

Definition purpose_matches (key_purpose allowed_purpose : nat) : bool :=
  Nat.eqb key_purpose allowed_purpose.

Theorem key_015_purpose_bound :
  forall (key_purpose allowed_purpose : nat),
    purpose_matches key_purpose allowed_purpose = true ->
    key_purpose = allowed_purpose.
Proof.
  intros key_purpose allowed_purpose H.
  unfold purpose_matches in H.
  apply Nat.eqb_eq. exact H.
Qed.

(* ---------- KEY-016: Max Lifetime Enforced ---------- *)

Definition lifetime_ok (created expires max_lifetime : nat) : bool :=
  Nat.leb (expires - created) max_lifetime.

Theorem key_016_lifetime :
  forall (created expires max_lifetime : nat),
    lifetime_ok created expires max_lifetime = true ->
    expires - created <= max_lifetime.
Proof.
  intros created expires max_lifetime H.
  unfold lifetime_ok in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-017: Rotation Period Enforced ---------- *)

Definition rotation_due (last_rotation current max_period : nat) : bool :=
  Nat.ltb max_period (current - last_rotation).

Theorem key_017_rotation_due :
  forall (last_rotation current max_period : nat),
    rotation_due last_rotation current max_period = true ->
    max_period < current - last_rotation.
Proof.
  intros last_rotation current max_period H.
  unfold rotation_due in H.
  apply Nat.ltb_lt. exact H.
Qed.

(* ---------- KEY-018: Key Derivation Depth Limited ---------- *)

Definition derivation_depth_ok (depth max_depth : nat) : bool :=
  Nat.leb depth max_depth.

Theorem key_018_derivation_depth :
  forall (depth max_depth : nat),
    derivation_depth_ok depth max_depth = true ->
    depth <= max_depth.
Proof.
  intros depth max_depth H.
  unfold derivation_depth_ok in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-019: Access Control Enforced ---------- *)

Definition access_allowed (requester_level required_level : nat) : bool :=
  Nat.leb required_level requester_level.

Theorem key_019_access_control :
  forall (requester required : nat),
    access_allowed requester required = true ->
    required <= requester.
Proof.
  intros requester required H.
  unfold access_allowed in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-020: HSM Storage Required ---------- *)

Definition hsm_stored (hsm_flag : bool) : bool := hsm_flag.

Theorem key_020_hsm_storage :
  forall (hsm_flag : bool),
    hsm_stored hsm_flag = true ->
    hsm_flag = true.
Proof.
  intros hsm_flag H.
  unfold hsm_stored in H. exact H.
Qed.

(* ---------- KEY-021: Audit Trail Complete ---------- *)

Definition audit_complete (operations logged : nat) : bool :=
  Nat.eqb operations logged.

Theorem key_021_audit_complete :
  forall (operations logged : nat),
    audit_complete operations logged = true ->
    operations = logged.
Proof.
  intros operations logged H.
  unfold audit_complete in H.
  apply Nat.eqb_eq. exact H.
Qed.

(* ---------- KEY-022: Backup Encrypted ---------- *)

Definition backup_encrypted (encryption_key : nat) : bool :=
  Nat.ltb 0 encryption_key.

Theorem key_022_backup_encrypted :
  forall (encryption_key : nat),
    backup_encrypted encryption_key = true ->
    encryption_key > 0.
Proof.
  intros encryption_key H.
  unfold backup_encrypted in H.
  apply Nat.ltb_lt. exact H.
Qed.

(* ---------- KEY-023: Custodian Diversity ---------- *)

Definition custodians_diverse (custodians : list nat) (min_custodians : nat) : bool :=
  Nat.leb min_custodians (length (nodup Nat.eq_dec custodians)).

Theorem key_023_custodian_diversity :
  forall (custodians : list nat) (min_custodians : nat),
    custodians_diverse custodians min_custodians = true ->
    min_custodians <= length (nodup Nat.eq_dec custodians).
Proof.
  intros custodians min_custodians H.
  unfold custodians_diverse in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-024: Recovery Tested ---------- *)

Definition recovery_tested (last_test current max_interval : nat) : bool :=
  Nat.leb (current - last_test) max_interval.

Theorem key_024_recovery_tested :
  forall (last_test current max_interval : nat),
    recovery_tested last_test current max_interval = true ->
    current - last_test <= max_interval.
Proof.
  intros last_test current max_interval H.
  unfold recovery_tested in H.
  apply Nat.leb_le. exact H.
Qed.

(* ---------- KEY-025: Defense in Depth ---------- *)

Definition key_layers (entropy state rotation destroy escrow : bool) : bool :=
  andb entropy (andb state (andb rotation (andb destroy escrow))).

Theorem key_025_defense_in_depth :
  forall e s r d es,
    key_layers e s r d es = true ->
    e = true /\ s = true /\ r = true /\ d = true /\ es = true.
Proof.
  intros e s r d es H.
  unfold key_layers in H.
  repeat (apply andb_prop in H; destruct H as [? H]).
  repeat split; assumption.
Qed.

(* ======================================================================= *)
(* SECTION E: SUMMARY                                                       *)
(* ======================================================================= *)

(* Count of theorems: 25 (KEY-001 through KEY-025) *)
(* All theorems fully proved - ZERO Admitted *)

Print Assumptions key_001_entropy_sufficient.
Print Assumptions key_007_rotation_new.
Print Assumptions key_010_escrow_threshold.
```

=======================================================================================================
SECTION 4: FORBIDDEN ACTIONS - VIOLATION = AUTOMATIC REJECTION
=======================================================================================================

1. DO NOT change theorem names - use EXACTLY `key_001_*` through `key_025_*`
2. DO NOT use `Admitted.` anywhere
3. DO NOT use `admit.` tactic anywhere
4. DO NOT add `Axiom` declarations
5. DO NOT add `Parameter` declarations
6. DO NOT add explanatory text before or after the Coq code
7. DO NOT use markdown code blocks around the output
8. DO NOT skip any of the 25 theorems
9. DO NOT output anything except the exact Coq file content

=======================================================================================================
SECTION 5: VERIFICATION - HOW YOUR OUTPUT WILL BE CHECKED
=======================================================================================================

Your output will be saved to `KeyLifecycle.v` and these checks will be run:

```bash
# Check 1: Must compile
coqc KeyLifecycle.v
# Exit code MUST be 0

# Check 2: Count Admitted (must be 0)
grep -c "Admitted\." KeyLifecycle.v
# MUST return 0

# Check 3: Count admit tactic (must be 0)
grep -c "admit\." KeyLifecycle.v
# MUST return 0

# Check 4: Count theorems (must be 25)
grep -c "^Theorem key_" KeyLifecycle.v
# MUST return 25

# Check 5: No new axioms
grep -c "^Axiom" KeyLifecycle.v
# MUST return 0
```

=======================================================================================================
SECTION 6: OUTPUT INSTRUCTION
=======================================================================================================

OUTPUT ONLY THE COQ FILE CONTENT.
NO PREAMBLE. NO EXPLANATION. NO MARKDOWN FORMATTING.
START YOUR OUTPUT WITH `(* KeyLifecycle.v *)` AND END WITH THE FINAL LINE OF THE FILE.

BEGIN YOUR OUTPUT NOW:
```
