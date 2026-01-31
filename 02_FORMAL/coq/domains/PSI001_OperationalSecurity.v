(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* PSI001_OperationalSecurity.v - RIINA Operational Security *)
(* Spec: 01_RESEARCH/31_DOMAIN_PSI_OPERATIONAL_SECURITY/RESEARCH_PSI01_FOUNDATION.md *)
(* Layer: Operational Security & Insider Threat Mitigation *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(** ===============================================================================
    SECTION 1: SHAMIR SECRET SHARING
    =============================================================================== *)

(* Finite field arithmetic modulo a prime p *)
(* We use nat with modular operations for simplicity *)

Definition field_add (a b p : nat) : nat := (a + b) mod p.
Definition field_mul (a b p : nat) : nat := (a * b) mod p.
Definition field_sub (a b p : nat) : nat := (a + p - b) mod p.

(* A share is (x, y) where y = f(x) for secret polynomial f *)
Record Share : Type := mkShare {
  share_x : nat;
  share_y : nat
}.

(* Polynomial evaluation: f(x) = a0 + a1*x + a2*x^2 + ... mod p *)
Fixpoint poly_eval (coeffs : list nat) (x p : nat) : nat :=
  match coeffs with
  | [] => 0
  | a :: rest => field_add a (field_mul x (poly_eval rest x p) p) p
  end.

(* Generate shares from polynomial *)
Definition generate_shares (coeffs : list nat) (n p : nat) : list Share :=
  map (fun i => {| share_x := S i; share_y := poly_eval coeffs (S i) p |})
      (seq 0 n).

(* The secret is the constant term (f(0)) *)
Definition secret_from_poly (coeffs : list nat) : nat :=
  match coeffs with
  | [] => 0
  | a0 :: _ => a0
  end.

(* Threshold k: polynomial degree is k-1, need k points to reconstruct *)
Definition threshold_met (shares : list Share) (k : nat) : bool :=
  k <=? length shares.

(** ===============================================================================
    SECTION 2: N-OF-M THRESHOLD OPERATIONS
    =============================================================================== *)

Record ThresholdPolicy : Type := mkThresholdPolicy {
  tp_n : nat;    (* required approvals *)
  tp_m : nat;    (* total authorized parties *)
  tp_approvals : list nat  (* party IDs that approved *)
}.

Definition tp_approved (pol : ThresholdPolicy) : bool :=
  tp_n pol <=? length (tp_approvals pol).

Definition tp_add_approval (pol : ThresholdPolicy) (party : nat) : ThresholdPolicy :=
  if existsb (Nat.eqb party) (tp_approvals pol) then pol
  else {| tp_n := tp_n pol;
          tp_m := tp_m pol;
          tp_approvals := party :: tp_approvals pol |}.

Definition tp_valid (pol : ThresholdPolicy) : bool :=
  (tp_n pol <=? tp_m pol) && (1 <=? tp_n pol).

(** ===============================================================================
    SECTION 3: DURESS DETECTION
    =============================================================================== *)

Inductive AuthMode : Type :=
  | NormalAuth : nat -> AuthMode      (* normal password/key *)
  | DuressAuth : nat -> AuthMode      (* duress code *)
  | EmergencyAuth : nat -> AuthMode.  (* emergency override *)

Record DuressResponse : Type := mkDuressResponse {
  dr_silent_alert : bool;
  dr_fake_access : bool;
  dr_real_lockdown : bool;
  dr_audit_logged : bool
}.

Definition handle_auth (mode : AuthMode) : DuressResponse :=
  match mode with
  | NormalAuth _ => {| dr_silent_alert := false;
                       dr_fake_access := false;
                       dr_real_lockdown := false;
                       dr_audit_logged := true |}
  | DuressAuth _ => {| dr_silent_alert := true;
                        dr_fake_access := true;
                        dr_real_lockdown := true;
                        dr_audit_logged := true |}
  | EmergencyAuth _ => {| dr_silent_alert := true;
                           dr_fake_access := false;
                           dr_real_lockdown := true;
                           dr_audit_logged := true |}
  end.

(** ===============================================================================
    SECTION 4: DEAD MAN'S SWITCH
    =============================================================================== *)

Record DeadManSwitch : Type := mkDMS {
  dms_last_checkin : nat;
  dms_timeout : nat;
  dms_triggered : bool;
  dms_recovery_action : nat  (* abstract action ID *)
}.

Definition dms_check (dms : DeadManSwitch) (now : nat) : DeadManSwitch :=
  if dms_timeout dms + dms_last_checkin dms <? now then
    {| dms_last_checkin := dms_last_checkin dms;
       dms_timeout := dms_timeout dms;
       dms_triggered := true;
       dms_recovery_action := dms_recovery_action dms |}
  else dms.

Definition dms_checkin (dms : DeadManSwitch) (now : nat) : DeadManSwitch :=
  {| dms_last_checkin := now;
     dms_timeout := dms_timeout dms;
     dms_triggered := false;
     dms_recovery_action := dms_recovery_action dms |}.

(** ===============================================================================
    SECTION 5: INSIDER THREAT MODEL
    =============================================================================== *)

Record InsiderBudget : Type := mkInsiderBudget {
  ib_max_bytes : nat;       (* max data export per window *)
  ib_max_queries : nat;     (* max queries per window *)
  ib_bytes_used : nat;
  ib_queries_used : nat;
  ib_window_start : nat
}.

Definition ib_can_query (budget : InsiderBudget) (bytes : nat) : bool :=
  (budget.(ib_bytes_used) + bytes <=? budget.(ib_max_bytes)) &&
  (budget.(ib_queries_used) <? budget.(ib_max_queries)).

Definition ib_record_query (budget : InsiderBudget) (bytes : nat) : InsiderBudget :=
  {| ib_max_bytes := budget.(ib_max_bytes);
     ib_max_queries := budget.(ib_max_queries);
     ib_bytes_used := budget.(ib_bytes_used) + bytes;
     ib_queries_used := S (budget.(ib_queries_used));
     ib_window_start := budget.(ib_window_start) |}.

(* Audit log for insider actions *)
Record AuditEntry : Type := mkAuditEntry {
  ae_timestamp : nat;
  ae_actor : nat;
  ae_action : nat;
  ae_data_hash : nat;
  ae_prev_hash : nat
}.

Definition AuditLog := list AuditEntry.

Definition audit_log_append (log : AuditLog) (entry : AuditEntry) : AuditLog :=
  entry :: log.

Definition audit_chain_valid (log : AuditLog) : bool :=
  match log with
  | [] => true
  | [_] => true
  | e1 :: ((e2 :: _) as _) => Nat.eqb (ae_prev_hash e1) (ae_data_hash e2)
  end.

(** ===============================================================================
    SECTION 6: HARDWARE DIVERSITY
    =============================================================================== *)

Record Platform : Type := mkPlatform {
  plat_vendor : nat;
  plat_arch : nat;
  plat_firmware_hash : nat
}.

Definition platforms_independent (p1 p2 : Platform) : bool :=
  negb (Nat.eqb (plat_vendor p1) (plat_vendor p2)) ||
  negb (Nat.eqb (plat_arch p1) (plat_arch p2)).

(* N-version execution: run same program on N independent platforms *)
Definition nversion_agree (results : list nat) : bool :=
  match results with
  | [] => true
  | r :: rest => forallb (Nat.eqb r) rest
  end.

Definition nversion_majority (results : list nat) : option nat :=
  match results with
  | [] => None
  | r :: _ => Some r  (* simplified: returns first *)
  end.

(** ===============================================================================
    SECTION 7: TIME-LOCKED OPERATIONS
    =============================================================================== *)

Record TimeLock : Type := mkTimeLock {
  tl_operation : nat;
  tl_submit_time : nat;
  tl_execute_time : nat;    (* earliest execution *)
  tl_cancelled : bool
}.

Definition tl_can_execute (tl : TimeLock) (now : nat) : bool :=
  (tl_execute_time tl <=? now) && negb (tl_cancelled tl).

Definition tl_can_cancel (tl : TimeLock) (now : nat) : bool :=
  now <? tl_execute_time tl.

Definition tl_cancel (tl : TimeLock) : TimeLock :=
  {| tl_operation := tl_operation tl;
     tl_submit_time := tl_submit_time tl;
     tl_execute_time := tl_execute_time tl;
     tl_cancelled := true |}.

(** ===============================================================================
    PROOFS: SHAMIR SECRET SHARING (8 theorems)
    =============================================================================== *)

Theorem PSI_001_01_poly_eval_zero : forall coeffs p,
  p > 0 ->
  poly_eval coeffs 0 p = match coeffs with [] => 0 | a :: _ => a mod p end.
Proof.
  intros coeffs p Hp. destruct coeffs as [|a rest].
  - simpl. reflexivity.
  - simpl. unfold field_add, field_mul. simpl.
    rewrite Nat.mod_0_l; [| lia]. rewrite Nat.add_0_r.
    reflexivity.
Qed.

Theorem PSI_001_02_generate_shares_length : forall coeffs n p,
  length (generate_shares coeffs n p) = n.
Proof.
  intros. unfold generate_shares. rewrite map_length. apply seq_length.
Qed.

Theorem PSI_001_03_threshold_monotone : forall shares k1 k2,
  k1 <= k2 ->
  threshold_met shares k2 = true ->
  threshold_met shares k1 = true.
Proof.
  intros shares k1 k2 Hle H. unfold threshold_met in *.
  apply Nat.leb_le in H. apply Nat.leb_le. lia.
Qed.

Theorem PSI_001_04_insufficient_shares : forall shares k,
  length shares < k ->
  threshold_met shares k = false.
Proof.
  intros shares k H. unfold threshold_met.
  apply Nat.leb_gt. exact H.
Qed.

Theorem PSI_001_05_share_x_positive : forall coeffs n p i,
  i < n ->
  share_x (nth i (generate_shares coeffs n p) {| share_x := 0; share_y := 0 |}) > 0.
Proof.
  intros coeffs n p i Hi. unfold generate_shares.
  rewrite nth_map_seq; [simpl; lia | exact Hi].
Qed.

Theorem PSI_001_06_shares_distinct_x : forall coeffs n p i j,
  i < n -> j < n -> i <> j ->
  share_x (nth i (generate_shares coeffs n p) {| share_x := 0; share_y := 0 |}) <>
  share_x (nth j (generate_shares coeffs n p) {| share_x := 0; share_y := 0 |}).
Proof.
  intros coeffs n p i j Hi Hj Hneq. unfold generate_shares.
  rewrite nth_map_seq; [| exact Hi].
  rewrite nth_map_seq; [| exact Hj].
  simpl. lia.
Qed.

Theorem PSI_001_07_secret_is_constant_term : forall a0 rest,
  secret_from_poly (a0 :: rest) = a0.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_001_08_empty_poly_zero_secret :
  secret_from_poly [] = 0.
Proof.
  simpl. reflexivity.
Qed.

(** ===============================================================================
    PROOFS: THRESHOLD OPERATIONS (6 theorems)
    =============================================================================== *)

Theorem PSI_002_01_single_approval_insufficient : forall pol party,
  tp_n pol > 1 ->
  tp_approvals pol = [] ->
  tp_approved (tp_add_approval pol party) = false.
Proof.
  intros pol party Hn Hempty. unfold tp_add_approval.
  rewrite Hempty. simpl. unfold tp_approved. simpl.
  apply Nat.leb_gt. lia.
Qed.

Theorem PSI_002_02_approval_monotone : forall pol party,
  tp_approved pol = true ->
  tp_approved (tp_add_approval pol party) = true.
Proof.
  intros pol party H. unfold tp_add_approval.
  destruct (existsb (Nat.eqb party) (tp_approvals pol)) eqn:E; [exact H |].
  unfold tp_approved in *. simpl.
  apply Nat.leb_le in H. apply Nat.leb_le. simpl. lia.
Qed.

Theorem PSI_002_03_duplicate_approval_noop : forall pol party,
  existsb (Nat.eqb party) (tp_approvals pol) = true ->
  tp_add_approval pol party = pol.
Proof.
  intros pol party H. unfold tp_add_approval. rewrite H.
  destruct pol. reflexivity.
Qed.

Theorem PSI_002_04_valid_policy_n_le_m : forall pol,
  tp_valid pol = true ->
  tp_n pol <= tp_m pol.
Proof.
  intros pol H. unfold tp_valid in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

Theorem PSI_002_05_valid_policy_n_positive : forall pol,
  tp_valid pol = true ->
  tp_n pol >= 1.
Proof.
  intros pol H. unfold tp_valid in H.
  apply andb_true_iff in H. destruct H as [_ H].
  apply Nat.leb_le in H. lia.
Qed.

Theorem PSI_002_06_approval_count_increases : forall pol party,
  existsb (Nat.eqb party) (tp_approvals pol) = false ->
  length (tp_approvals (tp_add_approval pol party)) = S (length (tp_approvals pol)).
Proof.
  intros pol party H. unfold tp_add_approval. rewrite H. simpl. reflexivity.
Qed.

(** ===============================================================================
    PROOFS: DURESS DETECTION (6 theorems)
    =============================================================================== *)

Theorem PSI_003_01_duress_triggers_alert : forall code,
  dr_silent_alert (handle_auth (DuressAuth code)) = true.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_003_02_duress_provides_fake : forall code,
  dr_fake_access (handle_auth (DuressAuth code)) = true.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_003_03_duress_locks_down : forall code,
  dr_real_lockdown (handle_auth (DuressAuth code)) = true.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_003_04_all_auth_audited : forall mode,
  dr_audit_logged (handle_auth mode) = true.
Proof.
  intros mode. destruct mode; simpl; reflexivity.
Qed.

Theorem PSI_003_05_normal_no_fake : forall key,
  dr_fake_access (handle_auth (NormalAuth key)) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_003_06_normal_no_alert : forall key,
  dr_silent_alert (handle_auth (NormalAuth key)) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

(** ===============================================================================
    PROOFS: DEAD MAN'S SWITCH (5 theorems)
    =============================================================================== *)

Theorem PSI_004_01_checkin_resets : forall dms now,
  dms_triggered (dms_checkin dms now) = false.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_004_02_checkin_updates_time : forall dms now,
  dms_last_checkin (dms_checkin dms now) = now.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_004_03_timeout_triggers : forall dms now,
  dms_timeout dms + dms_last_checkin dms < now ->
  dms_triggered (dms_check dms now) = true.
Proof.
  intros dms now H. unfold dms_check.
  destruct (dms_timeout dms + dms_last_checkin dms <? now) eqn:E.
  - simpl. reflexivity.
  - apply Nat.ltb_ge in E. lia.
Qed.

Theorem PSI_004_04_no_timeout_no_trigger : forall dms now,
  now <= dms_timeout dms + dms_last_checkin dms ->
  dms_triggered dms = false ->
  dms_triggered (dms_check dms now) = false.
Proof.
  intros dms now Hle Hfalse. unfold dms_check.
  destruct (dms_timeout dms + dms_last_checkin dms <? now) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - exact Hfalse.
Qed.

Theorem PSI_004_05_recovery_action_preserved : forall dms now,
  dms_recovery_action (dms_check dms now) = dms_recovery_action dms.
Proof.
  intros dms now. unfold dms_check.
  destruct (dms_timeout dms + dms_last_checkin dms <? now); simpl; reflexivity.
Qed.

(** ===============================================================================
    PROOFS: INSIDER BUDGET (5 theorems)
    =============================================================================== *)

Theorem PSI_005_01_budget_enforced : forall budget bytes,
  ib_can_query budget bytes = true ->
  budget.(ib_bytes_used) + bytes <= budget.(ib_max_bytes).
Proof.
  intros budget bytes H. unfold ib_can_query in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

Theorem PSI_005_02_budget_query_count : forall budget bytes,
  ib_can_query budget bytes = true ->
  budget.(ib_queries_used) < budget.(ib_max_queries).
Proof.
  intros budget bytes H. unfold ib_can_query in H.
  apply andb_true_iff in H. destruct H as [_ H].
  apply Nat.ltb_lt in H. exact H.
Qed.

Theorem PSI_005_03_record_increases_bytes : forall budget bytes,
  (ib_record_query budget bytes).(ib_bytes_used) = budget.(ib_bytes_used) + bytes.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_005_04_record_increases_queries : forall budget bytes,
  (ib_record_query budget bytes).(ib_queries_used) = S (budget.(ib_queries_used)).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_005_05_audit_append_preserves : forall log entry,
  In entry (audit_log_append log entry).
Proof.
  intros. simpl. left. reflexivity.
Qed.

(** ===============================================================================
    PROOFS: TIME-LOCKED OPERATIONS (5 theorems)
    =============================================================================== *)

Theorem PSI_006_01_timelock_cancellation_window : forall tl now,
  now < tl_execute_time tl ->
  tl_can_cancel tl now = true.
Proof.
  intros tl now H. unfold tl_can_cancel. apply Nat.ltb_lt. exact H.
Qed.

Theorem PSI_006_02_cancelled_cannot_execute : forall tl now,
  tl_cancelled tl = true ->
  tl_can_execute tl now = false.
Proof.
  intros tl now H. unfold tl_can_execute. rewrite H. simpl.
  apply andb_false_r.
Qed.

Theorem PSI_006_03_cancel_sets_flag : forall tl,
  tl_cancelled (tl_cancel tl) = true.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_006_04_early_execute_blocked : forall tl now,
  now < tl_execute_time tl ->
  tl_can_execute tl now = false.
Proof.
  intros tl now H. unfold tl_can_execute.
  destruct (tl_execute_time tl <=? now) eqn:E.
  - apply Nat.leb_le in E. lia.
  - simpl. reflexivity.
Qed.

Theorem PSI_006_05_cancel_preserves_operation : forall tl,
  tl_operation (tl_cancel tl) = tl_operation tl.
Proof.
  intros. simpl. reflexivity.
Qed.

(** ===============================================================================
    PROOFS: HARDWARE DIVERSITY (3 theorems)
    =============================================================================== *)

Theorem PSI_007_01_different_vendor_independent : forall p1 p2,
  plat_vendor p1 <> plat_vendor p2 ->
  platforms_independent p1 p2 = true.
Proof.
  intros p1 p2 H. unfold platforms_independent.
  destruct (Nat.eqb (plat_vendor p1) (plat_vendor p2)) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - simpl. reflexivity.
Qed.

Theorem PSI_007_02_nversion_single_agrees :
  forall r, nversion_agree [r] = true.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem PSI_007_03_nversion_empty_agrees :
  nversion_agree [] = true.
Proof.
  simpl. reflexivity.
Qed.

(** ===============================================================================
    END OF OPERATIONAL SECURITY PROOFS
    — 38 theorems, 0 admits, 0 axioms
    =============================================================================== *)
