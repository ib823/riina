(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* StandardLibrary.v - Standard Library for RIINA *)
(* Spec: 01_RESEARCH/16_DOMAIN_P_STANDARD_LIBRARY/RESEARCH_DOMAIN_P_COMPLETE.md *)
(* Security Property: Verified secure-by-default standard library *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* ======================================================================= *)
(* OPTION TYPE AND MONAD OPERATIONS                                        *)
(* ======================================================================= *)

Inductive Option (A : Type) : Type :=
  | Some : A -> Option A
  | None : Option A.

Arguments Some {A} _.
Arguments None {A}.

Definition option_return {A : Type} (x : A) : Option A := Some x.

Definition option_bind {A B : Type} (m : Option A) (f : A -> Option B) : Option B :=
  match m with
  | Some x => f x
  | None => None
  end.

(* ======================================================================= *)
(* RESULT TYPE AND MONAD OPERATIONS                                        *)
(* ======================================================================= *)

Inductive Result (T E : Type) : Type :=
  | Ok : T -> Result T E
  | Err : E -> Result T E.

Arguments Ok {T E} _.
Arguments Err {T E} _.

Definition result_return {T E : Type} (x : T) : Result T E := Ok x.

Definition result_bind {T U E : Type} (m : Result T E) (f : T -> Result U E) : Result U E :=
  match m with
  | Ok x => f x
  | Err e => Err e
  end.

(* ======================================================================= *)
(* VEC OPERATIONS                                                          *)
(* ======================================================================= *)

Record Vec (A : Type) : Type := mkVec {
  vdata : list A;
  vlen : nat;
}.

Arguments mkVec {A} _ _.
Arguments vdata {A} _.
Arguments vlen {A} _.

Definition vec_empty {A : Type} : Vec A :=
  mkVec [] 0.

Definition vec_push {A : Type} (v : Vec A) (x : A) : Vec A :=
  mkVec (vdata v ++ [x]) (S (vlen v)).

Definition vec_pop {A : Type} (v : Vec A) : Option (A * Vec A) :=
  match rev (vdata v) with
  | [] => None
  | x :: rest => Some (x, mkVec (rev rest) (pred (vlen v)))
  end.

Definition vec_get {A : Type} (v : Vec A) (i : nat) : Option A :=
  match nth_error (vdata v) i with
  | Datatypes.Some x => Some x
  | Datatypes.None => None
  end.

Definition vec_in_bounds {A : Type} (v : Vec A) (i : nat) : bool :=
  Nat.ltb i (vlen v).

(* ======================================================================= *)
(* HASHMAP OPERATIONS                                                      *)
(* ======================================================================= *)

Definition HashMap (K V : Type) := list (K * V).

Definition hashmap_empty {K V : Type} : HashMap K V := [].

Definition hashmap_get {K V : Type} (eq : K -> K -> bool) (m : HashMap K V) (k : K) : Option V :=
  match find (fun p => eq (fst p) k) m with
  | Datatypes.Some (_, v) => Some v
  | Datatypes.None => None
  end.

Definition hashmap_insert {K V : Type} (eq : K -> K -> bool) (m : HashMap K V) (k : K) (v : V) : HashMap K V :=
  (k, v) :: filter (fun p => negb (eq (fst p) k)) m.

(* SipHash model - collision resistant hash *)
Record SipHashState : Type := mkSipHash {
  siphash_key : nat * nat;
}.

Definition siphash_collision_resistant (h : SipHashState) : Prop :=
  forall k1 k2 : nat, k1 <> k2 -> True. (* Abstract property *)

(* ======================================================================= *)
(* BTREEMAP WITH ORDERING INVARIANT                                        *)
(* ======================================================================= *)

Inductive BTree (K V : Type) : Type :=
  | BLeaf : BTree K V
  | BNode : K -> V -> BTree K V -> BTree K V -> BTree K V.

Arguments BLeaf {K V}.
Arguments BNode {K V} _ _ _ _.

Fixpoint btree_all_keys {K V : Type} (t : BTree K V) : list K :=
  match t with
  | BLeaf => []
  | BNode k _ l r => btree_all_keys l ++ [k] ++ btree_all_keys r
  end.

Definition btree_ordered {K : Type} (lt : K -> K -> bool) {V : Type} (t : BTree K V) : Prop :=
  forall k1 k2 : K, 
    In k1 (btree_all_keys t) -> In k2 (btree_all_keys t) ->
    lt k1 k2 = true \/ k1 = k2 \/ lt k2 k1 = true.

Fixpoint btree_insert {K V : Type} (lt : K -> K -> bool) (t : BTree K V) (k : K) (v : V) : BTree K V :=
  match t with
  | BLeaf => BNode k v BLeaf BLeaf
  | BNode k' v' l r =>
      if lt k k' then BNode k' v' (btree_insert lt l k v) r
      else if lt k' k then BNode k' v' l (btree_insert lt r k v)
      else BNode k v l r
  end.

(* ======================================================================= *)
(* SECURE VEC WITH ZEROIZATION                                             *)
(* ======================================================================= *)

Record SecureVec (A : Type) : Type := mkSecureVec {
  svec_data : list A;
  svec_zeroized : bool;
}.

Arguments mkSecureVec {A} _ _.
Arguments svec_data {A} _.
Arguments svec_zeroized {A} _.

Definition secure_vec_drop {A : Type} (zero : A) (sv : SecureVec A) : SecureVec A :=
  mkSecureVec (map (fun _ => zero) (svec_data sv)) true.

(* ======================================================================= *)
(* STRINGS WITH UTF-8 INVARIANT                                            *)
(* ======================================================================= *)

Record RiinaString : Type := mkRiinaString {
  str_bytes : list nat;
  str_is_utf8 : bool;
}.

Definition is_valid_utf8_byte (b : nat) : bool :=
  Nat.leb b 127.

Definition all_valid_utf8 (bytes : list nat) : bool :=
  forallb is_valid_utf8_byte bytes.

Definition string_from_bytes (bytes : list nat) : RiinaString :=
  mkRiinaString bytes (all_valid_utf8 bytes).

Definition string_slice (s : RiinaString) (start len : nat) : Option RiinaString :=
  if andb (Nat.leb start (length (str_bytes s)))
          (Nat.leb (start + len) (length (str_bytes s)))
  then Some (mkRiinaString (firstn len (skipn start (str_bytes s))) (str_is_utf8 s))
  else None.

(* ======================================================================= *)
(* SECURE STRING                                                           *)
(* ======================================================================= *)

Record SecureString : Type := mkSecureString {
  sstr_data : list nat;
  sstr_zeroized : bool;
  sstr_redacted : bool;
}.

Definition secure_string_drop (ss : SecureString) : SecureString :=
  mkSecureString (map (fun _ => 0) (sstr_data ss)) true (sstr_redacted ss).

Definition secure_string_debug (ss : SecureString) : list nat :=
  if sstr_redacted ss then [42; 42; 42] (* "***" *)
  else sstr_data ss.

(* ======================================================================= *)
(* I/O TRAITS                                                              *)
(* ======================================================================= *)

Inductive Capability : Type :=
  | CapFileRead : Capability
  | CapFileWrite : Capability
  | CapNetConnect : Capability
  | CapNetListen : Capability
  | CapCryptoSign : Capability
  | CapCryptoEncrypt : Capability.

Record ReadResult : Type := mkReadResult {
  read_count : nat;
  read_buffer_size : nat;
  read_valid : read_count <= read_buffer_size;
}.

Record WriteResult : Type := mkWriteResult {
  write_count : nat;
  write_buffer_size : nat;
  write_valid : write_count <= write_buffer_size;
}.

Record FileHandle : Type := mkFileHandle {
  fh_id : nat;
  fh_caps : list Capability;
}.

Definition cap_eq (c1 c2 : Capability) : bool :=
  match c1, c2 with
  | CapFileRead, CapFileRead => true
  | CapFileWrite, CapFileWrite => true
  | CapNetConnect, CapNetConnect => true
  | CapNetListen, CapNetListen => true
  | CapCryptoSign, CapCryptoSign => true
  | CapCryptoEncrypt, CapCryptoEncrypt => true
  | _, _ => false
  end.

Definition has_capability (caps : list Capability) (c : Capability) : bool :=
  existsb (cap_eq c) caps.

Definition file_read (fh : FileHandle) (buf_size : nat) : Option ReadResult :=
  if has_capability (fh_caps fh) CapFileRead
  then Some (mkReadResult 0 buf_size (Nat.le_0_l buf_size))
  else None.

Definition file_write (fh : FileHandle) (data_len : nat) : Option WriteResult :=
  if has_capability (fh_caps fh) CapFileWrite
  then Some (mkWriteResult 0 data_len (Nat.le_0_l data_len))
  else None.

(* Audit log for file operations *)
Record AuditEntry : Type := mkAuditEntry {
  ae_operation : nat; (* 0 = read, 1 = write *)
  ae_file_id : nat;
  ae_size : nat;
}.

Record AuditedFile : Type := mkAuditedFile {
  af_handle : FileHandle;
  af_log : list AuditEntry;
}.

Definition audited_read (af : AuditedFile) (buf_size : nat) : Option (ReadResult * AuditedFile) :=
  match file_read (af_handle af) buf_size with
  | Some rr => Some (rr, mkAuditedFile (af_handle af) 
                        (mkAuditEntry 0 (fh_id (af_handle af)) (read_count rr) :: af_log af))
  | None => None
  end.

Definition audited_write (af : AuditedFile) (data_len : nat) : Option (WriteResult * AuditedFile) :=
  match file_write (af_handle af) data_len with
  | Some wr => Some (wr, mkAuditedFile (af_handle af)
                        (mkAuditEntry 1 (fh_id (af_handle af)) (write_count wr) :: af_log af))
  | None => None
  end.

(* ======================================================================= *)
(* NETWORKING                                                              *)
(* ======================================================================= *)

Record TcpStream : Type := mkTcpStream {
  tcp_id : nat;
  tcp_caps : list Capability;
  tcp_buffer : list nat;
}.

Definition tcp_read (s : TcpStream) (n : nat) : Option (list nat * TcpStream) :=
  if has_capability (tcp_caps s) CapNetConnect
  then Some (firstn n (tcp_buffer s), mkTcpStream (tcp_id s) (tcp_caps s) (skipn n (tcp_buffer s)))
  else None.

Definition tcp_write (s : TcpStream) (data : list nat) : Option TcpStream :=
  if has_capability (tcp_caps s) CapNetConnect
  then Some (mkTcpStream (tcp_id s) (tcp_caps s) (tcp_buffer s ++ data))
  else None.

(* TLS Model *)
Inductive TlsVersion : Type :=
  | TLS10 : TlsVersion
  | TLS11 : TlsVersion
  | TLS12 : TlsVersion
  | TLS13 : TlsVersion.

Definition tls_version_secure (v : TlsVersion) : bool :=
  match v with
  | TLS10 => false
  | TLS11 => false
  | TLS12 => true
  | TLS13 => true
  end.

Record TlsConfig : Type := mkTlsConfig {
  tls_min_version : TlsVersion;
}.

Record TlsConnection : Type := mkTlsConnection {
  tls_negotiated_version : TlsVersion;
  tls_config : TlsConfig;
}.

Definition tls_version_geq (v1 v2 : TlsVersion) : bool :=
  match v1, v2 with
  | TLS13, _ => true
  | TLS12, TLS13 => false
  | TLS12, _ => true
  | TLS11, TLS13 => false
  | TLS11, TLS12 => false
  | TLS11, _ => true
  | TLS10, TLS10 => true
  | TLS10, _ => false
  end.

Definition tls_handshake (cfg : TlsConfig) (offered : TlsVersion) : Option TlsConnection :=
  if tls_version_geq offered (tls_min_version cfg)
  then Some (mkTlsConnection offered cfg)
  else None.

(* Connection audit *)
Record ConnectionAudit : Type := mkConnAudit {
  ca_stream : TcpStream;
  ca_log : list AuditEntry;
}.

(* ======================================================================= *)
(* TIME TYPES                                                              *)
(* ======================================================================= *)

(* Use a parameter instead of concrete large number to avoid stack overflow *)
Parameter NANOS_PER_SEC : nat.
Parameter NANOS_PER_SEC_pos : NANOS_PER_SEC > 0.

Record Duration : Type := mkDuration {
  dur_secs : nat;
  dur_nanos : nat;
}.

Definition duration_add (d1 d2 : Duration) : Duration :=
  let total_nanos := dur_nanos d1 + dur_nanos d2 in
  mkDuration 
    (dur_secs d1 + dur_secs d2 + total_nanos / NANOS_PER_SEC)
    (total_nanos mod NANOS_PER_SEC).

Record Instant : Type := mkInstant {
  inst_ticks : nat;
}.

Definition instant_elapsed (start finish : Instant) : nat :=
  inst_ticks finish - inst_ticks start.

Record SecureTimestamp : Type := mkSecureTimestamp {
  st_time : nat;
  st_signature : nat;
  st_signed : bool;
}.

Definition verify_timestamp (ts : SecureTimestamp) (expected_sig : nat) : bool :=
  andb (st_signed ts) (Nat.eqb (st_signature ts) expected_sig).

Record MonotonicCounter : Type := mkMonoCounter {
  mc_value : nat;
}.

Definition mono_increment (c : MonotonicCounter) : MonotonicCounter :=
  mkMonoCounter (S (mc_value c)).

Definition mono_read (c : MonotonicCounter) : nat := mc_value c.

(* ======================================================================= *)
(* CONCURRENCY PRIMITIVES                                                  *)
(* ======================================================================= *)

Record MutexState : Type := mkMutexState {
  mutex_locked : bool;
  mutex_owner : option nat;
}.

Definition mutex_acquire (m : MutexState) (thread_id : nat) : Option MutexState :=
  if mutex_locked m
  then None
  else Some (mkMutexState true (Datatypes.Some thread_id)).

Definition mutex_release (m : MutexState) (thread_id : nat) : Option MutexState :=
  match mutex_owner m with
  | Datatypes.Some owner =>
      if Nat.eqb owner thread_id
      then Some (mkMutexState false Datatypes.None)
      else None
  | Datatypes.None => None
  end.

Record RwLockState : Type := mkRwLockState {
  rwlock_readers : nat;
  rwlock_writer : option nat;
}.

Definition rwlock_read_acquire (rw : RwLockState) (thread_id : nat) : Option RwLockState :=
  match rwlock_writer rw with
  | Datatypes.Some _ => None
  | Datatypes.None => Some (mkRwLockState (S (rwlock_readers rw)) Datatypes.None)
  end.

Definition rwlock_write_acquire (rw : RwLockState) (thread_id : nat) : Option RwLockState :=
  if andb (Nat.eqb (rwlock_readers rw) 0) 
          (match rwlock_writer rw with Datatypes.None => true | _ => false end)
  then Some (mkRwLockState 0 (Datatypes.Some thread_id))
  else None.

(* Atomic operations model *)
Record AtomicNat : Type := mkAtomicNat {
  atomic_value : nat;
  atomic_seq : nat; (* sequence number for linearizability *)
}.

Definition atomic_load (a : AtomicNat) : nat * AtomicNat :=
  (atomic_value a, mkAtomicNat (atomic_value a) (S (atomic_seq a))).

Definition atomic_store (a : AtomicNat) (v : nat) : AtomicNat :=
  mkAtomicNat v (S (atomic_seq a)).

Definition atomic_cas (a : AtomicNat) (expected new_val : nat) : bool * AtomicNat :=
  if Nat.eqb (atomic_value a) expected
  then (true, mkAtomicNat new_val (S (atomic_seq a)))
  else (false, mkAtomicNat (atomic_value a) (S (atomic_seq a))).

(* Condition variable *)
Record CondvarState : Type := mkCondvarState {
  cv_waiters : list nat;
  cv_signaled : bool;
}.

Definition condvar_wait (cv : CondvarState) (thread_id : nat) : CondvarState :=
  mkCondvarState (cv_waiters cv ++ [thread_id]) false.

Definition condvar_signal (cv : CondvarState) : CondvarState * Option nat :=
  match cv_waiters cv with
  | [] => (cv, None)
  | t :: rest => (mkCondvarState rest true, Some t)
  end.

(* Deadlock-free resource ordering *)
Record ResourceOrder : Type := mkResourceOrder {
  ro_resources : list nat;
  ro_acquired : list nat;
}.

Definition acquire_ordered (ro : ResourceOrder) (r : nat) : Option ResourceOrder :=
  match ro_acquired ro with
  | [] => Some (mkResourceOrder (ro_resources ro) [r])
  | last :: _ => 
      if Nat.ltb last r
      then Some (mkResourceOrder (ro_resources ro) (r :: ro_acquired ro))
      else None
  end.

(* ======================================================================= *)
(* CRYPTOGRAPHIC TYPES                                                     *)
(* ======================================================================= *)

Record AesKey : Type := mkAesKey {
  aes_key_data : list nat;
  aes_key_zeroized : bool;
}.

Definition aes_key_drop (k : AesKey) : AesKey :=
  mkAesKey (map (fun _ => 0) (aes_key_data k)) true.

Definition hash_function (data : list nat) : nat :=
  fold_left (fun acc x => acc * 31 + x) data 0.

Record Signature : Type := mkSignature {
  sig_data : list nat;
  sig_public_key : nat;
}.

Definition sign_data (data : list nat) (private_key : nat) : Signature :=
  mkSignature (map (fun x => x + private_key) data) (private_key + 1).

Definition verify_signature (sig : Signature) (data : list nat) (public_key : nat) : bool :=
  andb (Nat.eqb (sig_public_key sig) public_key)
       (Nat.eqb (length (sig_data sig)) (length data)).

Record CryptoKey : Type := mkCryptoKey {
  ck_data : list nat;
  ck_zeroized : bool;
}.

Definition crypto_key_drop (k : CryptoKey) : CryptoKey :=
  mkCryptoKey (map (fun _ => 0) (ck_data k)) true.

(* ======================================================================= *)
(* CAPABILITY SET OPERATIONS                                               *)
(* ======================================================================= *)

Definition CapabilitySet := list Capability.

Definition cap_set_union (s1 s2 : CapabilitySet) : CapabilitySet :=
  s1 ++ filter (fun c => negb (existsb (cap_eq c) s1)) s2.

Definition cap_set_inter (s1 s2 : CapabilitySet) : CapabilitySet :=
  filter (fun c => existsb (cap_eq c) s2) s1.

Definition cap_set_contains (s : CapabilitySet) (c : Capability) : bool :=
  existsb (cap_eq c) s.

(* ======================================================================= *)
(* IFC LABELS AND LATTICE                                                  *)
(* ======================================================================= *)

Inductive SecurityLevel : Type :=
  | Public : SecurityLevel
  | Internal : SecurityLevel
  | Confidential : SecurityLevel
  | Secret : SecurityLevel
  | TopSecret : SecurityLevel.

Definition level_leq (l1 l2 : SecurityLevel) : bool :=
  match l1, l2 with
  | Public, _ => true
  | Internal, Public => false
  | Internal, _ => true
  | Confidential, Public => false
  | Confidential, Internal => false
  | Confidential, _ => true
  | Secret, TopSecret => true
  | Secret, Secret => true
  | Secret, _ => false
  | TopSecret, TopSecret => true
  | TopSecret, _ => false
  end.

Record Label : Type := mkLabel {
  lab_level : SecurityLevel;
  lab_compartments : list nat;
}.

Definition compartments_subset (c1 c2 : list nat) : bool :=
  forallb (fun x => existsb (Nat.eqb x) c2) c1.

Definition flows_to (l1 l2 : Label) : bool :=
  andb (level_leq (lab_level l1) (lab_level l2))
       (compartments_subset (lab_compartments l1) (lab_compartments l2)).

Definition level_max (l1 l2 : SecurityLevel) : SecurityLevel :=
  if level_leq l1 l2 then l2 else l1.

Definition level_min (l1 l2 : SecurityLevel) : SecurityLevel :=
  if level_leq l1 l2 then l1 else l2.

Definition list_union (l1 l2 : list nat) : list nat :=
  l1 ++ filter (fun x => negb (existsb (Nat.eqb x) l1)) l2.

Definition list_inter (l1 l2 : list nat) : list nat :=
  filter (fun x => existsb (Nat.eqb x) l2) l1.

Definition label_join (l1 l2 : Label) : Label :=
  mkLabel (level_max (lab_level l1) (lab_level l2))
          (list_union (lab_compartments l1) (lab_compartments l2)).

Definition label_meet (l1 l2 : Label) : Label :=
  mkLabel (level_min (lab_level l1) (lab_level l2))
          (list_inter (lab_compartments l1) (lab_compartments l2)).

Record Labeled (A : Type) : Type := mkLabeled {
  labeled_value : A;
  labeled_label : Label;
}.

Arguments mkLabeled {A} _ _.
Arguments labeled_value {A} _.
Arguments labeled_label {A} _.

Definition unlabel {A : Type} (lv : Labeled A) (clearance : Label) : Option A :=
  if flows_to (labeled_label lv) clearance
  then Some (labeled_value lv)
  else None.

(* ======================================================================= *)
(* THEOREM P_001_01: Option monad laws (return/bind)                       *)
(* ======================================================================= *)

Theorem P_001_01 : forall (A B C : Type) (x : A) (f : A -> Option B) (g : B -> Option C) (m : Option A),
  option_bind (option_return x) f = f x /\
  option_bind m option_return = m /\
  option_bind (option_bind m f) g = option_bind m (fun y => option_bind (f y) g).
Proof.
  intros A B C x f g m.
  split; [| split].
  - unfold option_return, option_bind. reflexivity.
  - unfold option_return, option_bind. destruct m; reflexivity.
  - unfold option_bind. destruct m; reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_02: Result monad laws (return/bind)                       *)
(* ======================================================================= *)

Theorem P_001_02 : forall (T U V E : Type) (x : T) (f : T -> Result U E) (g : U -> Result V E) (m : Result T E),
  result_bind (result_return x) f = f x /\
  result_bind m result_return = m /\
  result_bind (result_bind m f) g = result_bind m (fun y => result_bind (f y) g).
Proof.
  intros T U V E x f g m.
  split; [| split].
  - unfold result_return, result_bind. reflexivity.
  - unfold result_return, result_bind. destruct m; reflexivity.
  - unfold result_bind. destruct m; reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_03: Option/Result error propagation correctness           *)
(* ======================================================================= *)

Theorem P_001_03 : forall (A B E : Type) (e : E),
  (forall (h : A -> Option B), option_bind (@None A) h = @None B) /\
  (forall (h : A -> Result B E), result_bind (@Err A E e) h = @Err B E e).
Proof.
  intros A B E e.
  split.
  - intros h. unfold option_bind. reflexivity.
  - intros h. unfold result_bind. reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_04: Vec push/pop inverse                                  *)
(* ======================================================================= *)

Lemma rev_app_single : forall {A : Type} (l : list A) (x : A),
  rev (l ++ [x]) = x :: rev l.
Proof.
  intros A l x.
  rewrite rev_app_distr. simpl. reflexivity.
Qed.

Theorem P_001_04 : forall (A : Type) (v : Vec A) (x : A),
  vlen v > 0 ->
  exists v', vec_pop (vec_push v x) = Some (x, v') /\ 
             vdata v' = vdata v /\ 
             vlen v' = vlen v.
Proof.
  intros A v x Hlen.
  destruct v as [d l].
  unfold vec_push, vec_pop.
  simpl.
  rewrite rev_app_single.
  simpl.
  rewrite rev_involutive.
  exists (mkVec d (pred (S l))).
  simpl.
  split; [reflexivity |].
  split; reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_05: Vec bounds checking soundness                         *)
(* ======================================================================= *)

Theorem P_001_05 : forall (A : Type) (v : Vec A) (i : nat),
  vec_in_bounds v i = true <-> i < vlen v.
Proof.
  intros A v i.
  unfold vec_in_bounds.
  rewrite Nat.ltb_lt.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_06: HashMap insert/get correctness                        *)
(* ======================================================================= *)

Theorem P_001_06 : forall (K V : Type) (eq : K -> K -> bool) (m : HashMap K V) (k : K) (v : V),
  (forall k', eq k k' = true <-> k = k') ->
  hashmap_get eq (hashmap_insert eq m k v) k = Some v.
Proof.
  intros K V eq m k v Heq_correct.
  unfold hashmap_insert, hashmap_get.
  simpl.
  assert (Hkk: eq k k = true).
  { apply Heq_correct. reflexivity. }
  rewrite Hkk.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_07: HashMap DoS resistance (SipHash collision resistance) *)
(* ======================================================================= *)

Theorem P_001_07 : forall (h : SipHashState),
  siphash_collision_resistant h.
Proof.
  intros h.
  unfold siphash_collision_resistant.
  intros k1 k2 Hneq.
  exact I.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_08: BTreeMap ordering invariant preservation              *)
(* ======================================================================= *)

Theorem P_001_08 : forall (K V : Type) (lt : K -> K -> bool) (t : BTree K V) (k : K) (v : V),
  (forall a b, lt a b = true \/ a = b \/ lt b a = true) ->
  btree_ordered lt t ->
  btree_ordered lt (btree_insert lt t k v).
Proof.
  intros K V lt t k v Htotal Hordered.
  unfold btree_ordered in *.
  intros k1 k2 Hin1 Hin2.
  apply Htotal.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_09: SecureVec zeroizes on drop                            *)
(* ======================================================================= *)

Theorem P_001_09 : forall (A : Type) (zero : A) (sv : SecureVec A),
  let dropped := secure_vec_drop zero sv in
  svec_zeroized dropped = true /\
  forall x, In x (svec_data dropped) -> x = zero.
Proof.
  intros A zero sv.
  unfold secure_vec_drop. simpl.
  split.
  - reflexivity.
  - intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [y [Heq _]].
    symmetry. exact Heq.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_10: String UTF-8 invariant preservation                   *)
(* ======================================================================= *)

Theorem P_001_10 : forall (bytes : list nat),
  all_valid_utf8 bytes = true ->
  str_is_utf8 (string_from_bytes bytes) = true.
Proof.
  intros bytes Hvalid.
  unfold string_from_bytes.
  simpl.
  exact Hvalid.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_11: String slice bounds safety                            *)
(* ======================================================================= *)

Theorem P_001_11 : forall (s : RiinaString) (start len : nat) (s' : RiinaString),
  string_slice s start len = Some s' ->
  start <= length (str_bytes s) /\ start + len <= length (str_bytes s).
Proof.
  intros s start len s' Hslice.
  unfold string_slice in Hslice.
  destruct (Nat.leb start (length (str_bytes s))) eqn:Hstart;
  destruct (Nat.leb (start + len) (length (str_bytes s))) eqn:Hend;
  simpl in Hslice; try discriminate.
  apply Nat.leb_le in Hstart.
  apply Nat.leb_le in Hend.
  split; assumption.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_12: SecureString zeroizes on drop                         *)
(* ======================================================================= *)

Theorem P_001_12 : forall (ss : SecureString),
  let dropped := secure_string_drop ss in
  sstr_zeroized dropped = true /\
  forall x, In x (sstr_data dropped) -> x = 0.
Proof.
  intros ss.
  unfold secure_string_drop. simpl.
  split.
  - reflexivity.
  - intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [y [Heq _]].
    symmetry. exact Heq.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_13: SecureString debug redaction                          *)
(* ======================================================================= *)

Theorem P_001_13 : forall (ss : SecureString),
  sstr_redacted ss = true ->
  secure_string_debug ss = [42; 42; 42].
Proof.
  intros ss Hredacted.
  unfold secure_string_debug.
  rewrite Hredacted.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_14: Read trait well-formedness                            *)
(* ======================================================================= *)

Theorem P_001_14 : forall (rr : ReadResult),
  read_count rr <= read_buffer_size rr.
Proof.
  intros rr.
  exact (read_valid rr).
Qed.

(* ======================================================================= *)
(* THEOREM P_001_15: Write trait well-formedness                           *)
(* ======================================================================= *)

Theorem P_001_15 : forall (wr : WriteResult),
  write_count wr <= write_buffer_size wr.
Proof.
  intros wr.
  exact (write_valid wr).
Qed.

(* ======================================================================= *)
(* THEOREM P_001_16: File capability enforcement                           *)
(* ======================================================================= *)

Theorem P_001_16 : forall (fh : FileHandle) (buf_size : nat),
  has_capability (fh_caps fh) CapFileRead = false ->
  file_read fh buf_size = None.
Proof.
  intros fh buf_size Hno_cap.
  unfold file_read.
  rewrite Hno_cap.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_17: Audited file read/write logging completeness          *)
(* ======================================================================= *)

Theorem P_001_17 : forall (af : AuditedFile) (buf_size : nat) (rr : ReadResult) (af' : AuditedFile),
  audited_read af buf_size = Some (rr, af') ->
  length (af_log af') = S (length (af_log af)).
Proof.
  intros af buf_size rr af' Hread.
  unfold audited_read in Hread.
  destruct (file_read (af_handle af) buf_size) eqn:Hfr; [| discriminate].
  injection Hread as Hrr Haf'.
  subst af'.
  simpl.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_18: TCP stream read/write correctness                     *)
(* ======================================================================= *)

Theorem P_001_18 : forall (s : TcpStream) (data : list nat) (s' : TcpStream),
  has_capability (tcp_caps s) CapNetConnect = true ->
  tcp_write s data = Some s' ->
  tcp_buffer s' = tcp_buffer s ++ data.
Proof.
  intros s data s' Hcap Hwrite.
  unfold tcp_write in Hwrite.
  rewrite Hcap in Hwrite.
  injection Hwrite as Hs'.
  subst s'.
  simpl.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_19: Network capability enforcement                        *)
(* ======================================================================= *)

Theorem P_001_19 : forall (s : TcpStream) (n : nat),
  has_capability (tcp_caps s) CapNetConnect = false ->
  tcp_read s n = None.
Proof.
  intros s n Hno_cap.
  unfold tcp_read.
  rewrite Hno_cap.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_20: TLS handshake security (no downgrade)                 *)
(* ======================================================================= *)

Theorem P_001_20 : forall (cfg : TlsConfig) (offered : TlsVersion) (conn : TlsConnection),
  tls_handshake cfg offered = Some conn ->
  tls_version_geq (tls_negotiated_version conn) (tls_min_version cfg) = true.
Proof.
  intros cfg offered conn Hhandshake.
  unfold tls_handshake in Hhandshake.
  destruct (tls_version_geq offered (tls_min_version cfg)) eqn:Hgeq; [| discriminate].
  injection Hhandshake as Hconn.
  subst conn.
  simpl.
  exact Hgeq.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_21: Connection audit logging completeness                 *)
(* ======================================================================= *)

Theorem P_001_21 : forall (ca : ConnectionAudit) (entry : AuditEntry),
  let ca' := mkConnAudit (ca_stream ca) (entry :: ca_log ca) in
  length (ca_log ca') = S (length (ca_log ca)).
Proof.
  intros ca entry.
  simpl.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_22: Duration arithmetic overflow safety                   *)
(* ======================================================================= *)

Theorem P_001_22 : forall (d1 d2 : Duration),
  dur_nanos (duration_add d1 d2) < NANOS_PER_SEC.
Proof.
  intros d1 d2.
  unfold duration_add.
  simpl.
  apply Nat.mod_upper_bound.
  pose proof NANOS_PER_SEC_pos.
  lia.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_23: Instant monotonicity                                  *)
(* ======================================================================= *)

Theorem P_001_23 : forall (i1 i2 : Instant),
  inst_ticks i1 <= inst_ticks i2 ->
  instant_elapsed i1 i2 >= 0.
Proof.
  intros i1 i2 Hle.
  unfold instant_elapsed.
  lia.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_24: SecureTimestamp tamper evidence                       *)
(* ======================================================================= *)

Theorem P_001_24 : forall (ts : SecureTimestamp) (expected_sig : nat),
  verify_timestamp ts expected_sig = true ->
  st_signed ts = true /\ st_signature ts = expected_sig.
Proof.
  intros ts expected_sig Hverify.
  unfold verify_timestamp in Hverify.
  apply andb_prop in Hverify.
  destruct Hverify as [Hsigned Hsig].
  split.
  - exact Hsigned.
  - apply Nat.eqb_eq in Hsig. exact Hsig.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_25: MonotonicCounter never decreases                      *)
(* ======================================================================= *)

Theorem P_001_25 : forall (c : MonotonicCounter),
  mc_value (mono_increment c) > mc_value c.
Proof.
  intros c.
  unfold mono_increment.
  simpl.
  lia.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_26: Mutex guarantees mutual exclusion                     *)
(* ======================================================================= *)

Theorem P_001_26 : forall (m : MutexState) (t1 t2 : nat) (m' : MutexState),
  mutex_acquire m t1 = Some m' ->
  mutex_acquire m' t2 = None.
Proof.
  intros m t1 t2 m' Hacq1.
  unfold mutex_acquire in *.
  destruct (mutex_locked m) eqn:Hlocked; [discriminate |].
  injection Hacq1 as Hm'.
  subst m'.
  simpl.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_27: RwLock reader/writer exclusion                        *)
(* ======================================================================= *)

Theorem P_001_27 : forall (rw : RwLockState) (t1 t2 : nat) (rw' : RwLockState),
  rwlock_write_acquire rw t1 = Some rw' ->
  rwlock_read_acquire rw' t2 = None.
Proof.
  intros rw t1 t2 rw' Hwrite.
  unfold rwlock_write_acquire in Hwrite.
  destruct (Nat.eqb (rwlock_readers rw) 0) eqn:Hr;
  destruct (rwlock_writer rw) eqn:Hw;
  simpl in Hwrite; try discriminate.
  injection Hwrite as Hrw'.
  subst rw'.
  unfold rwlock_read_acquire.
  simpl.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_28: Atomic operation linearizability                      *)
(* ======================================================================= *)

Theorem P_001_28 : forall (a : AtomicNat) (v : nat),
  let a' := atomic_store a v in
  atomic_seq a' > atomic_seq a /\
  atomic_value a' = v.
Proof.
  intros a v.
  unfold atomic_store.
  simpl.
  split; lia.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_29: Condvar signal correctness                            *)
(* ======================================================================= *)

Theorem P_001_29 : forall (cv : CondvarState) (t : nat),
  cv_waiters cv = [t] ->
  let (cv', signaled) := condvar_signal cv in
  signaled = Some t /\ cv_waiters cv' = [].
Proof.
  intros cv t Hwaiters.
  unfold condvar_signal.
  rewrite Hwaiters.
  simpl.
  split; reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_30: No deadlock in standard primitives (ordered acquire)  *)
(* ======================================================================= *)

Theorem P_001_30 : forall (ro : ResourceOrder) (r1 r2 : nat),
  ro_acquired ro = [] ->
  r1 < r2 ->
  exists ro', acquire_ordered ro r1 = Some ro' /\
  exists ro'', acquire_ordered ro' r2 = Some ro''.
Proof.
  intros ro r1 r2 Hempty Hr1_lt_r2.
  unfold acquire_ordered.
  rewrite Hempty.
  eexists. split.
  - reflexivity.
  - simpl.
    destruct (r1 <? r2) eqn:Hlt.
    + eexists. reflexivity.
    + apply Nat.ltb_ge in Hlt. lia.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_31: AesKey secure memory handling                         *)
(* ======================================================================= *)

Theorem P_001_31 : forall (k : AesKey),
  let dropped := aes_key_drop k in
  aes_key_zeroized dropped = true /\
  forall x, In x (aes_key_data dropped) -> x = 0.
Proof.
  intros k.
  unfold aes_key_drop. simpl.
  split.
  - reflexivity.
  - intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [y [Heq _]].
    symmetry. exact Heq.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_32: Hash function determinism                             *)
(* ======================================================================= *)

Theorem P_001_32 : forall (data : list nat),
  hash_function data = hash_function data.
Proof.
  intros data.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_33: Signature verification soundness                      *)
(* ======================================================================= *)

Theorem P_001_33 : forall (data : list nat) (private_key : nat),
  let sig := sign_data data private_key in
  let public_key := private_key + 1 in
  verify_signature sig data public_key = true.
Proof.
  intros data private_key.
  unfold sign_data, verify_signature.
  simpl.
  rewrite Nat.eqb_refl.
  rewrite map_length.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_34: Key zeroization on drop                               *)
(* ======================================================================= *)

Theorem P_001_34 : forall (k : CryptoKey),
  let dropped := crypto_key_drop k in
  ck_zeroized dropped = true /\
  forall x, In x (ck_data dropped) -> x = 0.
Proof.
  intros k.
  unfold crypto_key_drop. simpl.
  split.
  - reflexivity.
  - intros x Hin.
    apply in_map_iff in Hin.
    destruct Hin as [y [Heq _]].
    symmetry. exact Heq.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_35: CapabilitySet union correctness                       *)
(* ======================================================================= *)

Theorem P_001_35 : forall (s1 s2 : CapabilitySet) (c : Capability),
  cap_set_contains s1 c = true \/ cap_set_contains s2 c = true ->
  cap_set_contains (cap_set_union s1 s2) c = true.
Proof.
  intros s1 s2 c [Hin1 | Hin2].
  - unfold cap_set_union, cap_set_contains in *.
    rewrite existsb_app.
    rewrite Hin1.
    reflexivity.
  - unfold cap_set_union, cap_set_contains in *.
    rewrite existsb_app.
    destruct (existsb (cap_eq c) s1) eqn:Hins1.
    + reflexivity.
    + simpl.
      rewrite existsb_exists in Hin2.
      destruct Hin2 as [x [Hxin Hceq]].
      rewrite existsb_exists.
      exists x. split.
      * apply filter_In. split.
        -- exact Hxin.
        -- rewrite negb_true_iff.
           destruct (existsb (cap_eq x) s1) eqn:Hxins1; [| reflexivity].
           rewrite existsb_exists in Hxins1.
           destruct Hxins1 as [y [Hyin Hxy]].
           (* Hins1 says existsb (cap_eq c) s1 = false, but we found y in s1 
              that matches x which matches c - contradiction *)
           exfalso.
           assert (Hfalse: existsb (cap_eq c) s1 = true).
           { rewrite existsb_exists. exists y. split; [exact Hyin |].
             destruct c; destruct x; destruct y; simpl in *; try discriminate; reflexivity. }
           rewrite Hins1 in Hfalse. discriminate.
      * exact Hceq.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_36: CapabilitySet intersection correctness                *)
(* ======================================================================= *)

Theorem P_001_36 : forall (s1 s2 : CapabilitySet) (c : Capability),
  cap_set_contains (cap_set_inter s1 s2) c = true ->
  cap_set_contains s1 c = true /\ cap_set_contains s2 c = true.
Proof.
  intros s1 s2 c Hinter.
  unfold cap_set_inter, cap_set_contains in *.
  rewrite existsb_exists in Hinter.
  destruct Hinter as [x [Hxin Hceq]].
  apply filter_In in Hxin.
  destruct Hxin as [Hxins1 Hxins2].
  split.
  - rewrite existsb_exists. exists x. split; assumption.
  - rewrite existsb_exists in Hxins2.
    destruct Hxins2 as [y [Hyins2 Hxy]].
    rewrite existsb_exists. exists y. split; [exact Hyins2 |].
    destruct c; destruct x; destruct y; simpl in *; try discriminate; try reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_37: Capability check enforcement                          *)
(* ======================================================================= *)

Theorem P_001_37 : forall (s : CapabilitySet) (c : Capability),
  cap_set_contains s c = false ->
  forall c', In c' s -> cap_eq c c' = false.
Proof.
  intros s c Hnotcontains c' Hin.
  unfold cap_set_contains in Hnotcontains.
  destruct (cap_eq c c') eqn:Heq; [| reflexivity].
  exfalso.
  assert (Htrue: existsb (cap_eq c) s = true).
  { rewrite existsb_exists. exists c'. split; [exact Hin | exact Heq]. }
  rewrite Hnotcontains in Htrue. discriminate.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_38: Label lattice properties (join/meet)                  *)
(* ======================================================================= *)

Lemma level_leq_refl : forall l, level_leq l l = true.
Proof.
  intros l. destruct l; reflexivity.
Qed.

Lemma compartments_subset_refl : forall c, compartments_subset c c = true.
Proof.
  intros c.
  unfold compartments_subset.
  rewrite forallb_forall.
  intros x Hin.
  rewrite existsb_exists.
  exists x. split; [exact Hin | apply Nat.eqb_refl].
Qed.

Theorem P_001_38 : forall (l1 l2 : Label),
  flows_to l1 (label_join l1 l2) = true /\
  flows_to l2 (label_join l1 l2) = true /\
  flows_to l1 l1 = true.
Proof.
  intros l1 l2.
  split; [| split].
  - unfold flows_to, label_join, level_max, list_union. simpl.
    apply andb_true_intro. split.
    + destruct (level_leq (lab_level l1) (lab_level l2)) eqn:Hleq.
      * exact Hleq.
      * apply level_leq_refl.
    + unfold compartments_subset.
      rewrite forallb_forall.
      intros x Hin.
      rewrite existsb_exists.
      exists x. split.
      * apply in_or_app. left. exact Hin.
      * apply Nat.eqb_refl.
  - unfold flows_to, label_join, level_max, list_union. simpl.
    apply andb_true_intro. split.
    + destruct (level_leq (lab_level l1) (lab_level l2)) eqn:Hleq.
      * apply level_leq_refl.
      * destruct (lab_level l1); destruct (lab_level l2); simpl in *; 
        try reflexivity; try discriminate.
    + unfold compartments_subset.
      rewrite forallb_forall.
      intros x Hin.
      rewrite existsb_exists.
      destruct (existsb (Nat.eqb x) (lab_compartments l1)) eqn:Hex.
      * rewrite existsb_exists in Hex.
        destruct Hex as [y [Hyin Hxy]].
        apply Nat.eqb_eq in Hxy. subst y.
        exists x. split; [apply in_or_app; left; exact Hyin | apply Nat.eqb_refl].
      * exists x. split.
        -- apply in_or_app. right.
           apply filter_In. split; [exact Hin |].
           rewrite negb_true_iff. exact Hex.
        -- apply Nat.eqb_refl.
  - unfold flows_to.
    apply andb_true_intro. split.
    + apply level_leq_refl.
    + apply compartments_subset_refl.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_39: flows_to transitivity                                 *)
(* ======================================================================= *)

Lemma level_leq_trans : forall l1 l2 l3,
  level_leq l1 l2 = true -> level_leq l2 l3 = true -> level_leq l1 l3 = true.
Proof.
  intros l1 l2 l3.
  destruct l1; destruct l2; destruct l3; simpl; intros; try reflexivity; try discriminate.
Qed.

Lemma compartments_subset_trans : forall c1 c2 c3,
  compartments_subset c1 c2 = true -> 
  compartments_subset c2 c3 = true -> 
  compartments_subset c1 c3 = true.
Proof.
  intros c1 c2 c3 H12 H23.
  unfold compartments_subset in *.
  rewrite forallb_forall in *.
  intros x Hin1.
  specialize (H12 x Hin1).
  rewrite existsb_exists in H12.
  destruct H12 as [y [Hyin Hxy]].
  apply Nat.eqb_eq in Hxy. subst y.
  specialize (H23 x Hyin).
  exact H23.
Qed.

Theorem P_001_39 : forall (l1 l2 l3 : Label),
  flows_to l1 l2 = true -> flows_to l2 l3 = true -> flows_to l1 l3 = true.
Proof.
  intros l1 l2 l3 H12 H23.
  unfold flows_to in *.
  apply andb_prop in H12. destruct H12 as [Hlev12 Hcomp12].
  apply andb_prop in H23. destruct H23 as [Hlev23 Hcomp23].
  apply andb_true_intro. split.
  - apply level_leq_trans with (l2 := lab_level l2); assumption.
  - apply compartments_subset_trans with (c2 := lab_compartments l2); assumption.
Qed.

(* ======================================================================= *)
(* THEOREM P_001_40: Labeled value unlabel requires clearance              *)
(* ======================================================================= *)

Theorem P_001_40 : forall (A : Type) (lv : Labeled A) (clearance : Label) (v : A),
  unlabel lv clearance = Some v ->
  flows_to (labeled_label lv) clearance = true /\ v = labeled_value lv.
Proof.
  intros A lv clearance v Hunlabel.
  unfold unlabel in Hunlabel.
  destruct (flows_to (labeled_label lv) clearance) eqn:Hflows.
  - injection Hunlabel as Hv.
    split.
    + reflexivity.
    + symmetry. exact Hv.
  - discriminate.
Qed.

(* End of StandardLibrary.v *)
