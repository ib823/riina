(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* FFIAttackResearch.v - RIINA FFI & Attack Surface Research *)
(* Spec: 01_RESEARCH/12_DOMAIN_L_FFI_AND_ATTACK_RESEARCH/ *)
(* Zero admits, zero axioms *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(** ═══════════════════════════════════════════════════════════════════════════
    FFI TYPE REPRESENTATIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive FFIType : Type :=
  | FFI_Int8   : FFIType
  | FFI_Int16  : FFIType
  | FFI_Int32  : FFIType
  | FFI_Int64  : FFIType
  | FFI_Ptr    : FFIType -> FFIType
  | FFI_Array  : FFIType -> nat -> FFIType
  | FFI_Struct : list FFIType -> FFIType
  | FFI_Void   : FFIType.

(* Size in bytes of an FFI type *)
Fixpoint ffi_type_size (t : FFIType) : nat :=
  match t with
  | FFI_Int8         => 1
  | FFI_Int16        => 2
  | FFI_Int32        => 4
  | FFI_Int64        => 8
  | FFI_Ptr _        => 8
  | FFI_Array elem n => n * ffi_type_size elem
  | FFI_Struct fields => fold_left (fun acc f => acc + ffi_type_size f) fields 0
  | FFI_Void         => 0
  end.

(* Alignment requirement *)
Fixpoint ffi_type_align (t : FFIType) : nat :=
  match t with
  | FFI_Int8         => 1
  | FFI_Int16        => 2
  | FFI_Int32        => 4
  | FFI_Int64        => 8
  | FFI_Ptr _        => 8
  | FFI_Array elem _ => ffi_type_align elem
  | FFI_Struct []    => 1
  | FFI_Struct (f :: _) => ffi_type_align f
  | FFI_Void         => 1
  end.

(** ═══════════════════════════════════════════════════════════════════════════
    FFI CALL DESCRIPTOR & VALIDATION
    ═══════════════════════════════════════════════════════════════════════════ *)

Record FFICallDescriptor : Type := mkFFICall {
  ffi_name        : nat;        (* function id *)
  ffi_params      : list FFIType;
  ffi_return      : FFIType;
  ffi_sandboxed   : bool;
  ffi_validated   : bool;
}.

(* An FFI call is safe if it is both sandboxed and validated *)
Definition ffi_call_safe (call : FFICallDescriptor) : bool :=
  ffi_sandboxed call && ffi_validated call.

(** ═══════════════════════════════════════════════════════════════════════════
    MEMORY REGION & SANDBOX MODEL
    ═══════════════════════════════════════════════════════════════════════════ *)

Record MemRegion : Type := mkMemRegion {
  region_base : nat;
  region_size : nat;
  region_owner : nat;   (* sandbox id *)
}.

Definition regions_disjoint (r1 r2 : MemRegion) : Prop :=
  region_base r1 + region_size r1 <= region_base r2 \/
  region_base r2 + region_size r2 <= region_base r1.

Definition addr_in_region (addr size : nat) (r : MemRegion) : Prop :=
  region_base r <= addr /\ addr + size <= region_base r + region_size r.

Record Sandbox : Type := mkSandbox {
  sandbox_id      : nat;
  sandbox_region  : MemRegion;
  sandbox_active  : bool;
  allowed_calls   : list nat;   (* allowed FFI function ids *)
}.

Definition call_allowed (sb : Sandbox) (call_id : nat) : bool :=
  existsb (Nat.eqb call_id) (allowed_calls sb).

(** ═══════════════════════════════════════════════════════════════════════════
    TYPE MARSHALLING
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Buffer for marshalling *)
Record MarshalBuffer : Type := mkMarshalBuffer {
  buf_capacity : nat;
  buf_used     : nat;
}.

Definition buf_remaining (b : MarshalBuffer) : nat :=
  buf_capacity b - buf_used b.

Definition can_marshal (b : MarshalBuffer) (t : FFIType) : bool :=
  buf_used b + ffi_type_size t <=? buf_capacity b.

(* Marshalling result *)
Definition marshal_into (b : MarshalBuffer) (t : FFIType) : option MarshalBuffer :=
  if can_marshal b t then
    Some (mkMarshalBuffer (buf_capacity b) (buf_used b + ffi_type_size t))
  else
    None.

(** ═══════════════════════════════════════════════════════════════════════════
    THEOREMS: FFI CALL VALIDATION
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem ffi_safe_implies_sandboxed :
  forall call, ffi_call_safe call = true -> ffi_sandboxed call = true.
Proof.
  intros call H. unfold ffi_call_safe in H.
  apply andb_true_iff in H. destruct H. assumption.
Qed.

Theorem ffi_safe_implies_validated :
  forall call, ffi_call_safe call = true -> ffi_validated call = true.
Proof.
  intros call H. unfold ffi_call_safe in H.
  apply andb_true_iff in H. destruct H. assumption.
Qed.

Theorem ffi_safe_construct :
  forall call,
    ffi_sandboxed call = true ->
    ffi_validated call = true ->
    ffi_call_safe call = true.
Proof.
  intros call Hs Hv. unfold ffi_call_safe.
  rewrite Hs, Hv. reflexivity.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    THEOREMS: TYPE ALIGNMENT
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem int8_alignment_positive :
  ffi_type_align FFI_Int8 = 1.
Proof.
  reflexivity.
Qed.

Lemma ffi_type_align_ge_1 :
  forall t, ffi_type_align t >= 1.
Proof.
  fix IH 1. intro t. destruct t; simpl; try lia.
  - apply IH.
  - destruct l; [lia | apply IH].
Qed.

Theorem ptr_size_constant :
  forall t, ffi_type_size (FFI_Ptr t) = 8.
Proof.
  intro t. reflexivity.
Qed.

Theorem array_size_correct :
  forall elem n, ffi_type_size (FFI_Array elem n) = n * ffi_type_size elem.
Proof.
  intros. reflexivity.
Qed.

Theorem empty_struct_zero_size :
  ffi_type_size (FFI_Struct []) = 0.
Proof.
  reflexivity.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    THEOREMS: BUFFER SIZE BOUNDS & MARSHALLING
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem marshal_preserves_capacity :
  forall b t b',
    marshal_into b t = Some b' ->
    buf_capacity b' = buf_capacity b.
Proof.
  intros b t b' H. unfold marshal_into in H.
  destruct (can_marshal b t) eqn:E; [|discriminate].
  injection H as <-. reflexivity.
Qed.

Theorem marshal_increases_used :
  forall b t b',
    marshal_into b t = Some b' ->
    buf_used b' = buf_used b + ffi_type_size t.
Proof.
  intros b t b' H. unfold marshal_into in H.
  destruct (can_marshal b t) eqn:E; [|discriminate].
  injection H as <-. reflexivity.
Qed.

Theorem marshal_never_overflows :
  forall b t b',
    marshal_into b t = Some b' ->
    buf_used b' <= buf_capacity b'.
Proof.
  intros b t b' H.
  unfold marshal_into in H.
  destruct (can_marshal b t) eqn:E; [|discriminate].
  injection H as <-. simpl.
  unfold can_marshal in E.
  apply Nat.leb_le in E. lia.
Qed.

Theorem marshal_failure_means_insufficient :
  forall b t,
    marshal_into b t = None ->
    buf_capacity b < buf_used b + ffi_type_size t.
Proof.
  intros b t H. unfold marshal_into in H.
  destruct (can_marshal b t) eqn:E; [discriminate|].
  unfold can_marshal in E.
  apply Nat.leb_nle in E. lia.
Qed.

Theorem marshal_void_always_succeeds :
  forall b,
    buf_used b <= buf_capacity b ->
    exists b', marshal_into b FFI_Void = Some b'.
Proof.
  intros b Hle. unfold marshal_into. simpl.
  unfold can_marshal. simpl.
  assert (buf_used b + 0 <=? buf_capacity b = true) as ->.
  { apply Nat.leb_le. lia. }
  eexists. reflexivity.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    THEOREMS: SANDBOX ESCAPE PREVENTION & MEMORY ISOLATION
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem disjoint_regions_no_overlap :
  forall r1 r2 addr sz,
    regions_disjoint r1 r2 ->
    addr_in_region addr sz r1 ->
    sz > 0 ->
    ~ addr_in_region addr sz r2.
Proof.
  intros r1 r2 addr sz Hdisj Hin1 Hsz Hin2.
  unfold regions_disjoint in Hdisj.
  unfold addr_in_region in *.
  destruct Hin1 as [H1a H1b].
  destruct Hin2 as [H2a H2b].
  destruct Hdisj as [Hd | Hd]; lia.
Qed.

Theorem sandbox_call_allowed_decidable :
  forall sb cid, call_allowed sb cid = true \/ call_allowed sb cid = false.
Proof.
  intros. destruct (call_allowed sb cid); auto.
Qed.

Theorem disjoint_symmetric :
  forall r1 r2, regions_disjoint r1 r2 -> regions_disjoint r2 r1.
Proof.
  intros r1 r2 H. unfold regions_disjoint in *.
  destruct H; [right | left]; assumption.
Qed.

Theorem addr_in_region_bounds :
  forall addr sz r,
    addr_in_region addr sz r ->
    addr >= region_base r /\ addr + sz <= region_base r + region_size r.
Proof.
  intros addr sz r [H1 H2]. split; lia.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    THEOREMS: ADDITIONAL FFI PROPERTIES
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem ffi_void_size_zero :
  ffi_type_size FFI_Void = 0.
Proof.
  reflexivity.
Qed.

Theorem ffi_int8_size :
  ffi_type_size FFI_Int8 = 1.
Proof.
  reflexivity.
Qed.

Theorem marshal_void_preserves_used :
  forall b b',
    buf_used b <= buf_capacity b ->
    marshal_into b FFI_Void = Some b' ->
    buf_used b' = buf_used b.
Proof.
  intros b b' Hle H.
  unfold marshal_into in H.
  unfold can_marshal in H. simpl in H.
  assert (buf_used b + 0 <=? buf_capacity b = true) as E.
  { apply Nat.leb_le. lia. }
  rewrite E in H.
  injection H as <-.
  simpl. lia.
Qed.
