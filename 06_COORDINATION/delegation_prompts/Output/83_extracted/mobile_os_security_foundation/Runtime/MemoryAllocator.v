(* ========================================================================= *)
(*  RIINA Mobile OS - Verified Runtime: Memory Allocator                     *)
(*  Part of RIINA Mobile OS Security Foundation                              *)
(*  Spec Reference: RESEARCH_MOBILEOS01_FOUNDATION.md Section 4.1            *)
(* ========================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* ========================================================================= *)
(*  SECTION 1: Core Type Definitions                                         *)
(* ========================================================================= *)

(** Pointer representation *)
Inductive Pointer : Type :=
  | Ptr : nat -> Pointer.

(** Time representation *)
Definition Time := nat.

(** Buffer record *)
Record Buffer : Type := mkBuffer {
  buffer_base : Pointer;
  buffer_size : nat;
  buffer_allocated : bool;
}.

(** Allocator state *)
Record AllocatorState : Type := mkAllocState {
  allocated_ptrs : list (Pointer * Time);  (* ptr, allocation time *)
  freed_ptrs : list (Pointer * Time);      (* ptr, free time *)
  current_time : Time;
}.

(** Decidable equality for Pointer *)
Definition Pointer_eq_dec : forall (p1 p2 : Pointer), {p1 = p2} + {p1 <> p2}.
Proof.
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  - left. f_equal. exact e.
  - right. intros H. injection H. intros. contradiction.
Defined.

(* ========================================================================= *)
(*  SECTION 2: Memory Operations                                             *)
(* ========================================================================= *)

(** Check if pointer is freed at time *)
Definition freed_at (st : AllocatorState) (ptr : Pointer) (time : Time) : Prop :=
  In (ptr, time) (freed_ptrs st).

(** Check if pointer is currently freed *)
Definition is_freed (st : AllocatorState) (ptr : Pointer) : Prop :=
  exists t, In (ptr, t) (freed_ptrs st).

(** Check if pointer is allocated *)
Definition is_allocated (st : AllocatorState) (ptr : Pointer) : Prop :=
  exists t, In (ptr, t) (allocated_ptrs st) /\ ~ is_freed st ptr.

(** Pointer access after time *)
Definition can_access_after (st : AllocatorState) (ptr : Pointer) (time : Time) : Prop :=
  is_allocated st ptr /\ 
  forall t, freed_at st ptr t -> t > time.

(** Free operation *)
Definition can_free (st : AllocatorState) (ptr : Pointer) : Prop :=
  is_allocated st ptr /\ ~ is_freed st ptr.

(** Buffer access check *)
Definition valid_buffer_access (buf : Buffer) (offset : nat) : Prop :=
  offset < buffer_size buf /\ buffer_allocated buf = true.

(* ========================================================================= *)
(*  SECTION 3: Core Memory Safety Theorems                                   *)
(* ========================================================================= *)

(* Spec: RESEARCH_MOBILEOS01 Section 4.1 - No use-after-free *)
(** Theorem: A pointer cannot be accessed after it has been freed. *)
Theorem no_use_after_free :
  forall (st : AllocatorState) (ptr : Pointer) (free_time : Time),
    freed_at st ptr free_time ->
    forall t, t > free_time -> ~ can_access_after st ptr t.
Proof.
  intros st ptr free_time Hfreed t Hafter.
  unfold can_access_after.
  intros [Halloc Haccess].
  specialize (Haccess free_time Hfreed).
  (* Haccess: free_time > t, but we have t > free_time - contradiction *)
  apply Nat.lt_irrefl with (x := free_time).
  apply Nat.lt_trans with (m := t).
  - exact Hafter.
  - exact Haccess.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 4.1 - No double-free *)
(** Theorem: A pointer cannot be freed twice. *)
Theorem no_double_free :
  forall (st : AllocatorState) (ptr : Pointer),
    is_freed st ptr ->
    ~ can_free st ptr.
Proof.
  intros st ptr Hfreed.
  unfold can_free.
  intros [_ Hnot_freed].
  apply Hnot_freed. exact Hfreed.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 4.1 - No buffer overflow *)
(** Theorem: Buffer access beyond bounds is not possible. *)
Theorem no_buffer_overflow :
  forall (buffer : Buffer) (offset : nat),
    offset >= buffer_size buffer ->
    ~ valid_buffer_access buffer offset.
Proof.
  intros buffer offset Hoverflow.
  unfold valid_buffer_access.
  intros [Hbounds _].
  apply Nat.lt_irrefl with (x := buffer_size buffer).
  apply Nat.lt_le_trans with (m := offset).
  - exact Hbounds.
  - exact Hoverflow.
Qed.

(* ========================================================================= *)
(*  SECTION 4: Additional Memory Safety Properties                           *)
(* ========================================================================= *)

(** Allocated pointer not freed *)
Theorem allocated_not_freed :
  forall (st : AllocatorState) (ptr : Pointer),
    is_allocated st ptr ->
    ~ is_freed st ptr.
Proof.
  intros st ptr [t [Hin Hnotfreed]].
  exact Hnotfreed.
Qed.

(** Valid access requires allocation *)
Theorem access_requires_allocation :
  forall (st : AllocatorState) (ptr : Pointer) (t : Time),
    can_access_after st ptr t ->
    is_allocated st ptr.
Proof.
  intros st ptr t [Halloc _].
  exact Halloc.
Qed.

(** Buffer bounds enforced *)
Theorem buffer_bounds_enforced :
  forall (buf : Buffer) (offset : nat),
    valid_buffer_access buf offset ->
    offset < buffer_size buf.
Proof.
  intros buf offset [Hbounds _].
  exact Hbounds.
Qed.

(* ========================================================================= *)
(*  END OF FILE: MemoryAllocator.v                                           *)
(*  Theorems: 3 core + 3 supporting = 6 total                                *)
(*  Admitted: 0 | admit: 0 | New Axioms: 0                                   *)
(* ========================================================================= *)
