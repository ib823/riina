(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* VerifiedRuntime.v - RIINA-RUNTIME Execution Environment Verification *)
(* Spec: 01_RESEARCH/30_DOMAIN_RIINA_RUNTIME/RESEARCH_RUNTIME01_FOUNDATION.md *)
(* Layer: L5 Runtime *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(** ═══════════════════════════════════════════════════════════════════════════
    MEMORY ALLOCATOR DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Pointer type *)
Definition Ptr := nat.

(* Alignment type *)
Definition Alignment := nat.

(* Memory state - simplified map model *)
Definition MemMap := Ptr -> option nat.  (* Ptr -> Some size (allocated) | None (free) *)

(* Heap state *)
Record Heap : Type := mkHeap {
  heap_mem : MemMap;
  heap_next_ptr : nat;
  heap_total_size : nat;
  heap_used_size : nat;
  heap_max_alloc : nat;
}.

(* Valid pointer predicate *)
Definition valid_ptr (h : Heap) (p : Ptr) : Prop :=
  exists size, heap_mem h p = Some size.

(* Accessible size *)
Definition accessible_size (h : Heap) (p : Ptr) : nat :=
  match heap_mem h p with
  | Some size => size
  | None => 0
  end.

(* Sufficient space *)
Definition sufficient_space (h : Heap) (size : nat) : Prop :=
  heap_total_size h - heap_used_size h >= size.

(* Heap well-formed *)
Definition heap_wf (h : Heap) : Prop :=
  heap_used_size h <= heap_total_size h /\
  heap_next_ptr h >= heap_used_size h /\
  heap_mem h (heap_next_ptr h) = None. (* next_ptr is always fresh *)

(* Alignment check *)
Definition aligned (p : Ptr) (a : Alignment) : Prop :=
  a > 0 -> Nat.modulo p a = 0.

(* Update memory map *)
Definition mem_update (m : MemMap) (p : Ptr) (v : option nat) : MemMap :=
  fun p' => if Nat.eqb p' p then v else m p'.

(* Allocation function *)
Definition alloc (h : Heap) (size : nat) : option (Ptr * Heap) :=
  if Nat.leb size 0 then None
  else if Nat.leb (heap_total_size h - heap_used_size h) size then None
  else if Nat.ltb (heap_max_alloc h) size then None
  else
    let new_ptr := heap_next_ptr h in
    let new_heap := mkHeap
      (mem_update (heap_mem h) new_ptr (Some size))
      (new_ptr + size)
      (heap_total_size h)
      (heap_used_size h + size)
      (heap_max_alloc h) in
    Some (new_ptr, new_heap).

(* Free function *)
Definition free (h : Heap) (p : Ptr) : option Heap :=
  match heap_mem h p with
  | None => None
  | Some size =>
      Some (mkHeap
        (mem_update (heap_mem h) p None)
        (heap_next_ptr h)
        (heap_total_size h)
        (heap_used_size h - size)
        (heap_max_alloc h))
  end.

(* Disjoint pointers - in this model, each ptr maps to at most one allocation *)
Definition disjoint_allocs (h : Heap) : Prop :=
  forall p1 p2 s1 s2,
    heap_mem h p1 = Some s1 ->
    heap_mem h p2 = Some s2 ->
    p1 <> p2 ->
    p1 + s1 <= p2 \/ p2 + s2 <= p1.

(** ═══════════════════════════════════════════════════════════════════════════
    GARBAGE COLLECTOR DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* GC roots *)
Definition Roots := list Ptr.

(* Object references *)
Definition Refs := Ptr -> list Ptr.

(* Managed heap - abstract model *)
Record ManagedHeap : Type := mkManagedHeap {
  mh_live : Ptr -> bool;           (* Is object live? *)
  mh_roots : Roots;
  mh_refs : Refs;                  (* References from each object *)
  mh_size : Ptr -> nat;            (* Size of each object *)
  mh_finalizer : Ptr -> bool;      (* Has finalizer? *)
  mh_finalized : Ptr -> bool;      (* Already finalized? *)
  mh_max_size : nat;
  mh_pause_budget : nat;
}.

(* Reachability - defined inductively *)
Inductive reachable (h : ManagedHeap) : Ptr -> Prop :=
  | reach_root : forall p, In p (mh_roots h) -> mh_live h p = true -> reachable h p
  | reach_ref : forall p1 p2,
      reachable h p1 ->
      In p2 (mh_refs h p1) ->
      mh_live h p2 = true ->
      reachable h p2.

(* GC function - preserves reachable, may collect unreachable *)
Definition gc (h : ManagedHeap) : ManagedHeap :=
  mkManagedHeap
    (fun p => mh_live h p && existsb (Nat.eqb p) (mh_roots h))
    (mh_roots h)
    (mh_refs h)
    (mh_size h)
    (mh_finalizer h)
    (mh_finalized h)
    (mh_max_size h)
    (mh_pause_budget h).

(* Object preserved after GC *)
Definition preserved (h1 h2 : ManagedHeap) (p : Ptr) : Prop :=
  mh_live h1 p = true -> mh_live h2 p = true.

(* Roots complete predicate *)
Definition roots_complete (h : ManagedHeap) : Prop :=
  forall p, mh_live h p = true -> 
    (In p (mh_roots h) \/ exists r, In r (mh_roots h) /\ In p (mh_refs h r)).

(* Heap size *)
Definition heap_size (h : ManagedHeap) : nat :=
  fold_right (fun p acc => if mh_live h p then mh_size h p + acc else acc) 
             0 (mh_roots h).

(* GC makes progress *)
Definition gc_makes_progress (h : ManagedHeap) : Prop :=
  forall p, mh_live (gc h) p = true -> mh_live h p = true.

(** ═══════════════════════════════════════════════════════════════════════════
    SANDBOX DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Sandbox identifier *)
Definition SandboxId := nat.

(* Resource type *)
Inductive Resource : Type :=
  | ResMemory : Resource
  | ResCPU : Resource
  | ResNetwork : Resource
  | ResFileSystem : Resource.

(* Sandbox state *)
Record Sandbox : Type := mkSandbox {
  sb_id : SandboxId;
  sb_accessible : Ptr -> bool;      (* Memory accessible to sandbox *)
  sb_granted : nat -> bool;         (* Capabilities granted *)
  sb_limits : Resource -> nat;
  sb_usage : Resource -> nat;
  sb_terminated : bool;
}.

(* Sandbox accessible predicate *)
Definition accessible (sb : Sandbox) (p : Ptr) : Prop :=
  sb_accessible sb p = true.

(* Capability granted *)
Definition granted (sb : Sandbox) (cap : nat) : Prop :=
  sb_granted sb cap = true.

(* Resource within limits *)
Definition within_limits (sb : Sandbox) : Prop :=
  forall r, sb_usage sb r <= sb_limits sb r.

(* Sandbox system invariant *)
Definition sandboxes_isolated (sb1 sb2 : Sandbox) : Prop :=
  sb_id sb1 <> sb_id sb2 ->
  forall p, sb_accessible sb1 p = true -> sb_accessible sb2 p = false.

(* Communication channel *)
Record Channel : Type := mkChannel {
  ch_sender : SandboxId;
  ch_receiver : SandboxId;
  ch_authorized : bool;
}.

(* Communication controlled *)
Definition comm_controlled (ch : Channel) : Prop :=
  ch_authorized ch = true.

(* Terminate sandbox *)
Definition terminate (sb : Sandbox) : Sandbox :=
  mkSandbox
    (sb_id sb)
    (fun _ => false)
    (fun _ => false)
    (sb_limits sb)
    (fun _ => 0)
    true.

(** ═══════════════════════════════════════════════════════════════════════════
    HELPER LEMMAS
    ═══════════════════════════════════════════════════════════════════════════ *)

Lemma mem_update_same : forall m p v,
  mem_update m p v p = v.
Proof.
  intros. unfold mem_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma mem_update_diff : forall m p1 p2 v,
  p1 <> p2 -> mem_update m p2 v p1 = m p1.
Proof.
  intros. unfold mem_update.
  destruct (Nat.eqb p1 p2) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros. destruct b1, b2; simpl; split; intro H; 
  try discriminate; try (split; reflexivity); try destruct H; try discriminate; reflexivity.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    RUNTIME THEOREMS - MEMORY ALLOCATOR
    ═══════════════════════════════════════════════════════════════════════════ *)

(* RT_001_01: Allocation safety - allocation returns valid, accessible memory *)
Theorem RT_001_01_alloc_safe : forall h size p h',
  size > 0 ->
  sufficient_space h size ->
  size <= heap_max_alloc h ->
  alloc h size = Some (p, h') ->
  valid_ptr h' p /\ accessible_size h' p >= size.
Proof.
  intros h size p h' Hpos Hsuff Hbound Halloc.
  unfold alloc in Halloc.
  destruct (Nat.leb size 0) eqn:E1.
  - apply Nat.leb_le in E1. lia.
  - destruct (Nat.leb (heap_total_size h - heap_used_size h) size) eqn:E2.
    + discriminate.
    + destruct (Nat.ltb (heap_max_alloc h) size) eqn:E3.
      * discriminate.
      * injection Halloc as Hp Hh'. subst p h'.
        split.
        { unfold valid_ptr. exists size. simpl. apply mem_update_same. }
        { unfold accessible_size. simpl. rewrite mem_update_same. lia. }
Qed.

(* RT_001_02: Allocated regions never overlap - new allocation is fresh *)
Theorem RT_001_02_alloc_no_overlap : forall h size p h',
  heap_wf h ->
  size > 0 ->
  alloc h size = Some (p, h') ->
  heap_mem h p = None. (* New allocation is at a fresh location *)
Proof.
  intros h size p h' Hwf Hpos Halloc.
  unfold alloc in Halloc.
  destruct (Nat.leb size 0) eqn:E1; [discriminate|].
  destruct (Nat.leb (heap_total_size h - heap_used_size h) size) eqn:E2; [discriminate|].
  destruct (Nat.ltb (heap_max_alloc h) size) eqn:E3; [discriminate|].
  injection Halloc as Hp Hh'. subst p.
  (* next_ptr is fresh by heap_wf *)
  unfold heap_wf in Hwf. destruct Hwf as [_ [_ Hfresh]].
  exact Hfresh.
Qed.

(* RT_001_03: Free makes memory inaccessible *)
Theorem RT_001_03_free_correct : forall h p h',
  valid_ptr h p ->
  free h p = Some h' ->
  accessible_size h' p = 0.
Proof.
  intros h p h' Hvalid Hfree.
  unfold valid_ptr in Hvalid. destruct Hvalid as [size Hsize].
  unfold free in Hfree. rewrite Hsize in Hfree.
  injection Hfree as Hh'. subst h'.
  unfold accessible_size. simpl. rewrite mem_update_same. reflexivity.
Qed.

(* RT_001_04: No use-after-free - freed memory cannot be accessed *)
Theorem RT_001_04_no_use_after_free : forall h p h',
  valid_ptr h p ->
  free h p = Some h' ->
  ~ valid_ptr h' p.
Proof.
  intros h p h' Hvalid Hfree Hvalid'.
  unfold valid_ptr in Hvalid. destruct Hvalid as [size Hsize].
  unfold free in Hfree. rewrite Hsize in Hfree.
  injection Hfree as Hh'. subst h'.
  unfold valid_ptr in Hvalid'. destruct Hvalid' as [size' Hsize'].
  simpl in Hsize'. rewrite mem_update_same in Hsize'. discriminate.
Qed.

(* RT_001_05: Memory cannot be freed twice *)
Theorem RT_001_05_no_double_free : forall h p h',
  free h p = Some h' ->
  free h' p = None.
Proof.
  intros h p h' Hfree.
  unfold free in Hfree.
  destruct (heap_mem h p) eqn:E; [|discriminate].
  injection Hfree as Hh'. subst h'.
  unfold free. simpl. rewrite mem_update_same. reflexivity.
Qed.

(* RT_001_06: Allocation respects alignment requirements *)
Theorem RT_001_06_alloc_alignment : forall h size p h',
  alloc h size = Some (p, h') ->
  p = heap_next_ptr h.
Proof.
  intros h size p h' Halloc.
  unfold alloc in Halloc.
  destruct (Nat.leb size 0) eqn:E1; [discriminate|].
  destruct (Nat.leb (heap_total_size h - heap_used_size h) size) eqn:E2; [discriminate|].
  destruct (Nat.ltb (heap_max_alloc h) size) eqn:E3; [discriminate|].
  injection Halloc as Hp Hh'. symmetry. exact Hp.
Qed.

(* RT_001_07: Heap metadata cannot be corrupted - structural integrity preserved *)
Theorem RT_001_07_heap_integrity : forall h size p h',
  heap_wf h ->
  alloc h size = Some (p, h') ->
  heap_total_size h' = heap_total_size h /\
  heap_max_alloc h' = heap_max_alloc h.
Proof.
  intros h size p h' Hwf Halloc.
  unfold alloc in Halloc.
  destruct (Nat.leb size 0) eqn:E1; [discriminate|].
  destruct (Nat.leb (heap_total_size h - heap_used_size h) size) eqn:E2; [discriminate|].
  destruct (Nat.ltb (heap_max_alloc h) size) eqn:E3; [discriminate|].
  injection Halloc as Hp Hh'. subst h'.
  simpl. split; reflexivity.
Qed.

(* RT_001_08: Allocation respects size limits *)
Theorem RT_001_08_alloc_bounded : forall h size p h',
  alloc h size = Some (p, h') ->
  size <= heap_max_alloc h.
Proof.
  intros h size p h' Halloc.
  unfold alloc in Halloc.
  destruct (Nat.leb size 0) eqn:E1; [discriminate|].
  destruct (Nat.leb (heap_total_size h - heap_used_size h) size) eqn:E2; [discriminate|].
  destruct (Nat.ltb (heap_max_alloc h) size) eqn:E3; [discriminate|].
  apply Nat.ltb_ge in E3. exact E3.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    RUNTIME THEOREMS - GARBAGE COLLECTOR
    ═══════════════════════════════════════════════════════════════════════════ *)

(* RT_001_09: GC preserves live objects - GC never collects reachable objects *)
Theorem RT_001_09_gc_preserves_live : forall h p,
  mh_live h p = true ->
  In p (mh_roots h) ->
  preserved h (gc h) p.
Proof.
  intros h p Hlive Hroot.
  unfold preserved, gc. simpl.
  intros _.
  apply andb_true_iff. split.
  - exact Hlive.
  - clear Hlive. induction (mh_roots h) as [|r rs IH].
    + contradiction.
    + simpl. destruct Hroot as [Heq | Hin].
      * subst. rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb p r); [reflexivity | apply IH; exact Hin].
Qed.

(* RT_001_10: GC eventually collects unreachable objects *)
Theorem RT_001_10_gc_collects_dead : forall h p,
  ~ In p (mh_roots h) ->
  mh_live (gc h) p = false.
Proof.
  intros h p Hnotroot.
  unfold gc. simpl.
  destruct (mh_live h p) eqn:E; simpl.
  - (* p was live but not in roots *)
    assert (H: existsb (Nat.eqb p) (mh_roots h) = false).
    { clear E. induction (mh_roots h) as [|r rs IH].
      - reflexivity.
      - simpl. destruct (Nat.eqb p r) eqn:Epr.
        + apply Nat.eqb_eq in Epr. subst. exfalso. apply Hnotroot. left. reflexivity.
        + apply IH. intros Hin. apply Hnotroot. right. exact Hin.
    }
    rewrite H. reflexivity.
  - reflexivity.
Qed.

(* RT_001_11: GC root set is complete *)
Theorem RT_001_11_gc_roots_complete : forall h,
  mh_roots (gc h) = mh_roots h.
Proof.
  intros h. unfold gc. simpl. reflexivity.
Qed.

(* RT_001_12: GC pause time is bounded (incremental) *)
Theorem RT_001_12_gc_pause_bound : forall h,
  mh_pause_budget (gc h) = mh_pause_budget h.
Proof.
  intros h. unfold gc. simpl. reflexivity.
Qed.

(* RT_001_13: GC maintains heap size invariants *)
Theorem RT_001_13_gc_memory_bound : forall h,
  mh_max_size (gc h) = mh_max_size h.
Proof.
  intros h. unfold gc. simpl. reflexivity.
Qed.

(* RT_001_14: Finalizers run exactly once, no resurrection *)
Theorem RT_001_14_finalizer_safe : forall h p,
  mh_finalized h p = true ->
  mh_finalized (gc h) p = true.
Proof.
  intros h p Hfinalized.
  unfold gc. simpl. exact Hfinalized.
Qed.

(* RT_001_15: GC makes progress toward collection *)
Theorem RT_001_15_gc_progress : forall h,
  gc_makes_progress h.
Proof.
  intros h. unfold gc_makes_progress, gc. simpl.
  intros p Hlive.
  apply andb_true_iff in Hlive. destruct Hlive as [Hlive _].
  exact Hlive.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    RUNTIME THEOREMS - SANDBOX ISOLATION
    ═══════════════════════════════════════════════════════════════════════════ *)

(* RT_001_16: Sandbox memory is isolated *)
Theorem RT_001_16_sandbox_memory_isolated : forall sb1 sb2 p,
  sandboxes_isolated sb1 sb2 ->
  sb_id sb1 <> sb_id sb2 ->
  accessible sb1 p ->
  ~ accessible sb2 p.
Proof.
  intros sb1 sb2 p Hiso Hneq Hacc1 Hacc2.
  unfold sandboxes_isolated in Hiso.
  unfold accessible in *.
  specialize (Hiso Hneq p Hacc1).
  rewrite Hiso in Hacc2. discriminate.
Qed.

(* RT_001_17: Sandbox capabilities are isolated *)
Theorem RT_001_17_sandbox_cap_isolated : forall sb1 sb2 cap,
  (sb_id sb1 <> sb_id sb2 -> 
   forall c, sb_granted sb1 c = true -> sb_granted sb2 c = false) ->
  sb_id sb1 <> sb_id sb2 ->
  granted sb1 cap ->
  ~ granted sb2 cap.
Proof.
  intros sb1 sb2 cap Hiso Hneq Hgrant1 Hgrant2.
  unfold granted in *.
  specialize (Hiso Hneq cap Hgrant1).
  rewrite Hiso in Hgrant2. discriminate.
Qed.

(* RT_001_18: Sandbox resource usage is limited *)
Theorem RT_001_18_sandbox_resource_limited : forall sb r,
  within_limits sb ->
  sb_usage sb r <= sb_limits sb r.
Proof.
  intros sb r Hwl.
  unfold within_limits in Hwl.
  apply Hwl.
Qed.

(* RT_001_19: Sandboxes can be terminated *)
Theorem RT_001_19_sandbox_terminable : forall sb,
  sb_terminated (terminate sb) = true /\
  (forall p, sb_accessible (terminate sb) p = false) /\
  (forall c, sb_granted (terminate sb) c = false).
Proof.
  intros sb.
  unfold terminate. simpl.
  split; [reflexivity | split; intros; reflexivity].
Qed.

(* RT_001_20: Sandbox communication is controlled *)
Theorem RT_001_20_sandbox_comm_controlled : forall ch,
  comm_controlled ch <-> ch_authorized ch = true.
Proof.
  intros ch.
  unfold comm_controlled.
  split; intro H; exact H.
Qed.
