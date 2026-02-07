(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* SIMDVerification.v - SIMD Verification for RIINA *)
(* Spec: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ *)
(* Safety Property: Vectorized code semantically equivalent to scalar *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
Require Import Coq.micromega.Lia.
Import ListNotations.
Import VectorNotations.

(* SIMD vector width *)
Definition VWidth := 4.  (* 128-bit with 32-bit elements *)

(* SIMD vector type *)
Definition SIMDVec := Vector.t nat VWidth.

(* Boolean SIMD vector *)
Definition SIMDBoolVec := Vector.t bool VWidth.

(* Scalar operations *)
Definition scalar_add (a b : nat) : nat := a + b.
Definition scalar_mul (a b : nat) : nat := a * b.
Definition scalar_cmp (a b : nat) : bool := Nat.leb a b.

(* SIMD operations modeled as vector operations *)
Definition simd_add (a b : SIMDVec) : SIMDVec :=
  Vector.map2 scalar_add a b.

Definition simd_mul (a b : SIMDVec) : SIMDVec :=
  Vector.map2 scalar_mul a b.

Definition simd_cmp (a b : SIMDVec) : SIMDBoolVec :=
  Vector.map2 scalar_cmp a b.

(* Broadcast: replicate scalar to all lanes *)
Definition simd_broadcast (x : nat) : SIMDVec :=
  Vector.const x VWidth.

(* Reduction: fold all lanes *)
Definition simd_reduce (op : nat -> nat -> nat) (init : nat) (v : SIMDVec) : nat :=
  Vector.fold_left op init v.

(* Shuffle with permutation *)
Definition simd_shuffle (v : SIMDVec) (perm : Vector.t (Fin.t VWidth) VWidth) : SIMDVec :=
  Vector.map (fun i => Vector.nth v i) perm.

(* Alignment check *)
Definition is_aligned (addr : nat) (alignment : nat) : bool :=
  Nat.eqb (Nat.modulo addr alignment) 0.

(* Mask type *)
Definition SIMDMask := Vector.t bool VWidth.

(* Masked select operation - for each lane, if mask is true, use new value, else old *)
Definition simd_select (mask : SIMDMask) (old new_val : SIMDVec) : SIMDVec :=
  Vector.map2 (fun (m : bool) (p : nat * nat) => if m then snd p else fst p)
    mask (Vector.map2 (fun x y => (x, y)) old new_val).

(* Masked add: compute add, then select based on mask *)
Definition simd_masked_add (mask : SIMDMask) (a b old : SIMDVec) : SIMDVec :=
  simd_select mask old (simd_add a b).

(* Loop with potential dependency *)
Record Loop : Type := mkLoop {
  loop_iterations : nat;
  loop_body_reads : list nat;    (* Memory locations read *)
  loop_body_writes : list nat;   (* Memory locations written *)
}.

(* Dependency check: write-after-read or read-after-write across iterations *)
Definition has_carried_dependency (l : Loop) : bool :=
  existsb (fun w => existsb (Nat.eqb w) (loop_body_reads l)) (loop_body_writes l).

(* Vectorizable iff no carried dependencies *)
Definition vectorizable (l : Loop) : bool :=
  negb (has_carried_dependency l).

(* Index bounds check for gather/scatter *)
Definition indices_in_bounds (indices : list nat) (bound : nat) : bool :=
  forallb (fun i => Nat.ltb i bound) indices.

(* Gather operation: collect elements at given indices *)
Definition gather (mem : list nat) (indices : Vector.t nat VWidth) : option SIMDVec :=
  let check := Vector.fold_left 
    (fun acc i => acc && (Nat.ltb i (length mem))) 
    true indices in
  if check then
    Some (Vector.map (fun i => List.nth i mem 0) indices)
  else
    None.

(* Memory access result type *)
Inductive MemResult : Type :=
  | MemOK : SIMDVec -> MemResult
  | MemUB : MemResult.  (* Undefined behavior *)

(* Helper to extract exactly VWidth elements from a list as a vector *)
(* Returns a default vector if not enough elements *)
Definition list_to_simd (l : list nat) : SIMDVec :=
  let a := List.nth 0 l 0 in
  let b := List.nth 1 l 0 in
  let c := List.nth 2 l 0 in
  let d := List.nth 3 l 0 in
  Vector.cons nat a 3 (Vector.cons nat b 2 (Vector.cons nat c 1 (Vector.cons nat d 0 (Vector.nil nat)))).

(* Aligned load *)
Definition aligned_load (mem : list nat) (addr : nat) : MemResult :=
  if is_aligned addr VWidth then
    if Nat.leb (addr + VWidth) (length mem) then
      MemOK (list_to_simd (firstn VWidth (skipn addr mem)))
    else
      MemUB
  else
    MemUB.

(* Scalar list operations for comparison *)
Definition list_add (a b : list nat) : list nat :=
  List.map (fun p => fst p + snd p) (combine a b).

Definition list_mul (a b : list nat) : list nat :=
  List.map (fun p => fst p * snd p) (combine a b).

Definition list_cmp (a b : list nat) : list bool :=
  List.map (fun p => Nat.leb (fst p) (snd p)) (combine a b).

(* Convert vector to list *)
Definition vec_to_list {A n} (v : Vector.t A n) : list A :=
  Vector.to_list v.

(* Replicate function for lists *)
Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | 0 => List.nil
  | S n' => List.cons x (replicate n' x)
  end.

(* List fold *)
Definition list_fold_left {A B : Type} (f : A -> B -> A) (init : A) (l : list B) : A :=
  List.fold_left f l init.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_01: SIMD add equivalence                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_01_simd_add_equivalence :
  forall (a b : SIMDVec),
    simd_add a b = Vector.map2 Nat.add a b.
Proof.
  intros a b.
  unfold simd_add, scalar_add.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_02: SIMD mul equivalence                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_02_simd_mul_equivalence :
  forall (a b : SIMDVec),
    simd_mul a b = Vector.map2 Nat.mul a b.
Proof.
  intros a b.
  unfold simd_mul, scalar_mul.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_03: SIMD comparison equivalence                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_03_simd_cmp_equivalence :
  forall (a b : SIMDVec),
    simd_cmp a b = Vector.map2 Nat.leb a b.
Proof.
  intros a b.
  unfold simd_cmp, scalar_cmp.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_04: SIMD shuffle correctness                               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_04_simd_shuffle_correctness :
  forall (v : SIMDVec) (perm : Vector.t (Fin.t VWidth) VWidth) (i : Fin.t VWidth),
    Vector.nth (simd_shuffle v perm) i = Vector.nth v (Vector.nth perm i).
Proof.
  intros v perm i.
  unfold simd_shuffle.
  erewrite Vector.nth_map.
  - reflexivity.
  - reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_05: SIMD alignment requirement                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_05_simd_alignment_requirement :
  forall (mem : list nat) (addr : nat),
    (exists v, aligned_load mem addr = MemOK v) <->
    (is_aligned addr VWidth = true /\ Nat.leb (addr + VWidth) (length mem) = true).
Proof.
  intros mem addr.
  split.
  - intros [v H].
    unfold aligned_load in H.
    destruct (is_aligned addr VWidth) eqn:Halign.
    + destruct (Nat.leb (addr + VWidth) (length mem)) eqn:Hbound.
      * split; reflexivity.
      * discriminate H.
    + discriminate H.
  - intros [Halign Hbound].
    unfold aligned_load.
    rewrite Halign, Hbound.
    eexists.
    reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_06: SIMD lane independence                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_06_simd_lane_independence :
  forall (a b : SIMDVec) (i : Fin.t VWidth),
    Vector.nth (simd_add a b) i = 
    scalar_add (Vector.nth a i) (Vector.nth b i).
Proof.
  intros a b i.
  unfold simd_add.
  erewrite Vector.nth_map2.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_07: SIMD reduction equivalence                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_07_simd_reduce_equivalence :
  forall (v : SIMDVec) (init : nat),
    simd_reduce Nat.add init v = 
    List.fold_left Nat.add (Vector.to_list v) init.
Proof.
  intros v init.
  unfold simd_reduce.
  rewrite Vector.to_list_fold_left.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_08: SIMD broadcast correctness                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_08_simd_broadcast_correctness :
  forall (x : nat) (i : Fin.t VWidth),
    Vector.nth (simd_broadcast x) i = x.
Proof.
  intros x i.
  unfold simd_broadcast.
  apply Vector.const_nth.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_09: SIMD gather/scatter safety                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Helper lemma: fold_left with && preserves true if all elements satisfy predicate *)
Lemma fold_and_all_true : forall {n} (v : Vector.t nat n) (f : nat -> bool),
  (forall i, f (Vector.nth v i) = true) ->
  Vector.fold_left (fun acc x => acc && f x) true v = true.
Proof.
  intros n v f Hall.
  induction v as [|h n' t IH].
  - simpl. reflexivity.
  - simpl.
    assert (Hh: f h = true) by (apply (Hall Fin.F1)).
    rewrite Hh. simpl.
    apply IH.
    intros i. apply (Hall (Fin.FS i)).
Qed.

Theorem PERF_003_09_simd_gather_safety :
  forall (mem : list nat) (indices : Vector.t nat VWidth),
    (forall i : Fin.t VWidth, Vector.nth indices i < length mem) ->
    exists result, gather mem indices = Some result.
Proof.
  intros mem indices Hbounds.
  unfold gather.
  assert (Hcheck: Vector.fold_left (fun acc i => acc && (i <? length mem)) true indices = true).
  {
    apply fold_and_all_true.
    intros i.
    apply Nat.ltb_lt.
    apply Hbounds.
  }
  rewrite Hcheck.
  eexists.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_10: SIMD masking correctness                               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_10_simd_masking_correctness :
  forall (mask : SIMDMask) (a b old : SIMDVec) (i : Fin.t VWidth),
    Vector.nth (simd_masked_add mask a b old) i =
    if Vector.nth mask i 
    then Vector.nth (simd_add a b) i 
    else Vector.nth old i.
Proof.
  intros mask a b old i.
  unfold simd_masked_add, simd_select.
  erewrite Vector.nth_map2.
  2: reflexivity.
  2: reflexivity.
  erewrite Vector.nth_map2.
  2: reflexivity.
  2: reflexivity.
  destruct (Vector.nth mask i) eqn:Hmask.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_11: Vectorization legality                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_11_vectorization_legality :
  forall (l : Loop),
    vectorizable l = true <-> has_carried_dependency l = false.
Proof.
  intros l.
  unfold vectorizable.
  split.
  - intros H.
    apply negb_true_iff in H.
    exact H.
  - intros H.
    apply negb_true_iff.
    exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_12: SIMD semantic preservation                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Helper: scalar execution of addition on lists *)
Definition scalar_exec_add (a b : list nat) : list nat :=
  List.map (fun p => fst p + snd p) (combine a b).

(* Lemma: to_list distributes over map2 *)
Lemma to_list_map2 : forall {A B C : Type} {n : nat} (f : A -> B -> C)
  (v1 : Vector.t A n) (v2 : Vector.t B n),
  Vector.to_list (Vector.map2 f v1 v2) = 
  List.map (fun p => f (fst p) (snd p)) (combine (Vector.to_list v1) (Vector.to_list v2)).
Proof.
  intros A B C n f v1.
  induction v1 as [|h1 n' t1 IH]; intros v2.
  - (* nil case *)
    apply Vector.case0 with (v := v2).
    reflexivity.
  - (* cons case *)
    apply (Vector.caseS' v2).
    intros h2 t2.
    change (Vector.to_list (f h1 h2 :: Vector.map2 f t1 t2)%vector = 
            (f h1 h2 :: List.map (fun p => f (fst p) (snd p)) 
              (combine (Vector.to_list t1) (Vector.to_list t2)))%list).
    rewrite Vector.to_list_cons.
    f_equal.
    apply IH.
Qed.

(* Helper: vectorized execution produces same result as scalar *)
Theorem PERF_003_12_simd_semantic_preservation :
  forall (a b : SIMDVec),
    Vector.to_list (simd_add a b) =
    scalar_exec_add (Vector.to_list a) (Vector.to_list b).
Proof.
  intros a b.
  unfold simd_add, scalar_add, scalar_exec_add.
  rewrite to_list_map2.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_13: SIMD multiplication lane independence                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_13_simd_mul_lane_independence :
  forall (a b : SIMDVec) (i : Fin.t VWidth),
    Vector.nth (simd_mul a b) i =
    scalar_mul (Vector.nth a i) (Vector.nth b i).
Proof.
  intros a b i.
  unfold simd_mul.
  erewrite Vector.nth_map2.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_14: SIMD comparison lane independence                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_14_simd_cmp_lane_independence :
  forall (a b : SIMDVec) (i : Fin.t VWidth),
    Vector.nth (simd_cmp a b) i =
    scalar_cmp (Vector.nth a i) (Vector.nth b i).
Proof.
  intros a b i.
  unfold simd_cmp.
  erewrite Vector.nth_map2.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_15: Broadcast add equivalence                              *)
(* Adding broadcast scalar is same as adding scalar to each lane               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_15_broadcast_add_equiv :
  forall (v : SIMDVec) (x : nat) (i : Fin.t VWidth),
    Vector.nth (simd_add v (simd_broadcast x)) i =
    scalar_add (Vector.nth v i) x.
Proof.
  intros v x i.
  unfold simd_add.
  erewrite Vector.nth_map2.
  2: reflexivity.
  2: reflexivity.
  unfold simd_broadcast.
  rewrite Vector.const_nth.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_16: Identity shuffle preserves vector                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_16_identity_shuffle :
  forall (v : SIMDVec) (perm : Vector.t (Fin.t VWidth) VWidth),
    (forall i : Fin.t VWidth, Vector.nth perm i = i) ->
    simd_shuffle v perm = v.
Proof.
  intros v perm Hid.
  unfold simd_shuffle.
  apply Vector.eq_nth_iff.
  intros p1 p2 Heq.
  subst p2.
  erewrite Vector.nth_map.
  2: reflexivity.
  rewrite Hid.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_17: SIMD add commutativity                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_17_simd_add_commutative :
  forall (a b : SIMDVec) (i : Fin.t VWidth),
    Vector.nth (simd_add a b) i = Vector.nth (simd_add b a) i.
Proof.
  intros a b i.
  unfold simd_add, scalar_add.
  erewrite (Vector.nth_map2 _ a b).
  2: reflexivity.
  2: reflexivity.
  erewrite (Vector.nth_map2 _ b a).
  2: reflexivity.
  2: reflexivity.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_18: Masked select with all-true mask returns new value     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition all_true_mask : SIMDMask :=
  Vector.const true VWidth.

Theorem PERF_003_18_all_true_mask_selects_new :
  forall (old new_val : SIMDVec) (i : Fin.t VWidth),
    Vector.nth (simd_select all_true_mask old new_val) i =
    Vector.nth new_val i.
Proof.
  intros old new_val i.
  unfold simd_select, all_true_mask.
  erewrite Vector.nth_map2.
  2: reflexivity.
  2: reflexivity.
  erewrite Vector.nth_map2.
  2: reflexivity.
  2: reflexivity.
  rewrite Vector.const_nth.
  simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_19: Masked select with all-false mask preserves old value  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition all_false_mask : SIMDMask :=
  Vector.const false VWidth.

Theorem PERF_003_19_all_false_mask_preserves_old :
  forall (old new_val : SIMDVec) (i : Fin.t VWidth),
    Vector.nth (simd_select all_false_mask old new_val) i =
    Vector.nth old i.
Proof.
  intros old new_val i.
  unfold simd_select, all_false_mask.
  erewrite Vector.nth_map2.
  2: reflexivity.
  2: reflexivity.
  erewrite Vector.nth_map2.
  2: reflexivity.
  2: reflexivity.
  rewrite Vector.const_nth.
  simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_003_20: Alignment zero always aligned                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_003_20_zero_aligned :
  forall alignment : nat,
    alignment > 0 ->
    is_aligned 0 alignment = true.
Proof.
  intros alignment Hpos.
  unfold is_aligned.
  rewrite Nat.mod_0_l.
  - simpl. reflexivity.
  - lia.
Qed.
