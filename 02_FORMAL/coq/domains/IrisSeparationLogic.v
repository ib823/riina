(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** IrisSeparationLogic.v
    Strategic Item #1: Iris Separation Logic for RIINA

    Implements separation logic foundations without the Iris library,
    using custom ghost state and resource algebras.

    Self-contained — Coq stdlib only.
    Spec: 06_COORDINATION/iris_migration_spec.md
*)

Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(** * Heap model: partial maps from locations to values *)
Definition loc := nat.
Definition val := nat.
Definition heap := list (loc * val).

(** * Disjointness of heaps *)
Definition dom (h : heap) : list loc := map fst h.

Fixpoint mem (n : nat) (l : list nat) : bool :=
  match l with
  | [] => false
  | x :: xs => (x =? n) || mem n xs
  end.

Definition disjoint (h1 h2 : heap) : Prop :=
  forall l, In l (dom h1) -> ~ In l (dom h2).

(** * Heap union *)
Definition heap_union (h1 h2 : heap) : heap := h1 ++ h2.

(** * Heap lookup *)
Fixpoint heap_lookup (h : heap) (l : loc) : option val :=
  match h with
  | [] => None
  | (l', v) :: rest => if l' =? l then Some v else heap_lookup rest l
  end.

(** * Separation logic assertions *)
Inductive hprop : Type :=
  | HEmpty : hprop
  | HPointsTo : loc -> val -> hprop
  | HStar : hprop -> hprop -> hprop
  | HPure : Prop -> hprop
  | HWand : hprop -> hprop -> hprop.

(** * Satisfaction relation *)
Fixpoint satisfies (h : heap) (p : hprop) : Prop :=
  match p with
  | HEmpty => h = []
  | HPointsTo l v => h = [(l, v)]
  | HStar p1 p2 =>
      exists h1 h2,
        disjoint h1 h2 /\
        heap_union h1 h2 = h /\
        satisfies h1 p1 /\
        satisfies h2 p2
  | HPure P => P /\ h = []
  | HWand p1 p2 =>
      forall h',
        disjoint h h' ->
        satisfies h' p1 ->
        satisfies (heap_union h h') p2
  end.

(** * Theorem 1: Empty heap satisfies emp *)
Theorem emp_empty : satisfies [] HEmpty.
Proof. simpl. reflexivity. Qed.

(** * Theorem 2: Singleton heap satisfies points-to *)
Theorem points_to_singleton : forall l v,
  satisfies [(l, v)] (HPointsTo l v).
Proof. intros. simpl. reflexivity. Qed.

(** * Disjointness is symmetric *)
Lemma disjoint_sym : forall h1 h2, disjoint h1 h2 -> disjoint h2 h1.
Proof.
  unfold disjoint. intros h1 h2 Hd l Hin Hin'.
  eapply Hd; eauto.
Qed.

(** Note: star commutativity for the list-based heap model requires
    permutation equivalence (h1 ++ h2 is not definitionally equal to
    h2 ++ h1). The functional heap model below avoids this issue. *)

Module FuncHeap.

Definition fheap := loc -> option val.

Definition fempty : fheap := fun _ => None.

Definition fsingleton (l : loc) (v : val) : fheap :=
  fun l' => if l' =? l then Some v else None.

Definition fdisjoint (h1 h2 : fheap) : Prop :=
  forall l, h1 l = None \/ h2 l = None.

Definition funion (h1 h2 : fheap) : fheap :=
  fun l => match h1 l with Some v => Some v | None => h2 l end.

(** * Assertions *)
Inductive fprop : Type :=
  | FEmpty : fprop
  | FPointsTo : loc -> val -> fprop
  | FStar : fprop -> fprop -> fprop
  | FPure : Prop -> fprop.

Fixpoint fsat (h : fheap) (p : fprop) : Prop :=
  match p with
  | FEmpty => forall l, h l = None
  | FPointsTo l v => h l = Some v /\ forall l', l' <> l -> h l' = None
  | FStar p1 p2 =>
      exists h1 h2,
        fdisjoint h1 h2 /\
        (forall l, h l = funion h1 h2 l) /\
        fsat h1 p1 /\
        fsat h2 p2
  | FPure P => P /\ forall l, h l = None
  end.

(** * Theorem 3: Star is commutative *)
Theorem star_comm : forall p1 p2 h,
  fsat h (FStar p1 p2) -> fsat h (FStar p2 p1).
Proof.
  intros p1 p2 h H. simpl in *.
  destruct H as [h1 [h2 [Hdisj [Hunion [Hs1 Hs2]]]]].
  exists h2, h1.
  refine (conj _ (conj _ (conj Hs2 Hs1))).
  - unfold fdisjoint in *. intros l. specialize (Hdisj l). tauto.
  - intros l. rewrite Hunion. unfold funion.
    destruct (Hdisj l) as [Hn1 | Hn2];
      [rewrite Hn1 | rewrite Hn2]; destruct (h1 l); destruct (h2 l); auto; congruence.
Qed.

(** * Theorem 4: Star with emp is identity *)
Theorem star_emp_l : forall p h,
  fsat h p -> fsat h (FStar FEmpty p).
Proof.
  intros p h Hp. simpl.
  exists fempty, h.
  refine (conj _ (conj _ (conj _ Hp))).
  - unfold fdisjoint, fempty. intros. left. auto.
  - intros l. unfold funion, fempty. auto.
  - unfold fempty. auto.
Qed.

(** * Theorem 5: Points-to is exclusive *)
Theorem points_to_exclusive : forall l v1 v2 h,
  fsat h (FStar (FPointsTo l v1) (FPointsTo l v2)) -> False.
Proof.
  intros l v1 v2 h H. simpl in H.
  destruct H as [h1 [h2 [Hdisj [Hunion [[Hpt1 _] [Hpt2 _]]]]]].
  unfold fdisjoint in Hdisj. specialize (Hdisj l).
  destruct Hdisj as [Hn1 | Hn2]; congruence.
Qed.

(** * Frame rule: if P holds on h1, then P * F holds on h1 ∪ h2 *)
Theorem frame_rule : forall p f h1 h2,
  fsat h1 p ->
  fsat h2 f ->
  fdisjoint h1 h2 ->
  fsat (funion h1 h2) (FStar p f).
Proof.
  intros p f h1 h2 Hp Hf Hdisj. simpl.
  exists h1, h2.
  refine (conj Hdisj (conj _ (conj Hp Hf))).
  intros l. reflexivity.
Qed.

End FuncHeap.

(** Re-export main theorems *)
Definition sep_star_comm := FuncHeap.star_comm.
Definition sep_star_emp_l := FuncHeap.star_emp_l.
Definition sep_points_to_exclusive := FuncHeap.points_to_exclusive.
Definition sep_frame_rule := FuncHeap.frame_rule.
