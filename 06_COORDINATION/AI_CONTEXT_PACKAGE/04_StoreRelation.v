(** * StoreRelation.v

    RIINA Store Relation Properties for Semantic Typing

    This file extends the Phase 2 cumulative relation infrastructure
    with store-specific lemmas needed for proving reference operations
    (ref, deref, assign) and declassification.

    PHASE 5: Store Semantics & Semantic Typing Axioms

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_ζ (Zeta)
    Phase: 5 (Semantic Typing)

    References:
    - Ahmed (2006) "Step-Indexed Syntactic Logical Relations"
    - Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"
    - Phase 2 infrastructure (CumulativeRelation.v, CumulativeMonotone.v, KripkeProperties.v)
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.
Require Import Arith.PeanoNat.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.type_system.Preservation.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.LexOrder.
Require Import RIINA.properties.FirstOrderComplete.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.CumulativeMonotone.
Require Import RIINA.properties.KripkeProperties.

Import ListNotations.

(** ** Store Max Equality Properties

    When stores are related, they have the same size.
    This is critical for proving that allocations produce
    the same location in both stores.
*)

(** Related stores have the same max location *)
Lemma store_rel_simple_max : forall Σ st1 st2,
  store_rel_simple Σ st1 st2 ->
  store_max st1 = store_max st2.
Proof.
  intros Σ st1 st2 H. unfold store_rel_simple in H. exact H.
Qed.

(** Related stores allocate at the same location *)
Lemma store_rel_simple_fresh : forall Σ st1 st2,
  store_rel_simple Σ st1 st2 ->
  fresh_loc st1 = fresh_loc st2.
Proof.
  intros Σ st1 st2 H.
  unfold store_rel_simple in H.
  unfold fresh_loc.
  rewrite H. reflexivity.
Qed.

(** ** Store Update Properties

    When updating related stores at the same location
    with related values, the resulting stores are still related.
*)

(** Helper: store_max after update is bounded by max of l and original max *)
Lemma store_max_update_bound : forall l v st,
  store_max (store_update l v st) <= Nat.max l (store_max st).
Proof.
  intros l v st. revert l v.
  induction st as [| [l' v'] st' IH]; intros l v; simpl.
  - (* Empty store: result is (l,v)::nil, so max is max(l,0) = l *)
    simpl. lia.
  - (* Non-empty store *)
    destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l': replace at head, max is max of l and rest *)
      simpl. apply Nat.max_lub.
      * apply Nat.le_max_l.
      * apply Nat.le_trans with (m := store_max st').
        -- apply Nat.le_refl.
        -- apply Nat.le_trans with (m := Nat.max l' (store_max st')).
           ++ apply Nat.le_max_r.
           ++ apply Nat.le_max_r.
    + (* l <> l': recurse *)
      simpl. apply Nat.max_lub.
      * apply Nat.le_trans with (m := Nat.max l' (store_max st')).
        -- apply Nat.le_max_l.
        -- apply Nat.le_max_r.
      * apply Nat.le_trans with (m := Nat.max l (store_max st')).
        -- apply IH.
        -- apply Nat.max_le_compat_l. apply Nat.le_max_r.
Qed.

(** Helper: store_max after update is at least the original max *)
Lemma store_max_update_lower : forall l v st,
  store_max st <= store_max (store_update l v st).
Proof.
  intros l v st. revert l v.
  induction st as [| [l' v'] st' IH]; intros l v; simpl.
  - (* Empty store: 0 <= l *)
    apply Nat.le_0_l.
  - (* Non-empty store *)
    destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l': replace at head *)
      simpl. apply Nat.eqb_eq in Heq. subst.
      apply Nat.le_refl.
    + (* l <> l': recurse *)
      simpl. apply Nat.max_le_compat.
      * apply Nat.le_refl.
      * apply IH.
Qed.

(** Helper: l is at most store_max after updating at l *)
Lemma store_max_update_includes_l : forall l v st,
  l <= store_max (store_update l v st).
Proof.
  intros l v st. revert l v.
  induction st as [| [l' v'] st' IH]; intros l v; simpl.
  - (* Empty store: result is (l,v)::nil, max is max(l,0) = l *)
    simpl. lia.
  - (* Non-empty store *)
    destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l': replace at head, max includes l *)
      simpl. apply Nat.eqb_eq in Heq. subst.
      apply Nat.le_max_l.
    + (* l <> l': recurse, l is in the tail *)
      simpl. apply Nat.le_trans with (m := store_max (store_update l v st')).
      * apply IH.
      * apply Nat.le_max_r.
Qed.

(** Helper: store_max after update at same location gives same result *)
Lemma store_max_update_eq : forall l v1 v2 st1 st2,
  store_max st1 = store_max st2 ->
  store_max (store_update l v1 st1) = store_max (store_update l v2 st2).
Proof.
  intros l v1 v2 st1 st2 Heq.
  (* Key insight: store_max (store_update l v st) = max(l, store_max st) *)
  (* Since store_max st1 = store_max st2, the results are equal *)
  apply Nat.le_antisymm.
  - (* store_max (store_update l v1 st1) <= store_max (store_update l v2 st2) *)
    apply Nat.le_trans with (m := Nat.max l (store_max st1)).
    + apply store_max_update_bound.
    + rewrite Heq. apply Nat.max_lub.
      * apply store_max_update_includes_l.
      * apply store_max_update_lower.
  - (* Symmetric case *)
    apply Nat.le_trans with (m := Nat.max l (store_max st2)).
    + apply store_max_update_bound.
    + rewrite <- Heq. apply Nat.max_lub.
      * apply store_max_update_includes_l.
      * apply store_max_update_lower.
Qed.

(** Updating same location in related stores preserves simple relation *)
Lemma store_rel_simple_update : forall Σ st1 st2 l v1 v2,
  store_rel_simple Σ st1 st2 ->
  store_rel_simple Σ (store_update l v1 st1) (store_update l v2 st2).
Proof.
  intros Σ st1 st2 l v1 v2 H.
  unfold store_rel_simple in *.
  apply store_max_update_eq. exact H.
Qed.

(** ** Store Lookup and Update Properties *)

(** Looking up updated location returns the new value *)
Lemma store_lookup_update_eq : forall l v st,
  store_lookup l (store_update l v st) = Some v.
Proof.
  intros l v st. revert l v.
  induction st as [| [l' v'] st' IH]; intros l v; simpl.
  - (* Empty store: store_update l v nil = (l,v)::nil *)
    (* store_lookup l ((l,v)::nil) = if l=?l then Some v else None *)
    rewrite Nat.eqb_refl. reflexivity.
  - (* Non-empty store *)
    destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l': store_update returns (l,v)::st' *)
      (* store_lookup l ((l,v)::st') checks l=?l *)
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + (* l <> l': store_update recurses *)
      simpl. rewrite Heq. apply IH.
Qed.

(** Looking up different location after update is unchanged *)
Lemma store_lookup_update_neq : forall l l' v st,
  l <> l' ->
  store_lookup l' (store_update l v st) = store_lookup l' st.
Proof.
  intros l l' v st Hneq. revert l l' v Hneq.
  induction st as [| [l'' v''] st' IH]; intros l l' v Hneq; simpl.
  - (* Empty store *)
