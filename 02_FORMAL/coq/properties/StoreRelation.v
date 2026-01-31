(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

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
    destruct (Nat.eqb l' l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. symmetry in Heq. contradiction.
    + reflexivity.
  - (* Non-empty store *)
    destruct (Nat.eqb l l'') eqn:Heq1.
    + (* l = l'' *)
      simpl. apply Nat.eqb_eq in Heq1. subst l''.
      destruct (Nat.eqb l' l) eqn:Heq2.
      * apply Nat.eqb_eq in Heq2. symmetry in Heq2. contradiction.
      * reflexivity.
    + (* l <> l'' *)
      simpl. destruct (Nat.eqb l' l'') eqn:Heq2.
      * reflexivity.
      * apply IH. exact Hneq.
Qed.

(** ** Store Typing Update Properties *)

(** Looking up at updated location returns the new type *)
Lemma store_ty_lookup_update_eq : forall l T sl Σ,
  store_ty_lookup l (store_ty_update l T sl Σ) = Some (T, sl).
Proof.
  intros l T sl Σ. revert l T sl.
  induction Σ as [| [[l' T'] sl'] Σ' IH]; intros l T sl; simpl.
  - (* Empty store typing *)
    rewrite Nat.eqb_refl. reflexivity.
  - (* Non-empty store typing *)
    destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l' *)
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + (* l <> l' *)
      simpl. rewrite Heq. apply IH.
Qed.

(** Looking up different location after update is unchanged *)
Lemma store_ty_lookup_update_neq : forall l l' T sl Σ,
  l <> l' ->
  store_ty_lookup l' (store_ty_update l T sl Σ) = store_ty_lookup l' Σ.
Proof.
  intros l l' T sl Σ Hneq. revert l l' T sl Hneq.
  induction Σ as [| [[l'' T''] sl''] Σ' IH]; intros l l' T sl Hneq; simpl.
  - (* Empty store typing *)
    destruct (Nat.eqb l' l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. symmetry in Heq. contradiction.
    + reflexivity.
  - (* Non-empty store typing *)
    destruct (Nat.eqb l l'') eqn:Heq1.
    + (* l = l'' *)
      simpl. apply Nat.eqb_eq in Heq1. subst l''.
      destruct (Nat.eqb l' l) eqn:Heq2.
      * apply Nat.eqb_eq in Heq2. symmetry in Heq2. contradiction.
      * reflexivity.
    + (* l <> l'' *)
      simpl. destruct (Nat.eqb l' l'') eqn:Heq2.
      * reflexivity.
      * apply IH. exact Hneq.
Qed.

(** ** Full Store Relation Update

    For the full store relation (including value relations at all locations),
    updating with related values preserves the relation.
*)

(** Update preserves store relation when values are related *)
Lemma store_rel_le_update : forall n Σ st1 st2 l T sl v1 v2,
  store_rel_le n Σ st1 st2 ->
  store_ty_lookup l Σ = Some (T, sl) ->
  val_rel_le n Σ T v1 v2 ->
  store_rel_le n Σ (store_update l v1 st1) (store_update l v2 st2).
Proof.
  intros n Σ st1 st2 l T sl v1 v2 Hst Hlook Hval.
  unfold store_rel_le in *.
  destruct Hst as [Hmax Hlocs].
  split.
  - (* store_max preserved *)
    apply store_max_update_eq. exact Hmax.
  - (* All locations still related *)
    intros l' T' sl' Hlook'.
    destruct (Nat.eq_dec l l') as [Heq | Hneq].
    + (* l = l' - the updated location *)
      subst l'.
      (* Types must match *)
      rewrite Hlook in Hlook'. injection Hlook' as Heq1 Heq2.
      subst T' sl'.
      (* After update, we have the new related values *)
      rewrite store_lookup_update_eq.
      rewrite store_lookup_update_eq.
      exact Hval.
    + (* l <> l' - unchanged location *)
      specialize (Hlocs l' T' sl' Hlook').
      (* store_update at different location doesn't change lookup *)
      rewrite store_lookup_update_neq by exact Hneq.
      rewrite store_lookup_update_neq by exact Hneq.
      exact Hlocs.
Qed.

(** ** Store Allocation Properties

    When allocating new locations in related stores,
    the fresh locations are the same.
*)

(** Fresh location lookup returns None *)
Lemma store_lookup_fresh_none : forall st,
  store_lookup (fresh_loc st) st = None.
Proof.
  intros st.
  apply store_lookup_fresh.
Qed.

(** Allocating in related stores produces same location *)
Lemma store_alloc_same : forall Σ st1 st2,
  store_rel_simple Σ st1 st2 ->
  fresh_loc st1 = fresh_loc st2.
Proof.
  intros Σ st1 st2 H.
  apply store_rel_simple_fresh with (Σ := Σ). exact H.
Qed.

(** After allocation, stores remain related *)
Lemma store_rel_simple_alloc : forall Σ st1 st2 v1 v2,
  store_rel_simple Σ st1 st2 ->
  store_rel_simple Σ
    (store_update (fresh_loc st1) v1 st1)
    (store_update (fresh_loc st2) v2 st2).
Proof.
  intros Σ st1 st2 v1 v2 Hrel.
  assert (Heq : fresh_loc st1 = fresh_loc st2).
  { apply store_alloc_same with (Σ := Σ). exact Hrel. }
  rewrite Heq.
  apply store_rel_simple_update with (Σ := Σ). exact Hrel.
Qed.

(** ** Store Typing Extension on Allocation

    When we allocate a new location, we extend the store typing.
*)

(** Fresh location is not in store typing for well-formed stores *)
Lemma fresh_loc_not_in_store_ty : forall Σ st,
  store_wf Σ st ->
  store_ty_lookup (fresh_loc st) Σ = None.
Proof.
  intros Σ st Hwf.
  (* If the location were in Σ, it would have a value in st,
     but fresh_loc is above store_max *)
  destruct (store_ty_lookup (fresh_loc st) Σ) as [[T sl] |] eqn:Hlook; auto.
  (* Show contradiction: lookup would succeed in st, but fresh_loc > max *)
  unfold store_wf in Hwf. destruct Hwf as [HΣtost _].
  specialize (HΣtost (fresh_loc st) T sl Hlook).
  destruct HΣtost as [v [Hst _]].
  rewrite store_lookup_fresh in Hst. discriminate.
Qed.

(** Adding new location to store typing gives extension *)
Lemma store_ty_extends_alloc : forall Σ l T sl,
  store_ty_lookup l Σ = None ->
  store_ty_extends Σ (store_ty_update l T sl Σ).
Proof.
  intros Σ l T sl Hnone.
  unfold store_ty_extends.
  intros l' T' sl' Hlook.
  destruct (Nat.eq_dec l l') as [Heq | Hneq].
  - (* l = l' *)
    subst. rewrite Hnone in Hlook. discriminate.
  - (* l <> l' *)
    (* Lookup at different location is unchanged *)
    rewrite store_ty_lookup_update_neq; auto.
Qed.

(** ** Store Relation After Allocation with Extension

    After allocating a new reference, we can extend the store typing
    and maintain the store relation.
*)

(** Full store relation after allocation

    SEMANTIC JUSTIFICATION:
    When allocating a new reference, we extend the store typing with the new location.
    The key properties are:
    1. The new location gets the freshly allocated values (related by hypothesis)
    2. All existing locations maintain their values (unchanged by fresh allocation)
    3. The store max increases by 1 in both stores (same fresh_loc)

    This lemma is admitted because it requires detailed reasoning about
    store_update and store_ty_update interactions. The proof strategy is sound.
*)
Lemma store_rel_le_alloc : forall n Σ st1 st2 T sl v1 v2,
  store_rel_le n Σ st1 st2 ->
  val_rel_le n Σ T v1 v2 ->
  store_ty_lookup (fresh_loc st1) Σ = None ->
  fresh_loc st1 = fresh_loc st2 ->
  let Σ' := store_ty_update (fresh_loc st1) T sl Σ in
  let st1' := store_update (fresh_loc st1) v1 st1 in
  let st2' := store_update (fresh_loc st2) v2 st2 in
  store_rel_le n Σ' st1' st2'.
Proof.
  intros n Σ st1 st2 T sl v1 v2 Hst Hval Hfresh_none Heq_fresh.
  unfold store_rel_le in *.
  destruct Hst as [Hmax Htyped].
  split.
  - (* store_max equality *)
    rewrite Heq_fresh.
    apply store_max_update_eq. exact Hmax.
  - (* All typed locations have related values *)
    intros l T0 sl0 Hlookup.
    destruct (Nat.eq_dec (fresh_loc st1) l) as [Heql | Hneql].
    + (* l = fresh_loc st1: the newly allocated location *)
      subst l.
      (* Use the helper lemma to establish T0 = T, sl0 = sl *)
      assert (Hlookup_eq : store_ty_lookup (fresh_loc st1)
                (store_ty_update (fresh_loc st1) T sl Σ) = Some (T, sl)).
      { apply store_ty_lookup_update_eq. }
      rewrite Hlookup_eq in Hlookup.
      injection Hlookup as HT Hsl. subst T0 sl0.
      (* Now handle the store lookups *)
      rewrite Heq_fresh.
      rewrite store_lookup_update_eq.
      rewrite store_lookup_update_eq.
      (* Need val_rel_le n Σ' T v1 v2 from val_rel_le n Σ T v1 v2 *)
      (* Σ' = store_ty_update (fresh_loc st1) T sl Σ extends Σ *)
      (* Note: fresh_loc st1 = fresh_loc st2 by Heq_fresh *)
      apply val_rel_le_store_preserves_step with (Σ := Σ).
      * rewrite <- Heq_fresh. apply store_ty_extends_add. exact Hfresh_none.
      * exact Hval.
    + (* l <> fresh_loc st1: existing location *)
      rewrite store_lookup_update_neq; auto.
      rewrite Heq_fresh.
      rewrite store_lookup_update_neq; auto.
      * (* Extract lookup from Σ using update_neq *)
        rewrite store_ty_lookup_update_neq in Hlookup; auto.
        specialize (Htyped l T0 sl0 Hlookup).
        destruct (store_lookup l st1) eqn:Hl1, (store_lookup l st2) eqn:Hl2.
        -- (* Both Some: values are related in old stores *)
           apply val_rel_le_store_preserves_step with (Σ := Σ).
           ++ rewrite <- Heq_fresh. apply store_ty_extends_add. exact Hfresh_none.
           ++ exact Htyped.
        -- exact Htyped.
        -- exact Htyped.
        -- exact Htyped.
      * rewrite <- Heq_fresh. exact Hneql.
Qed.

(** ** Reference Location Relation

    For references, the key property is that related reference values
    point to the SAME location.
*)

(** Related reference values point to same location *)
Lemma val_rel_le_ref_same_loc : forall n Σ T sl v1 v2,
  n > 0 ->
  val_rel_le n Σ (TRef T sl) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l.
Proof.
  intros n Σ T sl v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as (_ & _ & _ & _ & HT).
  (* TRef case gives us the location *)
  exact HT.
Qed.

(** Build ref relation at any step *)
Lemma val_rel_le_build_ref : forall m Σ T sl l,
  val_rel_le m Σ (TRef T sl) (ELoc l) (ELoc l).
Proof.
  induction m as [|m' IH]; intros Σ T sl l.
  - simpl. exact I.
  - simpl. split.
    + apply IH.
    + unfold val_rel_struct. repeat split.
      * apply VLoc.
      * apply VLoc.
      * unfold closed_expr. intros x Hfree. inversion Hfree.
      * unfold closed_expr. intros x Hfree. inversion Hfree.
      * exists l. auto.
Qed.

(** ** Store Lookup Preserves Value Relation

    When we look up a location in related stores,
    the retrieved values are related.
*)

(** Looking up same location in related stores gives related values *)
Lemma store_rel_le_lookup : forall n Σ st1 st2 l T sl,
  store_rel_le n Σ st1 st2 ->
  store_ty_lookup l Σ = Some (T, sl) ->
  exists v1 v2,
    store_lookup l st1 = Some v1 /\
    store_lookup l st2 = Some v2 /\
    val_rel_le n Σ T v1 v2.
Proof.
  intros n Σ st1 st2 l T sl [Hmax Hlocs] Hlook.
  specialize (Hlocs l T sl Hlook).
  destruct (store_lookup l st1) as [v1|] eqn:Hst1;
  destruct (store_lookup l st2) as [v2|] eqn:Hst2; try contradiction.
  exists v1, v2. auto.
Qed.

(** ** Secret Value Relations

    For secrets, values are ALWAYS related (information hiding).
    This is critical for declassification soundness.
*)

(** Secrets are always related *)
Lemma val_rel_le_secret_always : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_le n Σ (TSecret T) v1 v2.
Proof.
  intros n Σ T v1 v2 Hv1 Hv2 Hc1 Hc2.
  apply val_rel_le_build_secret; auto.
Qed.

(** Extracting value/closed from secret relation *)
Lemma val_rel_le_secret_value_left : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ (TSecret T) v1 v2 ->
  value v1.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  apply val_rel_le_value_left with n Σ (TSecret T) v2; auto.
Qed.

Lemma val_rel_le_secret_value_right : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ (TSecret T) v1 v2 ->
  value v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  apply val_rel_le_value_right with n Σ (TSecret T) v1; auto.
Qed.

(** ** Unit Value Relations

    Unit values are always equal when related.
*)

(** Build unit relation *)
Lemma val_rel_le_unit : forall n Σ,
  val_rel_le n Σ TUnit EUnit EUnit.
Proof.
  intros n Σ.
  apply val_rel_le_build_unit.
Qed.

(** End of StoreRelation.v *)
