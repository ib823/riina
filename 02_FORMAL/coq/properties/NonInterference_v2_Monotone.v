(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * NonInterference_v2_Monotone.v

    Store-typing monotonicity lemmas for NonInterference_v2.

    Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md §4.2
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.type_system.Preservation.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.NonInterference_v2.

Import ListNotations.

(** Store typing weakening for has_type.
    Standard Kripke property: if e has type T under store typing Σ,
    then e has type T under any extension Σ' of Σ.
    PROVEN in Preservation.v as store_ty_extends_preserves_typing. *)
Definition has_type_store_weakening : forall Γ Σ Σ' Δ e T ε,
  store_ty_extends Σ Σ' ->
  has_type Γ Σ Δ e T ε ->
  has_type Γ Σ' Δ e T ε := store_ty_extends_preserves_typing.

(** Transitivity of store typing extension *)
Lemma store_ty_extends_trans_early : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
Proof.
  intros Σ1 Σ2 Σ3 H12 H23.
  unfold store_ty_extends in *.
  intros l T sl Hlook.
  apply H23. apply H12. exact Hlook.
Qed.

(** val_rel_at_type is covariant in Σ for all types *)
Lemma val_rel_at_type_mono_store : forall T Σ Σ'
  (sp : store_ty -> store -> store -> Prop)
  (vl : store_ty -> ty -> expr -> expr -> Prop)
  (sl : store_ty -> store -> store -> Prop)
  (svp : store_ty -> store -> store -> Prop) v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_at_type Σ sp vl sl svp T v1 v2 ->
  val_rel_at_type Σ' sp vl sl svp T v1 v2.
Proof.
  induction T; intros Σ Σ' sp vl sl svp v1 v2 Hext Hrel; simpl in *; try exact Hrel.
  - (* TFn *)
    intros Σ'' Hext'' x y Hvx Hvy Hcx Hcy Hargs st1 st2 ctx Hstore Hwf1 Hwf2 Hagree Hsvp.
    assert (Hext_Σ_Σ'' : store_ty_extends Σ Σ'').
    { apply store_ty_extends_trans_early with Σ'; assumption. }
    exact (Hrel Σ'' Hext_Σ_Σ'' x y Hvx Hvy Hcx Hcy Hargs st1 st2 ctx Hstore Hwf1 Hwf2 Hagree Hsvp).
  - (* TProd *)
    destruct Hrel as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    exists x1, y1, x2, y2. repeat split; try assumption.
    + apply IHT1 with Σ; assumption.
    + apply IHT2 with Σ; assumption.
  - (* TSum *)
    destruct Hrel as [[x1 [x2 [Heq1 [Heq2 Hrel1]]]] | [y1 [y2 [Heq1 [Heq2 Hrel2]]]]].
    + left. exists x1, x2. repeat split; try assumption.
      apply IHT1 with Σ; assumption.
    + right. exists y1, y2. repeat split; try assumption.
      apply IHT2 with Σ; assumption.
Qed.

(** First-order decidability helper *)
Lemma first_order_decidable_local : forall T,
  {first_order_type T = true} + {first_order_type T = false}.
Proof.
  induction T; simpl; try (left; reflexivity); try (right; reflexivity).
  - destruct IHT1 as [H1|H1]; destruct IHT2 as [H2|H2]; simpl;
      [left; rewrite H1, H2; reflexivity
      | right; rewrite H1, H2; reflexivity
      | right; rewrite H1, H2; reflexivity
      | right; rewrite H1, H2; reflexivity].
  - destruct IHT1 as [H1|H1]; destruct IHT2 as [H2|H2]; simpl;
      [left; rewrite H1, H2; reflexivity
      | right; rewrite H1, H2; reflexivity
      | right; rewrite H1, H2; reflexivity
      | right; rewrite H1, H2; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
  - destruct IHT as [H|H]; simpl; [left; rewrite H; reflexivity | right; rewrite H; reflexivity].
Qed.

(** Store-typing monotonicity for first-order types *)
Lemma val_rel_n_mono_store_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  induction n as [| n' IHn]; intros Σ Σ' T v1 v2 Hfo Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in *.
    destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 [Ht1 [Ht2 Hrat]]]]]].
    repeat split; try assumption.
    + apply (has_type_store_weakening nil Σ Σ' Public v1 T EffectPure Hext Ht1).
    + apply (has_type_store_weakening nil Σ Σ' Public v2 T EffectPure Hext Ht2).
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in *.
    destruct Hrel as [Hrec [Hv1 [Hv2 [Hc1 [Hc2 [Ht1 [Ht2 Hrat]]]]]]].
    split.
    + exact (IHn Σ Σ' T v1 v2 Hfo Hext Hrec).
    + repeat split; try assumption.
      * apply (has_type_store_weakening nil Σ Σ' Public v1 T EffectPure Hext Ht1).
      * apply (has_type_store_weakening nil Σ Σ' Public v2 T EffectPure Hext Ht2).
      * (* val_rel_at_type_n n' — need to case split on n' *)
        destruct n' as [| n''].
        -- (* n' = 0: val_rel_at_type_n 0 = True *)
           simpl. exact I.
        -- (* n' = S n'': val_rel_at_type_n (S n'') = val_rel_at_type *)
           apply val_rel_at_type_mono_store with Σ; assumption.
Qed.

(** Store-typing monotonicity (Kripke strengthening) *)
Lemma val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  induction n as [| n' IHn]; intros Σ Σ' T v1 v2 Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in *.
    destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 [Ht1 [Ht2 Hrat]]]]]].
    repeat split; try assumption.
    + apply (has_type_store_weakening nil Σ Σ' Public v1 T EffectPure Hext Ht1).
    + apply (has_type_store_weakening nil Σ Σ' Public v2 T EffectPure Hext Ht2).
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in *.
    destruct Hrel as [Hrec [Hv1 [Hv2 [Hc1 [Hc2 [Ht1 [Ht2 Hrat]]]]]]].
    split.
    + exact (IHn Σ Σ' T v1 v2 Hext Hrec).
    + repeat split; try assumption.
      * apply (has_type_store_weakening nil Σ Σ' Public v1 T EffectPure Hext Ht1).
      * apply (has_type_store_weakening nil Σ Σ' Public v2 T EffectPure Hext Ht2).
      * destruct n' as [| n''].
        -- simpl. exact I.
        -- apply val_rel_at_type_mono_store with Σ; assumption.
Qed.
