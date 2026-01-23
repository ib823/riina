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
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.NonInterference_v2.

Import ListNotations.

(** Store typing weakening for has_type.
    Standard Kripke property: if e has type T under store typing Σ,
    then e has type T under any extension Σ' of Σ.
    TODO: Prove via induction on typing derivation. *)
Axiom has_type_store_weakening : forall Γ Σ Σ' Δ e T ε,
  store_ty_extends Σ Σ' ->
  has_type Γ Σ Δ e T ε ->
  has_type Γ Σ' Δ e T ε.

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
  (sl : store_ty -> store -> store -> Prop) v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  val_rel_at_type Σ' sp vl sl T v1 v2.
Proof.
  induction T; intros Σ Σ' sp vl sl v1 v2 Hext Hrel; simpl in *; try exact Hrel.
  - (* TFn *)
    intros Σ'' Hext'' x y Hvx Hvy Hcx Hcy Hargs st1 st2 ctx Hstore.
    assert (Hext_Σ_Σ'' : store_ty_extends Σ Σ'').
    { apply store_ty_extends_trans_early with Σ'; assumption. }
    exact (Hrel Σ'' Hext_Σ_Σ'' x y Hvx Hvy Hcx Hcy Hargs st1 st2 ctx Hstore).
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
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    (* Simplify the conditional using Hfo *)
    rewrite Hfo in Hrel. rewrite Hfo.
    exact Hrel.
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in Hrel.
    rewrite Hfo in Hrel.
    destruct Hrel as [Hrec [Hv1 [Hv2 [Hc1 [Hc2 [Htyping Hrat]]]]]].
    rewrite val_rel_n_S_unfold.
    rewrite Hfo.
    repeat split; try assumption.
    + apply IHn with Σ; assumption.
    + apply (val_rel_at_type_fo_equiv T Σ' (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
      apply (val_rel_at_type_fo_equiv T Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
      exact Hrat.
Qed.

(** Store-typing monotonicity (Kripke strengthening) *)
Lemma val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  intros n Σ Σ' T. revert n Σ Σ'.
  apply ty_size_induction with (T := T).
  intros T' IH_type.
  induction n as [| n' IH_step]; intros Σ Σ' v1 v2 Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in Hrel.
    rewrite val_rel_n_0_unfold.
    destruct (first_order_type T') eqn:Hfo.
    + exact Hrel.
    + (* HO type at step 0: need typing weakening *)
      destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 [Hty1 Hty2]]]]].
      repeat split; try assumption.
      * apply has_type_store_weakening with Σ; assumption.
      * apply has_type_store_weakening with Σ; assumption.
  - (* n = S n' *)
    destruct (first_order_decidable_local T') as [Hfo | Hho].
    + apply val_rel_n_mono_store_fo with Σ; assumption.
    + rewrite val_rel_n_S_unfold in Hrel.
      rewrite Hho in Hrel.
      destruct Hrel as [Hrec [Hv1 [Hv2 [Hc1 [Hc2 [[Hty1 Hty2] Hrat]]]]]].
      rewrite val_rel_n_S_unfold.
      rewrite Hho.
      repeat split; try assumption.
      * apply (IH_step Σ Σ' v1 v2 Hext Hrec).
      * apply has_type_store_weakening with Σ; assumption.
      * apply has_type_store_weakening with Σ; assumption.
      * destruct T'; simpl in *; try exact Hrat; try contradiction.
        -- (* TFn *)
           intros Σ_ext Hext' x y Hvx Hvy Hcx Hcy Hargs st1 st2 ctx Hstore.
           assert (Hext_Σ_Σext : store_ty_extends Σ Σ_ext).
           { apply store_ty_extends_trans_early with Σ'; assumption. }
           exact (Hrat Σ_ext Hext_Σ_Σext x y Hvx Hvy Hcx Hcy Hargs st1 st2 ctx Hstore).
        -- (* TProd *)
           destruct Hrat as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
           exists x1, y1, x2, y2. repeat split; try assumption.
           ++ apply val_rel_at_type_mono_store with Σ; assumption.
           ++ apply val_rel_at_type_mono_store with Σ; assumption.
        -- (* TSum *)
           destruct Hrat as [[x1 [x2 [Heq1 [Heq2 Hrel1]]]] | [y1 [y2 [Heq1 [Heq2 Hrel2]]]]].
           ++ left. exists x1, x2. repeat split; try assumption.
              apply val_rel_at_type_mono_store with Σ; assumption.
           ++ right. exists y1, y2. repeat split; try assumption.
              apply val_rel_at_type_mono_store with Σ; assumption.
Qed.
