(** * StoreWfLemmas.v

    Helper lemmas for store well-formedness properties.

    Key lemma: store_wf implies store lookups return values.

    Mode: ULTRA KIASU | ZERO ADMITS
*)

Require Import String.
Require Import List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Import ListNotations.

(** Store well-formedness implies stored expressions are values *)
Lemma store_wf_lookup_value : forall Σ st l v,
  store_wf Σ st ->
  store_lookup l st = Some v ->
  value v.
Proof.
  intros Σ st l v Hwf Hlookup.
  destruct Hwf as [_ Hwf2].
  specialize (Hwf2 l v Hlookup).
  destruct Hwf2 as [T [sl [_ [Hval _]]]].
  exact Hval.
Qed.

(** Store well-formedness implies stored expressions are well-typed *)
Lemma store_wf_lookup_typed : forall Σ st l v,
  store_wf Σ st ->
  store_lookup l st = Some v ->
  exists T sl, store_ty_lookup l Σ = Some (T, sl) /\
               has_type nil Σ Public v T EffectPure.
Proof.
  intros Σ st l v Hwf Hlookup.
  destruct Hwf as [_ Hwf2].
  specialize (Hwf2 l v Hlookup).
  destruct Hwf2 as [T [sl [Hty_lookup [_ Htyped]]]].
  exists T, sl. split; assumption.
Qed.

(** For typed locations, lookup succeeds with a value *)
Lemma store_wf_typed_loc_has_value : forall Σ st l T sl,
  store_wf Σ st ->
  store_ty_lookup l Σ = Some (T, sl) ->
  exists v, store_lookup l st = Some v /\ value v.
Proof.
  intros Σ st l T sl Hwf Hty_lookup.
  destruct Hwf as [Hwf1 _].
  specialize (Hwf1 l T sl Hty_lookup).
  destruct Hwf1 as [v [Hlookup [Hval _]]].
  exists v. split; assumption.
Qed.

(** Combined: typed location lookup gives typed value *)
Lemma store_wf_typed_loc_gives_typed_value : forall Σ st l T sl,
  store_wf Σ st ->
  store_ty_lookup l Σ = Some (T, sl) ->
  exists v, store_lookup l st = Some v /\
            value v /\
            has_type nil Σ Public v T EffectPure.
Proof.
  intros Σ st l T sl Hwf Hty_lookup.
  destruct Hwf as [Hwf1 _].
  exact (Hwf1 l T sl Hty_lookup).
Qed.

(** End of file - ZERO ADMITS *)
