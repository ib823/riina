(** * Non-Interference for TERAS-LANG

    Information flow security property.

    TODO: Define and prove non-interference.
*)

Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.

(** Low-equivalence of expressions *)
Definition low_equiv (e1 e2 : expr) : Prop :=
  (* TODO: Define based on security levels *)
  True.

(** Non-interference statement *)
Definition non_interference := forall e1 e2 e1' e2' T st1 st2 st1' st2' ctx,
  has_type nil nil Public e1 T EffectPure ->
  has_type nil nil Public e2 T EffectPure ->
  low_equiv e1 e2 ->
  (e1, st1, ctx) -->* (e1', st1', ctx) ->
  (e2, st2, ctx) -->* (e2', st2', ctx) ->
  low_equiv e1' e2'.

(** End of NonInterference.v *)
