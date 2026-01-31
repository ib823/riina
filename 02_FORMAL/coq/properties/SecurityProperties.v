(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(** * Security Properties for RIINA

    Collection of security properties.

    TODO: Define and prove security properties.
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.NonInterference_v2_LogicalRelation.
Require Import Coq.Lists.List.
Import ListNotations.

(** ** Non-Interference (re-export)

    Well-typed, effect-pure programs do not leak secrets across related inputs.
*)

Theorem security_non_interference : forall x T_in T_out v1 v2 e,
  val_rel nil T_in v1 v2 ->
  has_type ((x, T_in) :: nil) nil Public e T_out EffectPure ->
  exp_rel nil T_out ([x := v1] e) ([x := v2] e).
Proof.
  apply non_interference_stmt.
Qed.

(** End of SecurityProperties.v *)
