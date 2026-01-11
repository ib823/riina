(** * Type Safety for TERAS-LANG

    Combination of Progress and Preservation.

    Reference: CTSS_v1_0_1.md, Section 6

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.
Require Import TERAS.type_system.Progress.
Require Import TERAS.type_system.Preservation.

(** ** Type Safety Theorem

    Well-typed programs don't get stuck.
*)

Definition stuck (cfg : expr * store * effect_ctx) : Prop :=
  let '(e, st, ctx) := cfg in
  ~ value e /\ ~ exists cfg', cfg --> cfg'.

Theorem type_safety : forall e T ε st ctx,
  has_type nil nil Public e T ε ->
  ~ stuck (e, st, ctx).
Proof.
  intros e T ε st ctx Hty.
  unfold stuck. unfold not.
  intros [Hnval Hnstep].
  destruct (progress e T ε st ctx Hty) as [Hval | Hstep].
  - apply Hnval. assumption.
  - destruct Hstep as [e' [st' [ctx' Hstep']]].
    apply Hnstep. exists (e', st', ctx'). assumption.
Qed.

(** ** Multi-step Type Safety *)

(** Multi-step safety: well-typed terms stay well-typed after any
    number of steps. This is a direct consequence of preservation.
    NOTE: Admitted due to complexity of induction. TODO: Complete.
*)
Theorem multi_step_safety : forall e e' T ε st st' ctx ctx',
  has_type nil nil Public e T ε ->
  (e, st, ctx) -->* (e', st', ctx') ->
  ~ stuck (e', st', ctx').
Proof.
  intros e e' T ε st st' ctx ctx' Hty Hmulti.
  (* Proof by induction on multi-step relation, using preservation at each step *)
Admitted.

(** End of TypeSafety.v *)
