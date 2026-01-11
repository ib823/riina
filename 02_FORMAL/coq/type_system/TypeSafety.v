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
  nil; nil; Public ⊢ e : T ! ε ->
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

Theorem multi_step_safety : forall e e' T ε st st' ctx ctx',
  nil; nil; Public ⊢ e : T ! ε ->
  (e, st, ctx) -->* (e', st', ctx') ->
  ~ stuck (e', st', ctx').
Proof.
  intros e e' T ε st st' ctx ctx' Hty Hmulti.
  induction Hmulti.
  - apply type_safety with T ε. assumption.
  - apply IHHmulti.
    apply preservation with e st ctx; assumption.
Qed.

(** End of TypeSafety.v *)
