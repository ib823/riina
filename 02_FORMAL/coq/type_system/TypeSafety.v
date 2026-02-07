(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * Type Safety for RIINA

    Combination of Progress and Preservation.

    Reference: CTSS_v1_0_1.md, Section 6

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Progress.
Require Import RIINA.type_system.Preservation.

(** ** Type Safety Theorem

    Well-typed programs don't get stuck.
*)

Definition stuck (cfg : expr * store * effect_ctx) : Prop :=
  let '(e, st, ctx) := cfg in
  ~ value e /\ ~ exists cfg', cfg --> cfg'.

Theorem type_safety : forall e T ε st ctx Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  ~ stuck (e, st, ctx).
Proof.
  intros e T ε st ctx Σ Hty Hwf.
  unfold stuck. unfold not.
  intros [Hnval Hnstep].
  destruct (progress e T ε st ctx Σ Hty Hwf) as [Hval | Hstep].
  - apply Hnval. assumption.
  - destruct Hstep as [e' [st' [ctx' Hstep']]].
    apply Hnstep. exists (e', st', ctx'). assumption.
Qed.

(** ** Multi-step Type Safety *)

(** Multi-step safety: well-typed terms stay well-typed after any
    number of steps. This is a direct consequence of preservation.
*)
Theorem multi_step_safety : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  (e, st, ctx) -->* (e', st', ctx') ->
  exists Σ', store_wf Σ' st' /\ ~ stuck (e', st', ctx').
Proof.
  intros e e' T ε st st' ctx ctx' Σ Hty Hwf Hmulti.
  (* Proof by induction on multi-step relation, using preservation at each step *)
  remember (e, st, ctx) as cfg1 eqn:Heq1.
  remember (e', st', ctx') as cfg2 eqn:Heq2.
  generalize dependent ctx'. generalize dependent st'. generalize dependent e'.
  generalize dependent ε. generalize dependent T.
  generalize dependent ctx. generalize dependent st. generalize dependent e.
  generalize dependent Σ.
  induction Hmulti; intros Σ e1 st1 Hwf1 ctx1 Heq1 T ε Hty e2 st2 ctx2 Heq2.
  - (* MS_Refl: cfg = cfg' *)
    repeat match goal with
    | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
    | H : ?x = (_, _, _) |- _ => inversion H; subst; clear H
    | H : (_, _, _) = ?x |- _ => inversion H; subst; clear H
    | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
    | H : ?x = (_, _) |- _ => inversion H; subst; clear H
    | H : (_, _) = ?x |- _ => inversion H; subst; clear H
    end.
    exists Σ. split; [exact Hwf1 | eapply type_safety; eassumption].
  - (* MS_Step: cfg1 --> cfg2 --> cfg3 *)
    repeat match goal with
    | H : (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
    | H : ?x = (_, _, _) |- _ => inversion H; subst; clear H
    | H : (_, _, _) = ?x |- _ => inversion H; subst; clear H
    | H : (_, _) = (_, _) |- _ => inversion H; subst; clear H
    | H : ?x = (_, _) |- _ => inversion H; subst; clear H
    | H : (_, _) = ?x |- _ => inversion H; subst; clear H
    end.
    destruct cfg2 as [[e_mid st_mid] ctx_mid].
    (* preservation now returns an existential *)
    destruct (preservation e1 e_mid T ε st1 st_mid ctx1 ctx_mid Σ Hty Hwf1 H)
      as [Σ' [ε' [Hext [Hwf' Hty']]]].
    eapply IHHmulti with (Σ := Σ') (e := e_mid) (st := st_mid) (ctx := ctx_mid)
                         (T := T) (ε := ε') (e' := e2) (st' := st2) (ctx' := ctx2);
      [exact Hwf' | reflexivity | exact Hty' | reflexivity].
Qed.

(** End of TypeSafety.v *)
