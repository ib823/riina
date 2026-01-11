(** * Progress Theorem for TERAS-LANG

    If a closed, well-typed expression is not a value,
    then it can take a step.

    Reference: CTSS_v1_0_1.md, Section 6

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.
Import ListNotations.

(** ** Progress Statement *)

Definition progress_stmt := forall e T ε st ctx,
  has_type nil nil Public e T ε ->
  value e \/ exists e' st' ctx', (e, st, ctx) --> (e', st', ctx').

(** ** Canonical Forms Lemmas *)

Lemma canonical_bool : forall v ε,
  has_type nil nil Public v TBool ε ->
  value v ->
  exists b, v = EBool b.
Proof.
  intros v ε Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists b. reflexivity.
Qed.

Lemma canonical_fn : forall v T1 T2 ε ε',
  has_type nil nil Public v (TFn T1 T2 ε) ε' ->
  value v ->
  exists x body, v = ELam x T1 body.
Proof.
  intros v T1 T2 ε ε' Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists x, e. reflexivity.
Qed.

Lemma canonical_pair : forall v T1 T2 ε,
  has_type nil nil Public v (TProd T1 T2) ε ->
  value v ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros v T1 T2 ε Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists v1, v2. split; try split; auto.
Qed.

Lemma canonical_sum : forall v T1 T2 ε,
  has_type nil nil Public v (TSum T1 T2) ε ->
  value v ->
  (exists v', v = EInl v' T2 /\ value v') \/
  (exists v', v = EInr v' T1 /\ value v').
Proof.
  intros v T1 T2 ε Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  - left. exists v0. split; auto.
  - right. exists v0. split; auto.
Qed.

(** ** Progress Theorem

    The progress theorem states that a well-typed closed expression
    is either a value or can take a step.
*)

Theorem progress : progress_stmt.
Proof.
  unfold progress_stmt.
  intros e T ε st ctx Hty.
  remember (@nil (ident * ty)) as Γ eqn:HΓ.
  remember (@nil (loc * ty * security_level)) as Σ eqn:HΣ.
  remember Public as Δ eqn:HΔ.
  induction Hty; subst.
  (* T_Unit *)
  1: { left. constructor. }
  (* T_Bool *)
  1: { left. constructor. }
  (* T_Int *)
  1: { left. constructor. }
  (* T_String *)
  1: { left. constructor. }
  (* T_Var - impossible: lookup in empty context gives None *)
  1: { simpl in H. discriminate H. }
  (* T_Lam - lambdas are values *)
  1: { left. exact (VLam x T1 e). }
  - (* T_App *)
    destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]].
    + destruct (IHHty2 eq_refl eq_refl eq_refl) as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]].
      * (* Both values - can beta reduce *)
        destruct (canonical_fn e1 T1 T2 ε ε1 Hty1 Hv1) as [x [body Heq]].
        subst. right. exists ([x := e2] body), st, ctx.
        apply ST_AppAbs. assumption.
      * (* e2 steps *)
        right. exists (EApp e1 e2'), st2', ctx2'.
        apply ST_App2; assumption.
    + (* e1 steps *)
      right. exists (EApp e1' e2), st1', ctx1'.
      apply ST_App1; assumption.
  - (* T_Pair *)
    destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]].
    + destruct (IHHty2 eq_refl eq_refl eq_refl) as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]].
      * (* Both values - pair is a value *)
        left. constructor; assumption.
      * (* e2 steps *)
        right. exists (EPair e1 e2'), st2', ctx2'.
        apply ST_Pair2; assumption.
    + (* e1 steps *)
      right. exists (EPair e1' e2), st1', ctx1'.
      apply ST_Pair1; assumption.
  - (* T_Fst *)
    destruct (IHHty eq_refl eq_refl eq_refl) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_pair e T1 T2 ε Hty Hv) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. right. exists v1, st, ctx.
      apply ST_Fst; assumption.
    + right. exists (EFst e''), st'', ctx''.
      apply ST_FstStep; assumption.
  - (* T_Snd *)
    destruct (IHHty eq_refl eq_refl eq_refl) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_pair e T1 T2 ε Hty Hv) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. right. exists v2, st, ctx.
      apply ST_Snd; assumption.
    + right. exists (ESnd e''), st'', ctx''.
      apply ST_SndStep; assumption.
  - (* T_Inl *)
    destruct (IHHty eq_refl eq_refl eq_refl) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + left. constructor; assumption.
    + right. exists (EInl e'' T2), st'', ctx''.
      apply ST_InlStep; assumption.
  - (* T_Inr *)
    destruct (IHHty eq_refl eq_refl eq_refl) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + left. constructor; assumption.
    + right. exists (EInr e'' T1), st'', ctx''.
      apply ST_InrStep; assumption.
  - (* T_Case *)
    destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_sum e T1 T2 ε Hty1 Hv) as [[v' [Heq Hv']] | [v' [Heq Hv']]].
      * subst. right. exists ([x1 := v'] e1), st, ctx.
        apply ST_CaseInl; assumption.
      * subst. right. exists ([x2 := v'] e2), st, ctx.
        apply ST_CaseInr; assumption.
    + right. exists (ECase e'' x1 e1 x2 e2), st'', ctx''.
      apply ST_CaseStep; assumption.
  - (* T_If *)
    destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hv | [e1'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_bool e1 ε1 Hty1 Hv) as [b Heq].
      subst. destruct b.
      * right. exists e2, st, ctx. apply ST_IfTrue.
      * right. exists e3, st, ctx. apply ST_IfFalse.
    + right. exists (EIf e1'' e2 e3), st'', ctx''.
      apply ST_IfStep; assumption.
  - (* T_Let *)
    destruct (IHHty1 eq_refl eq_refl eq_refl) as [Hv | [e1'' [st'' [ctx'' Hstep]]]].
    + right. exists ([x := e1] e2), st, ctx.
      apply ST_LetValue; assumption.
    + right. exists (ELet x e1'' e2), st'', ctx''.
      apply ST_LetStep; assumption.
Qed.

(** End of Progress.v *)
