(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * Progress Theorem for RIINA

    If a closed, well-typed expression is not a value,
    then it can take a step.

    Reference: CTSS_v1_0_1.md, Section 6

    Mode: Comprehensive Verification | Zero Trust
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Import ListNotations.

(** ** Progress Statement *)

Definition progress_stmt := forall e T ε st ctx Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  value e \/ exists e' st' ctx', (e, st, ctx) --> (e', st', ctx').

(** ** Canonical Forms Lemmas *)

Lemma canonical_bool : forall v ε Σ,
  has_type nil Σ Public v TBool ε ->
  value v ->
  exists b, v = EBool b.
Proof.
  intros v ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists b. reflexivity.
Qed.

Lemma canonical_fn : forall v T1 T2 ε ε' Σ,
  has_type nil Σ Public v (TFn T1 T2 ε) ε' ->
  value v ->
  exists x body, v = ELam x T1 body.
Proof.
  intros v T1 T2 ε ε' Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists x, e. reflexivity.
Qed.

Lemma canonical_pair : forall v T1 T2 ε Σ,
  has_type nil Σ Public v (TProd T1 T2) ε ->
  value v ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros v T1 T2 ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists v1, v2. split; try split; auto.
Qed.

Lemma canonical_sum : forall v T1 T2 ε Σ,
  has_type nil Σ Public v (TSum T1 T2) ε ->
  value v ->
  (exists v', v = EInl v' T2 /\ value v') \/
  (exists v', v = EInr v' T1 /\ value v').
Proof.
  intros v T1 T2 ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  - left. exists v0. split; auto.
  - right. exists v0. split; auto.
Qed.

Lemma canonical_ref : forall v T l ε Σ,
  has_type nil Σ Public v (TRef T l) ε ->
  value v ->
  exists l', v = ELoc l'.
Proof.
  intros v T l ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists l0. reflexivity.
Qed.

Lemma canonical_secret : forall v T ε Σ,
  has_type nil Σ Public v (TSecret T) ε ->
  value v ->
  exists v', v = EClassify v' /\ value v'.
Proof.
  intros v T ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists v0. split; auto.
Qed.

Lemma canonical_proof : forall v T ε Σ,
  has_type nil Σ Public v (TProof T) ε ->
  value v ->
  exists v', v = EProve v' /\ value v'.
Proof.
  intros v T ε Σ Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists v0. split; auto.
Qed.

Lemma lookup_nil_contra : forall x T,
  lookup x nil = Some T ->
  False.
Proof.
  intros x T H.
  simpl in H.
  discriminate H.
Qed.

(** ** Progress Theorem

    The progress theorem states that a well-typed closed expression
    is either a value or can take a step.
*)

Theorem progress : progress_stmt.
Proof.
  unfold progress_stmt.
  intros e T ε st ctx Σ Hty Hwf.
  remember (@nil (ident * ty)) as Γ eqn:HΓ.
  remember Public as Δ eqn:HΔ.
  induction Hty; subst.
  - (* T_Unit *)
    left. constructor.
  - (* T_Bool *)
    left. constructor.
  - (* T_Int *)
    left. constructor.
  - (* T_String *)
    left. constructor.
  - (* T_Loc *)
    left. constructor.
  - (* T_Var - impossible: lookup in empty context gives None *)
    simpl in H. discriminate H.
  - (* T_Lam - lambdas are values *)
    left. exact (VLam x T1 e).
  - (* T_App *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]].
    + destruct (IHHty2 eq_refl eq_refl Hwf) as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]].
      * (* Both values - can beta reduce *)
        destruct (canonical_fn e1 T1 T2 ε ε1 Σ Hty1 Hv1) as [x [body Heq]].
        subst. right. exists ([x := e2] body), st, ctx.
        apply ST_AppAbs. assumption.
      * (* e2 steps *)
        right. exists (EApp e1 e2'), st2', ctx2'.
        apply ST_App2; assumption.
    + (* e1 steps *)
      right. exists (EApp e1' e2), st1', ctx1'.
      apply ST_App1; assumption.
  - (* T_Pair *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]].
    + destruct (IHHty2 eq_refl eq_refl Hwf) as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]].
      * (* Both values - pair is a value *)
        left. constructor; assumption.
      * (* e2 steps *)
        right. exists (EPair e1 e2'), st2', ctx2'.
        apply ST_Pair2; assumption.
    + (* e1 steps *)
      right. exists (EPair e1' e2), st1', ctx1'.
      apply ST_Pair1; assumption.
  - (* T_Fst *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_pair e T1 T2 ε Σ Hty Hv) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. right. exists v1, st, ctx.
      apply ST_Fst; assumption.
    + right. exists (EFst e''), st'', ctx''.
      apply ST_FstStep; assumption.
  - (* T_Snd *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_pair e T1 T2 ε Σ Hty Hv) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. right. exists v2, st, ctx.
      apply ST_Snd; assumption.
    + right. exists (ESnd e''), st'', ctx''.
      apply ST_SndStep; assumption.
  - (* T_Inl *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + left. constructor; assumption.
    + right. exists (EInl e'' T2), st'', ctx''.
      apply ST_InlStep; assumption.
  - (* T_Inr *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + left. constructor; assumption.
    + right. exists (EInr e'' T1), st'', ctx''.
      apply ST_InrStep; assumption.
  - (* T_Case *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv | [e'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_sum e T1 T2 ε Σ Hty1 Hv) as [[v' [Heq Hv']] | [v' [Heq Hv']]].
      * subst. right. exists ([x1 := v'] e1), st, ctx.
        apply ST_CaseInl; assumption.
      * subst. right. exists ([x2 := v'] e2), st, ctx.
        apply ST_CaseInr; assumption.
    + right. exists (ECase e'' x1 e1 x2 e2), st'', ctx''.
      apply ST_CaseStep; assumption.
  - (* T_If *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv | [e1'' [st'' [ctx'' Hstep]]]].
    + destruct (canonical_bool e1 ε1 Σ Hty1 Hv) as [b Heq].
      subst. destruct b.
      * right. exists e2, st, ctx. apply ST_IfTrue.
      * right. exists e3, st, ctx. apply ST_IfFalse.
    + right. exists (EIf e1'' e2 e3), st'', ctx''.
      apply ST_IfStep; assumption.
  - (* T_Let *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv | [e1'' [st'' [ctx'' Hstep]]]].
    + right. exists ([x := e1] e2), st, ctx.
      apply ST_LetValue; assumption.
    + right. exists (ELet x e1'' e2), st'', ctx''.
      apply ST_LetStep; assumption.

  - (* T_Perform *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + right. exists e, st, ctx. apply ST_PerformValue; assumption.
    + right. exists (EPerform eff e'), st', ctx'. apply ST_PerformStep; assumption.

  - (* T_Handle *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + right. exists ([x := e] h), st, ctx. apply ST_HandleValue; assumption.
    + right. exists (EHandle e' x h), st', ctx'. apply ST_HandleStep; assumption.

  - (* T_Ref *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + right. exists (ELoc (fresh_loc st)), (store_update (fresh_loc st) e st), ctx.
      apply ST_RefValue; auto.
    + right. exists (ERef e' l), st', ctx'. apply ST_RefStep; assumption.

  - (* T_Deref *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + destruct (canonical_ref e T l ε Σ Hty Hv) as [l' Heq]. subst.
      inversion Hty; subst.
      destruct (proj1 Hwf l' T l) as [v [Hlookup Htyv]].
      * assumption.
      * right. exists v, st, ctx. apply ST_DerefLoc; assumption.
    + right. exists (EDeref e'), st', ctx'. apply ST_DerefStep; assumption.

  - (* T_Assign *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]].
    + destruct (canonical_ref e1 T l ε1 Σ Hty1 Hv1) as [l' Heq]. subst.
      inversion Hty1; subst.
      destruct (proj1 Hwf l' T l) as [v1 [Hlookup Htyv]].
      * assumption.
      * destruct (IHHty2 eq_refl eq_refl Hwf) as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]].
        { right. exists EUnit, (store_update l' e2 st), ctx.
          eapply ST_AssignLoc with (v1 := v1); eauto. }
        { right. exists (EAssign (ELoc l') e2'), st2', ctx2'. apply ST_Assign2; assumption. }
    + right. exists (EAssign e1' e2), st1', ctx1'. apply ST_Assign1; assumption.

  - (* T_Classify *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + left. apply VClassify. assumption.
    + right. exists (EClassify e'), st', ctx'. apply ST_ClassifyStep; assumption.

  - (* T_Declassify *)
    destruct (IHHty1 eq_refl eq_refl Hwf) as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]].
    + destruct (canonical_secret e1 T ε1 Σ Hty1 Hv1) as [v1 [Heq Hv1']]. subst.
      destruct (IHHty2 eq_refl eq_refl Hwf) as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]].
      * destruct H as [v' [Hv' [He1 He2]]]. inversion He1; subst v'.
        rewrite He2 in *.
        right. exists v1, st, ctx.
        eapply ST_DeclassifyValue.
        { exact Hv1'. }
        { exists v1. split.
          - exact Hv'.
          - split; reflexivity. }
      * right. exists (EDeclassify (EClassify v1) e2'), st2', ctx2'. apply ST_Declassify2; assumption.
    + right. exists (EDeclassify e1' e2), st1', ctx1'. apply ST_Declassify1; assumption.

  - (* T_Prove *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + left. apply VProve. assumption.
    + right. exists (EProve e'), st', ctx'. apply ST_ProveStep; assumption.

  - (* T_Require *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + right. exists e, st, ctx. apply ST_RequireValue; assumption.
    + right. exists (ERequire eff e'), st', ctx'. apply ST_RequireStep; assumption.

  - (* T_Grant *)
    destruct (IHHty eq_refl eq_refl Hwf) as [Hv | [e' [st' [ctx' Hstep]]]].
    + right. exists e, st, ctx. apply ST_GrantValue; assumption.
    + right. exists (EGrant eff e'), st', ctx'. apply ST_GrantStep; assumption.
Qed.

(** End of Progress.v *)
