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
  nil; nil; Public ⊢ e : T ! ε ->
  value e \/ exists e' st' ctx', (e, st, ctx) --> (e', st', ctx').

(** ** Canonical Forms Lemmas *)

Lemma canonical_bool : forall Σ Δ v ε,
  nil; Σ; Δ ⊢ v : TBool ! ε ->
  value v ->
  exists b, v = EBool b.
Proof.
  intros Σ Δ v ε Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists b. reflexivity.
Qed.

Lemma canonical_fn : forall Σ Δ v T1 T2 ε ε',
  nil; Σ; Δ ⊢ v : (TFn T1 T2 ε) ! ε' ->
  value v ->
  exists x body, v = ELam x T1 body.
Proof.
  intros Σ Δ v T1 T2 ε ε' Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists x, e. reflexivity.
Qed.

Lemma canonical_pair : forall Σ Δ v T1 T2 ε,
  nil; Σ; Δ ⊢ v : (TProd T1 T2) ! ε ->
  value v ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros Σ Δ v T1 T2 ε Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  exists v1, v2. split; try split; auto.
Qed.

Lemma canonical_sum : forall Σ Δ v T1 T2 ε,
  nil; Σ; Δ ⊢ v : (TSum T1 T2) ! ε ->
  value v ->
  (exists v', v = EInl v' T2 /\ value v') \/
  (exists v', v = EInr v' T1 /\ value v').
Proof.
  intros Σ Δ v T1 T2 ε Hty Hval.
  inversion Hval; subst; inversion Hty; subst.
  - left. exists v0. split; auto.
  - right. exists v0. split; auto.
Qed.

(** ** Progress Theorem
    
    TODO: Complete the proof.
    This is a critical theorem for type safety.
*)

Theorem progress : progress_stmt.
Proof.
  unfold progress_stmt.
  intros e T ε st ctx Hty.
  remember nil as Γ.
  remember nil as Σ.
  remember Public as Δ.
  induction Hty; subst.
  - (* Unit *) left. constructor.
  - (* Bool *) left. constructor.
  - (* Int *) left. constructor.
  - (* String *) left. constructor.
  - (* Var *) inversion H.
  - (* Lam *) left. constructor.
  - (* App *)
    right.
    destruct IHHty1 as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]]; auto.
    + destruct IHHty2 as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]]; auto.
      * (* Both values *)
        destruct (canonical_fn nil Public e1 T1 T2 ε ε1 Hty1 Hv1) 
          as [x [body Heq]].
        subst.
        exists ([x := e2] body), st, ctx.
        apply ST_AppAbs. assumption.
      * (* e2 steps *)
        exists (EApp e1 e2'), st2', ctx2'.
        apply ST_App2; assumption.
    + (* e1 steps *)
      exists (EApp e1' e2), st1', ctx1'.
      apply ST_App1. assumption.
  (* TODO: Complete remaining cases *)
  - (* Pair *) 
    destruct IHHty1 as [Hv1 | [e1' [st1' [ctx1' Hstep1]]]]; auto.
    + destruct IHHty2 as [Hv2 | [e2' [st2' [ctx2' Hstep2]]]]; auto.
      * left. constructor; assumption.
      * right. exists (EPair e1 e2'), st2', ctx2'.
        apply ST_Pair2; assumption.
    + right. exists (EPair e1' e2), st1', ctx1'.
      apply ST_Pair1. assumption.
  - (* Fst *)
    destruct IHHty as [Hv | [e' [st' [ctx' Hstep]]]]; auto.
    + destruct (canonical_pair nil Public e T1 T2 ε Hty Hv)
        as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. right.
      exists v1, st, ctx. apply ST_Fst; assumption.
    + right. exists (EFst e'), st', ctx'.
      apply ST_FstStep. assumption.
  - (* Snd *)
    destruct IHHty as [Hv | [e' [st' [ctx' Hstep]]]]; auto.
    + destruct (canonical_pair nil Public e T1 T2 ε Hty Hv)
        as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. right.
      exists v2, st, ctx. apply ST_Snd; assumption.
    + right. exists (ESnd e'), st', ctx'.
      apply ST_SndStep. assumption.
  - (* Inl *) 
    destruct IHHty as [Hv | [e' [st' [ctx' Hstep]]]]; auto.
    + left. constructor. assumption.
    + right. (* Expression steps - need EInl congruence rule *)
      (* Note: Need to add ST_InlStep to semantics *)
      admit.
  - (* Inr *)
    destruct IHHty as [Hv | [e' [st' [ctx' Hstep]]]]; auto.
    + left. constructor. assumption.
    + right. admit.
  - (* Case *)
    destruct IHHty1 as [Hv | [e' [st' [ctx' Hstep]]]]; auto.
    + destruct (canonical_sum nil Public e T1 T2 ε Hty1 Hv)
        as [[v' [Heq Hv']] | [v' [Heq Hv']]]; subst.
      * right. exists ([x1 := v'] e1), st, ctx.
        apply ST_CaseInl. assumption.
      * right. exists ([x2 := v'] e2), st, ctx.
        apply ST_CaseInr. assumption.
    + right. exists (ECase e' x1 e1 x2 e2), st', ctx'.
      apply ST_CaseStep. assumption.
  - (* If *)
    destruct IHHty1 as [Hv | [e1' [st1' [ctx1' Hstep1]]]]; auto.
    + destruct (canonical_bool nil Public e1 ε1 Hty1 Hv) as [b Heq].
      subst. destruct b.
      * right. exists e2, st, ctx. apply ST_IfTrue.
      * right. exists e3, st, ctx. apply ST_IfFalse.
    + right. exists (EIf e1' e2 e3), st1', ctx1'.
      apply ST_IfStep. assumption.
  - (* Let *)
    destruct IHHty1 as [Hv | [e1' [st1' [ctx1' Hstep1]]]]; auto.
    + right. exists ([x := e1] e2), st, ctx.
      apply ST_LetValue. assumption.
    + right. exists (ELet x e1' e2), st1', ctx1'.
      apply ST_LetStep. assumption.
Admitted.  (* TODO: Remove Admitted once semantics includes all congruence rules *)

(** End of Progress.v *)
