(** * Preservation Theorem for TERAS-LANG
    
    If a well-typed expression takes a step,
    the resulting expression is also well-typed with the same type.
    
    Reference: CTSS_v1_0_1.md, Section 6
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.
Import ListNotations.

(** ** Preservation Statement *)

Definition preservation_stmt := forall e e' T ε st st' ctx ctx',
  nil; nil; Public ⊢ e : T ! ε ->
  (e, st, ctx) --> (e', st', ctx') ->
  nil; nil; Public ⊢ e' : T ! ε.

(** ** Substitution Lemma
    
    Key lemma: substitution preserves typing.
*)

Lemma substitution_preserves_typing : forall Γ Σ Δ x v e T1 T2 ε1 ε2,
  nil; Σ; Δ ⊢ v : T1 ! ε1 ->
  ((x, T1) :: Γ); Σ; Δ ⊢ e : T2 ! ε2 ->
  Γ; Σ; Δ ⊢ [x := v] e : T2 ! ε2.
Proof.
  (* TODO: Complete the proof *)
  (* This requires showing that substitution preserves types *)
  (* Key insight: replacing x with v of type T1 maintains type correctness *)
Admitted.

(** ** Preservation Theorem
    
    TODO: Complete the proof.
    This is a critical theorem for type safety.
*)

Theorem preservation : preservation_stmt.
Proof.
  unfold preservation_stmt.
  intros e e' T ε st st' ctx ctx' Hty Hstep.
  generalize dependent ε.
  generalize dependent T.
  induction Hstep; intros T ε Hty; inversion Hty; subst.
  - (* ST_AppAbs *)
    inversion H2; subst.
    eapply substitution_preserves_typing; eauto.
  - (* ST_App1 *)
    apply IHHstep in H2.
    eapply T_App; eauto.
  - (* ST_App2 *)
    apply IHHstep in H4.
    eapply T_App; eauto.
  - (* ST_Pair1 *)
    apply IHHstep in H2.
    eapply T_Pair; eauto.
  - (* ST_Pair2 *)
    apply IHHstep in H5.
    eapply T_Pair; eauto.
  - (* ST_Fst *)
    inversion H2; subst. assumption.
  - (* ST_Snd *)
    inversion H2; subst. assumption.
  - (* ST_FstStep *)
    apply IHHstep in H2.
    eapply T_Fst; eauto.
  - (* ST_SndStep *)
    apply IHHstep in H2.
    eapply T_Snd; eauto.
  - (* ST_CaseInl *)
    inversion H3; subst.
    eapply substitution_preserves_typing; eauto.
  - (* ST_CaseInr *)
    inversion H3; subst.
    eapply substitution_preserves_typing; eauto.
  - (* ST_CaseStep *)
    apply IHHstep in H3.
    eapply T_Case; eauto.
  - (* ST_IfTrue *)
    assumption.
  - (* ST_IfFalse *)
    assumption.
  - (* ST_IfStep *)
    apply IHHstep in H3.
    eapply T_If; eauto.
  - (* ST_LetValue *)
    eapply substitution_preserves_typing; eauto.
  - (* ST_LetStep *)
    apply IHHstep in H2.
    eapply T_Let; eauto.
Qed.

(** End of Preservation.v *)
