(** * TERAS-LANG Operational Semantics
    
    Small-step operational semantics for TERAS-LANG.
    
    Reference: CTSS_v1_0_1.md, Section 5
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TERAS.foundations.Syntax.
Import ListNotations.

(** ** Store
    
    The store maps locations to values.
*)

Definition loc := nat.
Definition store := list (loc * expr).

(** Lookup in store *)
Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

(** Update in store *)
Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.

(** ** Effect Context
    
    Tracks which effects are currently available.
*)

Definition effect_ctx := list effect.

Definition has_effect (eff : effect) (ctx : effect_ctx) : Prop :=
  In eff ctx.

(** ** Small-Step Semantics
    
    The step relation: (e, st, ctx) --> (e', st', ctx')
*)

Reserved Notation "cfg1 '-->' cfg2" (at level 40).

Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  (* Beta reduction *)
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
  
  (* Application congruence *)
  | ST_App1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EApp e1 e2, st, ctx) --> (EApp e1' e2, st', ctx')
  
  | ST_App2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EApp v1 e2, st, ctx) --> (EApp v1 e2', st', ctx')
  
  (* Pair reduction *)
  | ST_Pair1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EPair e1 e2, st, ctx) --> (EPair e1' e2, st', ctx')
  
  | ST_Pair2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EPair v1 e2, st, ctx) --> (EPair v1 e2', st', ctx')
  
  (* Projections *)
  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
  
  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
  
  | ST_FstStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EFst e, st, ctx) --> (EFst e', st', ctx')
  
  | ST_SndStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ESnd e, st, ctx) --> (ESnd e', st', ctx')
  
  (* Sum elimination *)
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
  
  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
  
  | ST_CaseStep : forall e e' x1 e1 x2 e2 st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ECase e x1 e1 x2 e2, st, ctx) --> (ECase e' x1 e1 x2 e2, st', ctx')

  (* Sum construction congruence *)
  | ST_InlStep : forall e e' T st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EInl e T, st, ctx) --> (EInl e' T, st', ctx')

  | ST_InrStep : forall e e' T st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EInr e T, st, ctx) --> (EInr e' T, st', ctx')
  
  (* Conditionals *)
  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)
  
  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)
  
  | ST_IfStep : forall e1 e1' e2 e3 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EIf e1 e2 e3, st, ctx) --> (EIf e1' e2 e3, st', ctx')
  
  (* Let binding *)
  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)
  
  | ST_LetStep : forall x e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (ELet x e1 e2, st, ctx) --> (ELet x e1' e2, st', ctx')

  (* Effects *)
  | ST_PerformStep : forall eff e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EPerform eff e, st, ctx) --> (EPerform eff e', st', ctx')

  | ST_PerformValue : forall eff v st ctx,
      value v ->
      (EPerform eff v, st, ctx) --> (v, st, ctx)

  | ST_HandleStep : forall e e' x h st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EHandle e x h, st, ctx) --> (EHandle e' x h, st', ctx')

  | ST_HandleValue : forall v x h st ctx,
      value v ->
      (EHandle v x h, st, ctx) --> ([x := v] h, st, ctx)

  (* References *)
  | ST_RefStep : forall e e' l st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ERef e l, st, ctx) --> (ERef e' l, st', ctx')

  | ST_DerefStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EDeref e, st, ctx) --> (EDeref e', st', ctx')

  | ST_DerefRef : forall v l st ctx,
      value v ->
      (EDeref (ERef v l), st, ctx) --> (v, st, ctx)

  | ST_Assign1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EAssign e1 e2, st, ctx) --> (EAssign e1' e2, st', ctx')

  | ST_Assign2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EAssign v1 e2, st, ctx) --> (EAssign v1 e2', st', ctx')

  | ST_AssignRef : forall v1 v2 l st ctx,
      value v1 ->
      value v2 ->
      (EAssign (ERef v1 l) v2, st, ctx) --> (EUnit, st, ctx)

  | ST_ClassifyStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EClassify e, st, ctx) --> (EClassify e', st', ctx')

  | ST_Declassify1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EDeclassify e1 e2, st, ctx) --> (EDeclassify e1' e2, st', ctx')

  | ST_Declassify2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EDeclassify v1 e2, st, ctx) --> (EDeclassify v1 e2', st', ctx')

  | ST_DeclassifyValue : forall v p st ctx,
      value v ->
      value p ->
      (EDeclassify (EClassify v) p, st, ctx) --> (v, st, ctx)

  | ST_ProveStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EProve e, st, ctx) --> (EProve e', st', ctx')

  | ST_RequireStep : forall eff e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (ERequire eff e, st, ctx) --> (ERequire eff e', st', ctx')

  | ST_RequireValue : forall eff v st ctx,
      value v ->
      (ERequire eff v, st, ctx) --> (v, st, ctx)

  | ST_GrantStep : forall eff e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EGrant eff e, st, ctx) --> (EGrant eff e', st', ctx')

  | ST_GrantValue : forall eff v st ctx,
      value v ->
      (EGrant eff v, st, ctx) --> (v, st, ctx)

where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

(** ** Multi-step reduction *)

Inductive multi_step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg,
      multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).

(** ** Determinism *)

Lemma value_not_step : forall v st ctx cfg,
  value v -> ~ ((v, st, ctx) --> cfg).
Proof.
  intros v st ctx cfg Hv.
  generalize dependent ctx.
  generalize dependent st.
  generalize dependent cfg.
  induction Hv; intros cfg st ctx Hstep; inversion Hstep; subst;
  try match goal with
  | [ H : value ?v, H' : (?v, _, _) --> _ |- _ ] => apply (value_not_step v _ _ _) in H'; assumption
  end; eauto.
  (* Recursive cases *)
  - eapply IHHv1; eauto.
  - eapply IHHv2; eauto.
  - eapply IHHv; eauto.
  - eapply IHHv; eauto.
Qed.

(** Helper tactic for solving contradictions where a value steps *)
Ltac solve_val_step :=
  match goal with
  | [ H : (?v, _, _) --> _, Hv : value ?v |- _ ] =>
      exfalso; eapply value_not_step; [ apply Hv | apply H ]
  | [ H : (ELam _ _ _, _, _) --> _ |- _ ] =>
      exfalso; eapply value_not_step; [ constructor | apply H ]
  | [ H : (EPair _ _, _, _) --> _, Hv1 : value _, Hv2 : value _ |- _ ] =>
      exfalso; eapply value_not_step; [ apply VPair; assumption | apply H ]
  | [ H : (ERef ?v ?l, _, _) --> _, Hv : value ?v |- _ ] =>
      inversion H; subst;
      match goal with
      | Hs : (?v, _, _) --> _ |- _ =>
          exfalso; eapply value_not_step; [ apply Hv | apply Hs ]
      end
  | [ H : (EClassify ?v, _, _) --> _, Hv : value ?v |- _ ] =>
      inversion H; subst;
      match goal with
      | Hs : (?v, _, _) --> _ |- _ =>
          exfalso; eapply value_not_step; [ apply Hv | apply Hs ]
      end
  | [ H : (EInl _ _, _, _) --> _, Hv : value _ |- _ ] =>
      exfalso; eapply value_not_step; [ apply VInl; assumption | apply H ]
  | [ H : (EInr _ _, _, _) --> _, Hv : value _ |- _ ] =>
      exfalso; eapply value_not_step; [ apply VInr; assumption | apply H ]
  end.

(** Helper tactic for applying IH *)
Ltac solve_ih :=
  match goal with
  | [ H : (?e, _, _) --> ?cfg2, IH : forall c, (?e, _, _) --> c -> _ = c |- _ ] =>
      apply IH in H; injection H as Heq Hst Hctx; subst; reflexivity
  end.

Lemma step_deterministic : forall cfg cfg1 cfg2,
  cfg --> cfg1 ->
  cfg --> cfg2 ->
  cfg1 = cfg2.
Proof.
  intros cfg cfg1 cfg2 H1 H2.
  generalize dependent cfg2.
  induction H1; intros cfg2 H2; inversion H2; subst; try reflexivity.

  (* ST_AppAbs *)
  - solve_val_step. (* H2=App1 *)
  - solve_val_step. (* H2=App2 *)

  (* ST_App1 *)
  - solve_val_step. (* H2=AppAbs *)
  - solve_ih.       (* H2=App1 *)
  - solve_val_step. (* H2=App2 *)

  (* ST_App2 *)
  - solve_val_step. (* H2=AppAbs *)
  - solve_val_step. (* H2=App1 *)
  - solve_ih.       (* H2=App2 *)

  (* ST_Pair1 *)
  - solve_ih.
  - solve_val_step.

  (* ST_Pair2 *)
  - solve_val_step.
  - solve_ih.

  (* ST_Fst *)
  - match goal with | H : (EPair _ _, _, _) --> _ |- _ => inversion H; subst; solve_val_step end.

  (* ST_Snd *)
  - match goal with | H : (EPair _ _, _, _) --> _ |- _ => inversion H; subst; solve_val_step end.

  (* ST_FstStep *)
  - inversion H1; subst; solve_val_step.
  - solve_ih.

  (* ST_SndStep *)
  - inversion H1; subst; solve_val_step.
  - solve_ih.

  (* ST_CaseInl *)
  - match goal with | H : (EInl _ _, _, _) --> _ |- _ => inversion H; subst; solve_val_step end.

  (* ST_CaseInr *)
  - match goal with | H : (EInr _ _, _, _) --> _ |- _ => inversion H; subst; solve_val_step end.

  (* ST_CaseStep *)
  - inversion H1; subst; solve_val_step.
  - inversion H1; subst; solve_val_step.
  - solve_ih.

  (* ST_InlStep *)
  - solve_ih.

  (* ST_InrStep *)
  - solve_ih.

  (* ST_IfTrue *)
  - match goal with | H : (EBool _, _, _) --> _ |- _ => inversion H end.

  (* ST_IfFalse *)
  - match goal with | H : (EBool _, _, _) --> _ |- _ => inversion H end.

  (* ST_IfStep *)
  - inversion H1.
  - inversion H1.
  - solve_ih.

  (* ST_LetValue *)
  - solve_val_step.

  (* ST_LetStep *)
  - solve_val_step.
  - solve_ih.

  (* ST_PerformStep *)
  - solve_ih.
  - match goal with
    | Hs : (?e, _, _) --> _, Hv : value ?e |- _ =>
        exfalso; eapply value_not_step; [ exact Hv | exact Hs ]
    end.

  (* ST_PerformValue *)
  - try reflexivity.
    match goal with
    | Hs : (?e, _, _) --> _, Hv : value ?e |- _ =>
        exfalso; eapply value_not_step; [ exact Hv | exact Hs ]
    end.

  (* ST_HandleStep *)
  - solve_ih.
  - match goal with
    | Hs : (?e, _, _) --> _, Hv : value ?e |- _ =>
        exfalso; eapply value_not_step; [ exact Hv | exact Hs ]
    end.

  (* ST_HandleValue *)
  - try reflexivity.
    match goal with
    | Hs : (?e, _, _) --> _, Hv : value ?e |- _ =>
        exfalso; eapply value_not_step; [ exact Hv | exact Hs ]
    end.

  (* ST_RefStep *)
  - solve_ih.

  (* ST_DerefStep *)
  - solve_ih.
  - match goal with
    | Hs : (ERef ?v ?l, _, _) --> _, Hv : value ?v |- _ =>
        inversion Hs; subst;
        match goal with
        | Hs' : (?v, _, _) --> _ |- _ =>
            exfalso; eapply value_not_step; [ exact Hv | exact Hs' ]
        end
    end.

  (* ST_DerefRef *)
  - all: (
      match goal with
      | Hs : (ERef ?v ?l, _, _) --> _, Hv : value ?v |- _ =>
          inversion Hs; subst;
          match goal with
          | Hs' : (?v, _, _) --> _ |- _ =>
              exfalso; eapply value_not_step; [ exact Hv | exact Hs' ]
          end
      | _ => reflexivity
      end
    ).

  (* ST_Assign1 *)
  - solve_ih.
  - solve_val_step.
  - solve_val_step.

  (* ST_Assign2 *)
  - solve_val_step.
  - solve_ih.
  - solve_val_step.

  (* ST_AssignRef *)
  - match goal with
    | Hs : (ERef ?v ?l, _, _) --> _, Hv : value ?v |- _ =>
        inversion Hs; subst;
        match goal with
        | Hs' : (?v, _, _) --> _ |- _ =>
            exfalso; eapply value_not_step; [ exact Hv | exact Hs' ]
        end
    end.
  - match goal with
    | Hs : (?e, _, _) --> _, Hv : value ?e |- _ =>
        exfalso; eapply value_not_step; [ exact Hv | exact Hs ]
    end.

  (* ST_ClassifyStep *)
  - solve_ih.

  (* ST_Declassify1 *)
  - solve_ih.
  - solve_val_step.
  - solve_val_step.

  (* ST_Declassify2 *)
  - solve_val_step.
  - solve_ih.
  - solve_val_step.

  (* ST_DeclassifyValue *)
  - solve_val_step.
  - solve_val_step.

  (* ST_ProveStep *)
  - solve_ih.

  (* ST_RequireStep *)
  - solve_ih.
  - solve_val_step.

  (* ST_RequireValue *)
  - solve_val_step.

  (* ST_GrantStep *)
  - solve_ih.
  - solve_val_step.

  (* ST_GrantValue *)
  - solve_val_step.
Qed.

(** End of Semantics.v *)
