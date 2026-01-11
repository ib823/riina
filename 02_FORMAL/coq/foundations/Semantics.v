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

where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

(** ** Multi-step reduction *)

Inductive multi_step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg,
      multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 40).

(** ** Determinism
    
    The semantics is deterministic.
*)

Lemma value_not_step : forall v st ctx cfg,
  value v -> ~ ((v, st, ctx) --> cfg).
Proof.
  intros v st ctx cfg Hv.
  generalize dependent ctx.
  generalize dependent st.
  generalize dependent cfg.
  induction Hv; intros cfg st ctx Hstep; inversion Hstep; subst.
  - (* VPair, ST_Pair1 *) eapply IHHv1; eauto.
  - (* VPair, ST_Pair2 *) eapply IHHv2; eauto.
  - (* VInl, ST_InlStep *) eapply IHHv; eauto.
  - (* VInr, ST_InrStep *) eapply IHHv; eauto.
Qed.

(** The determinism proof requires careful case analysis. Each step rule
    must be shown to produce a unique result. The proof follows by induction
    on the first derivation and case analysis on the second.

    TODO: Complete this proof. The key cases involve showing that:
    1. Values cannot step (proven in value_not_step)
    2. When the same redex matches two rules, they must be the same rule
    3. The IH applies for congruence rules
*)
Lemma step_deterministic : forall cfg cfg1 cfg2,
  cfg --> cfg1 ->
  cfg --> cfg2 ->
  cfg1 = cfg2.
Proof.
  intros cfg cfg1 cfg2 H1 H2.
  generalize dependent cfg2.
  induction H1; intros cfg2 H2; inversion H2; subst;
    try reflexivity;
    try (exfalso; eapply value_not_step; eauto; fail).
  (* Application cases *)
  all: try match goal with
       | [ H : step (ELam _ _ _, _, _) _ |- _ ] => inversion H
       end.
  all: try match goal with
       | [ Hv : value ?v |- EApp ?e ?v2 = EApp ?e' ?v2 ] =>
           f_equal; f_equal; apply IHstep; assumption
       end.
  all: try match goal with
       | [ |- EApp ?e ?v = EApp ?e ?v' ] =>
           f_equal; apply IHstep; assumption
       end.
  (* Pair cases *)
  all: try match goal with
       | [ |- EPair ?e1 ?e2 = EPair ?e1' ?e2 ] =>
           f_equal; f_equal; apply IHstep; assumption
       end.
  all: try match goal with
       | [ |- EPair ?v ?e = EPair ?v ?e' ] =>
           f_equal; apply IHstep; assumption
       end.
  (* Fst/Snd cases *)
  all: try match goal with
       | [ H : step (EPair _ _, _, _) _ |- _ ] =>
           inversion H; subst; exfalso; eapply value_not_step;
           [constructor; eassumption | eassumption]
       end.
  all: try match goal with
       | [ |- EFst ?e = EFst ?e' ] =>
           f_equal; apply IHstep; assumption
       end.
  all: try match goal with
       | [ |- ESnd ?e = ESnd ?e' ] =>
           f_equal; apply IHstep; assumption
       end.
  (* Case cases *)
  all: try match goal with
       | [ H : step (EInl _ _, _, _) _ |- _ ] =>
           inversion H; subst; exfalso; eapply value_not_step;
           [constructor; eassumption | eassumption]
       end.
  all: try match goal with
       | [ H : step (EInr _ _, _, _) _ |- _ ] =>
           inversion H; subst; exfalso; eapply value_not_step;
           [constructor; eassumption | eassumption]
       end.
  all: try match goal with
       | [ |- ECase ?e _ _ _ _ = ECase ?e' _ _ _ _ ] =>
           f_equal; apply IHstep; assumption
       end.
  (* If cases *)
  all: try match goal with
       | [ H : step (EBool _, _, _) _ |- _ ] => inversion H
       end.
  all: try match goal with
       | [ |- EIf ?e _ _ = EIf ?e' _ _ ] =>
           f_equal; apply IHstep; assumption
       end.
  (* Let cases *)
  all: try match goal with
       | [ |- ELet _ ?e _ = ELet _ ?e' _ ] =>
           f_equal; apply IHstep; assumption
       end.
Admitted. (* TODO: Some edge cases remain - complete this proof *)

(** End of Semantics.v *)
