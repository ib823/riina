(** * RIINA Operational Semantics
    
    Small-step operational semantics for RIINA.
    
    Reference: CTSS_v1_0_1.md, Section 5
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import RIINA.foundations.Syntax.
Import ListNotations.

(** ** Store
    
    The store maps locations to values.
*)

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

(** Fresh location allocator *)
Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

Definition fresh_loc (st : store) : loc :=
  S (store_max st).

Lemma store_lookup_above_max : forall st l,
  store_max st < l ->
  store_lookup l st = None.
Proof.
  induction st as [| [l' v'] st' IH]; intros l Hlt; simpl in *.
  - reflexivity.
  - assert (l' < l) as Hlt1.
    { apply Nat.le_lt_trans with (m := Nat.max l' (store_max st')).
      - apply Nat.le_max_l.
      - exact Hlt. }
    assert (store_max st' < l) as Hlt2.
    { apply Nat.le_lt_trans with (m := Nat.max l' (store_max st')).
      - apply Nat.le_max_r.
      - exact Hlt. }
    simpl. destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      exfalso. apply (Nat.lt_irrefl l'). exact Hlt1.
    + apply IH. exact Hlt2.
Qed.

Lemma store_lookup_fresh : forall st,
  store_lookup (fresh_loc st) st = None.
Proof.
  intro st.
  unfold fresh_loc.
  apply store_lookup_above_max.
  apply Nat.lt_succ_diag_r.
Qed.

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

  | ST_RefValue : forall v sl st ctx l,
      value v ->
      l = fresh_loc st ->
      (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)

  | ST_DerefStep : forall e e' st st' ctx ctx',
      (e, st, ctx) --> (e', st', ctx') ->
      (EDeref e, st, ctx) --> (EDeref e', st', ctx')

  | ST_DerefLoc : forall v l st ctx,
      store_lookup l st = Some v ->
      (EDeref (ELoc l), st, ctx) --> (v, st, ctx)

  | ST_Assign1 : forall e1 e1' e2 st st' ctx ctx',
      (e1, st, ctx) --> (e1', st', ctx') ->
      (EAssign e1 e2, st, ctx) --> (EAssign e1' e2, st', ctx')

  | ST_Assign2 : forall v1 e2 e2' st st' ctx ctx',
      value v1 ->
      (e2, st, ctx) --> (e2', st', ctx') ->
      (EAssign v1 e2, st, ctx) --> (EAssign v1 e2', st', ctx')

  | ST_AssignLoc : forall v1 l st ctx,
      store_lookup l st = Some v1 ->
      forall v2,
        value v2 ->
        (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)

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
      declass_ok (EClassify v) p ->
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
  - eapply IHHv; eauto.
  - eapply IHHv; eauto.
Qed.

Lemma value_does_not_step : forall v st ctx e' st' ctx',
  value v ->
  (v, st, ctx) --> (e', st', ctx') ->
  False.
Proof.
  intros v st ctx e' st' ctx' Hv Hstep.
  eapply value_not_step; eauto.
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
  | [ H : (ELoc _, _, _) --> _ |- _ ] =>
      exfalso; eapply value_not_step; [ constructor | apply H ]
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

Ltac solve_det_ih :=
  match goal with
  | IH : forall t2 st2 ctx2,
           (?e, ?st, ?ctx) --> (t2, st2, ctx2) -> _,
    H : (?e, ?st, ?ctx) --> (?t2, ?st2, ?ctx2) |- _ =>
      specialize (IH _ _ _ H) as [Heq_t [Heq_st Heq_ctx]];
      subst;
      split; [reflexivity | split; reflexivity]
  end.

Ltac solve_det_ih_cfg :=
  match goal with
  | IH : forall cfg2, (?e, ?st, ?ctx) --> cfg2 -> _,
    H : (?e, ?st, ?ctx) --> ?cfg2 |- _ =>
      specialize (IH _ H); subst; reflexivity
  end.

Ltac solve_ctx_ih :=
  match goal with
  | IH : forall cfg2, (?e, ?st, ?ctx) --> cfg2 -> (?e', ?st', ?ctx') = cfg2,
    H : (?e, ?st, ?ctx) --> (?e2, ?st2, ?ctx2) |- _ =>
      specialize (IH _ H);
      inversion IH; subst; reflexivity
  end.

Ltac solve_val_step_pair :=
  match goal with
  | Hs : (EPair ?v1 ?v2, _, _) --> _,
    Hv1 : value ?v1,
    Hv2 : value ?v2 |- _ =>
      exfalso; eapply value_not_step; [ apply VPair; eauto | exact Hs ]
  end.

Theorem step_deterministic_cfg : forall cfg cfg1 cfg2,
  step cfg cfg1 ->
  step cfg cfg2 ->
  cfg1 = cfg2.
Proof.
  intros cfg cfg1 cfg2 H1 H2.
  generalize dependent cfg2.
  induction H1; intros cfg2 H2; inversion H2; subst;
    try solve_ctx_ih;
    try reflexivity;
    try solve_val_step_pair;
    try solve_val_step.
  - (* ST_AppAbs vs ST_App1 *)
    exfalso.
    pose proof (value_not_step (EPair v1 v2) st ctx (e', st', ctx')
                  (VPair v1 v2 H H0)) as Hns.
    apply Hns in H6.
    exact H6.
  - (* ST_AppAbs vs ST_App2 *)
    exfalso.
    pose proof (value_not_step (EPair v1 v2) st ctx (e', st', ctx')
                  (VPair v1 v2 H H0)) as Hns.
    apply Hns in H6.
    exact H6.
  - (* ST_App1 vs ST_AppAbs *)
    exfalso.
    pose proof (value_not_step (EPair v1 v2) st ctx (e', st', ctx')
                  (VPair v1 v2 H5 H6)) as Hns.
    apply Hns in H1.
    exact H1.
  - (* ST_App1 vs ST_App2 *)
    exfalso.
    pose proof (value_not_step (EPair v1 v2) st ctx (e', st', ctx')
                  (VPair v1 v2 H5 H6)) as Hns.
    apply Hns in H1.
    exact H1.
  - (* ST_App2 vs ST_AppAbs *)
    exfalso.
    pose proof (value_not_step (EInl v T) st ctx (e', st', ctx')
                  (VInl v T H)) as Hns.
    apply Hns in H9.
    exact H9.
  - (* ST_App2 vs ST_App1 *)
    exfalso.
    pose proof (value_not_step (EInr v T) st ctx (e', st', ctx')
                  (VInr v T H)) as Hns.
    apply Hns in H9.
    exact H9.
  - (* ST_Pair1 vs ST_Pair2 *)
    exfalso.
    pose proof (value_not_step (EInl v T) st ctx (e', st', ctx')
                  (VInl v T H9)) as Hns.
    apply Hns in H1.
    exact H1.
  - (* ST_Pair2 vs ST_Pair1 *)
    exfalso.
    pose proof (value_not_step (EInr v T) st ctx (e', st', ctx')
                  (VInr v T H9)) as Hns.
    apply Hns in H1.
    exact H1.
  - (* ST_Fst vs ST_FstStep *)
    exfalso.
    pose proof (value_not_step (EBool true) st ctx (e1', st', ctx')
                  (VBool true)) as Hns.
    apply Hns in H6.
    exact H6.
  - (* ST_Snd vs ST_SndStep *)
    exfalso.
    pose proof (value_not_step (EBool false) st ctx (e1', st', ctx')
                  (VBool false)) as Hns.
    apply Hns in H6.
    exact H6.
  - (* ST_FstStep vs ST_Fst *)
    exfalso.
    pose proof (value_not_step (EBool true) st ctx (e1', st', ctx')
                  (VBool true)) as Hns.
    apply Hns in H1.
    exact H1.
  - (* ST_SndStep vs ST_Snd *)
    exfalso.
    pose proof (value_not_step (EBool false) st ctx (e1', st', ctx')
                  (VBool false)) as Hns.
    apply Hns in H1.
    exact H1.
  - (* ST_CaseInl vs ST_CaseStep *)
    rewrite H in H5; inversion H5; subst; reflexivity.
  - (* ST_CaseInr vs ST_CaseStep *)
    destruct H8 as [v0 [Hv0 [He1 He2]]]; inversion He1; subst.
    exfalso.
    pose proof (value_not_step (EProve (EClassify v0)) st ctx (e2', st', ctx')
                  (VProve (EClassify v0) (VClassify v0 Hv0))) as Hns.
    apply Hns in H1.
    exact H1.
  - (* ST_CaseStep vs ST_CaseInl *)
    destruct H0 as [v0 [Hv0 [He1 He2]]]; inversion He1; subst.
    exfalso.
    pose proof (value_not_step (EProve (EClassify v0)) st ctx (e2', st', ctx')
                  (VProve (EClassify v0) (VClassify v0 Hv0))) as Hns.
    apply Hns in H8.
    exact H8.
Qed.

Theorem step_deterministic : forall t st ctx t1 st1 ctx1 t2 st2 ctx2,
  (t, st, ctx) --> (t1, st1, ctx1) ->
  (t, st, ctx) --> (t2, st2, ctx2) ->
  t1 = t2 /\ st1 = st2 /\ ctx1 = ctx2.
Proof.
  intros t st ctx t1 st1 ctx1 t2 st2 ctx2 H1 H2.
  pose proof (step_deterministic_cfg (t, st, ctx) (t1, st1, ctx1) (t2, st2, ctx2) H1 H2) as Heq.
  inversion Heq; subst; split; [reflexivity | split; reflexivity].
Qed.

(** End of Semantics.v *)
