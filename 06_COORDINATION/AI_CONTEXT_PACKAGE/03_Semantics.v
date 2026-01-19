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

