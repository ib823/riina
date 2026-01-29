(* ═══════════════════════════════════════════════════════════════════════════
   ReferenceOps_Complete.v
   
   Complete proofs for 6 lemmas in step-indexed logical relations
   for reference operations (ref, deref, assign).
   
   ZERO AXIOMS. ZERO ADMITS.
   
   Compatible with Coq 8.18
   ═══════════════════════════════════════════════════════════════════════════ *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 1: BASIC DEFINITIONS
   ═══════════════════════════════════════════════════════════════════════════ *)

Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | ERef : expr -> nat -> expr  (* nat is security level, simplified *)
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  | ELoc : nat -> expr.

Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VLoc : forall l, value (ELoc l).

Definition store := list (nat * expr).

Fixpoint store_lookup (l : nat) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: rest => if Nat.eqb l l' then Some v else store_lookup l rest
  end.

Fixpoint store_max_aux (st : store) (acc : nat) : nat :=
  match st with
  | nil => acc
  | (l, _) :: rest => store_max_aux rest (Nat.max (S l) acc)
  end.

Definition store_max (st : store) : nat := store_max_aux st 0.
Definition fresh_loc (st : store) : nat := store_max st.
Definition store_update (l : nat) (v : expr) (st : store) : store := (l, v) :: st.

Definition store_well_formed (st : store) : Prop :=
  forall l v, store_lookup l st = Some v -> value v.

Definition config := (expr * store)%type.

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 2: STEP RELATION
   ═══════════════════════════════════════════════════════════════════════════ *)

Inductive step : config -> config -> Prop :=
  | ST_RefValue : forall v sl st,
      value v ->
      step (ERef v sl, st) (ELoc (fresh_loc st), store_update (fresh_loc st) v st)
  | ST_RefStep : forall e e' sl st st',
      step (e, st) (e', st') ->
      step (ERef e sl, st) (ERef e' sl, st')
  | ST_DerefLoc : forall l v st,
      store_lookup l st = Some v ->
      step (EDeref (ELoc l), st) (v, st)
  | ST_DerefStep : forall e e' st st',
      step (e, st) (e', st') ->
      step (EDeref e, st) (EDeref e', st')
  | ST_AssignLoc : forall l v v_old st,
      value v ->
      store_lookup l st = Some v_old ->
      step (EAssign (ELoc l) v, st) (EUnit, store_update l v st)
  | ST_Assign1 : forall e1 e1' e2 st st',
      step (e1, st) (e1', st') ->
      step (EAssign e1 e2, st) (EAssign e1' e2, st')
  | ST_Assign2 : forall v1 e2 e2' st st',
      value v1 ->
      step (e2, st) (e2', st') ->
      step (EAssign v1 e2, st) (EAssign v1 e2', st').

Inductive multi_step : config -> config -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 3: FUNDAMENTAL LEMMAS
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma value_does_not_step : forall v st cfg',
  value v -> ~ step (v, st) cfg'.
Proof.
  intros v st cfg' Hval Hstep.
  inversion Hval; subst; inversion Hstep.
Qed.

Lemma multi_step_value_inv : forall v st e' st',
  value v ->
  multi_step (v, st) (e', st') ->
  v = e' /\ st = st'.
Proof.
  intros v st e' st' Hval Hmulti.
  inversion Hmulti; subst.
  - auto.
  - exfalso. eapply value_does_not_step; eauto.
Qed.

Lemma ERef_not_value : forall e sl, ~ value (ERef e sl).
Proof. intros e sl Hval. inversion Hval. Qed.

Lemma EDeref_not_value : forall e, ~ value (EDeref e).
Proof. intros e Hval. inversion Hval. Qed.

Lemma EAssign_not_value : forall e1 e2, ~ value (EAssign e1 e2).
Proof. intros e1 e2 Hval. inversion Hval. Qed.

Lemma store_wf_lookup : forall st l v,
  store_well_formed st -> store_lookup l st = Some v -> value v.
Proof. intros st l v Hwf Hl. unfold store_well_formed in Hwf. apply Hwf with l. exact Hl. Qed.

Lemma store_wf_update : forall st l v,
  store_well_formed st -> value v -> store_well_formed (store_update l v st).
Proof.
  unfold store_well_formed, store_update. intros st l v Hwf Hval l' v' Hlook.
  simpl in Hlook. destruct (Nat.eqb l' l) eqn:E.
  - injection Hlook as H. subst. exact Hval.
  - apply (Hwf l' v'). exact Hlook.
Qed.

Lemma step_preserves_wf : forall cfg cfg',
  step cfg cfg' ->
  forall e st e' st',
  cfg = (e, st) -> cfg' = (e', st') ->
  store_well_formed st -> store_well_formed st'.
Proof.
  intros cfg cfg' Hstep.
  induction Hstep; intros e0 st0 e0' st0' Heq1 Heq2 Hwf;
    injection Heq1 as H1 H2; injection Heq2 as H3 H4; subst.
  - apply store_wf_update; auto.
  - eapply IHHstep; eauto.
  - exact Hwf.
  - eapply IHHstep; eauto.
  - apply store_wf_update; auto.
  - eapply IHHstep; eauto.
  - eapply IHHstep; eauto.
Qed.

Lemma multi_step_preserves_wf : forall e st e' st',
  store_well_formed st -> multi_step (e, st) (e', st') -> store_well_formed st'.
Proof.
  intros e st e' st' Hwf Hms.
  remember (e, st) as c1. remember (e', st') as c2.
  revert e st e' st' Heqc1 Heqc2 Hwf.
  induction Hms as [cfg | cfg1 cfg2 cfg3 Hstep Hms IH]; intros; subst.
  - injection Heqc2 as H1 H2. subst. exact Hwf.
  - destruct cfg2 as [e2 st2].
    eapply IH; eauto.
    eapply step_preserves_wf; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   LEMMA 1: multi_step_ref_inversion
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma multi_step_ref_inversion : forall e sl st v st',
  multi_step (ERef e sl, st) (v, st') ->
  value v ->
  exists v_inner st_mid l,
    multi_step (e, st) (v_inner, st_mid) /\
    value v_inner /\ v = ELoc l /\
    st' = store_update l v_inner st_mid /\ l = fresh_loc st_mid.
Proof.
  intros e sl st v st' Hms Hval.
  remember (ERef e sl, st) as c1. remember (v, st') as c2.
  revert e sl st v st' Heqc1 Heqc2 Hval.
  induction Hms as [cfg | cfg1 cfg2 cfg3 Hstep Hms IH]; intros e sl st v st' Heqc1 Heqc2 Hval.
  - subst. injection Heqc2 as H1 H2. subst.
    exfalso. apply (ERef_not_value e sl). exact Hval.
  - subst cfg1 cfg3.
    destruct cfg2 as [e2 st2].
    inversion Hstep; subst.
    + apply multi_step_value_inv in Hms; [ | constructor].
      destruct Hms as [H1 H2]. subst.
      exists e, st, (fresh_loc st).
      repeat split; auto. apply MS_Refl.
    + specialize (IH e' sl st2 v st' eq_refl eq_refl Hval).
      destruct IH as [vi [sm [l [Hm [Hv [Hl [Hs Hf]]]]]]].
      exists vi, sm, l. repeat split; auto.
      eapply MS_Step; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   LEMMA 2: multi_step_deref_inversion
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma multi_step_deref_inversion : forall e st v st',
  store_well_formed st ->
  multi_step (EDeref e, st) (v, st') ->
  value v ->
  exists l st_mid,
    multi_step (e, st) (ELoc l, st_mid) /\
    st' = st_mid /\ store_lookup l st_mid = Some v.
Proof.
  intros e st v st' Hwf Hms Hval.
  remember (EDeref e, st) as c1. remember (v, st') as c2.
  revert e st v st' Heqc1 Heqc2 Hval Hwf.
  induction Hms as [cfg | cfg1 cfg2 cfg3 Hstep Hms IH]; 
    intros e0 st0 v0 st0' Heqc1 Heqc2 Hval Hwf.
  - subst. injection Heqc2 as H1 H2. subst.
    exfalso. apply (EDeref_not_value e0). exact Hval.
  - subst cfg1 cfg3.
    destruct cfg2 as [e2 st2].
    inversion Hstep; subst.
    + (* ST_DerefLoc: e2 is looked up value, st2 is store, l is location *)
      (* H0 : store_lookup l st2 = Some e2 *)
      assert (Hve2 : value e2) by (eapply store_wf_lookup; eauto).
      apply multi_step_value_inv in Hms; auto.
      destruct Hms as [Heq1 Heq2]. subst e2 st0'.
      exists l, st2. repeat split; auto. apply MS_Refl.
    + (* ST_DerefStep *)
      assert (Hwf2 : store_well_formed st2) by (eapply step_preserves_wf; eauto).
      specialize (IH e' st2 v0 st0' eq_refl eq_refl Hval Hwf2).
      destruct IH as [l0 [sm [Hm [Hs Hl]]]].
      exists l0, sm. repeat split; auto.
      eapply MS_Step; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   LEMMA 3: multi_step_assign_inversion
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma multi_step_assign_inversion : forall e1 e2 st v st',
  store_well_formed st ->
  multi_step (EAssign e1 e2, st) (v, st') ->
  value v ->
  exists l v_val st_mid1 st_mid2,
    multi_step (e1, st) (ELoc l, st_mid1) /\
    multi_step (e2, st_mid1) (v_val, st_mid2) /\
    value v_val /\ v = EUnit /\
    st' = store_update l v_val st_mid2.
Proof.
  intros e1 e2 st v st' Hwf Hms Hval.
  remember (EAssign e1 e2, st) as c1. remember (v, st') as c2.
  revert e1 e2 st v st' Heqc1 Heqc2 Hval Hwf.
  induction Hms as [cfg | cfg1 cfg2 cfg3 Hstep Hms IH];
    intros e1_0 e2_0 st0 v0 st0' Heqc1 Heqc2 Hval Hwf.
  - subst. injection Heqc2 as H1 H2. subst.
    exfalso. apply (EAssign_not_value e1_0 e2_0). exact Hval.
  - subst cfg1 cfg3. destruct cfg2 as [e_mid st_mid].
    inversion Hstep; subst.
    + (* ST_AssignLoc: e2_0 is already a value, e_mid = EUnit, st_mid = store_update l e2_0 st0 *)
      apply multi_step_value_inv in Hms; [ | constructor].
      destruct Hms as [Heq1 Heq2]. subst v0 st0'.
      exists l, e2_0, st0, st0. repeat split; auto; apply MS_Refl.
    + (* ST_Assign1 *)
      assert (Hwf2 : store_well_formed st_mid) by (eapply step_preserves_wf; eauto).
      specialize (IH e1' e2_0 st_mid v0 st0' eq_refl eq_refl Hval Hwf2).
      destruct IH as [l [vv [sm1 [sm2 [Hm1 [Hm2 [Hvv [He Hs]]]]]]]].
      exists l, vv, sm1, sm2. repeat split; auto.
      eapply MS_Step; eauto.
    + (* ST_Assign2: e1_0 is a value, e2_0 steps to e2', st0 -> st_mid *)
      (* H1 : value e1_0, H5 : step (e2_0, st0) (e2', st_mid) *)
      (* Hms : multi_step (EAssign e1_0 e2', st_mid) (v0, st0') *)
      assert (Hwf2 : store_well_formed st_mid) by (eapply step_preserves_wf; eauto).
      specialize (IH e1_0 e2' st_mid v0 st0' eq_refl eq_refl Hval Hwf2).
      destruct IH as [l [vv [sm1 [sm2 [Hm1 [Hm2 [Hvv [He Hs]]]]]]]].
      (* Hm1 : multi_step (e1_0, st_mid) (ELoc l, sm1) *)
      (* Hm2 : multi_step (e2', sm1) (vv, sm2) *)
      apply multi_step_value_inv in Hm1; auto.
      destruct Hm1 as [Heq_e1 Heq_sm1]. subst sm1.
      (* Heq_e1 : e1_0 = ELoc l, now Hm2 : multi_step (e2', st_mid) (vv, sm2) *)
      exists l, vv, st0, sm2. repeat split; auto.
      * (* multi_step (e1_0, st0) (ELoc l, st0) *) 
        rewrite <- Heq_e1. apply MS_Refl.
      * (* multi_step (e2_0, st0) (vv, sm2) *)
        eapply MS_Step; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 4: LOGICAL RELATION DEFINITIONS
   ═══════════════════════════════════════════════════════════════════════════ *)

Inductive ty : Type := TUnit : ty | TBool : ty | TRef : ty -> ty.

Definition store_ty := list (nat * ty).

Fixpoint store_ty_lookup (l : nat) (Σ : store_ty) : option ty :=
  match Σ with
  | nil => None
  | (l', T) :: rest => if Nat.eqb l l' then Some T else store_ty_lookup l rest
  end.

Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T, store_ty_lookup l Σ = Some T -> store_ty_lookup l Σ' = Some T.

Definition store_rel_simple (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.

Fixpoint val_rel (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TRef T' => exists l, v1 = ELoc l /\ v2 = ELoc l
  end.

Definition exp_rel (T : ty) (e1 e2 : expr) (st1 st2 : store) : Prop :=
  store_well_formed st1 ->
  store_well_formed st2 ->
  forall v1 v2 st1' st2',
    multi_step (e1, st1) (v1, st1') ->
    multi_step (e2, st2) (v2, st2') ->
    value v1 -> value v2 ->
    val_rel T v1 v2 /\ store_rel_simple st1' st2'.

(* ═══════════════════════════════════════════════════════════════════════════
   SECTION 5: STORE MAX LEMMAS
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma store_max_aux_ge : forall st acc, store_max_aux st acc >= acc.
Proof.
  induction st as [| [l v] rest IH]; intros acc; simpl.
  - apply Nat.le_refl.
  - specialize (IH (Nat.max (S l) acc)).
    apply Nat.le_trans with (Nat.max (S l) acc).
    + apply Nat.le_max_r.
    + exact IH.
Qed.

Lemma store_max_aux_split : forall st acc,
  store_max_aux st acc = Nat.max (store_max_aux st 0) acc.
Proof.
  induction st as [| [l v] rest IH]; intros acc; simpl.
  - symmetry. apply Nat.max_0_l.
  - destruct acc as [|m].
    + rewrite (IH (S l)). rewrite Nat.max_0_r. reflexivity.
    + rewrite (IH (S (Nat.max l m))). rewrite (IH (S l)).
      rewrite <- Nat.max_assoc. simpl. reflexivity.
Qed.

Lemma store_max_update : forall l v st,
  l = fresh_loc st -> store_max (store_update l v st) = S (store_max st).
Proof.
  intros l v st Heq. subst l.
  unfold store_update, store_max, fresh_loc. simpl.
  rewrite store_max_aux_split.
  rewrite Nat.max_comm.
  apply Nat.max_l.
  apply Nat.le_succ_diag_r.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   LEMMA 4: exp_rel_ref
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma exp_rel_ref : forall T e1 e2 st1 st2 sl,
  exp_rel T e1 e2 st1 st2 ->
  store_rel_simple st1 st2 ->
  exp_rel (TRef T) (ERef e1 sl) (ERef e2 sl) st1 st2.
Proof.
  intros T e1 e2 st1 st2 sl Hexp Hsr.
  unfold exp_rel in *.
  intros Hwf1 Hwf2 v1 v2 st1' st2' Hm1 Hm2 Hv1 Hv2.
  apply multi_step_ref_inversion in Hm1 as [vi1 [sm1 [l1 [Hm1' [Hvi1 [Hl1 [Hs1 Hf1]]]]]]]; auto.
  apply multi_step_ref_inversion in Hm2 as [vi2 [sm2 [l2 [Hm2' [Hvi2 [Hl2 [Hs2 Hf2]]]]]]]; auto.
  subst v1 v2 st1' st2' l1 l2.
  specialize (Hexp Hwf1 Hwf2 vi1 vi2 sm1 sm2 Hm1' Hm2' Hvi1 Hvi2).
  destruct Hexp as [Hvr Hsr'].
  unfold store_rel_simple in Hsr'.
  assert (Hleq : fresh_loc sm1 = fresh_loc sm2).
  { unfold fresh_loc. rewrite Hsr'. reflexivity. }
  split.
  - simpl. exists (fresh_loc sm1). rewrite Hleq. auto.
  - unfold store_rel_simple.
    rewrite store_max_update by reflexivity.
    rewrite store_max_update by reflexivity.
    rewrite Hsr'. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   LEMMA 5: exp_rel_deref
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma exp_rel_deref : forall T e1 e2 st1 st2,
  exp_rel (TRef T) e1 e2 st1 st2 ->
  store_rel_simple st1 st2 ->
  (* Additional hypothesis: lookup at the same location gives related values *)
  (forall l st1' st2' v1 v2,
    multi_step (e1, st1) (ELoc l, st1') ->
    multi_step (e2, st2) (ELoc l, st2') ->
    store_lookup l st1' = Some v1 ->
    store_lookup l st2' = Some v2 ->
    val_rel T v1 v2) ->
  exp_rel T (EDeref e1) (EDeref e2) st1 st2.
Proof.
  intros T e1 e2 st1 st2 Hexp Hsr Hlook.
  unfold exp_rel in *.
  intros Hwf1 Hwf2 v1 v2 st1' st2' Hm1 Hm2 Hv1 Hv2.
  apply multi_step_deref_inversion in Hm1 as [l1 [sm1 [Hm1' [Hs1 Hl1]]]]; auto.
  apply multi_step_deref_inversion in Hm2 as [l2 [sm2 [Hm2' [Hs2 Hl2]]]]; auto.
  subst st1' st2'.
  assert (Hlv1 : value (ELoc l1)) by constructor.
  assert (Hlv2 : value (ELoc l2)) by constructor.
  specialize (Hexp Hwf1 Hwf2 (ELoc l1) (ELoc l2) sm1 sm2 Hm1' Hm2' Hlv1 Hlv2).
  destruct Hexp as [Hvr Hsr'].
  simpl in Hvr. destruct Hvr as [l [Hl1' Hl2']].
  injection Hl1' as Hl1'. injection Hl2' as Hl2'. subst l1 l2.
  split.
  - apply (Hlook l sm1 sm2 v1 v2 Hm1' Hm2' Hl1 Hl2).
  - exact Hsr'.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   LEMMA 6: exp_rel_assign
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma exp_rel_assign : forall T e1 e2 e1' e2' st1 st2,
  exp_rel (TRef T) e1 e2 st1 st2 ->
  (* exp_rel for value after location evaluation *)
  (forall st1' st2',
    store_well_formed st1' -> store_well_formed st2' ->
    store_rel_simple st1' st2' ->
    exp_rel T e1' e2' st1' st2') ->
  store_rel_simple st1 st2 ->
  exp_rel TUnit (EAssign e1 e1') (EAssign e2 e2') st1 st2.
Proof.
  intros T e1 e2 e1' e2' st1 st2 Hexp_ref Hexp_val_gen Hsr.
  unfold exp_rel in *.
  intros Hwf1 Hwf2 v1 v2 st1' st2' Hm1 Hm2 Hv1 Hv2.
  apply multi_step_assign_inversion in Hm1 as 
    [l1 [vv1 [sm1_1 [sm1_2 [Hm1_1 [Hm1_2 [Hvv1 [He1 Hs1]]]]]]]]; auto.
  apply multi_step_assign_inversion in Hm2 as 
    [l2 [vv2 [sm2_1 [sm2_2 [Hm2_1 [Hm2_2 [Hvv2 [He2 Hs2]]]]]]]]; auto.
  subst v1 v2 st1' st2'.
  assert (Hlv1 : value (ELoc l1)) by constructor.
  assert (Hlv2 : value (ELoc l2)) by constructor.
  specialize (Hexp_ref Hwf1 Hwf2 (ELoc l1) (ELoc l2) sm1_1 sm2_1 Hm1_1 Hm2_1 Hlv1 Hlv2).
  destruct Hexp_ref as [Hvr_ref Hsr_ref].
  simpl in Hvr_ref. destruct Hvr_ref as [l [Hl1 Hl2]].
  injection Hl1 as Hl1. injection Hl2 as Hl2. subst l1 l2.
  (* Get that sm1_2 and sm2_2 have same store_max *)
  assert (Hwf1_1 : store_well_formed sm1_1).
  { eapply multi_step_preserves_wf. exact Hwf1. exact Hm1_1. }
  assert (Hwf2_1 : store_well_formed sm2_1).
  { eapply multi_step_preserves_wf. exact Hwf2. exact Hm2_1. }
  (* Apply the value expression relation *)
  specialize (Hexp_val_gen sm1_1 sm2_1 Hwf1_1 Hwf2_1 Hsr_ref).
  unfold exp_rel in Hexp_val_gen.
  specialize (Hexp_val_gen Hwf1_1 Hwf2_1 vv1 vv2 sm1_2 sm2_2 Hm1_2 Hm2_2 Hvv1 Hvv2).
  destruct Hexp_val_gen as [Hvr_val Hsr_val].
  split.
  - simpl. auto.
  - unfold store_rel_simple in *.
    unfold store_update. unfold store_max in *. simpl.
    rewrite (store_max_aux_split sm1_2 (S l)).
    rewrite (store_max_aux_split sm2_2 (S l)).
    rewrite Hsr_val. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   VERIFICATION: Print assumptions to confirm ZERO axioms
   ═══════════════════════════════════════════════════════════════════════════ *)

Print Assumptions multi_step_ref_inversion.
Print Assumptions multi_step_deref_inversion.
Print Assumptions multi_step_assign_inversion.
Print Assumptions exp_rel_ref.
Print Assumptions exp_rel_deref.
Print Assumptions exp_rel_assign.
