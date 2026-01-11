(** * Preservation Theorem for TERAS-LANG

    If a well-typed expression takes a step,
    the resulting expression is also well-typed with the same type.

    Reference: CTSS_v1_0_1.md, Section 6

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.
Import ListNotations.

(** ** Preservation Statement *)

Definition preservation_stmt := forall e e' T ε st st' ctx ctx',
  has_type nil nil Public e T ε ->
  (e, st, ctx) --> (e', st', ctx') ->
  has_type nil nil Public e' T ε.

(** ** Auxiliary Lemma 1: Free Variables in Context

    If x is free in e and e is well-typed in Γ, then x is in Γ.
*)

Lemma free_in_context : forall x e Γ Σ Δ T ε,
  free_in x e ->
  has_type Γ Σ Δ e T ε ->
  exists T', lookup x Γ = Some T'.
Proof.
  intros x e.
  induction e; intros Γ Σ Δ T ε Hfr Hty; simpl in Hfr.
  (* Handle cases where free_in is False (values with no free vars) *)
  all: try contradiction.
  (* Handle cases where there's no typing rule (EPerform, EHandle, etc.) *)
  all: try (inversion Hty; fail).
  - (* EVar *)
    subst. inversion Hty; subst.
    exists T. assumption.
  - (* ELam *)
    destruct Hfr as [Hneq Hfr'].
    inversion Hty; subst.
    match goal with
    | [ H : has_type ((?y, ?ty) :: ?G) ?S ?D ?body ?T2 ?eff |- _ ] =>
        destruct (IHe _ _ _ _ _ Hfr' H) as [T' Hlook]
    end.
    simpl in Hlook.
    destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. contradiction.
    + exists T'. assumption.
  - (* EApp *)
    inversion Hty; subst.
    destruct Hfr as [Hfr1 | Hfr2].
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - (* EPair *)
    inversion Hty; subst.
    destruct Hfr as [Hfr1 | Hfr2].
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - (* EFst *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* ESnd *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* EInl *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* EInr *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* ECase *)
    inversion Hty; subst.
    destruct Hfr as [Hfr0 | [[Hneq1 Hfr1] | [Hneq2 Hfr2]]].
    + eapply IHe1; eauto.
    + match goal with
      | [ H1 : has_type ((?y1, ?T1) :: ?G) _ _ e2 _ _,
          H2 : has_type ((?y2, ?T2) :: ?G) _ _ e3 _ _ |- _ ] =>
          destruct (IHe2 _ _ _ _ _ Hfr1 H1) as [T' Hlook]
      end.
      simpl in Hlook.
      destruct (String.eqb x i) eqn:Heq.
      * apply String.eqb_eq in Heq. contradiction.
      * exists T'. assumption.
    + match goal with
      | [ H1 : has_type ((?y1, ?T1) :: ?G) _ _ e2 _ _,
          H2 : has_type ((?y2, ?T2) :: ?G) _ _ e3 _ _ |- _ ] =>
          destruct (IHe3 _ _ _ _ _ Hfr2 H2) as [T' Hlook]
      end.
      simpl in Hlook.
      destruct (String.eqb x i0) eqn:Heq.
      * apply String.eqb_eq in Heq. contradiction.
      * exists T'. assumption.
  - (* EIf *)
    inversion Hty; subst.
    destruct Hfr as [Hfr1 | [Hfr2 | Hfr3]].
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
    + eapply IHe3; eauto.
  - (* ELet *)
    inversion Hty; subst.
    destruct Hfr as [Hfr1 | [Hneq Hfr2]].
    + eapply IHe1; eauto.
    + match goal with
      | [ H : has_type ((?y, ?T1) :: ?G) _ _ e2 _ _ |- _ ] =>
          destruct (IHe2 _ _ _ _ _ Hfr2 H) as [T' Hlook]
      end.
      simpl in Hlook.
      destruct (String.eqb x i) eqn:Heq.
      * apply String.eqb_eq in Heq. contradiction.
      * exists T'. assumption.
Qed.

(** ** Auxiliary Lemma 2: Context Invariance

    Typing only depends on free variables. If all free variables of e
    have the same binding in Γ1 and Γ2, then e types the same in both.
*)

Lemma context_invariance : forall Γ1 Γ2 Σ Δ e T ε,
  has_type Γ1 Σ Δ e T ε ->
  (forall x, free_in x e -> lookup x Γ1 = lookup x Γ2) ->
  has_type Γ2 Σ Δ e T ε.
Proof.
  intros Γ1 Γ2 Σ Δ e T ε Hty Hctx.
  generalize dependent Γ2.
  induction Hty; intros Γ2 Hctx.
  - (* T_Unit *) constructor.
  - (* T_Bool *) constructor.
  - (* T_Int *) constructor.
  - (* T_String *) constructor.
  - (* T_Var *)
    constructor.
    rewrite <- Hctx.
    + assumption.
    + simpl. reflexivity.
  - (* T_Lam *)
    constructor.
    apply IHHty.
    intros y Hfree.
    simpl.
    destruct (String.eqb y x) eqn:Heq.
    + reflexivity.
    + apply Hctx. simpl. split.
      * intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
      * assumption.
  - (* T_App *)
    apply T_App with (T1 := T1) (ε1 := ε1) (ε2 := ε2).
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. apply Hctx. simpl. right. assumption.
  - (* T_Pair *)
    apply T_Pair with (ε1 := ε1) (ε2 := ε2).
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. apply Hctx. simpl. right. assumption.
  - (* T_Fst *)
    apply T_Fst with (T2 := T2).
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Snd *)
    apply T_Snd with (T1 := T1).
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Inl *)
    apply T_Inl.
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Inr *)
    apply T_Inr.
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Case *)
    apply T_Case with (T1 := T1) (T2 := T2) (ε := ε) (ε1 := ε1) (ε2 := ε2).
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. simpl.
      destruct (String.eqb y x1) eqn:Heq.
      * reflexivity.
      * apply Hctx. simpl. right. left. split.
        -- intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
        -- assumption.
    + apply IHHty3. intros y Hy. simpl.
      destruct (String.eqb y x2) eqn:Heq.
      * reflexivity.
      * apply Hctx. simpl. right. right. split.
        -- intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
        -- assumption.
  - (* T_If *)
    apply T_If with (ε1 := ε1) (ε2 := ε2) (ε3 := ε3).
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. apply Hctx. simpl. right. left. assumption.
    + apply IHHty3. intros y Hy. apply Hctx. simpl. right. right. assumption.
  - (* T_Let *)
    apply T_Let with (T1 := T1) (ε1 := ε1) (ε2 := ε2).
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. simpl.
      destruct (String.eqb y x) eqn:Heq.
      * reflexivity.
      * apply Hctx. simpl. right. split.
        -- intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
        -- assumption.
Qed.

(** ** Auxiliary Lemma 3: Closed Terms Weaken

    A closed term (typed in empty context) can be typed in any context.
*)

Lemma closed_typing_weakening : forall Σ Δ v T ε Γ,
  has_type nil Σ Δ v T ε ->
  has_type Γ Σ Δ v T ε.
Proof.
  intros Σ Δ v T ε Γ Hty.
  apply context_invariance with (Γ1 := nil).
  - assumption.
  - intros x Hfree.
    destruct (free_in_context _ _ _ _ _ _ _ Hfree Hty) as [T' Hlook].
    simpl in Hlook. discriminate.
Qed.

(** ** Substitution Lemma

    Key lemma: substitution preserves typing.

    If v has type T1 in empty context, and e has type T2 in context
    extended with x:T1, then [x := v] e has type T2 in the original context.
*)

Lemma substitution_preserves_typing : forall Γ Σ Δ z v e T1 T2 ε2,
  has_type nil Σ Δ v T1 EffectPure ->
  has_type ((z, T1) :: Γ) Σ Δ e T2 ε2 ->
  has_type Γ Σ Δ ([z := v] e) T2 ε2.
Proof.
  intros Γ Σ Δ z v e T1 T2 ε2 Hv Hty.
  generalize dependent Γ.
  generalize dependent ε2.
  generalize dependent T2.
  generalize dependent z.
  induction e; intros z T2 ε2 Γ Hty; simpl.
  (* EUnit *)
  - inversion Hty; subst. constructor.
  (* EBool *)
  - inversion Hty; subst. constructor.
  (* EInt *)
  - inversion Hty; subst. constructor.
  (* EString *)
  - inversion Hty; subst. constructor.
  (* EVar *)
  - inversion Hty as [ | | | | ? ? ? ? ? Hlook | | | | | | | | | | ]; subst.
    (* Hlook : lookup i ((z, T1) :: Γ) = Some T2 *)
    simpl.
    simpl in Hlook.
    (* Goal has: if String.eqb x i then v else EVar i
       Hlook has: if String.eqb i x then Some T1 else lookup i Γ *)
    destruct (String.eqb z i) eqn:Heq.
    + (* x = i: substitute v *)
      apply String.eqb_eq in Heq. subst.
      (* Now i = x, so String.eqb i i = true *)
      rewrite String.eqb_refl in Hlook.
      inversion Hlook; subst.
      (* Goal: has_type Γ Σ Δ v T1 EffectPure *)
      apply closed_typing_weakening. assumption.
    + (* z ≠ i: keep variable *)
      constructor.
      (* Need to show: String.eqb i z = false from String.eqb z i = false *)
      assert (String.eqb i z = false) as Heq'.
      { destruct (String.eqb i z) eqn:E; auto.
        apply String.eqb_eq in E. subst.
        rewrite String.eqb_refl in Heq. discriminate. }
      rewrite Heq' in Hlook. assumption.
  (* ELam *)
  - inversion Hty; subst.
    destruct (String.eqb z i) eqn:Heq.
    + (* z = i: variable shadowed, no substitution in body *)
      apply String.eqb_eq in Heq. subst.
      constructor.
      apply context_invariance with (Γ1 := (i, t) :: (i, T1) :: Γ).
      * assumption.
      * intros y Hfree. simpl.
        destruct (String.eqb y i); reflexivity.
    + (* z ≠ i: substitute in body *)
      constructor.
      apply IHe.
      apply context_invariance with (Γ1 := (i, t) :: (z, T1) :: Γ).
      * assumption.
      * intros y Hfree. simpl.
        destruct (String.eqb y i) eqn:Heq2.
        -- (* y = i: need to show Some t = if y =? z then Some T1 else Some t *)
           (* Since y = i and z ≠ i, we have y ≠ z *)
           apply String.eqb_eq in Heq2. subst.
           (* Now need: Some t = if i =? z then Some T1 else Some t *)
           (* We have Heq : z ≠ i, so i ≠ z *)
           assert ((i =? z)%string = false) as Hix.
           { destruct (String.eqb i z) eqn:E; auto.
             apply String.eqb_eq in E. subst.
             rewrite String.eqb_refl in Heq. discriminate. }
           rewrite Hix. reflexivity.
        -- destruct (String.eqb y z) eqn:Heq3; reflexivity.
  (* EApp *)
  - inversion Hty; subst.
    eapply T_App; eauto.
  (* EPair *)
  - inversion Hty; subst.
    eapply T_Pair; eauto.
  (* EFst *)
  - inversion Hty; subst.
    eapply T_Fst; eauto.
  (* ESnd *)
  - inversion Hty; subst.
    eapply T_Snd; eauto.
  (* EInl *)
  - inversion Hty; subst.
    eapply T_Inl; eauto.
  (* EInr *)
  - inversion Hty; subst.
    eapply T_Inr; eauto.
  (* ECase *)
  - inversion Hty; subst.
    eapply T_Case.
    + eapply IHe1; eauto.
    + (* Branch 1: binder i may shadow z *)
      destruct (String.eqb z i) eqn:Heq.
      * (* z = i: no substitution in e2 *)
        apply String.eqb_eq in Heq. subst.
        (* H10 : has_type ((i, T0) :: (i, T1) :: Γ) Σ Δ e2 T2 ε1 *)
        (* Goal: has_type ((i, T0) :: Γ) Σ Δ e2 T2 ?ε1 *)
        eapply context_invariance.
        -- eassumption.
        -- intros y Hfr. simpl.
           destruct (String.eqb y i); reflexivity.
      * (* z ≠ i: substitution happens *)
        apply IHe2.
        (* H10 : has_type ((i, T0) :: (z, T1) :: Γ) Σ Δ e2 T2 ε1 *)
        (* Need: has_type ((z, T1) :: (i, T0) :: Γ) Σ Δ e2 T2 ε1 *)
        eapply context_invariance.
        -- eassumption.
        -- intros y Hfr. simpl.
           destruct (String.eqb y i) eqn:Heq2.
           ++ (* y = i: lookup y gives T0 in both contexts *)
              apply String.eqb_eq in Heq2. subst.
              assert ((i =? z)%string = false) as Hne.
              { destruct (String.eqb i z) eqn:E; auto.
                apply String.eqb_eq in E. subst.
                rewrite String.eqb_refl in Heq. discriminate. }
              rewrite Hne. reflexivity.
           ++ destruct (String.eqb y z) eqn:Heq3; reflexivity.
    + (* Branch 2: binder i0 may shadow z *)
      destruct (String.eqb z i0) eqn:Heq.
      * apply String.eqb_eq in Heq. subst.
        eapply context_invariance.
        -- eassumption.
        -- intros y Hfr. simpl.
           destruct (String.eqb y i0); reflexivity.
      * apply IHe3.
        eapply context_invariance.
        -- eassumption.
        -- intros y Hfr. simpl.
           destruct (String.eqb y i0) eqn:Heq2.
           ++ apply String.eqb_eq in Heq2. subst.
              assert ((i0 =? z)%string = false) as Hne.
              { destruct (String.eqb i0 z) eqn:E; auto.
                apply String.eqb_eq in E. subst.
                rewrite String.eqb_refl in Heq. discriminate. }
              rewrite Hne. reflexivity.
           ++ destruct (String.eqb y z) eqn:Heq3; reflexivity.
  (* EIf *)
  - inversion Hty; subst.
    eapply T_If; eauto.
  (* ELet *)
  - inversion Hty; subst.
    eapply T_Let.
    + eapply IHe1; eauto.
    + (* Binder i may shadow z *)
      destruct (String.eqb z i) eqn:Heq.
      * (* z = i: no substitution in e2 *)
        apply String.eqb_eq in Heq. subst.
        eapply context_invariance.
        -- eassumption.
        -- intros y Hfr. simpl.
           destruct (String.eqb y i); reflexivity.
      * (* z ≠ i: substitution happens *)
        apply IHe2.
        eapply context_invariance.
        -- eassumption.
        -- intros y Hfr. simpl.
           destruct (String.eqb y i) eqn:Heq2.
           ++ apply String.eqb_eq in Heq2. subst.
              assert ((i =? z)%string = false) as Hne.
              { destruct (String.eqb i z) eqn:E; auto.
                apply String.eqb_eq in E. subst.
                rewrite String.eqb_refl in Heq. discriminate. }
              rewrite Hne. reflexivity.
           ++ destruct (String.eqb y z) eqn:Heq3; reflexivity.
  (* Remaining expression forms without typing rules - these cases are impossible
     since the expression cannot be well-typed. These expressions have no typing rules
     in the current subset of the language. *)
  - (* EPerform *) inversion Hty.
  - (* EHandle *) inversion Hty.
  - (* ERef *) inversion Hty.
  - (* EDeref *) inversion Hty.
  - (* EAssign *) inversion Hty.
  - (* EClassify *) inversion Hty.
  - (* EDeclassify *) inversion Hty.
  - (* EProve *) inversion Hty.
  - (* ERequire *) inversion Hty.
  - (* EGrant *) inversion Hty.
Qed.

(** ** Preservation Theorem

    If a well-typed expression takes a step, the result is also well-typed
    with the same type and effect.
*)

(** Helper: values have pure effect when typed in empty context *)
Lemma value_has_pure_effect : forall v T ε,
  value v ->
  has_type nil nil Public v T ε ->
  has_type nil nil Public v T EffectPure.
Proof.
  intros v T ε Hval.
  generalize dependent ε.
  generalize dependent T.
  induction Hval; intros T' ε' Hty; inversion Hty; subst.
  - (* VUnit *) constructor.
  - (* VBool *) constructor.
  - (* VInt *) constructor.
  - (* VString *) constructor.
  - (* VLam *) constructor. assumption.
  - (* VPair *)
    eapply T_Pair; eassumption.
  - (* VInl *)
    eapply T_Inl. eapply IHHval. eassumption.
  - (* VInr *)
    eapply T_Inr. eapply IHHval. eassumption.
Qed.

(** Helper lemma for preservation with proper IH *)
Lemma preservation_helper : forall cfg1 cfg2,
  cfg1 --> cfg2 ->
  forall e st ctx e' st' ctx' T ε,
    cfg1 = (e, st, ctx) ->
    cfg2 = (e', st', ctx') ->
    has_type nil nil Public e T ε ->
    has_type nil nil Public e' T ε.
Proof.
  intros cfg1 cfg2 Hstep.
  induction Hstep; intros e0 st0 ctx0 e0' st0' ctx0' T0 ε0 Heq1 Heq2 Hty;
    inversion Heq1; inversion Heq2; subst.
  (* ST_AppAbs: beta reduction for function application *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (ELam _ _ _) _ _ |- _ ] => inversion H; subst
    end.
    eapply substitution_preserves_typing.
    + eapply value_has_pure_effect; eassumption.
    + eassumption.
  (* ST_App1: congruence for application (left) *)
  - inversion Hty; subst.
    eapply T_App.
    + eapply IHHstep; try reflexivity. eassumption.
    + eassumption.
  (* ST_App2: congruence for application (right) *)
  - inversion Hty; subst.
    eapply T_App.
    + eassumption.
    + eapply IHHstep; try reflexivity. eassumption.
  (* ST_Pair1: congruence for pairs (left) *)
  - inversion Hty; subst.
    eapply T_Pair.
    + eapply IHHstep; try reflexivity. eassumption.
    + eassumption.
  (* ST_Pair2: congruence for pairs (right) *)
  - inversion Hty; subst.
    eapply T_Pair.
    + eassumption.
    + eapply IHHstep; try reflexivity. eassumption.
  (* ST_Fst: projection from pair (left) *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EPair _ _) _ _ |- _ ] => inversion H; subst
    end.
    (* Result is a value, so use value_has_pure_effect *)
    eapply value_has_pure_effect; eassumption.
  (* ST_Snd: projection from pair (right) *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EPair _ _) _ _ |- _ ] => inversion H; subst
    end.
    (* Result is a value, so use value_has_pure_effect *)
    eapply value_has_pure_effect; eassumption.
  (* ST_FstStep: congruence for fst *)
  - inversion Hty; subst.
    eapply T_Fst.
    eapply IHHstep; try reflexivity. eassumption.
  (* ST_SndStep: congruence for snd *)
  - inversion Hty; subst.
    eapply T_Snd.
    eapply IHHstep; try reflexivity. eassumption.
  (* ST_CaseInl: case analysis on Inl *)
  (* Note: T_Case gives result effect = scrutinee effect, but branch may have different effect.
     This requires effect subtyping or refined T_Case rule for full preservation. *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EInl _ _) _ _ |- _ ] => inversion H; subst
    end.
    eapply substitution_preserves_typing.
    + eapply value_has_pure_effect; eassumption.
    + (* TODO: Effect mismatch - need effect subtyping or refined T_Case *)
      admit.
  (* ST_CaseInr: case analysis on Inr *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EInr _ _) _ _ |- _ ] => inversion H; subst
    end.
    eapply substitution_preserves_typing.
    + eapply value_has_pure_effect; eassumption.
    + (* TODO: Effect mismatch - need effect subtyping or refined T_Case *)
      admit.
  (* ST_CaseStep: congruence for case *)
  - inversion Hty; subst.
    eapply T_Case.
    + eapply IHHstep; try reflexivity. eassumption.
    + eassumption.
    + eassumption.
  (* ST_InlStep: congruence for Inl *)
  - inversion Hty; subst.
    eapply T_Inl.
    eapply IHHstep; try reflexivity. eassumption.
  (* ST_InrStep: congruence for Inr *)
  - inversion Hty; subst.
    eapply T_Inr.
    eapply IHHstep; try reflexivity. eassumption.
  (* ST_IfTrue: if-then-else with true *)
  (* Note: T_If gives result effect = condition effect, but branch may have different effect *)
  - inversion Hty; subst.
    (* TODO: Effect mismatch - need effect join or refined T_If *)
    admit.
  (* ST_IfFalse: if-then-else with false *)
  - inversion Hty; subst.
    (* TODO: Effect mismatch - need effect join or refined T_If *)
    admit.
  (* ST_IfStep: congruence for if *)
  - inversion Hty; subst.
    eapply T_If.
    + eapply IHHstep; try reflexivity. eassumption.
    + eassumption.
    + eassumption.
  (* ST_LetValue: let binding with value *)
  (* Note: T_Let gives result effect = binding effect, but body may have different effect *)
  - inversion Hty; subst.
    eapply substitution_preserves_typing.
    + eapply value_has_pure_effect; eassumption.
    + (* TODO: Effect mismatch - need effect join or refined T_Let *)
      admit.
  (* ST_LetStep: congruence for let *)
  - inversion Hty; subst.
    eapply T_Let.
    + eapply IHHstep; try reflexivity. eassumption.
    + eassumption.
Admitted. (* TODO: Fix effect system for full preservation - see effect mismatch notes above *)

Theorem preservation : preservation_stmt.
Proof.
  unfold preservation_stmt.
  intros e e' T ε st st' ctx ctx' Hty Hstep.
  eapply preservation_helper with (cfg1 := (e, st, ctx)) (cfg2 := (e', st', ctx'));
    try reflexivity; eassumption.
Qed.

(** End of Preservation.v *)
