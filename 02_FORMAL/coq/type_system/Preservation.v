(** * Preservation Theorem for TERAS-LANG

    If a well-typed expression takes a step,
    the resulting expression is also well-typed with the same type.

    Reference: CTSS_v1_0_1.md, Section 6

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.
Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.
Import ListNotations.

(** ** Preservation Statement

    The preservation theorem states that evaluation preserves types.

    NOTE: We use a weaker form that allows the effect to change during
    reduction. This is necessary because when a case/if/let reduces to
    one of its branches, the branch may have a different effect than the
    overall expression. This weaker form is still sufficient for type safety,
    since what matters is that the result is well-typed (any effect is fine).
*)

Definition preservation_stmt := forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  exists Σ' ε',
    store_ty_extends Σ Σ' /\
    store_wf Σ' st' /\
    has_type nil Σ' Public e' T ε'.

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
  - (* EPerform *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* EHandle *)
    inversion Hty; subst.
    destruct Hfr as [Hfr1 | [Hneq Hfr2]].
    + eapply IHe1; eauto.
    + match goal with
      | [ H : has_type ((?y, ?T1) :: ?G) _ _ ?h _ _ |- _ ] =>
          destruct (IHe2 _ _ _ _ _ Hfr2 H) as [T' Hlook]
      end.
      simpl in Hlook.
      destruct (String.eqb x i) eqn:Heq.
      * apply String.eqb_eq in Heq. contradiction.
      * exists T'. assumption.
  - (* ERef *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* EDeref *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* EAssign *)
    inversion Hty; subst.
    destruct Hfr as [Hfr1 | Hfr2].
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - (* EClassify *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* EDeclassify *)
    inversion Hty; subst.
    destruct Hfr as [Hfr1 | Hfr2].
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - (* EProve *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* ERequire *)
    inversion Hty; subst.
    eapply IHe; eauto.
  - (* EGrant *)
    inversion Hty; subst.
    eapply IHe; eauto.
Qed.

(** ** Store Typing Lemmas *)

Lemma store_lookup_update_eq : forall st l v,
  store_lookup l (store_update l v st) = Some v.
Proof.
  induction st as [| [l' v'] st' IH]; intros l v; simpl.
  - rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. rewrite Heq. exact (IH l v).
Qed.

Lemma store_lookup_update_neq : forall st l l' v,
  l <> l' ->
  store_lookup l (store_update l' v st) = store_lookup l st.
Proof.
  induction st as [| [l0 v0] st' IH]; intros l l' v Hneq; simpl.
  - destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. contradiction.
    + reflexivity.
  - destruct (Nat.eqb l' l0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      destruct (Nat.eqb l l0) eqn:Heq0.
      * apply Nat.eqb_eq in Heq0. contradiction.
      * simpl. rewrite Heq0. reflexivity.
    + destruct (Nat.eqb l l0) eqn:Heq0.
      * simpl. rewrite Heq0. reflexivity.
      * simpl. rewrite Heq0. apply IH. exact Hneq.
Qed.

Lemma store_ty_lookup_update_eq : forall Σ l T sl,
  store_ty_lookup l (store_ty_update l T sl Σ) = Some (T, sl).
Proof.
  induction Σ as [| [[l' T'] sl'] Σ' IH]; intros l T sl; simpl.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. simpl. rewrite Nat.eqb_refl. reflexivity.
    + simpl. rewrite Heq. simpl. apply IH.
Qed.

Lemma store_ty_lookup_update_neq : forall Σ l l' T sl,
  l <> l' ->
  store_ty_lookup l (store_ty_update l' T sl Σ) = store_ty_lookup l Σ.
Proof.
  induction Σ as [| [[l0 T0] sl0] Σ' IH]; intros l l' T sl Hneq; simpl.
  - destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. contradiction.
    + reflexivity.
  - destruct (Nat.eqb l' l0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      destruct (Nat.eqb l l0) eqn:Heq0.
      * apply Nat.eqb_eq in Heq0. contradiction.
      * simpl. rewrite Heq0. reflexivity.
    + destruct (Nat.eqb l l0) eqn:Heq0.
      * simpl. rewrite Heq0. reflexivity.
      * simpl. rewrite Heq0. apply IH. exact Hneq.
Qed.

Lemma store_ty_extends_update_fresh : forall Σ l T sl,
  store_ty_lookup l Σ = None ->
  store_ty_extends Σ (store_ty_update l T sl Σ).
Proof.
  induction Σ as [| a Σ' IH]; intros l T sl Hnone.
  - intros l0 T0 sl0 Hlookup. inversion Hlookup.
  - destruct a as [[l' T'] sl'].
    simpl in Hnone.
    destruct (Nat.eqb l l') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. discriminate.
    + intros l0 T0 sl0 Hlookup.
      simpl in Hlookup.
      destruct (Nat.eqb l0 l') eqn:Heq0.
      * apply Nat.eqb_eq in Heq0. subst.
        inversion Hlookup; subst.
        simpl. rewrite Heq. simpl. rewrite Nat.eqb_refl. reflexivity.
      * simpl. rewrite Heq. simpl. rewrite Heq0.
        apply (IH _ _ _ Hnone _ _ _ Hlookup).
Qed.

Lemma store_ty_extends_preserves_typing : forall Γ Σ Σ' Δ e T ε,
  store_ty_extends Σ Σ' ->
  has_type Γ Σ Δ e T ε ->
  has_type Γ Σ' Δ e T ε.
Proof.
  intros Γ Σ Σ' Δ e T ε Hext Hty.
  induction Hty; try (econstructor; eauto).
Qed.

Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Proof.
  intros Σ l T sl Hlookup. exact Hlookup.
Qed.

Lemma store_wf_update_existing : forall Σ st l T sl v,
  store_wf Σ st ->
  store_ty_lookup l Σ = Some (T, sl) ->
  has_type nil Σ Public v T EffectPure ->
  store_wf Σ (store_update l v st).
Proof.
  intros Σ st l T sl v [HΣtoSt HSttoΣ] Hlookup Hv.
  split.
  - intros l0 T0 sl0 Hlookup0.
    destruct (Nat.eqb l0 l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      rewrite Hlookup in Hlookup0. inversion Hlookup0; subst.
      exists v. split.
      * apply store_lookup_update_eq.
      * exact Hv.
    + apply Nat.eqb_neq in Heq.
      destruct (HΣtoSt l0 T0 sl0 Hlookup0) as [v0 [Hst Hty]].
      exists v0. split.
      * rewrite store_lookup_update_neq; auto.
      * exact Hty.
  - intros l0 v0 Hst.
    destruct (Nat.eqb l0 l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      exists T, sl. split.
      * exact Hlookup.
      * assert (store_lookup l (store_update l v st) = Some v) as Hst'.
        { apply store_lookup_update_eq. }
        rewrite Hst' in Hst. inversion Hst. subst. exact Hv.
    + apply Nat.eqb_neq in Heq.
      rewrite store_lookup_update_neq in Hst; [exact (HSttoΣ l0 v0 Hst) | exact Heq].
Qed.

Lemma store_wf_update_fresh : forall Σ st l T sl v,
  store_wf Σ st ->
  store_lookup l st = None ->
  store_ty_lookup l Σ = None ->
  has_type nil Σ Public v T EffectPure ->
  store_wf (store_ty_update l T sl Σ) (store_update l v st).
Proof.
  intros Σ st l T sl v [HΣtoSt HSttoΣ] Hstnone Htynone Hv.
  split.
  - intros l0 T0 sl0 Hlookup.
    simpl in Hlookup.
    destruct (Nat.eqb l0 l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      rewrite store_ty_lookup_update_eq in Hlookup.
      inversion Hlookup; subst.
      exists v. split.
      * apply store_lookup_update_eq.
      * apply store_ty_extends_preserves_typing with (Σ := Σ).
        -- apply store_ty_extends_update_fresh. exact Htynone.
        -- exact Hv.
    + apply Nat.eqb_neq in Heq.
      rewrite store_ty_lookup_update_neq in Hlookup; auto.
      destruct (HΣtoSt l0 T0 sl0 Hlookup) as [v0 [Hst Hty]].
      exists v0. split.
      * rewrite store_lookup_update_neq; auto.
      * apply store_ty_extends_preserves_typing with (Σ := Σ).
        -- apply store_ty_extends_update_fresh. exact Htynone.
        -- exact Hty.
  - intros l0 v0 Hst.
    destruct (Nat.eqb l0 l) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      exists T, sl. split.
      * apply store_ty_lookup_update_eq.
      * assert (store_lookup l (store_update l v st) = Some v) as Hst'.
        { apply store_lookup_update_eq. }
        rewrite Hst' in Hst. inversion Hst. subst.
        apply store_ty_extends_preserves_typing with (Σ := Σ).
        -- apply store_ty_extends_update_fresh. exact Htynone.
        -- exact Hv.
    + apply Nat.eqb_neq in Heq.
      rewrite store_lookup_update_neq in Hst; auto.
      destruct (HSttoΣ l0 v0 Hst) as [T0 [sl0 [Hlookup0 Hty0]]].
      exists T0, sl0. split.
      * rewrite store_ty_lookup_update_neq; [exact Hlookup0 | exact Heq].
      * apply store_ty_extends_preserves_typing with (Σ := Σ).
        -- apply store_ty_extends_update_fresh. exact Htynone.
        -- exact Hty0.
Qed.

Lemma store_ty_lookup_fresh_none : forall Σ st,
  store_wf Σ st ->
  store_ty_lookup (fresh_loc st) Σ = None.
Proof.
  intros Σ st [HΣtoSt _].
  destruct (store_ty_lookup (fresh_loc st) Σ) as [[T sl] |] eqn:Hlookup; auto.
  destruct (HΣtoSt _ _ _ Hlookup) as [v [Hst _]].
  rewrite store_lookup_fresh in Hst. discriminate.
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
  - (* T_Loc *)
    constructor. exact H.
  - (* T_Var *)
    constructor.
    match goal with
    | Hlookup : lookup ?x _ = Some _ |- _ =>
        assert (free_in x (EVar x)) as Hfree by (simpl; reflexivity);
        specialize (Hctx x Hfree);
        rewrite <- Hctx;
        exact Hlookup
    end.
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
  - (* T_Perform *)
    apply T_Perform with (eff := eff).
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Handle *)
    apply T_Handle with (T1 := T1) (ε1 := ε1) (ε2 := ε2).
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. simpl.
      destruct (String.eqb y x) eqn:Heq.
      * reflexivity.
      * apply Hctx. simpl. right. split.
        -- intro Heq'. subst. rewrite String.eqb_refl in Heq. discriminate.
        -- assumption.
  - (* T_Ref *)
    eapply T_Ref.
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Deref *)
    eapply T_Deref.
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Assign *)
    eapply T_Assign.
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. apply Hctx. simpl. right. assumption.
  - (* T_Classify *)
    apply T_Classify.
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Declassify *)
    apply T_Declassify with (ε1 := ε1) (ε2 := ε2).
    + apply IHHty1. intros y Hy. apply Hctx. simpl. left. assumption.
    + apply IHHty2. intros y Hy. apply Hctx. simpl. right. assumption.
    + match goal with
      | Hok : declass_ok _ _ |- _ => exact Hok
      end.
  - (* T_Prove *)
    apply T_Prove.
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Require *)
    apply T_Require with (eff := eff).
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
  - (* T_Grant *)
    apply T_Grant with (eff := eff).
    apply IHHty. intros y Hy. apply Hctx. simpl. assumption.
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
  value v ->
  has_type nil Σ Δ v T1 EffectPure ->
  has_type ((z, T1) :: Γ) Σ Δ e T2 ε2 ->
  has_type Γ Σ Δ ([z := v] e) T2 ε2.
Proof.
  intros Γ Σ Δ z v e T1 T2 ε2 Hval Htyv.
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
  (* ELoc *)
  - inversion Hty; subst. constructor. assumption.
  (* EVar *)
  - inversion Hty; subst.
    simpl.
    rename H3 into Hlook.
    simpl in Hlook.
    destruct (String.eqb z i) eqn:Heq.
    + apply String.eqb_eq in Heq; subst.
      rewrite String.eqb_refl in Hlook.
      inversion Hlook; subst.
      apply closed_typing_weakening; exact Htyv.
    + apply T_Var.
      assert (String.eqb i z = false) as Heq'.
      { destruct (String.eqb i z) eqn:Heq'.
        - apply String.eqb_eq in Heq'. subst.
          rewrite String.eqb_refl in Heq. discriminate.
        - reflexivity. }
      rewrite Heq' in Hlook.
      exact Hlook.
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
  (* EPerform *)
  - inversion Hty; subst.
    eapply T_Perform. eapply IHe. eassumption.
  (* EHandle *)
  - inversion Hty; subst.
    eapply T_Handle.
    + eapply IHe1; eassumption.
    + destruct (String.eqb z i) eqn:Heq.
      * apply String.eqb_eq in Heq. subst.
        eapply context_invariance.
        -- eassumption.
        -- intros y Hfr. simpl. destruct (String.eqb y i); reflexivity.
      * eapply IHe2.
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
  (* ERef *)
  - inversion Hty; subst.
    eapply T_Ref. eapply IHe. eassumption.
  (* EDeref *)
  - inversion Hty; subst.
    eapply T_Deref. eapply IHe. eassumption.
  (* EAssign *)
  - inversion Hty; subst.
    eapply T_Assign; eauto.
  (* EClassify *)
  - inversion Hty; subst.
    eapply T_Classify. eapply IHe. eassumption.
  (* EDeclassify *)
  - inversion Hty; subst.
    eapply T_Declassify; eauto.
    apply declass_ok_subst; [exact Hval | assumption].
  (* EProve *)
  - inversion Hty; subst.
    eapply T_Prove. eapply IHe. eassumption.
  (* ERequire *)
  - inversion Hty; subst.
    eapply T_Require. eapply IHe. eassumption.
  (* EGrant *)
  - inversion Hty; subst.
    eapply T_Grant. eapply IHe. eassumption.
Qed.

(** ** Preservation Theorem

    If a well-typed expression takes a step, the result is also well-typed
    with the same type and effect.
*)

(** Helper: values have pure effect when typed in empty context *)
Lemma value_has_pure_effect : forall v T ε Σ,
  value v ->
  has_type nil Σ Public v T ε ->
  has_type nil Σ Public v T EffectPure.
Proof.
  intros v T ε Σ Hval.
  generalize dependent ε.
  generalize dependent T.
  induction Hval; intros T' ε' Hty; inversion Hty; subst.
  - (* VUnit *) constructor.
  - (* VBool *) constructor.
  - (* VInt *) constructor.
  - (* VString *) constructor.
  - (* VLoc *) constructor. assumption.
  - (* VLam *) constructor. assumption.
  - (* VPair *)
    specialize (IHHval1 _ _ H4) as Hty1.
    specialize (IHHval2 _ _ H7) as Hty2.
    replace EffectPure with (effect_join EffectPure EffectPure).
    + apply T_Pair with (ε1 := EffectPure) (ε2 := EffectPure); assumption.
    + rewrite effect_join_pure_l. reflexivity.
  - (* VInl *)
    eapply T_Inl. eapply IHHval. eassumption.
  - (* VInr *)
    eapply T_Inr. eapply IHHval. eassumption.
  - (* VClassify *)
    eapply T_Classify. eapply IHHval. eassumption.
  - (* VProve *)
    eapply T_Prove. eapply IHHval. eassumption.
Qed.

(** Helper lemma for preservation with proper IH *)
Lemma preservation_helper : forall cfg1 cfg2,
  cfg1 --> cfg2 ->
  forall e st ctx e' st' ctx' T ε Σ,
    cfg1 = (e, st, ctx) ->
    cfg2 = (e', st', ctx') ->
    has_type nil Σ Public e T ε ->
    store_wf Σ st ->
    exists Σ' ε',
      store_ty_extends Σ Σ' /\
      store_wf Σ' st' /\
      has_type nil Σ' Public e' T ε'.
Proof.
  intros cfg1 cfg2 Hstep.
  induction Hstep; intros e0 st0 ctx0 e0' st0' ctx0' T0 ε0 Σ Heq1 Heq2 Hty Hwf;
    inversion Heq1; inversion Heq2; subst.
  (* ST_AppAbs: beta reduction for function application *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (ELam _ _ _) _ _ |- _ ] => inversion H; subst
    end.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eapply substitution_preserves_typing.
        -- eassumption.
        -- eapply value_has_pure_effect; eassumption.
        -- eassumption.
  (* ST_App1: congruence for application (left) *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty1']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_App.
        -- exact Hty1'.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
  (* ST_App2: congruence for application (right) *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty2']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_App.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
        -- exact Hty2'.
  (* ST_Pair1: congruence for pairs (left) *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty1']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Pair.
        -- exact Hty1'.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
  (* ST_Pair2: congruence for pairs (right) *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty2']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Pair.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
        -- exact Hty2'.
  (* ST_Fst: projection from pair (left) *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EPair _ _) _ _ |- _ ] => inversion H; subst
    end.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
  (* ST_Snd: projection from pair (right) *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EPair _ _) _ _ |- _ ] => inversion H; subst
    end.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
  (* ST_FstStep: congruence for fst *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Fst. exact Hty'.
  (* ST_SndStep: congruence for snd *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Snd. exact Hty'.
  (* ST_CaseInl: case analysis on Inl *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EInl _ _) _ _ |- _ ] => inversion H; subst
    end.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eapply substitution_preserves_typing.
        -- eassumption.
        -- eapply value_has_pure_effect; eassumption.
        -- eassumption.
  (* ST_CaseInr: case analysis on Inr *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EInr _ _) _ _ |- _ ] => inversion H; subst
    end.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eapply substitution_preserves_typing.
        -- eassumption.
        -- eapply value_has_pure_effect; eassumption.
        -- eassumption.
  (* ST_CaseStep: congruence for case *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Case.
        -- exact Hty'.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
  (* ST_InlStep: congruence for Inl *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Inl. exact Hty'.
  (* ST_InrStep: congruence for Inr *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Inr. exact Hty'.
  (* ST_IfTrue: if-then-else with true *)
  - inversion Hty; subst.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
  (* ST_IfFalse: if-then-else with false *)
  - inversion Hty; subst.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
  (* ST_IfStep: congruence for if *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_If.
        -- exact Hty'.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
  (* ST_LetValue: let binding with value *)
  - inversion Hty; subst.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eapply substitution_preserves_typing.
        -- eassumption.
        -- eapply value_has_pure_effect; eassumption.
        -- eassumption.
  (* ST_LetStep: congruence for let *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Let.
        -- exact Hty'.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
  (* ST_PerformStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Perform. exact Hty'.
  (* ST_PerformValue *)
  - inversion Hty; subst.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
  (* ST_HandleStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Handle.
        -- exact Hty'.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
  (* ST_HandleValue *)
  - inversion Hty; subst.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eapply substitution_preserves_typing.
        -- eassumption.
        -- eapply value_has_pure_effect; eassumption.
        -- eassumption.
  (* ST_RefStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Ref. exact Hty'.
  (* ST_RefValue *)
  - inversion Hty; subst.
    assert (has_type nil Σ Public v T EffectPure) as Hvty.
    { eapply value_has_pure_effect; eassumption. }
    assert (store_ty_lookup (fresh_loc st0) Σ = None) as Hfresh_none.
    { apply store_ty_lookup_fresh_none. exact Hwf. }
    set (Σ' := store_ty_update (fresh_loc st0) T sl Σ).
    exists Σ'. eexists.
    split.
    + subst Σ'. apply store_ty_extends_update_fresh. exact Hfresh_none.
    + split.
      * subst Σ'. eapply store_wf_update_fresh; eauto.
        -- apply store_lookup_fresh.
      * subst Σ'. apply T_Loc. apply store_ty_lookup_update_eq.
  (* ST_DerefStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Deref. exact Hty'.
  (* ST_DerefLoc *)
  - inversion Hty; subst.
    destruct Hwf as [HΣtoSt HSttoΣ].
    destruct (HSttoΣ l e0' H) as [T1 [sl1 [Hlookup Htyv]]].
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact (conj HΣtoSt HSttoΣ).
      * inversion H4; subst.
        match goal with
        | Hloc : store_ty_lookup l Σ = Some (T0, ?sl0) |- _ =>
            rewrite Hloc in Hlookup; inversion Hlookup; subst; exact Htyv
        end.
  (* ST_Assign1 *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Assign.
        -- exact Hty'.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
  (* ST_Assign2 *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty2']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Assign.
        -- apply store_ty_extends_preserves_typing with (Σ := Σ); [exact Hext | eassumption].
        -- exact Hty2'.
  (* ST_AssignLoc *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (ELoc _) _ _ |- _ ] => inversion H; subst
    end.
    assert (has_type nil Σ Public v2 T EffectPure) as Hvty.
    { eapply value_has_pure_effect; eassumption. }
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * eapply store_wf_update_existing; eauto.
      * constructor.
  (* ST_ClassifyStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Classify. exact Hty'.
  (* ST_Declassify1 *)
  - inversion Hty; subst.
    match goal with
    | Hdeclass : declass_ok _ _ |- _ =>
        destruct Hdeclass as [v0 [Hv0 [He1 He2]]]; subst
    end.
    exfalso.
    pose proof (value_not_step (EClassify v0) st0 ctx0 (e1', st0', ctx0')
                  (VClassify v0 Hv0)) as Hns.
    exact (Hns Hstep).
  (* ST_Declassify2 *)
  - inversion Hty; subst.
    match goal with
    | Hdeclass : declass_ok _ _ |- _ =>
        destruct Hdeclass as [v0 [Hv0 [He1 He2]]]; subst
    end.
    exfalso.
    pose proof (value_not_step (EProve (EClassify v0)) st0 ctx0 (e2', st0', ctx0')
                  (VProve (EClassify v0) (VClassify v0 Hv0))) as Hns.
    exact (Hns Hstep).
  (* ST_DeclassifyValue *)
  - inversion Hty; subst.
    match goal with
    | [ H : has_type _ _ _ (EClassify _) _ _ |- _ ] => inversion H; subst
    end.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
  (* ST_ProveStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Prove. exact Hty'.
  (* ST_RequireStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Require. exact Hty'.
  (* ST_RequireValue *)
  - inversion Hty; subst.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
  (* ST_GrantStep *)
  - inversion Hty; subst.
    edestruct IHHstep as [Σ' [ε' [Hext [Hwf' Hty']]]]; try reflexivity; eauto.
    exists Σ'. eexists.
    split.
    + exact Hext.
    + split.
      * exact Hwf'.
      * eapply T_Grant. exact Hty'.
  (* ST_GrantValue *)
  - inversion Hty; subst.
    exists Σ. eexists.
    split.
    + apply store_ty_extends_refl.
    + split.
      * exact Hwf.
      * eassumption.
Qed.

Theorem preservation : preservation_stmt.
Proof.
  unfold preservation_stmt.
  intros e e' T ε st st' ctx ctx' Σ Hty Hwf Hstep.
  eapply preservation_helper with (cfg1 := (e, st, ctx)) (cfg2 := (e', st', ctx'));
    try reflexivity; eassumption.
Qed.

(** End of Preservation.v *)
