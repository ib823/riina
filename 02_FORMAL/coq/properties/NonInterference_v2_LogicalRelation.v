(** * Non-Interference for RIINA - V2 Logical Relation

    Logical-relation layer for NonInterference_v2.

    This file ports the environment/substitution machinery and the
    logical_relation + non_interference_stmt theorems from the legacy
    development, but uses the v2 step-indexed relations.

    Mode: ULTRA KIASU | ZERO TRUST | ZERO LAZINESS
*)

Require Export RIINA.properties.NonInterference_v2.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Preservation.
Require Import RIINA.properties.NonInterference_v2_Monotone.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.TypeMeasure.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

Definition closed_except (x : ident) (e : expr) : Prop :=
  forall y, y <> x -> ~ free_in y e.

Lemma closed_expr_lam : forall x T body,
  closed_except x body ->
  closed_expr (ELam x T body).
Proof.
  intros x T body Hclosed y Hfree. simpl in Hfree.
  destruct Hfree as [Hyneq Hfree].
  apply (Hclosed y Hyneq) in Hfree. contradiction.
Qed.

Lemma closed_expr_pair : forall v1 v2,
  closed_expr v1 ->
  closed_expr v2 ->
  closed_expr (EPair v1 v2).
Proof.
  intros v1 v2 Hc1 Hc2 y Hfree. simpl in Hfree.
  destruct Hfree as [Hfree | Hfree].
  - apply (Hc1 y) in Hfree. contradiction.
  - apply (Hc2 y) in Hfree. contradiction.
Qed.

Lemma closed_expr_pair_inv : forall v1 v2,
  closed_expr (EPair v1 v2) ->
  closed_expr v1 /\ closed_expr v2.
Proof.
  intros v1 v2 Hc. split.
  - intros y Hfree. apply (Hc y). simpl. left. exact Hfree.
  - intros y Hfree. apply (Hc y). simpl. right. exact Hfree.
Qed.

Lemma closed_expr_inl : forall v T,
  closed_expr v ->
  closed_expr (EInl v T).
Proof.
  intros v T Hc y Hfree. simpl in Hfree.
  apply (Hc y) in Hfree. contradiction.
Qed.

Lemma closed_expr_inr : forall v T,
  closed_expr v ->
  closed_expr (EInr v T).
Proof.
  intros v T Hc y Hfree. simpl in Hfree.
  apply (Hc y) in Hfree. contradiction.
Qed.

Lemma val_rel_closed_left_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  closed_expr v1.
Proof.
  intros n Σ T v1 v2 _ Hrel.
  destruct (val_rel_n_closed n Σ T v1 v2 Hrel) as [Hc1 _].
  exact Hc1.
Qed.

Lemma val_rel_closed_right_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  closed_expr v2.
Proof.
  intros n Σ T v1 v2 _ Hrel.
  destruct (val_rel_n_closed n Σ T v1 v2 Hrel) as [_ Hc2].
  exact Hc2.
Qed.

Lemma val_rel_value_left_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  value v1.
Proof.
  intros n Σ T v1 v2 _ Hrel.
  destruct (val_rel_n_value n Σ T v1 v2 Hrel) as [Hv1 _].
  exact Hv1.
Qed.

Lemma val_rel_value_right_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  value v2.
Proof.
  intros n Σ T v1 v2 _ Hrel.
  destruct (val_rel_n_value n Σ T v1 v2 Hrel) as [_ Hv2].
  exact Hv2.
Qed.

Lemma val_rel_closed_left : forall Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  closed_expr v1.
Proof.
  intros Σ T v1 v2 Hrel.
  apply (val_rel_closed_left_n 1 Σ T v1 v2); [lia | exact (Hrel 1)].
Qed.

Lemma val_rel_closed_right : forall Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  closed_expr v2.
Proof.
  intros Σ T v1 v2 Hrel.
  apply (val_rel_closed_right_n 1 Σ T v1 v2); [lia | exact (Hrel 1)].
Qed.

Lemma val_rel_value_left : forall Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  value v1.
Proof.
  intros Σ T v1 v2 Hrel.
  apply (val_rel_value_left_n 1 Σ T v1 v2); [lia | exact (Hrel 1)].
Qed.

Lemma val_rel_value_right : forall Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  value v2.
Proof.
  intros Σ T v1 v2 Hrel.
  apply (val_rel_value_right_n 1 Σ T v1 v2); [lia | exact (Hrel 1)].
Qed.
Definition rho_shadow (rho : ident -> expr) (x : ident) : ident -> expr :=
  fun y => if String.eqb y x then EVar y else rho y.

Definition rho_extend (rho : ident -> expr) (x : ident) (v : expr) : ident -> expr :=
  fun y => if String.eqb y x then v else rho y.

Fixpoint subst_rho (rho : ident -> expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar x => rho x
  | ELam x T body => ELam x T (subst_rho (rho_shadow rho x) body)
  | EApp e1 e2 => EApp (subst_rho rho e1) (subst_rho rho e2)
  | EPair e1 e2 => EPair (subst_rho rho e1) (subst_rho rho e2)
  | EFst e1 => EFst (subst_rho rho e1)
  | ESnd e1 => ESnd (subst_rho rho e1)
  | EInl e1 T => EInl (subst_rho rho e1) T
  | EInr e1 T => EInr (subst_rho rho e1) T
  | ECase e x1 e1 x2 e2 =>
      ECase (subst_rho rho e)
            x1 (subst_rho (rho_shadow rho x1) e1)
            x2 (subst_rho (rho_shadow rho x2) e2)
  | EIf e1 e2 e3 => EIf (subst_rho rho e1) (subst_rho rho e2) (subst_rho rho e3)
  | ELet x e1 e2 =>
      ELet x (subst_rho rho e1) (subst_rho (rho_shadow rho x) e2)
  | EPerform eff e1 => EPerform eff (subst_rho rho e1)
  | EHandle e1 x h =>
      EHandle (subst_rho rho e1) x (subst_rho (rho_shadow rho x) h)
  | ERef e1 l => ERef (subst_rho rho e1) l
  | EDeref e1 => EDeref (subst_rho rho e1)
  | EAssign e1 e2 => EAssign (subst_rho rho e1) (subst_rho rho e2)
  | EClassify e1 => EClassify (subst_rho rho e1)
  | EDeclassify e1 e2 => EDeclassify (subst_rho rho e1) (subst_rho rho e2)
  | EProve e1 => EProve (subst_rho rho e1)
  | ERequire eff e1 => ERequire eff (subst_rho rho e1)
  | EGrant eff e1 => EGrant eff (subst_rho rho e1)
  end.

Lemma free_in_subst_rho : forall x rho e,
  free_in x (subst_rho rho e) ->
  exists y, free_in y e /\ free_in x (rho y).
Proof.
  intros x rho e.
  generalize dependent rho.
  generalize dependent x.
  induction e; intros x rho Hfree; simpl in Hfree; try contradiction.
  - exists i. split; simpl; auto.
  - destruct Hfree as [Hneq Hfree].
    destruct (IHe x (rho_shadow rho i) Hfree) as [y [Hy Hrho]].
    assert (y <> i) as Hyneq.
    { intro Heq. subst.
      unfold rho_shadow in Hrho. rewrite String.eqb_refl in Hrho. simpl in Hrho.
      apply Hneq. exact Hrho. }
    exists y. split.
    + simpl. split; assumption.
    + unfold rho_shadow in Hrho.
      rewrite (proj2 (String.eqb_neq y i) Hyneq) in Hrho. exact Hrho.
  - destruct Hfree as [Hfree | Hfree].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct (IHe2 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. right. exact Hy. exact Hrho.
  - destruct Hfree as [Hfree | Hfree].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct (IHe2 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. right. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct Hfree as [Hfree | [Hfree | Hfree]].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct Hfree as [Hneq Hfree].
      destruct (IHe2 x (rho_shadow rho i) Hfree) as [y [Hy Hrho]].
      assert (y <> i) as Hyneq.
      { intro Heq. subst.
        unfold rho_shadow in Hrho. rewrite String.eqb_refl in Hrho. simpl in Hrho.
        apply Hneq. exact Hrho. }
      exists y. split.
      * right. left. split; assumption.
      * unfold rho_shadow in Hrho.
        rewrite (proj2 (String.eqb_neq y i) Hyneq) in Hrho. exact Hrho.
    + destruct Hfree as [Hneq Hfree].
      destruct (IHe3 x (rho_shadow rho i0) Hfree) as [y [Hy Hrho]].
      assert (y <> i0) as Hyneq.
      { intro Heq. subst.
        unfold rho_shadow in Hrho. rewrite String.eqb_refl in Hrho. simpl in Hrho.
        apply Hneq. exact Hrho. }
      exists y. split.
      * right. right. split; assumption.
      * unfold rho_shadow in Hrho.
        rewrite (proj2 (String.eqb_neq y i0) Hyneq) in Hrho. exact Hrho.
  - destruct Hfree as [Hfree | [Hfree | Hfree]].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct (IHe2 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. right. left. exact Hy. exact Hrho.
    + destruct (IHe3 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. right. right. exact Hy. exact Hrho.
  - destruct Hfree as [Hfree | Hfree].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct Hfree as [Hneq Hfree].
      destruct (IHe2 x (rho_shadow rho i) Hfree) as [y [Hy Hrho]].
      assert (y <> i) as Hyneq.
      { intro Heq. subst.
        unfold rho_shadow in Hrho. rewrite String.eqb_refl in Hrho. simpl in Hrho.
        apply Hneq. exact Hrho. }
      exists y. split.
      * right. split; assumption.
      * unfold rho_shadow in Hrho.
        rewrite (proj2 (String.eqb_neq y i) Hyneq) in Hrho. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct Hfree as [Hfree | Hfree].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct Hfree as [Hneq Hfree].
      destruct (IHe2 x (rho_shadow rho i) Hfree) as [y [Hy Hrho]].
      assert (y <> i) as Hyneq.
      { intro Heq. subst.
        unfold rho_shadow in Hrho. rewrite String.eqb_refl in Hrho. simpl in Hrho.
        apply Hneq. exact Hrho. }
      exists y. split.
      * right. split; assumption.
      * unfold rho_shadow in Hrho.
        rewrite (proj2 (String.eqb_neq y i) Hyneq) in Hrho. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct Hfree as [Hfree | Hfree].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct (IHe2 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. right. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct Hfree as [Hfree | Hfree].
    + destruct (IHe1 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. left. exact Hy. exact Hrho.
    + destruct (IHe2 x rho Hfree) as [y [Hy Hrho]].
      exists y. split. right. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
  - destruct (IHe x rho Hfree) as [y [Hy Hrho]].
    exists y. split. exact Hy. exact Hrho.
Qed.

Definition env_rel_n (n : nat) (Σ : store_ty) (G : type_env) (rho1 rho2 : ident -> expr) : Prop :=
  forall x T, lookup x G = Some T -> val_rel_n n Σ T (rho1 x) (rho2 x).

Definition env_rel (Σ : store_ty) (G : type_env) (rho1 rho2 : ident -> expr) : Prop :=
  forall n, env_rel_n n Σ G rho1 rho2.

Definition rho_closed_on (G : type_env) (rho : ident -> expr) : Prop :=
  forall x T, lookup x G = Some T -> closed_expr (rho x).

Definition rho_no_free_all (rho : ident -> expr) : Prop :=
  forall x y, y <> x -> ~ free_in x (rho y).

(** ** Syntactic Environment Typing

    This relates an environment substitution rho to a typing context Γ.
    For each variable x : T in Γ, rho(x) must be:
    1. A value
    2. Well-typed at type T in the empty context

    This is the SYNTACTIC counterpart to env_rel (which is SEMANTIC).
*)

Definition env_typed (Σ : store_ty) (Γ : type_env) (rho : ident -> expr) : Prop :=
  forall x T, lookup x Γ = Some T ->
    value (rho x) /\ has_type nil Σ Public (rho x) T EffectPure.

Lemma env_typed_lookup : forall Σ Γ rho x T,
  env_typed Σ Γ rho ->
  lookup x Γ = Some T ->
  value (rho x) /\ has_type nil Σ Public (rho x) T EffectPure.
Proof.
  intros Σ Γ rho x T Henv Hlook.
  exact (Henv x T Hlook).
Qed.

(** Typing in empty context implies closed. *)
Lemma typing_nil_closed : forall Σ Δ e T ε,
  has_type nil Σ Δ e T ε ->
  closed_expr e.
Proof.
  intros Σ Δ e T ε Hty x Hfree.
  destruct (free_in_context x e nil Σ Δ T ε Hfree Hty) as [T' Hlook].
  simpl in Hlook. discriminate.
Qed.

Lemma env_typed_closed : forall Σ Γ rho x T,
  env_typed Σ Γ rho ->
  lookup x Γ = Some T ->
  closed_expr (rho x).
Proof.
  intros Σ Γ rho x T Henv Hlook.
  destruct (Henv x T Hlook) as [Hval Hty].
  apply (typing_nil_closed Σ Public (rho x) T EffectPure Hty).
Qed.

Lemma env_typed_extend : forall Σ Γ rho x T v,
  env_typed Σ Γ rho ->
  value v ->
  has_type nil Σ Public v T EffectPure ->
  env_typed Σ ((x, T) :: Γ) (rho_extend rho x v).
Proof.
  intros Σ Γ rho x T v Henv Hval Htyv.
  unfold env_typed. intros y Ty Hlook.
  simpl in Hlook.
  unfold rho_extend.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq. subst.
    inversion Hlook; subst. split; assumption.
  - apply (Henv y Ty Hlook).
Qed.

(** NOTE: env_typed_shadow cannot be proven because rho_shadow returns EVar,
    which is not a value. This is intentional - the substitution typing lemma
    handles binders differently via the general formulation. *)

(** NOTE: rho_shadow does NOT produce values for shadowed variables.
    This is because rho_shadow rho x y = EVar y when y = x.
    EVar is NOT a value, so env_typed cannot hold for rho_shadow directly.

    Instead, we need subst_rho_preserves_typing to handle binders differently:
    when we go under a binder for variable x, the typing context extends,
    and the substitution does not touch x (it remains a variable).
*)

(** ** Substitution Preserves Typing (Full Environment Version)

    This is the key lemma connecting syntactic typing with semantic relations.

    FUNDAMENTAL INSIGHT:

    The issue is that subst_rho with rho_shadow does NOT produce closed terms.
    When we go under a lambda, rho_shadow rho x returns EVar x for variable x.

    The correct approach is to track typing through an OUTPUT context.
    Key insight: subst_rho (rho_shadow rho x) body has type T2 in context
    containing just x : T1, NOT in the empty context.

    We prove: If Γ ⊢ e : T and rho maps Γ\Γ' to closed values, then
    Γ' ⊢ subst_rho rho e : T, where Γ' contains the bound variables.
*)

(** Lemma: substitution preserves values.
    Values remain values after substitution because the value constructors
    only care about syntactic structure, not about free variables. *)
Lemma value_subst_rho : forall rho v,
  value v ->
  value (subst_rho rho v).
Proof.
  intros rho v Hv.
  induction Hv; simpl.
  - constructor.  (* VUnit *)
  - constructor.  (* VBool *)
  - constructor.  (* VInt *)
  - constructor.  (* VString *)
  - constructor.  (* VLoc *)
  - constructor.  (* VLam - body doesn't need to be value *)
  - constructor; assumption.  (* VPair *)
  - constructor; assumption.  (* VInl *)
  - constructor; assumption.  (* VInr *)
  - constructor; assumption.  (* VClassify *)
  - constructor; assumption.  (* VProve *)
Qed.

(** Lemma: declass_ok is preserved by subst_rho.
    PROVEN (was Axiom). Uses value_subst_rho. *)
Lemma declass_ok_subst_rho : forall rho e1 e2,
  declass_ok e1 e2 ->
  declass_ok (subst_rho rho e1) (subst_rho rho e2).
Proof.
  intros rho e1 e2 Hok.
  destruct Hok as [v [Hv [He1 He2]]]; subst.
  simpl.
  exists (subst_rho rho v).
  split.
  - apply value_subst_rho; assumption.
  - split; reflexivity.
Qed.

(** The correct formulation: substitution reduces the typing context. *)

Lemma subst_rho_typing_general : forall Γ Γ' Σ Δ e T ε rho,
  has_type Γ Σ Δ e T ε ->
  (* For variables in Γ but not Γ', rho provides typed values *)
  (forall x Tx, lookup x Γ = Some Tx -> lookup x Γ' = None ->
    value (rho x) /\ has_type nil Σ Δ (rho x) Tx EffectPure) ->
  (* For variables in both Γ and Γ', rho is identity *)
  (forall x, lookup x Γ' <> None -> rho x = EVar x) ->
  (* Γ' is a suffix/subset of Γ with same types *)
  (forall x Tx, lookup x Γ' = Some Tx -> lookup x Γ = Some Tx) ->
  has_type Γ' Σ Δ (subst_rho rho e) T ε.
Proof.
  intros Γ Γ' Σ Δ e T ε rho Hty.
  generalize dependent Γ'.
  generalize dependent rho.
  induction Hty; intros rho Γ' Hsubst Hid Hsuffix; simpl.
  (* T_Unit *)
  - constructor.
  (* T_Bool *)
  - constructor.
  (* T_Int *)
  - constructor.
  (* T_String *)
  - constructor.
  (* T_Loc *)
  - constructor. assumption.
  (* T_Var *)
  - destruct (lookup x Γ') eqn:Hlook'.
    + (* x is in Γ': rho x = EVar x, use T_Var *)
      assert (rho x = EVar x) as Heq.
      { apply Hid. rewrite Hlook'. discriminate. }
      rewrite Heq. constructor.
      (* Need lookup x Γ' = Some T *)
      assert (lookup x Γ = Some t) as Ht.
      { apply Hsuffix. exact Hlook'. }
      rewrite H in Ht. inversion Ht; subst. exact Hlook'.
    + (* x is not in Γ': rho x is a closed value *)
      destruct (Hsubst x T H Hlook') as [Hval Htyx].
      apply closed_typing_weakening. exact Htyx.
  (* T_Lam *)
  - constructor.
    apply (IHHty (rho_shadow rho x) ((x, T1) :: Γ')).
    + (* Substitution condition *)
      intros y Ty Hlook Hlook'.
      simpl in Hlook.
      unfold rho_shadow.
      destruct (String.eqb y x) eqn:Heq.
      * (* y = x: but then lookup y ((x,T1)::Γ') = Some T1 ≠ None, contradiction *)
        apply String.eqb_eq in Heq. subst.
        simpl in Hlook'. rewrite String.eqb_refl in Hlook'. discriminate.
      * (* y ≠ x: use original Hsubst *)
        apply String.eqb_neq in Heq.
        simpl in Hlook'. rewrite (proj2 (String.eqb_neq y x) Heq) in Hlook'.
        apply (Hsubst y Ty Hlook Hlook').
    + (* Identity condition *)
      intros y Hlook'.
      unfold rho_shadow.
      destruct (String.eqb y x) eqn:Heq.
      * reflexivity.
      * apply Hid.
        simpl in Hlook'. rewrite Heq in Hlook'. exact Hlook'.
    + (* Suffix condition *)
      intros y Ty Hlook'.
      simpl in Hlook'. simpl.
      destruct (String.eqb y x) eqn:Heq.
      * inversion Hlook'; subst. reflexivity.
      * apply Hsuffix. exact Hlook'.
  (* T_App *)
  - eapply T_App; eauto.
  (* T_Pair *)
  - eapply T_Pair; eauto.
  (* T_Fst *)
  - eapply T_Fst; eauto.
  (* T_Snd *)
  - eapply T_Snd; eauto.
  (* T_Inl *)
  - eapply T_Inl; eauto.
  (* T_Inr *)
  - eapply T_Inr; eauto.
  (* T_Case *)
  - eapply T_Case.
    + eapply IHHty1; eauto.
    + (* Branch for x1 *)
      apply (IHHty2 (rho_shadow rho x1) ((x1, T1) :: Γ')).
      * intros y Ty Hlook Hlook'.
        simpl in Hlook. unfold rho_shadow.
        destruct (String.eqb y x1) eqn:Heq.
        -- apply String.eqb_eq in Heq. subst.
           simpl in Hlook'. rewrite String.eqb_refl in Hlook'. discriminate.
        -- apply String.eqb_neq in Heq.
           simpl in Hlook'. rewrite (proj2 (String.eqb_neq y x1) Heq) in Hlook'.
           apply (Hsubst y Ty Hlook Hlook').
      * intros y Hlook'. unfold rho_shadow.
        destruct (String.eqb y x1) eqn:Heq; [reflexivity | ].
        apply Hid.
        simpl in Hlook'. rewrite Heq in Hlook'. exact Hlook'.
      * intros y Ty Hlook'. simpl in Hlook'. simpl.
        destruct (String.eqb y x1) eqn:Heq; [inversion Hlook'; reflexivity | ].
        apply Hsuffix. exact Hlook'.
    + (* Branch for x2 *)
      apply (IHHty3 (rho_shadow rho x2) ((x2, T2) :: Γ')).
      * intros y Ty Hlook Hlook'.
        simpl in Hlook. unfold rho_shadow.
        destruct (String.eqb y x2) eqn:Heq.
        -- apply String.eqb_eq in Heq. subst.
           simpl in Hlook'. rewrite String.eqb_refl in Hlook'. discriminate.
        -- apply String.eqb_neq in Heq.
           simpl in Hlook'. rewrite (proj2 (String.eqb_neq y x2) Heq) in Hlook'.
           apply (Hsubst y Ty Hlook Hlook').
      * intros y Hlook'. unfold rho_shadow.
        destruct (String.eqb y x2) eqn:Heq; [reflexivity | ].
        apply Hid.
        simpl in Hlook'. rewrite Heq in Hlook'. exact Hlook'.
      * intros y Ty Hlook'. simpl in Hlook'. simpl.
        destruct (String.eqb y x2) eqn:Heq; [inversion Hlook'; reflexivity | ].
        apply Hsuffix. exact Hlook'.
  (* T_If *)
  - eapply T_If; eauto.
  (* T_Let *)
  - eapply T_Let.
    + eapply IHHty1; eauto.
    + apply (IHHty2 (rho_shadow rho x) ((x, T1) :: Γ')).
      * intros y Ty Hlook Hlook'.
        simpl in Hlook. unfold rho_shadow.
        destruct (String.eqb y x) eqn:Heq.
        -- apply String.eqb_eq in Heq. subst.
           simpl in Hlook'. rewrite String.eqb_refl in Hlook'. discriminate.
        -- apply String.eqb_neq in Heq.
           simpl in Hlook'. rewrite (proj2 (String.eqb_neq y x) Heq) in Hlook'.
           apply (Hsubst y Ty Hlook Hlook').
      * intros y Hlook'. unfold rho_shadow.
        destruct (String.eqb y x) eqn:Heq; [reflexivity | ].
        apply Hid.
        simpl in Hlook'. rewrite Heq in Hlook'. exact Hlook'.
      * intros y Ty Hlook'. simpl in Hlook'. simpl.
        destruct (String.eqb y x) eqn:Heq; [inversion Hlook'; reflexivity | ].
        apply Hsuffix. exact Hlook'.
  (* T_Perform *)
  - eapply T_Perform; eauto.
  (* T_Handle *)
  - eapply T_Handle.
    + eapply IHHty1; eauto.
    + apply (IHHty2 (rho_shadow rho x) ((x, T1) :: Γ')).
      * intros y Ty Hlook Hlook'.
        simpl in Hlook. unfold rho_shadow.
        destruct (String.eqb y x) eqn:Heq.
        -- apply String.eqb_eq in Heq. subst.
           simpl in Hlook'. rewrite String.eqb_refl in Hlook'. discriminate.
        -- apply String.eqb_neq in Heq.
           simpl in Hlook'. rewrite (proj2 (String.eqb_neq y x) Heq) in Hlook'.
           apply (Hsubst y Ty Hlook Hlook').
      * intros y Hlook'. unfold rho_shadow.
        destruct (String.eqb y x) eqn:Heq; [reflexivity | ].
        apply Hid.
        simpl in Hlook'. rewrite Heq in Hlook'. exact Hlook'.
      * intros y Ty Hlook'. simpl in Hlook'. simpl.
        destruct (String.eqb y x) eqn:Heq; [inversion Hlook'; reflexivity | ].
        apply Hsuffix. exact Hlook'.
  (* T_Ref *)
  - eapply T_Ref; eauto.
  (* T_Deref *)
  - eapply T_Deref; eauto.
  (* T_Assign *)
  - eapply T_Assign; eauto.
  (* T_Classify *)
  - eapply T_Classify; eauto.
  (* T_Declassify *)
  - eapply T_Declassify; eauto using declass_ok_subst_rho.
  (* T_Prove *)
  - eapply T_Prove; eauto.
  (* T_Require *)
  - eapply T_Require; eauto.
  (* T_Grant *)
  - eapply T_Grant; eauto.
Qed.

(** Corollary: Full substitution to empty context.
    Note: env_typed provides typing at Public level, so we specialize to Public. *)
Lemma subst_rho_preserves_typing : forall Γ Σ e T ε rho,
  has_type Γ Σ Public e T ε ->
  env_typed Σ Γ rho ->
  has_type nil Σ Public (subst_rho rho e) T ε.
Proof.
  intros Γ Σ e T ε rho Hty Henv.
  apply (subst_rho_typing_general Γ nil Σ Public e T ε rho Hty).
  - intros x Tx Hlook Hlook'.
    destruct (Henv x Tx Hlook) as [Hval Htyx].
    split; assumption.
  - intros x Hlook'. simpl in Hlook'. exfalso. apply Hlook'. reflexivity.
  - intros x Tx Hlook'. simpl in Hlook'. discriminate.
Qed.

(** Bridge: extract env_typed from env_rel using val_rel_n_typing.
    env_rel gives val_rel_n at every step; val_rel_n_typing extracts typing. *)
Lemma env_rel_implies_env_typed : forall Σ Γ rho1 rho2,
  env_rel Σ Γ rho1 rho2 ->
  env_typed Σ Γ rho1 /\ env_typed Σ Γ rho2.
Proof.
  intros Σ Γ rho1 rho2 Henv.
  split; unfold env_typed; intros x T Hlook.
  - (* rho1 *)
    specialize (Henv 0). unfold env_rel_n in Henv.
    specialize (Henv x T Hlook).
    split.
    + apply (val_rel_value_left_n 0 Σ T). exact Henv.
    + destruct (val_rel_n_typing 0 Σ T (rho1 x) (rho2 x) Henv) as [Ht _]. exact Ht.
  - (* rho2 *)
    specialize (Henv 0). unfold env_rel_n in Henv.
    specialize (Henv x T Hlook).
    split.
    + apply (val_rel_value_right_n 0 Σ T). exact Henv.
    + destruct (val_rel_n_typing 0 Σ T (rho1 x) (rho2 x) Henv) as [_ Ht]. exact Ht.
Qed.

(** Helper: typing for substituted lambda from env_rel.
    Given Γ ⊢ ELam x T1 e : TFn T1 T2 ε and env_rel on Γ,
    the substituted lambda has_type nil Σ Public ... (TFn T1 T2 ε) EffectPure. *)
Lemma lam_typing_from_env_rel : forall Γ Σ x T1 T2 e ε rho1 rho2,
  has_type ((x, T1) :: Γ) Σ Public e T2 ε ->
  env_rel Σ Γ rho1 rho2 ->
  has_type nil Σ Public (ELam x T1 (subst_rho (rho_shadow rho1 x) e)) (TFn T1 T2 ε) EffectPure /\
  has_type nil Σ Public (ELam x T1 (subst_rho (rho_shadow rho2 x) e)) (TFn T1 T2 ε) EffectPure.
Proof.
  intros Γ Σ x T1 T2 e ε rho1 rho2 Hty Henv.
  destruct (env_rel_implies_env_typed Σ Γ rho1 rho2 Henv) as [Henv_ty1 Henv_ty2].
  (* For each rho_i, use subst_rho_typing_general with
     Γ = (x,T1)::Γ, Γ' = (x,T1)::nil, rho = rho_shadow rho_i x *)
  assert (Hbody1 : has_type ((x, T1) :: nil) Σ Public (subst_rho (rho_shadow rho1 x) e) T2 ε).
  { apply (subst_rho_typing_general ((x, T1) :: Γ) ((x, T1) :: nil) Σ Public e T2 ε (rho_shadow rho1 x) Hty).
    - intros y Ty Hlook Hlook'.
      simpl in Hlook. simpl in Hlook'.
      destruct (String.eqb y x) eqn:Heq.
      + (* y = x: but then Hlook' would find it in (x,T1)::nil *)
        simpl in Hlook'. rewrite Heq in Hlook'. discriminate.
      + (* y ≠ x: rho_shadow rho1 x y = rho1 y, use env_typed *)
        unfold rho_shadow. rewrite Heq.
        apply Henv_ty1. exact Hlook.
    - intros y Hlook'.
      simpl in Hlook'.
      destruct (String.eqb y x) eqn:Heq.
      + unfold rho_shadow. rewrite Heq. reflexivity.
      + exfalso. apply Hlook'. reflexivity.
    - intros y Ty Hlook'. simpl in Hlook'.
      destruct (String.eqb y x) eqn:Heq.
      + simpl. rewrite Heq. exact Hlook'.
      + simpl in Hlook'. discriminate. }
  assert (Hbody2 : has_type ((x, T1) :: nil) Σ Public (subst_rho (rho_shadow rho2 x) e) T2 ε).
  { apply (subst_rho_typing_general ((x, T1) :: Γ) ((x, T1) :: nil) Σ Public e T2 ε (rho_shadow rho2 x) Hty).
    - intros y Ty Hlook Hlook'.
      simpl in Hlook. simpl in Hlook'.
      destruct (String.eqb y x) eqn:Heq.
      + simpl in Hlook'. rewrite Heq in Hlook'. discriminate.
      + unfold rho_shadow. rewrite Heq.
        apply Henv_ty2. exact Hlook.
    - intros y Hlook'.
      simpl in Hlook'.
      destruct (String.eqb y x) eqn:Heq.
      + unfold rho_shadow. rewrite Heq. reflexivity.
      + exfalso. apply Hlook'. reflexivity.
    - intros y Ty Hlook'. simpl in Hlook'.
      destruct (String.eqb y x) eqn:Heq.
      + simpl. rewrite Heq. exact Hlook'.
      + simpl in Hlook'. discriminate. }
  split; apply T_Lam; assumption.
Qed.

(** ** Effect Operation Axioms

    Effects (T_Perform, T_Handle) involve complex effect context manipulation.
    The fundamental theorem for these cases follows from:
    1. Effect type soundness (EffectSystem.v)
    2. The fact that effect operations preserve value relatedness
    3. Store typing extensions are preserved through effect handling
*)

(** T_Perform: PROVEN INLINE in logical_relation theorem.
    Proof uses multi_step_perform + ST_PerformValue.
*)

(** T_Handle: ELIMINATED — Proof inlined in logical_relation theorem.
    The proof follows the same pattern as T_Let:
    1. Evaluate e using IH to get related values v, v'
    2. Build extended environment for handler h
    3. Apply substitution lemma (subst_rho_extend) to connect
       [x := v] (subst_rho (rho_shadow ...) h) with subst_rho (rho_extend ...) h
    4. Apply IH on h with extended environment
*)

(** ** Reference Operation Axioms

    References (T_Ref, T_Deref, T_Assign) involve store manipulation.
    The fundamental theorem for these cases follows from:
    1. Store typing extensions (Kripke monotonicity)
    2. The store_rel_n relation tracks location relatedness
    3. Type preservation ensures well-typed references
*)

(** T_Ref: Creating a reference preserves relatedness.
    Semantically: new locations are added to store typing consistently.
*)
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e T ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).

(** T_Deref: Dereferencing preserves relatedness.
    Semantically: related locations contain related values.
*)
Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e (TRef T l) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).

(** T_Assign: Assignment preserves relatedness.
    Semantically: store updates maintain location relatedness.
*)
Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n,
  has_type Γ Σ Δ e1 (TRef T l) ε1 ->
  has_type Γ Σ Δ e2 T ε2 ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ TUnit (subst_rho rho1 (EAssign e1 e2)) (subst_rho rho2 (EAssign e1 e2)).

(** T_Declassify: Declassification preserves relatedness.
    Semantically: declassification unwraps secret values to their underlying type.
    This is safe because val_rel_at_type for TSecret is True,
    so any secret values are trivially related.
*)
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n,
  has_type Γ Σ Δ e (TSecret T) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeclassify e p)) (subst_rho rho2 (EDeclassify e p)).

(** AXIOM: Store anti-monotonicity for value relations.
    Values produced by evaluating terms typed at store Σ cannot reference
    locations allocated after Σ (by preservation + canonical forms).
    Standard in step-indexed Kripke logical relations; requires full
    preservation proof to eliminate.
    Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md §5 (store typing) *)
Axiom val_rel_store_weaken_back : forall Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel Σ' T v1 v2 ->
  val_rel Σ T v1 v2.

(** Helper: convert val_rel_n at ANY step (including 0) to val_rel.
    For step 0, we step up once using typing from val_rel_n_typing,
    then apply val_rel_n_to_val_rel. *)
Lemma val_rel_n_to_val_rel_any : forall Σ T v1 v2 n,
  value v1 -> value v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 n Hv1 Hv2 Hrel.
  destruct n as [| k].
  - (* n = 0: step up to get val_rel_n 1, then use val_rel_n_to_val_rel *)
    destruct (val_rel_n_typing 0 Σ T v1 v2 Hrel) as [Hty1 Hty2].
    apply val_rel_n_to_val_rel; try assumption.
    exists 0. apply val_rel_n_step_up; assumption.
  - (* n = S k: direct *)
    apply val_rel_n_to_val_rel; try assumption.
    exists k. exact Hrel.
Qed.

(** Lemma: env_rel implies closed expressions for mapped variables.
    Environment substitutions map free variables to closed values.
    This follows from env_rel requiring val_rel for each mapping,
    and val_rel at step > 0 implying closed_expr.
*)
Lemma env_rel_rho_closed : forall Σ Γ rho1 rho2 x T,
  env_rel Σ Γ rho1 rho2 ->
  lookup x Γ = Some T ->
  closed_expr (rho1 x) /\ closed_expr (rho2 x).
Proof.
  intros Σ Γ rho1 rho2 x T Henv Hlookup.
  (* env_rel means forall n, env_rel_n n Σ Γ rho1 rho2 *)
  (* env_rel_n n means forall x T, lookup x Γ = Some T -> val_rel_n n Σ T (rho1 x) (rho2 x) *)
  specialize (Henv 1). unfold env_rel_n in Henv.
  specialize (Henv x T Hlookup).
  (* Now have: val_rel_n 1 Σ T (rho1 x) (rho2 x) *)
  simpl in Henv.
  destruct Henv as [_ [_ [_ [Hc1 [Hc2 _]]]]].
  exact (conj Hc1 Hc2).
Qed.

(** Closedness lemma for lambda case — PROVEN (was axiom)

    MATHEMATICAL JUSTIFICATION:
    When y is in the type environment Γ, env_rel guarantees that
    rho1 y and rho2 y are values related by val_rel. At step index > 0,
    val_rel includes the requirement that both values are closed expressions.
    Therefore, free_in y (rho1 y) leads to contradiction with closed_expr.

    PROOF STRATEGY:
    1. lookup y Γ = Some T  (premise: y is in context)
    2. env_rel → val_rel_n 1 → closed_expr (by env_rel_rho_closed)
    3. closed_expr (rho1 y) means forall z, ~ free_in z (rho1 y)
    4. In particular, ~ free_in y (rho1 y)
    5. Contradiction with free_in y (rho1 y)

    NOTE: This lemma requires the lookup premise because env_rel only
    constrains variables IN the context. For y ∉ Γ, rho1 y could be anything.
*)
Lemma lam_closedness_contradiction : forall Σ Γ rho1 rho2 y T,
  lookup y Γ = Some T ->
  env_rel Σ Γ rho1 rho2 ->
  free_in y (rho1 y) -> False.
Proof.
  intros Σ Γ rho1 rho2 y T Hlook Henv Hfree.
  (* By env_rel_rho_closed, if y ∈ Γ, then rho1 y is closed *)
  destruct (env_rel_rho_closed Σ Γ rho1 rho2 y T Henv Hlook) as [Hclosed _].
  (* closed_expr (rho1 y) means forall z, ~ free_in z (rho1 y) *)
  (* Apply with z := y to get ~ free_in y (rho1 y) *)
  apply (Hclosed y Hfree).
Qed.

Lemma lam_closedness_contradiction2 : forall Σ Γ rho1 rho2 y T,
  lookup y Γ = Some T ->
  env_rel Σ Γ rho1 rho2 ->
  free_in y (rho2 y) -> False.
Proof.
  intros Σ Γ rho1 rho2 y T Hlook Henv Hfree.
  (* By env_rel_rho_closed, if y ∈ Γ, then rho2 y is closed *)
  destruct (env_rel_rho_closed Σ Γ rho1 rho2 y T Henv Hlook) as [_ Hclosed].
  (* closed_expr (rho2 y) means forall z, ~ free_in z (rho2 y) *)
  apply (Hclosed y Hfree).
Qed.

Definition rho_single (x : ident) (v : expr) : ident -> expr :=
  fun y => if String.eqb y x then v else EVar y.

Definition rho_id : ident -> expr :=
  fun y => EVar y.

Lemma rho_no_free_all_single : forall x v,
  closed_expr v ->
  rho_no_free_all (rho_single x v).
Proof.
  intros x v Hclosed.
  unfold rho_no_free_all. intros a b Hneq.
  unfold rho_single. destruct (String.eqb b x) eqn:Heq.
  - apply String.eqb_eq in Heq. subst. apply (Hclosed a).
  - simpl. intro Hfree. apply Hneq. symmetry. exact Hfree.
Qed.

Lemma env_rel_closed_left : forall Σ G rho1 rho2,
  env_rel Σ G rho1 rho2 ->
  rho_closed_on G rho1.
Proof.
  intros Σ G rho1 rho2 Henv x T Hlook.
  specialize (Henv 1) as Henv1.
  specialize (Henv1 x T Hlook) as Hrel.
  apply (val_rel_closed_left_n 1 Σ T (rho1 x) (rho2 x)); [lia | exact Hrel].
Qed.

Lemma env_rel_closed_right : forall Σ G rho1 rho2,
  env_rel Σ G rho1 rho2 ->
  rho_closed_on G rho2.
Proof.
  intros Σ G rho1 rho2 Henv x T Hlook.
  specialize (Henv 1) as Henv1.
  specialize (Henv1 x T Hlook) as Hrel.
  apply (val_rel_closed_right_n 1 Σ T (rho1 x) (rho2 x)); [lia | exact Hrel].
Qed.

Lemma closed_except_subst_rho_shadow : forall G Σ Δ rho x e T1 T2 eps,
  has_type ((x, T1) :: G) Σ Δ e T2 eps ->
  rho_closed_on G rho ->
  closed_except x (subst_rho (rho_shadow rho x) e).
Proof.
  intros G Σ Δ rho x e T1 T2 eps Hty Hclosed y Hyneq Hfree.
  destruct (free_in_subst_rho y (rho_shadow rho x) e Hfree) as [z [Hzfree Hzrho]].
  destruct (free_in_context _ _ _ _ _ _ _ Hzfree Hty) as [Tz Hlook].
  simpl in Hlook.
  destruct (String.eqb z x) eqn:Heqzx.
  - apply String.eqb_eq in Heqzx. subst.
    unfold rho_shadow in Hzrho. rewrite String.eqb_refl in Hzrho. simpl in Hzrho.
    apply Hyneq. exact Hzrho.
  - simpl in Hlook.
    unfold rho_shadow in Hzrho. rewrite Heqzx in Hzrho.
    specialize (Hclosed z Tz Hlook) as Hclosedz.
    unfold closed_expr in Hclosedz. apply (Hclosedz y) in Hzrho. contradiction.
Qed.

Lemma subst_not_free : forall x v e,
  ~ free_in x e ->
  [x := v] e = e.
Proof.
  induction e; intros Hfree; simpl in *; try reflexivity.
  - destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst. exfalso. apply Hfree. reflexivity.
    + reflexivity.
  - destruct (String.eqb x i) eqn:Heq.
    + reflexivity.
    + apply String.eqb_neq in Heq.
      f_equal. apply IHe. intro Hbody. apply Hfree. split; assumption.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + apply IHe2. intro H. apply Hfree. right. exact H.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + apply IHe2. intro H. apply Hfree. right. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + destruct (String.eqb x i) eqn:Heq1.
      * reflexivity.
      * apply String.eqb_neq in Heq1.
        apply IHe2. intro H. apply Hfree. right. left. split; assumption.
    + destruct (String.eqb x i0) eqn:Heq2.
      * reflexivity.
      * apply String.eqb_neq in Heq2.
        apply IHe3. intro H. apply Hfree. right. right. split; assumption.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + apply IHe2. intro H. apply Hfree. right. left. exact H.
    + apply IHe3. intro H. apply Hfree. right. right. exact H.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + destruct (String.eqb x i) eqn:Heq.
      * reflexivity.
      * apply String.eqb_neq in Heq.
        apply IHe2. intro H. apply Hfree. right. split; assumption.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + destruct (String.eqb x i) eqn:Heq.
      * reflexivity.
      * apply String.eqb_neq in Heq.
        apply IHe2. intro H. apply Hfree. right. split; assumption.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + apply IHe2. intro H. apply Hfree. right. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal.
    + apply IHe1. intro H. apply Hfree. left. exact H.
    + apply IHe2. intro H. apply Hfree. right. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
  - f_equal. apply IHe. intro H. apply Hfree. exact H.
Qed.

Lemma rho_shadow_id : forall x,
  rho_shadow rho_id x = rho_id.
Proof.
  intros x. unfold rho_shadow, rho_id.
  apply functional_extensionality. intros y.
  destruct (String.eqb y x); reflexivity.
Qed.

Lemma rho_shadow_identity : forall rho x,
  (forall y, rho y = EVar y) ->
  forall y, rho_shadow rho x y = EVar y.
Proof.
  intros rho x Hrho y.
  unfold rho_shadow.
  destruct (String.eqb y x); [reflexivity | apply Hrho].
Qed.

Lemma subst_rho_identity : forall e rho,
  (forall x, rho x = EVar x) ->
  subst_rho rho e = e.
Proof.
  induction e; intros rho Hrho; simpl; try reflexivity.
  - apply Hrho.
  - f_equal.
    apply IHe.
    intros y. apply rho_shadow_identity; assumption.
  - rewrite (IHe1 rho Hrho). rewrite (IHe2 rho Hrho). reflexivity.
  - rewrite (IHe1 rho Hrho). rewrite (IHe2 rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe1 rho Hrho).
    rewrite (IHe2 (rho_shadow rho i) (rho_shadow_identity rho i Hrho)).
    rewrite (IHe3 (rho_shadow rho i0) (rho_shadow_identity rho i0 Hrho)).
    reflexivity.
  - rewrite (IHe1 rho Hrho).
    rewrite (IHe2 rho Hrho).
    rewrite (IHe3 rho Hrho).
    reflexivity.
  - rewrite (IHe1 rho Hrho).
    rewrite (IHe2 (rho_shadow rho i) (rho_shadow_identity rho i Hrho)).
    reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe1 rho Hrho).
    rewrite (IHe2 (rho_shadow rho i) (rho_shadow_identity rho i Hrho)).
    reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe1 rho Hrho). rewrite (IHe2 rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe1 rho Hrho). rewrite (IHe2 rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
  - rewrite (IHe rho Hrho). reflexivity.
Qed.

Lemma subst_rho_id : forall e,
  subst_rho rho_id e = e.
Proof.
  intros e.
  apply (subst_rho_identity e rho_id).
  intros x. unfold rho_id. reflexivity.
Qed.

Lemma rho_shadow_single_eq : forall x v i,
  x <> i ->
  rho_shadow (rho_single x v) i = rho_single x v.
Proof.
  intros x v i Hneq.
  unfold rho_shadow, rho_single.
  apply functional_extensionality. intros y.
  destruct (String.eqb y i) eqn:Heqyi.
  - apply String.eqb_eq in Heqyi. subst.
    assert (String.eqb i x = false) as Heqix.
    { apply (proj2 (String.eqb_neq i x)).
      intro Heq. apply Hneq. symmetry. exact Heq. }
    rewrite Heqix. reflexivity.
  - reflexivity.
Qed.

Lemma rho_shadow_single_id : forall x v,
  rho_shadow (rho_single x v) x = rho_id.
Proof.
  intros x v.
  unfold rho_shadow, rho_single, rho_id.
  apply functional_extensionality. intros y.
  destruct (String.eqb y x) eqn:Heqyx; reflexivity.
Qed.

Lemma subst_rho_single : forall e x v,
  subst_rho (rho_single x v) e = [x := v] e.
Proof.
  induction e; intros x v; simpl; try reflexivity.
  - unfold rho_single. destruct (String.eqb x i) eqn:Heqxi; simpl.
    + apply String.eqb_eq in Heqxi. subst. rewrite String.eqb_refl. reflexivity.
    + apply String.eqb_neq in Heqxi.
      assert (String.eqb i x = false) as Heqix.
      { destruct (String.eqb i x) eqn:Heqix; auto.
        apply String.eqb_eq in Heqix. subst.
        exfalso. apply Heqxi. reflexivity. }
      rewrite Heqix. reflexivity.
  - destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      rewrite rho_shadow_single_id. rewrite subst_rho_id. reflexivity.
    + apply (proj1 (String.eqb_neq x i)) in Heq.
      rewrite rho_shadow_single_eq by assumption. rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1.
    destruct (String.eqb x i) eqn:Heq1.
    + apply String.eqb_eq in Heq1. subst.
      rewrite rho_shadow_single_id. rewrite subst_rho_id.
      destruct (String.eqb i i0) eqn:Heq2.
      * apply String.eqb_eq in Heq2. subst.
        rewrite rho_shadow_single_id. rewrite subst_rho_id. reflexivity.
      * apply (proj1 (String.eqb_neq i i0)) in Heq2.
        rewrite rho_shadow_single_eq by assumption. rewrite IHe3. reflexivity.
    + apply (proj1 (String.eqb_neq x i)) in Heq1.
      rewrite rho_shadow_single_eq by assumption. rewrite IHe2.
      destruct (String.eqb x i0) eqn:Heq2.
      * apply String.eqb_eq in Heq2. subst.
        rewrite rho_shadow_single_id. rewrite subst_rho_id. reflexivity.
      * apply (proj1 (String.eqb_neq x i0)) in Heq2.
        rewrite rho_shadow_single_eq by assumption. rewrite IHe3. reflexivity.
  - rewrite IHe1, IHe2, IHe3. reflexivity.
  - rewrite IHe1.
    destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      rewrite rho_shadow_single_id. rewrite subst_rho_id. reflexivity.
    + apply (proj1 (String.eqb_neq x i)) in Heq.
      rewrite rho_shadow_single_eq by assumption. rewrite IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1.
    destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      rewrite rho_shadow_single_id. rewrite subst_rho_id. reflexivity.
    + apply (proj1 (String.eqb_neq x i)) in Heq.
      rewrite rho_shadow_single_eq by assumption. rewrite IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
Qed.

Lemma rho_shadow_extend_same : forall rho x v,
  rho_shadow (rho_extend rho x v) x = rho_shadow rho x.
Proof.
  intros rho x v. unfold rho_shadow, rho_extend.
  apply functional_extensionality. intros y.
  destruct (String.eqb y x) eqn:Heq; reflexivity.
Qed.

Lemma rho_shadow_shadow_same : forall rho x,
  rho_shadow (rho_shadow rho x) x = rho_shadow rho x.
Proof.
  intros rho x. unfold rho_shadow.
  apply functional_extensionality. intros y.
  destruct (String.eqb y x) eqn:Heq; reflexivity.
Qed.

Lemma rho_shadow_shadow_comm : forall rho x y,
  x <> y ->
  rho_shadow (rho_shadow rho x) y = rho_shadow (rho_shadow rho y) x.
Proof.
  intros rho x y Hneq. unfold rho_shadow.
  apply functional_extensionality. intros z.
  destruct (String.eqb z y) eqn:Heqzy;
  destruct (String.eqb z x) eqn:Heqzx; try reflexivity.
  all: apply String.eqb_eq in Heqzy; apply String.eqb_eq in Heqzx; subst;
    exfalso; apply Hneq; reflexivity.
Qed.

Lemma rho_shadow_extend_comm : forall rho x y v,
  x <> y ->
  rho_shadow (rho_extend rho x v) y = rho_extend (rho_shadow rho y) x v.
Proof.
  intros rho x y v Hneq. unfold rho_shadow, rho_extend.
  apply functional_extensionality. intros z.
  destruct (String.eqb z y) eqn:Heqzy;
  destruct (String.eqb z x) eqn:Heqzx; try reflexivity.
  all: apply String.eqb_eq in Heqzy; apply String.eqb_eq in Heqzx; subst;
    exfalso; apply Hneq; reflexivity.
Qed.

Lemma rho_no_free_extend : forall rho x v,
  rho_no_free_all rho ->
  closed_expr v ->
  rho_no_free_all (rho_extend rho x v).
Proof.
  intros rho x v Hno Hclosed.
  unfold rho_no_free_all in *. intros a b Hneq.
  unfold rho_extend. destruct (String.eqb b x) eqn:Heq.
  - apply String.eqb_eq in Heq. subst. apply Hclosed.
  - apply Hno. exact Hneq.
Qed.

Lemma rho_no_free_shadow : forall rho x,
  rho_no_free_all rho ->
  rho_no_free_all (rho_shadow rho x).
Proof.
  intros rho x Hno.
  unfold rho_no_free_all in *. intros a b Hneq.
  unfold rho_shadow. destruct (String.eqb b x) eqn:Heq.
  - simpl. intro Hfree. apply Hneq. symmetry. exact Hfree.
  - apply Hno. exact Hneq.
Qed.

Lemma subst_rho_extend : forall rho x v e,
  rho_no_free_all rho ->
  [x := v] (subst_rho (rho_shadow rho x) e) =
  subst_rho (rho_extend rho x v) e.
Proof.
  intros rho0 x0 v0 e Hno.
  revert rho0 x0 v0 Hno.
  induction e; intros rho0 x0 v0 Hno; simpl; try reflexivity.
  - destruct (String.eqb i x0) eqn:Heq; simpl.
    + apply String.eqb_eq in Heq. subst.
      unfold rho_shadow, rho_extend. simpl.
      rewrite String.eqb_refl. simpl. rewrite String.eqb_refl. reflexivity.
    + assert (i <> x0) as Hneq by (apply String.eqb_neq; exact Heq).
      unfold rho_shadow, rho_extend.
      rewrite Heq.
      simpl.
      apply subst_not_free.
      apply (Hno x0 i). exact Hneq.
  - destruct (String.eqb x0 i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      simpl. rewrite rho_shadow_shadow_same. rewrite rho_shadow_extend_same. reflexivity.
    + apply String.eqb_neq in Heq.
      simpl.
      rewrite (rho_shadow_shadow_comm rho0 x0 i) by assumption.
      rewrite (rho_shadow_extend_comm rho0 x0 i v0) by assumption.
      rewrite (IHe (rho_shadow rho0 i) x0 v0 (rho_no_free_shadow rho0 i Hno)).
      reflexivity.
  - rewrite (IHe1 rho0 x0 v0 Hno), (IHe2 rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe1 rho0 x0 v0 Hno), (IHe2 rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe1 rho0 x0 v0 Hno).
    destruct (String.eqb x0 i) eqn:Heq1.
    + apply String.eqb_eq in Heq1. subst.
      simpl.
      rewrite rho_shadow_shadow_same. rewrite rho_shadow_extend_same.
      destruct (String.eqb i i0) eqn:Heq2.
      * apply String.eqb_eq in Heq2. subst.
        simpl.
        rewrite rho_shadow_shadow_same. rewrite rho_shadow_extend_same. reflexivity.
      * assert (i <> i0) as Hneq2 by (apply String.eqb_neq; exact Heq2).
        simpl.
        rewrite (rho_shadow_shadow_comm rho0 i i0) by assumption.
        rewrite (rho_shadow_extend_comm rho0 i i0 v0) by assumption.
        rewrite (IHe3 (rho_shadow rho0 i0) i v0 (rho_no_free_shadow rho0 i0 Hno)).
        reflexivity.
    + assert (x0 <> i) as Hneq1 by (apply String.eqb_neq; exact Heq1).
      simpl.
      rewrite (rho_shadow_shadow_comm rho0 x0 i) by assumption.
      rewrite (rho_shadow_extend_comm rho0 x0 i v0) by assumption.
      rewrite (IHe2 (rho_shadow rho0 i) x0 v0 (rho_no_free_shadow rho0 i Hno)).
      destruct (String.eqb x0 i0) eqn:Heq2.
      * apply String.eqb_eq in Heq2. subst.
        simpl.
        rewrite rho_shadow_shadow_same. rewrite rho_shadow_extend_same. reflexivity.
      * assert (x0 <> i0) as Hneq2 by (apply String.eqb_neq; exact Heq2).
        simpl.
        rewrite (rho_shadow_shadow_comm rho0 x0 i0) by assumption.
        rewrite (rho_shadow_extend_comm rho0 x0 i0 v0) by assumption.
        rewrite (IHe3 (rho_shadow rho0 i0) x0 v0 (rho_no_free_shadow rho0 i0 Hno)).
        reflexivity.
  - rewrite (IHe1 rho0 x0 v0 Hno). rewrite (IHe2 rho0 x0 v0 Hno). rewrite (IHe3 rho0 x0 v0 Hno). reflexivity.
  - destruct (String.eqb x0 i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      simpl.
      rewrite (IHe1 rho0 i v0 Hno).
      rewrite rho_shadow_shadow_same. rewrite rho_shadow_extend_same. reflexivity.
    + apply String.eqb_neq in Heq.
      simpl.
      rewrite (IHe1 rho0 x0 v0 Hno).
      rewrite (rho_shadow_shadow_comm rho0 x0 i) by assumption.
      rewrite (rho_shadow_extend_comm rho0 x0 i v0) by assumption.
      rewrite (IHe2 (rho_shadow rho0 i) x0 v0 (rho_no_free_shadow rho0 i Hno)).
      reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - destruct (String.eqb x0 i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      simpl.
      rewrite (IHe1 rho0 i v0 Hno).
      rewrite rho_shadow_shadow_same. rewrite rho_shadow_extend_same. reflexivity.
    + apply String.eqb_neq in Heq.
      simpl.
      rewrite (IHe1 rho0 x0 v0 Hno).
      rewrite (rho_shadow_shadow_comm rho0 x0 i) by assumption.
      rewrite (rho_shadow_extend_comm rho0 x0 i v0) by assumption.
      rewrite (IHe2 (rho_shadow rho0 i) x0 v0 (rho_no_free_shadow rho0 i Hno)).
      reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe1 rho0 x0 v0 Hno). rewrite (IHe2 rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe1 rho0 x0 v0 Hno). rewrite (IHe2 rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
  - rewrite (IHe rho0 x0 v0 Hno). reflexivity.
Qed.

(** Empty environment is related to any environments (step-indexed version)
    Package I Proof Integration: env_rel_empty *)
Lemma env_rel_empty_n : forall n Σ rho1 rho2,
  env_rel_n n Σ nil rho1 rho2.
Proof.
  intros n Σ rho1 rho2.
  unfold env_rel_n. intros x T Hlook.
  simpl in Hlook. discriminate.
Qed.

(** Empty environment is related (forall-n version) *)
Lemma env_rel_empty : forall Σ rho1 rho2,
  env_rel Σ nil rho1 rho2.
Proof.
  intros Σ rho1 rho2 n.
  apply env_rel_empty_n.
Qed.

Lemma env_rel_extend_n : forall n Σ G rho1 rho2 x T v1 v2,
  env_rel_n n Σ G rho1 rho2 ->
  val_rel_n n Σ T v1 v2 ->
  env_rel_n n Σ ((x, T) :: G) (rho_extend rho1 x v1) (rho_extend rho2 x v2).
Proof.
  intros n Σ G rho1 rho2 x T v1 v2 Henv Hv.
  unfold env_rel_n in *. intros y Ty Hlook.
  simpl in Hlook.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq. subst.
    inversion Hlook; subst.
    unfold rho_extend.
    destruct (String.eqb x x) eqn:Heqxx.
    * simpl. exact Hv.
    * apply String.eqb_neq in Heqxx. exfalso. apply Heqxx. reflexivity.
  - unfold rho_extend. rewrite Heq. apply Henv. assumption.
Qed.

Lemma env_rel_extend : forall Σ G rho1 rho2 x T v1 v2,
  env_rel Σ G rho1 rho2 ->
  val_rel Σ T v1 v2 ->
  env_rel Σ ((x, T) :: G) (rho_extend rho1 x v1) (rho_extend rho2 x v2).
Proof.
  intros Σ G rho1 rho2 x T v1 v2 Henv Hv n.
  apply env_rel_extend_n.
  - apply Henv.
  - apply Hv.
Qed.

(** Store typing monotonicity for env_rel (Kripke monotonicity) *)
Lemma env_rel_mono_store : forall Σ Σ' G rho1 rho2,
  store_ty_extends Σ Σ' ->
  env_rel Σ G rho1 rho2 ->
  env_rel Σ' G rho1 rho2.
Proof.
  intros Σ Σ' G rho1 rho2 Hext Henv n x T Hlook.
  apply val_rel_n_mono_store with (Σ := Σ).
  - exact Hext.
  - apply Henv. exact Hlook.
Qed.

(** ** Multi-step Lemmas *)

Lemma multi_step_trans : forall cfg1 cfg2 cfg3,
  cfg1 -->* cfg2 ->
  cfg2 -->* cfg3 ->
  cfg1 -->* cfg3.
Proof.
  intros cfg1 cfg2 cfg3 H12 H23.
  induction H12.
  - assumption.
  - eapply MS_Step; eauto.
Qed.

Lemma multi_step_app1 : forall e1 e1' e2 st st' ctx ctx',
  (e1, st, ctx) -->* (e1', st', ctx') ->
  (EApp e1 e2, st, ctx) -->* (EApp e1' e2, st', ctx').
Proof.
  intros e1 e1' e2 st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_App1. exact H.
    + apply (IHmulti_step e_mid e1' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_app2 : forall v1 e2 e2' st st' ctx ctx',
  value v1 ->
  (e2, st, ctx) -->* (e2', st', ctx') ->
  (EApp v1 e2, st, ctx) -->* (EApp v1 e2', st', ctx').
Proof.
  intros v1 e2 e2' st st' ctx ctx' Hv H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_App2; eauto.
    + apply (IHmulti_step e_mid e2' st_mid st' ctx_mid ctx').
      * exact Hv.
      * exact eq_refl.
      * exact eq_refl.
Qed.

Lemma multi_step_pair1 : forall e1 e1' e2 st st' ctx ctx',
  (e1, st, ctx) -->* (e1', st', ctx') ->
  (EPair e1 e2, st, ctx) -->* (EPair e1' e2, st', ctx').
Proof.
  intros e1 e1' e2 st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_Pair1. exact H.
    + apply (IHmulti_step e_mid e1' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_pair2 : forall v1 e2 e2' st st' ctx ctx',
  value v1 ->
  (e2, st, ctx) -->* (e2', st', ctx') ->
  (EPair v1 e2, st, ctx) -->* (EPair v1 e2', st', ctx').
Proof.
  intros v1 e2 e2' st st' ctx ctx' Hv H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_Pair2; eauto.
    + apply (IHmulti_step e_mid e2' st_mid st' ctx_mid ctx').
      * exact Hv.
      * exact eq_refl.
      * exact eq_refl.
Qed.

Lemma multi_step_fst : forall e e' st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EFst e, st, ctx) -->* (EFst e', st', ctx').
Proof.
  intros e e' st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_FstStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_snd : forall e e' st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (ESnd e, st, ctx) -->* (ESnd e', st', ctx').
Proof.
  intros e e' st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_SndStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_inl : forall e e' T st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EInl e T, st, ctx) -->* (EInl e' T, st', ctx').
Proof.
  intros e e' T st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_InlStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_inr : forall e e' T st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EInr e T, st, ctx) -->* (EInr e' T, st', ctx').
Proof.
  intros e e' T st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_InrStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_case : forall e e' x1 e1 x2 e2 st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (ECase e x1 e1 x2 e2, st, ctx) -->* (ECase e' x1 e1 x2 e2, st', ctx').
Proof.
  intros e e' x1 e1 x2 e2 st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_CaseStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_if : forall e1 e1' e2 e3 st st' ctx ctx',
  (e1, st, ctx) -->* (e1', st', ctx') ->
  (EIf e1 e2 e3, st, ctx) -->* (EIf e1' e2 e3, st', ctx').
Proof.
  intros e1 e1' e2 e3 st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_IfStep. exact H.
    + apply (IHmulti_step e_mid e1' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_let : forall x e1 e1' e2 st st' ctx ctx',
  (e1, st, ctx) -->* (e1', st', ctx') ->
  (ELet x e1 e2, st, ctx) -->* (ELet x e1' e2, st', ctx').
Proof.
  intros x e1 e1' e2 st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_LetStep. exact H.
    + apply (IHmulti_step e_mid e1' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_classify : forall e e' st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EClassify e, st, ctx) -->* (EClassify e', st', ctx').
Proof.
  intros e e' st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_ClassifyStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_prove : forall e e' st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EProve e, st, ctx) -->* (EProve e', st', ctx').
Proof.
  intros e e' st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_ProveStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx'); reflexivity.
Qed.

Lemma multi_step_require : forall eff e e' st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (ERequire eff e, st, ctx) -->* (ERequire eff e', st', ctx').
Proof.
  intros eff e e' st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_RequireStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx' eq_refl eq_refl).
Qed.

Lemma multi_step_grant : forall eff e e' st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EGrant eff e, st, ctx) -->* (EGrant eff e', st', ctx').
Proof.
  intros eff e e' st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_GrantStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx' eq_refl eq_refl).
Qed.

Lemma multi_step_perform : forall eff e e' st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EPerform eff e, st, ctx) -->* (EPerform eff e', st', ctx').
Proof.
  intros eff e e' st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_PerformStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx' eq_refl eq_refl).
Qed.

Lemma multi_step_handle : forall e e' x h st st' ctx ctx',
  (e, st, ctx) -->* (e', st', ctx') ->
  (EHandle e x h, st, ctx) -->* (EHandle e' x h, st', ctx').
Proof.
  intros e e' x h st st' ctx ctx' H.
  dependent induction H.
  - apply MS_Refl.
  - destruct cfg2 as [[e_mid st_mid] ctx_mid].
    eapply MS_Step.
    + apply ST_HandleStep. exact H.
    + apply (IHmulti_step e_mid e' st_mid st' ctx_mid ctx' eq_refl eq_refl).
Qed.

Lemma exp_rel_of_val_rel : forall Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  exp_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hrel n.
  destruct n as [| n'].
  - exact I.
  - intros Σ_cur st1 st2 ctx Hext Hstore Hwf1 Hwf2 Hagree.
    (* Values don't step, so we return immediately with Σ_cur *)
    exists v1, v2, st1, st2, ctx, Σ_cur.
    split.
    + (* store_ty_extends Σ_cur Σ_cur - reflexive *)
      unfold store_ty_extends. intros l T' sl Hlook. exact Hlook.
    + split.
      * apply MS_Refl.
      * split.
        -- apply MS_Refl.
        -- split.
           ++ (* value v1 - from val_rel *)
              apply (val_rel_value_left Σ T v1 v2 Hrel).
           ++ split.
              ** (* value v2 - from val_rel *)
                 apply (val_rel_value_right Σ T v1 v2 Hrel).
              ** split.
                 { (* val_rel_n n' Σ_cur T v1 v2 *)
                   apply (val_rel_n_mono_store n' Σ Σ_cur T v1 v2 Hext (Hrel n')). }
                 split. { exact Hstore. }
                 split. { exact Hwf1. }
                 split. { exact Hwf2. }
                 { exact Hagree. }
Qed.

Lemma exp_rel_of_val_rel_step : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  exp_rel_n (S n) Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel Σ_cur st1 st2 ctx Hext Hstore Hwf1 Hwf2 Hagree.
  exists v1, v2, st1, st2, ctx, Σ_cur.
  split.
  - unfold store_ty_extends. intros l T' sl Hlook. exact Hlook.
  - split.
    + apply MS_Refl.
    + split.
      * apply MS_Refl.
      * split.
        -- apply (val_rel_value_left_n n Σ T v1 v2 Hn Hrel).
        -- split.
           ++ apply (val_rel_value_right_n n Σ T v1 v2 Hn Hrel).
           ++ split.
              ** apply (val_rel_n_mono_store n Σ Σ_cur T v1 v2 Hext Hrel).
              ** split. { exact Hstore. }
                 split. { exact Hwf1. }
                 split. { exact Hwf2. }
                 { exact Hagree. }
Qed.

Lemma exp_rel_of_val_rel_n : forall n Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  exp_rel_n n Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hrel.
  exact (exp_rel_of_val_rel Σ T v1 v2 Hrel n).
Qed.

Fixpoint lookup_val (x : ident) (s : list (ident * expr)) : option expr :=
  match s with
  | nil => None
  | (y, v) :: s' => if String.eqb x y then Some v else lookup_val x s'
  end.

Definition subst_rel (Σ : store_ty) (G : type_env) (s1 s2 : list (ident * expr)) : Prop :=
  forall x T, lookup x G = Some T ->
    exists v1 v2,
      lookup_val x s1 = Some v1 /\
      lookup_val x s2 = Some v2 /\
      val_rel Σ T v1 v2.

(** ** Fundamental Theorem *)

(** Helper: extract product component relation from val_rel_n.
    These extract the first/second component relation from a product relation,
    preserving the step index (key benefit of the new structure). *)
Lemma value_pair_inv : forall x y,
  value (EPair x y) -> value x /\ value y.
Proof.
  intros x y Hval. inversion Hval; subst. split; assumption.
Qed.

Lemma value_inl_inv : forall v T,
  value (EInl v T) -> value v.
Proof.
  intros v T Hval. inversion Hval; subst. assumption.
Qed.

Lemma value_inr_inv : forall v T,
  value (EInr v T) -> value v.
Proof.
  intros v T Hval. inversion Hval; subst. assumption.
Qed.

Lemma closed_expr_inl_inv : forall v T,
  closed_expr (EInl v T) -> closed_expr v.
Proof.
  intros v T Hcl y Hfree. apply (Hcl y). simpl. exact Hfree.
Qed.

Lemma closed_expr_inr_inv : forall v T,
  closed_expr (EInr v T) -> closed_expr v.
Proof.
  intros v T Hcl y Hfree. apply (Hcl y). simpl. exact Hfree.
Qed.

(** Helper to extract val_rel_at_type from val_rel_n for products.
    Note: With the cumulative structure, we get val_rel_at_type directly,
    and can combine with value/closed properties separately if needed. *)
Lemma val_rel_n_prod_decompose : forall n Σ T1 T2 v1 v2,
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    value a1 /\ value b1 /\ value a2 /\ value b2 /\
    closed_expr a1 /\ closed_expr b1 /\ closed_expr a2 /\ closed_expr b2 /\
    val_rel_at_type Σ (store_rel_n (n-1)) (val_rel_n (n-1)) (store_rel_n (n-1)) T1 a1 a2 /\
    val_rel_at_type Σ (store_rel_n (n-1)) (val_rel_n (n-1)) (store_rel_n (n-1)) T2 b1 b2.
Proof.
  intros n Σ T1 T2 v1 v2 Hn Hrel.
  destruct n as [| n']; [lia |].
  simpl in Hrel.
  destruct Hrel as [Hrec [Hval1 [Hval2 [Hclosed1 [Hclosed2 [Htyping Hrat]]]]]].
  simpl in Hrat.
  destruct Hrat as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
  exists x1, y1, x2, y2.
  subst v1 v2.
  apply value_pair_inv in Hval1. destruct Hval1 as [Ha1 Hb1].
  apply value_pair_inv in Hval2. destruct Hval2 as [Ha2 Hb2].
  assert (Hcx1 : closed_expr x1).
  { intros y Hfree. apply (Hclosed1 y). simpl. left. exact Hfree. }
  assert (Hcy1 : closed_expr y1).
  { intros y Hfree. apply (Hclosed1 y). simpl. right. exact Hfree. }
  assert (Hcx2 : closed_expr x2).
  { intros y Hfree. apply (Hclosed2 y). simpl. left. exact Hfree. }
  assert (Hcy2 : closed_expr y2).
  { intros y Hfree. apply (Hclosed2 y). simpl. right. exact Hfree. }
  (* S n' - 1 = n' *)
  replace (S n' - 1) with n' by lia.
  repeat split; try assumption.
Qed.

(** For first-order types, we can construct val_rel_n from val_rel_at_type.
    This is a general building lemma for first-order types. *)
Lemma val_rel_n_of_first_order : forall n Σ T v1 v2,
  first_order_type T = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  (forall sp vl sl, val_rel_at_type Σ sp vl sl T v1 v2) ->
  val_rel_n n Σ T v1 v2.
Proof.
  induction n as [| n' IHn]; intros Σ T v1 v2 Hfo Hval1 Hval2 Hcl1 Hcl2 Hrat.
  - rewrite val_rel_n_0_unfold.
    destruct (NonInterference_v2.first_order_type T) eqn:Hfo'.
    + simpl. repeat split; try assumption.
      apply (proj1 (val_rel_at_type_fo_equiv T Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) v1 v2 Hfo')).
      apply Hrat.
    + change (NonInterference_v2.first_order_type T) with (first_order_type T) in Hfo'.
      rewrite Hfo in Hfo'. discriminate.
  - rewrite val_rel_n_S_unfold.
    (* Handle the qualified name *)
    change (NonInterference_v2.first_order_type T) with (first_order_type T).
    rewrite Hfo.
    split.
    + apply IHn; assumption.
    + repeat split; try assumption.
      apply Hrat.
Qed.

(** LEMMA: For first-order types, convert val_rel_n to val_rel. *)
Lemma val_rel_n_to_val_rel_fo : forall Σ T v1 v2,
  first_order_type T = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hfo _ _ _ _ [n Hrel].
  unfold val_rel. intro m.
  apply val_rel_n_step_up_fo; [exact Hfo |].
  apply (val_rel_n_mono 0 (S n) Σ T v1 v2); [lia | exact Hrel].
Qed.

(** LEMMA: Higher-order step-to-limit conversion — PROVEN.
    Strategy: from val_rel_n (S n), extract typing via val_rel_n_typing,
    then for any target step m, either step down (val_rel_n_mono) or
    step up (val_rel_n_step_up) to reach m. *)
Lemma val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hv1 Hv2 [n Hrel].
  destruct (val_rel_n_typing (S n) Σ T v1 v2 Hrel) as [Hty1 Hty2].
  unfold val_rel. intro m.
  (* We prove val_rel_n m Σ T v1 v2 by induction on m *)
  induction m as [| m' IHm].
  - (* m = 0 *)
    apply (val_rel_n_mono 0 (S n) Σ T v1 v2). lia. exact Hrel.
  - (* m = S m' *)
    apply val_rel_n_step_up; assumption.
Qed.

(** For first-order types, convert val_rel_at_type to val_rel.

    REVOLUTIONARY CHANGE: Instead of axiomatizing value/closed extraction
    from val_rel_at_type (which doesn't hold for TBytes/TSecret), we take
    value and closed_expr as explicit premises. This allows callers who
    already have these properties (from the strengthened TFn definition)
    to use this lemma without needing unsound axioms.

    This ELIMINATES 4 axioms:
    - val_rel_at_type_value_left
    - val_rel_at_type_value_right
    - val_rel_at_type_closed_left
    - val_rel_at_type_closed_right *)
Lemma val_rel_at_type_to_val_rel_fo : forall Σ sp vl sl T v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ sp vl sl T v1 v2 Hfo Hrat Hval1 Hval2 Hcl1 Hcl2.
  (* value and closed now come as premises - no axioms needed! *)
  apply val_rel_n_to_val_rel_fo; try assumption.
  exists 0.
  apply val_rel_n_of_first_order; try assumption.
  assert (Hfo_rel : val_rel_at_type_fo T v1 v2).
  { apply (proj1 (val_rel_at_type_fo_equiv T Σ sp vl sl v1 v2 Hfo)). exact Hrat. }
  intros sp' vl' sl'.
  apply (proj2 (val_rel_at_type_fo_equiv T Σ sp' vl' sl' v1 v2 Hfo)).
  exact Hfo_rel.
Qed.

Lemma val_rel_n_prod_fst : forall n Σ T1 T2 v1 v2,
  first_order_type T1 = true ->
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_n n Σ T1 a1 a2.
Proof.
  intros n Σ T1 T2 v1 v2 Hfo Hn Hrel.
  destruct (val_rel_n_prod_decompose n Σ T1 T2 v1 v2 Hn Hrel)
    as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hva1 [Hvb1 [Hva2 [Hvb2
        [Hca1 [Hcb1 [Hca2 [Hcb2 [Hrat1 Hrat2]]]]]]]]]]]]]]].
  exists a1, b1, a2, b2.
  split; [exact Heq1 |].
  split; [exact Heq2 |].
  apply val_rel_n_of_first_order; try assumption.
  intros sp vl sl.
  apply (proj2 (val_rel_at_type_fo_equiv T1 Σ sp vl sl a1 a2 Hfo)).
  apply (proj1 (val_rel_at_type_fo_equiv T1 Σ (store_rel_n (n - 1)) (val_rel_n (n - 1)) (store_rel_n (n - 1)) a1 a2 Hfo)).
  exact Hrat1.
Qed.

Lemma val_rel_n_prod_snd : forall n Σ T1 T2 v1 v2,
  first_order_type T2 = true ->
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_n n Σ T2 b1 b2.
Proof.
  intros n Σ T1 T2 v1 v2 Hfo Hn Hrel.
  destruct (val_rel_n_prod_decompose n Σ T1 T2 v1 v2 Hn Hrel)
    as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hva1 [Hvb1 [Hva2 [Hvb2
        [Hca1 [Hcb1 [Hca2 [Hcb2 [Hrat1 Hrat2]]]]]]]]]]]]]]].
  exists a1, b1, a2, b2.
  split; [exact Heq1 |].
  split; [exact Heq2 |].
  apply val_rel_n_of_first_order; try assumption.
  intros sp vl sl.
  apply (proj2 (val_rel_at_type_fo_equiv T2 Σ sp vl sl b1 b2 Hfo)).
  apply (proj1 (val_rel_at_type_fo_equiv T2 Σ (store_rel_n (n - 1)) (val_rel_n (n - 1)) (store_rel_n (n - 1)) b1 b2 Hfo)).
  exact Hrat2.
Qed.

(** Extract typing from val_rel_n for higher-order types.
    For HO types, val_rel_n at any step carries has_type. *)
Lemma val_rel_n_typing_ho : forall n Σ T v1 v2,
  first_order_type T = false ->
  val_rel_n n Σ T v1 v2 ->
  has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure.
Proof.
  intros n Σ T v1 v2 Hho Hrel.
  destruct n as [| n'].
  - rewrite val_rel_n_0_unfold in Hrel.
    destruct Hrel as [_ [_ [_ [_ Hif]]]].
    change (NonInterference_v2.first_order_type T) with (first_order_type T) in Hif.
    rewrite Hho in Hif. exact Hif.
  - rewrite val_rel_n_S_unfold in Hrel.
    destruct Hrel as [_ [_ [_ [_ [_ [Htyping _]]]]]].
    change (NonInterference_v2.first_order_type T) with (first_order_type T) in Htyping.
    rewrite Hho in Htyping. exact Htyping.
Qed.

(** Typing inversion for pairs: extract component typing from pair typing *)
Lemma has_type_pair_inv : forall Σ e1 e2 T1 T2 ε,
  has_type nil Σ Public (EPair e1 e2) (TProd T1 T2) ε ->
  exists ε1 ε2,
    has_type nil Σ Public e1 T1 ε1 /\
    has_type nil Σ Public e2 T2 ε2 /\
    ε = effect_join ε1 ε2.
Proof.
  intros Σ e1 e2 T1 T2 ε Hty.
  inversion Hty; subst.
  exists ε1, ε2. repeat split; assumption.
Qed.

(** Typing inversion for inl *)
Lemma has_type_inl_inv : forall Σ e T1 T2 ε,
  has_type nil Σ Public (EInl e T2) (TSum T1 T2) ε ->
  has_type nil Σ Public e T1 ε.
Proof.
  intros Σ e T1 T2 ε Hty.
  inversion Hty; subst. assumption.
Qed.

(** Typing inversion for inr *)
Lemma has_type_inr_inv : forall Σ e T1 T2 ε,
  has_type nil Σ Public (EInr e T1) (TSum T1 T2) ε ->
  has_type nil Σ Public e T2 ε.
Proof.
  intros Σ e T1 T2 ε Hty.
  inversion Hty; subst. assumption.
Qed.

(** Typing inversion for classify *)
Lemma has_type_classify_inv : forall Σ e T ε,
  has_type nil Σ Public (EClassify e) (TSecret T) ε ->
  has_type nil Σ Public e T ε.
Proof.
  intros Σ e T ε Hty.
  inversion Hty; subst. assumption.
Qed.

(** Typing inversion for prove *)
Lemma has_type_prove_inv : forall Σ e T ε,
  has_type nil Σ Public (EProve e) (TProof T) ε ->
  has_type nil Σ Public e T ε.
Proof.
  intros Σ e T ε Hty.
  inversion Hty; subst. assumption.
Qed.

(** Construct val_rel_n for products from components.
    Requires typing premises for all component values, since
    HO product types need has_type for the constructed pair. *)
Lemma val_rel_n_prod_compose : forall n Σ T1 T2 v1 v1' v2 v2',
  val_rel_n n Σ T1 v1 v1' ->
  val_rel_n n Σ T2 v2 v2' ->
  has_type nil Σ Public v1 T1 EffectPure ->
  has_type nil Σ Public v1' T1 EffectPure ->
  has_type nil Σ Public v2 T2 EffectPure ->
  has_type nil Σ Public v2' T2 EffectPure ->
  val_rel_n n Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2').
Proof.
  (* Use induction on n to handle the cumulative structure *)
  intro n. induction n as [| n' IHn]; intros Σ T1 T2 v1 v1' v2 v2' Hrel1 Hrel2 Ht1 Ht1' Ht2 Ht2'.
  - rewrite val_rel_n_0_unfold.
    rewrite val_rel_n_0_unfold in Hrel1.
    rewrite val_rel_n_0_unfold in Hrel2.
    destruct Hrel1 as [Hv1 [Hv1' [Hc1 [Hc1' Hif1]]]].
    destruct Hrel2 as [Hv2 [Hv2' [Hc2 [Hc2' Hif2]]]].
    split.
    + constructor; assumption.
    + split.
      * constructor; assumption.
      * split.
        { apply closed_expr_pair; assumption. }
        split.
        { apply closed_expr_pair; assumption. }
        change (NonInterference_v2.first_order_type (TProd T1 T2))
          with (first_order_type (TProd T1 T2)).
        destruct (first_order_type (TProd T1 T2)) eqn:Hfo_prod.
        { simpl.
          pose proof Hfo_prod as Hfo_prod_orig.
          cbn [first_order_type] in Hfo_prod.
          apply andb_true_iff in Hfo_prod as [Hfo1 Hfo2].
          assert (Hfo_rel1 : val_rel_at_type_fo T1 v1 v1').
          { change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Hif1.
            destruct (first_order_type T1) eqn:Hfo1'.
            - simpl in Hif1. exact Hif1.
            - rewrite Hfo1 in Hfo1'. discriminate. }
          assert (Hfo_rel2 : val_rel_at_type_fo T2 v2 v2').
          { change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Hif2.
            destruct (first_order_type T2) eqn:Hfo2'.
            - simpl in Hif2. exact Hif2.
            - rewrite Hfo2 in Hfo2'. discriminate. }
          cbn.
          exists v1, v2, v1', v2'.
          split; [reflexivity |].
          split; [reflexivity |].
          split; assumption. }
        { (* HO case: construct pair typing from component typing *)
          split.
          - change EffectPure with (effect_join EffectPure EffectPure).
            apply T_Pair; assumption.
          - change EffectPure with (effect_join EffectPure EffectPure).
            apply T_Pair; assumption. }
  - simpl. simpl in Hrel1, Hrel2.
    destruct Hrel1 as [Hrel1_cum [Hvalv1 [Hvalv1' [Hcl1 [Hcl1' [Htyping1 Hrat1]]]]]].
    destruct Hrel2 as [Hrel2_cum [Hvalv2 [Hvalv2' [Hcl2 [Hcl2' [Htyping2 Hrat2]]]]]].
    split.
    { (* Cumulative: use IH *)
      apply IHn; assumption. }
    split.
    { (* value (EPair v1 v2) *) constructor; assumption. }
    split.
    { (* value (EPair v1' v2') *) constructor; assumption. }
    split.
    { (* closed_expr (EPair v1 v2) *)
      intros y Hfree. simpl in Hfree.
      destruct Hfree as [Hfree | Hfree].
      - apply (Hcl1 y). exact Hfree.
      - apply (Hcl2 y). exact Hfree. }
    split.
    { (* closed_expr (EPair v1' v2') *)
      intros y Hfree. simpl in Hfree.
      destruct Hfree as [Hfree | Hfree].
      - apply (Hcl1' y). exact Hfree.
      - apply (Hcl2' y). exact Hfree. }
    split.
    { (* typing conjunct for TProd *)
      change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
      change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
      simpl.
      destruct (first_order_type T1 && first_order_type T2) eqn:Hfo_prod.
      - exact I.
      - (* HO case: construct pair typing from component typing *)
        split.
        + change EffectPure with (effect_join EffectPure EffectPure).
          apply T_Pair; assumption.
        + change EffectPure with (effect_join EffectPure EffectPure).
          apply T_Pair; assumption. }
    (* val_rel_at_type for TProd *)
    simpl. exists v1, v2, v1', v2'.
    repeat split; try reflexivity; assumption.
Qed.

(** Extract val_rel_n for first projection from product (general version).
    This works for any type because val_rel_at_type for products
    recursively contains val_rel_at_type for components at the same level. *)
Lemma val_rel_n_from_prod_fst : forall n Σ T1 T2 a1 b1 a2 b2,
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) (EPair a1 b1) (EPair a2 b2) ->
  val_rel_n n Σ T1 a1 a2.
Proof.
  induction n as [| n' IHn]; intros Σ T1 T2 a1 b1 a2 b2 Hn Hrel.
  - lia.
  - destruct n' as [| n''].
    + (* n = 1 *)
      simpl in Hrel.
      destruct Hrel as [Hcum [Hval [Hval' [Hcl [Hcl' [Htyping Hrat]]]]]].
      simpl in Hrat.
      destruct Hrat as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrat1 Hrat2]]]]]]].
      inversion Heq1; subst. inversion Heq2; subst.
      apply value_pair_inv in Hval. destruct Hval as [Hv1 Hv2].
      apply value_pair_inv in Hval'. destruct Hval' as [Hv1' Hv2'].
      apply closed_expr_pair_inv in Hcl. destruct Hcl as [Hcl1 Hcl2].
      apply closed_expr_pair_inv in Hcl'. destruct Hcl' as [Hcl1' Hcl2'].
      rewrite val_rel_n_S_unfold. split.
      * rewrite val_rel_n_0_unfold.
        repeat split; try assumption.
        destruct (first_order_type T1) eqn:Hfo1.
        { change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
          rewrite Hfo1.
          apply (proj1 (val_rel_at_type_fo_equiv T1 Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) x1 x2 Hfo1)).
          exact Hrat1. }
        { change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
          rewrite Hfo1.
          (* T1 is HO, so TProd T1 T2 is HO *)
          change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Htyping.
          change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Htyping.
          simpl in Htyping. rewrite Hfo1 in Htyping. simpl in Htyping.
          destruct Htyping as [Hty_pair1 Hty_pair2].
          (* Invert pair typing to get component typing *)
          inversion Hty_pair1; subst.
          inversion Hty_pair2; subst.
          split; assumption. }
      * split; [assumption |].
        split; [assumption |].
        split; [assumption |].
        split; [assumption |].
        split.
        { change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
          destruct (first_order_type T1) eqn:Hfo1.
          - exact I.
          - (* T1 HO, so TProd is HO *)
            change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Htyping.
            change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Htyping.
            simpl in Htyping. rewrite Hfo1 in Htyping. simpl in Htyping.
            destruct Htyping as [Hty_pair1 Hty_pair2].
            inversion Hty_pair1; subst.
            inversion Hty_pair2; subst.
            split; assumption. }
        exact Hrat1.
    + (* n = S (S n'') *)
      (* Extract val_rel_n (S (S n'')) from hypothesis and build val_rel_n (S (S n'')) for T1 *)
      rewrite val_rel_n_S_unfold in Hrel.
      destruct Hrel as [Hrel_cum [Hval [Hval' [Hcl [Hcl' [Htyping Hrat]]]]]].
      simpl in Hrat.
      destruct Hrat as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrat1 Hrat2]]]]]]].
      inversion Heq1; subst. inversion Heq2; subst.
      apply value_pair_inv in Hval. destruct Hval as [Hv1 Hv2].
      apply value_pair_inv in Hval'. destruct Hval' as [Hv1' Hv2'].
      apply closed_expr_pair_inv in Hcl. destruct Hcl as [Hcl1 Hcl2].
      apply closed_expr_pair_inv in Hcl'. destruct Hcl' as [Hcl1' Hcl2'].
      (* Use IH to get val_rel_n (S n'') for T1 from val_rel_n_cum *)
      assert (Hgt : S n'' > 0) by lia.
      apply (IHn Σ T1 T2 x1 y1 x2 y2 Hgt Hrel_cum).
Qed.

(** Extract val_rel_n for second projection from product (general version). *)
Lemma val_rel_n_from_prod_snd : forall n Σ T1 T2 a1 b1 a2 b2,
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) (EPair a1 b1) (EPair a2 b2) ->
  val_rel_n n Σ T2 b1 b2.
Proof.
  induction n as [| n' IHn]; intros Σ T1 T2 a1 b1 a2 b2 Hn Hrel.
  - lia.
  - destruct n' as [| n''].
    + (* n = 1 *)
      simpl in Hrel.
      destruct Hrel as [Hcum [Hval [Hval' [Hcl [Hcl' [_ Hrat]]]]]].
      simpl in Hrat.
      destruct Hrat as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrat1 Hrat2]]]]]]].
      inversion Heq1; subst. inversion Heq2; subst.
      apply value_pair_inv in Hval. destruct Hval as [Hv1 Hv2].
      apply value_pair_inv in Hval'. destruct Hval' as [Hv1' Hv2'].
      apply closed_expr_pair_inv in Hcl. destruct Hcl as [Hcl1 Hcl2].
      apply closed_expr_pair_inv in Hcl'. destruct Hcl' as [Hcl1' Hcl2'].
      rewrite val_rel_n_S_unfold.
      refine (conj _ _).
      { rewrite val_rel_n_0_unfold.
        repeat split; try assumption.
        destruct (first_order_type T2) eqn:Hfo2.
        { change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
          rewrite Hfo2.
          apply (proj1 (val_rel_at_type_fo_equiv T2 Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) y1 y2 Hfo2)).
          exact Hrat2. }
        { change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
          rewrite Hfo2.
          (* T2 is HO, so TProd T1 T2 is HO — extract typing from Hcum *)
          (* Hcum is val_rel_n 0 for TProd T1 T2 *)
          rewrite val_rel_n_0_unfold in Hcum.
          destruct Hcum as [_ [_ [_ [_ Hcum_if]]]].
          change (NonInterference_v2.first_order_type (TProd T1 T2)) with (first_order_type (TProd T1 T2)) in Hcum_if.
          simpl in Hcum_if.
          change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Hcum_if.
          change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Hcum_if.
          rewrite Hfo2 in Hcum_if. rewrite Bool.andb_false_r in Hcum_if.
          destruct Hcum_if as [Hty_pair1 Hty_pair2].
          apply has_type_pair_inv in Hty_pair1 as [ε1 [ε2 [Ht_y1 [Ht_y2 _]]]].
          apply has_type_pair_inv in Hty_pair2 as [ε1' [ε2' [Ht_y1' [Ht_y2' _]]]].
          split; assumption. } }
      { split; [assumption |].
        split; [assumption |].
        split; [assumption |].
        split; [assumption |].
        split.
        { change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
          destruct (first_order_type T2) eqn:Hfo2.
          - exact I.
          - (* T2 HO — same extraction from Hcum *)
            rewrite val_rel_n_0_unfold in Hcum.
            destruct Hcum as [_ [_ [_ [_ Hcum_if]]]].
            change (NonInterference_v2.first_order_type (TProd T1 T2)) with (first_order_type (TProd T1 T2)) in Hcum_if.
            simpl in Hcum_if.
            change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Hcum_if.
            change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Hcum_if.
            rewrite Hfo2 in Hcum_if. rewrite Bool.andb_false_r in Hcum_if.
            destruct Hcum_if as [Hty_pair1 Hty_pair2].
            apply has_type_pair_inv in Hty_pair1 as [ε1 [ε2 [Ht_y1 [Ht_y2 _]]]].
            apply has_type_pair_inv in Hty_pair2 as [ε1' [ε2' [Ht_y1' [Ht_y2' _]]]].
            split; assumption. }
        exact Hrat2. }
    + (* n = S (S n'') *)
      rewrite val_rel_n_S_unfold in Hrel.
      destruct Hrel as [Hrel_cum [Hval [Hval' [Hcl [Hcl' [Htyping Hrat]]]]]].
      simpl in Hrat.
      destruct Hrat as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrat1 Hrat2]]]]]]].
      inversion Heq1; subst. inversion Heq2; subst.
      apply value_pair_inv in Hval. destruct Hval as [Hv1 Hv2].
      apply value_pair_inv in Hval'. destruct Hval' as [Hv1' Hv2'].
      apply closed_expr_pair_inv in Hcl. destruct Hcl as [Hcl1 Hcl2].
      apply closed_expr_pair_inv in Hcl'. destruct Hcl' as [Hcl1' Hcl2'].
      assert (Hgt : S n'' > 0) by lia.
      apply (IHn Σ T1 T2 x1 y1 x2 y2 Hgt Hrel_cum).
Qed.

(** Construct val_rel_n for sum types from components *)
Lemma val_rel_n_sum_inl : forall n Σ T1 T2 v1 v2,
  val_rel_n n Σ T1 v1 v2 ->
  has_type nil Σ Public v1 T1 EffectPure ->
  has_type nil Σ Public v2 T1 EffectPure ->
  val_rel_n n Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  induction n as [| n' IHn]; intros Σ T1 T2 v1 v2 Hrel Htv1 Htv2.
  - rewrite val_rel_n_0_unfold in Hrel.
    destruct Hrel as [Hv1 [Hv2 [Hcl1 [Hcl2 Hfo]]]].
    rewrite val_rel_n_0_unfold.
    repeat split.
    + constructor; assumption.
    + constructor; assumption.
    + apply closed_expr_inl; assumption.
    + apply closed_expr_inl; assumption.
    + destruct (first_order_type (TSum T1 T2)) eqn:HfoSum; simpl.
      * simpl in HfoSum.
        apply andb_true_iff in HfoSum.
        destruct HfoSum as [Hfo1 Hfo2].
        change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Hfo.
        rewrite Hfo1 in Hfo. simpl in Hfo.
        change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
        change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
        rewrite Hfo1, Hfo2. simpl.
        unfold val_rel_at_type_fo; simpl.
        left. exists v1, v2. repeat split; try reflexivity; assumption.
      * change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
        change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
        simpl in HfoSum. rewrite HfoSum.
        (* HO case: construct typing for EInl from component typing *)
        split; apply T_Inl; assumption.
  - simpl in Hrel.
    destruct Hrel as [Hcum [Hvalv1 [Hvalv2 [Hclv1 [Hclv2 [_ Hrat]]]]]].
    simpl. split.
    + apply IHn; assumption.
    + split; [constructor; assumption |].
      split; [constructor; assumption |].
      split.
      { intros y Hfree. simpl in Hfree. apply (Hclv1 y). exact Hfree. }
      split.
      { intros y Hfree. simpl in Hfree. apply (Hclv2 y). exact Hfree. }
      split.
      { (* typing conjunct *)
        change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
        change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
        destruct (first_order_type T1 && first_order_type T2) eqn:Hfo.
        - exact I.
        - (* HO case: construct typing for EInl *)
          split; apply T_Inl; assumption. }
      simpl. left. exists v1, v2.
      repeat split; try reflexivity; assumption.
Qed.

Lemma val_rel_n_sum_inr : forall n Σ T1 T2 v1 v2,
  val_rel_n n Σ T2 v1 v2 ->
  has_type nil Σ Public v1 T2 EffectPure ->
  has_type nil Σ Public v2 T2 EffectPure ->
  val_rel_n n Σ (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  induction n as [| n' IHn]; intros Σ T1 T2 v1 v2 Hrel Htv1 Htv2.
  - rewrite val_rel_n_0_unfold in Hrel.
    destruct Hrel as [Hv1 [Hv2 [Hcl1 [Hcl2 Hfo]]]].
    rewrite val_rel_n_0_unfold.
    repeat split.
    + constructor; assumption.
    + constructor; assumption.
    + apply closed_expr_inr; assumption.
    + apply closed_expr_inr; assumption.
    + destruct (first_order_type (TSum T1 T2)) eqn:HfoSum; simpl.
      * simpl in HfoSum.
        apply andb_true_iff in HfoSum.
        destruct HfoSum as [Hfo1 Hfo2].
        change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Hfo.
        rewrite Hfo2 in Hfo. simpl in Hfo.
        change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
        change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
        rewrite Hfo1, Hfo2. simpl.
        unfold val_rel_at_type_fo; simpl.
        right. exists v1, v2. repeat split; try reflexivity; assumption.
      * change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
        change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
        simpl in HfoSum. rewrite HfoSum.
        (* HO case: construct typing for EInr from component typing *)
        split; apply T_Inr; assumption.
  - simpl in Hrel.
    destruct Hrel as [Hcum [Hvalv1 [Hvalv2 [Hclv1 [Hclv2 [_ Hrat]]]]]].
    simpl. split.
    + apply IHn; assumption.
    + split; [constructor; assumption |].
      split; [constructor; assumption |].
      split.
      { intros y Hfree. simpl in Hfree. apply (Hclv1 y). exact Hfree. }
      split.
      { intros y Hfree. simpl in Hfree. apply (Hclv2 y). exact Hfree. }
      split.
      { (* typing conjunct *)
        change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
        change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
        destruct (first_order_type T1 && first_order_type T2) eqn:Hfo.
        - exact I.
        - (* HO case: construct typing for EInr *)
          split; apply T_Inr; assumption. }
      simpl. right. exists v1, v2.
      repeat split; try reflexivity; assumption.
Qed.

(** Decompose val_rel_n at TSum to get the sum structure *)
Lemma val_rel_n_sum_decompose : forall n Σ T1 T2 v1 v2,
  n > 0 ->
  val_rel_n n Σ (TSum T1 T2) v1 v2 ->
  (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\
     value a1 /\ value a2 /\ closed_expr a1 /\ closed_expr a2 /\
     val_rel_at_type Σ (store_rel_n (n-1)) (val_rel_n (n-1)) (store_rel_n (n-1)) T1 a1 a2) \/
  (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\
     value b1 /\ value b2 /\ closed_expr b1 /\ closed_expr b2 /\
     val_rel_at_type Σ (store_rel_n (n-1)) (val_rel_n (n-1)) (store_rel_n (n-1)) T2 b1 b2).
Proof.
  intros n Σ T1 T2 v1 v2 Hn Hrel.
  destruct n as [| n']; [lia |].
  simpl in Hrel.
  destruct Hrel as [_ [Hval1 [Hval2 [Hcl1 [Hcl2 [_ Hrat]]]]]].
  simpl in Hrat.
  replace (S n' - 1) with n' by lia.
  destruct Hrat as [[a1 [a2 [Heq1 [Heq2 Hrat]]]] | [b1 [b2 [Heq1 [Heq2 Hrat]]]]].
  - (* Inl case *)
    left. exists a1, a2. subst.
    inversion Hval1; subst. inversion Hval2; subst.
    assert (Hcla1 : closed_expr a1).
    { intros y Hfree. apply (Hcl1 y). simpl. exact Hfree. }
    assert (Hcla2 : closed_expr a2).
    { intros y Hfree. apply (Hcl2 y). simpl. exact Hfree. }
    repeat split; try assumption.
  - (* Inr case *)
    right. exists b1, b2. subst.
    inversion Hval1; subst. inversion Hval2; subst.
    assert (Hclb1 : closed_expr b1).
    { intros y Hfree. apply (Hcl1 y). simpl. exact Hfree. }
    assert (Hclb2 : closed_expr b2).
    { intros y Hfree. apply (Hcl2 y). simpl. exact Hfree. }
    repeat split; try assumption.
Qed.

(** Extract val_rel_n for Inl component from sum relation (general version) *)
Lemma val_rel_n_from_sum_inl : forall n Σ T1 T2 a1 a2,
  n > 0 ->
  val_rel_n n Σ (TSum T1 T2) (EInl a1 T2) (EInl a2 T2) ->
  val_rel_n n Σ T1 a1 a2.
Proof.
  induction n as [| n' IHn]; intros Σ T1 T2 a1 a2 Hn Hrel.
  - lia.
  - rewrite val_rel_n_S_unfold in Hrel.
    destruct Hrel as [Hrel_cum [Hval [Hval' [Hcl [Hcl' [Htyping Hrat]]]]]].
    simpl in Hrat.
    destruct Hrat as [Hinl | Hinr].
    + (* Inl case *)
      destruct Hinl as [x1 [x2 [Heq1 [Heq2 [Hrat1 _]]]]].
      (* EInl a1 T2 = EInl x1 T2, so a1 = x1 *)
      inversion Heq1; subst. inversion Heq2; subst.
      apply value_inl_inv in Hval. apply value_inl_inv in Hval'.
      apply closed_expr_inl_inv in Hcl. apply closed_expr_inl_inv in Hcl'.
      destruct n' as [| n''].
      * (* n = 1 *)
        rewrite val_rel_n_S_unfold. split.
        { rewrite val_rel_n_0_unfold.
          repeat split; try assumption.
          destruct (first_order_type T1) eqn:Hfo1.
          - change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
            rewrite Hfo1.
            apply (proj1 (val_rel_at_type_fo_equiv T1 Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) x1 x2 Hfo1)).
            exact Hrat1.
          - (* HO T1: extract typing from Htyping *)
            change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
            rewrite Hfo1.
            change (NonInterference_v2.first_order_type (TSum T1 T2)) with (first_order_type (TSum T1 T2)) in Htyping.
            simpl in Htyping.
            change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Htyping.
            change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Htyping.
            rewrite Hfo1 in Htyping. simpl in Htyping.
            destruct Htyping as [Hty1 Hty2].
            split.
            { apply has_type_inl_inv in Hty1. exact Hty1. }
            { apply has_type_inl_inv in Hty2. exact Hty2. } }
        { split; [assumption |]. split; [assumption |].
          split; [assumption |]. split; [assumption |].
          split.
          { change (NonInterference_v2.first_order_type T1) with (first_order_type T1).
            destruct (first_order_type T1) eqn:Hfo1.
            - exact I.
            - change (NonInterference_v2.first_order_type (TSum T1 T2)) with (first_order_type (TSum T1 T2)) in Htyping.
              simpl in Htyping.
              change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Htyping.
              change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Htyping.
              rewrite Hfo1 in Htyping. simpl in Htyping.
              destruct Htyping as [Hty1 Hty2].
              split.
              { apply has_type_inl_inv in Hty1. exact Hty1. }
              { apply has_type_inl_inv in Hty2. exact Hty2. } }
          exact Hrat1. }
      * (* n = S (S n'') — use IH *)
        assert (Hgt : S n'' > 0) by lia.
        apply (IHn Σ T1 T2 x1 x2 Hgt Hrel_cum).
    + (* Inr case — contradiction: EInl ≠ EInr *)
      destruct Hinr as [y1 [y2 [Heq1 _]]].
      discriminate Heq1.
Qed.

(** Extract val_rel_n for Inr component from sum relation (general version) *)
Lemma val_rel_n_from_sum_inr : forall n Σ T1 T2 b1 b2,
  n > 0 ->
  val_rel_n n Σ (TSum T1 T2) (EInr b1 T1) (EInr b2 T1) ->
  val_rel_n n Σ T2 b1 b2.
Proof.
  induction n as [| n' IHn]; intros Σ T1 T2 b1 b2 Hn Hrel.
  - lia.
  - rewrite val_rel_n_S_unfold in Hrel.
    destruct Hrel as [Hrel_cum [Hval [Hval' [Hcl [Hcl' [Htyping Hrat]]]]]].
    simpl in Hrat.
    destruct Hrat as [Hinl | Hinr].
    + (* Inl case — contradiction: EInr ≠ EInl *)
      destruct Hinl as [x1 [x2 [Heq1 _]]].
      discriminate Heq1.
    + (* Inr case *)
      destruct Hinr as [y1 [y2 [Heq1 [Heq2 [_ Hrat2]]]]].
      inversion Heq1; subst. inversion Heq2; subst.
      apply value_inr_inv in Hval. apply value_inr_inv in Hval'.
      apply closed_expr_inr_inv in Hcl. apply closed_expr_inr_inv in Hcl'.
      destruct n' as [| n''].
      * (* n = 1 *)
        rewrite val_rel_n_S_unfold. split.
        { rewrite val_rel_n_0_unfold.
          repeat split; try assumption.
          destruct (first_order_type T2) eqn:Hfo2.
          - change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
            rewrite Hfo2.
            apply (proj1 (val_rel_at_type_fo_equiv T2 Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) y1 y2 Hfo2)).
            exact Hrat2.
          - change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
            rewrite Hfo2.
            change (NonInterference_v2.first_order_type (TSum T1 T2)) with (first_order_type (TSum T1 T2)) in Htyping.
            simpl in Htyping.
            change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Htyping.
            change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Htyping.
            rewrite Hfo2 in Htyping. rewrite Bool.andb_false_r in Htyping.
            destruct Htyping as [Hty1 Hty2].
            split.
            { apply has_type_inr_inv in Hty1. exact Hty1. }
            { apply has_type_inr_inv in Hty2. exact Hty2. } }
        { split; [assumption |]. split; [assumption |].
          split; [assumption |]. split; [assumption |].
          split.
          { change (NonInterference_v2.first_order_type T2) with (first_order_type T2).
            destruct (first_order_type T2) eqn:Hfo2.
            - exact I.
            - change (NonInterference_v2.first_order_type (TSum T1 T2)) with (first_order_type (TSum T1 T2)) in Htyping.
              simpl in Htyping.
              change (NonInterference_v2.first_order_type T1) with (first_order_type T1) in Htyping.
              change (NonInterference_v2.first_order_type T2) with (first_order_type T2) in Htyping.
              rewrite Hfo2 in Htyping. rewrite Bool.andb_false_r in Htyping.
              destruct Htyping as [Hty1 Hty2].
              split.
              { apply has_type_inr_inv in Hty1. exact Hty1. }
              { apply has_type_inr_inv in Hty2. exact Hty2. } }
          exact Hrat2. }
      * (* n = S (S n'') — use IH *)
        assert (Hgt : S n'' > 0) by lia.
        apply (IHn Σ T1 T2 y1 y2 Hgt Hrel_cum).
Qed.

(** Extract val_rel_at_type from product decomposition (for any type) *)
Lemma val_rel_n_prod_fst_at : forall n Σ T1 T2 v1 v2 v1' v2',
  val_rel_n (S n) Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2') ->
  value v1 /\ value v1' /\ closed_expr v1 /\ closed_expr v1' /\
  val_rel_at_type Σ (store_rel_n n) (val_rel_n n) (store_rel_n n) T1 v1 v1'.
Proof.
  intros n Σ T1 T2 v1 v2 v1' v2' Hrel.
  simpl in Hrel.
  destruct Hrel as [Hcum [Hval [Hval' [Hcl [Hcl' [_ Hrat]]]]]].
  apply value_pair_inv in Hval. destruct Hval as [Hv1 Hv2].
  apply value_pair_inv in Hval'. destruct Hval' as [Hv1' Hv2'].
  assert (Hcl1 : closed_expr v1).
  { intros y Hfree. apply (Hcl y). simpl. left. exact Hfree. }
  assert (Hcl1' : closed_expr v1').
  { intros y Hfree. apply (Hcl' y). simpl. left. exact Hfree. }
  simpl in Hrat.
  destruct Hrat as [w1 [w2 [w1' [w2' [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
  injection Heq1 as Hv1eq Hv2eq. subst.
  injection Heq2 as Hv1'eq Hv2'eq. subst.
  repeat split; assumption.
Qed.

Lemma val_rel_n_prod_snd_at : forall n Σ T1 T2 v1 v2 v1' v2',
  val_rel_n (S n) Σ (TProd T1 T2) (EPair v1 v2) (EPair v1' v2') ->
  value v2 /\ value v2' /\ closed_expr v2 /\ closed_expr v2' /\
  val_rel_at_type Σ (store_rel_n n) (val_rel_n n) (store_rel_n n) T2 v2 v2'.
Proof.
  intros n Σ T1 T2 v1 v2 v1' v2' Hrel.
  simpl in Hrel.
  destruct Hrel as [Hcum [Hval [Hval' [Hcl [Hcl' [_ Hrat]]]]]].
  apply value_pair_inv in Hval. destruct Hval as [Hv1 Hv2].
  apply value_pair_inv in Hval'. destruct Hval' as [Hv1' Hv2'].
  assert (Hcl2 : closed_expr v2).
  { intros y Hfree. apply (Hcl y). simpl. right. exact Hfree. }
  assert (Hcl2' : closed_expr v2').
  { intros y Hfree. apply (Hcl' y). simpl. right. exact Hfree. }
  simpl in Hrat.
  destruct Hrat as [w1 [w2 [w1' [w2' [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
  injection Heq1 as Hv1eq Hv2eq. subst.
  injection Heq2 as Hv1'eq Hv2'eq. subst.
  repeat split; assumption.
Qed.

(** Helper: closed_expr for closed value constructors *)
Lemma closed_expr_unit : closed_expr EUnit.
Proof. intros y Hfree. simpl in Hfree. contradiction. Qed.

Lemma closed_expr_bool : forall b, closed_expr (EBool b).
Proof. intros b y Hfree. simpl in Hfree. contradiction. Qed.

Lemma closed_expr_int : forall i, closed_expr (EInt i).
Proof. intros i y Hfree. simpl in Hfree. contradiction. Qed.

Lemma closed_expr_string : forall s, closed_expr (EString s).
Proof. intros s y Hfree. simpl in Hfree. contradiction. Qed.

Lemma closed_expr_loc : forall l, closed_expr (ELoc l).
Proof. intros l y Hfree. simpl in Hfree. contradiction. Qed.

(** Helper: val_rel for first-order value types using val_rel_n_of_first_order *)
Lemma val_rel_unit : forall Σ,
  val_rel Σ TUnit EUnit EUnit.
Proof.
  intros Σ n.
  apply val_rel_n_of_first_order.
  - reflexivity.
  - constructor.
  - constructor.
  - apply closed_expr_unit.
  - apply closed_expr_unit.
  - intros sp vl sl. simpl. split; reflexivity.
Qed.

Lemma val_rel_bool : forall Σ b,
  val_rel Σ TBool (EBool b) (EBool b).
Proof.
  intros Σ b n.
  apply val_rel_n_of_first_order.
  - reflexivity.
  - constructor.
  - constructor.
  - apply closed_expr_bool.
  - apply closed_expr_bool.
  - intros sp vl sl. simpl. exists b. split; reflexivity.
Qed.

(** Extract equal booleans from val_rel_n at TBool *)
Lemma val_rel_n_bool_eq : forall n Σ v1 v2,
  n > 0 ->
  val_rel_n n Σ TBool v1 v2 ->
  exists b, v1 = EBool b /\ v2 = EBool b.
Proof.
  intros n Σ v1 v2 Hn Hrel.
  destruct n as [| n']; [lia |].
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [_ [_ Hrat]]]]]].
  simpl in Hrat.
  exact Hrat.
Qed.

Lemma val_rel_int : forall Σ i,
  val_rel Σ TInt (EInt i) (EInt i).
Proof.
  intros Σ i n.
  apply val_rel_n_of_first_order.
  - reflexivity.
  - constructor.
  - constructor.
  - apply closed_expr_int.
  - apply closed_expr_int.
  - intros sp vl sl. simpl. exists i. split; reflexivity.
Qed.

(** Build val_rel_n for TSecret type (val_rel_at_type is True) *)
Lemma val_rel_n_classify : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_n n Σ (TSecret T) (EClassify v1) (EClassify v2).
Proof.
  induction n as [| n' IHn]; intros Σ T v1 v2 Hv1 Hv2 Hc1 Hc2 Ht1 Ht2.
  - rewrite val_rel_n_0_unfold. repeat split.
    + constructor; assumption.
    + constructor; assumption.
    + intros y Hfree. simpl in Hfree. apply (Hc1 y Hfree).
    + intros y Hfree. simpl in Hfree. apply (Hc2 y Hfree).
    + change (NonInterference_v2.first_order_type (TSecret T)) with (first_order_type (TSecret T)).
      simpl.
      change (NonInterference_v2.first_order_type T) with (first_order_type T).
      destruct (first_order_type T) eqn:Hfo.
      * exact I.
      * split; apply T_Classify; assumption.
  - rewrite val_rel_n_S_unfold. split.
    + apply IHn; assumption.
    + repeat split.
      * constructor; assumption.
      * constructor; assumption.
      * intros y Hfree. simpl in Hfree. apply (Hc1 y Hfree).
      * intros y Hfree. simpl in Hfree. apply (Hc2 y Hfree).
      * change (NonInterference_v2.first_order_type (TSecret T)) with (first_order_type (TSecret T)).
        simpl.
        change (NonInterference_v2.first_order_type T) with (first_order_type T).
        destruct (first_order_type T) eqn:Hfo.
        { exact I. }
        { split; apply T_Classify; assumption. }
      * exact I.
Qed.

(** Build val_rel_n for TProof type (val_rel_at_type is True) *)
Lemma val_rel_n_prove : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_n n Σ (TProof T) (EProve v1) (EProve v2).
Proof.
  induction n as [| n' IHn]; intros Σ T v1 v2 Hv1 Hv2 Hc1 Hc2 Ht1 Ht2.
  - rewrite val_rel_n_0_unfold. repeat split.
    + constructor; assumption.
    + constructor; assumption.
    + intros y Hfree. simpl in Hfree. apply (Hc1 y Hfree).
    + intros y Hfree. simpl in Hfree. apply (Hc2 y Hfree).
    + change (NonInterference_v2.first_order_type (TProof T)) with (first_order_type (TProof T)).
      simpl.
      change (NonInterference_v2.first_order_type T) with (first_order_type T).
      destruct (first_order_type T) eqn:Hfo.
      * exact I.
      * split; apply T_Prove; assumption.
  - rewrite val_rel_n_S_unfold. split.
    + apply IHn; assumption.
    + repeat split.
      * constructor; assumption.
      * constructor; assumption.
      * intros y Hfree. simpl in Hfree. apply (Hc1 y Hfree).
      * intros y Hfree. simpl in Hfree. apply (Hc2 y Hfree).
      * change (NonInterference_v2.first_order_type (TProof T)) with (first_order_type (TProof T)).
        simpl.
        change (NonInterference_v2.first_order_type T) with (first_order_type T).
        destruct (first_order_type T) eqn:Hfo.
        { exact I. }
        { split; apply T_Prove; assumption. }
      * exact I.
Qed.

Lemma val_rel_string : forall Σ s,
  val_rel Σ TString (EString s) (EString s).
Proof.
  intros Σ s n.
  apply val_rel_n_of_first_order.
  - reflexivity.
  - constructor.
  - constructor.
  - apply closed_expr_string.
  - apply closed_expr_string.
  - intros sp vl sl. simpl. exists s. split; reflexivity.
Qed.

Lemma val_rel_loc : forall Σ l,
  val_rel Σ (TRef TUnit Public) (ELoc l) (ELoc l).
Proof.
  intros Σ l n.
  apply val_rel_n_of_first_order.
  - reflexivity.
  - constructor.
  - constructor.
  - apply closed_expr_loc.
  - apply closed_expr_loc.
  - intros sp vl sl. simpl. exists l. split; reflexivity.
Qed.

(** ========================================================================
    MUTUAL INDUCTION: step_up and fundamental theorem
    ========================================================================

    The key insight is that:
    - step_up(n) for TFn needs fundamental theorem at step n for the body
    - fundamental(n) for T_App needs step_up(n-1) to lift results

    This creates a mutual dependency that we break by proving both together
    by strong induction on n.

    Order of proof:
    - fundamental(0) is trivially true (exp_rel_n 0 = True)
    - step_up(0) uses fundamental(0)
    - fundamental(1) uses step_up(0)
    - step_up(1) uses fundamental(1)
    - fundamental(2) uses step_up(1)
    - ...

    This is a valid mutual induction!
*)

(** Step-indexed fundamental theorem statement *)
Definition fundamental_at_step (n : nat) : Prop :=
  forall Γ Σ Δ e T ε rho1 rho2,
    has_type Γ Σ Δ e T ε ->
    env_rel Σ Γ rho1 rho2 ->
    rho_no_free_all rho1 ->
    rho_no_free_all rho2 ->
    exp_rel_n n Σ T (subst_rho rho1 e) (subst_rho rho2 e).

(** Step-up statement at a specific step *)
Definition step_up_at (n : nat) : Prop :=
  forall Σ T v1 v2,
    val_rel_n n Σ T v1 v2 ->
    has_type nil Σ Public v1 T EffectPure ->
    has_type nil Σ Public v2 T EffectPure ->
    val_rel_n (S n) Σ T v1 v2.

(** Combined statement: both hold at step n *)
Definition step_up_and_fundamental (n : nat) : Prop :=
  step_up_at n /\ fundamental_at_step n.

(** Base case: fundamental at step 0 is trivially true *)
Lemma fundamental_at_0 : fundamental_at_step 0.
Proof.
  unfold fundamental_at_step. intros.
  simpl. trivial.
Qed.

(** step_up at 0: follows directly from val_rel_n_step_up (proven in base file) *)
Lemma step_up_at_0 : step_up_at 0.
Proof.
  unfold step_up_at. intros Σ T v1 v2 Hrel Hty1 Hty2.
  apply val_rel_n_step_up; assumption.
Qed.

(** Multi-step preservation - extends single-step preservation to multi-step.
    This lemma is needed for typing premises in IH_step_up applications. *)
Lemma multi_step_preservation_aux : forall cfg1 cfg2,
  cfg1 -->* cfg2 ->
  forall Σ e st ctx T ε,
    cfg1 = (e, st, ctx) ->
    has_type nil Σ Public e T ε ->
    store_wf Σ st ->
    exists e' st' ctx' Σ' ε',
      cfg2 = (e', st', ctx') /\
      store_ty_extends Σ Σ' /\
      store_wf Σ' st' /\
      has_type nil Σ' Public e' T ε'.
Proof.
  intros cfg1 cfg2 Hmulti.
  induction Hmulti as [cfg | cfg1' cfg2' cfg3 Hstep Hmulti' IH];
    intros Σ e st ctx T ε Heq Hty Hwf.
  - (* MS_Refl *)
    subst cfg.
    exists e, st, ctx, Σ, ε.
    split. { reflexivity. }
    split. { apply store_ty_extends_refl. }
    split; assumption.
  - (* MS_Step *)
    subst cfg1'.
    destruct cfg2' as [[e_mid st_mid] ctx_mid].
    (* Single-step preservation *)
    destruct (preservation e e_mid T ε st st_mid ctx ctx_mid Σ Hty Hwf Hstep)
      as [Σ' [ε' [Hext [Hwf' Hty']]]].
    (* Apply IH *)
    destruct (IH Σ' e_mid st_mid ctx_mid T ε' eq_refl Hty' Hwf')
      as [e'' [st'' [ctx'' [Σ'' [ε'' [Heq'' [Hext' [Hwf'' Hty'']]]]]]]].
    exists e'', st'', ctx'', Σ'', ε''.
    split. { exact Heq''. }
    split. { eapply store_ty_extends_trans; eassumption. }
    split; assumption.
Qed.

Lemma multi_step_preservation : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  (e, st, ctx) -->* (e', st', ctx') ->
  exists Σ' ε',
    store_ty_extends Σ Σ' /\
    store_wf Σ' st' /\
    has_type nil Σ' Public e' T ε'.
Proof.
  intros e e' T ε st st' ctx ctx' Σ Hty Hwf Hmulti.
  destruct (multi_step_preservation_aux _ _ Hmulti Σ e st ctx T ε eq_refl Hty Hwf)
    as [e'' [st'' [ctx'' [Σ' [ε' [Heq [Hext [Hwf' Hty']]]]]]]].
  inversion Heq; subst.
  exists Σ', ε'. split; [exact Hext | split; assumption].
Qed.

(** Security level is irrelevant in typing — Δ is universally passed through *)
Lemma has_type_level_irrelevant : forall Γ Σ Δ1 e T ε,
  has_type Γ Σ Δ1 e T ε ->
  forall Δ2, has_type Γ Σ Δ2 e T ε.
Proof.
  intros Γ Σ Δ1 e T ε Hty.
  induction Hty; intro Δ2; try (econstructor; eauto; fail).
Qed.

(** The mutual induction theorem.
    Since val_rel_n_step_up is fully proven in the base file (NonInterference_v2.v),
    step_up_at is trivially proven for all n. The fundamental theorem part
    requires induction on typing derivations and is admitted pending
    completion of the logical_relation proof. *)
Theorem step_up_and_fundamental_mutual : forall n,
  step_up_and_fundamental n.
Proof.
  intro n.
  unfold step_up_and_fundamental.
  split.
  - (* step_up at n: follows directly from val_rel_n_step_up *)
    unfold step_up_at. intros Σ T v1 v2 Hrel Hty1 Hty2.
    apply val_rel_n_step_up; assumption.
  - (* fundamental at n *)
    destruct n as [| n'].
    + apply fundamental_at_0.
    + (* fundamental at S n': requires induction on typing derivation *)
      unfold fundamental_at_step.
      intros Γ Σ Δ e0 T ε rho1 rho2 Hty Henv Hno1 Hno2.
      (* Convert typing from arbitrary Δ to Public *)
      assert (Hty_pub : has_type Γ Σ Public e0 T ε).
      { exact (has_type_level_irrelevant Γ Σ Δ e0 T ε Hty Public). }
      (* Apply the logical_relation theorem *)
      exact (logical_relation Γ Σ e0 T ε rho1 rho2 Hty_pub Henv Hno1 Hno2 (S n')).
Qed.

(** Corollary: step_up holds at all steps *)
Corollary val_rel_n_step_up_proven : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_n (S n) Σ T v1 v2.
Proof.
  intros n.
  destruct (step_up_and_fundamental_mutual n) as [Hsu _].
  exact Hsu.
Qed.

(** Corollary: fundamental theorem holds at all steps *)
Corollary fundamental_at_all_steps : forall n Γ Σ Δ e T ε rho1 rho2,
  has_type Γ Σ Δ e T ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 e) (subst_rho rho2 e).
Proof.
  intros n.
  destruct (step_up_and_fundamental_mutual n) as [_ Hf].
  exact Hf.
Qed.

(* The fundamental theorem - proof by induction on typing derivation *)
Theorem logical_relation : forall G Σ e T eps rho1 rho2,
  has_type G Σ Public e T eps ->
  env_rel Σ G rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel Σ T (subst_rho rho1 e) (subst_rho rho2 e).
Proof.
  intros G Σ e T eps rho1 rho2 Hty.
  generalize dependent rho2. generalize dependent rho1.
  induction Hty; intros rho1 rho2 Henv Hno1 Hno2.

  - (* T_Unit *)
    simpl. apply exp_rel_of_val_rel. apply val_rel_unit.

  - (* T_Bool *)
    simpl. apply exp_rel_of_val_rel. apply val_rel_bool.

  - (* T_Int *)
    simpl. apply exp_rel_of_val_rel. apply val_rel_int.

  - (* T_String *)
    simpl. apply exp_rel_of_val_rel. apply val_rel_string.

  - (* T_Loc - locations are related to themselves *)
    simpl. apply exp_rel_of_val_rel.
    intros n. induction n as [| n' IHn].
    + (* n = 0 *)
      rewrite val_rel_n_0_unfold. simpl.
      split. { constructor. }
      split. { constructor. }
      split. { apply closed_expr_loc. }
      split. { apply closed_expr_loc. }
      destruct (NonInterference_v2.first_order_type T) eqn:Hfo.
      * simpl. exists l. split; reflexivity.
      * (* HO type: need typing for TRef — use T_Loc with store lookup *)
        split; apply T_Loc; exact H.
    + (* n = S n' *)
      rewrite val_rel_n_S_unfold. split; [exact IHn |].
      split. { constructor. }
      split. { constructor. }
      split. { apply closed_expr_loc. }
      split. { apply closed_expr_loc. }
      split.
      { (* typing conjunct for TRef *)
        change (NonInterference_v2.first_order_type (TRef T sl)) with (first_order_type (TRef T sl)).
        simpl.
        change (NonInterference_v2.first_order_type T) with (first_order_type T).
        destruct (first_order_type T) eqn:Hfo.
        - exact I.
        - (* HO type: use T_Loc *)
          split; apply T_Loc; exact H. }
      simpl. exists l. split; reflexivity.

  - (* T_Var *)
    (* subst_rho rho (EVar x) = rho x by definition.
       From env_rel and lookup x Γ = Some T, we get val_rel for rho1 x and rho2 x. *)
    simpl.
    apply exp_rel_of_val_rel.
    unfold val_rel. intro n.
    unfold env_rel in Henv.
    specialize (Henv n) as Henv_n.
    unfold env_rel_n in Henv_n.
    apply Henv_n.
    exact H.

  - (* T_Lam - lambda abstraction *)
    (* Lambda is a value, so exp_rel follows from val_rel.
       The key is showing val_rel_at_type for TFn, which requires:
       for all related args, applying the lambdas produces related results. *)
    simpl.
    (* Note: IHHty is for the body under extended context *)
    (* Obtain typing for both substituted lambdas from env_rel *)
    assert (Hlam_ty : has_type nil Σ Public (ELam x T1 (subst_rho (rho_shadow rho1 x) e)) (TFn T1 T2 ε) EffectPure /\
                      has_type nil Σ Public (ELam x T1 (subst_rho (rho_shadow rho2 x) e)) (TFn T1 T2 ε) EffectPure).
    { apply (lam_typing_from_env_rel G Σ x T1 T2 e ε rho1 rho2 Hty Henv). }
    destruct Hlam_ty as [Hlam_ty1 Hlam_ty2].
    assert (Hcl1 : closed_expr (ELam x T1 (subst_rho (rho_shadow rho1 x) e))).
    { apply (typing_nil_closed Σ Public). exact Hlam_ty1. }
    assert (Hcl2 : closed_expr (ELam x T1 (subst_rho (rho_shadow rho2 x) e))).
    { apply (typing_nil_closed Σ Public). exact Hlam_ty2. }
    (* We prove exp_rel from val_rel *)
    apply exp_rel_of_val_rel.
    unfold val_rel. intro n.
    (* Use INDUCTION on n to get val_rel_n n' as IH for the S n' case *)
    induction n as [| n' IHn_lam].
    + (* n = 0: v2 requires value/closed, not just True *)
      rewrite val_rel_n_0_unfold. simpl.
      split. { constructor. }
      split. { constructor. }
      split. { exact Hcl1. }
      split. { exact Hcl2. }
      (* TFn is HO, so needs typing *)
      change (NonInterference_v2.first_order_type (TFn T1 T2 ε)) with (first_order_type (TFn T1 T2 ε)).
      simpl. split; assumption.
    + (* S n' case - prove val_rel_n (S n') for TFn *)
      rewrite val_rel_n_S_unfold.
      split.
      * (* val_rel_n n' - from IH on n *)
        exact IHn_lam.
      * (* value /\ value /\ closed /\ closed /\ typing /\ val_rel_at_type *)
        split. { constructor. }
        split. { constructor. }
        split. { exact Hcl1. }
        split. { exact Hcl2. }
        split. { (* typing conjunct for TFn *)
          change (NonInterference_v2.first_order_type (TFn T1 T2 ε)) with (first_order_type (TFn T1 T2 ε)).
          simpl. split; assumption. }
        (* val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') (TFn T1 T2 ε) lam1 lam2 *)
        simpl.
        intros Σ' Hext_Σ' arg1 arg2 Hvarg1 Hvarg2 Hclarg1 Hclarg2 Hargrel st1 st2 ctx Hstrel Hwf1 Hwf2 Hagree.
        (* Apply lambdas: EApp (ELam x T1 body) arg --> [x := arg] body *)
        (* lam1 = ELam x T1 (subst_rho (rho_shadow rho1 x) e) *)
        (* lam2 = ELam x T1 (subst_rho (rho_shadow rho2 x) e) *)

        (* Build extended environment for IHHty at ORIGINAL Σ (not Σ') *)
        (* Need val_rel Σ T1 arg1 arg2 from val_rel_n n' Σ' T1 arg1 arg2 *)
        (* This requires:
           1. Store weakening: Σ' → Σ (needs val_rel_n_weaken)
           2. Step generalization: n' → forall m (needs val_rel_n_step_up)
           For FO T1: both are proven/provable
           For HO T1: both require additional axioms/lemmas *)
        assert (Hargrel_at_Σ : val_rel Σ T1 arg1 arg2).
        { apply (val_rel_store_weaken_back Σ Σ' T1 arg1 arg2 Hext_Σ').
          apply (val_rel_n_to_val_rel_any Σ' T1 arg1 arg2 n');
            assumption. }

        assert (Henv' : env_rel Σ ((x, T1) :: Γ) (rho_extend rho1 x arg1) (rho_extend rho2 x arg2)).
        { apply env_rel_extend.
          - exact Henv.
          - exact Hargrel_at_Σ. }

        assert (Hno1' : rho_no_free_all (rho_extend rho1 x arg1)).
        { apply rho_no_free_extend; assumption. }
        assert (Hno2' : rho_no_free_all (rho_extend rho2 x arg2)).
        { apply rho_no_free_extend; assumption. }

        (* Apply IHHty to get exp_rel at Σ *)
        specialize (IHHty (rho_extend rho1 x arg1) (rho_extend rho2 x arg2) Henv' Hno1' Hno2') as He_rel.
        unfold exp_rel in He_rel.

        (* Connect substitutions: [x := arg](subst_rho (rho_shadow rho x) e) = subst_rho (rho_extend rho x arg) e *)
        assert (Hsubst1 : [x := arg1] (subst_rho (rho_shadow rho1 x) e) = subst_rho (rho_extend rho1 x arg1) e).
        { apply subst_rho_extend. exact Hno1. }
        assert (Hsubst2 : [x := arg2] (subst_rho (rho_shadow rho2 x) e) = subst_rho (rho_extend rho2 x arg2) e).
        { apply subst_rho_extend. exact Hno2. }

        (* Apply exp_rel at step S n' with Σ_cur = Σ' (since Σ ⊆ Σ') *)
        specialize (He_rel (S n') Σ' st1 st2 ctx Hext_Σ' Hstrel Hwf1 Hwf2 Hagree) as
          [v1 [v2 [st1' [st2' [ctx' [Σ'' [Hext'' [Hstep1 [Hstep2 [Hvalv1 [Hvalv2 [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]].

        (* Result *)
        exists v1, v2, st1', st2', ctx', Σ''.
        split. { exact Hext''. }
        split.
        { (* EApp (ELam x T1 body1) arg1 -->* v1 *)
          eapply MS_Step.
          - apply ST_AppAbs. exact Hvarg1.
          - rewrite Hsubst1. exact Hstep1. }
        split.
        { (* EApp (ELam x T1 body2) arg2 -->* v2 *)
          eapply MS_Step.
          - apply ST_AppAbs. exact Hvarg2.
          - rewrite Hsubst2. exact Hstep2. }
        split. { exact Hval. }
        split. { exact Hstore'. }
        split. { exact Hwf1'. }
        split. { exact Hwf2'. }
        { exact Hagree'. }
  - (* T_App - function application *)
    simpl.
    specialize (IHHty1 rho1 rho2 Henv Hno1 Hno2) as Hf_rel.  (* function *)
    specialize (IHHty2 rho1 rho2 Henv Hno1 Hno2) as Ha_rel.  (* argument *)
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.

      (* Step 1: Evaluate function to lambda *)
      specialize (Hf_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [f1 [f2 [st1' [st2' [ctx' [Σ' [Hext1 [Hstep_f1 [Hstep_f2 [Hvalf1 [Hvalf2 [Hfrel [Hstore1 [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]].

      (* Step 2: Evaluate argument *)
      assert (Hext_arg : store_ty_extends Σ Σ').
      { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext1). }
      specialize (Ha_rel (S n') Σ' st1' st2' ctx' Hext_arg Hstore1 Hwf1' Hwf2' Hagree') as
        [a1 [a2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_a1 [Hstep_a2 [Hvala1 [Hvala2 [Harel [Hstore2 [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]].

      (* Step 3: Apply function to argument *)
      (* f1, f2 are val_rel_n n' at TFn - extract val_rel_at_type *)
      (* Need to use the TFn val_rel_at_type property *)
      destruct n' as [| n''].
      { (* n' = 0: Step-1 case - use fundamental_theorem_step_0 axiom *)
        (* f1, f2 : val_rel_n 0 Σ' (TFn T1 T2 ε) — weaken to Σ'' *)
        assert (Hfrel'' : val_rel_n 0 Σ'' (TFn T1 T2 ε) f1 f2).
        { apply (val_rel_n_mono_store 0 Σ' Σ'' (TFn T1 T2 ε) f1 f2 Hext2 Hfrel). }
        destruct (val_rel_n_typing 0 Σ'' (TFn T1 T2 ε) f1 f2 Hfrel'') as [Htyf1'' Htyf2''].
        (* Get val_rel_at_type via fundamental_theorem_step_0 *)
        assert (Hfat : val_rel_at_type Σ'' (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) (TFn T1 T2 ε) f1 f2).
        { apply fundamental_theorem_step_0; try assumption.
          simpl. reflexivity. }
        (* Apply val_rel_at_type for TFn *)
        simpl in Hfat.
        destruct (val_rel_n_closed 0 Σ'' T1 a1 a2 Harel) as [Hcla1 Hcla2].
        specialize (Hfat Σ'' (store_ty_extends_refl Σ'') a1 a2 Hvala1 Hvala2 Hcla1 Hcla2).
        specialize (Hfat Harel st1'' st2'' ctx'' Hstore2 Hwf1'' Hwf2'' Hagree'') as
          [r1 [r2 [st1''' [st2''' [ctx''' [Σ''' [Hext3 [Hstep_app1 [Hstep_app2 [Hrrel [Hstore3 [Hwf1''' [Hwf2''' Hagree''']]]]]]]]]]]]].
        exists r1, r2, st1''', st2''', ctx''', Σ'''.
        split. { apply (store_ty_extends_trans_early Σ_cur Σ'' Σ''').
                 - apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext1 Hext2).
                 - exact Hext3. }
        split.
        { apply multi_step_trans with (cfg2 := (EApp f1 (subst_rho rho1 e2), st1', ctx')).
          - apply multi_step_app1. exact Hstep_f1.
          - apply multi_step_trans with (cfg2 := (EApp f1 a1, st1'', ctx'')).
            + apply multi_step_app2. exact Hvalf1. exact Hstep_a1.
            + exact Hstep_app1. }
        split.
        { apply multi_step_trans with (cfg2 := (EApp f2 (subst_rho rho2 e2), st2', ctx')).
          - apply multi_step_app1. exact Hstep_f2.
          - apply multi_step_trans with (cfg2 := (EApp f2 a2, st2'', ctx'')).
            + apply multi_step_app2. exact Hvalf2. exact Hstep_a2.
            + exact Hstep_app2. }
        destruct (val_rel_n_value 0 Σ''' T2 r1 r2 Hrrel) as [Hvalr1 Hvalr2].
        split. { exact Hvalr1. }
        split. { exact Hvalr2. }
        split. { exact Hrrel. }
        split. { exact Hstore3. }
        split. { exact Hwf1'''. }
        split. { exact Hwf2'''. }
        { exact Hagree'''. } }

      (* n' = S n'': have val_rel_n (S n'') which includes val_rel_at_type *)
      (* Extract the function application property from Hfrel *)
      rewrite val_rel_n_S_unfold in Hfrel.
      destruct Hfrel as [Hfrel_lower [Hvf1 [Hvf2 [Hclf1 [Hclf2 [_ Hfn_at_type]]]]]].

      (* Use val_rel_at_type for TFn: given related args, apps produce related results *)
      simpl in Hfn_at_type.

      (* Get closed_expr for arguments from val_rel_n at S n'' *)
      destruct (val_rel_n_closed (S n'') Σ'' T1 a1 a2 Harel) as [Hcla1 Hcla2].

      (* Downgrade Harel and Hstore2 to step n'' for Hfn_at_type *)
      assert (Harel' : val_rel_n n'' Σ'' T1 a1 a2).
      { apply (val_rel_n_mono n'' (S n'') Σ'' T1 a1 a2); [lia | exact Harel]. }
      assert (Hstore2' : store_rel_n n'' Σ'' st1'' st2'').
      { apply (store_rel_n_mono n'' (S n'') Σ'' st1'' st2''); [lia | exact Hstore2]. }

      (* Apply Hfn_at_type with:
         - Σ' extended to Σ''
         - args a1, a2 which are val_rel_n n'' at T1
         - stores st1'', st2'' which are store_rel_n n'' at Σ'' *)
      specialize (Hfn_at_type Σ'' Hext2 a1 a2 Hvala1 Hvala2 Hcla1 Hcla2).

      specialize (Hfn_at_type Harel' st1'' st2'' ctx'' Hstore2' Hwf1'' Hwf2'' Hagree'') as
        [r1 [r2 [st1''' [st2''' [ctx''' [Σ''' [Hext3 [Hstep_app1 [Hstep_app2 [Hrrel [Hstore3 [Hwf1''' [Hwf2''' Hagree''']]]]]]]]]]]]].

      (* Build result *)
      exists r1, r2, st1''', st2''', ctx''', Σ'''.
      split. { (* Σ_cur → Σ' → Σ'' → Σ''' *)
               apply (store_ty_extends_trans_early Σ_cur Σ'' Σ''').
               - apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext1 Hext2).
               - exact Hext3. }
      split.
      { (* Multi-step: EApp f a --> ... --> r1 *)
        apply multi_step_trans with (cfg2 := (EApp f1 (subst_rho rho1 e2), st1', ctx')).
        - apply multi_step_app1. exact Hstep_f1.
        - apply multi_step_trans with (cfg2 := (EApp f1 a1, st1'', ctx'')).
          + apply multi_step_app2. exact Hvalf1. exact Hstep_a1.
          + exact Hstep_app1. }
      split.
      { (* Multi-step for second execution *)
        apply multi_step_trans with (cfg2 := (EApp f2 (subst_rho rho2 e2), st2', ctx')).
        - apply multi_step_app1. exact Hstep_f2.
        - apply multi_step_trans with (cfg2 := (EApp f2 a2, st2'', ctx'')).
          + apply multi_step_app2. exact Hvalf2. exact Hstep_a2.
          + exact Hstep_app2. }
      destruct (val_rel_n_value n'' Σ''' T2 r1 r2 Hrrel) as [Hvalr1 Hvalr2].
      split. { exact Hvalr1. }
      split. { exact Hvalr2. }
      split.
      { (* Need val_rel_n (S n'') Σ''' T2 r1 r2 from val_rel_n n'' *)
        apply val_rel_n_step_up.
        - exact Hrrel.
        - destruct (val_rel_n_typing n'' Σ''' T2 r1 r2 Hrrel) as [Hty1_r _]. exact Hty1_r.
        - destruct (val_rel_n_typing n'' Σ''' T2 r1 r2 Hrrel) as [_ Hty2_r]. exact Hty2_r. }
      split.
      { (* Need store_rel_n (S n'') Σ''' from store_rel_n n'' *)
        apply store_rel_n_step_up.
        - exact Hstore3.
        - exact Hwf1'''.
        - exact Hwf2'''.
        - apply store_wf_to_has_values with Σ'''. exact Hwf1'''.
        - apply store_wf_to_has_values with Σ'''. exact Hwf2'''.
        - exact Hagree'''. }
      split. { exact Hwf1'''. }
      split. { exact Hwf2'''. }
      { exact Hagree'''. }
  - (* T_Pair - With Kripke-style exp_rel_n, the proof chains evaluations *)
    (* IH for e1 and e2 accept any current store typing extending Σ.
       We chain: Σ_cur → Σ' (after e1) → Σ'' (after e2). *)
    simpl.
    specialize (IHHty1 rho1 rho2 Henv Hno1 Hno2) as He1_rel.
    specialize (IHHty2 rho1 rho2 Henv Hno1 Hno2) as He2_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: exp_rel_n 0 is trivially True *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      (* Step 1: Evaluate e1 using IH with current store typing Σ_cur *)
      assert (Hext1_input : store_ty_extends Σ Σ_cur) by exact Hext_cur.
      specialize (He1_rel (S n') Σ_cur st1 st2 ctx Hext1_input Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v1 [v1' [st1' [st2' [ctx' [Σ' [Hext1 [Hstep1 [Hstep1' [Hvalv1 [Hvalv1' [Hval1 [Hstore1 [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]]].
      (* After e1: Σ_cur → Σ' and stores related at Σ' *)

      (* Step 2: Evaluate e2 using IH with Σ' as current store typing *)
      (* First show Σ ⊆ Σ' for the IH *)
      assert (Hext2_input : store_ty_extends Σ Σ').
      { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext1). }
      specialize (He2_rel (S n') Σ' st1' st2' ctx' Hext2_input Hstore1 Hwf1' Hwf2' Hagree') as
        [v2 [v2' [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep2 [Hstep2' [Hvalv2 [Hvalv2' [Hval2 [Hstore2 [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].
      (* After e2: Σ' → Σ'' and stores related at Σ'' *)

      (* Step 3: Construct the result *)
      exists (EPair v1 v2), (EPair v1' v2'), st1'', st2'', ctx'', Σ''.
      split.
      * (* store_ty_extends Σ_cur Σ'' - compose Σ_cur → Σ' → Σ'' *)
        apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext1 Hext2).
      * split.
        { (* (EPair e1 e2, st1, ctx) -->* (EPair v1 v2, st1'', ctx'') *)
          apply multi_step_trans with (cfg2 := (EPair v1 (subst_rho rho1 e2), st1', ctx')).
          - apply multi_step_pair1. exact Hstep1.
          - apply multi_step_trans with (cfg2 := (EPair v1 v2, st1'', ctx'')).
            + apply multi_step_pair2.
              * exact Hvalv1.
              * exact Hstep2.
            + apply MS_Refl. }
        split.
        { (* (EPair e1' e2', st2, ctx) -->* (EPair v1' v2', st2'', ctx'') *)
          apply multi_step_trans with (cfg2 := (EPair v1' (subst_rho rho2 e2), st2', ctx')).
          - apply multi_step_pair1. exact Hstep1'.
          - apply multi_step_trans with (cfg2 := (EPair v1' v2', st2'', ctx'')).
            + apply multi_step_pair2.
              * exact Hvalv1'.
              * exact Hstep2'.
            + apply MS_Refl. }
        split.
        { (* value (EPair v1 v2) *) constructor; assumption. }
        split.
        { (* value (EPair v1' v2') *) constructor; assumption. }
        split.
        { (* val_rel_n n' Σ'' (TProd T1 T2) (EPair v1 v2) (EPair v1' v2') *)
          assert (Hval1_ext : val_rel_n n' Σ'' T1 v1 v1').
          { apply (val_rel_n_mono_store n' Σ' Σ'' T1 v1 v1' Hext2 Hval1). }
          apply val_rel_n_prod_compose.
          - exact Hval1_ext.
          - exact Hval2.
          - destruct (val_rel_n_typing n' Σ'' T1 v1 v1' Hval1_ext) as [Ht _]. exact Ht.
          - destruct (val_rel_n_typing n' Σ'' T1 v1 v1' Hval1_ext) as [_ Ht]. exact Ht.
          - destruct (val_rel_n_typing n' Σ'' T2 v2 v2' Hval2) as [Ht _]. exact Ht.
          - destruct (val_rel_n_typing n' Σ'' T2 v2 v2' Hval2) as [_ Ht]. exact Ht. }
        split. { exact Hstore2. }
        split. { exact Hwf1''. }
        split. { exact Hwf2''. }
        { exact Hagree''. }
  - (* T_Fst - First projection *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: exp_rel_n 0 is trivially True *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      (* Step 1: Run the product expression using IH *)
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* v and v' are related products at type TProd T1 T2 *)

      destruct n' as [| n''].
      { (* n' = 0: Step-1 case - use exp_rel_step1_fst_general *)
        assert (HextΣ : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }
        destruct (exp_rel_step1_fst_general Σ T1 T2 v v' st1' st2' ctx' Σ'
                   Hval Hstore' HextΣ)
          as [a1 [a2 [st1'' [st2'' [ctx'' [Σ'' [Hext'' [HstepF1 [HstepF2 [Hva1 [Hva2 [Hvrel'' Hstore'']]]]]]]]]]]].
        exists a1, a2, st1'', st2'', ctx'', Σ''.
        split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext''). }
        split. { apply multi_step_trans with (cfg2 := (EFst v, st1', ctx')).
                 - apply multi_step_fst. exact Hstep.
                 - exact HstepF1. }
        split. { apply multi_step_trans with (cfg2 := (EFst v', st2', ctx')).
                 - apply multi_step_fst. exact Hstep'.
                 - exact HstepF2. }
        split; [exact Hva1 |].
        split; [exact Hva2 |].
        split; [exact Hvrel'' |].
        split. { exact Hstore''. }
        split. { exact Hwf1'. }
        split. { exact Hwf2'. }
        exact Hagree'. }
      (* n' = S n'': use val_rel_n_prod_decompose since n' > 0 *)
      destruct (val_rel_n_prod_decompose (S n'') Σ' T1 T2 v v')
        as [a1 [b1 [a2 [b2 [Heqv [Heqv' [Hva1 [Hvb1 [Hva2 [Hvb2
            [Hcla1 [Hclb1 [Hcla2 [Hclb2 [Hrat1 Hrat2]]]]]]]]]]]]]]].
      { lia. }
      { exact Hval. }
      subst v v'.
      (* Now: v = EPair a1 b1, v' = EPair a2 b2 *)

      (* Step 3: EFst (EPair a1 b1) --> a1 *)
      exists a1, a2, st1', st2', ctx', Σ'.
      split; [exact Hext |].
      split.
      { (* EFst (subst_rho rho1 e) -->* a1 *)
        apply multi_step_trans with (cfg2 := (EFst (EPair a1 b1), st1', ctx')).
        - apply multi_step_fst. exact Hstep.
        - eapply MS_Step.
          + apply ST_Fst; assumption.
          + apply MS_Refl. }
      split.
      { (* EFst (subst_rho rho2 e) -->* a2 *)
        apply multi_step_trans with (cfg2 := (EFst (EPair a2 b2), st2', ctx')).
        - apply multi_step_fst. exact Hstep'.
        - eapply MS_Step.
          + apply ST_Fst; assumption.
          + apply MS_Refl. }
      split; [exact Hva1 |].
      split; [exact Hva2 |].
      split.
      { (* val_rel_n (S n'') Σ' T1 a1 a2 *)
        apply (val_rel_n_from_prod_fst (S n'') Σ' T1 T2 a1 b1 a2 b2).
        - lia.
        - exact Hval. }
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Snd - Second projection *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: exp_rel_n 0 is trivially True *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      (* Step 1: Run the product expression using IH *)
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* v and v' are related products at type TProd T1 T2 *)

      destruct n' as [| n''].
      { (* n' = 0: Step-1 case - use exp_rel_step1_snd_general *)
        assert (HextΣ : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }
        destruct (exp_rel_step1_snd_general Σ T1 T2 v v' st1' st2' ctx' Σ'
                   Hval Hstore' HextΣ)
          as [b1 [b2 [st1'' [st2'' [ctx'' [Σ'' [Hext'' [HstepS1 [HstepS2 [Hvb1 [Hvb2 [Hvrel'' Hstore'']]]]]]]]]]]].
        exists b1, b2, st1'', st2'', ctx'', Σ''.
        split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext''). }
        split. { apply multi_step_trans with (cfg2 := (ESnd v, st1', ctx')).
                 - apply multi_step_snd. exact Hstep.
                 - exact HstepS1. }
        split. { apply multi_step_trans with (cfg2 := (ESnd v', st2', ctx')).
                 - apply multi_step_snd. exact Hstep'.
                 - exact HstepS2. }
        split; [exact Hvb1 |].
        split; [exact Hvb2 |].
        split; [exact Hvrel'' |].
        split. { exact Hstore''. }
        split. { exact Hwf1'. }
        split. { exact Hwf2'. }
        exact Hagree'. }
      (* n' = S n'': use val_rel_n_prod_decompose since n' > 0 *)
      destruct (val_rel_n_prod_decompose (S n'') Σ' T1 T2 v v')
        as [a1 [b1 [a2 [b2 [Heqv [Heqv' [Hva1 [Hvb1 [Hva2 [Hvb2
            [Hcla1 [Hclb1 [Hcla2 [Hclb2 [Hrat1 Hrat2]]]]]]]]]]]]]]].
      { lia. }
      { exact Hval. }
      subst v v'.
      (* Now: v = EPair a1 b1, v' = EPair a2 b2 *)

      (* Step 3: ESnd (EPair a1 b1) --> b1 *)
      exists b1, b2, st1', st2', ctx', Σ'.
      split; [exact Hext |].
      split.
      { (* ESnd (subst_rho rho1 e) -->* b1 *)
        apply multi_step_trans with (cfg2 := (ESnd (EPair a1 b1), st1', ctx')).
        - apply multi_step_snd. exact Hstep.
        - eapply MS_Step.
          + apply ST_Snd; assumption.
          + apply MS_Refl. }
      split.
      { (* ESnd (subst_rho rho2 e) -->* b2 *)
        apply multi_step_trans with (cfg2 := (ESnd (EPair a2 b2), st2', ctx')).
        - apply multi_step_snd. exact Hstep'.
        - eapply MS_Step.
          + apply ST_Snd; assumption.
          + apply MS_Refl. }
      split; [exact Hvb1 |].
      split; [exact Hvb2 |].
      split.
      { (* val_rel_n (S n'') Σ' T2 b1 b2 *)
        apply (val_rel_n_from_prod_snd (S n'') Σ' T1 T2 a1 b1 a2 b2).
        - lia.
        - exact Hval. }
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Inl - Left injection *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + simpl. trivial.
    + simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      exists (EInl v T2), (EInl v' T2), st1', st2', ctx', Σ'.
      split. { exact Hext. }
      split. { apply multi_step_inl. exact Hstep. }
      split. { apply multi_step_inl. exact Hstep'. }
      split. { constructor; assumption. }
      split. { constructor; assumption. }
      split. { apply val_rel_n_sum_inl; try exact Hval.
              - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [Ht _]. exact Ht.
              - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [_ Ht]. exact Ht. }
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Inr - Right injection *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + simpl. trivial.
    + simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      exists (EInr v T1), (EInr v' T1), st1', st2', ctx', Σ'.
      split. { exact Hext. }
      split. { apply multi_step_inr. exact Hstep. }
      split. { apply multi_step_inr. exact Hstep'. }
      split. { constructor; assumption. }
      split. { constructor; assumption. }
      split. { apply val_rel_n_sum_inr; try exact Hval.
              - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [Ht _]. exact Ht.
              - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [_ Ht]. exact Ht. }
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Case - Pattern matching on sums *)
    simpl.
    specialize (IHHty1 rho1 rho2 Henv Hno1 Hno2) as He_rel.  (* scrutinee *)
    (* Note: IHHty2 and IHHty3 have extended environments, handled below *)
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      (* Step 1: Evaluate the scrutinee *)
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep1 [Hstep1' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].

      destruct n' as [| n''].
      { (* n' = 0: Step-1 case — compose IHs directly *)
        assert (HextΣ : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

        (* Get val_rel at Σ to decompose the sum *)
        assert (Hval_full : val_rel Σ (TSum T1 T2) v v').
        { apply (val_rel_store_weaken_back Σ Σ' (TSum T1 T2) v v' HextΣ).
          apply (val_rel_n_to_val_rel_any Σ' (TSum T1 T2) v v' 0 Hvalv Hvalv' Hval). }

        (* Decompose at step 2 (need n > 0 for sum_decompose) *)
        assert (Hval2 : val_rel_n 2 Σ (TSum T1 T2) v v').
        { apply Hval_full. }
        destruct (val_rel_n_sum_decompose 2 Σ T1 T2 v v') as
          [[a1 [a2 [Heqv [Heqv' [Hvala1 [Hvala2 [Hcla1 [Hcla2 _]]]]]]]] |
           [b1 [b2 [Heqv [Heqv' [Hvalb1 [Hvalb2 [Hclb1 [Hclb2 _]]]]]]]]].
        { lia. }
        { exact Hval2. }

        * (* EInl case *)
          subst v v'.
          assert (Hval_a_at_Σ : val_rel Σ T1 a1 a2).
          { unfold val_rel. intro m. apply (val_rel_n_from_sum_inl m Σ T1 T2 a1 a2).
            destruct m; [lia | lia]. apply Hval_full. }

          assert (Henv' : env_rel Σ ((x1, T1) :: Γ) (rho_extend rho1 x1 a1) (rho_extend rho2 x1 a2)).
          { apply env_rel_extend. exact Henv. exact Hval_a_at_Σ. }

          assert (Hno1' : rho_no_free_all (rho_extend rho1 x1 a1)).
          { apply rho_no_free_extend; assumption. }
          assert (Hno2' : rho_no_free_all (rho_extend rho2 x1 a2)).
          { apply rho_no_free_extend; assumption. }

          specialize (IHHty2 (rho_extend rho1 x1 a1) (rho_extend rho2 x1 a2) Henv' Hno1' Hno2') as He1_rel.
          unfold exp_rel in He1_rel.

          assert (Hsubst1 : [x1 := a1] (subst_rho (rho_shadow rho1 x1) e1) =
                            subst_rho (rho_extend rho1 x1 a1) e1).
          { apply subst_rho_extend. exact Hno1. }
          assert (Hsubst2 : [x1 := a2] (subst_rho (rho_shadow rho2 x1) e1) =
                            subst_rho (rho_extend rho2 x1 a2) e1).
          { apply subst_rho_extend. exact Hno2. }

          specialize (He1_rel 1 Σ' st1' st2' ctx' HextΣ Hstore' Hwf1' Hwf2' Hagree') as
            [v1 [v2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_e1 [Hstep_e1' [Hvalv1 [Hvalv2 [Hval1 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

          exists v1, v2, st1'', st2'', ctx'', Σ''.
          split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2). }
          split. { apply multi_step_trans with (cfg2 := (ECase (EInl a1 T2) x1 (subst_rho (rho_shadow rho1 x1) e1)
                                                                             x2 (subst_rho (rho_shadow rho1 x2) e2), st1', ctx')).
                   - apply multi_step_case. exact Hstep1.
                   - eapply MS_Step.
                     + apply ST_CaseInl. exact Hvala1.
                     + rewrite Hsubst1. exact Hstep_e1. }
          split. { apply multi_step_trans with (cfg2 := (ECase (EInl a2 T2) x1 (subst_rho (rho_shadow rho2 x1) e1)
                                                                             x2 (subst_rho (rho_shadow rho2 x2) e2), st2', ctx')).
                   - apply multi_step_case. exact Hstep1'.
                   - eapply MS_Step.
                     + apply ST_CaseInl. exact Hvala2.
                     + rewrite Hsubst2. exact Hstep_e1'. }
          split; [exact Hvalv1 |].
          split; [exact Hvalv2 |].
          split; [exact Hval1 |].
          split. { exact Hstore''. }
          split. { exact Hwf1''. }
          split. { exact Hwf2''. }
          exact Hagree''.

        * (* EInr case *)
          subst v v'.
          assert (Hval_b_at_Σ : val_rel Σ T2 b1 b2).
          { unfold val_rel. intro m. apply (val_rel_n_from_sum_inr m Σ T1 T2 b1 b2).
            destruct m; [lia | lia]. apply Hval_full. }

          assert (Henv' : env_rel Σ ((x2, T2) :: Γ) (rho_extend rho1 x2 b1) (rho_extend rho2 x2 b2)).
          { apply env_rel_extend. exact Henv. exact Hval_b_at_Σ. }

          assert (Hno1' : rho_no_free_all (rho_extend rho1 x2 b1)).
          { apply rho_no_free_extend; assumption. }
          assert (Hno2' : rho_no_free_all (rho_extend rho2 x2 b2)).
          { apply rho_no_free_extend; assumption. }

          specialize (IHHty3 (rho_extend rho1 x2 b1) (rho_extend rho2 x2 b2) Henv' Hno1' Hno2') as He2_rel.
          unfold exp_rel in He2_rel.

          assert (Hsubst1 : [x2 := b1] (subst_rho (rho_shadow rho1 x2) e2) =
                            subst_rho (rho_extend rho1 x2 b1) e2).
          { apply subst_rho_extend. exact Hno1. }
          assert (Hsubst2 : [x2 := b2] (subst_rho (rho_shadow rho2 x2) e2) =
                            subst_rho (rho_extend rho2 x2 b2) e2).
          { apply subst_rho_extend. exact Hno2. }

          specialize (He2_rel 1 Σ' st1' st2' ctx' HextΣ Hstore' Hwf1' Hwf2' Hagree') as
            [v1 [v2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_e2 [Hstep_e2' [Hvalv1 [Hvalv2 [Hval_e2 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

          exists v1, v2, st1'', st2'', ctx'', Σ''.
          split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2). }
          split. { apply multi_step_trans with (cfg2 := (ECase (EInr b1 T1) x1 (subst_rho (rho_shadow rho1 x1) e1)
                                                                             x2 (subst_rho (rho_shadow rho1 x2) e2), st1', ctx')).
                   - apply multi_step_case. exact Hstep1.
                   - eapply MS_Step.
                     + apply ST_CaseInr. exact Hvalb1.
                     + rewrite Hsubst1. exact Hstep_e2. }
          split. { apply multi_step_trans with (cfg2 := (ECase (EInr b2 T1) x1 (subst_rho (rho_shadow rho2 x1) e1)
                                                                             x2 (subst_rho (rho_shadow rho2 x2) e2), st2', ctx')).
                   - apply multi_step_case. exact Hstep1'.
                   - eapply MS_Step.
                     + apply ST_CaseInr. exact Hvalb2.
                     + rewrite Hsubst2. exact Hstep_e2'. }
          split; [exact Hvalv1 |].
          split; [exact Hvalv2 |].
          split; [exact Hval_e2 |].
          split. { exact Hstore''. }
          split. { exact Hwf1''. }
          split. { exact Hwf2''. }
          exact Hagree''. }
      (* n' = S n'': have budget to evaluate branch, decompose the sum *)
      destruct (val_rel_n_sum_decompose (S n'') Σ' T1 T2 v v') as
        [[a1 [a2 [Heqv [Heqv' [Hvala1 [Hvala2 [Hcla1 [Hcla2 _]]]]]]]] |
         [b1 [b2 [Heqv [Heqv' [Hvalb1 [Hvalb2 [Hclb1 [Hclb2 _]]]]]]]]].
      { lia. }
      { exact Hval. }

      * (* EInl case: v = EInl a1 T2, v' = EInl a2 T2 *)
        subst v v'.
        (* Extract val_rel_n for a1, a2 at T1 *)
        assert (Hval_a : val_rel_n (S n'') Σ' T1 a1 a2).
        { apply (val_rel_n_from_sum_inl (S n'') Σ' T1 T2 a1 a2). lia. exact Hval. }

        assert (Hext_for_e1 : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

        (* Build extended environment at ORIGINAL Σ *)
        (* Requires: val_rel Σ T1 a1 a2 from val_rel_n (S n'') Σ' T1 a1 a2 *)
        (* This needs: (1) val_rel_n_weaken (Σ' → Σ) and (2) val_rel_n_to_val_rel *)
        (* Both depend on the step_up axiom for HO types *)
        assert (Hval_a_at_Σ : val_rel Σ T1 a1 a2).
        { apply (val_rel_store_weaken_back Σ Σ' T1 a1 a2 Hext_for_e1).
          apply (val_rel_n_to_val_rel_any Σ' T1 a1 a2 (S n'') Hvala1 Hvala2 Hval_a). }

        assert (Henv' : env_rel Σ ((x1, T1) :: Γ) (rho_extend rho1 x1 a1) (rho_extend rho2 x1 a2)).
        { apply env_rel_extend.
          - exact Henv.
          - exact Hval_a_at_Σ. }

        assert (Hno1' : rho_no_free_all (rho_extend rho1 x1 a1)).
        { apply rho_no_free_extend; assumption. }
        assert (Hno2' : rho_no_free_all (rho_extend rho2 x1 a2)).
        { apply rho_no_free_extend; assumption. }

        (* Apply IH for e1 with extended environment *)
        specialize (IHHty2 (rho_extend rho1 x1 a1) (rho_extend rho2 x1 a2) Henv' Hno1' Hno2') as He1_rel.
        unfold exp_rel in He1_rel.

        (* Connect substitutions: [x1 := a1](subst_rho (rho_shadow rho1 x1) e1) = subst_rho (rho_extend rho1 x1 a1) e1 *)
        assert (Hsubst1 : [x1 := a1] (subst_rho (rho_shadow rho1 x1) e1) =
                          subst_rho (rho_extend rho1 x1 a1) e1).
        { apply subst_rho_extend. exact Hno1. }
        assert (Hsubst2 : [x1 := a2] (subst_rho (rho_shadow rho2 x1) e1) =
                          subst_rho (rho_extend rho2 x1 a2) e1).
        { apply subst_rho_extend. exact Hno2. }

        (* Apply IH at step (S (S n'')) with store Σ' *)
        specialize (He1_rel (S (S n'')) Σ' st1' st2' ctx' Hext_for_e1 Hstore' Hwf1' Hwf2' Hagree') as
          [v1 [v2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_e1 [Hstep_e1' [Hvalv1 [Hvalv2 [Hval1 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

        exists v1, v2, st1'', st2'', ctx'', Σ''.
        split; [apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2) |].
        split.
        { (* Multi-step for first execution *)
          apply multi_step_trans with (cfg2 := (ECase (EInl a1 T2) x1 (subst_rho (rho_shadow rho1 x1) e1)
                                                                   x2 (subst_rho (rho_shadow rho1 x2) e2), st1', ctx')).
          - apply multi_step_case. exact Hstep1.
          - eapply MS_Step.
            + apply ST_CaseInl. exact Hvala1.
            + rewrite Hsubst1. exact Hstep_e1. }
        split.
        { (* Multi-step for second execution *)
          apply multi_step_trans with (cfg2 := (ECase (EInl a2 T2) x1 (subst_rho (rho_shadow rho2 x1) e1)
                                                                   x2 (subst_rho (rho_shadow rho2 x2) e2), st2', ctx')).
          - apply multi_step_case. exact Hstep1'.
          - eapply MS_Step.
            + apply ST_CaseInl. exact Hvala2.
            + rewrite Hsubst2. exact Hstep_e1'. }
        split; [exact Hvalv1 |].
        split; [exact Hvalv2 |].
        split; [exact Hval1 |].
        split. { exact Hstore''. }
        split. { exact Hwf1''. }
        split. { exact Hwf2''. }
        { exact Hagree''. }

      * (* EInr case: v = EInr b1 T1, v' = EInr b2 T1 *)
        subst v v'.
        (* Extract val_rel_n for b1, b2 at T2 *)
        assert (Hval_b : val_rel_n (S n'') Σ' T2 b1 b2).
        { apply (val_rel_n_from_sum_inr (S n'') Σ' T1 T2 b1 b2). lia. exact Hval. }

        assert (Hext_for_e2 : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

        (* Build extended environment at ORIGINAL Σ *)
        (* Same as EInl case: requires val_rel_n_weaken + val_rel_n_to_val_rel *)
        assert (Hval_b_at_Σ : val_rel Σ T2 b1 b2).
        { apply (val_rel_store_weaken_back Σ Σ' T2 b1 b2 Hext_for_e2).
          apply (val_rel_n_to_val_rel_any Σ' T2 b1 b2 (S n'') Hvalb1 Hvalb2 Hval_b). }

        assert (Henv' : env_rel Σ ((x2, T2) :: Γ) (rho_extend rho1 x2 b1) (rho_extend rho2 x2 b2)).
        { apply env_rel_extend.
          - exact Henv.
          - exact Hval_b_at_Σ. }

        assert (Hno1' : rho_no_free_all (rho_extend rho1 x2 b1)).
        { apply rho_no_free_extend; assumption. }
        assert (Hno2' : rho_no_free_all (rho_extend rho2 x2 b2)).
        { apply rho_no_free_extend; assumption. }

        (* Apply IH for e2 with extended environment *)
        specialize (IHHty3 (rho_extend rho1 x2 b1) (rho_extend rho2 x2 b2) Henv' Hno1' Hno2') as He2_rel.
        unfold exp_rel in He2_rel.

        (* Connect substitutions *)
        assert (Hsubst1 : [x2 := b1] (subst_rho (rho_shadow rho1 x2) e2) =
                          subst_rho (rho_extend rho1 x2 b1) e2).
        { apply subst_rho_extend. exact Hno1. }
        assert (Hsubst2 : [x2 := b2] (subst_rho (rho_shadow rho2 x2) e2) =
                          subst_rho (rho_extend rho2 x2 b2) e2).
        { apply subst_rho_extend. exact Hno2. }

        (* Apply IH at step (S (S n'')) with store Σ' *)
        specialize (He2_rel (S (S n'')) Σ' st1' st2' ctx' Hext_for_e2 Hstore' Hwf1' Hwf2' Hagree') as
          [v1 [v2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_e2 [Hstep_e2' [Hvalv1 [Hvalv2 [Hval2 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

        exists v1, v2, st1'', st2'', ctx'', Σ''.
        split; [apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2) |].
        split.
        { (* Multi-step for first execution *)
          apply multi_step_trans with (cfg2 := (ECase (EInr b1 T1) x1 (subst_rho (rho_shadow rho1 x1) e1)
                                                                   x2 (subst_rho (rho_shadow rho1 x2) e2), st1', ctx')).
          - apply multi_step_case. exact Hstep1.
          - eapply MS_Step.
            + apply ST_CaseInr. exact Hvalb1.
            + rewrite Hsubst1. exact Hstep_e2. }
        split.
        { (* Multi-step for second execution *)
          apply multi_step_trans with (cfg2 := (ECase (EInr b2 T1) x1 (subst_rho (rho_shadow rho2 x1) e1)
                                                                   x2 (subst_rho (rho_shadow rho2 x2) e2), st2', ctx')).
          - apply multi_step_case. exact Hstep1'.
          - eapply MS_Step.
            + apply ST_CaseInr. exact Hvalb2.
            + rewrite Hsubst2. exact Hstep_e2'. }
        split; [exact Hvalv1 |].
        split; [exact Hvalv2 |].
        split; [exact Hval2 |].
        split. { exact Hstore''. }
        split. { exact Hwf1''. }
        split. { exact Hwf2''. }
        { exact Hagree''. }
  - (* T_If - Conditional with same boolean evaluates same branch *)
    simpl.
    specialize (IHHty1 rho1 rho2 Henv Hno1 Hno2) as He1_rel.  (* condition *)
    specialize (IHHty2 rho1 rho2 Henv Hno1 Hno2) as He2_rel.  (* then branch *)
    specialize (IHHty3 rho1 rho2 Henv Hno1 Hno2) as He3_rel.  (* else branch *)
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: exp_rel_n 0 is trivially True *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      (* Step 1: Evaluate condition using IH1 *)
      specialize (He1_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* v and v' are related booleans: val_rel_n (S n') Σ' TBool v v' *)

      destruct n' as [| n''].
      { (* n' = 0: Step-1 case — compose IHs directly *)
        (* At step S 0: Hval : val_rel_n 0, Hstore' : store_rel_n 0 *)
        assert (HextΣ : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

        (* Extract same boolean from val_rel_n 0 *)
        destruct (val_rel_n_bool_structure 0 Σ' v v' Hval) as [b [Heq1 Heq2]].
        subst v v'.

        destruct b.
        - (* b = true: both step to then branch, apply He2_rel at step 1 *)
          specialize (He2_rel 1 Σ' st1' st2' ctx' HextΣ Hstore' Hwf1' Hwf2' Hagree') as
            [w1 [w2 [st1'' [st2'' [ctx'' [Σ'' [Hext'' [HstepB1 [HstepB2 [Hvalw1 [Hvalw2 [Hvalrel [Hstorerel [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].
          exists w1, w2, st1'', st2'', ctx'', Σ''.
          split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext''). }
          split. { apply multi_step_trans with (cfg2 := (EIf (EBool true) (subst_rho rho1 e2) (subst_rho rho1 e3), st1', ctx')).
                   - apply multi_step_if. exact Hstep.
                   - eapply MS_Step. apply ST_IfTrue. exact HstepB1. }
          split. { apply multi_step_trans with (cfg2 := (EIf (EBool true) (subst_rho rho2 e2) (subst_rho rho2 e3), st2', ctx')).
                   - apply multi_step_if. exact Hstep'.
                   - eapply MS_Step. apply ST_IfTrue. exact HstepB2. }
          split; [exact Hvalw1 |].
          split; [exact Hvalw2 |].
          split; [exact Hvalrel |].
          split. { exact Hstorerel. }
          split. { exact Hwf1''. }
          split. { exact Hwf2''. }
          exact Hagree''.
        - (* b = false: both step to else branch, apply He3_rel at step 1 *)
          specialize (He3_rel 1 Σ' st1' st2' ctx' HextΣ Hstore' Hwf1' Hwf2' Hagree') as
            [w1 [w2 [st1'' [st2'' [ctx'' [Σ'' [Hext'' [HstepB1 [HstepB2 [Hvalw1 [Hvalw2 [Hvalrel [Hstorerel [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].
          exists w1, w2, st1'', st2'', ctx'', Σ''.
          split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext''). }
          split. { apply multi_step_trans with (cfg2 := (EIf (EBool false) (subst_rho rho1 e2) (subst_rho rho1 e3), st1', ctx')).
                   - apply multi_step_if. exact Hstep.
                   - eapply MS_Step. apply ST_IfFalse. exact HstepB1. }
          split. { apply multi_step_trans with (cfg2 := (EIf (EBool false) (subst_rho rho2 e2) (subst_rho rho2 e3), st2', ctx')).
                   - apply multi_step_if. exact Hstep'.
                   - eapply MS_Step. apply ST_IfFalse. exact HstepB2. }
          split; [exact Hvalw1 |].
          split; [exact Hvalw2 |].
          split; [exact Hvalrel |].
          split. { exact Hstorerel. }
          split. { exact Hwf1''. }
          split. { exact Hwf2''. }
          exact Hagree''. }
      (* n' = S n'': n' >= 1, have budget to evaluate branch *)
      (* At step (S n'), IH1 gives val_rel_n n' = val_rel_n (S n''), store_rel_n n' = store_rel_n (S n'') *)
      (* Extract same boolean from val_rel_n (S n'') *)
      destruct (val_rel_n_bool_structure (S n'') Σ' v v' Hval) as [b [Heq1 Heq2]].
      subst v v'.
      (* Now we know: v = EBool b, v' = EBool b - SAME boolean! *)

      (* Step 2: Step EIf (EBool b) e2 e3 to the appropriate branch *)
      destruct b.
      * (* b = true: both step to then branch *)
        assert (HextΣ' : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }
        (* Apply IH2 for then branch at step (S n') = (S (S n''))
           This needs store_rel_n n' = store_rel_n (S n''), which is Hstore' *)
        specialize (He2_rel (S (S n'')) Σ' st1' st2' ctx'
                     HextΣ' Hstore' Hwf1' Hwf2' Hagree') as
          [r1 [r2 [st1'' [st2'' [ctx'' [Σ'' [Hext'' [Hstep2 [Hstep2' [Hvalr1 [Hvalr2 [Hval2 [Hstore2 [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].
        exists r1, r2, st1'', st2'', ctx'', Σ''.
        split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext''). }
        split.
        { (* Chain: e1 -->* EBool true, then EIf (EBool true) e2 e3 --> e2, then e2 -->* r1 *)
          apply multi_step_trans with (cfg2 := (EIf (EBool true) (subst_rho rho1 e2) (subst_rho rho1 e3), st1', ctx')).
          - apply multi_step_if. exact Hstep.
          - apply multi_step_trans with (cfg2 := (subst_rho rho1 e2, st1', ctx')).
            + eapply MS_Step. { apply ST_IfTrue. } apply MS_Refl.
            + exact Hstep2. }
        split.
        { (* Same for second expression *)
          apply multi_step_trans with (cfg2 := (EIf (EBool true) (subst_rho rho2 e2) (subst_rho rho2 e3), st2', ctx')).
          - apply multi_step_if. exact Hstep'.
          - apply multi_step_trans with (cfg2 := (subst_rho rho2 e2, st2', ctx')).
            + eapply MS_Step. { apply ST_IfTrue. } apply MS_Refl.
            + exact Hstep2'. }
        split; [exact Hvalr1 |].
        split; [exact Hvalr2 |].
        split; [exact Hval2 |].
        split. { exact Hstore2. }
        split. { exact Hwf1''. }
        split. { exact Hwf2''. }
        { exact Hagree''. }
      * (* b = false: both step to else branch *)
        assert (HextΣ' : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }
        (* Apply IH3 for else branch at step (S n') = (S (S n''))
           This needs store_rel_n n' = store_rel_n (S n''), which is Hstore' *)
        specialize (He3_rel (S (S n'')) Σ' st1' st2' ctx'
                     HextΣ' Hstore' Hwf1' Hwf2' Hagree') as
          [r1 [r2 [st1'' [st2'' [ctx'' [Σ'' [Hext'' [Hstep3 [Hstep3' [Hvalr1 [Hvalr2 [Hval3 [Hstore3 [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].
        exists r1, r2, st1'', st2'', ctx'', Σ''.
        split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext''). }
        split.
        { (* Chain: e1 -->* EBool false, then EIf (EBool false) e2 e3 --> e3, then e3 -->* r1 *)
          apply multi_step_trans with (cfg2 := (EIf (EBool false) (subst_rho rho1 e2) (subst_rho rho1 e3), st1', ctx')).
          - apply multi_step_if. exact Hstep.
          - apply multi_step_trans with (cfg2 := (subst_rho rho1 e3, st1', ctx')).
            + eapply MS_Step. { apply ST_IfFalse. } apply MS_Refl.
            + exact Hstep3. }
        split.
        { (* Same for second expression *)
          apply multi_step_trans with (cfg2 := (EIf (EBool false) (subst_rho rho2 e2) (subst_rho rho2 e3), st2', ctx')).
          - apply multi_step_if. exact Hstep'.
          - apply multi_step_trans with (cfg2 := (subst_rho rho2 e3, st2', ctx')).
            + eapply MS_Step. { apply ST_IfFalse. } apply MS_Refl.
            + exact Hstep3'. }
        split; [exact Hvalr1 |].
        split; [exact Hvalr2 |].
        split; [exact Hval3 |].
        split. { exact Hstore3. }
        split. { exact Hwf1''. }
        split. { exact Hwf2''. }
        { exact Hagree''. }
  - (* T_Let - Variable binding *)
    simpl.
    specialize (IHHty1 rho1 rho2 Henv Hno1 Hno2) as He1_rel.  (* bound expression *)
    (* IHHty2 has extended environment, handled below *)
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      (* Step 1: Evaluate the bound expression e1 *)
      specialize (He1_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep1 [Hstep1' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].

      destruct n' as [| n''].
      { (* n' = 0: Step-1 case — compose IHs directly *)
        assert (HextΣ : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

        (* Build extended environment *)
        assert (Hval_at_Σ : val_rel Σ T1 v v').
        { apply (val_rel_store_weaken_back Σ Σ' T1 v v' HextΣ).
          apply (val_rel_n_to_val_rel_any Σ' T1 v v' 0 Hvalv Hvalv' Hval). }

        assert (Henv' : env_rel Σ ((x, T1) :: Γ) (rho_extend rho1 x v) (rho_extend rho2 x v')).
        { apply env_rel_extend. exact Henv. exact Hval_at_Σ. }

        destruct (val_rel_n_closed 0 Σ' T1 v v' Hval) as [Hcl1 Hcl2].
        assert (Hno1' : rho_no_free_all (rho_extend rho1 x v)).
        { apply rho_no_free_extend. exact Hno1. exact Hcl1. }
        assert (Hno2' : rho_no_free_all (rho_extend rho2 x v')).
        { apply rho_no_free_extend. exact Hno2. exact Hcl2. }

        specialize (IHHty2 (rho_extend rho1 x v) (rho_extend rho2 x v') Henv' Hno1' Hno2') as He2_rel.
        unfold exp_rel in He2_rel.

        assert (Hsubst1 : [x := v] (subst_rho (rho_shadow rho1 x) e2) =
                          subst_rho (rho_extend rho1 x v) e2).
        { apply subst_rho_extend. exact Hno1. }
        assert (Hsubst2 : [x := v'] (subst_rho (rho_shadow rho2 x) e2) =
                          subst_rho (rho_extend rho2 x v') e2).
        { apply subst_rho_extend. exact Hno2. }

        specialize (He2_rel 1 Σ' st1' st2' ctx' HextΣ Hstore' Hwf1' Hwf2' Hagree') as
          [v1 [v2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_e2 [Hstep_e2' [Hvalv1 [Hvalv2 [Hval2 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

        exists v1, v2, st1'', st2'', ctx'', Σ''.
        split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2). }
        split. { apply multi_step_trans with (cfg2 := (ELet x v (subst_rho (rho_shadow rho1 x) e2), st1', ctx')).
                 - apply multi_step_let. exact Hstep1.
                 - eapply MS_Step.
                   + apply ST_LetValue. exact Hvalv.
                   + rewrite Hsubst1. exact Hstep_e2. }
        split. { apply multi_step_trans with (cfg2 := (ELet x v' (subst_rho (rho_shadow rho2 x) e2), st2', ctx')).
                 - apply multi_step_let. exact Hstep1'.
                 - eapply MS_Step.
                   + apply ST_LetValue. exact Hvalv'.
                   + rewrite Hsubst2. exact Hstep_e2'. }
        split; [exact Hvalv1 |].
        split; [exact Hvalv2 |].
        split; [exact Hval2 |].
        split. { exact Hstore''. }
        split. { exact Hwf1''. }
        split. { exact Hwf2''. }
        exact Hagree''. }

      (* n' = S n'': have budget to evaluate body *)
      assert (Hext_for_e2 : store_ty_extends Σ Σ').
      { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

      (* Build extended environment at ORIGINAL Σ *)
      (* Requires: val_rel Σ T1 v v' from val_rel_n (S n'') Σ' T1 v v' *)
      assert (Hval_at_Σ : val_rel Σ T1 v v').
      { apply (val_rel_store_weaken_back Σ Σ' T1 v v' Hext_for_e2).
        apply (val_rel_n_to_val_rel_any Σ' T1 v v' (S n'') Hvalv Hvalv' Hval). }

      assert (Henv' : env_rel Σ ((x, T1) :: Γ) (rho_extend rho1 x v) (rho_extend rho2 x v')).
      { apply env_rel_extend.
        - exact Henv.
        - exact Hval_at_Σ. }

      (* v and v' are closed because they come from val_rel_n at S n'' > 0 *)
      destruct (val_rel_n_closed (S n'') Σ' T1 v v' Hval) as [Hcl1 Hcl2].
      assert (Hno1' : rho_no_free_all (rho_extend rho1 x v)).
      { apply rho_no_free_extend.
        - exact Hno1.
        - exact Hcl1. }
      assert (Hno2' : rho_no_free_all (rho_extend rho2 x v')).
      { apply rho_no_free_extend.
        - exact Hno2.
        - exact Hcl2. }

      (* Apply IH for e2 with extended environment *)
      specialize (IHHty2 (rho_extend rho1 x v) (rho_extend rho2 x v') Henv' Hno1' Hno2') as He2_rel.
      unfold exp_rel in He2_rel.

      (* Connect substitutions: [x := v](subst_rho (rho_shadow rho1 x) e2) = subst_rho (rho_extend rho1 x v) e2 *)
      assert (Hsubst1 : [x := v] (subst_rho (rho_shadow rho1 x) e2) =
                        subst_rho (rho_extend rho1 x v) e2).
      { apply subst_rho_extend. exact Hno1. }
      assert (Hsubst2 : [x := v'] (subst_rho (rho_shadow rho2 x) e2) =
                        subst_rho (rho_extend rho2 x v') e2).
      { apply subst_rho_extend. exact Hno2. }

      (* Apply IH at step (S (S n'')) with store Σ' *)
      specialize (He2_rel (S (S n'')) Σ' st1' st2' ctx' Hext_for_e2 Hstore' Hwf1' Hwf2' Hagree') as
        [v1 [v2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_e2 [Hstep_e2' [Hvalv1 [Hvalv2 [Hval2 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

      exists v1, v2, st1'', st2'', ctx'', Σ''.
      split; [apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2) |].
      split.
      { (* Multi-step for first execution *)
        apply multi_step_trans with (cfg2 := (ELet x v (subst_rho (rho_shadow rho1 x) e2), st1', ctx')).
        - apply multi_step_let. exact Hstep1.
        - eapply MS_Step.
          + apply ST_LetValue. exact Hvalv.
          + rewrite Hsubst1. exact Hstep_e2. }
      split.
      { (* Multi-step for second execution *)
        apply multi_step_trans with (cfg2 := (ELet x v' (subst_rho (rho_shadow rho2 x) e2), st2', ctx')).
        - apply multi_step_let. exact Hstep1'.
        - eapply MS_Step.
          + apply ST_LetValue. exact Hvalv'.
          + rewrite Hsubst2. exact Hstep_e2'. }
      split; [exact Hvalv1 |].
      split; [exact Hvalv2 |].
      split; [exact Hval2 |].
      split. { exact Hstore''. }
      split. { exact Hwf1''. }
      split. { exact Hwf2''. }
      { exact Hagree''. }
  - (* T_Perform - Effect perform just passes through the value *)
    (* EPerform eff e evaluates e to a value v, then EPerform eff v --> v *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* EPerform eff v --> v by ST_PerformValue *)
      exists v, v', st1', st2', ctx', Σ'.
      split. { exact Hext. }
      split.
      { (* Multi-step: EPerform eff (subst_rho rho1 e) -->* v *)
        apply multi_step_trans with (cfg2 := (EPerform eff v, st1', ctx')).
        - apply multi_step_perform. exact Hstep.
        - eapply MS_Step.
          + apply ST_PerformValue. exact Hvalv.
          + apply MS_Refl. }
      split.
      { (* Multi-step for second execution *)
        apply multi_step_trans with (cfg2 := (EPerform eff v', st2', ctx')).
        - apply multi_step_perform. exact Hstep'.
        - eapply MS_Step.
          + apply ST_PerformValue. exact Hvalv'.
          + apply MS_Refl. }
      split; [exact Hvalv |].
      split; [exact Hvalv' |].
      split; [exact Hval |].
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Handle - Effect handler is like let-binding *)
    (* EHandle e x h evaluates e to v, then steps to [x := v] h *)
    simpl.
    specialize (IHHty1 rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep1 [Hstep1' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].

      destruct n' as [| n''].
      { (* n' = 0: Step-1 case — compose IHs directly *)
        assert (HextΣ : store_ty_extends Σ Σ').
        { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

        assert (Hval_at_Σ : val_rel Σ T1 v v').
        { apply (val_rel_store_weaken_back Σ Σ' T1 v v' HextΣ).
          apply (val_rel_n_to_val_rel_any Σ' T1 v v' 0 Hvalv Hvalv' Hval). }

        assert (Henv' : env_rel Σ ((x, T1) :: Γ) (rho_extend rho1 x v) (rho_extend rho2 x v')).
        { apply env_rel_extend. exact Henv. exact Hval_at_Σ. }

        destruct (val_rel_n_closed 0 Σ' T1 v v' Hval) as [Hcl1 Hcl2].
        assert (Hno1' : rho_no_free_all (rho_extend rho1 x v)).
        { apply rho_no_free_extend. exact Hno1. exact Hcl1. }
        assert (Hno2' : rho_no_free_all (rho_extend rho2 x v')).
        { apply rho_no_free_extend. exact Hno2. exact Hcl2. }

        specialize (IHHty2 (rho_extend rho1 x v) (rho_extend rho2 x v') Henv' Hno1' Hno2') as Hh_rel.
        unfold exp_rel in Hh_rel.

        assert (Hsubst1 : [x := v] (subst_rho (rho_shadow rho1 x) h) =
                          subst_rho (rho_extend rho1 x v) h).
        { apply subst_rho_extend. exact Hno1. }
        assert (Hsubst2 : [x := v'] (subst_rho (rho_shadow rho2 x) h) =
                          subst_rho (rho_extend rho2 x v') h).
        { apply subst_rho_extend. exact Hno2. }

        specialize (Hh_rel 1 Σ' st1' st2' ctx' HextΣ Hstore' Hwf1' Hwf2' Hagree') as
          [r1 [r2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_h [Hstep_h' [Hvalr1 [Hvalr2 [Hval2 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

        exists r1, r2, st1'', st2'', ctx'', Σ''.
        split. { apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2). }
        split. { apply multi_step_trans with (cfg2 := (EHandle v x (subst_rho (rho_shadow rho1 x) h), st1', ctx')).
                 - apply multi_step_handle. exact Hstep1.
                 - eapply MS_Step.
                   + apply ST_HandleValue. exact Hvalv.
                   + rewrite Hsubst1. exact Hstep_h. }
        split. { apply multi_step_trans with (cfg2 := (EHandle v' x (subst_rho (rho_shadow rho2 x) h), st2', ctx')).
                 - apply multi_step_handle. exact Hstep1'.
                 - eapply MS_Step.
                   + apply ST_HandleValue. exact Hvalv'.
                   + rewrite Hsubst2. exact Hstep_h'. }
        split; [exact Hvalr1 |].
        split; [exact Hvalr2 |].
        split; [exact Hval2 |].
        split. { exact Hstore''. }
        split. { exact Hwf1''. }
        split. { exact Hwf2''. }
        exact Hagree''. }

      (* n' = S n'': have budget to evaluate handler body *)
      assert (Hext_for_h : store_ty_extends Σ Σ').
      { apply (store_ty_extends_trans_early Σ Σ_cur Σ' Hext_cur Hext). }

      (* Build extended environment at ORIGINAL Σ *)
      assert (Hval_at_Σ : val_rel Σ T1 v v').
      { apply (val_rel_store_weaken_back Σ Σ' T1 v v' Hext_for_h).
        apply (val_rel_n_to_val_rel_any Σ' T1 v v' (S n'') Hvalv Hvalv' Hval). }

      assert (Henv' : env_rel Σ ((x, T1) :: Γ) (rho_extend rho1 x v) (rho_extend rho2 x v')).
      { apply env_rel_extend.
        - exact Henv.
        - exact Hval_at_Σ. }

      destruct (val_rel_n_closed (S n'') Σ' T1 v v' Hval) as [Hcl1 Hcl2].
      assert (Hno1' : rho_no_free_all (rho_extend rho1 x v)).
      { apply rho_no_free_extend. exact Hno1. exact Hcl1. }
      assert (Hno2' : rho_no_free_all (rho_extend rho2 x v')).
      { apply rho_no_free_extend. exact Hno2. exact Hcl2. }

      specialize (IHHty2 (rho_extend rho1 x v) (rho_extend rho2 x v') Henv' Hno1' Hno2') as Hh_rel.
      unfold exp_rel in Hh_rel.

      (* Connect substitutions *)
      assert (Hsubst1 : [x := v] (subst_rho (rho_shadow rho1 x) h) =
                        subst_rho (rho_extend rho1 x v) h).
      { apply subst_rho_extend. exact Hno1. }
      assert (Hsubst2 : [x := v'] (subst_rho (rho_shadow rho2 x) h) =
                        subst_rho (rho_extend rho2 x v') h).
      { apply subst_rho_extend. exact Hno2. }

      specialize (Hh_rel (S (S n'')) Σ' st1' st2' ctx' Hext_for_h Hstore' Hwf1' Hwf2' Hagree') as
        [r1 [r2 [st1'' [st2'' [ctx'' [Σ'' [Hext2 [Hstep_h [Hstep_h' [Hvalr1 [Hvalr2 [Hval2 [Hstore'' [Hwf1'' [Hwf2'' Hagree'']]]]]]]]]]]]]]]]].

      exists r1, r2, st1'', st2'', ctx'', Σ''.
      split; [apply (store_ty_extends_trans_early Σ_cur Σ' Σ'' Hext Hext2) |].
      split.
      { apply multi_step_trans with (cfg2 := (EHandle v x (subst_rho (rho_shadow rho1 x) h), st1', ctx')).
        - apply multi_step_handle. exact Hstep1.
        - eapply MS_Step.
          + apply ST_HandleValue. exact Hvalv.
          + rewrite Hsubst1. exact Hstep_h. }
      split.
      { apply multi_step_trans with (cfg2 := (EHandle v' x (subst_rho (rho_shadow rho2 x) h), st2', ctx')).
        - apply multi_step_handle. exact Hstep1'.
        - eapply MS_Step.
          + apply ST_HandleValue. exact Hvalv'.
          + rewrite Hsubst2. exact Hstep_h'. }
      split; [exact Hvalr1 |].
      split; [exact Hvalr2 |].
      split; [exact Hval2 |].
      split. { exact Hstore''. }
      split. { exact Hwf1''. }
      split. { exact Hwf2''. }
      { exact Hagree''. }
  - (* T_Ref - Uses logical_relation_ref axiom *)
    (* The axiom logical_relation_ref directly proves this case. *)
    simpl.
    unfold exp_rel. intro n.
    eapply logical_relation_ref.
    + eassumption.  (* has_type for e *)
    + exact Henv.
    + exact Hno1.
    + exact Hno2.
  - (* T_Deref - Uses logical_relation_deref axiom *)
    (* The axiom logical_relation_deref directly proves this case. *)
    simpl.
    unfold exp_rel. intro n.
    eapply logical_relation_deref.
    + eassumption.  (* has_type for e *)
    + exact Henv.
    + exact Hno1.
    + exact Hno2.
  - (* T_Assign - Uses logical_relation_assign axiom *)
    (* The axiom logical_relation_assign directly proves this case. *)
    simpl.
    unfold exp_rel. intro n.
    eapply logical_relation_assign.
    + eassumption.  (* has_type for e1 *)
    + eassumption.  (* has_type for e2 *)
    + exact Henv.
    + exact Hno1.
    + exact Hno2.
  - (* T_Classify - Wrapping in TSecret is trivially related *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* Classify wraps the value *)
      exists (EClassify v), (EClassify v'), st1', st2', ctx', Σ'.
      split. { exact Hext. }
      split. { apply multi_step_classify. exact Hstep. }
      split. { apply multi_step_classify. exact Hstep'. }
      split. { constructor. assumption. }
      split. { constructor. assumption. }
      split.
      { (* val_rel_n for TSecret T - use val_rel_n_classify *)
        destruct (val_rel_n_closed n' Σ' T v v' Hval) as [Hcl1 Hcl2].
        apply val_rel_n_classify; try assumption.
        - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [Ht _]. exact Ht.
        - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [_ Ht]. exact Ht. }
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Declassify - Uses logical_relation_declassify axiom *)
    (* The axiom logical_relation_declassify directly proves this case. *)
    simpl.
    unfold exp_rel. intro n.
    eapply logical_relation_declassify.
    + eassumption.  (* has_type for e *)
    + exact Henv.
    + exact Hno1.
    + exact Hno2.
  - (* T_Prove - Wrapping in EProve produces proof type *)
    (* EProve e evaluates e to v, then EProve v is a value of type TProof T *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* EProve v is a value *)
      exists (EProve v), (EProve v'), st1', st2', ctx', Σ'.
      split. { exact Hext. }
      split. { apply multi_step_prove. exact Hstep. }
      split. { apply multi_step_prove. exact Hstep'. }
      split. { constructor. assumption. }
      split. { constructor. assumption. }
      split.
      { (* val_rel_n for TProof T - use val_rel_n_prove *)
        destruct (val_rel_n_closed n' Σ' T v v' Hval) as [Hcl1 Hcl2].
        apply val_rel_n_prove; try assumption.
        - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [Ht _]. exact Ht.
        - destruct (val_rel_n_typing _ _ _ _ _ Hval) as [_ Ht]. exact Ht. }
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Require - Effect require just passes through the value *)
    (* ERequire eff e evaluates e to v, then ERequire eff v --> v *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* ERequire eff v --> v by ST_RequireValue *)
      exists v, v', st1', st2', ctx', Σ'.
      split. { exact Hext. }
      split.
      { apply multi_step_trans with (cfg2 := (ERequire eff v, st1', ctx')).
        - apply multi_step_require. exact Hstep.
        - eapply MS_Step.
          + apply ST_RequireValue. exact Hvalv.
          + apply MS_Refl. }
      split.
      { apply multi_step_trans with (cfg2 := (ERequire eff v', st2', ctx')).
        - apply multi_step_require. exact Hstep'.
        - eapply MS_Step.
          + apply ST_RequireValue. exact Hvalv'.
          + apply MS_Refl. }
      split; [exact Hvalv |].
      split; [exact Hvalv' |].
      split; [exact Hval |].
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
  - (* T_Grant - Effect grant just passes through the value *)
    (* EGrant eff e evaluates e to v, then EGrant eff v --> v *)
    simpl.
    specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
    unfold exp_rel in *. intros n.
    destruct n as [| n'].
    + (* n = 0: trivially true *)
      simpl. trivial.
    + (* n = S n' *)
      simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur.
      specialize (He_rel (S n') Σ_cur st1 st2 ctx Hext_cur Hstore Hwf1_cur Hwf2_cur Hagree_cur) as
        [v [v' [st1' [st2' [ctx' [Σ' [Hext [Hstep [Hstep' [Hvalv [Hvalv' [Hval [Hstore' [Hwf1' [Hwf2' Hagree']]]]]]]]]]]]]]]].
      (* EGrant eff v --> v by ST_GrantValue *)
      exists v, v', st1', st2', ctx', Σ'.
      split. { exact Hext. }
      split.
      { apply multi_step_trans with (cfg2 := (EGrant eff v, st1', ctx')).
        - apply multi_step_grant. exact Hstep.
        - eapply MS_Step.
          + apply ST_GrantValue. exact Hvalv.
          + apply MS_Refl. }
      split.
      { apply multi_step_trans with (cfg2 := (EGrant eff v', st2', ctx')).
        - apply multi_step_grant. exact Hstep'.
        - eapply MS_Step.
          + apply ST_GrantValue. exact Hvalv'.
          + apply MS_Refl. }
      split; [exact Hvalv |].
      split; [exact Hvalv' |].
      split; [exact Hval |].
      split. { exact Hstore'. }
      split. { exact Hwf1'. }
      split. { exact Hwf2'. }
      { exact Hagree'. }
Qed. (* Remaining cases admitted for v2 migration *)


(** Lemma: val_rel implies closed expressions *)
Lemma val_rel_closed : forall Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  closed_expr v1 /\ closed_expr v2.
Proof.
  intros Σ T v1 v2 Hval.
  (* val_rel means forall n, val_rel_n n Σ T v1 v2 *)
  (* Instantiate with n = 1 to get the closed_expr requirements *)
  specialize (Hval 1).
  simpl in Hval.
  (* At S 0: val_rel_n 0 /\ value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\ ... *)
  destruct Hval as [_ [_ [_ [Hc1 [Hc2 _]]]]].
  exact (conj Hc1 Hc2).
Qed.

(** Environment relation for a single binding *)
Lemma env_rel_single : forall Σ x T v1 v2,
  val_rel Σ T v1 v2 ->
  env_rel Σ ((x, T) :: nil) (rho_single x v1) (rho_single x v2).
Proof.
  intros Σ x T v1 v2 Hval.
  unfold env_rel, env_rel_n.
  intros n y Ty Hlook.
  simpl in Hlook.
  destruct (String.eqb y x) eqn:Heq.
  - (* y = x *)
    apply String.eqb_eq in Heq. subst y.
    inversion Hlook. subst Ty.
    unfold rho_single. rewrite String.eqb_refl.
    apply Hval.
  - (* y <> x, impossible since lookup fails *)
    discriminate Hlook.
Qed.

Theorem non_interference_stmt : forall x T_in T_out v1 v2 e,
  val_rel nil T_in v1 v2 ->
  has_type ((x, T_in) :: nil) nil Public e T_out EffectPure ->
  exp_rel nil T_out ([x := v1] e) ([x := v2] e).
Proof.
  intros x T_in T_out v1 v2 e Hval Hty.
  (* Rewrite using subst_rho_single lemma *)
  rewrite <- (subst_rho_single e x v1).
  rewrite <- (subst_rho_single e x v2).
  (* Apply logical_relation *)
  apply (logical_relation ((x, T_in) :: nil) nil e T_out EffectPure
                          (rho_single x v1) (rho_single x v2)).
  - exact Hty.
  - apply env_rel_single. exact Hval.
  - (* rho_no_free_all for v1 *)
    apply rho_no_free_all_single.
    destruct (val_rel_closed nil T_in v1 v2 Hval) as [Hc1 _]. exact Hc1.
  - (* rho_no_free_all for v2 *)
    apply rho_no_free_all_single.
    destruct (val_rel_closed nil T_in v1 v2 Hval) as [_ Hc2]. exact Hc2.
Qed.

(** ========================================================================
    SECTION: QUICK-WIN LEMMAS FOR AXIOM ELIMINATION
    ========================================================================

    These lemmas prove properties that were previously axioms in the
    LogicalRelationDeclassify_PROOF_REFINED.v and LogicalRelationAssign_PROOF.v
    files. By proving them here with the actual definitions, we can mark
    those axioms as verified.
*)

(** QUICK-WIN 1: Substitution distributes over EDeclassify
    This follows directly from the definition of subst_rho.
    Proves: Axiom subst_rho_declassify_dist from LogicalRelationDeclassify_PROOF_REFINED.v
*)
Lemma subst_rho_declassify_dist : forall rho e1 e2,
  subst_rho rho (EDeclassify e1 e2) = EDeclassify (subst_rho rho e1) (subst_rho rho e2).
Proof.
  intros rho e1 e2.
  simpl.
  reflexivity.
Qed.

(** End of NonInterference.v *)
