(** * Non-Interference for RIINA

    Information flow security property.
    
    We define a logical relation to capture observational equivalence.
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Preservation.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

(** Observer level *)
Parameter observer : security_level.

(** Security lattice check: l <= observer *)
Definition is_low (l : security_level) : Prop :=
  sec_leq l observer.

(** Closed expressions: no free variables. *)
Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

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

(** ** Logical Relation

    We define a binary logical relation R_V(T) on values.
    R_E(T) is defined as "reduces to values related by R_V(T)".

    CRITICAL: Products and sums use the SAME step index (structural recursion).
    Only functions decrement the index (computational step/"later" modality).

    We use a two-level structure:
    - val_rel_at_n: given a fixed n, recurses on type structure
    - val_rel_n/store_rel_n: outer step-indexed relation
*)

(** Type-structural value relation at a fixed step index.
    Products/sums recurse at the SAME level - no index decrement. *)
Section ValRelAtN.
  Variable Σ : store_ty.
  Variable store_rel_pred : store -> store -> Prop.
  Variable val_rel_lower : ty -> expr -> expr -> Prop. (* for function results *)
  Variable store_rel_lower : store_ty -> store -> store -> Prop. (* for result stores *)

  Fixpoint val_rel_at_type (T : ty) (v1 v2 : expr) {struct T} : Prop :=
    match T with
    | TUnit => v1 = EUnit /\ v2 = EUnit
    | TBool => exists b, v1 = EBool b /\ v2 = EBool b
    | TInt => exists i, v1 = EInt i /\ v2 = EInt i
    | TString => exists s, v1 = EString s /\ v2 = EString s
    | TBytes => v1 = v2
    | TSecret T' => True
    | TRef T' _ =>
        exists l, v1 = ELoc l /\ v2 = ELoc l
    | TProd T1 T2 =>
        exists x1 y1 x2 y2,
          v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
          val_rel_at_type T1 x1 x2 /\ val_rel_at_type T2 y1 y2
    | TSum T1 T2 =>
        (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type T1 x1 x2) \/
        (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type T2 y1 y2)
    | TFn T1 T2 eff =>
        forall x y, val_rel_at_type T1 x y ->
          forall st1 st2 ctx,
            store_rel_pred st1 st2 ->
            exists (v1' : expr) (v2' : expr) (st1' : store) (st2' : store)
                   (ctx' : effect_ctx) (Σ' : store_ty),
              store_ty_extends Σ Σ' /\
              (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
              (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
              val_rel_lower T2 v1' v2' /\
              store_rel_lower Σ' st1' st2'
    | TCapability _ => True
    | TProof _ => True
    end.
End ValRelAtN.

(** Step-indexed value and store relations *)
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type Σ (store_rel_n n' Σ) (val_rel_n n' Σ) (store_rel_n n') T v1 v2
  end
with store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' Σ T v1 v2)
  end.

(** Monotonicity: higher step index implies lower step index relation.
    Note: This property holds but is NOT sufficient for T_Fst/T_Snd proofs.
    Those cases need the index to stay the same for products, not decrease.
    The real fix requires changing val_rel_n to not decrement for products. *)
Lemma val_rel_n_mono : forall n m Σ T v1 v2,
  n >= m ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  (* Proof requires careful handling of function contravariance.
     Will be completed after val_rel_n restructuring. *)
Admitted.

Fixpoint exp_rel_n (n : nat) (Σ : store_ty) (T : ty) (e1 e2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      forall st1 st2 ctx,
        store_rel_n n' Σ st1 st2 ->
        exists (v1 : expr) (v2 : expr) (st1' : store) (st2' : store)
               (ctx' : effect_ctx) (Σ' : store_ty),
          store_ty_extends Σ Σ' /\
          (e1, st1, ctx) -->* (v1, st1', ctx') /\
          (e2, st2, ctx) -->* (v2, st2', ctx') /\
          val_rel_n n' Σ T v1 v2 /\
          store_rel_n n' Σ' st1' st2'
  end.

Definition val_rel (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  forall n, val_rel_n n Σ T v1 v2.

Definition store_rel (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall n, store_rel_n n Σ st1 st2.

Definition exp_rel (Σ : store_ty) (T : ty) (e1 e2 : expr) : Prop :=
  forall n, exp_rel_n n Σ T e1 e2.

Notation "e1 '~' e2 ':' T ':' Σ" := (exp_rel Σ T e1 e2) (at level 40).
Notation "v1 '~~' v2 ':' T ':' Σ" := (val_rel Σ T v1 v2) (at level 40).

Lemma val_rel_closed_left_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  closed_expr v1.
Proof.
  destruct n as [| n']; intros Σ T v1 v2 Hn Hrel.
  - lia.
  - simpl in Hrel. destruct Hrel as [_ [_ [Hc1 _]]]. exact Hc1.
Qed.

Lemma val_rel_closed_right_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  closed_expr v2.
Proof.
  destruct n as [| n']; intros Σ T v1 v2 Hn Hrel.
  - lia.
  - simpl in Hrel. destruct Hrel as [_ [_ [_ [Hc2 _]]]]. exact Hc2.
Qed.

Lemma val_rel_value_left_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  value v1.
Proof.
  destruct n as [| n']; intros Σ T v1 v2 Hn Hrel.
  - lia.
  - simpl in Hrel. destruct Hrel as [Hv1 _]. exact Hv1.
Qed.

Lemma val_rel_value_right_n : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  value v2.
Proof.
  destruct n as [| n']; intros Σ T v1 v2 Hn Hrel.
  - lia.
  - simpl in Hrel. destruct Hrel as [_ [Hv2 _]]. exact Hv2.
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

(* TODO: This lemma requires val_rel_n monotonicity in store typing *)
Lemma store_rel_n_weaken : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  (* Temporarily admitted - needs val_rel_n_weaken lemma *)
Admitted.

(** ** Environment Substitution *)

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

Lemma exp_rel_of_val_rel : forall Σ T v1 v2,
  val_rel Σ T v1 v2 ->
  exp_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hrel n.
  destruct n as [| n'].
  - exact I.
  - intros st1 st2 ctx Hstore.
    exists v1, v2, st1, st2, ctx, Σ.
    split.
    + unfold store_ty_extends. intros l T' sl Hlook. exact Hlook.
    + split.
      * apply MS_Refl.
      * split.
        -- apply MS_Refl.
        -- split.
           ++ exact (Hrel n').
           ++ exact Hstore.
Qed.

Lemma exp_rel_of_val_rel_step : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 ->
  exp_rel_n (S n) Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hrel st1 st2 ctx Hstore.
  exists v1, v2, st1, st2, ctx, Σ.
  split.
  - unfold store_ty_extends. intros l T' sl Hlook. exact Hlook.
  - split.
    + apply MS_Refl.
    + split.
      * apply MS_Refl.
      * split.
        -- exact Hrel.
        -- exact Hstore.
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
Lemma val_rel_n_prod_fst : forall n Σ T1 T2 v1 v2,
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_n n Σ T1 a1 a2.
Proof.
  (* Technical lemma - proof involves careful reasoning about value/closed *)
Admitted.

Lemma val_rel_n_prod_snd : forall n Σ T1 T2 v1 v2,
  n > 0 ->
  val_rel_n n Σ (TProd T1 T2) v1 v2 ->
  exists a1 b1 a2 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_n n Σ T2 b1 b2.
Proof.
  (* Technical lemma - proof involves careful reasoning about value/closed *)
Admitted.

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
  (* Most cases require careful handling - admit for now while we verify structure *)
Admitted.


(* TODO: Fix after logical_relation is proven *)
Theorem non_interference_stmt : forall x T_in T_out v1 v2 e,
  val_rel nil T_in v1 v2 ->
  has_type ((x, T_in) :: nil) nil Public e T_out EffectPure ->
  exp_rel nil T_out ([x := v1] e) ([x := v2] e).
Proof.
  (* Depends on logical_relation which is temporarily admitted *)
Admitted.

(** End of NonInterference.v *)
