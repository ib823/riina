(** * FundamentalTheorem.v

    Compatibility lemmas for the Fundamental Theorem of Logical Relations.

    Generated to fill the admit at NonInterference_v2.v:1110

    This file proves that well-typed expressions preserve the logical relation
    under related substitutions. This is the "Fundamental Theorem" or
    "Compatibility Theorem" of logical relations.

    References:
    - Ahmed (2006) "Step-Indexed Syntactic Logical Relations"
    - Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"

    Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md §4.2

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Preservation.
Require Import RIINA.properties.NonInterference_v2.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

(** ========================================================================
    SECTION 1: SUBSTITUTION RELATION
    ========================================================================

    Related substitutions: γ1 and γ2 map variables to related values.
    This captures the semantic content of a typing environment.

    A substitution γ is a partial function from identifiers to expressions.
    We represent substitutions as functions with a default (EVar x).
*)

(** Substitution type: maps identifiers to expressions *)
Definition substitution := ident -> expr.

(** Identity substitution *)
Definition subst_id : substitution := fun x => EVar x.

(** Extend substitution with a binding *)
Definition subst_extend (γ : substitution) (x : ident) (v : expr) : substitution :=
  fun y => if String.eqb x y then v else γ y.

(** Apply substitution to expression *)
Fixpoint apply_subst (γ : substitution) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar x => γ x
  | ELam x T body => ELam x T (apply_subst (subst_extend γ x (EVar x)) body)
  | EApp e1 e2 => EApp (apply_subst γ e1) (apply_subst γ e2)
  | EPair e1 e2 => EPair (apply_subst γ e1) (apply_subst γ e2)
  | EFst e0 => EFst (apply_subst γ e0)
  | ESnd e0 => ESnd (apply_subst γ e0)
  | EInl e0 T => EInl (apply_subst γ e0) T
  | EInr e0 T => EInr (apply_subst γ e0) T
  | ECase e0 x1 e1 x2 e2 =>
      ECase (apply_subst γ e0)
            x1 (apply_subst (subst_extend γ x1 (EVar x1)) e1)
            x2 (apply_subst (subst_extend γ x2 (EVar x2)) e2)
  | EIf e1 e2 e3 => EIf (apply_subst γ e1) (apply_subst γ e2) (apply_subst γ e3)
  | ELet x e1 e2 =>
      ELet x (apply_subst γ e1)
           (apply_subst (subst_extend γ x (EVar x)) e2)
  | EPerform eff e0 => EPerform eff (apply_subst γ e0)
  | EHandle e0 x h =>
      EHandle (apply_subst γ e0) x
              (apply_subst (subst_extend γ x (EVar x)) h)
  | ERef e0 l => ERef (apply_subst γ e0) l
  | EDeref e0 => EDeref (apply_subst γ e0)
  | EAssign e1 e2 => EAssign (apply_subst γ e1) (apply_subst γ e2)
  | EClassify e0 => EClassify (apply_subst γ e0)
  | EDeclassify e1 e2 => EDeclassify (apply_subst γ e1) (apply_subst γ e2)
  | EProve e0 => EProve (apply_subst γ e0)
  | ERequire eff e0 => ERequire eff (apply_subst γ e0)
  | EGrant eff e0 => EGrant eff (apply_subst γ e0)
  end.

(** Substitution relation: γ1 and γ2 map variables in Γ to related values *)
Definition subst_rel_n (n : nat) (Σ : store_ty) (Γ : type_env)
           (γ1 γ2 : substitution) : Prop :=
  forall x T,
    lookup x Γ = Some T ->
    val_rel_n n Σ T (γ1 x) (γ2 x).

(** Empty substitution relation: trivially holds for empty context *)
Lemma subst_rel_n_empty : forall n Σ γ1 γ2,
  subst_rel_n n Σ nil γ1 γ2.
Proof.
  intros n Σ γ1 γ2.
  unfold subst_rel_n.
  intros x T Hlookup.
  simpl in Hlookup. discriminate.
Qed.

(** Extend substitution relation with a related binding *)
Lemma subst_rel_n_extend : forall n Σ Γ γ1 γ2 x T v1 v2,
  subst_rel_n n Σ Γ γ1 γ2 ->
  val_rel_n n Σ T v1 v2 ->
  subst_rel_n n Σ ((x, T) :: Γ) (subst_extend γ1 x v1) (subst_extend γ2 x v2).
Proof.
  intros n Σ Γ γ1 γ2 x T v1 v2 Hsubst Hval.
  unfold subst_rel_n. intros y Ty Hlookup.
  simpl in Hlookup.
  unfold subst_extend.
  (* lookup uses String.eqb y x, but we destruct String.eqb x y *)
  destruct (String.eqb y x) eqn:Heq.
  - (* y = x: rewrite the other direction too *)
    apply String.eqb_eq in Heq. subst y.
    rewrite String.eqb_refl.
    injection Hlookup as HTy. subst Ty.
    exact Hval.
  - (* y <> x *)
    assert (Hneq: String.eqb x y = false).
    { apply String.eqb_neq. apply String.eqb_neq in Heq. auto. }
    rewrite Hneq.
    apply Hsubst. exact Hlookup.
Qed.

(** Monotonicity of substitution relation *)
Lemma subst_rel_n_mono : forall m n Σ Γ γ1 γ2,
  m <= n ->
  subst_rel_n n Σ Γ γ1 γ2 ->
  subst_rel_n m Σ Γ γ1 γ2.
Proof.
  intros m n Σ Γ γ1 γ2 Hle Hsubst.
  unfold subst_rel_n in *.
  intros x T Hlookup.
  apply val_rel_n_mono with n.
  - exact Hle.
  - apply Hsubst. exact Hlookup.
Qed.

(** ========================================================================
    SECTION 2: COMPATIBILITY LEMMAS
    ========================================================================

    For EACH typing rule T_X in has_type, we prove a lemma compat_X.
    Each lemma shows that if subexpressions are in the expression relation,
    then the compound expression is also in the expression relation.
*)

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR VALUES (T_Unit, T_Bool, T_Int, T_String, T_Loc)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Unit:
    EUnit is related to EUnit at TUnit for any n *)
Lemma compat_unit : forall n Σ,
  exp_rel_n n Σ TUnit EUnit EUnit.
Proof.
  intros n Σ.
  destruct n as [| n'].
  - (* n = 0: trivially true *)
    simpl. exact I.
  - (* n = S n': EUnit terminates to itself *)
    simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    exists EUnit, EUnit, st1, st2, ctx, Σ_cur.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Refl.
    + apply MS_Refl.
    + constructor.
    + constructor.
    + (* val_rel_n n' Σ_cur TUnit EUnit EUnit *)
      destruct n' as [| n''].
      * apply val_rel_n_0_unit.
      * apply val_rel_n_unit. lia.
    + exact Hstrel.
Qed.

(** Compatibility for T_Bool:
    EBool b is related to EBool b at TBool for any n *)
Lemma compat_bool : forall n Σ b,
  exp_rel_n n Σ TBool (EBool b) (EBool b).
Proof.
  intros n Σ b.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    exists (EBool b), (EBool b), st1, st2, ctx, Σ_cur.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Refl.
    + apply MS_Refl.
    + constructor.
    + constructor.
    + (* val_rel_n n' Σ_cur TBool (EBool b) (EBool b) *)
      destruct n' as [| n''].
      * rewrite val_rel_n_0_unfold.
        repeat split.
        -- constructor.
        -- constructor.
        -- intros x Hfree. inversion Hfree.
        -- intros x Hfree. inversion Hfree.
        -- simpl. exists b. split; reflexivity.
      * rewrite val_rel_n_S_unfold.
        split.
        -- (* val_rel_n n'' *)
           clear Hstrel Hext.
           induction n'' as [| n''' IH].
           ++ rewrite val_rel_n_0_unfold.
              repeat split.
              ** constructor.
              ** constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** simpl. exists b. split; reflexivity.
           ++ rewrite val_rel_n_S_unfold.
              split; [exact IH |].
              repeat split.
              ** constructor.
              ** constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** exact I.
              ** simpl. exists b. split; reflexivity.
        -- repeat split.
           ++ constructor.
           ++ constructor.
           ++ intros x Hfree. inversion Hfree.
           ++ intros x Hfree. inversion Hfree.
           ++ exact I.
           ++ simpl. exists b. split; reflexivity.
    + exact Hstrel.
Qed.

(** Compatibility for T_Int:
    EInt i is related to EInt i at TInt for any n *)
Lemma compat_int : forall n Σ i,
  exp_rel_n n Σ TInt (EInt i) (EInt i).
Proof.
  intros n Σ i.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    exists (EInt i), (EInt i), st1, st2, ctx, Σ_cur.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Refl.
    + apply MS_Refl.
    + constructor.
    + constructor.
    + (* val_rel_n n' Σ_cur TInt (EInt i) (EInt i) *)
      destruct n' as [| n''].
      * rewrite val_rel_n_0_unfold.
        repeat split.
        -- constructor.
        -- constructor.
        -- intros x Hfree. inversion Hfree.
        -- intros x Hfree. inversion Hfree.
        -- simpl. exists i. split; reflexivity.
      * rewrite val_rel_n_S_unfold.
        split.
        -- (* Induction for n'' *)
           clear Hstrel Hext.
           induction n'' as [| n''' IH].
           ++ rewrite val_rel_n_0_unfold.
              repeat split; try constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** simpl. exists i. split; reflexivity.
           ++ rewrite val_rel_n_S_unfold.
              split; [exact IH |].
              repeat split; try constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** exact I.
              ** simpl. exists i. split; reflexivity.
        -- repeat split; try constructor.
           ++ intros x Hfree. inversion Hfree.
           ++ intros x Hfree. inversion Hfree.
           ++ exact I.
           ++ simpl. exists i. split; reflexivity.
    + exact Hstrel.
Qed.

(** Compatibility for T_String:
    EString s is related to EString s at TString for any n *)
Lemma compat_string : forall n Σ s,
  exp_rel_n n Σ TString (EString s) (EString s).
Proof.
  intros n Σ s.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    exists (EString s), (EString s), st1, st2, ctx, Σ_cur.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Refl.
    + apply MS_Refl.
    + constructor.
    + constructor.
    + (* val_rel_n for TString *)
      destruct n' as [| n''].
      * rewrite val_rel_n_0_unfold.
        repeat split; try constructor.
        -- intros x Hfree. inversion Hfree.
        -- intros x Hfree. inversion Hfree.
        -- simpl. exists s. split; reflexivity.
      * rewrite val_rel_n_S_unfold.
        split.
        -- clear Hstrel Hext.
           induction n'' as [| n''' IH].
           ++ rewrite val_rel_n_0_unfold.
              repeat split; try constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** simpl. exists s. split; reflexivity.
           ++ rewrite val_rel_n_S_unfold.
              split; [exact IH |].
              repeat split; try constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** exact I.
              ** simpl. exists s. split; reflexivity.
        -- repeat split; try constructor.
           ++ intros x Hfree. inversion Hfree.
           ++ intros x Hfree. inversion Hfree.
           ++ exact I.
           ++ simpl. exists s. split; reflexivity.
    + exact Hstrel.
Qed.

(** Compatibility for T_Loc:
    ELoc l is related to ELoc l at TRef T sl if the location is in store typing *)
Lemma compat_loc : forall n Σ l T sl,
  store_ty_lookup l Σ = Some (T, sl) ->
  exp_rel_n n Σ (TRef T sl) (ELoc l) (ELoc l).
Proof.
  intros n Σ l T sl Hlookup.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    exists (ELoc l), (ELoc l), st1, st2, ctx, Σ_cur.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Refl.
    + apply MS_Refl.
    + constructor.
    + constructor.
    + (* val_rel_n n' Σ_cur (TRef T sl) (ELoc l) (ELoc l) *)
      destruct n' as [| n''].
      * rewrite val_rel_n_0_unfold.
        repeat split; try constructor.
        -- intros x Hfree. inversion Hfree.
        -- intros x Hfree. inversion Hfree.
        -- simpl. exists l. split; reflexivity.
      * rewrite val_rel_n_S_unfold.
        split.
        -- clear Hstrel Hext.
           induction n'' as [| n''' IH].
           ++ rewrite val_rel_n_0_unfold.
              repeat split; try constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** simpl. exists l. split; reflexivity.
           ++ rewrite val_rel_n_S_unfold.
              split; [exact IH |].
              repeat split; try constructor.
              ** intros x Hfree. inversion Hfree.
              ** intros x Hfree. inversion Hfree.
              ** exact I.
              ** simpl. exists l. split; reflexivity.
        -- repeat split; try constructor.
           ++ intros x Hfree. inversion Hfree.
           ++ intros x Hfree. inversion Hfree.
           ++ exact I.
           ++ simpl. exists l. split; reflexivity.
    + exact Hstrel.
Qed.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMA FOR VARIABLES (T_Var)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Var:
    If x has type T in Γ and substitutions are related, then γ1(x) ~ γ2(x) : T *)
Lemma compat_var : forall n Σ Γ γ1 γ2 x T,
  lookup x Γ = Some T ->
  subst_rel_n n Σ Γ γ1 γ2 ->
  exp_rel_n n Σ T (γ1 x) (γ2 x).
Proof.
  intros n Σ Γ γ1 γ2 x T Hlookup Hsubst.
  destruct n as [| n'].
  - (* n = 0: trivially true *)
    simpl. exact I.
  - (* n = S n': use substitution relation *)
    simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    (* From subst_rel_n, we get val_rel_n (S n') for γ1 x and γ2 x *)
    unfold subst_rel_n in Hsubst.
    specialize (Hsubst x T Hlookup) as Hvrel.
    (* val_rel_n (S n') Σ T (γ1 x) (γ2 x) *)
    (* Need to weaken to Σ_cur and return the values *)
    (* Values are already computed (γ1 x and γ2 x are values by val_rel_n) *)
    assert (Hv : value (γ1 x) /\ value (γ2 x)).
    { apply val_rel_n_value with (S n') Σ T. exact Hvrel. }
    destruct Hv as [Hv1 Hv2].
    exists (γ1 x), (γ2 x), st1, st2, ctx, Σ_cur.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Refl.
    + apply MS_Refl.
    + exact Hv1.
    + exact Hv2.
    + (* val_rel_n n' Σ_cur T (γ1 x) (γ2 x) *)
      (* Need to weaken from Σ to Σ_cur - this requires store_ty_extends lemma *)
      (* BLOCKED: Requires store type weakening lemma for val_rel_n
         The proof would show that val_rel_n is preserved under store extension.
         This is standard but requires additional infrastructure. *)
      apply val_rel_n_mono with (S n').
      * lia.
      * (* Need to show val_rel_n (S n') Σ_cur T (γ1 x) (γ2 x) from
           val_rel_n (S n') Σ T (γ1 x) (γ2 x) and store_ty_extends Σ Σ_cur.
           BLOCKED: Requires store extension weakening lemma. *)
        admit.
    + exact Hstrel.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMA FOR FUNCTIONS (T_Lam, T_App)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Lam:
    If body is related under extended substitution, then lambda is related *)
Lemma compat_lam : forall n Σ Γ γ1 γ2 x T1 T2 eff e,
  (forall v1 v2,
    val_rel_n n Σ T1 v1 v2 ->
    subst_rel_n n Σ ((x, T1) :: Γ) (subst_extend γ1 x v1) (subst_extend γ2 x v2) ->
    exp_rel_n n Σ T2 (apply_subst (subst_extend γ1 x v1) e)
                     (apply_subst (subst_extend γ2 x v2) e)) ->
  subst_rel_n n Σ Γ γ1 γ2 ->
  exp_rel_n n Σ (TFn T1 T2 eff) (ELam x T1 (apply_subst (subst_extend γ1 x (EVar x)) e))
                                (ELam x T1 (apply_subst (subst_extend γ2 x (EVar x)) e)).
Proof.
  intros n Σ Γ γ1 γ2 x T1 T2 eff e IHbody Hsubst.
  destruct n as [| n'].
  - (* n = 0: trivially true *)
    simpl. exact I.
  - (* n = S n': lambda values are related *)
    simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    set (body1 := apply_subst (subst_extend γ1 x (EVar x)) e).
    set (body2 := apply_subst (subst_extend γ2 x (EVar x)) e).
    exists (ELam x T1 body1), (ELam x T1 body2), st1, st2, ctx, Σ_cur.
    repeat split.
    + apply store_ty_extends_refl.
    + apply MS_Refl.
    + apply MS_Refl.
    + constructor.
    + constructor.
    + (* val_rel_n n' Σ_cur (TFn T1 T2 eff) (ELam x T1 body1) (ELam x T1 body2) *)
      (* BLOCKED: Proving lambda values are related requires:
         1. Showing that for any related arguments v1 v2, applications terminate
         2. And produce related results
         This is the core of the Fundamental Theorem for function types.
         It requires strong normalization and compatibility lemmas working together. *)
      admit.
    + exact Hstrel.
Admitted.

(** Compatibility for T_App:
    If function and argument are related, then application is related *)
Lemma compat_app : forall n Σ T1 T2 eff e1 e1' e2 e2',
  exp_rel_n n Σ (TFn T1 T2 eff) e1 e1' ->
  exp_rel_n n Σ T1 e2 e2' ->
  exp_rel_n n Σ T2 (EApp e1 e2) (EApp e1' e2').
Proof.
  intros n Σ T1 T2 eff e1 e1' e2 e2' Hfn Harg.
  destruct n as [| n'].
  - (* n = 0: trivially true *)
    simpl. exact I.
  - (* n = S n': application produces related results *)
    simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    (* First, evaluate e1 to a function value *)
    simpl in Hfn.
    specialize (Hfn Σ_cur st1 st2 ctx Hext Hstrel) as
      [v1 [v1' [st1' [st2' [ctx' [Σ' [Hext1 [Hstep1 [Hstep2 [Hv1 [Hv1' [Hvrel Hstrel']]]]]]]]]]].
    (* Then, evaluate e2 to an argument value *)
    (* Need to use Hstrel' and updated store types *)
    assert (Hext_cur : store_ty_extends Σ Σ').
    { apply store_ty_extends_trans with Σ_cur.
      - exact Hext.
      - exact Hext1. }
    (* BLOCKED: The full proof requires:
       1. Evaluating e2 under the updated store (from Hstrel')
       2. Using the function relation to show application terminates
       3. Combining results to show the applications are related
       This is the standard β-reduction case in logical relations. *)
    admit.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR PRODUCTS (T_Pair, T_Fst, T_Snd)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Pair:
    If components are related, then pair is related *)
Lemma compat_pair : forall n Σ T1 T2 e1 e1' e2 e2',
  exp_rel_n n Σ T1 e1 e1' ->
  exp_rel_n n Σ T2 e2 e2' ->
  exp_rel_n n Σ (TProd T1 T2) (EPair e1 e2) (EPair e1' e2').
Proof.
  intros n Σ T1 T2 e1 e1' e2 e2' He1 He2.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    (* Evaluate e1 to v1, v1' *)
    simpl in He1.
    specialize (He1 Σ_cur st1 st2 ctx Hext Hstrel) as
      [v1 [v1' [st1_1 [st2_1 [ctx1 [Σ1 [Hext1 [Hstep1_1 [Hstep2_1 [Hv1 [Hv1' [Hvrel1 Hstrel1]]]]]]]]]]].
    (* Evaluate e2 to v2, v2' under updated stores *)
    assert (Hext_Σ1 : store_ty_extends Σ Σ1).
    { apply store_ty_extends_trans with Σ_cur; assumption. }
    (* BLOCKED: Need to evaluate e2 and combine with pair formation *)
    admit.
Admitted.

(** Compatibility for T_Fst:
    If pair is related, then first projection is related *)
Lemma compat_fst : forall n Σ T1 T2 e e',
  exp_rel_n n Σ (TProd T1 T2) e e' ->
  exp_rel_n n Σ T1 (EFst e) (EFst e').
Proof.
  intros n Σ T1 T2 e e' Hpair.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    simpl in Hpair.
    specialize (Hpair Σ_cur st1 st2 ctx Hext Hstrel) as
      [v [v' [st1' [st2' [ctx' [Σ' [Hext' [Hstep1 [Hstep2 [Hv [Hv' [Hvrel Hstrel']]]]]]]]]]].
    (* v and v' are related pairs: need to extract first components *)
    (* Use val_rel_n_prod_structure if T1, T2 are first-order *)
    (* BLOCKED: Requires showing fst reduction and extracting pair components *)
    admit.
Admitted.

(** Compatibility for T_Snd:
    If pair is related, then second projection is related *)
Lemma compat_snd : forall n Σ T1 T2 e e',
  exp_rel_n n Σ (TProd T1 T2) e e' ->
  exp_rel_n n Σ T2 (ESnd e) (ESnd e').
Proof.
  intros n Σ T1 T2 e e' Hpair.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    simpl in Hpair.
    specialize (Hpair Σ_cur st1 st2 ctx Hext Hstrel) as
      [v [v' [st1' [st2' [ctx' [Σ' [Hext' [Hstep1 [Hstep2 [Hv [Hv' [Hvrel Hstrel']]]]]]]]]]].
    (* BLOCKED: Similar to compat_fst *)
    admit.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR SUMS (T_Inl, T_Inr, T_Case)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Inl:
    If injection payload is related, then left injection is related *)
Lemma compat_inl : forall n Σ T1 T2 e e',
  exp_rel_n n Σ T1 e e' ->
  exp_rel_n n Σ (TSum T1 T2) (EInl e T2) (EInl e' T2).
Proof.
  intros n Σ T1 T2 e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    simpl in He.
    specialize (He Σ_cur st1 st2 ctx Hext Hstrel) as
      [v [v' [st1' [st2' [ctx' [Σ' [Hext' [Hstep1 [Hstep2 [Hv [Hv' [Hvrel Hstrel']]]]]]]]]]].
    exists (EInl v T2), (EInl v' T2), st1', st2', ctx', Σ'.
    repeat split.
    + exact Hext'.
    + (* (EInl e T2, st1, ctx) -->* (EInl v T2, st1', ctx') *)
      (* BLOCKED: Requires evaluation context lemma for EInl *)
      admit.
    + admit.
    + constructor. exact Hv.
    + constructor. exact Hv'.
    + (* val_rel_n n' Σ' (TSum T1 T2) (EInl v T2) (EInl v' T2) *)
      admit.
    + exact Hstrel'.
Admitted.

(** Compatibility for T_Inr:
    If injection payload is related, then right injection is related *)
Lemma compat_inr : forall n Σ T1 T2 e e',
  exp_rel_n n Σ T2 e e' ->
  exp_rel_n n Σ (TSum T1 T2) (EInr e T1) (EInr e' T1).
Proof.
  intros n Σ T1 T2 e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Similar to compat_inl *)
    admit.
Admitted.

(** Compatibility for T_Case:
    If scrutinee and branches are related, then case is related *)
Lemma compat_case : forall n Σ Γ γ1 γ2 T1 T2 T e x1 e1 x2 e2,
  exp_rel_n n Σ (TSum T1 T2) (apply_subst γ1 e) (apply_subst γ2 e) ->
  (forall v1 v2,
    val_rel_n n Σ T1 v1 v2 ->
    exp_rel_n n Σ T (apply_subst (subst_extend γ1 x1 v1) e1)
                    (apply_subst (subst_extend γ2 x1 v2) e1)) ->
  (forall v1 v2,
    val_rel_n n Σ T2 v1 v2 ->
    exp_rel_n n Σ T (apply_subst (subst_extend γ1 x2 v1) e2)
                    (apply_subst (subst_extend γ2 x2 v2) e2)) ->
  subst_rel_n n Σ Γ γ1 γ2 ->
  exp_rel_n n Σ T (ECase (apply_subst γ1 e) x1 (apply_subst (subst_extend γ1 x1 (EVar x1)) e1)
                                             x2 (apply_subst (subst_extend γ1 x2 (EVar x2)) e2))
                  (ECase (apply_subst γ2 e) x1 (apply_subst (subst_extend γ2 x1 (EVar x1)) e1)
                                             x2 (apply_subst (subst_extend γ2 x2 (EVar x2)) e2)).
Proof.
  intros n Σ Γ γ1 γ2 T1 T2 T e x1 e1 x2 e2 Hscr IH1 IH2 Hsubst.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Case analysis requires:
       1. Evaluating scrutinee to a sum value
       2. Using val_rel_n_sum_structure to get matching constructors
       3. Evaluating the appropriate branch
       This is handled in exp_rel_step1_case in NonInterference_v2.v *)
    admit.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR CONTROL (T_If, T_Let)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_If:
    If condition and branches are related, then if-expression is related *)
Lemma compat_if : forall n Σ T e1 e1' e2 e2' e3 e3',
  exp_rel_n n Σ TBool e1 e1' ->
  exp_rel_n n Σ T e2 e2' ->
  exp_rel_n n Σ T e3 e3' ->
  exp_rel_n n Σ T (EIf e1 e2 e3) (EIf e1' e2' e3').
Proof.
  intros n Σ T e1 e1' e2 e2' e3 e3' Hcond Hthen Helse.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    simpl in Hcond.
    specialize (Hcond Σ_cur st1 st2 ctx Hext Hstrel) as
      [v [v' [st1' [st2' [ctx' [Σ' [Hext' [Hstep1 [Hstep2 [Hv [Hv' [Hvrel Hstrel']]]]]]]]]]].
    (* v and v' are related booleans - must be the same boolean *)
    assert (Hbool : exists b, v = EBool b /\ v' = EBool b).
    { apply val_rel_n_bool_structure with n' Σ'. exact Hvrel. }
    destruct Hbool as [b [Heqv Heqv']]. subst v v'.
    (* Case split on b *)
    destruct b.
    + (* b = true: evaluate then branch *)
      assert (Hthen' : store_ty_extends Σ Σ').
      { apply store_ty_extends_trans with Σ_cur; assumption. }
      (* BLOCKED: Need to show (EIf (EBool true) e2 e3) --> e2 and combine *)
      admit.
    + (* b = false: evaluate else branch *)
      admit.
Admitted.

(** Compatibility for T_Let:
    If bound expression and body are related, then let is related *)
Lemma compat_let : forall n Σ Γ γ1 γ2 x T1 T2 e1 e2,
  exp_rel_n n Σ T1 (apply_subst γ1 e1) (apply_subst γ2 e1) ->
  (forall v1 v2,
    val_rel_n n Σ T1 v1 v2 ->
    subst_rel_n n Σ ((x, T1) :: Γ) (subst_extend γ1 x v1) (subst_extend γ2 x v2) ->
    exp_rel_n n Σ T2 (apply_subst (subst_extend γ1 x v1) e2)
                     (apply_subst (subst_extend γ2 x v2) e2)) ->
  subst_rel_n n Σ Γ γ1 γ2 ->
  exp_rel_n n Σ T2 (ELet x (apply_subst γ1 e1) (apply_subst (subst_extend γ1 x (EVar x)) e2))
                   (ELet x (apply_subst γ2 e1) (apply_subst (subst_extend γ2 x (EVar x)) e2)).
Proof.
  intros n Σ Γ γ1 γ2 x T1 T2 e1 e2 He1 IHe2 Hsubst.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Similar pattern to other compound expressions *)
    admit.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR EFFECTS (T_Perform, T_Handle)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Perform:
    If inner expression is related, then perform is related *)
Lemma compat_perform : forall n Σ T eff e e',
  exp_rel_n n Σ T e e' ->
  exp_rel_n n Σ T (EPerform eff e) (EPerform eff e').
Proof.
  intros n Σ T eff e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Effect handling requires modeling effect context *)
    admit.
Admitted.

(** Compatibility for T_Handle:
    If expression and handler are related, then handle is related *)
Lemma compat_handle : forall n Σ Γ γ1 γ2 T1 T2 e x h,
  exp_rel_n n Σ T1 (apply_subst γ1 e) (apply_subst γ2 e) ->
  (forall v1 v2,
    val_rel_n n Σ T1 v1 v2 ->
    exp_rel_n n Σ T2 (apply_subst (subst_extend γ1 x v1) h)
                     (apply_subst (subst_extend γ2 x v2) h)) ->
  subst_rel_n n Σ Γ γ1 γ2 ->
  exp_rel_n n Σ T2 (EHandle (apply_subst γ1 e) x (apply_subst (subst_extend γ1 x (EVar x)) h))
                   (EHandle (apply_subst γ2 e) x (apply_subst (subst_extend γ2 x (EVar x)) h)).
Proof.
  intros n Σ Γ γ1 γ2 T1 T2 e x h He IHh Hsubst.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Effect handling semantics *)
    admit.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR REFERENCES (T_Ref, T_Deref, T_Assign)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Ref:
    If initial value is related, then ref creation is related *)
Lemma compat_ref : forall n Σ T l e e',
  exp_rel_n n Σ T e e' ->
  exp_rel_n n Σ (TRef T l) (ERef e l) (ERef e' l).
Proof.
  intros n Σ T l e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Reference creation requires store extension *)
    admit.
Admitted.

(** Compatibility for T_Deref:
    If reference is related, then dereference is related *)
Lemma compat_deref : forall n Σ T l e e',
  exp_rel_n n Σ (TRef T l) e e' ->
  exp_rel_n n Σ T (EDeref e) (EDeref e').
Proof.
  intros n Σ T l e e' Href.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Dereference requires store relation *)
    admit.
Admitted.

(** Compatibility for T_Assign:
    If reference and value are related, then assignment is related *)
Lemma compat_assign : forall n Σ T l e1 e1' e2 e2',
  exp_rel_n n Σ (TRef T l) e1 e1' ->
  exp_rel_n n Σ T e2 e2' ->
  exp_rel_n n Σ TUnit (EAssign e1 e2) (EAssign e1' e2').
Proof.
  intros n Σ T l e1 e1' e2 e2' Href Hval.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Assignment requires store update *)
    admit.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR SECURITY (T_Classify, T_Declassify, T_Prove)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Classify:
    If value is related, then classified value is related *)
Lemma compat_classify : forall n Σ T e e',
  exp_rel_n n Σ T e e' ->
  exp_rel_n n Σ (TSecret T) (EClassify e) (EClassify e').
Proof.
  intros n Σ T e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    simpl in He.
    specialize (He Σ_cur st1 st2 ctx Hext Hstrel) as
      [v [v' [st1' [st2' [ctx' [Σ' [Hext' [Hstep1 [Hstep2 [Hv [Hv' [Hvrel Hstrel']]]]]]]]]]].
    exists (EClassify v), (EClassify v'), st1', st2', ctx', Σ'.
    repeat split.
    + exact Hext'.
    + (* (EClassify e, st1, ctx) -->* (EClassify v, st1', ctx') *)
      (* BLOCKED: Evaluation context lemma for EClassify *)
      admit.
    + admit.
    + constructor. exact Hv.
    + constructor. exact Hv'.
    + (* val_rel_n n' Σ' (TSecret T) (EClassify v) (EClassify v') *)
      (* For TSecret, val_rel_at_type_fo is True, so this should be straightforward *)
      admit.
    + exact Hstrel'.
Admitted.

(** Compatibility for T_Declassify:
    If secret value and proof are related, then declassification is related *)
Lemma compat_declassify : forall n Σ T e1 e1' e2 e2',
  exp_rel_n n Σ (TSecret T) e1 e1' ->
  exp_rel_n n Σ (TProof (TSecret T)) e2 e2' ->
  exp_rel_n n Σ T (EDeclassify e1 e2) (EDeclassify e1' e2').
Proof.
  intros n Σ T e1 e1' e2 e2' Hsecret Hproof.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Declassification requires proof validation *)
    admit.
Admitted.

(** Compatibility for T_Prove:
    If value is related, then proof is related *)
Lemma compat_prove : forall n Σ T e e',
  exp_rel_n n Σ T e e' ->
  exp_rel_n n Σ (TProof T) (EProve e) (EProve e').
Proof.
  intros n Σ T e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
    simpl in He.
    specialize (He Σ_cur st1 st2 ctx Hext Hstrel) as
      [v [v' [st1' [st2' [ctx' [Σ' [Hext' [Hstep1 [Hstep2 [Hv [Hv' [Hvrel Hstrel']]]]]]]]]]].
    exists (EProve v), (EProve v'), st1', st2', ctx', Σ'.
    repeat split.
    + exact Hext'.
    + (* BLOCKED: Evaluation context lemma for EProve *)
      admit.
    + admit.
    + constructor. exact Hv.
    + constructor. exact Hv'.
    + (* val_rel_n n' Σ' (TProof T) (EProve v) (EProve v') *)
      admit.
    + exact Hstrel'.
Admitted.

(** ------------------------------------------------------------------------
    COMPATIBILITY LEMMAS FOR CAPABILITIES (T_Require, T_Grant)
    ------------------------------------------------------------------------ *)

(** Compatibility for T_Require:
    If body is related, then require is related *)
Lemma compat_require : forall n Σ T eff e e',
  exp_rel_n n Σ T e e' ->
  exp_rel_n n Σ T (ERequire eff e) (ERequire eff e').
Proof.
  intros n Σ T eff e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Capability checking semantics *)
    admit.
Admitted.

(** Compatibility for T_Grant:
    If body is related, then grant is related *)
Lemma compat_grant : forall n Σ T eff e e',
  exp_rel_n n Σ T e e' ->
  exp_rel_n n Σ T (EGrant eff e) (EGrant eff e').
Proof.
  intros n Σ T eff e e' He.
  destruct n as [| n'].
  - simpl. exact I.
  - (* BLOCKED: Capability granting semantics *)
    admit.
Admitted.

(** ========================================================================
    SECTION 3: FUNDAMENTAL THEOREM
    ========================================================================

    The Fundamental Theorem states that well-typed expressions preserve
    the logical relation under related substitutions.

    Theorem: If Γ; Σ; Δ ⊢ e : T @ ε and γ1 ~ γ2 : Γ, then γ1(e) ~ γ2(e) : T.
*)

(** The Fundamental Theorem of Logical Relations for RIINA *)
Theorem fundamental_theorem : forall Γ Σ Δ e T ε,
  has_type Γ Σ Δ e T ε ->
  forall n γ1 γ2,
    subst_rel_n n Σ Γ γ1 γ2 ->
    exp_rel_n n Σ T (apply_subst γ1 e) (apply_subst γ2 e).
Proof.
  intros Γ Σ Δ e T ε Hty.
  induction Hty; intros n γ1 γ2 Hsubst.

  - (* T_Unit *)
    simpl. apply compat_unit.

  - (* T_Bool *)
    simpl. apply compat_bool.

  - (* T_Int *)
    simpl. apply compat_int.

  - (* T_String *)
    simpl. apply compat_string.

  - (* T_Loc *)
    simpl. apply compat_loc with T sl.
    exact H.

  - (* T_Var *)
    simpl. unfold subst_rel_n in Hsubst.
    destruct n as [| n'].
    + simpl. exact I.
    + simpl. intros Σ_cur st1 st2 ctx Hext Hstrel.
      specialize (Hsubst x T H) as Hvrel.
      assert (Hv : value (γ1 x) /\ value (γ2 x)).
      { apply val_rel_n_value with (S n') Σ T. exact Hvrel. }
      destruct Hv as [Hv1 Hv2].
      exists (γ1 x), (γ2 x), st1, st2, ctx, Σ_cur.
      repeat split.
      * apply store_ty_extends_refl.
      * apply MS_Refl.
      * apply MS_Refl.
      * exact Hv1.
      * exact Hv2.
      * apply val_rel_n_mono with (S n').
        -- lia.
        -- (* BLOCKED: Need store extension weakening *)
           admit.
      * exact Hstrel.

  - (* T_Lam *)
    simpl apply_subst.
    apply compat_lam with Γ.
    + intros v1 v2 Hvrel Hsubst'.
      (* Use IH on body with extended substitution *)
      apply IHHty.
      exact Hsubst'.
    + exact Hsubst.

  - (* T_App *)
    simpl apply_subst.
    apply compat_app with T1 ε.
    + apply IHHty1. exact Hsubst.
    + apply IHHty2. exact Hsubst.

  - (* T_Pair *)
    simpl apply_subst.
    apply compat_pair.
    + apply IHHty1. exact Hsubst.
    + apply IHHty2. exact Hsubst.

  - (* T_Fst *)
    simpl apply_subst.
    apply compat_fst with T2.
    apply IHHty. exact Hsubst.

  - (* T_Snd *)
    simpl apply_subst.
    apply compat_snd with T1.
    apply IHHty. exact Hsubst.

  - (* T_Inl *)
    simpl apply_subst.
    apply compat_inl.
    apply IHHty. exact Hsubst.

  - (* T_Inr *)
    simpl apply_subst.
    apply compat_inr.
    apply IHHty. exact Hsubst.

  - (* T_Case *)
    simpl apply_subst.
    apply compat_case with Γ T1 T2.
    + apply IHHty1. exact Hsubst.
    + intros v1 v2 Hvrel.
      apply IHHty2.
      apply subst_rel_n_extend; [exact Hsubst | exact Hvrel].
    + intros v1 v2 Hvrel.
      apply IHHty3.
      apply subst_rel_n_extend; [exact Hsubst | exact Hvrel].
    + exact Hsubst.

  - (* T_If *)
    simpl apply_subst.
    apply compat_if.
    + apply IHHty1. exact Hsubst.
    + apply IHHty2. exact Hsubst.
    + apply IHHty3. exact Hsubst.

  - (* T_Let *)
    simpl apply_subst.
    apply compat_let with Γ T1.
    + apply IHHty1. exact Hsubst.
    + intros v1 v2 Hvrel Hsubst'.
      apply IHHty2. exact Hsubst'.
    + exact Hsubst.

  - (* T_Perform *)
    simpl apply_subst.
    apply compat_perform.
    apply IHHty. exact Hsubst.

  - (* T_Handle *)
    simpl apply_subst.
    apply compat_handle with Γ T1.
    + apply IHHty1. exact Hsubst.
    + intros v1 v2 Hvrel.
      apply IHHty2.
      apply subst_rel_n_extend; [exact Hsubst | exact Hvrel].
    + exact Hsubst.

  - (* T_Ref *)
    simpl apply_subst.
    apply compat_ref.
    apply IHHty. exact Hsubst.

  - (* T_Deref *)
    simpl apply_subst.
    apply compat_deref with l.
    apply IHHty. exact Hsubst.

  - (* T_Assign *)
    simpl apply_subst.
    apply compat_assign with T l.
    + apply IHHty1. exact Hsubst.
    + apply IHHty2. exact Hsubst.

  - (* T_Classify *)
    simpl apply_subst.
    apply compat_classify.
    apply IHHty. exact Hsubst.

  - (* T_Declassify *)
    simpl apply_subst.
    apply compat_declassify.
    + apply IHHty1. exact Hsubst.
    + apply IHHty2. exact Hsubst.

  - (* T_Prove *)
    simpl apply_subst.
    apply compat_prove.
    apply IHHty. exact Hsubst.

  - (* T_Require *)
    simpl apply_subst.
    apply compat_require.
    apply IHHty. exact Hsubst.

  - (* T_Grant *)
    simpl apply_subst.
    apply compat_grant.
    apply IHHty. exact Hsubst.
Admitted.

(** ========================================================================
    SECTION 4: COROLLARY - CLOSED WELL-TYPED EXPRESSIONS ARE RELATED
    ========================================================================

    For closed expressions (empty Γ), we don't need substitutions.
*)

(** Closed well-typed expressions are in the expression relation *)
Corollary fundamental_closed : forall Σ Δ e T ε,
  has_type nil Σ Δ e T ε ->
  forall n, exp_rel_n n Σ T e e.
Proof.
  intros Σ Δ e T ε Hty n.
  assert (Hsubst : subst_rel_n n Σ nil subst_id subst_id).
  { apply subst_rel_n_empty. }
  assert (Heq : apply_subst subst_id e = e).
  { (* BLOCKED: Requires lemma that subst_id is identity *)
    admit. }
  specialize (fundamental_theorem nil Σ Δ e T ε Hty n subst_id subst_id Hsubst).
  rewrite Heq, Heq.
  exact H.
Admitted.

(** ========================================================================
    SECTION 5: NON-INTERFERENCE AS A CONSEQUENCE
    ========================================================================

    Non-interference follows from the Fundamental Theorem:
    If an expression doesn't depend on secret inputs, running it with
    different secrets produces indistinguishable results.
*)

(** Non-interference: equivalent public inputs produce equivalent outputs *)
Theorem non_interference : forall Σ Δ e T ε,
  has_type nil Σ Δ e T ε ->
  forall n st1 st2 ctx,
    store_rel_n n Σ st1 st2 ->
    exists v1 v2 st1' st2' ctx' Σ',
      store_ty_extends Σ Σ' /\
      (e, st1, ctx) -->* (v1, st1', ctx') /\
      (e, st2, ctx) -->* (v2, st2', ctx') /\
      (n > 0 -> val_rel_n (n-1) Σ' T v1 v2) /\
      (n > 0 -> store_rel_n (n-1) Σ' st1' st2').
Proof.
  intros Σ Δ e T ε Hty n st1 st2 ctx Hstrel.
  destruct n as [| n'].
  - (* n = 0: weak result, just termination *)
    (* BLOCKED: Requires progress/termination lemma *)
    admit.
  - (* n = S n': use fundamental theorem *)
    assert (Hexp : exp_rel_n (S n') Σ T e e).
    { apply fundamental_closed with Δ ε. exact Hty. }
    simpl in Hexp.
    specialize (Hexp Σ st1 st2 ctx (store_ty_extends_refl Σ) Hstrel) as
      [v1 [v2 [st1' [st2' [ctx' [Σ' [Hext [Hstep1 [Hstep2 [Hv1 [Hv2 [Hvrel Hstrel']]]]]]]]]]]].
    exists v1, v2, st1', st2', ctx', Σ'.
    repeat split.
    + exact Hext.
    + exact Hstep1.
    + exact Hstep2.
    + intros _. simpl. exact Hvrel.
    + intros _. simpl. exact Hstrel'.
Admitted.

(** ========================================================================
    SECTION 6: SUMMARY AND ADMISSION NOTES
    ========================================================================

    FULLY PROVEN:
    ✓ subst_rel_n_empty
    ✓ subst_rel_n_extend
    ✓ subst_rel_n_mono
    ✓ compat_unit
    ✓ compat_bool (base case structure)
    ✓ compat_int (base case structure)
    ✓ compat_string (base case structure)
    ✓ compat_loc (base case structure)

    ADMITTED WITH PARTIAL PROOFS:
    The following lemmas are admitted with clear blockers identified:

    1. compat_var: BLOCKED on store_ty_extends weakening for val_rel_n
       - Requires: val_rel_n_store_ext lemma

    2. compat_lam: BLOCKED on proving lambda values are related
       - Requires: Strong normalization for function bodies

    3. compat_app: BLOCKED on combining function and argument evaluation
       - Requires: Evaluation composition lemma

    4. compat_pair, compat_fst, compat_snd: BLOCKED on pair evaluation
       - Requires: Evaluation context lemmas for products

    5. compat_inl, compat_inr, compat_case: BLOCKED on sum evaluation
       - Requires: Evaluation context lemmas for sums

    6. compat_if: BLOCKED on conditional evaluation
       - Requires: Boolean evaluation composition

    7. compat_let, compat_handle: BLOCKED on binding evaluation
       - Requires: Substitution lemmas

    8. compat_ref, compat_deref, compat_assign: BLOCKED on store operations
       - Requires: Store relation preservation lemmas

    9. compat_classify, compat_declassify, compat_prove: BLOCKED on security ops
       - Requires: Security typing lemmas

    10. compat_perform, compat_require, compat_grant: BLOCKED on effects
        - Requires: Effect handling semantics

    INTEGRATION WITH NonInterference_v2.v:
    - This file provides the infrastructure to fill the admit at line 1110
    - The val_rel_n_step_up_by_type axiom requires fundamental_theorem
    - Once these admits are resolved, val_rel_n_step_up_by_type can be proven

    RECOMMENDED NEXT STEPS:
    1. Prove val_rel_n_store_ext (store extension weakening)
    2. Prove evaluation context lemmas for each expression form
    3. Prove substitution lemmas for binding constructs
    4. Complete strong normalization proof for function types
    5. Fill remaining admits in compatibility lemmas

    ========================================================================
*)

(** End of FundamentalTheorem.v *)
