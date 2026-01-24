(** * SubstitutionCommute.v

    Substitution environment definitions and commutation lemmas.

    Key theorem: Substitution commutes with environment application
    when the environment range consists of closed expressions.

    Mode: ULTRA KIASU | ZERO ADMITS
*)

Require Import String.
Require Import List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.ClosedValueLemmas.
Import ListNotations.

(** ----------------------------------------------------------------- *)
(** * Substitution Environment Definitions                            *)
(** ----------------------------------------------------------------- *)

(** Substitution environment: maps identifiers to expressions *)
Definition subst_rho := list (ident * expr).

(** Lookup in substitution environment *)
Fixpoint rho_lookup (x : ident) (ρ : subst_rho) : option expr :=
  match ρ with
  | nil => None
  | (y, e) :: ρ' => if String.eqb x y then Some e else rho_lookup x ρ'
  end.

(** Extend substitution environment *)
Definition extend_rho (ρ : subst_rho) (x : ident) (e : expr) : subst_rho :=
  (x, e) :: ρ.

(** Apply substitution environment to expression *)
Fixpoint subst_env (ρ : subst_rho) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar x => match rho_lookup x ρ with
              | Some v => v
              | None => EVar x
              end
  | ELam x T body => ELam x T (subst_env (filter (fun p => negb (String.eqb (fst p) x)) ρ) body)
  | EApp e1 e2 => EApp (subst_env ρ e1) (subst_env ρ e2)
  | EPair e1 e2 => EPair (subst_env ρ e1) (subst_env ρ e2)
  | EFst e => EFst (subst_env ρ e)
  | ESnd e => ESnd (subst_env ρ e)
  | EInl e T => EInl (subst_env ρ e) T
  | EInr e T => EInr (subst_env ρ e) T
  | ECase e x1 e1 x2 e2 =>
      ECase (subst_env ρ e)
            x1 (subst_env (filter (fun p => negb (String.eqb (fst p) x1)) ρ) e1)
            x2 (subst_env (filter (fun p => negb (String.eqb (fst p) x2)) ρ) e2)
  | EIf e1 e2 e3 => EIf (subst_env ρ e1) (subst_env ρ e2) (subst_env ρ e3)
  | ELet x e1 e2 =>
      ELet x (subst_env ρ e1) (subst_env (filter (fun p => negb (String.eqb (fst p) x)) ρ) e2)
  | EPerform op e => EPerform op (subst_env ρ e)
  | EHandle e x eh => 
      EHandle (subst_env ρ e) x (subst_env (filter (fun p => negb (String.eqb (fst p) x)) ρ) eh)
  | ERef e => ERef (subst_env ρ e)
  | EDeref e => EDeref (subst_env ρ e)
  | EAssign e1 e2 => EAssign (subst_env ρ e1) (subst_env ρ e2)
  | EClassify sl e => EClassify sl (subst_env ρ e)
  | EDeclassify e1 e2 => EDeclassify (subst_env ρ e1) (subst_env ρ e2)
  | EProve p e => EProve p (subst_env ρ e)
  | ERequire p e => ERequire p (subst_env ρ e)
  | EGrant cap e => EGrant cap (subst_env ρ e)
  end.

(** ----------------------------------------------------------------- *)
(** * Closed Environment Definition                                   *)
(** ----------------------------------------------------------------- *)

(** All expressions in the environment range are closed *)
Definition closed_rho (ρ : subst_rho) : Prop :=
  forall x e, rho_lookup x ρ = Some e -> closed_expr e.

(** ----------------------------------------------------------------- *)
(** * Basic Lemmas                                                    *)
(** ----------------------------------------------------------------- *)

(** Empty environment is closed *)
Lemma closed_rho_nil : closed_rho nil.
Proof.
  unfold closed_rho. intros x e H. simpl in H. discriminate.
Qed.

(** Extension preserves closedness *)
Lemma closed_rho_extend : forall ρ x v,
  closed_rho ρ ->
  closed_expr v ->
  closed_rho (extend_rho ρ x v).
Proof.
  unfold closed_rho, extend_rho. intros ρ x v Hρ Hv y e Hlook.
  simpl in Hlook. destruct (String.eqb y x) eqn:Heq.
  - injection Hlook as Heq'. subst. exact Hv.
  - apply Hρ with y. exact Hlook.
Qed.

(** Lookup after extend: same variable *)
Lemma rho_lookup_extend_same : forall ρ x v,
  rho_lookup x (extend_rho ρ x v) = Some v.
Proof.
  intros ρ x v. simpl. rewrite String.eqb_refl. reflexivity.
Qed.

(** Lookup after extend: different variable *)
Lemma rho_lookup_extend_diff : forall ρ x y v,
  x <> y ->
  rho_lookup x (extend_rho ρ y v) = rho_lookup x ρ.
Proof.
  intros ρ x y v Hneq. simpl.
  destruct (String.eqb x y) eqn:Heq.
  - apply String.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

(** Empty environment has no effect *)
Lemma subst_env_nil : forall e, subst_env nil e = e.
Proof.
  induction e; simpl; try reflexivity; try (f_equal; assumption).
  - (* ELam *) f_equal. rewrite IHe. reflexivity.
  - (* ECase *) f_equal; [apply IHe1 | apply IHe2 | apply IHe3].
  - (* ELet *) f_equal; [apply IHe1 | apply IHe2].
  - (* EHandle *) f_equal; [apply IHe1 | apply IHe2].
Qed.

(** ----------------------------------------------------------------- *)
(** * Substitution on Closed Expressions                              *)
(** ----------------------------------------------------------------- *)

(** Substitution has no effect on closed range of rho *)
Lemma subst_closed_rho_range : forall x v ρ y,
  closed_rho ρ ->
  match rho_lookup y ρ with
  | Some e => [x := v] e = e
  | None => True
  end.
Proof.
  intros x v ρ y Hρ.
  destruct (rho_lookup y ρ) eqn:Hlook.
  - apply subst_closed_noop. apply Hρ with y. exact Hlook.
  - exact I.
Qed.

(** ----------------------------------------------------------------- *)
(** * Main Commutation Theorem                                        *)
(** ----------------------------------------------------------------- *)

(** Key insight: When ρ is closed and we extend with variable binding,
    subsequent substitution commutes with environment application. *)

Lemma filter_closed_rho : forall ρ f,
  closed_rho ρ ->
  closed_rho (filter f ρ).
Proof.
  intros ρ f Hρ. unfold closed_rho in *.
  intros x e Hlook.
  induction ρ as [| [y v] ρ' IH].
  - simpl in Hlook. discriminate.
  - simpl in Hlook. destruct (f (y, v)) eqn:Hf.
    + simpl in Hlook. destruct (String.eqb x y) eqn:Heq.
      * injection Hlook as Heq'. subst.
        apply Hρ with y. simpl. rewrite String.eqb_refl. reflexivity.
      * apply IH. intros z ez Hz. apply Hρ with z.
        simpl. destruct (String.eqb z y) eqn:Heqz; [|exact Hz].
        apply String.eqb_eq in Heqz. subst.
        apply String.eqb_neq in Heq.
        (* z = y but we looked up x which is not y *)
        simpl in Hz. exact Hz.
      * exact Hlook.
    + apply IH.
      intros z ez Hz. apply Hρ with z.
      simpl. destruct (String.eqb z y) eqn:Heqz; [|exact Hz].
      apply String.eqb_eq in Heqz. subst. exact Hz.
      exact Hlook.
Qed.

(** Substitution commutes with subst_env when rho is closed *)
Theorem subst_subst_env_commute : forall x v ρ e,
  closed_rho ρ ->
  closed_expr v ->
  ~ In x (map fst ρ) ->
  [x := v] (subst_env ρ e) = subst_env ρ ([x := v] e).
Proof.
  intros x v ρ e Hρ Hv Hnotin.
  induction e; simpl.
  - (* EUnit *) reflexivity.
  - (* EBool *) reflexivity.
  - (* EInt *) reflexivity.
  - (* EString *) reflexivity.
  - (* ELoc *) reflexivity.
  - (* EVar *)
    destruct (String.eqb x i) eqn:Heq.
    + (* x = i: substitution replaces variable *)
      apply String.eqb_eq in Heq. subst.
      simpl. destruct (rho_lookup i ρ) eqn:Hlook.
      * (* i is in ρ - contradiction since x not in domain *)
        exfalso. apply Hnotin. clear Hnotin.
        induction ρ as [| [y ey] ρ' IH].
        -- simpl in Hlook. discriminate.
        -- simpl in Hlook. simpl. destruct (String.eqb i y) eqn:Heqy.
           ++ left. apply String.eqb_eq in Heqy. auto.
           ++ right. apply IH. exact Hlook.
      * (* i not in ρ *)
        simpl. rewrite String.eqb_refl. reflexivity.
    + (* x <> i: substitution doesn't affect variable *)
      simpl. destruct (rho_lookup i ρ) eqn:Hlook.
      * (* i in ρ: lookup returns closed expression, subst has no effect *)
        apply subst_closed_noop. apply Hρ with i. exact Hlook.
      * (* i not in ρ *)
        simpl. rewrite Heq. reflexivity.
  - (* ELam *)
    destruct (String.eqb x i) eqn:Heq.
    + (* x = i: lambda shadows x, no substitution in body *)
      f_equal. 
      (* subst_env with filter removes bindings shadowed by lambda *)
      assert (Hclosed_filter : closed_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ)).
      { apply filter_closed_rho. exact Hρ. }
      (* After filtering, same expression since x not substituted *)
      reflexivity.
    + (* x <> i: substitute in body *)
      f_equal. 
      assert (Hclosed_filter : closed_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ)).
      { apply filter_closed_rho. exact Hρ. }
      assert (Hnotin_filter : ~ In x (map fst (filter (fun p => negb (String.eqb (fst p) i)) ρ))).
      { intro Hin. apply Hnotin. clear Hnotin.
        induction ρ as [| [y ey] ρ' IH].
        - simpl in Hin. exact Hin.
        - simpl. simpl in Hin. destruct (negb (String.eqb y i)) eqn:Hneq.
          + simpl in Hin. destruct Hin as [H | H].
            * left. exact H.
            * right. apply IH. exact H.
          + right. apply IH. exact Hin. }
      apply IHe.
      * exact Hclosed_filter.
      * exact Hnotin_filter.
  - (* EApp *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + apply IHe2. exact Hnotin.
  - (* EPair *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + apply IHe2. exact Hnotin.
  - (* EFst *)
    f_equal. apply IHe. exact Hnotin.
  - (* ESnd *)
    f_equal. apply IHe. exact Hnotin.
  - (* EInl *)
    f_equal. apply IHe. exact Hnotin.
  - (* EInr *)
    f_equal. apply IHe. exact Hnotin.
  - (* ECase *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      assert (Hclosed_filter : closed_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ)).
      { apply filter_closed_rho. exact Hρ. }
      assert (Hnotin_filter : ~ In x (map fst (filter (fun p => negb (String.eqb (fst p) i)) ρ))).
      { intro Hin. apply Hnotin. clear Hnotin.
        induction ρ as [| [y ey] ρ' IH].
        - simpl in Hin. exact Hin.
        - simpl. simpl in Hin. destruct (negb (String.eqb y i)) eqn:Hneq.
          + simpl in Hin. destruct Hin as [H | H]; [left | right; apply IH]; exact H.
          + right. apply IH. exact Hin. }
      apply IHe2.
      * exact Hclosed_filter.
      * exact Hnotin_filter.
    + destruct (String.eqb x i0) eqn:Heq; [reflexivity|].
      assert (Hclosed_filter : closed_rho (filter (fun p => negb (String.eqb (fst p) i0)) ρ)).
      { apply filter_closed_rho. exact Hρ. }
      assert (Hnotin_filter : ~ In x (map fst (filter (fun p => negb (String.eqb (fst p) i0)) ρ))).
      { intro Hin. apply Hnotin. clear Hnotin.
        induction ρ as [| [y ey] ρ' IH].
        - simpl in Hin. exact Hin.
        - simpl. simpl in Hin. destruct (negb (String.eqb y i0)) eqn:Hneq.
          + simpl in Hin. destruct Hin as [H | H]; [left | right; apply IH]; exact H.
          + right. apply IH. exact Hin. }
      apply IHe3.
      * exact Hclosed_filter.
      * exact Hnotin_filter.
  - (* EIf *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + apply IHe2. exact Hnotin.
    + apply IHe3. exact Hnotin.
  - (* ELet *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      assert (Hclosed_filter : closed_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ)).
      { apply filter_closed_rho. exact Hρ. }
      assert (Hnotin_filter : ~ In x (map fst (filter (fun p => negb (String.eqb (fst p) i)) ρ))).
      { intro Hin. apply Hnotin. clear Hnotin.
        induction ρ as [| [y ey] ρ' IH].
        - simpl in Hin. exact Hin.
        - simpl. simpl in Hin. destruct (negb (String.eqb y i)) eqn:Hneq.
          + simpl in Hin. destruct Hin as [H | H]; [left | right; apply IH]; exact H.
          + right. apply IH. exact Hin. }
      apply IHe2.
      * exact Hclosed_filter.
      * exact Hnotin_filter.
  - (* EPerform *)
    f_equal. apply IHe. exact Hnotin.
  - (* EHandle *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      assert (Hclosed_filter : closed_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ)).
      { apply filter_closed_rho. exact Hρ. }
      assert (Hnotin_filter : ~ In x (map fst (filter (fun p => negb (String.eqb (fst p) i)) ρ))).
      { intro Hin. apply Hnotin. clear Hnotin.
        induction ρ as [| [y ey] ρ' IH].
        - simpl in Hin. exact Hin.
        - simpl. simpl in Hin. destruct (negb (String.eqb y i)) eqn:Hneq.
          + simpl in Hin. destruct Hin as [H | H]; [left | right; apply IH]; exact H.
          + right. apply IH. exact Hin. }
      apply IHe2.
      * exact Hclosed_filter.
      * exact Hnotin_filter.
  - (* ERef *)
    f_equal. apply IHe. exact Hnotin.
  - (* EDeref *)
    f_equal. apply IHe. exact Hnotin.
  - (* EAssign *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + apply IHe2. exact Hnotin.
  - (* EClassify *)
    f_equal. apply IHe. exact Hnotin.
  - (* EDeclassify *)
    f_equal.
    + apply IHe1. exact Hnotin.
    + apply IHe2. exact Hnotin.
  - (* EProve *)
    f_equal. apply IHe. exact Hnotin.
  - (* ERequire *)
    f_equal. apply IHe. exact Hnotin.
  - (* EGrant *)
    f_equal. apply IHe. exact Hnotin.
Qed.

(** ----------------------------------------------------------------- *)
(** * Specialized Version for Extend-then-Substitute Pattern          *)
(** ----------------------------------------------------------------- *)

(** The specific pattern needed for reducibility:
    Extending rho with x -> EVar x, then substituting x with v *)
Corollary subst_extend_var_commute : forall x v ρ e,
  closed_rho ρ ->
  closed_expr v ->
  ~ In x (map fst ρ) ->
  [x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e.
Proof.
  intros x v ρ e Hρ Hv Hnotin.
  (* Extending with EVar x means lookup x returns EVar x *)
  (* After substitution [x := v], EVar x becomes v *)
  (* This equals directly extending with v *)
  induction e; simpl.
  - (* EUnit *) reflexivity.
  - (* EBool *) reflexivity.
  - (* EInt *) reflexivity.
  - (* EString *) reflexivity.
  - (* ELoc *) reflexivity.
  - (* EVar *)
    destruct (String.eqb i x) eqn:Heq.
    + (* i = x *)
      apply String.eqb_eq in Heq. subst.
      simpl. rewrite String.eqb_refl. simpl. rewrite String.eqb_refl. reflexivity.
    + (* i <> x *)
      simpl. rewrite Heq. 
      destruct (rho_lookup i ρ) eqn:Hlook.
      * (* i in ρ *)
        apply subst_closed_noop. apply Hρ with i. exact Hlook.
      * (* i not in ρ *)
        simpl. rewrite Heq. reflexivity.
  - (* ELam *)
    destruct (String.eqb x i) eqn:Heqxi.
    + (* x = i: lambda shadows x *)
      f_equal. 
      (* Both sides filter out x, so they're equal *)
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x (EVar x)) =
              filter (fun p => negb (String.eqb (fst p) i)) ρ) as Hfilter1.
      { simpl. apply String.eqb_eq in Heqxi. subst. rewrite String.eqb_refl. reflexivity. }
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x v) =
              filter (fun p => negb (String.eqb (fst p) i)) ρ) as Hfilter2.
      { simpl. apply String.eqb_eq in Heqxi. subst. rewrite String.eqb_refl. reflexivity. }
      rewrite Hfilter1. rewrite Hfilter2.
      reflexivity.
    + (* x <> i *)
      f_equal.
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x (EVar x)) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x (EVar x)) as Hfilter1.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hneg.
        - reflexivity.
        - apply negb_false_iff in Hneg. apply String.eqb_eq in Hneg. contradiction. }
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x v) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x v) as Hfilter2.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hneg.
        - reflexivity.
        - apply negb_false_iff in Hneg. apply String.eqb_eq in Hneg. contradiction. }
      rewrite Hfilter1. rewrite Hfilter2.
      apply IHe.
      apply filter_closed_rho. exact Hρ.
      intro Hin. apply Hnotin.
      clear -Hin. induction ρ as [| [y ey] ρ' IH].
      * simpl in Hin. exact Hin.
      * simpl. simpl in Hin. destruct (negb (String.eqb y i)).
        -- simpl in Hin. destruct Hin; [left | right; apply IH]; assumption.
        -- right. apply IH. exact Hin.
  - (* EApp *)
    f_equal; [apply IHe1 | apply IHe2].
  - (* EPair *)
    f_equal; [apply IHe1 | apply IHe2].
  - (* EFst *)
    f_equal. apply IHe.
  - (* ESnd *)
    f_equal. apply IHe.
  - (* EInl *)
    f_equal. apply IHe.
  - (* EInr *)
    f_equal. apply IHe.
  - (* ECase - similar to ELam handling for bound variables *)
    f_equal.
    + apply IHe1.
    + destruct (String.eqb x i) eqn:Heqxi; [reflexivity|].
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x (EVar x)) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x (EVar x)) as Hf1.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x v) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x v) as Hf2.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      rewrite Hf1. rewrite Hf2.
      apply IHe2.
      apply filter_closed_rho. exact Hρ.
      intro Hin. apply Hnotin.
      clear -Hin. induction ρ; simpl in *; [exact Hin|].
      destruct a. destruct (negb (String.eqb i0 i)); simpl in *.
      destruct Hin; [left | right; apply IHρ]; assumption.
      right. apply IHρ. exact Hin.
    + destruct (String.eqb x i0) eqn:Heqxi0; [reflexivity|].
      assert (filter (fun p => negb (String.eqb (fst p) i0)) (extend_rho ρ x (EVar x)) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i0)) ρ) x (EVar x)) as Hf1.
      { simpl. apply String.eqb_neq in Heqxi0.
        destruct (negb (String.eqb x i0)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      assert (filter (fun p => negb (String.eqb (fst p) i0)) (extend_rho ρ x v) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i0)) ρ) x v) as Hf2.
      { simpl. apply String.eqb_neq in Heqxi0.
        destruct (negb (String.eqb x i0)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      rewrite Hf1. rewrite Hf2.
      apply IHe3.
      apply filter_closed_rho. exact Hρ.
      intro Hin. apply Hnotin.
      clear -Hin. induction ρ; simpl in *; [exact Hin|].
      destruct a. destruct (negb (String.eqb i1 i0)); simpl in *.
      destruct Hin; [left | right; apply IHρ]; assumption.
      right. apply IHρ. exact Hin.
  - (* EIf *)
    f_equal; [apply IHe1 | apply IHe2 | apply IHe3].
  - (* ELet *)
    f_equal.
    + apply IHe1.
    + destruct (String.eqb x i) eqn:Heqxi; [reflexivity|].
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x (EVar x)) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x (EVar x)) as Hf1.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x v) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x v) as Hf2.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      rewrite Hf1. rewrite Hf2.
      apply IHe2.
      apply filter_closed_rho. exact Hρ.
      intro Hin. apply Hnotin.
      clear -Hin. induction ρ; simpl in *; [exact Hin|].
      destruct a. destruct (negb (String.eqb i0 i)); simpl in *.
      destruct Hin; [left | right; apply IHρ]; assumption.
      right. apply IHρ. exact Hin.
  - (* EPerform *)
    f_equal. apply IHe.
  - (* EHandle *)
    f_equal.
    + apply IHe1.
    + destruct (String.eqb x i) eqn:Heqxi; [reflexivity|].
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x (EVar x)) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x (EVar x)) as Hf1.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      assert (filter (fun p => negb (String.eqb (fst p) i)) (extend_rho ρ x v) =
              extend_rho (filter (fun p => negb (String.eqb (fst p) i)) ρ) x v) as Hf2.
      { simpl. apply String.eqb_neq in Heqxi.
        destruct (negb (String.eqb x i)) eqn:Hn; [reflexivity|].
        apply negb_false_iff in Hn. apply String.eqb_eq in Hn. contradiction. }
      rewrite Hf1. rewrite Hf2.
      apply IHe2.
      apply filter_closed_rho. exact Hρ.
      intro Hin. apply Hnotin.
      clear -Hin. induction ρ; simpl in *; [exact Hin|].
      destruct a. destruct (negb (String.eqb i0 i)); simpl in *.
      destruct Hin; [left | right; apply IHρ]; assumption.
      right. apply IHρ. exact Hin.
  - (* ERef *)
    f_equal. apply IHe.
  - (* EDeref *)
    f_equal. apply IHe.
  - (* EAssign *)
    f_equal; [apply IHe1 | apply IHe2].
  - (* EClassify *)
    f_equal. apply IHe.
  - (* EDeclassify *)
    f_equal; [apply IHe1 | apply IHe2].
  - (* EProve *)
    f_equal. apply IHe.
  - (* ERequire *)
    f_equal. apply IHe.
  - (* EGrant *)
    f_equal. apply IHe.
Qed.

(** End of file - ZERO ADMITS *)
