# RIINA Strong Normalization Proof: COMPLETE Analysis and Fix

## MISSION CRITICAL OBJECTIVE

Eliminate the 2 admits in `ReducibilityFull.v` (lines 546 and 627) by providing EXACT, COMPILABLE Coq code that:
1. Does NOT modify `SN_Closure.v`
2. Does NOT break any existing proofs
3. Compiles successfully with `make`
4. Enables `well_typed_SN` theorem to remain valid

---

## ROLE AND EXPERTISE REQUIRED

You are an expert in:
- Coq proof assistant (version 8.18.0)
- Type theory and logical relations
- Tait's reducibility method / Girard's proof technique
- Strong normalization proofs for typed lambda calculi
- Substitution lemmas and preservation theorems

---

## ABSOLUTE CONSTRAINTS

### DO NOT:
1. Modify `properties/SN_Closure.v` (all 553 lines are proven with `Qed`)
2. Change exported lemma signatures that other files depend on
3. Introduce new `admit`, `Admitted`, or `Axiom`
4. Change the `Reducible` definition (it must remain `SN_expr`)
5. Break the compilation of any file
6. Provide partial or sketch proofs
7. Use tactics that don't exist in Coq 8.18.0

### YOU MUST:
1. Only modify `termination/ReducibilityFull.v`
2. Provide EXACT Coq code (copy-paste ready, syntactically correct)
3. Eliminate BOTH admits at lines 546 and 627
4. Preserve the `well_typed_SN` theorem
5. Ensure `make termination/ReducibilityFull.vo` succeeds
6. Ensure `make properties/NonInterference_v2.vo` still works after

---

## COMPLETE FILE CONTENTS

### FILE 1: properties/SN_Closure.v (COMPLETE - 553 LINES - READ ONLY)

```coq
(** * SN Closure Lemmas

    This file proves that SN (strong normalization) is closed under
    all syntactic forms. These are the key lemmas needed for the
    fundamental theorem.

    The main technique is: if all immediate subterms are SN, and
    all one-step reducts are SN, then the compound term is SN.

    Mode: ULTRA KIASU | ZERO ADMITS TARGET
    Date: 2026-01-18
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Lia.
Import ListNotations.

(** ========================================================================
    SECTION 1: DEFINITIONS
    ======================================================================== *)

Definition config := (expr * store * effect_ctx)%type.

Definition step_inv (cfg1 cfg2 : config) : Prop :=
  let '(e2, st2, ctx2) := cfg2 in
  let '(e1, st1, ctx1) := cfg1 in
  (e2, st2, ctx2) --> (e1, st1, ctx1).

Definition SN (cfg : config) : Prop := Acc step_inv cfg.

Definition SN_expr (e : expr) : Prop := forall st ctx, SN (e, st, ctx).

(** ========================================================================
    SECTION 2: BASIC SN LEMMAS
    ======================================================================== *)

Lemma SN_step : forall e st ctx e' st' ctx',
  SN (e, st, ctx) ->
  (e, st, ctx) --> (e', st', ctx') ->
  SN (e', st', ctx').
Proof.
  intros e st ctx e' st' ctx' Hsn Hstep.
  inversion Hsn. apply H.
  unfold step_inv.
  exact Hstep.
Qed.

Lemma value_not_step : forall v st ctx e' st' ctx',
  value v ->
  (v, st, ctx) --> (e', st', ctx') ->
  False.
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  generalize dependent ctx'. generalize dependent st'.
  generalize dependent e'. generalize dependent ctx.
  generalize dependent st.
  induction Hval; intros st ctx e' st' ctx' Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma value_SN : forall v st ctx,
  value v ->
  SN (v, st, ctx).
Proof.
  intros v st ctx Hval.
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  exfalso. apply (value_not_step v st ctx e' st' ctx' Hval Hstep).
Qed.

(** ========================================================================
    SECTION 3: SN CLOSURE FOR APPLICATION
    ======================================================================== *)

Lemma SN_all_reducts : forall e st ctx,
  SN (e, st, ctx) ->
  forall e' st' ctx',
    (e, st, ctx) --> (e', st', ctx') ->
    SN (e', st', ctx').
Proof.
  intros e st ctx Hsn e' st' ctx' Hstep.
  inversion Hsn. apply H.
  unfold step_inv. exact Hstep.
Qed.

Lemma SN_app_value_left_aux : forall v cfg,
  value v ->
  SN cfg ->
  (forall x body v' st' ctx', value v' -> SN ([x := v'] body, st', ctx')) ->
  SN (EApp v (fst (fst cfg)), snd (fst cfg), snd cfg).
Proof.
  intros v cfg Hv Hsn2 Hbeta.
  induction Hsn2 as [[[e2 st] ctx] Hacc2 IH2].
  simpl. constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  - (* ST_AppAbs: v = ELam x T body, beta reduction *)
    apply Hbeta. assumption.
  - (* ST_App1: v --> e1' - but v is a value, contradiction *)
    exfalso. eapply value_not_step; eassumption.
  - (* ST_App2: value v, e2 --> e2' *)
    apply (IH2 (e2', st', ctx')).
    unfold step_inv. simpl. assumption.
Qed.

Lemma SN_app_value_left : forall v e2 st ctx,
  value v ->
  SN (e2, st, ctx) ->
  (forall x body v' st' ctx', value v' -> SN ([x := v'] body, st', ctx')) ->
  SN (EApp v e2, st, ctx).
Proof.
  intros v e2 st ctx Hv Hsn2 Hbeta.
  exact (SN_app_value_left_aux v (e2, st, ctx) Hv Hsn2 Hbeta).
Qed.

Lemma SN_app_aux : forall cfg e2,
  SN cfg ->
  (forall st ctx, SN (e2, st, ctx)) ->
  (forall x body v st' ctx', value v -> SN ([x := v] body, st', ctx')) ->
  SN (EApp (fst (fst cfg)) e2, snd (fst cfg), snd cfg).
Proof.
  intros cfg e2 Hsn1 Hsn2 Hbeta.
  induction Hsn1 as [[[e1 st] ctx] Hacc1 IH1].
  simpl. constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  - (* ST_AppAbs: e1 = ELam x T body, beta reduction *)
    apply Hbeta. exact H0.
  - (* ST_App1: e1 --> e1' *)
    apply (IH1 (e1', st', ctx')).
    unfold step_inv. simpl. exact H0.
  - (* ST_App2: value e1, e2 --> e2' *)
    assert (Hsn2': SN (e2', st', ctx')).
    { eapply SN_step; [apply Hsn2 | exact H7]. }
    apply SN_app_value_left; [exact H1 | exact Hsn2' | exact Hbeta].
Qed.

(** THIS IS THE KEY LEMMA - SIGNATURE CANNOT BE CHANGED *)
Lemma SN_app : forall e1 e2 st ctx,
  (forall st' ctx', SN (e1, st', ctx')) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  (* Beta reduction premise: for any substitution of a value into a body, result is SN *)
  (forall x body v st' ctx',
    value v ->
    SN ([x := v] body, st', ctx')) ->
  SN (EApp e1 e2, st, ctx).
Proof.
  intros e1 e2 st ctx Hsn1 Hsn2 Hbeta.
  exact (SN_app_aux (e1, st, ctx) e2 (Hsn1 st ctx) Hsn2 Hbeta).
Qed.

(** ========================================================================
    SECTION 4-9: OTHER SN CLOSURE LEMMAS (ALL PROVEN)
    ======================================================================== *)

Lemma SN_pair : forall e1 e2 st ctx,
  (forall st' ctx', SN (e1, st', ctx')) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  SN (EPair e1 e2, st, ctx).
Proof.
  (* Full proof in file - ends with Qed *)
Admitted. (* PLACEHOLDER - actual file has Qed *)

Lemma SN_fst : forall e st ctx, SN (e, st, ctx) -> SN (EFst e, st, ctx).
Proof. (* Full proof in file *) Admitted.

Lemma SN_snd : forall e st ctx, SN (e, st, ctx) -> SN (ESnd e, st, ctx).
Proof. (* Full proof in file *) Admitted.

Lemma SN_inl : forall e T st ctx, SN (e, st, ctx) -> SN (EInl e T, st, ctx).
Proof. (* Full proof in file *) Admitted.

Lemma SN_inr : forall e T st ctx, SN (e, st, ctx) -> SN (EInr e T, st, ctx).
Proof. (* Full proof in file *) Admitted.

Lemma SN_case : forall e x1 e1 x2 e2 st ctx,
  SN (e, st, ctx) ->
  (forall v st' ctx', value v -> SN ([x1 := v] e1, st', ctx')) ->
  (forall v st' ctx', value v -> SN ([x2 := v] e2, st', ctx')) ->
  SN (ECase e x1 e1 x2 e2, st, ctx).
Proof. (* Full proof in file *) Admitted.

Lemma SN_if : forall e1 e2 e3 st ctx,
  SN (e1, st, ctx) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  (forall st' ctx', SN (e3, st', ctx')) ->
  SN (EIf e1 e2 e3, st, ctx).
Proof. (* Full proof in file *) Admitted.

Lemma SN_let : forall x e1 e2 st ctx,
  SN (e1, st, ctx) ->
  (forall v st' ctx', value v -> SN ([x := v] e2, st', ctx')) ->
  SN (ELet x e1 e2, st, ctx).
Proof. (* Full proof in file *) Admitted.

(** ========================================================================
    SECTION 10: SN CLOSURE FOR REFERENCES
    ======================================================================== *)

Lemma SN_ref : forall e sl st ctx, SN (e, st, ctx) -> SN (ERef e sl, st, ctx).
Proof. (* Full proof in file *) Admitted.

Definition store_wf (st : store) : Prop :=
  forall l v, store_lookup l st = Some v -> value v.

Lemma SN_deref_aux : forall cfg,
  SN cfg ->
  (forall l v st', store_lookup l st' = Some v -> value v) ->
  SN (EDeref (fst (fst cfg)), snd (fst cfg), snd cfg).
Proof.
  intros cfg Hsn Hwf.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e'' st''] ctx''] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_DerefStep: e --> e'0 *)
    apply (IH (e', st'', ctx'')). unfold step_inv. simpl. assumption. }
  { (* ST_DerefLoc: e = ELoc l, result is v from store *)
    apply value_SN. eapply Hwf. eassumption. }
Qed.

(** THIS IS THE KEY LEMMA - SIGNATURE CANNOT BE CHANGED *)
Lemma SN_deref : forall e st ctx,
  SN (e, st, ctx) ->
  (forall l v st', store_lookup l st' = Some v -> value v) ->
  SN (EDeref e, st, ctx).
Proof. intros. exact (SN_deref_aux (e, st, ctx) H H0). Qed.

Lemma SN_assign : forall e1 e2 st ctx,
  (forall st' ctx', SN (e1, st', ctx')) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  SN (EAssign e1 e2, st, ctx).
Proof. (* Full proof in file *) Admitted.

Lemma SN_handle : forall e x h st ctx,
  SN (e, st, ctx) ->
  (forall v st' ctx', value v -> SN ([x := v] h, st', ctx')) ->
  SN (EHandle e x h, st, ctx).
Proof. (* Full proof in file *) Admitted.

(** NOTE: In the actual SN_Closure.v file, ALL lemmas marked "Admitted" above
    are actually proven with Qed. The "Admitted" here is just for brevity.
    The actual file has ZERO admits. *)
```

---

### FILE 2: termination/ReducibilityFull.v (COMPLETE - 766 LINES - TO BE FIXED)

```coq
(** * ReducibilityFull.v

    RIINA Full Reducibility Proof for Strong Normalization

    KEY THEOREM: well_typed_SN
      If e has type T, then e is strongly normalizing.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE
    Date: 2026-01-19
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.SN_Closure.

Import ListNotations.

Section ReducibilityFull.

(** ========================================================================
    SECTION 1: STRONG NORMALIZATION DEFINITION
    ======================================================================== *)

Definition config := (expr * store * effect_ctx)%type.

Definition step_inv (cfg1 cfg2 : config) : Prop :=
  let '(e2, st2, ctx2) := cfg2 in
  let '(e1, st1, ctx1) := cfg1 in
  (e2, st2, ctx2) --> (e1, st1, ctx1).

Definition SN (cfg : config) : Prop := Acc step_inv cfg.

Definition SN_expr (e : expr) : Prop :=
  forall st ctx, SN (e, st, ctx).

(** ========================================================================
    SECTION 2: BASIC SN LEMMAS (ALL PROVEN)
    ======================================================================== *)

Lemma value_not_step : forall v st ctx e' st' ctx',
  value v ->
  (v, st, ctx) --> (e', st', ctx') ->
  False.
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  generalize dependent ctx'. generalize dependent st'.
  generalize dependent e'. generalize dependent ctx.
  generalize dependent st.
  induction Hval; intros st ctx e' st' ctx' Hstep; inversion Hstep; subst; eauto.
Qed.

Lemma value_SN : forall v,
  value v -> SN_expr v.
Proof.
  intros v Hval st ctx.
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  exfalso. eapply value_not_step; eauto.
Qed.

Lemma SN_step : forall e st ctx e' st' ctx',
  SN (e, st, ctx) ->
  (e, st, ctx) --> (e', st', ctx') ->
  SN (e', st', ctx').
Proof.
  intros e st ctx e' st' ctx' Hsn Hstep.
  inversion Hsn; subst.
  apply H.
  unfold step_inv. simpl. exact Hstep.
Qed.

(** Additional SN lemmas: SN_classify, SN_prove, SN_perform, SN_require,
    SN_grant, SN_declassify - ALL PROVEN WITH Qed in actual file *)

(** ========================================================================
    SECTION 4: SUBSTITUTION INFRASTRUCTURE
    ======================================================================== *)

Definition subst_rho := ident -> expr.

Definition id_rho : subst_rho := fun x => EVar x.

Definition extend_rho (ρ : subst_rho) (x : ident) (v : expr) : subst_rho :=
  fun y => if String.eqb y x then v else ρ y.

Fixpoint subst_env (ρ : subst_rho) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar x => ρ x
  | ELam x T body => ELam x T (subst_env (extend_rho ρ x (EVar x)) body)
  | EApp e1 e2 => EApp (subst_env ρ e1) (subst_env ρ e2)
  | EPair e1 e2 => EPair (subst_env ρ e1) (subst_env ρ e2)
  | EFst e => EFst (subst_env ρ e)
  | ESnd e => ESnd (subst_env ρ e)
  | EInl e T => EInl (subst_env ρ e) T
  | EInr e T => EInr (subst_env ρ e) T
  | ECase e x1 e1 x2 e2 =>
      ECase (subst_env ρ e) x1 (subst_env (extend_rho ρ x1 (EVar x1)) e1)
            x2 (subst_env (extend_rho ρ x2 (EVar x2)) e2)
  | EIf e1 e2 e3 => EIf (subst_env ρ e1) (subst_env ρ e2) (subst_env ρ e3)
  | ELet x e1 e2 => ELet x (subst_env ρ e1) (subst_env (extend_rho ρ x (EVar x)) e2)
  | EPerform eff e => EPerform eff (subst_env ρ e)
  | EHandle e x h => EHandle (subst_env ρ e) x (subst_env (extend_rho ρ x (EVar x)) h)
  | ERef e l => ERef (subst_env ρ e) l
  | EDeref e => EDeref (subst_env ρ e)
  | EAssign e1 e2 => EAssign (subst_env ρ e1) (subst_env ρ e2)
  | EClassify e => EClassify (subst_env ρ e)
  | EDeclassify e p => EDeclassify (subst_env ρ e) (subst_env ρ p)
  | EProve e => EProve (subst_env ρ e)
  | ERequire eff e => ERequire eff (subst_env ρ e)
  | EGrant eff e => EGrant eff (subst_env ρ e)
  end.

Lemma extend_rho_id : forall x,
  extend_rho id_rho x (EVar x) = id_rho.
Proof.
  intros x.
  extensionality y. unfold extend_rho, id_rho.
  destruct (String.eqb y x) eqn:Heq.
  - apply String.eqb_eq in Heq. subst. reflexivity.
  - reflexivity.
Qed.

Lemma subst_env_id : forall e,
  subst_env id_rho e = e.
Proof.
  intros e.
  induction e; simpl; try reflexivity;
  try (rewrite IHe; reflexivity);
  try (rewrite IHe1, IHe2; reflexivity);
  try (rewrite IHe1, IHe2, IHe3; reflexivity).
  - rewrite extend_rho_id, IHe. reflexivity.
  - rewrite IHe1, extend_rho_id, IHe2, extend_rho_id, IHe3. reflexivity.
  - rewrite IHe1, extend_rho_id, IHe2. reflexivity.
  - rewrite IHe1, extend_rho_id, IHe2. reflexivity.
Qed.

(** THIS LEMMA IS ADMITTED - Line 389 *)
Lemma subst_subst_env_commute : forall ρ x v e,
  [x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e.
Proof.
Admitted.

(** ========================================================================
    SECTION 5: REDUCIBILITY CANDIDATES
    ======================================================================== *)

Definition Reducible (T : ty) (e : expr) : Prop := SN_expr e.

(** ========================================================================
    SECTION 6-9: CR PROPERTIES AND ENVIRONMENT REDUCIBILITY
    ======================================================================== *)

Lemma CR1 : forall T x, Reducible T x -> SN_expr x.
Proof. intros T x Hred. exact Hred. Qed.

Definition env_reducible (Γ : list (ident * ty)) (ρ : subst_rho) : Prop :=
  forall x T, lookup x Γ = Some T -> value (ρ x) /\ Reducible T (ρ x).

Lemma env_reducible_nil : forall ρ, env_reducible nil ρ.
Proof. intros ρ x T Hlook. discriminate. Qed.

Lemma env_reducible_cons : forall Γ ρ x T v,
  env_reducible Γ ρ -> value v -> Reducible T v ->
  env_reducible ((x, T) :: Γ) (extend_rho ρ x v).
Proof.
  intros Γ ρ x T v Henv Hval Hred y T' Hlook.
  simpl in Hlook. unfold extend_rho.
  destruct (String.eqb y x) eqn:Heq.
  - inversion Hlook; subst. split; assumption.
  - apply Henv. exact Hlook.
Qed.

(** ========================================================================
    SECTION 10: FUNDAMENTAL THEOREM - THE LEMMA WITH 2 ADMITS
    ======================================================================== *)

Lemma fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  Reducible T (subst_env ρ e).
Proof.
  intros Γ Σ pc e T ε ρ Hty.
  revert ρ.
  unfold Reducible.
  induction Hty; intros ρ Henv; simpl.

  (* T_Unit *) - apply value_SN. constructor.
  (* T_Bool *) - apply value_SN. constructor.
  (* T_Int *) - apply value_SN. constructor.
  (* T_String *) - apply value_SN. constructor.
  (* T_Loc *) - apply value_SN. constructor.

  (* T_Var *)
  - unfold env_reducible in Henv.
    specialize (Henv x T H).
    destruct Henv as [Hval Hred].
    unfold Reducible in Hred. exact Hred.

  (* T_Lam *)
  - apply value_SN. constructor.

  (* T_App - ADMIT #1 AT LINE 546 *)
  - intros st ctx.
    apply SN_Closure.SN_app.
    + intros st' ctx'. apply IHHty1. assumption.
    + intros st' ctx'. apply IHHty2. assumption.
    + (* Beta premise *)
      intros x body v st' ctx' Hval.
      (* GOAL: SN ([x := v] body, st', ctx') *)
      (* PROBLEM: Need SN for ANY body, but only have IH for e1 *)
      admit.  (* <-- ADMIT #1 *)

  (* T_Pair through T_Handle - all proven *)
  (* ... *)

  (* T_Deref - ADMIT #2 AT LINE 627 *)
  - intros st ctx.
    apply SN_Closure.SN_deref.
    + apply IHHty. assumption.
    + intros loc val st' Hlook.
      (* GOAL: value val *)
      (* PROBLEM: st' is ANY store, not necessarily well-formed *)
      admit.  (* <-- ADMIT #2 *)

  (* T_Assign through T_Grant - all proven *)
  (* ... *)

Admitted. (* Due to 2 admits above *)

(** ========================================================================
    SECTION 11: MAIN THEOREMS
    ======================================================================== *)

Theorem well_typed_SN : forall Σ pc e T ε,
  has_type nil Σ pc e T ε ->
  SN_expr e.
Proof.
  intros Σ pc e T ε Hty.
  assert (Hred: Reducible T e).
  { replace e with (subst_env id_rho e) by apply subst_env_id.
    apply fundamental_reducibility with (Γ := nil) (Σ := Σ) (pc := pc) (ε := ε).
    - exact Hty.
    - apply env_reducible_nil. }
  apply CR1 with (T := T). exact Hred.
Qed.

Theorem SN_app : forall f a T1 T2 eff Σ pc,
  has_type nil Σ pc f (TFn T1 T2 eff) EffectPure ->
  has_type nil Σ pc a T1 EffectPure ->
  SN_expr (EApp f a).
Proof.
  intros f a T1 T2 eff Σ pc Htyf Htya.
  assert (Hty_app: has_type nil Σ pc (EApp f a) T2
                   (effect_join eff (effect_join EffectPure EffectPure))).
  { apply T_App with (T1 := T1) (ε1 := EffectPure) (ε2 := EffectPure); assumption. }
  apply well_typed_SN with (Σ := Σ) (pc := pc) (T := T2)
        (ε := effect_join eff (effect_join EffectPure EffectPure)).
  exact Hty_app.
Qed.

End ReducibilityFull.
```

---

### FILE 3: foundations/Typing.v (RELEVANT EXCERPTS)

```coq
(** Typing rules *)
Inductive has_type : type_env -> store_ty -> security_level ->
                     expr -> ty -> effect -> Prop :=

  | T_Lam : forall Γ Σ Δ x T1 T2 e ε,
      has_type ((x, T1) :: Γ) Σ Δ e T2 ε ->
      has_type Γ Σ Δ (ELam x T1 e) (TFn T1 T2 ε) EffectPure

  | T_App : forall Γ Σ Δ e1 e2 T1 T2 ε ε1 ε2,
      has_type Γ Σ Δ e1 (TFn T1 T2 ε) ε1 ->
      has_type Γ Σ Δ e2 T1 ε2 ->
      has_type Γ Σ Δ (EApp e1 e2) T2 (effect_join ε (effect_join ε1 ε2))

  | T_Deref : forall Γ Σ Δ e T l ε,
      has_type Γ Σ Δ e (TRef T l) ε ->
      has_type Γ Σ Δ (EDeref e) T (effect_join ε EffectRead)

  (* ... other rules ... *)

(** Store well-formedness - Lines 215-222 *)
Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  (forall l T sl,
     store_ty_lookup l Σ = Some (T, sl) ->
     exists v, store_lookup l st = Some v /\ value v /\
               has_type nil Σ Public v T EffectPure)
  /\
  (forall l v,
     store_lookup l st = Some v ->
     exists T sl, store_ty_lookup l Σ = Some (T, sl) /\ value v /\
                  has_type nil Σ Public v T EffectPure).
```

---

### FILE 4: type_system/Preservation.v (RELEVANT EXCERPTS)

```coq
(** Substitution preserves typing - Line 512 - FULLY PROVEN *)
Lemma substitution_preserves_typing : forall Γ Σ Δ z v e T1 T2 ε2,
  value v ->
  has_type nil Σ Δ v T1 EffectPure ->
  has_type ((z, T1) :: Γ) Σ Δ e T2 ε2 ->
  has_type Γ Σ Δ ([z := v] e) T2 ε2.
Proof.
  (* Fully proven - ends with Qed *)
Qed.

(** Preservation theorem - FULLY PROVEN *)
Theorem preservation : forall Σ pc e T ε e' st st' ctx ctx',
  has_type nil Σ pc e T ε ->
  store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  exists Σ', store_ty_extends Σ Σ' /\
             has_type nil Σ' pc e' T ε /\
             store_wf Σ' st'.
Proof.
  (* Fully proven - ends with Qed *)
Qed.
```

---

### FILE 5: foundations/Syntax.v (RELEVANT EXCERPTS)

```coq
(** Substitution - Lines 473-512 *)
Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar y => if String.eqb x y then v else EVar y
  | ELam y T body =>
      if String.eqb x y then ELam y T body
      else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  (* ... other cases ... *)
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20).
```

---

### FILE 6: foundations/Semantics.v (RELEVANT EXCERPTS)

```coq
(** Multi-step relation - Lines 271-279 *)
Inductive multi_step : (expr * store * effect_ctx) ->
                       (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).

(** Relevant step rules:
    ST_AppAbs: (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
               when value v
    ST_App1: e1 --> e1' implies (EApp e1 e2) --> (EApp e1' e2)
    ST_App2: value v1, e2 --> e2' implies (EApp v1 e2) --> (EApp v1 e2')
    ST_DerefLoc: store_lookup l st = Some v implies (EDeref (ELoc l)) --> v
    ST_DerefStep: e --> e' implies (EDeref e) --> (EDeref e')
*)
```

---

## THE TWO ADMITS - DETAILED ANALYSIS

### ADMIT #1: Line 546 (T_App Beta Case)

**Current code:**
```coq
(* T_App *)
- intros st ctx.
  apply SN_Closure.SN_app.
  + intros st' ctx'. apply IHHty1. assumption.  (* SN of e1 - OK *)
  + intros st' ctx'. apply IHHty2. assumption.  (* SN of e2 - OK *)
  + intros x body v st' ctx' Hval.
    (* GOAL: SN ([x := v] body, st', ctx') *)
    admit.  (* <-- ADMIT #1 *)
```

**What SN_Closure.SN_app requires:**
```coq
(forall x body v st' ctx', value v -> SN ([x := v] body, st', ctx'))
```

**The core problem:**
- This premise requires SN for ANY `body`, including ill-typed/divergent ones
- We have `IHHty1` for `e1`, but NOT for arbitrary `body`
- The IH gives us SN for `subst_env ρ e1`, not for `body`

**What we have available:**
- `Hty1 : has_type Γ Σ pc e1 (TFn T1 T2 ε) ε1`
- `IHHty1 : forall ρ, env_reducible Γ ρ -> SN_expr (subst_env ρ e1)`
- `IHHty2 : forall ρ, env_reducible Γ ρ -> SN_expr (subst_env ρ e2)`
- `Henv : env_reducible Γ ρ`
- `Hval : value v`
- `substitution_preserves_typing` (proven in Preservation.v)

**Key insight for solution:**
- In SN_Closure.SN_app, the beta premise is only USED when e1 IS a lambda
- When e1 = ELam x T1 body, by T_Lam inversion: `has_type ((x,T1)::Γ) Σ pc body T2 ε`
- For well-typed e1, if e1 reduces to a lambda, that lambda's body is well-typed
- We might be able to use the IH with extended environment for body

### ADMIT #2: Line 627 (T_Deref Store Case)

**Current code:**
```coq
(* T_Deref *)
- intros st ctx.
  apply SN_Closure.SN_deref.
  + apply IHHty. assumption.  (* SN of e - OK *)
  + intros loc val st' Hlook.
    (* GOAL: value val *)
    admit.  (* <-- ADMIT #2 *)
```

**What SN_Closure.SN_deref requires:**
```coq
(forall l v st', store_lookup l st' = Some v -> value v)
```

**The core problem:**
- Must hold for ALL stores `st'`, including malformed ones
- We have no `store_wf` in the hypotheses
- The universal quantification is too strong

**What we have available:**
- `IHHty : forall ρ, env_reducible Γ ρ -> SN_expr (subst_env ρ e)`
- `Henv : env_reducible Γ ρ`
- `Hty : has_type Γ Σ pc e (TRef T l) ε`
- `store_wf` definition exists in Typing.v
- `preservation` theorem guarantees store_wf is maintained

**Key insight for solution:**
- In SN_Closure.SN_deref proof, the store premise is only USED at ST_DerefLoc
- ST_DerefLoc only fires when e = ELoc l (a value)
- At that point, store_lookup is called on the CURRENT store
- But the proof needs the premise to hold for ALL stores reached during evaluation

---

## DEPENDENCY CHAIN

```
foundations/Syntax.v          (subst)
         ↓
foundations/Semantics.v       (step, multi_step)
         ↓
foundations/Typing.v          (has_type, store_wf)
         ↓
type_system/Preservation.v    (substitution_preserves_typing, preservation)
         ↓
properties/SN_Closure.v       (SN_app, SN_deref) [READ-ONLY]
         ↓
termination/ReducibilityFull.v (fundamental_reducibility) [TO FIX]
         ↓
properties/NonInterference_v2.v (uses well_typed_SN)
```

---

## POTENTIAL SOLUTION STRATEGIES

### Strategy A: Direct proof using typing structure

For T_App:
- Observe that when SN_app invokes the beta premise, e1 = ELam x T body
- By canonical forms, well-typed values of function type are lambdas
- The body has typing `has_type ((x,T1)::Γ) Σ pc body T2 ε`
- This is exactly what we need for the IH with extended environment

For T_Deref:
- This is harder because the universal quantification over st' is intrinsic
- May need to argue that only well-formed stores arise during evaluation
- Or restructure the proof to track store well-formedness

### Strategy B: Add store_wf as premise to fundamental_reducibility

```coq
Lemma fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  (forall st, store_wf Σ st -> (* additional condition *)) ->
  Reducible T (subst_env ρ e).
```

Need to verify this doesn't break well_typed_SN.

### Strategy C: Create typed versions that bypass SN_Closure

```coq
Lemma SN_app_typed : forall Γ Σ pc e1 e2 T1 T2 ε ε1 ε2 ρ,
  has_type Γ Σ pc e1 (TFn T1 T2 ε) ε1 ->
  has_type Γ Σ pc e2 T1 ε2 ->
  env_reducible Γ ρ ->
  (forall ρ', env_reducible Γ ρ' -> SN_expr (subst_env ρ' e1)) ->
  (forall ρ', env_reducible Γ ρ' -> SN_expr (subst_env ρ' e2)) ->
  (* Additional premise about body *)
  SN_expr (EApp (subst_env ρ e1) (subst_env ρ e2)).
```

### Strategy D: Induction on typing derivation depth

Use well-founded induction on typing derivation, carrying store_wf as an invariant.

---

## VERIFICATION COMMANDS

```bash
# 1. Backup
cd /workspaces/proof/02_FORMAL/coq
cp termination/ReducibilityFull.v termination/ReducibilityFull.v.backup

# 2. Apply your changes

# 3. Compile
make clean
make termination/ReducibilityFull.vo

# 4. Verify no admits remain
grep -n "admit\." termination/ReducibilityFull.v
# Expected: NO OUTPUT (or only in subst_subst_env_commute if that stays)

# 5. Verify no Admitted remains
grep -n "Admitted\." termination/ReducibilityFull.v
# Expected: NO OUTPUT (or only subst_subst_env_commute)

# 6. Test downstream
make properties/NonInterference_v2.vo

# 7. Full build
make
```

---

## EXPECTED OUTPUT FORMAT

Your response MUST follow this EXACT structure:

```
## EXECUTIVE SUMMARY

[2-3 sentences describing your approach and why it works]

---

## DETAILED ANALYSIS

### Root Cause of Admit #1
[Explain why the current proof can't satisfy SN_app's beta premise]

### Root Cause of Admit #2
[Explain why the current proof can't satisfy SN_deref's store premise]

### Why My Approach Works
[Mathematical justification for your solution]

---

## SOLUTION

### Approach: [Name]

### Overview
[High-level description of the fix]

### New Helper Lemmas (if any)

#### Lemma: [name]
```coq
(* Location: Add before fundamental_reducibility *)
Lemma [name] : [statement].
Proof.
  [complete proof]
Qed.
```

### Modifications to Existing Code

#### Modification 1: [description]
**File:** termination/ReducibilityFull.v
**Lines:** [start]-[end]
**Action:** [Replace/Insert/Delete]

**Before:**
```coq
[exact original code]
```

**After:**
```coq
[exact new code]
```

#### Modification 2: ...

---

## COMPLETE fundamental_reducibility LEMMA

```coq
(** Copy-paste ready - complete lemma *)
Lemma fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  Reducible T (subst_env ρ e).
Proof.
  intros Γ Σ pc e T ε ρ Hty.
  revert ρ.
  unfold Reducible.
  induction Hty; intros ρ Henv; simpl.

  (* T_Unit *)
  - apply value_SN. constructor.

  (* T_Bool *)
  - apply value_SN. constructor.

  (* T_Int *)
  - apply value_SN. constructor.

  (* T_String *)
  - apply value_SN. constructor.

  (* T_Loc *)
  - apply value_SN. constructor.

  (* T_Var *)
  - unfold env_reducible in Henv.
    specialize (Henv x T H).
    destruct Henv as [Hval Hred].
    unfold Reducible in Hred. exact Hred.

  (* T_Lam *)
  - apply value_SN. constructor.

  (* T_App - FIXED *)
  - [YOUR COMPLETE PROOF FOR T_App CASE]

  (* T_Pair *)
  - intros st ctx.
    apply SN_Closure.SN_pair.
    + intros st' ctx'. apply IHHty1. assumption.
    + intros st' ctx'. apply IHHty2. assumption.

  (* T_Fst *)
  - intros st ctx.
    apply SN_Closure.SN_fst.
    apply IHHty. assumption.

  (* T_Snd *)
  - intros st ctx.
    apply SN_Closure.SN_snd.
    apply IHHty. assumption.

  (* T_Inl *)
  - intros st ctx.
    apply SN_Closure.SN_inl.
    apply IHHty. assumption.

  (* T_Inr *)
  - intros st ctx.
    apply SN_Closure.SN_inr.
    apply IHHty. assumption.

  (* T_Case *)
  - intros st ctx.
    apply SN_Closure.SN_case.
    + apply IHHty1. assumption.
    + intros v st' ctx' Hv.
      rewrite subst_subst_env_commute.
      specialize (IHHty2 (extend_rho ρ x1 v)).
      apply IHHty2.
      apply env_reducible_cons; [assumption | assumption |].
      unfold Reducible. apply value_SN. assumption.
    + intros v st' ctx' Hv.
      rewrite subst_subst_env_commute.
      specialize (IHHty3 (extend_rho ρ x2 v)).
      apply IHHty3.
      apply env_reducible_cons; [assumption | assumption |].
      unfold Reducible. apply value_SN. assumption.

  (* T_If *)
  - intros st ctx.
    apply SN_Closure.SN_if.
    + apply IHHty1. assumption.
    + intros st' ctx'. apply IHHty2. assumption.
    + intros st' ctx'. apply IHHty3. assumption.

  (* T_Let *)
  - intros st ctx.
    apply SN_Closure.SN_let.
    + apply IHHty1. assumption.
    + intros v st' ctx' Hv.
      rewrite subst_subst_env_commute.
      specialize (IHHty2 (extend_rho ρ x v)).
      apply IHHty2.
      apply env_reducible_cons; [assumption | assumption |].
      unfold Reducible. apply value_SN. assumption.

  (* T_Perform *)
  - intros st ctx.
    apply SN_perform.
    apply IHHty. assumption.

  (* T_Handle *)
  - intros st ctx.
    apply SN_Closure.SN_handle.
    + apply IHHty1. assumption.
    + intros v st' ctx' Hv.
      rewrite subst_subst_env_commute.
      specialize (IHHty2 (extend_rho ρ x v)).
      apply IHHty2.
      apply env_reducible_cons; [assumption | assumption |].
      unfold Reducible. apply value_SN. assumption.

  (* T_Ref *)
  - intros st ctx.
    apply SN_Closure.SN_ref.
    apply IHHty. assumption.

  (* T_Deref - FIXED *)
  - [YOUR COMPLETE PROOF FOR T_Deref CASE]

  (* T_Assign *)
  - intros st ctx.
    apply SN_Closure.SN_assign.
    + intros st' ctx'. apply IHHty1. assumption.
    + intros st' ctx'. apply IHHty2. assumption.

  (* T_Classify *)
  - intros st ctx.
    apply SN_classify.
    apply IHHty. assumption.

  (* T_Declassify *)
  - intros st ctx.
    apply SN_declassify.
    + apply IHHty1. assumption.
    + intros st' ctx'. apply IHHty2. assumption.

  (* T_Prove *)
  - intros st ctx.
    apply SN_prove.
    apply IHHty. assumption.

  (* T_Require *)
  - intros st ctx.
    apply SN_require.
    apply IHHty. assumption.

  (* T_Grant *)
  - intros st ctx.
    apply SN_grant.
    apply IHHty. assumption.

Qed.  (* <-- MUST BE Qed, NOT Admitted *)
```

---

## VERIFICATION

### Proof of Mathematical Correctness
[Explain why each fixed case is logically sound]

### No Regressions
[Confirm well_typed_SN and ReducibilityFull.SN_app still work]

### Commands to Verify
```bash
cd /workspaces/proof/02_FORMAL/coq
make clean
make termination/ReducibilityFull.vo
grep -n "admit\." termination/ReducibilityFull.v
# Should output nothing (or only line 389 for subst_subst_env_commute)
make properties/NonInterference_v2.vo
make
```

---

## KNOWN LIMITATIONS

[Note if subst_subst_env_commute at line 389 remains Admitted - this is acceptable]
[Any other caveats]
```

---

## FINAL CHECKLIST

Before providing your answer, verify ALL of these:

- [ ] All Coq code is syntactically correct (no typos, balanced parentheses)
- [ ] No new `admit` tactics introduced
- [ ] No new `Admitted` introduced (except subst_subst_env_commute which was already Admitted)
- [ ] `SN_Closure.v` is NOT modified at all
- [ ] `fundamental_reducibility` ends with `Qed`
- [ ] `well_typed_SN` theorem still works (no changes needed)
- [ ] `ReducibilityFull.SN_app` theorem still works
- [ ] The T_App case is FULLY proven (no admit)
- [ ] The T_Deref case is FULLY proven (no admit)
- [ ] All 24 typing cases are handled (T_Unit through T_Grant)
- [ ] Code is copy-paste ready (no "..." placeholders)
- [ ] Tactics used exist in Coq 8.18.0

---

## COROLLARY: IF MODIFICATION OF SN_Closure.v IS REQUIRED

If after thorough analysis you determine that eliminating both admits is MATHEMATICALLY IMPOSSIBLE without modifying SN_Closure.v, then:

1. Explain EXACTLY why it's impossible
2. Propose the MINIMAL changes to SN_Closure.v
3. Provide the corresponding changes to ReducibilityFull.v
4. Verify that the changed SN_Closure.v still compiles
5. Verify all downstream dependencies still work

The preference order is:
1. Fix only ReducibilityFull.v (preferred)
2. Fix ReducibilityFull.v + minimal SN_Closure.v changes (acceptable if necessary)
3. Major restructuring (last resort, must be fully justified)

---

## ADDITIONAL TECHNICAL CONTEXT

### Coq Version
8.18.0

### Available Tactics (non-exhaustive)
`intros`, `apply`, `exact`, `destruct`, `induction`, `inversion`, `rewrite`,
`simpl`, `unfold`, `assert`, `specialize`, `split`, `left`, `right`, `exists`,
`reflexivity`, `assumption`, `auto`, `eauto`, `lia`, `constructor`, `exfalso`,
`discriminate`, `injection`, `subst`, `generalize`, `clear`, `rename`, `pose`,
`remember`, `replace`, `trivial`, `congruence`, `f_equal`.

### Key Lemmas Available
- `value_SN : forall v, value v -> SN_expr v`
- `SN_step : forall e st ctx e' st' ctx', SN (e, st, ctx) -> (e, st, ctx) --> (e', st', ctx') -> SN (e', st', ctx')`
- `env_reducible_nil : forall ρ, env_reducible nil ρ`
- `env_reducible_cons : forall Γ ρ x T v, env_reducible Γ ρ -> value v -> Reducible T v -> env_reducible ((x, T) :: Γ) (extend_rho ρ x v)`
- `subst_env_id : forall e, subst_env id_rho e = e`
- `subst_subst_env_commute : forall ρ x v e, [x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e` (Admitted)
- `substitution_preserves_typing` (from Preservation.v, Qed)
- `preservation` (from Preservation.v, Qed)

### Store-Related Definitions
```coq
Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  (forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
     exists v, store_lookup l st = Some v /\ value v /\
               has_type nil Σ Public v T EffectPure)
  /\
  (forall l v, store_lookup l st = Some v ->
     exists T sl, store_ty_lookup l Σ = Some (T, sl) /\ value v /\
                  has_type nil Σ Public v T EffectPure).
```

---

**PROVIDE A COMPLETE, COMPILABLE SOLUTION. NO PLACEHOLDERS. NO SKETCHES. EXACT COQ CODE.**
