(** * ReducibilityFull.v

    RIINA Full Reducibility Proof for Strong Normalization

    This file proves strong normalization for well-typed RIINA terms
    using Tait's reducibility method (logical relations).

    KEY THEOREM: well_typed_SN
      If e has type T, then e is strongly normalizing.

    This unlocks:
    - SN_app: applications of SN functions to SN arguments are SN
    - TFn step-up in NonInterference_v2.v

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE
    Date: 2026-01-19
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.properties.TypeMeasure.

Import ListNotations.

(** ========================================================================
    SECTION 1: STRONG NORMALIZATION DEFINITION
    ======================================================================== *)

(** Configuration for evaluation *)
Definition config := (expr * store * effect_ctx)%type.

(** Inverse step relation for well-foundedness *)
Definition step_inv (cfg1 cfg2 : config) : Prop :=
  let '(e2, st2, ctx2) := cfg2 in
  let '(e1, st1, ctx1) := cfg1 in
  (e2, st2, ctx2) --> (e1, st1, ctx1).

(** Strong normalization via accessibility *)
Definition SN (cfg : config) : Prop := Acc step_inv cfg.

(** SN for expressions (store-polymorphic) *)
Definition SN_expr (e : expr) : Prop :=
  forall st ctx, SN (e, st, ctx).

(** ========================================================================
    SECTION 2: BASIC SN LEMMAS
    ======================================================================== *)

(** Values don't step *)
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

(** Values are SN *)
Lemma value_SN : forall v,
  value v -> SN_expr v.
Proof.
  intros v Hval st ctx.
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  exfalso. eapply value_not_step; eauto.
Qed.

(** SN is preserved by reduction *)
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

(** ========================================================================
    SECTION 3: NEUTRAL TERMS
    ======================================================================== *)

(** Neutral terms: terms that are not values but can potentially reduce *)
Inductive neutral : expr -> Prop :=
  | N_Var : forall x, neutral (EVar x)
  | N_App : forall e1 e2, neutral (EApp e1 e2)
  | N_Fst : forall e, neutral (EFst e)
  | N_Snd : forall e, neutral (ESnd e)
  | N_Case : forall e x1 e1 x2 e2, neutral (ECase e x1 e1 x2 e2)
  | N_If : forall e1 e2 e3, neutral (EIf e1 e2 e3)
  | N_Let : forall x e1 e2, neutral (ELet x e1 e2)
  | N_Deref : forall e, neutral (EDeref e)
  | N_Assign : forall e1 e2, neutral (EAssign e1 e2)
  | N_Ref : forall e sl, neutral (ERef e sl)
  | N_Handle : forall e x h, neutral (EHandle e x h)
  | N_Declassify : forall e p, neutral (EDeclassify e p).

(** ========================================================================
    SECTION 4: REDUCIBILITY CANDIDATES
    ======================================================================== *)

(**
    Reducibility is defined by induction on types.

    For base types: Reducible = SN
    For function types: Reducible f = forall reducible x, (f x) is reducible

    We use a simplified type structure focusing on:
    - Base types (Unit, Bool, Int, String)
    - Products (TProd)
    - Sums (TSum)
    - Functions (TFn)
*)

(** Reducibility predicate - defined by recursion on type_depth *)
Fixpoint Reducible (T : ty) (e : expr) {struct T} : Prop :=
  match T with
  (* Base types: just SN *)
  | TUnit => SN_expr e
  | TBool => SN_expr e
  | TInt => SN_expr e
  | TString => SN_expr e
  | TBytes => SN_expr e

  (* Products: both components reducible *)
  | TProd T1 T2 =>
      SN_expr e /\
      (forall st ctx v st' ctx',
        (e, st, ctx) -->* (v, st', ctx') ->
        value v ->
        exists v1 v2, v = EPair v1 v2 /\ Reducible T1 v1 /\ Reducible T2 v2)

  (* Sums: the contained value is reducible *)
  | TSum T1 T2 =>
      SN_expr e /\
      (forall st ctx v st' ctx',
        (e, st, ctx) -->* (v, st', ctx') ->
        value v ->
        (exists v1, v = EInl v1 T2 /\ Reducible T1 v1) \/
        (exists v2, v = EInr v2 T1 /\ Reducible T2 v2))

  (* Functions: map reducible arguments to reducible results *)
  | TFn T1 T2 eff =>
      SN_expr e /\
      (forall a,
        Reducible T1 a ->
        SN_expr (EApp e a))

  (* Reference types: just SN for now *)
  | TRef T' sl => SN_expr e

  (* Security wrappers: reducibility of underlying type *)
  | TSecret T' => SN_expr e
  | TLabeled T' l => SN_expr e
  | TTainted T' l => SN_expr e
  | TSanitized T' l => SN_expr e

  (* Other types: just SN *)
  | TList T' => SN_expr e
  | TOption T' => SN_expr e
  | TProof T' => SN_expr e
  | TCapability c => SN_expr e
  | TCapabilityFull c => SN_expr e
  | TChan s => SN_expr e
  | TSecureChan s l => SN_expr e
  | TConstantTime T' => SN_expr e
  | TZeroizing T' => SN_expr e
  end.

(** ========================================================================
    SECTION 5: CR PROPERTIES (Candidate Reducibility)
    ======================================================================== *)

(** CR1: Reducible terms are SN *)
Lemma CR1 : forall T x,
  Reducible T x -> SN_expr x.
Proof.
  intros T. induction T; intros x Hred; simpl in Hred;
  try exact Hred;
  try (destruct Hred as [Hsn _]; exact Hsn).
Qed.

(** CR2: Reducibility is closed under head expansion
    If e --> e' and e' is reducible, then e is reducible.
    (For values, this is vacuously true since values don't reduce) *)
Lemma CR2_base : forall e e' st ctx st' ctx',
  (e, st, ctx) --> (e', st', ctx') ->
  SN_expr e' ->
  SN_expr e.
Proof.
  intros e e' st ctx st' ctx' Hstep Hsn st0 ctx0.
  (* We need to show SN (e, st0, ctx0) *)
  (* This requires knowing that e steps to something SN in all stores *)
  (* For now, we admit this - it requires careful reasoning about store independence *)
  admit.
Admitted.

(** CR3: Neutral SN terms are reducible at base types *)
Lemma CR3_base : forall e,
  neutral e ->
  SN_expr e ->
  Reducible TUnit e /\ Reducible TBool e /\ Reducible TInt e /\
  Reducible TString e /\ Reducible TBytes e.
Proof.
  intros e Hneut Hsn.
  repeat split; simpl; exact Hsn.
Qed.

(** ========================================================================
    SECTION 6: KEY LEMMA - SN_APP
    ======================================================================== *)

(** The key lemma: if f is reducible at TFn and a is reducible at T1,
    then (EApp f a) is SN *)
Lemma SN_app_reducible : forall T1 T2 eff f a,
  Reducible (TFn T1 T2 eff) f ->
  Reducible T1 a ->
  SN_expr (EApp f a).
Proof.
  intros T1 T2 eff f a Hf Ha.
  simpl in Hf.
  destruct Hf as [Hf_sn Hf_app].
  apply Hf_app.
  exact Ha.
Qed.

(** ========================================================================
    SECTION 7: REDUCIBILITY OF VALUES
    ======================================================================== *)

(** Unit value is reducible *)
Lemma unit_reducible : Reducible TUnit EUnit.
Proof.
  simpl. apply value_SN. constructor.
Qed.

(** Boolean values are reducible *)
Lemma bool_reducible : forall b, Reducible TBool (EBool b).
Proof.
  intros b. simpl. apply value_SN. constructor.
Qed.

(** Integer values are reducible *)
Lemma int_reducible : forall n, Reducible TInt (EInt n).
Proof.
  intros n. simpl. apply value_SN. constructor.
Qed.

(** Lambda values are reducible if body is reducible under substitution *)
Lemma lam_reducible : forall x T1 T2 eff body,
  (forall a, Reducible T1 a -> value a -> Reducible T2 ([x := a] body)) ->
  Reducible (TFn T1 T2 eff) (ELam x T1 body).
Proof.
  intros x T1 T2 eff body Hbody.
  simpl. split.
  - (* SN_expr (ELam x T1 body) *)
    apply value_SN. constructor.
  - (* forall reducible a, SN_expr (EApp (ELam x T1 body) a) *)
    intros a Ha st ctx.
    (* EApp (ELam x T1 body) a --> [x := a] body when a is a value *)
    (* We need to handle the case where a is not yet a value *)
    (* This requires the full reducibility argument *)
    admit.
Admitted.

(** Pair values are reducible *)
Lemma pair_reducible : forall T1 T2 v1 v2,
  value v1 -> value v2 ->
  Reducible T1 v1 ->
  Reducible T2 v2 ->
  Reducible (TProd T1 T2) (EPair v1 v2).
Proof.
  intros T1 T2 v1 v2 Hval1 Hval2 Hr1 Hr2.
  simpl. split.
  - (* SN *)
    apply value_SN. constructor; assumption.
  - (* Evaluation gives pair with reducible components *)
    intros st ctx v st' ctx' Hsteps Hval.
    (* EPair v1 v2 is a value, so v = EPair v1 v2 *)
    inversion Hsteps; subst.
    + (* zero steps *)
      exists v1, v2. repeat split; assumption.
    + (* at least one step - contradiction since EPair v1 v2 is a value *)
      exfalso.
      inversion H; subst;
      [inversion Hval1 | inversion Hval2].
Qed.

(** ========================================================================
    SECTION 8: FUNDAMENTAL THEOREM
    ======================================================================== *)

(** Environment reducibility: all bindings are reducible *)
Definition env_reducible (Γ : list (ident * ty)) (ρ : ident -> option expr) : Prop :=
  forall x T,
    lookup x Γ = Some T ->
    exists v, ρ x = Some v /\ value v /\ Reducible T v.

(** Empty environment is trivially reducible *)
Lemma env_reducible_nil : forall ρ,
  env_reducible nil ρ.
Proof.
  intros ρ x T Hlook.
  discriminate.
Qed.

(** Extending reducible environment *)
Lemma env_reducible_cons : forall Γ ρ x T v,
  env_reducible Γ ρ ->
  value v ->
  Reducible T v ->
  env_reducible ((x, T) :: Γ) (fun y => if String.eqb y x then Some v else ρ y).
Proof.
  intros Γ ρ x T v Henv Hval Hred y T' Hlook.
  simpl in Hlook.
  destruct (String.eqb y x) eqn:Heq.
  - (* y = x *)
    inversion Hlook; subst.
    exists v. repeat split; assumption.
  - (* y <> x *)
    apply Henv. exact Hlook.
Qed.

(** FUNDAMENTAL THEOREM: Well-typed terms are reducible

    This is the main theorem. It requires careful induction on typing
    derivations and uses the CR properties.

    For full proof, we need:
    1. Substitution lemma for reducibility
    2. Case analysis on each typing rule
*)
Theorem fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  Reducible T (subst_env ρ e).
Proof.
  intros Γ Σ pc e T ε ρ Hty Henv.
  (* Full proof requires induction on typing derivation *)
  (* This is substantial work - admit for now *)
  admit.
Admitted.

(** ========================================================================
    SECTION 9: MAIN THEOREMS
    ======================================================================== *)

(** Well-typed closed terms are SN *)
Theorem well_typed_SN : forall Σ pc e T ε,
  has_type nil Σ pc e T ε ->
  SN_expr e.
Proof.
  intros Σ pc e T ε Hty.
  assert (Hred: Reducible T e).
  { replace e with (subst_env (fun _ => None) e).
    - apply fundamental_reducibility with (Γ := nil) (Σ := Σ) (pc := pc) (ε := ε).
      + exact Hty.
      + apply env_reducible_nil.
    - (* subst_env with empty env is identity *)
      admit. }
  apply CR1 with (T := T).
  exact Hred.
Admitted.

(** SN_app: The key theorem for NonInterference_v2.v *)
Theorem SN_app : forall f a T1 T2 eff Σ pc,
  has_type nil Σ pc f (TFn T1 T2 eff) EffectPure ->
  has_type nil Σ pc a T1 EffectPure ->
  SN_expr (EApp f a).
Proof.
  intros f a T1 T2 eff Σ pc Htyf Htya.
  assert (Hf: Reducible (TFn T1 T2 eff) f).
  { replace f with (subst_env (fun _ => None) f).
    - apply fundamental_reducibility with (Γ := nil) (Σ := Σ) (pc := pc) (ε := EffectPure).
      + exact Htyf.
      + apply env_reducible_nil.
    - admit. }
  assert (Ha: Reducible T1 a).
  { replace a with (subst_env (fun _ => None) a).
    - apply fundamental_reducibility with (Γ := nil) (Σ := Σ) (pc := pc) (ε := EffectPure).
      + exact Htya.
      + apply env_reducible_nil.
    - admit. }
  apply SN_app_reducible with (T1 := T1) (T2 := T2) (eff := eff).
  - exact Hf.
  - exact Ha.
Admitted.

(** ========================================================================
    SECTION 10: SUMMARY
    ======================================================================== *)

(**
    PROVEN LEMMAS (Qed):
    - value_not_step
    - value_SN
    - SN_step
    - CR1 (reducible → SN)
    - CR3_base (neutral SN → reducible at base)
    - unit_reducible, bool_reducible, int_reducible
    - pair_reducible
    - env_reducible_nil, env_reducible_cons
    - SN_app_reducible (given reducibility premises)

    ADMITTED (require full proof):
    - CR2_base (head expansion)
    - lam_reducible (lambda reducibility)
    - fundamental_reducibility (THE KEY THEOREM)
    - well_typed_SN (corollary)
    - SN_app (THE GOAL)

    The admits are in the expected places - the fundamental theorem
    requires substantial case analysis on typing derivations.

    NEXT STEPS:
    1. Prove substitution lemma for reducibility
    2. Complete fundamental_reducibility by induction on typing
    3. This will unlock SN_app and then TFn step-up
*)

End ReducibilityFull.
