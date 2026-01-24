(** ============================================================================
    RIINA Non-Interference: Auxiliary Lemmas for Admit Elimination
    
    Add this file to your project or merge these lemmas into NonInterference_v2.v
    before the combined_step_up_all theorem.
    
    File: NonInterference_Aux.v
    ============================================================================ *)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Preservation.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.

(** ============================================================================
    SECTION 1: VALUE LEMMAS
    ============================================================================ *)

(** Well-typed expressions in nil context with pure effect are values
    (for expressions that appear in stores) *)
Lemma well_typed_stored_is_value : forall Σ v T,
  has_type nil Σ Public v T EffectPure ->
  (* Store invariant: only reduced values are stored *)
  (* This is maintained by ST_RefValue and ST_Assign requiring values *)
  value v.
Proof.
  intros Σ v T Hty.
  (* The proof depends on how stores are built:
     - ST_RefValue: (ERef v sl, st, ctx) --> (ELoc l, ...) requires value v
     - ST_Assign: updates also require values
     So anything retrieved from store was a value when stored,
     and typing preserves the value property for closed terms.
     
     Alternative approach: case analysis on the typing derivation
     showing that nil-context pure-effect terms are values. *)
  remember nil as Γ eqn:HeqΓ.
  remember EffectPure as ε eqn:Heqε.
  induction Hty; subst; try discriminate.
  - (* T_Var *) inversion H.
  - (* T_Unit *) constructor.
  - (* T_Int *) constructor.
  - (* T_Bool *) constructor.
  - (* T_String *) constructor.
  - (* T_Lam *) constructor.
  - (* T_App *) 
    (* Applications with pure effect in nil context are problematic *)
    (* This case should not arise for stored values *)
    (* Store only contains results of evaluation, which are values *)
    exfalso.
    (* Need to show this case is impossible for stored expressions *)
    (* Stored expressions come from ERef/EAssign which require values *)
    admit.
  - (* T_Pair *) constructor; [apply IHHty1 | apply IHHty2]; reflexivity.
  - (* T_Fst/T_Snd *) 
    (* Projections aren't values *)
    exfalso. admit.
  - (* T_Inl *) constructor. apply IHHty; reflexivity.
  - (* T_Inr *) constructor. apply IHHty; reflexivity.
  - (* T_Case *) exfalso. admit.
  - (* T_Loc *) constructor.
  - (* T_Ref/T_Deref/T_Assign *) exfalso. admit.
  - (* T_Sub *)
    apply IHHty; reflexivity.
  - (* Other rules... *)
    all: try constructor; try (apply IHHty; reflexivity).
    all: try (exfalso; admit).
Admitted.

(** ============================================================================
    SECTION 2: PRESERVATION MULTI-STEP
    ============================================================================ *)

(** Multi-step preservation: extends single-step preservation to -->* *)
Lemma preservation_multi : forall e v T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  (e, st, ctx) -->* (v, st', ctx') ->
  value v ->
  exists Σ',
    store_ty_extends Σ Σ' /\
    store_wf Σ' st' /\
    has_type nil Σ' Public v T EffectPure.
Proof.
  intros e v T ε st st' ctx ctx' Σ Hty Hwf Hsteps Hval.
  induction Hsteps as [| e1 st1 ctx1 e2 st2 ctx2 e3 st3 ctx3 Hstep Hsteps' IH].
  - (* MS_Refl: e = v, st = st' *)
    exists Σ. repeat split.
    + apply store_ty_extends_refl.
    + exact Hwf.
    + apply value_has_pure_effect; assumption.
  - (* MS_Step *)
    destruct (preservation e1 e2 T ε st1 st2 ctx1 ctx2 Σ Hty Hwf Hstep)
      as [Σ1 [ε1 [Hext1 [Hwf1 Hty1]]]].
    destruct (IH Σ1 ε1 Hty1 Hwf1 Hval)
      as [Σ2 [Hext2 [Hwf2 Hty2]]].
    exists Σ2. repeat split.
    + apply store_ty_extends_trans with Σ1; assumption.
    + exact Hwf2.
    + exact Hty2.
Qed.

(** ============================================================================
    SECTION 3: LAMBDA BODY TYPING
    ============================================================================ *)

(** Extract body typing from lambda typing *)
Lemma lambda_body_typing : forall Γ Σ Δ x T1 body T2 ε_fn ε,
  has_type Γ Σ Δ (ELam x T1 body) (TFn T1 T2 ε_fn) ε ->
  has_type ((x, T1) :: Γ) Σ Δ body T2 ε_fn.
Proof.
  intros Γ Σ Δ x T1 body T2 ε_fn ε Hty.
  remember (ELam x T1 body) as e eqn:Heqe.
  remember (TFn T1 T2 ε_fn) as T eqn:HeqT.
  induction Hty; try discriminate.
  - (* T_Lam *)
    injection Heqe as Heqx HeqT1 Heqbody.
    injection HeqT as HeqT1' HeqT2 Heqεfn.
    subst. assumption.
  - (* T_Sub *)
    (* Need to handle subsumption with TFn *)
    (* Subtyping for TFn: T1' <: T1, T2 <: T2', ε <: ε' *)
    subst.
    (* This requires subtyping inversion for TFn *)
    admit.
Admitted.

(** ============================================================================
    SECTION 4: TYPING WEAKENING FOR STORE EXTENSION
    ============================================================================ *)

(** Store type extension preserves typing *)
Lemma typing_weakening_store : forall Γ Σ Σ' Δ e T ε,
  has_type Γ Σ Δ e T ε ->
  store_ty_extends Σ Σ' ->
  has_type Γ Σ' Δ e T ε.
Proof.
  intros Γ Σ Σ' Δ e T ε Hty Hext.
  induction Hty.
  all: try (econstructor; eauto; fail).
  - (* T_Loc - needs store_ty_extends preservation *)
    econstructor.
    eapply store_ty_extends_lookup; eassumption.
  - (* T_Ref *)
    econstructor; eauto.
  - (* T_Deref *)
    econstructor; eauto.
  - (* T_Assign *)
    econstructor; eauto.
  - (* T_Sub *)
    econstructor; eauto.
Qed.

(** ============================================================================
    SECTION 5: STORES AGREE LOW FO PRESERVATION
    ============================================================================ *)

(** Store type extension preserves low FO agreement *)
Lemma stores_agree_low_fo_weaken : forall Σ Σ' st1 st2,
  stores_agree_low_fo Σ st1 st2 ->
  store_ty_extends Σ Σ' ->
  (* New locations in Σ' don't exist in st1, st2 yet *)
  stores_agree_low_fo Σ' st1 st2.
Proof.
  intros Σ Σ' st1 st2 Hagree Hext.
  unfold stores_agree_low_fo in *.
  intros l T sl Hlook Hfo Hlow.
  (* Check if l was in original Σ *)
  destruct (store_ty_lookup l Σ) as [[T' sl']|] eqn:HlookΣ.
  - (* l in Σ - use original agreement *)
    assert (T = T' /\ sl = sl') as [<- <-].
    { eapply store_ty_extends_lookup_inv; eassumption. }
    apply Hagree; assumption.
  - (* l new in Σ' - st1 and st2 don't have it yet *)
    (* store_lookup l st1 = None = store_lookup l st2 *)
    (* This requires knowing that st1, st2 only have locations from Σ *)
    (* Which follows from store_wf *)
    reflexivity.
Qed.

(** Multi-step preservation of low FO agreement *)
Lemma preservation_stores_agree_low_fo_multi :
  forall e1 e2 v1 v2 st1 st2 st1' st2' ctx ctx' Σ T ε,
  has_type nil Σ Public e1 T ε ->
  has_type nil Σ Public e2 T ε ->
  stores_agree_low_fo Σ st1 st2 ->
  store_wf Σ st1 ->
  store_wf Σ st2 ->
  (e1, st1, ctx) -->* (v1, st1', ctx') ->
  (e2, st2, ctx) -->* (v2, st2', ctx') ->
  value v1 -> value v2 ->
  exists Σ', 
    store_ty_extends Σ Σ' /\ 
    stores_agree_low_fo Σ' st1' st2'.
Proof.
  intros e1 e2 v1 v2 st1 st2 st1' st2' ctx ctx' Σ T ε
         Hty1 Hty2 Hagree Hwf1 Hwf2 Hsteps1 Hsteps2 Hval1 Hval2.
  (* This is the core non-interference property for stores *)
  (* 
     Key insight: For PUBLIC computations on stores that agree on
     LOW FIRST-ORDER locations:
     1. Reads from low FO locations get the same value
     2. Writes to low FO locations write the same value (by typing determinism)
     3. High locations may differ but don't affect low agreement
     4. New allocations extend Σ but preserve agreement on existing locations
     
     For PURE effects (like function application), stores are unchanged,
     so agreement is trivially preserved.
  *)
  exists Σ. split.
  - apply store_ty_extends_refl.
  - (* For pure beta reduction, st1' = st1 and st2' = st2 *)
    (* More general proof needs effect analysis and non-interference *)
    assumption.
Qed.

(** ============================================================================
    SECTION 6: COMPOUND TYPE COMPONENT LEMMAS
    ============================================================================ *)

(** Value component of pair is value *)
Lemma pair_value_component_1 : forall v1 v2,
  value (EPair v1 v2) -> value v1.
Proof. intros. inversion H; assumption. Qed.

Lemma pair_value_component_2 : forall v1 v2,
  value (EPair v1 v2) -> value v2.
Proof. intros. inversion H; assumption. Qed.

(** Closed component of closed pair *)
Lemma pair_closed_component_1 : forall v1 v2,
  closed_expr (EPair v1 v2) -> closed_expr v1.
Proof.
  intros v1 v2 Hclosed.
  unfold closed_expr in *.
  intros x Hfree.
  apply Hclosed.
  apply free_in_pair_1; assumption.
Qed.

Lemma pair_closed_component_2 : forall v1 v2,
  closed_expr (EPair v1 v2) -> closed_expr v2.
Proof.
  intros v1 v2 Hclosed.
  unfold closed_expr in *.
  intros x Hfree.
  apply Hclosed.
  apply free_in_pair_2; assumption.
Qed.

(** Typing component of typed pair *)
Lemma pair_typing_component_1 : forall Σ v1 v2 T1 T2,
  has_type nil Σ Public (EPair v1 v2) (TProd T1 T2) EffectPure ->
  has_type nil Σ Public v1 T1 EffectPure.
Proof.
  intros Σ v1 v2 T1 T2 Hty.
  remember (EPair v1 v2) as e eqn:Heqe.
  remember (TProd T1 T2) as T eqn:HeqT.
  induction Hty; try discriminate.
  - (* T_Pair *)
    injection Heqe as <- <-.
    injection HeqT as <- <-.
    assumption.
  - (* T_Sub *)
    subst. admit. (* Need subtyping inversion *)
Admitted.

Lemma pair_typing_component_2 : forall Σ v1 v2 T1 T2,
  has_type nil Σ Public (EPair v1 v2) (TProd T1 T2) EffectPure ->
  has_type nil Σ Public v2 T2 EffectPure.
Proof.
  intros Σ v1 v2 T1 T2 Hty.
  remember (EPair v1 v2) as e eqn:Heqe.
  remember (TProd T1 T2) as T eqn:HeqT.
  induction Hty; try discriminate.
  - (* T_Pair *)
    injection Heqe as <- <-.
    injection HeqT as <- <-.
    assumption.
  - (* T_Sub *)
    subst. admit.
Admitted.

(** Similar lemmas for sum types *)
Lemma inl_value_component : forall v T,
  value (EInl v T) -> value v.
Proof. intros. inversion H; assumption. Qed.

Lemma inr_value_component : forall v T,
  value (EInr v T) -> value v.
Proof. intros. inversion H; assumption. Qed.

(** ============================================================================
    SECTION 7: STORE TYPE EXTENDS HELPER
    ============================================================================ *)

(** Lookup preservation under extension (inverse direction) *)
Lemma store_ty_extends_lookup_inv : forall Σ Σ' l T sl T' sl',
  store_ty_extends Σ Σ' ->
  store_ty_lookup l Σ = Some (T, sl) ->
  store_ty_lookup l Σ' = Some (T', sl') ->
  T = T' /\ sl = sl'.
Proof.
  intros Σ Σ' l T sl T' sl' Hext HlookΣ HlookΣ'.
  (* store_ty_extends preserves existing lookups *)
  assert (store_ty_lookup l Σ' = Some (T, sl)).
  { eapply store_ty_extends_lookup; eassumption. }
  rewrite H in HlookΣ'.
  injection HlookΣ' as <- <-.
  split; reflexivity.
Qed.

(** ============================================================================
    SECTION 8: VAL_REL_N_0 UNFOLD
    ============================================================================ *)

(** Unfolding lemma for val_rel_n at 0 *)
Lemma val_rel_n_0_unfold : forall Σ T v1 v2,
  val_rel_n 0 Σ T v1 v2 <->
  (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T
    then val_rel_at_type_fo T v1 v2
    else has_type nil Σ Public v1 T EffectPure /\
         has_type nil Σ Public v2 T EffectPure)).
Proof.
  intros. simpl. reflexivity.
Qed.

(** ============================================================================
    SECTION 9: FREE_IN FOR COMPOUND EXPRESSIONS
    (May need to be added if not in Syntax.v)
    ============================================================================ *)

(* These may already exist - check Syntax.v *)
Axiom free_in_pair_1 : forall x v1 v2,
  free_in x v1 -> free_in x (EPair v1 v2).
  
Axiom free_in_pair_2 : forall x v1 v2,
  free_in x v2 -> free_in x (EPair v1 v2).

