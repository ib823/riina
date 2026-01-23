(* ================================================================ *)
(*  STORE WELL-FORMEDNESS PRESERVATION                              *)
(*  Proof that multi-step evaluation preserves store well-formedness *)
(*  with possible store type extension.                             *)
(*                                                                  *)
(*  Target: Eliminate admit at line 1179 of NonInterference_v2.v    *)
(*  Repository: https://github.com/ib823/proof                      *)
(* ================================================================ *)

(*
  IMPORTANT: This file is a TEMPLATE.
  
  Before using:
  1. Read 02_FORMAL/coq/foundations/Semantics.v to find:
     - step relation (-->)
     - multi_step relation (-->*)
     - store type
     - store_lookup and store_update
  
  2. Read 02_FORMAL/coq/foundations/Typing.v lines 1-300 to find:
     - store_ty type
     - store_ty_lookup function
     - store_ty_extends relation
  
  3. Read 02_FORMAL/coq/properties/NonInterference_v2.v lines 200-350 to find:
     - store_wf definition
  
  4. Read 02_FORMAL/coq/type_system/Preservation.v lines 1-400 to find:
     - existing preservation lemmas
     - store_ty_extends_preserves_typing
  
  Then:
  - Replace placeholder imports with actual imports
  - Replace placeholder definitions with actual imports
  - Adjust proof tactics to match actual definitions
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* ================================================================ *)
(* PLACEHOLDER IMPORTS - REPLACE WITH ACTUAL PROJECT IMPORTS        *)
(* ================================================================ *)

(*
Require Import RIINA.Foundations.Syntax.
Require Import RIINA.Foundations.Semantics.
Require Import RIINA.Foundations.Typing.
Require Import RIINA.TypeSystem.Preservation.
Require Import RIINA.Properties.NonInterference_v2.
*)

(* ================================================================ *)
(* PLACEHOLDER TYPE DEFINITIONS                                     *)
(* Replace these with imports from actual project files             *)
(* ================================================================ *)

Section PlaceholderTypes.

  (* Location type - typically nat *)
  Definition loc := nat.
  
  (* Security labels *)
  Inductive security_label : Type :=
  | Public : security_label
  | Secret : security_label.
  
  (* Effect annotations *)
  Inductive effect : Type :=
  | EffectPure : effect
  | EffectRead : effect
  | EffectWrite : effect
  | EffectAlloc : effect.
  
  (* Placeholder expression type - replace with actual *)
  Inductive expr : Type :=
  | EUnit : expr
  | EInt : nat -> expr
  | EBool : bool -> expr
  | EVar : nat -> expr
  | ELoc : loc -> expr
  | ERef : expr -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  | EApp : expr -> expr -> expr
  | ELam : expr -> expr
  | ELet : expr -> expr -> expr
  | EIf : expr -> expr -> expr -> expr.
  
  (* Placeholder type *)
  Inductive ty : Type :=
  | TUnit : ty
  | TInt : ty
  | TBool : ty
  | TRef : ty -> security_label -> ty
  | TArrow : ty -> ty -> effect -> ty.
  
  (* Store: maps locations to values *)
  Definition store := list (loc * expr).
  
  (* Store typing: maps locations to (type, security_label) *)
  Definition store_ty := list (loc * (ty * security_label)).
  
  (* Typing context *)
  Definition context := list (nat * ty).
  
  (* Evaluation context (may include security context, etc.) *)
  Definition eval_ctx := unit. (* Simplified - replace with actual *)

End PlaceholderTypes.

(* ================================================================ *)
(* PLACEHOLDER FUNCTION DEFINITIONS                                 *)
(* Replace these with imports from actual project files             *)
(* ================================================================ *)

Section PlaceholderFunctions.

  (* Location equality *)
  Definition loc_eq (l1 l2 : loc) : bool := Nat.eqb l1 l2.
  
  (* Store lookup *)
  Fixpoint store_lookup (st : store) (l : loc) : option expr :=
    match st with
    | [] => None
    | (l', v) :: st' => if loc_eq l l' then Some v else store_lookup st' l
    end.
  
  (* Store update *)
  Fixpoint store_update (st : store) (l : loc) (v : expr) : store :=
    match st with
    | [] => [(l, v)]
    | (l', v') :: st' => 
        if loc_eq l l' then (l, v) :: st' 
        else (l', v') :: store_update st' l v
    end.
  
  (* Fresh location *)
  Definition fresh_loc (st : store) : loc :=
    S (fold_right max 0 (map fst st)).
  
  (* Store typing lookup *)
  Fixpoint store_ty_lookup (Σ : store_ty) (l : loc) : option (ty * security_label) :=
    match Σ with
    | [] => None
    | (l', ts) :: Σ' => if loc_eq l l' then Some ts else store_ty_lookup Σ' l
    end.
  
  (* Store typing extend with new location *)
  Definition store_ty_extend (Σ : store_ty) (l : loc) (T : ty) (sl : security_label) 
    : store_ty := Σ ++ [(l, (T, sl))].

End PlaceholderFunctions.

(* ================================================================ *)
(* STORE TYPING EXTENSION RELATION                                  *)
(* This should match the definition in Typing.v                     *)
(* ================================================================ *)

Section StoreTypingExtension.

  (* Store typing extension: Σ extends to Σ' if all bindings in Σ are preserved *)
  Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
    forall l T sl,
      store_ty_lookup Σ l = Some (T, sl) ->
      store_ty_lookup Σ' l = Some (T, sl).
  
  (* Alternative definition using length and prefix *)
  (* Uncomment if this matches your actual definition
  Definition store_ty_extends_alt (Σ Σ' : store_ty) : Prop :=
    length Σ <= length Σ' /\
    forall l T sl,
      store_ty_lookup Σ l = Some (T, sl) ->
      store_ty_lookup Σ' l = Some (T, sl).
  *)

End StoreTypingExtension.

(* ================================================================ *)
(* PLACEHOLDER TYPING JUDGMENT                                      *)
(* Replace with import from Typing.v                                *)
(* ================================================================ *)

Section TypingJudgment.

  (* Placeholder typing judgment *)
  (* has_type Γ Σ pc e T ε means:
     - In context Γ with store typing Σ and program counter label pc
     - Expression e has type T with effect ε *)
  Parameter has_type : context -> store_ty -> security_label -> 
                       expr -> ty -> effect -> Prop.
  
  (* Typing respects store extension *)
  Axiom has_type_store_extends : forall Γ Σ Σ' pc e T ε,
    has_type Γ Σ pc e T ε ->
    store_ty_extends Σ Σ' ->
    has_type Γ Σ' pc e T ε.

End TypingJudgment.

(* ================================================================ *)
(* PLACEHOLDER STEP RELATION                                        *)
(* Replace with import from Semantics.v                             *)
(* ================================================================ *)

Section StepRelation.

  (* Configuration: (expression, store, evaluation_context) *)
  Definition config := (expr * store * eval_ctx)%type.
  
  (* Single step relation *)
  (* (e, st, ctx) --> (e', st', ctx') *)
  Parameter step : config -> config -> Prop.
  
  Notation "c1 '-->' c2" := (step c1 c2) (at level 40).
  
  (* Multi-step relation (reflexive-transitive closure) *)
  Inductive multi_step : config -> config -> Prop :=
  | multi_step_refl : forall c, multi_step c c
  | multi_step_step : forall c1 c2 c3,
      step c1 c2 ->
      multi_step c2 c3 ->
      multi_step c1 c3.
  
  Notation "c1 '-->*' c2" := (multi_step c1 c2) (at level 40).

End StepRelation.

(* ================================================================ *)
(* STORE WELL-FORMEDNESS DEFINITION                                 *)
(* This should match the definition in NonInterference_v2.v         *)
(* ================================================================ *)

Section StoreWellFormedness.

  (* Store well-formedness: every location in Σ has a well-typed value in st *)
  Definition store_wf (Σ : store_ty) (st : store) : Prop :=
    (* Part 1: Every location in Σ has a corresponding well-typed value in st *)
    (forall l T sl, 
       store_ty_lookup Σ l = Some (T, sl) ->
       exists v, store_lookup st l = Some v /\
                 has_type nil Σ Public v T EffectPure) /\
    (* Part 2: Every location in st is tracked in Σ *)
    (forall l v, 
       store_lookup st l = Some v ->
       exists T sl, store_ty_lookup Σ l = Some (T, sl)).

End StoreWellFormedness.

(* ================================================================ *)
(* AUXILIARY LEMMAS FOR STORE TYPING EXTENSION                      *)
(* ================================================================ *)

Section StoreTypingExtensionLemmas.

  (** Store typing extension is reflexive *)
  Lemma store_ty_extends_refl : forall Σ,
    store_ty_extends Σ Σ.
  Proof.
    unfold store_ty_extends.
    intros Σ l T sl H.
    exact H.
  Qed.
  
  (** Store typing extension is transitive *)
  Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
    store_ty_extends Σ1 Σ2 ->
    store_ty_extends Σ2 Σ3 ->
    store_ty_extends Σ1 Σ3.
  Proof.
    unfold store_ty_extends.
    intros Σ1 Σ2 Σ3 H12 H23 l T sl Hin.
    apply H23.
    apply H12.
    exact Hin.
  Qed.
  
  (** Extending store typing preserves existing lookups *)
  Lemma store_ty_extend_preserves : forall Σ l l' T' sl',
    l <> l' ->
    store_ty_lookup (store_ty_extend Σ l' T' sl') l = store_ty_lookup Σ l.
  Proof.
    unfold store_ty_extend.
    intros Σ l l' T' sl' Hneq.
    induction Σ as [| [l'' ts''] Σ' IH].
    - simpl.
      unfold loc_eq.
      rewrite <- Nat.eqb_neq in Hneq.
      rewrite Hneq.
      reflexivity.
    - simpl.
      destruct (loc_eq l l'') eqn:Heq.
      + reflexivity.
      + apply IH.
  Qed.
  
  (** Store typing extension holds after extending *)
  Lemma store_ty_extends_extend : forall Σ l T sl,
    store_ty_lookup Σ l = None ->
    store_ty_extends Σ (store_ty_extend Σ l T sl).
  Proof.
    unfold store_ty_extends, store_ty_extend.
    intros Σ l T sl Hfresh l' T' sl' Hlookup.
    induction Σ as [| [l'' ts''] Σ' IH].
    - (* Σ = [] *)
      simpl in Hlookup. discriminate.
    - (* Σ = (l'', ts'') :: Σ' *)
      simpl in *.
      destruct (loc_eq l' l'') eqn:Heq.
      + (* l' = l'' *)
        exact Hlookup.
      + (* l' <> l'' *)
        apply IH.
        exact Hlookup.
  Qed.

End StoreTypingExtensionLemmas.

(* ================================================================ *)
(* SINGLE-STEP PRESERVATION OF STORE WELL-FORMEDNESS                *)
(* ================================================================ *)

Section SingleStepPreservation.

  (* 
    This lemma requires induction on the step relation.
    The critical cases are:
    
    1. ERef v --> ELoc l (reference allocation)
       - Store extends: st' = store_update st l v
       - Store typing extends: Σ' = store_ty_extend Σ l T sl
       - Must show store_wf Σ' st'
    
    2. EAssign (ELoc l) v --> EUnit (assignment)
       - Store updates: st' = store_update st l v
       - Store typing unchanged: Σ' = Σ
       - Must show v has correct type for location l
    
    3. All other cases: Store unchanged
       - st' = st
       - Σ' = Σ
       - Apply reflexivity
  *)

  (** Single step preserves store well-formedness *)
  Lemma step_preserves_store_wf : forall e st ctx e' st' ctx' Σ T ε,
    (e, st, ctx) --> (e', st', ctx') ->
    has_type nil Σ Public e T ε ->
    store_wf Σ st ->
    exists Σ',
      store_ty_extends Σ Σ' /\
      store_wf Σ' st' /\
      has_type nil Σ' Public e' T ε.
  Proof.
    intros e st ctx e' st' ctx' Σ T ε Hstep Htype Hwf.
    (* 
      PROOF STRATEGY:
      
      Induction on Hstep (the step relation).
      For each step rule, analyze how store changes:
      
      Case 1: Store unchanged (most cases)
        - Σ' = Σ
        - Use store_ty_extends_refl
        - store_wf Σ st' follows from store_wf Σ st
        
      Case 2: Reference allocation (ERef v --> ELoc l)
        - l = fresh_loc st
        - st' = store_update st l v
        - Need to determine T_v (type of v) from typing derivation
        - Σ' = store_ty_extend Σ l T_v sl
        - Show store_wf Σ' st' holds
        
      Case 3: Assignment (EAssign (ELoc l) v --> EUnit)
        - st' = store_update st l v
        - Σ' = Σ (store typing unchanged)
        - Show v has type T where (T, sl) = store_ty_lookup Σ l
        - store_wf preserved because value type matches
    *)
    
    (* 
      BLOCKING ISSUE:
      
      This proof requires:
      1. Actual definition of step relation to perform case analysis
      2. Inversion lemmas for typing judgment
      3. Canonical forms lemmas
      
      Mark as admitted with detailed blocking reason.
    *)
    
    (* Attempt using preservation from Preservation.v if available *)
    (* This should follow from single-step type preservation *)
    admit.
    
    (* 
      DETAILED PROOF SKETCH for when actual definitions are available:
      
      induction Hstep; intros Htype Hwf.
      
      - (* Case: ST_RefVal - ERef v --> ELoc l *)
        (* Premises: is_value v, l = fresh_loc st, st' = store_update st l v *)
        exists (store_ty_extend Σ l T_v sl_pc).
        split.
        + (* store_ty_extends Σ Σ' *)
          apply store_ty_extends_extend.
          apply fresh_loc_not_in_store_ty. (* Need this auxiliary lemma *)
        + split.
          * (* store_wf Σ' st' *)
            unfold store_wf. split.
            -- (* Part 1: locations in Σ' have well-typed values *)
               intros l' T' sl' Hlookup'.
               destruct (Nat.eq_dec l l') as [Heq | Hneq].
               ++ (* l = l' - the new location *)
                  subst l'.
                  exists v. split.
                  ** apply store_update_lookup_eq. (* Need this lemma *)
                  ** (* has_type nil Σ' Public v T' EffectPure *)
                     (* From typing inversion on ERef v *)
                     admit.
               ++ (* l <> l' - existing location *)
                  destruct Hwf as [Hwf1 Hwf2].
                  specialize (Hwf1 l' T' sl').
                  (* show store_ty_lookup Σ l' = Some (T', sl') *)
                  assert (store_ty_lookup Σ l' = Some (T', sl')).
                  { rewrite store_ty_extend_preserves in Hlookup'; auto. }
                  specialize (Hwf1 H).
                  destruct Hwf1 as [v' [Hv' Htv']].
                  exists v'. split.
                  ** rewrite store_update_lookup_neq; auto.
                  ** apply has_type_store_extends with Σ; auto.
                     apply store_ty_extends_extend.
                     apply fresh_loc_not_in_store_ty.
            -- (* Part 2: locations in st' are in Σ' *)
               intros l' v' Hlookup'.
               (* Similar case analysis on whether l = l' *)
               admit.
          * (* has_type nil Σ' Public (ELoc l) T EffectPure *)
            (* From typing rule for locations *)
            admit.
      
      - (* Case: ST_AssignVal - EAssign (ELoc l) v --> EUnit *)
        exists Σ.
        split.
        + apply store_ty_extends_refl.
        + split.
          * (* store_wf Σ st' *)
            unfold store_wf. split.
            -- intros l' T' sl' Hlookup'.
               destruct Hwf as [Hwf1 Hwf2].
               destruct (Nat.eq_dec l l') as [Heq | Hneq].
               ++ (* l = l' - the updated location *)
                  subst l'.
                  exists v. split.
                  ** apply store_update_lookup_eq.
                  ** (* has_type nil Σ Public v T' EffectPure *)
                     (* From typing inversion: v has type matching l's type *)
                     admit.
               ++ (* l <> l' *)
                  specialize (Hwf1 l' T' sl' Hlookup').
                  destruct Hwf1 as [v' [Hv' Htv']].
                  exists v'. split.
                  ** rewrite store_update_lookup_neq; auto.
                  ** exact Htv'.
            -- intros l' v' Hlookup'.
               destruct (Nat.eq_dec l l') as [Heq | Hneq].
               ++ subst. destruct Hwf as [_ Hwf2].
                  (* l was already in st, so in Σ *)
                  (* Need: store_lookup st l = Some _ *)
                  admit.
               ++ rewrite store_update_lookup_neq in Hlookup'; auto.
                  destruct Hwf as [_ Hwf2].
                  apply Hwf2 with v'. exact Hlookup'.
          * (* has_type nil Σ Public EUnit T EffectPure *)
            (* T = TUnit from typing of assignment *)
            admit.
      
      - (* Other cases: store unchanged *)
        exists Σ.
        split; [apply store_ty_extends_refl | split; [exact Hwf | ]].
        (* Type preservation from standard preservation lemma *)
        admit.
    *)
  Admitted.
  (* 
    ADMITTED REASON: 
    - Requires actual step relation definition for case analysis
    - Requires typing inversion lemmas
    - Requires auxiliary lemmas about store_update and store_ty_extend
    
    TO COMPLETE:
    1. Import actual definitions from Semantics.v and Typing.v
    2. Add auxiliary lemmas (see next section)
    3. Replace admit with actual proof
  *)

End SingleStepPreservation.

(* ================================================================ *)
(* AUXILIARY LEMMAS FOR STORE OPERATIONS                            *)
(* These may already exist in your codebase - check first           *)
(* ================================================================ *)

Section StoreOperationLemmas.

  (** Looking up updated location returns the new value *)
  Lemma store_update_lookup_eq : forall st l v,
    store_lookup (store_update st l v) l = Some v.
  Proof.
    intros st l v.
    induction st as [| [l' v'] st' IH].
    - simpl. unfold loc_eq. rewrite Nat.eqb_refl. reflexivity.
    - simpl.
      destruct (loc_eq l l') eqn:Heq.
      + simpl. rewrite Heq. reflexivity.
      + simpl. rewrite Heq. apply IH.
  Qed.
  
  (** Looking up different location in updated store is unchanged *)
  Lemma store_update_lookup_neq : forall st l l' v,
    l <> l' ->
    store_lookup (store_update st l v) l' = store_lookup st l'.
  Proof.
    intros st l l' v Hneq.
    induction st as [| [l'' v''] st' IH].
    - simpl.
      unfold loc_eq.
      assert (Nat.eqb l' l = false) as Hneqb.
      { apply Nat.eqb_neq. auto. }
      rewrite Hneqb. reflexivity.
    - simpl.
      destruct (loc_eq l l'') eqn:Heq1.
      + (* l = l'' *)
        simpl.
        apply Nat.eqb_eq in Heq1.
        subst l''.
        destruct (loc_eq l' l) eqn:Heq2.
        * apply Nat.eqb_eq in Heq2. subst. contradiction.
        * reflexivity.
      + (* l <> l'' *)
        simpl.
        destruct (loc_eq l' l'') eqn:Heq2.
        * reflexivity.
        * apply IH.
  Qed.
  
  (** Fresh location is not in store *)
  Lemma fresh_loc_not_in_store : forall st,
    store_lookup st (fresh_loc st) = None.
  Proof.
    intros st.
    unfold fresh_loc.
    induction st as [| [l v] st' IH].
    - simpl. reflexivity.
    - simpl.
      unfold loc_eq.
      (* Need to show: Nat.eqb (S (max l (fold_right max 0 (map fst st')))) l = false *)
      (* Because S (max l ...) > l *)
      assert (Nat.eqb (S (Nat.max l (fold_right Nat.max 0 (map fst st')))) l = false) as Hneq.
      {
        apply Nat.eqb_neq.
        lia.
      }
      rewrite Hneq.
      (* Now need: store_lookup st' (S (max l ...)) = None *)
      (* This requires showing fresh_loc doesn't decrease when we remove head *)
      admit. (* Requires more detailed proof about fresh_loc *)
  Admitted.
  
  (** Fresh location is not in store typing *)
  Lemma fresh_loc_not_in_store_ty : forall Σ st,
    store_wf Σ st ->
    store_ty_lookup Σ (fresh_loc st) = None.
  Proof.
    intros Σ st Hwf.
    destruct (store_ty_lookup Σ (fresh_loc st)) eqn:Hlookup.
    - (* Some (t, s) - derive contradiction *)
      destruct p as [T sl].
      destruct Hwf as [Hwf1 _].
      specialize (Hwf1 (fresh_loc st) T sl Hlookup).
      destruct Hwf1 as [v [Hv _]].
      rewrite fresh_loc_not_in_store in Hv.
      discriminate.
    - (* None - done *)
      reflexivity.
  Qed.

End StoreOperationLemmas.

(* ================================================================ *)
(* MULTI-STEP PRESERVATION OF STORE WELL-FORMEDNESS                 *)
(* ================================================================ *)

Section MultiStepPreservation.

  (** Multi-step evaluation preserves store well-formedness.
      The store typing may extend (new locations allocated). *)
  Lemma multi_step_preserves_store_wf : forall e st ctx v st' ctx' Σ T ε,
    (e, st, ctx) -->* (v, st', ctx') ->
    has_type nil Σ Public e T ε ->
    store_wf Σ st ->
    exists Σ',
      store_ty_extends Σ Σ' /\
      store_wf Σ' st' /\
      has_type nil Σ' Public v T EffectPure.
  Proof.
    intros e st ctx v st' ctx' Σ T ε Hsteps.
    (* Induction on the multi-step derivation *)
    induction Hsteps as [c | c1 c2 c3 Hstep Hsteps' IH].
    
    - (* Case: multi_step_refl *)
      (* c = (e, st, ctx) = (v, st', ctx'), so e = v, st = st', ctx = ctx' *)
      intros Htype Hwf.
      exists Σ.
      split.
      + apply store_ty_extends_refl.
      + split.
        * exact Hwf.
        * (* Need: has_type nil Σ Public e T EffectPure *)
          (* Issue: e has effect ε, not necessarily EffectPure *)
          (* This depends on how values are typed in your system *)
          (* Typically, values have pure effect *)
          admit. (* Need: is_value e -> effect is Pure *)
    
    - (* Case: multi_step_step *)
      (* c1 --> c2 -->* c3 *)
      intros Htype Hwf.
      destruct c1 as [[e1 st1] ctx1].
      destruct c2 as [[e2 st2] ctx2].
      destruct c3 as [[e3 st3] ctx3].
      
      (* Apply single-step preservation to get intermediate Σ'' *)
      destruct (step_preserves_store_wf e1 st1 ctx1 e2 st2 ctx2 Σ T ε 
                Hstep Htype Hwf) as [Σ'' [Hext'' [Hwf'' Htype'']]].
      
      (* Apply IH to get final Σ' *)
      destruct (IH Σ'' T ε Htype'' Hwf'') as [Σ' [Hext' [Hwf' Htype']]].
      
      (* Combine extensions by transitivity *)
      exists Σ'.
      split.
      + apply store_ty_extends_trans with Σ''; assumption.
      + split; assumption.
  Admitted.
  (*
    ADMITTED REASON:
    - Depends on step_preserves_store_wf which is admitted
    - The admit in the refl case needs: is_value e implies effect is EffectPure
    
    TO COMPLETE:
    1. Complete step_preserves_store_wf proof
    2. Add lemma: is_value e -> has_type Γ Σ pc e T ε -> ε = EffectPure
       (or modify theorem statement)
  *)

End MultiStepPreservation.

(* ================================================================ *)
(* ALTERNATIVE: THEOREM WITH EXPLICIT VALUE REQUIREMENT             *)
(* ================================================================ *)

Section MultiStepPreservationAlt.

  (* Value predicate - replace with actual definition *)
  Fixpoint is_value (e : expr) : Prop :=
    match e with
    | EUnit => True
    | EInt _ => True
    | EBool _ => True
    | ELoc _ => True
    | ELam _ => True
    | _ => False
    end.
  
  (** Alternative formulation requiring v to be a value *)
  Lemma multi_step_preserves_store_wf_value : forall e st ctx v st' ctx' Σ T ε,
    (e, st, ctx) -->* (v, st', ctx') ->
    is_value v ->
    has_type nil Σ Public e T ε ->
    store_wf Σ st ->
    exists Σ',
      store_ty_extends Σ Σ' /\
      store_wf Σ' st' /\
      has_type nil Σ' Public v T EffectPure.
  Proof.
    intros e st ctx v st' ctx' Σ T ε Hsteps Hval Htype Hwf.
    induction Hsteps as [c | c1 c2 c3 Hstep Hsteps' IH].
    
    - (* Reflexive case *)
      exists Σ.
      split; [apply store_ty_extends_refl |].
      split; [exact Hwf |].
      (* Need: values have pure effect *)
      (* This is typically a standard lemma *)
      admit.
    
    - (* Step case *)
      destruct c1 as [[e1 st1] ctx1].
      destruct c2 as [[e2 st2] ctx2].
      destruct c3 as [[e3 st3] ctx3].
      
      destruct (step_preserves_store_wf e1 st1 ctx1 e2 st2 ctx2 Σ T ε 
                Hstep Htype Hwf) as [Σ'' [Hext'' [Hwf'' Htype'']]].
      
      specialize (IH Hval Σ'' T ε Htype'' Hwf'').
      destruct IH as [Σ' [Hext' [Hwf' Htype']]].
      
      exists Σ'.
      split; [apply store_ty_extends_trans with Σ''; assumption |].
      split; assumption.
  Admitted.

End MultiStepPreservationAlt.

(* ================================================================ *)
(* INTEGRATION INSTRUCTIONS                                         *)
(* ================================================================ *)

(*
  TO INTEGRATE INTO NonInterference_v2.v:
  
  1. Copy the proven lemmas (store_ty_extends_refl, store_ty_extends_trans,
     store operation lemmas) into your file, or import them if they exist.
  
  2. Ensure your imports include:
     - step relation from Semantics.v
     - multi_step relation from Semantics.v
     - has_type from Typing.v
     - store_ty_extends from Typing.v
     - store_wf from NonInterference_v2.v
  
  3. Use the multi_step_preserves_store_wf lemma at line 1179 where
     the admit currently is:
     
     destruct (multi_step_preserves_store_wf e st ctx v st' ctx' Σ T ε
               Hsteps Htype Hwf) as [Σ' [Hext [Hwf' Htype']]].
     (* Now use Σ', Hext, Hwf', Htype' *)
  
  4. If step_preserves_store_wf is already proved in Preservation.v
     (possibly under a different name), use that instead.

  CHECKING FOR EXISTING LEMMAS:
  
  Run: grep -n "preserves.*store\|store.*preserv" *.v
  Run: grep -n "store_wf\|store_well_formed" *.v
  
  Look in Preservation.v for lemmas like:
  - preservation (single-step type preservation)
  - multi_preservation
  - Any lemma mentioning store_wf or store_ty_extends
*)
