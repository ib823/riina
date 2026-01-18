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
  inversion Hsn as [_ H].
  apply H.
  unfold step_inv.
  exact Hstep.
Qed.

Lemma value_SN : forall v st ctx,
  value v ->
  SN (v, st, ctx).
Proof.
  intros v st ctx Hval.
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  exfalso.
  induction Hval; inversion Hstep.
Qed.

(** ========================================================================
    SECTION 3: SN CLOSURE FOR APPLICATION
    ========================================================================
    
    KEY LEMMA: If e1 and e2 are SN, then EApp e1 e2 is SN.
    
    Proof idea: Use lexicographic induction on (SN e1, SN e2).
    When EApp e1 e2 steps:
    - If e1 --> e1': use IH on (e1', e2) with smaller first component
    - If e1 is value and e2 --> e2': use IH on (e1, e2') with smaller second
    - If both values and e1 = ELam: redex reduces, need SN of body
*)

(** Auxiliary: SN implies all reducts are SN *)
Lemma SN_all_reducts : forall e st ctx,
  SN (e, st, ctx) ->
  forall e' st' ctx',
    (e, st, ctx) --> (e', st', ctx') ->
    SN (e', st', ctx').
Proof.
  intros e st ctx Hsn e' st' ctx' Hstep.
  inversion Hsn as [_ H].
  apply H.
  unfold step_inv. exact Hstep.
Qed.

(** SN closure for application - version with explicit termination *)
Lemma SN_app_aux : forall n e1 e2 st ctx,
  (forall st' ctx', SN (e1, st', ctx')) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  (* Additional premise: application reducts are SN *)
  (forall e' st' ctx',
    (EApp e1 e2, st, ctx) --> (e', st', ctx') ->
    SN (e', st', ctx')) ->
  SN (EApp e1 e2, st, ctx).
Proof.
  intros n e1 e2 st ctx Hsn1 Hsn2 Hreducts.
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  apply Hreducts.
  exact Hstep.
Qed.

(** The main application closure lemma *)
Lemma SN_app : forall e1 e2 st ctx,
  SN (e1, st, ctx) ->
  SN (e2, st, ctx) ->
  (* For beta reduction: body is SN when e1 is a lambda *)
  (forall x T body a st' ctx',
    e1 = ELam x T body ->
    value e2 ->
    (EApp (ELam x T body) e2, st, ctx) --> ([x := e2] body, st', ctx') ->
    SN ([x := e2] body, st', ctx')) ->
  SN (EApp e1 e2, st, ctx).
Proof.
  intros e1 e2 st ctx Hsn1 Hsn2 Hbeta.
  (* Double induction on Hsn1 and Hsn2 *)
  generalize dependent ctx.
  generalize dependent st.
  generalize dependent e2.
  induction Hsn1 as [[[e1' st1'] ctx1'] _ IH1].
  intros e2 Hsn2 st ctx Hbeta.
  induction Hsn2 as [[[e2' st2'] ctx2'] _ IH2].
  
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_AppAbs: (EApp (ELam x T body) v) --> [x := v] body *)
    apply Hbeta with (x := x) (T := T0) (body := body) (a := e2').
    + reflexivity.
    + exact H0.
    + exact Hstep.
  
  - (* ST_App1: e1 --> e1'0, so EApp e1 e2 --> EApp e1'0 e2 *)
    (* Use IH1 on e1'0 *)
    apply IH1 with (y := (e1'0, st', ctx')).
    + unfold step_inv. exact H2.
    + (* SN (e2', st', ctx') - need to rebuild *)
      constructor.
      intros [[e'' st''] ctx''] Hstep'.
      unfold step_inv in Hstep'. simpl in Hstep'.
      (* e2' steps to e'' *)
      inversion Hsn2 as [_ H].
      apply H.
      unfold step_inv. exact Hstep'.
    + (* Beta case for new e1 *)
      intros x T body a st'' ctx'' Heq Hval Hstep'.
      subst e1'0.
      (* e1 stepped to ELam x T body, contradiction since e1 stepped *)
      (* Wait, e1 = e1' in our induction, and e1 --> e1'0 = ELam... *)
      (* This is actually possible if e1 was some term that reduced to a lambda *)
      (* Need the original Hbeta to handle this... *)
      (* Actually, we need a stronger induction hypothesis *)
      admit.
  
  - (* ST_App2: e1 is value, e2 --> e2'0 *)
    (* Use IH2 on e2'0 *)
    apply IH2 with (y := (e2'0, st', ctx')).
    + unfold step_inv. exact H3.
    + intros x T body a st'' ctx'' Heq Hval Hstep'.
      (* e1' is a value, and we're applying it *)
      (* Need beta reduction case *)
      admit.
Admitted.

(** ========================================================================
    SECTION 4: SN CLOSURE FOR PAIRS
    ======================================================================== *)

Lemma SN_pair : forall e1 e2 st ctx,
  SN (e1, st, ctx) ->
  SN (e2, st, ctx) ->
  SN (EPair e1 e2, st, ctx).
Proof.
  intros e1 e2 st ctx Hsn1 Hsn2.
  generalize dependent ctx.
  generalize dependent st.
  generalize dependent e2.
  induction Hsn1 as [[[e1' st1'] ctx1'] _ IH1].
  intros e2 Hsn2 st ctx.
  induction Hsn2 as [[[e2' st2'] ctx2'] _ IH2].
  
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_Pair1: e1 --> e1'0 *)
    apply IH1 with (y := (e1'0, st', ctx')).
    + unfold step_inv. exact H2.
    + constructor.
      intros [[e'' st''] ctx''] Hstep'.
      inversion Hsn2 as [_ H].
      apply H.
      unfold step_inv. exact Hstep'.
  
  - (* ST_Pair2: e1 is value, e2 --> e2'0 *)
    apply IH2 with (y := (e2'0, st', ctx')).
    unfold step_inv. exact H3.
Qed.

(** ========================================================================
    SECTION 5: SN CLOSURE FOR PROJECTIONS
    ======================================================================== *)

Lemma SN_fst : forall e st ctx,
  SN (e, st, ctx) ->
  (* When e is a pair, projection is SN *)
  (forall v1 v2 st' ctx',
    e = EPair v1 v2 ->
    value v1 -> value v2 ->
    SN (v1, st', ctx')) ->
  SN (EFst e, st, ctx).
Proof.
  intros e st ctx Hsn Hproj.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_Fst: e = EPair v1 v2 *)
    apply Hproj with (v2 := v2).
    + reflexivity.
    + exact H.
    + exact H0.
  
  - (* ST_FstStep: e --> e'0 *)
    apply IH with (y := (e'0, st'', ctx'')).
    + unfold step_inv. exact H0.
    + intros v1 v2 st0 ctx0 Heq Hval1 Hval2.
      (* e stepped to e'0 which is EPair v1 v2 *)
      subst e'0.
      apply value_SN. exact Hval1.
Qed.

Lemma SN_snd : forall e st ctx,
  SN (e, st, ctx) ->
  (forall v1 v2 st' ctx',
    e = EPair v1 v2 ->
    value v1 -> value v2 ->
    SN (v2, st', ctx')) ->
  SN (ESnd e, st, ctx).
Proof.
  intros e st ctx Hsn Hproj.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_Snd *)
    apply Hproj with (v1 := v1).
    + reflexivity.
    + exact H.
    + exact H0.
  
  - (* ST_SndStep *)
    apply IH with (y := (e'0, st'', ctx'')).
    + unfold step_inv. exact H0.
    + intros v1 v2 st0 ctx0 Heq Hval1 Hval2.
      subst e'0.
      apply value_SN. exact Hval2.
Qed.

(** ========================================================================
    SECTION 6: SN CLOSURE FOR INJECTIONS
    ======================================================================== *)

Lemma SN_inl : forall e T st ctx,
  SN (e, st, ctx) ->
  SN (EInl e T, st, ctx).
Proof.
  intros e T st ctx Hsn.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  (* ST_InlStep: e --> e'0 *)
  apply IH with (y := (e'0, st'', ctx'')).
  unfold step_inv. exact H0.
Qed.

Lemma SN_inr : forall e T st ctx,
  SN (e, st, ctx) ->
  SN (EInr e T, st, ctx).
Proof.
  intros e T st ctx Hsn.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  apply IH with (y := (e'0, st'', ctx'')).
  unfold step_inv. exact H0.
Qed.

(** ========================================================================
    SECTION 7: SN CLOSURE FOR CASE
    ======================================================================== *)

Lemma SN_case : forall e x1 e1 x2 e2 st ctx,
  SN (e, st, ctx) ->
  (* When e is EInl v, the substituted body is SN *)
  (forall v st' ctx',
    value v ->
    SN ([x1 := v] e1, st', ctx')) ->
  (* When e is EInr v, the substituted body is SN *)
  (forall v st' ctx',
    value v ->
    SN ([x2 := v] e2, st', ctx')) ->
  SN (ECase e x1 e1 x2 e2, st, ctx).
Proof.
  intros e x1 e1 x2 e2 st ctx Hsn Hinl Hinr.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_CaseInl: e = EInl v T2 *)
    apply Hinl. exact H.
  
  - (* ST_CaseInr: e = EInr v T1 *)
    apply Hinr. exact H.
  
  - (* ST_CaseStep: e --> e'0 *)
    apply IH with (y := (e'0, st'', ctx'')).
    + unfold step_inv. exact H4.
    + intros v st0 ctx0 Hval.
      apply Hinl. exact Hval.
    + intros v st0 ctx0 Hval.
      apply Hinr. exact Hval.
Qed.

(** ========================================================================
    SECTION 8: SN CLOSURE FOR IF
    ======================================================================== *)

Lemma SN_if : forall e1 e2 e3 st ctx,
  SN (e1, st, ctx) ->
  SN (e2, st, ctx) ->
  SN (e3, st, ctx) ->
  SN (EIf e1 e2 e3, st, ctx).
Proof.
  intros e1 e2 e3 st ctx Hsn1 Hsn2 Hsn3.
  induction Hsn1 as [[[e1' st1'] ctx1'] _ IH1].
  
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_IfTrue: e1 = EBool true *)
    exact Hsn2.
  
  - (* ST_IfFalse: e1 = EBool false *)
    exact Hsn3.
  
  - (* ST_IfStep: e1 --> e1'0 *)
    apply IH1 with (y := (e1'0, st', ctx')).
    + unfold step_inv. exact H3.
    + exact Hsn2.
    + exact Hsn3.
Qed.

(** ========================================================================
    SECTION 9: SN CLOSURE FOR LET
    ======================================================================== *)

Lemma SN_let : forall x e1 e2 st ctx,
  SN (e1, st, ctx) ->
  (* When e1 is a value, the substituted body is SN *)
  (forall v st' ctx',
    value v ->
    SN ([x := v] e2, st', ctx')) ->
  SN (ELet x e1 e2, st, ctx).
Proof.
  intros x e1 e2 st ctx Hsn1 Hbody.
  induction Hsn1 as [[[e1' st1'] ctx1'] _ IH1].
  
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_LetValue: e1 is a value *)
    apply Hbody. exact H.
  
  - (* ST_LetStep: e1 --> e1'0 *)
    apply IH1 with (y := (e1'0, st', ctx')).
    + unfold step_inv. exact H0.
    + intros v st0 ctx0 Hval.
      apply Hbody. exact Hval.
Qed.

(** ========================================================================
    SECTION 10: SN CLOSURE FOR REFERENCES
    ======================================================================== *)

Lemma SN_ref : forall e l st ctx,
  SN (e, st, ctx) ->
  SN (ERef e l, st, ctx).
Proof.
  intros e l st ctx Hsn.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_RefAlloc: e is a value, allocates *)
    apply value_SN. constructor.
  
  - (* ST_RefStep: e --> e'0 *)
    apply IH with (y := (e'0, st'', ctx'')).
    unfold step_inv. exact H0.
Qed.

Lemma SN_deref : forall e st ctx,
  SN (e, st, ctx) ->
  (* When e is a location, dereferencing gives SN result *)
  (forall l v st' ctx',
    e = ELoc l ->
    store_lookup l st' = Some v ->
    SN (v, st', ctx')) ->
  SN (EDeref e, st, ctx).
Proof.
  intros e st ctx Hsn Hlookup.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_DerefLoc: e = ELoc l *)
    apply Hlookup with (l := l).
    + reflexivity.
    + exact H.
  
  - (* ST_DerefStep: e --> e'0 *)
    apply IH with (y := (e'0, st'', ctx'')).
    + unfold step_inv. exact H0.
    + intros l v st0 ctx0 Heq Hlook.
      subst e'0.
      apply value_SN.
      (* v is from store, need to assume store contains values *)
      admit. (* Requires store well-formedness *)
Admitted.

Lemma SN_assign : forall e1 e2 st ctx,
  SN (e1, st, ctx) ->
  SN (e2, st, ctx) ->
  SN (EAssign e1 e2, st, ctx).
Proof.
  intros e1 e2 st ctx Hsn1 Hsn2.
  generalize dependent ctx.
  generalize dependent st.
  generalize dependent e2.
  induction Hsn1 as [[[e1' st1'] ctx1'] _ IH1].
  intros e2 Hsn2 st ctx.
  induction Hsn2 as [[[e2' st2'] ctx2'] _ IH2].
  
  constructor.
  intros [[e' st'] ctx'] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_AssignLoc: both values, assignment happens *)
    apply value_SN. constructor.
  
  - (* ST_Assign1: e1 --> e1'0 *)
    apply IH1 with (y := (e1'0, st', ctx')).
    + unfold step_inv. exact H3.
    + constructor.
      intros [[e'' st''] ctx''] Hstep'.
      inversion Hsn2 as [_ H].
      apply H. unfold step_inv. exact Hstep'.
  
  - (* ST_Assign2: e1 is value, e2 --> e2'0 *)
    apply IH2 with (y := (e2'0, st', ctx')).
    unfold step_inv. exact H4.
Qed.

(** ========================================================================
    SECTION 11: SN CLOSURE FOR HANDLE
    ======================================================================== *)

Lemma SN_handle : forall e x h st ctx,
  SN (e, st, ctx) ->
  (* When e is a value, the handler body is SN *)
  (forall v st' ctx',
    value v ->
    SN ([x := v] h, st', ctx')) ->
  SN (EHandle e x h, st, ctx).
Proof.
  intros e x h st ctx Hsn Hhandler.
  induction Hsn as [[[e' st'] ctx'] _ IH].
  
  constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  
  inversion Hstep; subst.
  
  - (* ST_HandleValue: e is a value *)
    apply Hhandler. exact H.
  
  - (* ST_HandleStep: e --> e'0 *)
    apply IH with (y := (e'0, st'', ctx'')).
    + unfold step_inv. exact H0.
    + intros v st0 ctx0 Hval.
      apply Hhandler. exact Hval.
Qed.

(** ========================================================================
    SECTION 12: SUMMARY
    ======================================================================== *)

(** 
    PROVEN WITH QED:
    - value_SN
    - SN_step
    - SN_pair
    - SN_inl
    - SN_inr
    - SN_case
    - SN_if
    - SN_let
    - SN_ref
    - SN_assign
    - SN_handle
    - SN_fst (with premise)
    - SN_snd (with premise)
    
    ADMITTED:
    - SN_app (requires careful handling of beta reduction)
    - SN_deref (requires store well-formedness)
    
    These lemmas form the backbone of the fundamental theorem proof.
    With these, we can show that well-typed terms are SN by induction
    on the typing derivation.
*)

End SN_Closure.
