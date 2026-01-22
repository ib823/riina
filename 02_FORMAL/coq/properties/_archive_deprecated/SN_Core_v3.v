(** * Strong Normalization Core - ALL PROOFS COMPLETE

    This file contains the core definitions and lemmas for strong normalization.
    ALL lemmas are proven with Qed. ZERO Admitted.

    Mode: ULTRA KIASU | ZERO COMPILATION ERRORS | EXTREME RIGOUR
    Date: 2026-01-18
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(** ========================================================================
    SECTION 1: CONFIGURATION AND SN DEFINITIONS
    ======================================================================== *)

Definition config := (expr * store * effect_ctx)%type.

(** Inverse step relation for well-foundedness *)
Definition step_inv (cfg1 cfg2 : config) : Prop :=
  let '(e2, st2, ctx2) := cfg2 in
  let '(e1, st1, ctx1) := cfg1 in
  (e2, st2, ctx2) --> (e1, st1, ctx1).

(** Strong normalization: all reduction paths terminate *)
Definition SN (cfg : config) : Prop := Acc step_inv cfg.

(** SN for expressions *)
Definition SN_expr (e : expr) : Prop :=
  forall st ctx, SN (e, st, ctx).

(** ========================================================================
    SECTION 2: VALUE-DOES-NOT-STEP LEMMA
    ======================================================================== *)

(** Auxiliary: values have specific forms that don't match step LHS *)
Lemma value_canonical : forall v,
  value v ->
  v = EUnit \/
  (exists b, v = EBool b) \/
  (exists n, v = EInt n) \/
  (exists s, v = EString s) \/
  (exists l, v = ELoc l) \/
  (exists x T e, v = ELam x T e) \/
  (exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2) \/
  (exists v' T, v = EInl v' T /\ value v') \/
  (exists v' T, v = EInr v' T /\ value v') \/
  (exists v', v = EClassify v' /\ value v') \/
  (exists v', v = EProve v' /\ value v').
Proof.
  intros v Hval. destruct Hval.
  - left. reflexivity.
  - right. left. exists b. reflexivity.
  - right. right. left. exists n. reflexivity.
  - right. right. right. left. exists s. reflexivity.
  - right. right. right. right. left. exists l. reflexivity.
  - right. right. right. right. right. left. exists x, T, e. reflexivity.
  - right. right. right. right. right. right. left.
    exists v1, v2. split. reflexivity. split; assumption.
  - right. right. right. right. right. right. right. left.
    exists v, T. split. reflexivity. assumption.
  - right. right. right. right. right. right. right. right. left.
    exists v, T. split. reflexivity. assumption.
  - right. right. right. right. right. right. right. right. right. left.
    exists v. split. reflexivity. assumption.
  - right. right. right. right. right. right. right. right. right. right.
    exists v. split. reflexivity. assumption.
Qed.

(** Main lemma: values don't step *)
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

(** Negation form for convenience *)
Lemma value_no_step : forall v st ctx e' st' ctx',
  value v ->
  ~ (v, st, ctx) --> (e', st', ctx').
Proof.
  intros v st ctx e' st' ctx' Hval Hstep.
  apply (value_not_step v st ctx e' st' ctx' Hval Hstep).
Qed.

(** ========================================================================
    SECTION 3: BASIC SN PROPERTIES
    ======================================================================== *)

(** If cfg --> cfg', and cfg is SN, then cfg' is SN *)
Lemma SN_step : forall e st ctx e' st' ctx',
  SN (e, st, ctx) ->
  (e, st, ctx) --> (e', st', ctx') ->
  SN (e', st', ctx').
Proof.
  intros e st ctx e' st' ctx' Hsn Hstep.
  inversion Hsn. apply H.
  unfold step_inv. exact Hstep.
Qed.

(** Values are trivially SN (no reduction possible) *)
Lemma value_SN : forall v st ctx,
  value v ->
  SN (v, st, ctx).
Proof.
  intros v st ctx Hval. constructor.
  intros [[e' st'] ctx'] Hstep_inv.
  unfold step_inv in Hstep_inv. exfalso.
  apply (value_not_step v st ctx e' st' ctx' Hval Hstep_inv).
Qed.

(** ========================================================================
    SECTION 4: SN CLOSURE UNDER SYNTACTIC FORMS

    Strategy: For each form F[e], we prove:
      SN(e) -> SN(F[e])

    The proof uses Acc induction on SN(e). For each step of F[e]:
    - If it's a computation step (e.g., ST_IfTrue), the result is SN
      by the premise or by value_SN.
    - If it's a congruence step (e.g., ST_IfStep), we use the IH on
      the stepped subterm.

    Key insight: We use generalized auxiliary lemmas that work over
    abstract configurations to get proper induction hypotheses.
    ======================================================================== *)

(** ============ SN_inl ============ *)
Lemma SN_inl_aux : forall cfg T,
  SN cfg -> SN (EInl (fst (fst cfg)) T, snd (fst cfg), snd cfg).
Proof.
  intros cfg T Hsn.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  apply (IH (e'0, st', ctx')). unfold step_inv. simpl. assumption.
Qed.

Lemma SN_inl : forall e T st ctx, SN (e, st, ctx) -> SN (EInl e T, st, ctx).
Proof. intros. exact (SN_inl_aux (e, st, ctx) T H). Qed.

(** ============ SN_inr ============ *)
Lemma SN_inr_aux : forall cfg T,
  SN cfg -> SN (EInr (fst (fst cfg)) T, snd (fst cfg), snd cfg).
Proof.
  intros cfg T Hsn.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  apply (IH (e'0, st', ctx')). unfold step_inv. simpl. assumption.
Qed.

Lemma SN_inr : forall e T st ctx, SN (e, st, ctx) -> SN (EInr e T, st, ctx).
Proof. intros. exact (SN_inr_aux (e, st, ctx) T H). Qed.

(** ============ SN_ref ============ *)
Lemma SN_ref_aux : forall cfg sl,
  SN cfg -> SN (ERef (fst (fst cfg)) sl, snd (fst cfg), snd cfg).
Proof.
  intros cfg sl Hsn.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_RefStep *)
    apply (IH (e'0, st', ctx')). unfold step_inv. simpl. assumption. }
  { (* ST_RefValue: result is ELoc l, a value *)
    apply value_SN. constructor. }
Qed.

Lemma SN_ref : forall e sl st ctx, SN (e, st, ctx) -> SN (ERef e sl, st, ctx).
Proof. intros. exact (SN_ref_aux (e, st, ctx) sl H). Qed.

(** ============ SN_fst ============ *)
Lemma SN_fst_aux : forall cfg,
  SN cfg -> SN (EFst (fst (fst cfg)), snd (fst cfg), snd cfg).
Proof.
  intros cfg Hsn.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_Fst: e = EPair v1 v2, result is v1 which is a value *)
    apply value_SN. assumption. }
  { (* ST_FstStep: e --> e'0 *)
    apply (IH (e'0, st', ctx')). unfold step_inv. simpl. assumption. }
Qed.

Lemma SN_fst : forall e st ctx, SN (e, st, ctx) -> SN (EFst e, st, ctx).
Proof. intros. exact (SN_fst_aux (e, st, ctx) H). Qed.

(** ============ SN_snd ============ *)
Lemma SN_snd_aux : forall cfg,
  SN cfg -> SN (ESnd (fst (fst cfg)), snd (fst cfg), snd cfg).
Proof.
  intros cfg Hsn.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_Snd: e = EPair v1 v2, result is v2 which is a value *)
    apply value_SN. assumption. }
  { (* ST_SndStep: e --> e'0 *)
    apply (IH (e'0, st', ctx')). unfold step_inv. simpl. assumption. }
Qed.

Lemma SN_snd : forall e st ctx, SN (e, st, ctx) -> SN (ESnd e, st, ctx).
Proof. intros. exact (SN_snd_aux (e, st, ctx) H). Qed.

(** ============ SN_if ============
    Note: The premise requires SN for branches at all stores/contexts,
    since the condition may modify the store during evaluation. *)
Lemma SN_if_aux : forall cfg e2 e3,
  SN cfg ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  (forall st' ctx', SN (e3, st', ctx')) ->
  SN (EIf (fst (fst cfg)) e2 e3, snd (fst cfg), snd cfg).
Proof.
  intros cfg e2 e3 Hsn Htrue Hfalse.
  induction Hsn as [[[e1 st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_IfTrue *) apply Htrue. }
  { (* ST_IfFalse *) apply Hfalse. }
  { (* ST_IfStep *)
    apply (IH (e1', st', ctx')). unfold step_inv. simpl. assumption. }
Qed.

Lemma SN_if : forall e1 e2 e3 st ctx,
  SN (e1, st, ctx) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  (forall st' ctx', SN (e3, st', ctx')) ->
  SN (EIf e1 e2 e3, st, ctx).
Proof. intros. exact (SN_if_aux (e1, st, ctx) e2 e3 H H0 H1). Qed.

(** ============ SN_let ============ *)
Lemma SN_let_aux : forall cfg x e2,
  SN cfg ->
  (forall v st' ctx', value v -> SN ([x := v] e2, st', ctx')) ->
  SN (ELet x (fst (fst cfg)) e2, snd (fst cfg), snd cfg).
Proof.
  intros cfg x e2 Hsn Hbody.
  induction Hsn as [[[e1 st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_LetValue *) apply Hbody. assumption. }
  { (* ST_LetStep *)
    apply (IH (e1', st', ctx')). unfold step_inv. simpl. assumption. }
Qed.

Lemma SN_let : forall x e1 e2 st ctx,
  SN (e1, st, ctx) ->
  (forall v st' ctx', value v -> SN ([x := v] e2, st', ctx')) ->
  SN (ELet x e1 e2, st, ctx).
Proof. intros. exact (SN_let_aux (e1, st, ctx) x e2 H H0). Qed.

(** ============ SN_handle ============ *)
Lemma SN_handle_aux : forall cfg x h,
  SN cfg ->
  (forall v st' ctx', value v -> SN ([x := v] h, st', ctx')) ->
  SN (EHandle (fst (fst cfg)) x h, snd (fst cfg), snd cfg).
Proof.
  intros cfg x h Hsn Hhandler.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_HandleStep *)
    apply (IH (e'0, st', ctx')). unfold step_inv. simpl. assumption. }
  { (* ST_HandleValue *) apply Hhandler. assumption. }
Qed.

Lemma SN_handle : forall e x h st ctx,
  SN (e, st, ctx) ->
  (forall v st' ctx', value v -> SN ([x := v] h, st', ctx')) ->
  SN (EHandle e x h, st, ctx).
Proof. intros. exact (SN_handle_aux (e, st, ctx) x h H H0). Qed.

(** ============ SN_case ============ *)
Lemma SN_case_aux : forall cfg x1 e1 x2 e2,
  SN cfg ->
  (forall v st' ctx', value v -> SN ([x1 := v] e1, st', ctx')) ->
  (forall v st' ctx', value v -> SN ([x2 := v] e2, st', ctx')) ->
  SN (ECase (fst (fst cfg)) x1 e1 x2 e2, snd (fst cfg), snd cfg).
Proof.
  intros cfg x1 e1 x2 e2 Hsn Hinl Hinr.
  induction Hsn as [[[e st] ctx] Hacc IH]. simpl. constructor.
  intros [[e' st'] ctx'] Hstep. unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  { (* ST_CaseInl *) apply Hinl. assumption. }
  { (* ST_CaseInr *) apply Hinr. assumption. }
  { (* ST_CaseStep *)
    apply (IH (e'0, st', ctx')). unfold step_inv. simpl. assumption. }
Qed.

Lemma SN_case : forall e x1 e1 x2 e2 st ctx,
  SN (e, st, ctx) ->
  (forall v st' ctx', value v -> SN ([x1 := v] e1, st', ctx')) ->
  (forall v st' ctx', value v -> SN ([x2 := v] e2, st', ctx')) ->
  SN (ECase e x1 e1 x2 e2, st, ctx).
Proof. intros. exact (SN_case_aux (e, st, ctx) x1 e1 x2 e2 H H0 H1). Qed.

(** ============ SN_pair ============
    This requires nested induction with store-polymorphic premise for e2.
    When EPair e1 e2 steps:
    - ST_Pair1: e1 steps to e1', store may change; use outer IH
    - ST_Pair2: e1 is value, e2 steps to e2'; use inner IH

    Key insight: e2's SN must hold for ALL stores because e1's evaluation
    may modify the store before we start evaluating e2. *)

(** Helper: When e1 is already a value, SN_pair follows from SN e2 *)
Lemma SN_pair_value_left_aux : forall v cfg,
  value v ->
  SN cfg ->
  SN (EPair v (fst (fst cfg)), snd (fst cfg), snd cfg).
Proof.
  intros v cfg Hv Hsn2.
  induction Hsn2 as [[[e2 st] ctx] Hacc2 IH2].
  simpl. constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  - (* ST_Pair1: v --> e1' - but v is a value, contradiction *)
    exfalso. apply (value_not_step v st ctx e1' st'' ctx'' Hv H0).
  - (* ST_Pair2: value v, e2 --> e2' *)
    apply (IH2 (e2', st'', ctx'')).
    unfold step_inv. simpl. assumption.
Qed.

Lemma SN_pair_value_left : forall v e2 st ctx,
  value v ->
  SN (e2, st, ctx) ->
  SN (EPair v e2, st, ctx).
Proof.
  intros v e2 st ctx Hv Hsn2.
  exact (SN_pair_value_left_aux v (e2, st, ctx) Hv Hsn2).
Qed.

(** General case with store-polymorphic premise *)
Lemma SN_pair_aux : forall cfg e2,
  SN cfg ->
  (forall st ctx, SN (e2, st, ctx)) ->
  SN (EPair (fst (fst cfg)) e2, snd (fst cfg), snd cfg).
Proof.
  intros cfg e2 Hsn1 Hsn2.
  induction Hsn1 as [[[e1 st] ctx] Hacc1 IH1].
  simpl. constructor.
  intros [[e'' st''] ctx''] Hstep.
  unfold step_inv in Hstep. simpl in Hstep.
  inversion Hstep; subst.
  - (* ST_Pair1: e1 --> e1' *)
    apply (IH1 (e1', st'', ctx'')).
    unfold step_inv. simpl. assumption.
  - (* ST_Pair2: value e1, e2 --> e2' *)
    (* Get SN for e2' from SN for e2 using SN_step *)
    assert (Hsn2': SN (e2', st'', ctx'')).
    { apply (SN_step e2 st ctx e2' st'' ctx'').
      - apply Hsn2.
      - assumption. }
    apply SN_pair_value_left; [assumption | exact Hsn2'].
Qed.

Lemma SN_pair : forall e1 e2 st ctx,
  (forall st' ctx', SN (e1, st', ctx')) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  SN (EPair e1 e2, st, ctx).
Proof.
  intros e1 e2 st ctx Hsn1 Hsn2.
  exact (SN_pair_aux (e1, st, ctx) e2 (Hsn1 st ctx) Hsn2).
Qed.

(** ========================================================================
    SECTION 5: SUMMARY
    ======================================================================== *)

(**
    ALL LEMMAS PROVEN WITH Qed:

    Section 2 - Value Properties:
    1. value_canonical - canonical form of values
    2. value_not_step - values don't step (positive form)
    3. value_no_step - values don't step (negation form)

    Section 3 - Basic SN Properties:
    4. SN_step - SN preserved by stepping
    5. value_SN - values are SN

    Section 4 - SN Closure Under Syntactic Forms:
    6. SN_inl - EInl of SN term is SN
    7. SN_inr - EInr of SN term is SN
    8. SN_ref - ERef of SN term is SN
    9. SN_fst - EFst of SN term is SN
    10. SN_snd - ESnd of SN term is SN
    11. SN_if - EIf of SN terms is SN (with store-polymorphic branch premises)
    12. SN_let - ELet of SN term is SN (with store-polymorphic body premise)
    13. SN_handle - EHandle of SN term is SN (with store-polymorphic handler premise)
    14. SN_case - ECase of SN term is SN (with store-polymorphic branch premises)
    15. SN_pair_value_left - EPair with value first component is SN
    16. SN_pair - EPair of SN terms is SN (with store-polymorphic premises)

    KEY INSIGHT: Store-polymorphic premises (forall st ctx, SN (..., st, ctx))
    are required because evaluation of one subterm may modify the store before
    evaluation of another subterm begins.

    ZERO Admitted. ZERO compilation errors.
    Mode: ULTRA KIASU | EXTREME RIGOUR | ALL PROOFS VERIFIED
*)

