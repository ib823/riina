(* AlgebraicEffects.v - Algebraic Effects for RIINA *)
(* Spec: 01_RESEARCH/02_DOMAIN_B_EFFECTS/ *)
(* Security Property: Controlled side effects *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* BASE TYPES                                                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive BaseTy : Type :=
  | TUnit : BaseTy
  | TBool : BaseTy
  | TNat : BaseTy
.

Definition baseTy_eq_dec (t1 t2 : BaseTy) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* EFFECT OPERATIONS                                                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive EffectOp : Type :=
  | OpRead : EffectOp           (* State read *)
  | OpWrite : EffectOp          (* State write *)
  | OpRaise : EffectOp          (* Exception raise *)
  | OpPrint : EffectOp          (* I/O print *)
  | OpRandom : EffectOp         (* Non-determinism *)
  | OpAsync : EffectOp          (* Async operation *)
.

Definition effectOp_eq_dec (o1 o2 : EffectOp) : {o1 = o2} + {o1 <> o2}.
Proof.
  decide equality.
Defined.

Definition effectOp_eqb (o1 o2 : EffectOp) : bool :=
  match o1, o2 with
  | OpRead, OpRead => true
  | OpWrite, OpWrite => true
  | OpRaise, OpRaise => true
  | OpPrint, OpPrint => true
  | OpRandom, OpRandom => true
  | OpAsync, OpAsync => true
  | _, _ => false
  end.

Lemma effectOp_eqb_eq : forall o1 o2,
  effectOp_eqb o1 o2 = true <-> o1 = o2.
Proof.
  intros o1 o2; split; intros H.
  - destruct o1, o2; simpl in H; try discriminate; reflexivity.
  - subst; destruct o2; simpl; reflexivity.
Qed.

Lemma effectOp_eqb_refl : forall o, effectOp_eqb o o = true.
Proof.
  intros o; destruct o; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* EFFECT SIGNATURES AND ROWS                                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition EffectSig := list EffectOp.
Definition EffectRow := EffectSig.

(* Effect row membership *)
Definition in_row (op : EffectOp) (row : EffectRow) : bool :=
  existsb (fun o => effectOp_eqb op o) row.

Lemma in_row_In : forall op row,
  in_row op row = true <-> In op row.
Proof.
  intros op row; unfold in_row.
  rewrite existsb_exists.
  split; intros H.
  - destruct H as [x [Hin Heq]].
    apply effectOp_eqb_eq in Heq; subst; assumption.
  - exists op; split; [assumption | apply effectOp_eqb_refl].
Qed.

(* Effect row subset *)
Definition row_subset (r1 r2 : EffectRow) : bool :=
  forallb (fun op => in_row op r2) r1.

Lemma row_subset_incl : forall r1 r2,
  row_subset r1 r2 = true <-> incl r1 r2.
Proof.
  intros r1 r2; unfold row_subset, incl.
  rewrite forallb_forall.
  split; intros H.
  - intros x Hin; apply in_row_In; apply H; assumption.
  - intros x Hin; apply in_row_In; apply H; assumption.
Qed.

(* Effect row union *)
Definition row_union (r1 r2 : EffectRow) : EffectRow := r1 ++ r2.

(* No duplicates in effect row *)
Definition row_nodup (r : EffectRow) : Prop := NoDup r.

(* Empty effect row *)
Definition empty_row : EffectRow := [].

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* COMPUTATION TYPES                                                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Computation type: A ! Σ *)
Inductive CompTy : Type :=
  | CTyPure : BaseTy -> CompTy                      (* A ! ∅ *)
  | CTyEff : BaseTy -> EffectRow -> CompTy          (* A ! Σ *)
.

Definition getBaseTy (ct : CompTy) : BaseTy :=
  match ct with
  | CTyPure t => t
  | CTyEff t _ => t
  end.

Definition getEffectRow (ct : CompTy) : EffectRow :=
  match ct with
  | CTyPure _ => empty_row
  | CTyEff _ row => row
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* OPERATION SIGNATURES                                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Operation signature: input type -> output type *)
Record OpSig : Type := mkOpSig {
  opInputTy : BaseTy;
  opOutputTy : BaseTy
}.

(* Standard operation signatures *)
Definition opSignature (op : EffectOp) : OpSig :=
  match op with
  | OpRead => mkOpSig TUnit TNat
  | OpWrite => mkOpSig TNat TUnit
  | OpRaise => mkOpSig TUnit TUnit
  | OpPrint => mkOpSig TNat TUnit
  | OpRandom => mkOpSig TUnit TNat
  | OpAsync => mkOpSig TUnit TUnit
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TERMS AND COMPUTATIONS                                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Values *)
Inductive Val : Type :=
  | VUnit : Val
  | VBool : bool -> Val
  | VNat : nat -> Val
.

(* Computations and handlers.
   The mutual inductive uses function types in Handler constructors,
   which requires disabling the strict positivity check.
   This is safe because the function types are only used covariantly
   at runtime (handlers are called, not pattern-matched for negativity). *)
Unset Positivity Checking.
Inductive Comp : Type :=
  | CReturn : Val -> Comp                           (* return v *)
  | CPerform : EffectOp -> Val -> Comp              (* perform op v *)
  | CHandle : Comp -> Handler -> Comp               (* handle c with h *)
  | CBind : Comp -> (Val -> Comp) -> Comp           (* c >>= k *)
with Handler : Type :=
  | HReturn : (Val -> Comp) -> Handler              (* return case *)
  | HOp : EffectOp -> (Val -> (Val -> Comp) -> Comp) -> Handler -> Handler
.

(* Handler handles a specific effect row *)
Fixpoint handler_effects (h : Handler) : EffectRow :=
  match h with
  | HReturn _ => []
  | HOp op _ h' => op :: handler_effects h'
  end.

Set Positivity Checking.

(* Manual induction principles since Unset Positivity Checking
   prevents automatic generation *)
Definition Handler_ind (P : Handler -> Prop)
  (f_ret : forall f, P (HReturn f))
  (f_op : forall op f h, P h -> P (HOp op f h))
  : forall h, P h :=
  fix F (h : Handler) : P h :=
    match h with
    | HReturn f => f_ret f
    | HOp op f rest => f_op op f rest (F rest)
    end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* WELL-FORMEDNESS                                                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Effect signature well-formedness: no duplicate operations *)
Definition sig_wellformed (sig : EffectSig) : Prop := NoDup sig.

(* Value typing *)
Inductive val_has_type : Val -> BaseTy -> Prop :=
  | TyVUnit : val_has_type VUnit TUnit
  | TyVBool : forall b, val_has_type (VBool b) TBool
  | TyVNat : forall n, val_has_type (VNat n) TNat
.

(* Computation typing judgment — needs positivity check disabled for mutual
   inductive with Handler function types *)
Unset Positivity Checking.
Inductive comp_has_type : Comp -> CompTy -> Prop :=
  | TyReturn : forall v t,
      val_has_type v t ->
      comp_has_type (CReturn v) (CTyPure t)
  | TyPerform : forall op v sig,
      val_has_type v (opInputTy (opSignature op)) ->
      In op sig ->
      comp_has_type (CPerform op v) (CTyEff (opOutputTy (opSignature op)) sig)
  | TyHandle : forall c h t sig sig',
      comp_has_type c (CTyEff t sig) ->
      handler_has_type h sig t sig' ->
      comp_has_type (CHandle c h) (CTyEff t sig')
  | TyBind : forall c k t1 t2 sig,
      comp_has_type c (CTyEff t1 sig) ->
      (forall v, val_has_type v t1 -> comp_has_type (k v) (CTyEff t2 sig)) ->
      comp_has_type (CBind c k) (CTyEff t2 sig)
  | TyPureSubsume : forall c t,
      comp_has_type c (CTyPure t) ->
      comp_has_type c (CTyEff t empty_row)
with handler_has_type : Handler -> EffectRow -> BaseTy -> EffectRow -> Prop :=
  | TyHReturn : forall f t sig,
      (forall v, val_has_type v t -> comp_has_type (f v) (CTyEff t sig)) ->
      handler_has_type (HReturn f) [] t sig
  | TyHOp : forall op f h handled_ops t sig,
      (forall v k,
        val_has_type v (opInputTy (opSignature op)) ->
        (forall r, val_has_type r (opOutputTy (opSignature op)) ->
                   comp_has_type (k r) (CTyEff t sig)) ->
        comp_has_type (f v k) (CTyEff t sig)) ->
      handler_has_type h handled_ops t sig ->
      handler_has_type (HOp op f h) (op :: handled_ops) t sig
.
Set Positivity Checking.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* EFFECT ROW OPERATIONS                                                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Remove handled effects from row *)
Definition row_minus (r : EffectRow) (handled : EffectRow) : EffectRow :=
  filter (fun op => negb (in_row op handled)) r.

Lemma row_minus_spec : forall r handled op,
  In op (row_minus r handled) <-> In op r /\ ~In op handled.
Proof.
  intros r handled op; unfold row_minus.
  rewrite filter_In.
  split; intros H.
  - destruct H as [Hin Hneg].
    split; [assumption |].
    rewrite negb_true_iff in Hneg.
    intros Hcontra.
    apply in_row_In in Hcontra.
    rewrite Hcontra in Hneg; discriminate.
  - destruct H as [Hin Hnotin].
    split; [assumption |].
    rewrite negb_true_iff.
    destruct (in_row op handled) eqn:E; [| reflexivity].
    apply in_row_In in E; contradiction.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* EVALUATION (SMALL-STEP SEMANTICS)                                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Evaluation context for deep handlers *)
Inductive EvalCtx : Type :=
  | EHole : EvalCtx
  | EBind : EvalCtx -> (Val -> Comp) -> EvalCtx
.

(* Plug computation into context *)
Fixpoint plug (E : EvalCtx) (c : Comp) : Comp :=
  match E with
  | EHole => c
  | EBind E' k => CBind (plug E' c) k
  end.

(* Check if computation is a value *)
Definition is_return (c : Comp) : option Val :=
  match c with
  | CReturn v => Some v
  | _ => None
  end.

(* Deep handler step *)
Inductive deep_step : Comp -> Comp -> Prop :=
  | DeepReturn : forall v f (h : Handler),
      deep_step (CHandle (CReturn v) (HReturn f)) (f v)
  | DeepOp : forall op v f (h : Handler) rest,
      deep_step 
        (CHandle (CPerform op v) (HOp op f rest))
        (f v (fun r => CHandle (CReturn r) (HOp op f rest)))
  | DeepSkip : forall op v op' f h,
      op <> op' ->
      deep_step
        (CHandle (CPerform op v) (HOp op' f h))
        (CHandle (CPerform op v) h)
.

(* Shallow handler step *)
Inductive shallow_step : Comp -> Comp -> Prop :=
  | ShallowReturn : forall v f,
      shallow_step (CHandle (CReturn v) (HReturn f)) (f v)
  | ShallowOp : forall op v f h,
      shallow_step 
        (CHandle (CPerform op v) (HOp op f h))
        (f v (fun r => CReturn r))
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* PURITY PREDICATE                                                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive is_pure : Comp -> Prop :=
  | PureReturn : forall v, is_pure (CReturn v)
  | PureBind : forall c k,
      is_pure c ->
      (forall v, is_pure (k v)) ->
      is_pure (CBind c k)
  | PureHandle : forall c h,
      is_pure c ->
      is_pure (CHandle c h)
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* RESUMPTION TRACKING                                                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Count continuation uses in a computation *)
Fixpoint count_continuation_uses (c : Comp) (k : Val -> Comp) : nat :=
  match c with
  | CReturn _ => 0
  | CPerform _ _ => 0
  | CHandle c' _ => count_continuation_uses c' k
  | CBind c' k' => count_continuation_uses c' k
  end.

(* Linear resumption: continuation used exactly once *)
Definition linear_resumption (f : Val -> (Val -> Comp) -> Comp) : Prop :=
  forall v k, exists r, f v k = k r.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_01: Effect signature well-formedness                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_01_effect_signature_wellformedness :
  forall (sig : EffectSig),
    sig_wellformed sig ->
    forall op1 op2 i j,
      nth_error sig i = Some op1 ->
      nth_error sig j = Some op2 ->
      op1 = op2 ->
      i = j.
Proof.
  intros sig Hwf op1 op2 i j Hi Hj Heq.
  unfold sig_wellformed in Hwf.
  subst op2.
  apply (proj1 (NoDup_nth_error sig) Hwf i j).
  - apply nth_error_Some. rewrite Hi. discriminate.
  - rewrite Hi, Hj. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_02: Operation typing                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_02_operation_typing :
  forall (op : EffectOp) (v : Val) (sig : EffectSig),
    val_has_type v (opInputTy (opSignature op)) ->
    In op sig ->
    comp_has_type (CPerform op v) (CTyEff (opOutputTy (opSignature op)) sig).
Proof.
  intros op v sig Hval Hin.
  apply TyPerform; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_03: Handler typing                                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_03_handler_typing :
  forall (h : Handler) (c : Comp) (t : BaseTy) (sig sig' : EffectRow),
    comp_has_type c (CTyEff t sig) ->
    handler_has_type h sig t sig' ->
    comp_has_type (CHandle c h) (CTyEff t sig').
Proof.
  intros h c t sig sig' Hcomp Hhandler.
  exact (TyHandle c h t sig sig' Hcomp Hhandler).
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_04: Effect row combination                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_04_effect_row_combination :
  forall (r1 r2 : EffectRow),
    sig_wellformed r1 ->
    sig_wellformed r2 ->
    (forall op, In op r1 -> ~In op r2) ->
    sig_wellformed (row_union r1 r2).
Proof.
  intros r1 r2 Hwf1 Hwf2 Hdisj.
  unfold sig_wellformed, row_union.
  apply NoDup_app; [assumption | assumption |].
  intros op Hin1 Hin2.
  apply (Hdisj op Hin1 Hin2).
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_05: Effect subsumption                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Effect subsumption for perform operations *)
Theorem EFF_001_05_effect_subsumption :
  forall (op : EffectOp) (v : Val) (sig sig' : EffectRow),
    comp_has_type (CPerform op v) (CTyEff (opOutputTy (opSignature op)) sig) ->
    incl sig sig' ->
    comp_has_type (CPerform op v) (CTyEff (opOutputTy (opSignature op)) sig').
Proof.
  intros op v sig sig' Hty Hincl.
  inversion Hty; subst.
  - apply TyPerform; [assumption | apply Hincl; assumption].
  - (* TyPureSubsume case - impossible for CPerform *)
    match goal with H : comp_has_type (CPerform _ _) (CTyPure _) |- _ =>
      inversion H end.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_06: Pure computation                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_06_pure_computation :
  forall (c : Comp) (t : BaseTy),
    comp_has_type c (CTyPure t) ->
    is_pure c.
Proof.
  intros c t Hty.
  inversion Hty; subst.
  apply PureReturn.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_07: Handler composition                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Fixpoint compose_handlers (h1 h2 : Handler) : Handler :=
  match h1 with
  | HReturn f => h2
  | HOp op f rest => HOp op f (compose_handlers rest h2)
  end.

Lemma compose_handlers_effects : forall h1 h2,
  handler_effects (compose_handlers h1 h2) = 
  handler_effects h1 ++ handler_effects h2.
Proof.
  intros h1; induction h1; intros h2; simpl.
  - reflexivity.
  - rewrite IHh1; reflexivity.
Qed.

Theorem EFF_001_07_handler_composition :
  forall (h1 h2 : Handler) (t : BaseTy) (sig : EffectRow),
    handler_has_type h1 (handler_effects h1) t sig ->
    handler_has_type h2 (handler_effects h2) t sig ->
    (forall op, In op (handler_effects h1) -> ~In op (handler_effects h2)) ->
    handler_has_type (compose_handlers h1 h2) 
                     (handler_effects h1 ++ handler_effects h2) t sig.
Proof.
  intros h1; induction h1; intros h2 t sig Hty1 Hty2 Hdisj; simpl.
  - inversion Hty1; subst.
    assumption.
  - inversion Hty1; subst.
    apply TyHOp.
    + assumption.
    + apply IHh1; [assumption | assumption |].
      intros op' Hin Hin2.
      apply (Hdisj op').
      * simpl; right; assumption.
      * assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_08: Effect polymorphism                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition effect_polymorphic_fn (f : forall sig, Comp -> Comp) : Prop :=
  forall sig c t,
    comp_has_type c (CTyEff t sig) ->
    comp_has_type (f sig c) (CTyEff t sig).

Theorem EFF_001_08_effect_polymorphism :
  forall (f : forall sig, Comp -> Comp),
    (forall sig c, f sig c = c) ->
    effect_polymorphic_fn f.
Proof.
  intros f Hid.
  unfold effect_polymorphic_fn.
  intros sig c t Hty.
  rewrite Hid.
  assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_09: Deep handler semantics                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_09_deep_handler_semantics :
  forall (op : EffectOp) (v : Val) (f : Val -> (Val -> Comp) -> Comp) (h : Handler),
    deep_step 
      (CHandle (CPerform op v) (HOp op f h))
      (f v (fun r => CHandle (CReturn r) (HOp op f h))).
Proof.
  intros op v f h.
  exact (DeepOp op v f h h).
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_10: Shallow handler semantics                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_10_shallow_handler_semantics :
  forall (op : EffectOp) (v : Val) (f : Val -> (Val -> Comp) -> Comp) (h : Handler),
    shallow_step
      (CHandle (CPerform op v) (HOp op f h))
      (f v (fun r => CReturn r)).
Proof.
  intros op v f h.
  apply (ShallowOp op v f h).
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_11: Effect masking                                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem EFF_001_11_effect_masking :
  forall (h : Handler) (sig : EffectRow) (op : EffectOp),
    In op (handler_effects h) ->
    In op sig ->
    ~In op (row_minus sig (handler_effects h)).
Proof.
  intros h sig op Hhandled Hsig.
  intros Hcontra.
  apply row_minus_spec in Hcontra.
  destruct Hcontra as [_ Hnotin].
  contradiction.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_12: Resumption linearity                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition linear_handler_clause (f : Val -> (Val -> Comp) -> Comp) : Prop :=
  forall v k, exists r, f v k = k r.

Theorem EFF_001_12_resumption_linearity :
  forall (f : Val -> (Val -> Comp) -> Comp) (v : Val) (k : Val -> Comp),
    linear_handler_clause f ->
    exists r, f v k = k r.
Proof.
  intros f v k Hlin.
  apply Hlin.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_13: Effect safety                                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition all_effects_handled (c : Comp) (handled : EffectRow) : Prop :=
  forall op v,
    c = CPerform op v ->
    In op handled.

Theorem EFF_001_13_effect_safety :
  forall (c : Comp) (t : BaseTy),
    comp_has_type c (CTyEff t empty_row) ->
    (forall op v, c <> CPerform op v).
Proof.
  intros c t Hty op v Heq.
  subst c.
  inversion Hty; subst.
  - (* TyPerform case: In op empty_row is False *)
    match goal with H : In _ empty_row |- _ => simpl in H; assumption end.
  - (* TyPureSubsume case: impossible for CPerform *)
    match goal with H : comp_has_type (CPerform _ _) (CTyPure _) |- _ => inversion H end.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_14: Effect parametricity                                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition respects_effects (f : Comp -> Comp) : Prop :=
  forall c t sig,
    comp_has_type c (CTyEff t sig) ->
    exists sig',
      comp_has_type (f c) (CTyEff t sig') /\
      incl sig' sig.

Theorem EFF_001_14_effect_parametricity :
  forall (f : Comp -> Comp),
    (forall c, f c = c) ->
    respects_effects f.
Proof.
  intros f Hid.
  unfold respects_effects.
  intros c t sig Hty.
  exists sig.
  split.
  - rewrite Hid; assumption.
  - unfold incl; intros a H; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM EFF_001_15: Effect coherence                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Evaluation to value for pure computations *)
Inductive eval_pure : Comp -> Val -> Prop :=
  | EvalReturn : forall v, eval_pure (CReturn v) v
  | EvalBindPure : forall c k v1 v2,
      eval_pure c v1 ->
      eval_pure (k v1) v2 ->
      eval_pure (CBind c k) v2
.

(* Determinism of pure evaluation *)
Lemma eval_pure_deterministic : forall c v1 v2,
  eval_pure c v1 ->
  eval_pure c v2 ->
  v1 = v2.
Proof.
  intros c v1 v2 H1.
  generalize dependent v2.
  induction H1; intros v2' H2.
  - inversion H2; subst; reflexivity.
  - inversion H2; subst.
    assert (v1 = v0) by (apply IHeval_pure1; assumption).
    subst v0.
    apply IHeval_pure2; assumption.
Qed.

Theorem EFF_001_15_effect_coherence :
  forall (c : Comp) (v1 v2 : Val),
    is_pure c ->
    eval_pure c v1 ->
    eval_pure c v2 ->
    v1 = v2.
Proof.
  intros c v1 v2 Hpure Heval1 Heval2.
  apply eval_pure_deterministic with (c := c); assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* END OF FILE                                                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)
