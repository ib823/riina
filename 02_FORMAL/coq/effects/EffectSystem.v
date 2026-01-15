(** * Effect Type System for TERAS-LANG
    
    Extended type system including Effect Handling and Capabilities.
    
    This module defines the FULL typing relation including:
    - Effect Operations (perform, handle)
    - Capabilities (require, grant)
    - Security Operations (classify, declassify)
    
    Note: The core TypeSafety proof uses the restricted 'has_type' from
    foundations/Typing.v. This module defines the complete specification.
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Typing.
Require Import TERAS.effects.EffectAlgebra.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(** ** Effect Occurrence Predicate *)

Lemma effect_leq_pure : forall eff, effect_leq EffectPure eff.
Proof.
  intros eff. unfold effect_leq. simpl. apply Nat.le_0_l.
Qed.

Fixpoint performs_within (e : expr) (eff : effect) : Prop :=
  match e with
  | EUnit => True
  | EBool _ => True
  | EInt _ => True
  | EString _ => True
  | ELoc _ => True
  | EVar _ => True
  | ELam _ _ body => performs_within body eff
  | EApp e1 e2 => performs_within e1 eff /\ performs_within e2 eff
  | EPair e1 e2 => performs_within e1 eff /\ performs_within e2 eff
  | EFst e1 => performs_within e1 eff
  | ESnd e1 => performs_within e1 eff
  | EInl e1 _ => performs_within e1 eff
  | EInr e1 _ => performs_within e1 eff
  | ECase e0 _ e1 _ e2 =>
      performs_within e0 eff /\ performs_within e1 eff /\ performs_within e2 eff
  | EIf e1 e2 e3 =>
      performs_within e1 eff /\ performs_within e2 eff /\ performs_within e3 eff
  | ELet _ e1 e2 => performs_within e1 eff /\ performs_within e2 eff
  | EPerform eff' e1 => effect_leq eff' eff /\ performs_within e1 eff
  | EHandle e1 _ h => performs_within e1 eff /\ performs_within h eff
  | ERef e1 _ => performs_within e1 eff
  | EDeref e1 => performs_within e1 eff
  | EAssign e1 e2 => performs_within e1 eff /\ performs_within e2 eff
  | EClassify e1 => performs_within e1 eff
  | EDeclassify e1 e2 => performs_within e1 eff /\ performs_within e2 eff
  | EProve e1 => performs_within e1 eff
  | ERequire _ e1 => performs_within e1 eff
  | EGrant _ e1 => performs_within e1 eff
  end.

Lemma performs_within_mono : forall e eff1 eff2,
  effect_leq eff1 eff2 ->
  performs_within e eff1 ->
  performs_within e eff2.
Proof.
  intros e eff1 eff2 Hle.
  induction e; simpl; intros Hpw; try assumption.
  - apply IHe. exact Hpw.
  - destruct Hpw as [H1 H2]. split; [apply IHe1 | apply IHe2]; assumption.
  - destruct Hpw as [H1 H2]. split; [apply IHe1 | apply IHe2]; assumption.
  - apply IHe. exact Hpw.
  - apply IHe. exact Hpw.
  - apply IHe. exact Hpw.
  - apply IHe. exact Hpw.
  - destruct Hpw as [H0 [H1 H2]]. split; [apply IHe1 | split; [apply IHe2 | apply IHe3]]; assumption.
  - destruct Hpw as [H0 [H1 H2]]. split; [apply IHe1 | split; [apply IHe2 | apply IHe3]]; assumption.
  - destruct Hpw as [H1 H2]. split; [apply IHe1 | apply IHe2]; assumption.
  - destruct Hpw as [Hperf Hinner]. split.
    + eapply effect_leq_trans; eassumption.
    + apply IHe. exact Hinner.
  - destruct Hpw as [H1 H2]. split; [apply IHe1 | apply IHe2]; assumption.
  - apply IHe. exact Hpw.
  - apply IHe. exact Hpw.
  - destruct Hpw as [H1 H2]. split; [apply IHe1 | apply IHe2]; assumption.
  - apply IHe. exact Hpw.
  - destruct Hpw as [H1 H2]. split; [apply IHe1 | apply IHe2]; assumption.
  - apply IHe. exact Hpw.
  - apply IHe. exact Hpw.
Qed.

(** ** Core Effect Soundness *)

Lemma core_effects_within : forall G S D e T eff,
  has_type G S D e T eff ->
  performs_within e eff.
Proof.
  intros G S D e T eff Hty.
  induction Hty; simpl; try auto.
  - (* T_Lam *)
    apply IHHty.
  - (* T_App *)
    split.
    + eapply performs_within_mono.
      * apply effect_join_ub_l.
      * exact IHHty1.
    + eapply performs_within_mono.
      * apply effect_join_ub_r.
      * eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty2].
  - (* T_Pair *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty2].
  - (* T_Fst *)
    exact IHHty.
  - (* T_Snd *)
    exact IHHty.
  - (* T_Inl *)
    exact IHHty.
  - (* T_Inr *)
    exact IHHty.
  - (* T_Case *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + split.
      * eapply performs_within_mono.
        -- apply effect_join_ub_r.
        -- eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty2].
      * eapply performs_within_mono.
        -- apply effect_join_ub_r.
        -- eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty3].
  - (* T_If *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + split.
      * eapply performs_within_mono.
        -- apply effect_join_ub_r.
        -- eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty2].
      * eapply performs_within_mono.
        -- apply effect_join_ub_r.
        -- eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty3].
  - (* T_Let *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty2].
  - (* T_Perform *)
    split.
    + apply effect_join_ub_r.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty].
  - (* T_Handle *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty2].
  - (* T_Ref *)
    eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty].
  - (* T_Deref *)
    eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty].
  - (* T_Assign *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + eapply performs_within_mono.
      * apply effect_join_ub_r.
      * eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty2].
  - (* T_Classify *)
    exact IHHty.
  - (* T_Declassify *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty2].
  - (* T_Prove *)
    exact IHHty.
  - (* T_Require *)
    eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty].
  - (* T_Grant *)
    exact IHHty.
Qed.
(** ** Effect Typing Rules *)

Inductive has_type_full : type_env -> store_ty -> security_level ->
                          expr -> ty -> effect -> Prop :=
  (* Include all core rules *)
  | T_Core : forall G S D e T eff,
      has_type G S D e T eff ->
      has_type_full G S D e T eff

  (* Effect Operations *)
  | T_Perform : forall G S D eff e T ε,
      has_type_full G S D e T ε ->
      has_type_full G S D (EPerform eff e) T (effect_join ε eff)

  | T_Handle : forall G S D e y h T1 T2 ε1 ε2,
      has_type_full G S D e T1 ε1 ->
      has_type_full ((y, T1) :: G) S D h T2 ε2 ->
      has_type_full G S D (EHandle e y h) T2 (effect_join ε1 ε2)

  (* Capabilities *)
  | T_Require : forall G S D eff e T eff_e,
      (* e requires capability for 'eff' *)
      has_type_full G S D e T eff_e ->
      (* The resulting term has effect eff + eff_e *)
      has_type_full G S D (ERequire eff e) T (effect_join eff eff_e)

  | T_Grant : forall G S D eff e T eff_e,
      (* Granting a capability satisfies the requirement in e *)
      has_type_full G S D e T eff_e ->
      (* If e required eff, it is now discharged? 
         Or does it just mean this block has the authority? *)
      has_type_full G S D (EGrant eff e) T eff_e

  (* Security Operations *)
  | T_Classify : forall G S D e T eff,
      has_type_full G S D e T eff ->
      has_type_full G S D (EClassify e) (TSecret T) eff

  | T_Declassify : forall G S D e1 e2 T eff1 eff2,
      has_type_full G S D e1 (TSecret T) eff1 ->
      has_type_full G S D e2 (TProof (TSecret T)) eff2 -> (* Proof of safety *)
      declass_ok e1 e2 ->
      has_type_full G S D (EDeclassify e1 e2) T (effect_join eff1 eff2)

  | T_Prove : forall G S D e T eff,
      has_type_full G S D e T eff ->
      has_type_full G S D (EProve e) (TProof T) eff.

(** ** Effect Safety (Stub)
    
    Theorem: If has_type_full G S D e T eff, then executing e
    only produces effects in eff.
*)
Theorem effect_safety : forall G S D e T eff,
  has_type_full G S D e T eff ->
  (* Operational semantics for traces needed here *)
  performs_within e eff.
Proof.
  intros G S D e T eff Hty.
  induction Hty; simpl.
  - eapply core_effects_within. eassumption.
  - (* T_Perform *)
    split.
    + apply effect_join_ub_r.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty].
  - (* T_Handle *)
    split.
    + eapply performs_within_mono; [apply effect_join_ub_l | exact IHHty1].
    + eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty2].
  - (* T_Require *)
    eapply performs_within_mono; [apply effect_join_ub_r | exact IHHty].
  - (* T_Grant *)
    exact IHHty.
  - (* T_Classify *)
    exact IHHty.
  - (* T_Declassify *)
    split; assumption.
  - (* T_Prove *)
    exact IHHty.
Qed.

(** End of EffectSystem.v *)
