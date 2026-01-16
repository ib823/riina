(** * Effect Type System for RIINA
    
    Extended type system including Effect Handling and Capabilities.
    
    This module defines the FULL typing relation including:
    - Effect Operations (perform, handle)
    - Capabilities (require, grant)
    - Security Operations (classify, declassify)
    
    Note: The core TypeSafety proof uses the restricted 'has_type' from
    foundations/Typing.v. This module defines the complete specification.
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.effects.EffectAlgebra.
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
  | ELam _ _ _ => True  (* Lambda body not evaluated at creation time *)
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
  (* EApp *)
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
  - apply IHe. exact Hpw.  (* EGrant case *)
Qed.

(** ** Core Effect Soundness *)

(** Helper lemmas for effect ordering in complex cases *)

Lemma effect_leq_join_ub_l_trans : forall e1 e2 e3,
  effect_leq e1 (effect_join e2 (effect_join e1 e3)).
Proof.
  intros e1 e2 e3.
  eapply effect_leq_trans.
  - apply effect_join_ub_l.
  - apply effect_join_ub_r.
Qed.

Lemma effect_leq_join_ub_r_trans : forall e1 e2 e3,
  effect_leq e3 (effect_join e2 (effect_join e1 e3)).
Proof.
  intros e1 e2 e3.
  eapply effect_leq_trans.
  - apply effect_join_ub_r.
  - apply effect_join_ub_r.
Qed.

Lemma core_effects_within : forall G S D e T eff,
  has_type G S D e T eff ->
  performs_within e eff.
Proof.
  intros G S D e T eff Hty.
  induction Hty; simpl.

  (* T_Unit *) - trivial.
  (* T_Bool *) - trivial.
  (* T_Int *) - trivial.
  (* T_String *) - trivial.
  (* T_Loc *) - trivial.
  (* T_Var *) - trivial.
  (* T_Lam *) - trivial.

  (* T_App: e = EApp e1 e2, eff = effect_join ε (effect_join ε1 ε2) *)
  - split.
    + apply (performs_within_mono e1 ε1); [| exact IHHty1].
      eapply effect_leq_trans; [apply effect_join_ub_l | apply effect_join_ub_r].
    + apply (performs_within_mono e2 ε2); [| exact IHHty2].
      eapply effect_leq_trans; [apply effect_join_ub_r | apply effect_join_ub_r].

  (* T_Pair: e = EPair e1 e2, eff = effect_join ε1 ε2 *)
  - split.
    + apply (performs_within_mono e1 ε1); [apply effect_join_ub_l | exact IHHty1].
    + apply (performs_within_mono e2 ε2); [apply effect_join_ub_r | exact IHHty2].

  (* T_Fst: eff = ε *)
  - exact IHHty.

  (* T_Snd: eff = ε *)
  - exact IHHty.

  (* T_Inl: eff = ε *)
  - exact IHHty.

  (* T_Inr: eff = ε *)
  - exact IHHty.

  (* T_Case: eff = effect_join ε (effect_join ε1 ε2) *)
  - split.
    + apply (performs_within_mono e ε); [apply effect_join_ub_l | exact IHHty1].
    + split.
      * apply (performs_within_mono e1 ε1); [| exact IHHty2].
        eapply effect_leq_trans; [apply effect_join_ub_l | apply effect_join_ub_r].
      * apply (performs_within_mono e2 ε2); [| exact IHHty3].
        eapply effect_leq_trans; [apply effect_join_ub_r | apply effect_join_ub_r].

  (* T_If: eff = effect_join ε1 (effect_join ε2 ε3) *)
  - split.
    + apply (performs_within_mono e1 ε1); [apply effect_join_ub_l | exact IHHty1].
    + split.
      * apply (performs_within_mono e2 ε2); [| exact IHHty2].
        eapply effect_leq_trans; [apply effect_join_ub_l | apply effect_join_ub_r].
      * apply (performs_within_mono e3 ε3); [| exact IHHty3].
        eapply effect_leq_trans; [apply effect_join_ub_r | apply effect_join_ub_r].

  (* T_Let: eff = effect_join ε1 ε2 *)
  - split.
    + apply (performs_within_mono e1 ε1); [apply effect_join_ub_l | exact IHHty1].
    + apply (performs_within_mono e2 ε2); [apply effect_join_ub_r | exact IHHty2].

  (* T_Perform: eff = effect_join ε eff0 *)
  - split.
    + apply effect_join_ub_r.
    + apply (performs_within_mono e ε); [apply effect_join_ub_l | exact IHHty].

  (* T_Handle: eff = effect_join ε1 ε2 *)
  - split.
    + apply (performs_within_mono e ε1); [apply effect_join_ub_l | exact IHHty1].
    + apply (performs_within_mono h ε2); [apply effect_join_ub_r | exact IHHty2].

  (* T_Ref: eff = effect_join ε EffectWrite *)
  - apply (performs_within_mono e ε); [apply effect_join_ub_l | exact IHHty].

  (* T_Deref: eff = effect_join ε EffectRead *)
  - apply (performs_within_mono e ε); [apply effect_join_ub_l | exact IHHty].

  (* T_Assign: eff = effect_join ε1 (effect_join ε2 EffectWrite) *)
  - split.
    + apply (performs_within_mono e1 ε1); [apply effect_join_ub_l | exact IHHty1].
    + apply (performs_within_mono e2 ε2); [| exact IHHty2].
      eapply effect_leq_trans; [apply effect_join_ub_l | apply effect_join_ub_r].

  (* T_Classify: eff = ε *)
  - exact IHHty.

  (* T_Declassify: eff = effect_join ε1 ε2 *)
  - split.
    + apply (performs_within_mono e1 ε1); [apply effect_join_ub_l | exact IHHty1].
    + apply (performs_within_mono e2 ε2); [apply effect_join_ub_r | exact IHHty2].

  (* T_Prove: eff = ε *)
  - exact IHHty.

  (* T_Require: eff = effect_join ε eff0 *)
  - apply (performs_within_mono e ε); [apply effect_join_ub_l | exact IHHty].

  (* T_Grant: eff = ε *)
  - exact IHHty.
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

(** ** Effect Safety

    Theorem: If has_type_full G S D e T eff, then executing e
    only produces effects in eff.
*)
Theorem effect_safety : forall G S D e T eff,
  has_type_full G S D e T eff ->
  performs_within e eff.
Proof.
  intros G S D e T eff Hty.
  induction Hty; simpl.

  (* T_Core: use core_effects_within *)
  - apply core_effects_within with (G := G) (S := S) (D := D) (T := T).
    exact H.

  (* T_Perform: e = EPerform eff' e1, eff = effect_join ε eff' *)
  - split.
    + apply effect_join_ub_r.
    + apply (performs_within_mono e ε).
      * apply effect_join_ub_l.
      * exact IHHty.

  (* T_Handle: e = EHandle e1 y h, eff = effect_join ε1 ε2 *)
  - split.
    + apply (performs_within_mono e ε1).
      * apply effect_join_ub_l.
      * exact IHHty1.
    + apply (performs_within_mono h ε2).
      * apply effect_join_ub_r.
      * exact IHHty2.

  (* T_Require: e = ERequire eff' e1, eff = effect_join eff' eff_e *)
  - apply (performs_within_mono e eff_e).
    + apply effect_join_ub_r.
    + exact IHHty.

  (* T_Grant *)
  - exact IHHty.

  (* T_Classify *)
  - exact IHHty.

  (* T_Declassify: e = EDeclassify e1 e2, eff = effect_join eff1 eff2 *)
  - split.
    + apply (performs_within_mono e1 eff1).
      * apply effect_join_ub_l.
      * exact IHHty1.
    + apply (performs_within_mono e2 eff2).
      * apply effect_join_ub_r.
      * exact IHHty2.

  (* T_Prove *)
  - exact IHHty.
Qed.

(** End of EffectSystem.v *)
