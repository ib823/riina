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
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(** ** Effect Typing Rules *)

Inductive has_type_full : type_env -> store_ty -> security_level ->
                          expr -> ty -> effect -> Prop :=
  (* Include all core rules *)
  | T_Core : forall G S D e T eff,
      has_type G S D e T eff ->
      has_type_full G S D e T eff

  (* Effect Operations *)
  | T_Perform : forall G S D eff e T,
      has_type_full G S D e T EffectPure -> (* Payload is pure *)
      (* Performing an effect 'eff' requires 'eff' in the effect budget *)
      has_type_full G S D (EPerform eff e) TUnit eff

  | T_Handle : forall G S D e y h T eff_e eff_h,
      (* Expression e has some effect eff_e *)
      has_type_full G S D e T eff_e ->
      (* Handler h handles it. h gets the resumption or payload.
         Simplified: y binds the effect payload. *)
      (* For a full algebraic effect system, we need a refined handler typing.
         Here we assume a simple exception-like or one-shot handler for now. *)
      has_type_full ((y, TUnit) :: G) S D h T eff_h ->
      (* The handle expression eliminates eff_e if h handles it? 
         Or just wraps it?
         Let's assume it handles 'eff_e' and returns 'T'. *)
      has_type_full G S D (EHandle e y h) T eff_h

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
      has_type_full G S D e2 (TProof T) eff2 -> (* Proof of safety *)
      has_type_full G S D (EDeclassify e1 e2) T (effect_join eff1 eff2)

  | T_Prove : forall G S D e T eff,
      has_type_full G S D e T eff ->
      has_type_full G S D (EProve e) (TProof T) eff.

(** ** Effect Safety (Stub)
    
    Theorem: If has_type_full G S D e T eff, then executing e
    only produces effects in eff.
*)
Theorem effect_safety : forall e T eff,
  has_type_full nil nil Public e T eff ->
  (* Operational semantics for traces needed here *)
  True.
Proof.
  intros. exact I.
Qed.

(** End of EffectSystem.v *)