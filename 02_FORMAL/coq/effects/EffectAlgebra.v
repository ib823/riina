(** * Effect Algebra for TERAS-LANG
    
    Algebraic structure of effects.
    
    TODO: Define effect lattice and operations.
*)

Require Import TERAS.foundations.Syntax.

(** Effect ordering *)
Definition effect_leq (e1 e2 : effect) : Prop :=
  e1 = EffectPure \/ e1 = e2.

(** Effect join (least upper bound) *)
Definition effect_join (e1 e2 : effect) : effect :=
  if decide (e1 = EffectPure) then e2
  else if decide (e2 = EffectPure) then e1
  else e1. (* TODO: proper join *)

(** End of EffectAlgebra.v *)
