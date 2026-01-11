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
  match e1, e2 with
  | EffectPure, _ => e2
  | _, EffectPure => e1
  | _, _ => e1 (* TODO: proper join for non-pure effects *)
  end.

(** End of EffectAlgebra.v *)
