(** * Security Properties for TERAS-LANG
    
    Collection of security properties.
    
    TODO: Define and prove security properties.
*)

Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Typing.
Require Import TERAS.properties.NonInterference.

(** ** Non-Interference (re-export)

    Well-typed, effect-pure programs do not leak secrets across related inputs.
*)

Theorem security_non_interference : forall x T_in T_out v1 v2 e,
  val_rel T_in v1 v2 ->
  has_type ((x, T_in) :: nil) nil Public e T_out EffectPure ->
  exp_rel T_out ([x := v1] e) ([x := v2] e).
Proof.
  apply non_interference_stmt.
Qed.

(** End of SecurityProperties.v *)
