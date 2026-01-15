(** * Effect Gate Proofs for RIINA

    Formal verification of the Effect Gate mechanism.

    The Effect Gate ensures that high-privilege effects cannot leak
    into low-privilege contexts without explicit handling/granting.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.effects.EffectAlgebra.
Require Import RIINA.effects.EffectSystem.

(** ** Gate Definition

    A context C is an Effect Gate for effect 'eff' if
    execution of C[e] blocks 'eff' from e unless granted.
*)

Definition is_gate (eff : effect) (e_gate : expr) : Prop :=
  (* Conceptual definition:
     For any expression e that performs 'eff',
     embedding it in e_gate traps or handles the effect. *)
  forall e T eff_used,
    has_type_full nil nil Public e T eff_used ->
    effect_leq eff_used eff ->
    performs_within (EApp e_gate e) eff.

(** ** Non-Leakage Property

    If a term is typed with effect 'eff', and 'eff' is restricted,
    it cannot reduce to an 'EPerform eff' step at the top level.
*)

(* TODO: Fix after effect_safety is proven *)
Theorem gate_enforcement : forall G S D e T eff_allowed eff_used,
  has_type_full G S D e T eff_used ->
  effect_level eff_used <= effect_level eff_allowed ->
  performs_within e eff_allowed.
Proof.
  (* Depends on effect_safety which is temporarily admitted *)
Admitted.

(** End of EffectGate.v *)
