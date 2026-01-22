(** * Prelude: Common Definitions for TERAS-LANG Formalization *)

(** This module provides common imports and basic definitions used throughout
    the TERAS-LANG formalization. *)

Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Logic.Decidable.
Require Export Coq.Program.Equality.

Export ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ** Basic Type Definitions *)

Definition var := string.
Definition loc := nat.

(** ** Helper Tactics *)

Ltac inv H := inversion H; subst; clear H.
Ltac destr H := destruct H.
Ltac ind H := induction H.

(** ** Decidability Helpers *)

Definition eq_var_dec : forall (x y : var), {x = y} + {x <> y} := string_dec.
Definition eq_loc_dec : forall (l1 l2 : loc), {l1 = l2} + {l1 <> l2} := Nat.eq_dec.
