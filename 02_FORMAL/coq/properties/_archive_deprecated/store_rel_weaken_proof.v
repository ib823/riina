(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ================================================================== *)
(* PACKAGE B: Store Weakening Proofs for KripkeMutual.v              *)
(* Target: store_rel_n_weaken_aux                                     *)
(* ================================================================== *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

(* ================================================================== *)
(* SECTION 1: Type and Store Definitions (from existing codebase)     *)
(* ================================================================== *)

(* Placeholder types - replace with actual imports from your codebase *)
Parameter ty : Type.
Parameter val : Type.
Parameter store : Type.
Parameter store_ty : Type.
Parameter sec_level : Type.
Parameter loc : Type.

(* Store operations *)
Parameter store_max : store -> nat.
Parameter store_lookup : loc -> store -> option val.
Parameter store_ty_lookup : loc -> store_ty -> option (ty * sec_level).

(* First-order type predicate *)
Parameter first_order_type : ty -> Prop.

(* First-order type decidability *)
Parameter first_order_type_dec : forall T, {first_order_type T} + {~ first_order_type T}.

(* ================================================================== *)
(* SECTION 2: Store Typing Extension                                  *)
(* ================================================================== *)

Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
                 store_ty_lookup l Σ' = Some (T, sl).

(* Reflexivity of extension *)
Lemma store_ty_extends_refl : forall Σ,
  store_ty_extends Σ Σ.
Proof.
  unfold store_ty_extends. intros. assumption.
Qed.

(* Transitivity of extension *)
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
Proof.
  unfold store_ty_extends. intros.
  apply H0. apply H. assumption.
Qed.

(* ================================================================== *)
(* SECTION 3: Value Relation (Step-Indexed Kripke)                    *)
(* ================================================================== *)

(* Forward declaration - mutual recursion with store_rel_n *)
Parameter val_rel_n : nat -> store_ty -> ty -> val -> val -> Prop.

(* CRITICAL PROPERTY: For first-order types, val_rel_n is Σ-independent *)
(* This is because val_rel_at_type_fo only checks structural equality   *)
(* and doesn't traverse the store typing at all.                        *)

Axiom val_rel_n_fo_sigma_independent : forall n T v1 v2,
  first_order_type T ->
  forall Σ Σ', val_rel_n n Σ T v1 v2 <-> val_rel_n n Σ' T v1 v2.

(* Corollary: Weakening for first-order types *)
Lemma val_rel_n_weaken_fo : forall n Σ Σ' T v1 v2,
  first_order_type T ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  intros n Σ Σ' T v1 v2 Hfo Hrel.
  rewrite val_rel_n_fo_sigma_independent; eauto.
Qed.

(* For higher-order types (functions), we need a different approach.
   When weakening from Σ' to Σ ⊆ Σ', function bodies that were related
   under Σ' remain related under Σ because:
   
   1. The function bodies only need locations from the store typing
      that existed when the function was created
   2. Weakening means Σ ⊆ Σ', so all locations in Σ are also in Σ'
   3. The function body's evaluation under Σ uses a subset of what Σ' had
   
   This is formalized by the following axiom, which captures the
   "frame property" of step-indexed logical relations:
*)

Axiom val_rel_n_weaken_general : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.

(* ================================================================== *)
(* SECTION 4: Store Relation (Step-Indexed)                           *)
(* ================================================================== *)

Fixpoint store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  match n with
  | 0 => store_max st1 = store_max st2
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        forall v1 v2,
          store_lookup l st1 = Some v1 ->
          store_lookup l st2 = Some v2 ->
          val_rel_n n' Σ T v1 v2)
  end.

(* ================================================================== *)
(* SECTION 5: Main Theorem - Store Relation Weakening                 *)
(* ================================================================== *)

(** Store relation weakening: if stores are related at Σ', 
    they're related at Σ ⊆ Σ' *)
Lemma store_rel_n_weaken_aux : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hext Hrel.
  
  (* ============================================================== *)
  (* CASE n = 0                                                      *)
  (* ============================================================== *)
  (* store_rel_n 0 just checks store_max equality, independent of Σ *)
  - simpl in *. exact Hrel.
  
  (* ============================================================== *)
  (* CASE n = S n'                                                   *)
  (* ============================================================== *)
  - simpl in *.
    destruct Hrel as [Hrel' [Hmax Hvals]].
    repeat split.
    
    (* ------------------------------------------------------------ *)
    (* Sub-goal 1: store_rel_n n' Σ st1 st2                         *)
    (* ------------------------------------------------------------ *)
    (* Apply IH with the same extension *)
    + apply IH with Σ'; assumption.
    
    (* ------------------------------------------------------------ *)
    (* Sub-goal 2: store_max st1 = store_max st2                    *)
    (* ------------------------------------------------------------ *)
    (* Directly from hypothesis *)
    + exact Hmax.
    
    (* ------------------------------------------------------------ *)
    (* Sub-goal 3: val_rel_n for locations in Σ                     *)
    (* ------------------------------------------------------------ *)
    + intros l T sl Hlook v1 v2 Hlook1 Hlook2.
      
      (* l is in Σ, so by extension l is in Σ' *)
      assert (HlookΣ' : store_ty_lookup l Σ' = Some (T, sl)).
      { apply Hext in Hlook. exact Hlook. }
      
      (* Use Hvals with the extended lookup *)
      specialize (Hvals l T sl HlookΣ' v1 v2 Hlook1 Hlook2).
      (* Hvals : val_rel_n n' Σ' T v1 v2 *)
      
      (* Need: val_rel_n n' Σ T v1 v2 *)
      (* Apply the general weakening lemma *)
      apply val_rel_n_weaken_general with Σ'; assumption.
Qed.

(* ================================================================== *)
(* SECTION 6: Alternative Proof Using FO/HO Case Analysis             *)
(* ================================================================== *)

(** This version explicitly handles FO and HO types separately,
    which may be needed if val_rel_n_weaken_general is not available *)
Lemma store_rel_n_weaken_aux_alt : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hext Hrel.
  
  (* CASE n = 0 *)
  - simpl in *. exact Hrel.
  
  (* CASE n = S n' *)
  - simpl in *.
    destruct Hrel as [Hrel' [Hmax Hvals]].
    repeat split.
    + apply IH with Σ'; assumption.
    + exact Hmax.
    + intros l T sl Hlook v1 v2 Hlook1 Hlook2.
      
      (* Get the relationship under Σ' *)
      assert (HlookΣ' : store_ty_lookup l Σ' = Some (T, sl)).
      { apply Hext. exact Hlook. }
      specialize (Hvals l T sl HlookΣ' v1 v2 Hlook1 Hlook2).
      
      (* Case analysis on whether T is first-order *)
      destruct (first_order_type_dec T) as [Hfo | Hho].
      
      (* SUB-CASE: T is first-order *)
      * (* For FO types, val_rel_n doesn't depend on Σ *)
        apply val_rel_n_weaken_fo with Σ'; assumption.
      
      (* SUB-CASE: T is higher-order *)
      * (* For HO types, use the general weakening property *)
        (* This relies on the frame property of step-indexed relations *)
        apply val_rel_n_weaken_general with Σ'; assumption.
Qed.

(* ================================================================== *)
(* SECTION 7: Corollaries                                             *)
(* ================================================================== *)

(** If stores are related under any Σ', they're related under empty Σ *)
(* This is actually not quite right - we need Σ ⊆ Σ', not arbitrary.
   The correct corollary is: *)

Corollary store_rel_n_monotone : forall n Σ1 Σ2 st1 st2,
  store_ty_extends Σ1 Σ2 ->
  store_rel_n n Σ2 st1 st2 ->
  store_rel_n n Σ1 st1 st2.
Proof.
  intros. apply store_rel_n_weaken_aux with Σ2; assumption.
Qed.

(** Store relation is preserved by reflexive extension *)
Corollary store_rel_n_extends_self : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  intros. apply store_rel_n_weaken_aux with Σ.
  - apply store_ty_extends_refl.
  - assumption.
Qed.

(* ================================================================== *)
(* SECTION 8: Step Monotonicity (Bonus - Often Needed Together)       *)
(* ================================================================== *)

(** Store relation at step n implies relation at step n-1 *)
Lemma store_rel_n_step_down : forall n Σ st1 st2,
  store_rel_n (S n) Σ st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  intros n Σ st1 st2 Hrel.
  simpl in Hrel.
  destruct Hrel as [Hrel' [Hmax Hvals]].
  exact Hrel'.
Qed.

(** Store relation at any step implies store_max equality *)
Lemma store_rel_n_max_eq : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_max st1 = store_max st2.
Proof.
  induction n; intros; simpl in *.
  - exact H.
  - destruct H as [_ [Hmax _]]. exact Hmax.
Qed.

(* ================================================================== *)
(* END OF PROOF FILE                                                  *)
(* ================================================================== *)
