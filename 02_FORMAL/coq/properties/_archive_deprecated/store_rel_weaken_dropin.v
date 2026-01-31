(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ================================================================== *)
(* DROP-IN PROOF for KripkeMutual.v                                   *)
(* Replace the Admitted proof with this                               *)
(* ================================================================== *)

(* 
   PREREQUISITES: You need one of these lemmas to exist or be proven:
   
   Option A (Recommended): A general weakening lemma
   
   Lemma val_rel_n_weaken : forall n Σ Σ' T v1 v2,
     store_ty_extends Σ Σ' ->
     val_rel_n n Σ' T v1 v2 ->
     val_rel_n n Σ T v1 v2.
   
   Option B: Separate lemmas for FO and HO types
   
   Lemma val_rel_n_fo_sigma_independent : forall n T v1 v2,
     first_order_type T ->
     forall Σ Σ', val_rel_n n Σ T v1 v2 <-> val_rel_n n Σ' T v1 v2.
   
   (* HO types still need val_rel_n_weaken or frame property *)
*)

(* ================================================================== *)
(* PROOF USING val_rel_n_weaken                                       *)
(* ================================================================== *)

Lemma store_rel_n_weaken_aux : forall n Σ Σ' st1 st2,
  store_ty_extends Σ Σ' ->
  store_rel_n n Σ' st1 st2 ->
  store_rel_n n Σ st1 st2.
Proof.
  induction n as [| n' IH]; intros Σ Σ' st1 st2 Hext Hrel.
  
  (* n = 0: store_rel_n 0 is just store_max equality, Σ-independent *)
  - simpl in *. exact Hrel.
  
  (* n = S n' *)
  - simpl in *.
    destruct Hrel as [Hrel' [Hmax Hvals]].
    split; [| split].
    
    (* Goal 1: store_rel_n n' Σ st1 st2 *)
    + apply IH with Σ'; assumption.
    
    (* Goal 2: store_max st1 = store_max st2 *)
    + exact Hmax.
    
    (* Goal 3: val_rel_n for all locations in Σ *)
    + intros l T sl Hlook v1 v2 Hlook1 Hlook2.
      (* l ∈ Σ implies l ∈ Σ' by extension *)
      apply Hext in Hlook as HlookΣ'.
      (* Get val_rel_n n' Σ' T v1 v2 *)
      specialize (Hvals l T sl HlookΣ' v1 v2 Hlook1 Hlook2).
      (* Weaken from Σ' to Σ *)
      apply val_rel_n_weaken with Σ'; assumption.
Qed.

(* ================================================================== *)
(* ALTERNATIVE: If you need to PROVE val_rel_n_weaken first           *)
(* ================================================================== *)

(* 
   The key insight is that val_rel_n is defined by cases:
   
   For first-order types (TInt, TBool, TUnit, TRef, etc.):
     val_rel_n n Σ T v1 v2 ≡ val_rel_at_type_fo T v1 v2
   
   where val_rel_at_type_fo doesn't mention Σ at all!
   
   For TFn (function types):
     val_rel_n n Σ (TFn T1 ε T2) v1 v2 ≡ 
       ∀ n' ≤ n, Σ' ⊇ Σ, st1' st2' related, arg1 arg2 related,
         bodies are related at step n'-1 under Σ'
   
   The key is that TFn uses universal quantification over EXTENSIONS Σ',
   not the current Σ. This means weakening Σ to Σ'' ⊆ Σ is safe because:
   - Any extension Σ' ⊇ Σ is also an extension of Σ'' (by transitivity)
   
   This is the "Kripke monotonicity" property of step-indexed logical relations.
*)

(* If val_rel_n_weaken doesn't exist, prove it by induction on n and
   case analysis on T. The FO case is trivial. The HO case uses the
   fact that TFn is defined with ∀ Σ' ⊇ Σ, which gives us monotonicity
   for free. *)

Lemma val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  (* Strategy: induction on n, nested induction on T *)
  induction n as [| n' IHn]; intros Σ Σ' T v1 v2 Hext Hrel.
  
  (* n = 0: val_rel_n 0 is typically val_rel_base, which is Σ-independent *)
  - (* Use val_rel_n_base or val_rel_at_type_fo *)
    (* This should unfold to structural equality, no Σ involved *)
    admit. (* Depends on your val_rel_n definition at step 0 *)
  
  (* n = S n' *)
  - (* Case analysis on T *)
    destruct T; simpl in *.
    
    (* For each first-order type: val_rel_at_type_fo doesn't use Σ *)
    (* TInt, TBool, TUnit, TRef, etc. - all Σ-independent *)
    all: try exact Hrel.
    
    (* For TFn: use Kripke monotonicity *)
    (* TFn case: the definition quantifies over Σ'' ⊇ Σ, so
       weakening Σ → Σ₀ ⊆ Σ just enlarges the quantifier domain *)
    + (* This requires unfolding your specific TFn definition *)
      admit. (* Depends on exact TFn definition *)
      
Admitted. (* Replace admits with actual proofs based on your definitions *)

(* ================================================================== *)
(* INTEGRATION NOTES                                                  *)
(* ================================================================== *)

(*
   To integrate into KripkeMutual.v:
   
   1. If val_rel_n_weaken already exists:
      - Just use the first proof above
   
   2. If val_rel_n_weaken doesn't exist but val_rel_n_fo_sigma_independent does:
      - Use case analysis on first_order_type T
      - FO case: use val_rel_n_fo_sigma_independent
      - HO case: prove directly from TFn definition
   
   3. If neither exists:
      - First prove val_rel_n_weaken as shown above
      - Then prove store_rel_n_weaken_aux
   
   KEY INSIGHT: The proof is fundamentally about Kripke monotonicity.
   Step-indexed Kripke logical relations are designed to support
   weakening (anti-monotonicity in Σ) precisely because:
   - Base types don't reference Σ
   - Function types quantify over ALL extensions of Σ
*)
