(** ============================================================================
    RIINA Non-Interference: Complete Analysis of Remaining 13 Admits
    
    STRUCTURAL ISSUE IDENTIFIED:
    val_rel_at_type for TFn quantifies over stores satisfying store_rel_pred
    but does NOT include store_wf as a precondition. This makes preservation
    properties unprovable without refactoring.
    
    ============================================================================ *)

(** ============================================================================
    SECTION 1: THE CORE STRUCTURAL PROBLEM
    ============================================================================ *)

(*
   Current TFn case in val_rel_at_type (simplified):
   
   | TFn T1 T2 eff =>
       forall Σ', store_ty_extends Σ Σ' ->
         forall x y, value x -> value y -> ... -> val_rel_lower Σ' T1 x y ->
         forall st1 st2 ctx,
           store_rel_pred Σ' st1 st2 ->    (* <-- ONLY store_rel, NOT store_wf! *)
           exists v1' v2' st1' st2' ctx' Σ'',
             ... /\ store_rel_lower Σ'' st1' st2' /\ val_rel_lower Σ'' T2 v1' v2'
   
   The problem:
   - We need store_wf to prove preservation properties for st1', st2'
   - But store_wf is NOT a precondition of val_rel_at_type
   - So inside the TFn case, we don't have store_wf Σ' st1 or store_wf Σ' st2
   
   This affects ALL 10 preservation-related admits (lines 1334, 1593-1601, 1662, 1733, 1808, 1880)
*)

(** ============================================================================
    SECTION 2: SOLUTION OPTIONS
    ============================================================================ *)

(*
   OPTION A: Refactor val_rel_at_type (RECOMMENDED - Clean but invasive)
   -----------------------------------------------------------------------
   Change the TFn case to include store_wf as preconditions:
   
   | TFn T1 T2 eff =>
       forall Σ', store_ty_extends Σ Σ' ->
         forall x y, ... val_rel_lower Σ' T1 x y ->
         forall st1 st2 ctx,
           store_rel_pred Σ' st1 st2 ->
           store_wf Σ' st1 ->              (* ADD *)
           store_wf Σ' st2 ->              (* ADD *)
           stores_agree_low_fo Σ' st1 st2 -> (* ADD *)
           exists v1' v2' st1' st2' ctx' Σ'',
             ... 
   
   Pros: Structurally correct, all preservation admits become provable
   Cons: Requires updating all uses of val_rel_at_type
   
   
   OPTION B: Prove store_rel_n implies partial store_wf (PARTIAL)
   ---------------------------------------------------------------
   Lemma store_rel_implies_store_wf_partial : forall n Σ st1 st2,
     store_rel_n (S n) Σ st1 st2 ->
     (* First direction of store_wf: typed locations have values *)
     (forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
        exists v, store_lookup l st1 = Some v /\ value v /\ 
                  has_type nil Σ Public v T EffectPure).
   
   This IS provable from store_rel_n definition! But the second direction
   (all store entries are typed) requires external knowledge.
   
   
   OPTION C: Axiomatize preservation (PRAGMATIC)
   ---------------------------------------------
   Add well-justified axioms for the unprovable properties:
   
   Axiom store_wf_preserved_by_typed_evaluation : forall Σ e v st st' ctx ctx' T ε,
     has_type nil Σ Public e T ε ->
     store_wf Σ st ->
     (e, st, ctx) -->* (v, st', ctx') ->
     value v ->
     exists Σ', store_ty_extends Σ Σ' /\ store_wf Σ' st'.
   
   Pros: Unblocks proof completion
   Cons: Introduces axiom
   
   
   OPTION D: Strengthen combined_step_up_all preconditions (CLEAN)
   ----------------------------------------------------------------
   Add store_wf to val_rel_at_type_step_up_with_IH as explicit parameters:
   
   The IH for store_rel is:
     forall Σ st1 st2,
       store_rel_n n Σ st1 st2 ->
       store_wf Σ st1 -> store_wf Σ st2 -> ... ->
       store_rel_n (S n) Σ st1 st2
   
   Thread these through the lemma structure.
*)


(** ============================================================================
    SECTION 3: RECOMMENDED APPROACH - OPTION D WITH HELPER LEMMA
    ============================================================================ *)

(*
   The key insight: We CAN derive store_wf from the OUTER combined_step_up 
   hypotheses IF we thread them through properly.
   
   In combined_step_up_all, Part 2 (store_rel step-up) we have:
   - Hwf1 : store_wf Σ st1
   - Hwf2 : store_wf Σ st2
   - Hvals1 : store_has_values st1
   - Hvals2 : store_has_values st2
   - Hagree : stores_agree_low_fo Σ st1 st2
   
   When we're in Part 1 (val_rel step-up) handling TFn, we enter 
   val_rel_at_type which quantifies over stores. The stores st1, st2
   that get instantiated should come WITH their store_wf proofs.
   
   SOLUTION: The val_rel_at_type_step_up_with_IH lemma should take
   store_wf as additional parameters for the result stores.
*)

(** Strengthened helper lemma signature *)
Lemma val_rel_at_type_step_up_with_IH_strengthened : forall T n Σ v1 v2,
  val_rel_at_type Σ (store_rel_n n) (val_rel_n n) (store_rel_n n) T v1 v2 ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  (* IH for val_rel - no change *)
  (forall T' Σ' v1' v2',
     val_rel_n n Σ' T' v1' v2' ->
     (first_order_type T' = false -> has_type nil Σ' Public v1' T' EffectPure) ->
     (first_order_type T' = false -> has_type nil Σ' Public v2' T' EffectPure) ->
     val_rel_n (S n) Σ' T' v1' v2') ->
  (* IH for store_rel - REQUIRES store_wf *)
  (forall Σ' st1 st2,
     store_rel_n n Σ' st1 st2 ->
     store_wf Σ' st1 ->        (* THESE are the key *)
     store_wf Σ' st2 ->
     store_has_values st1 ->
     store_has_values st2 ->
     stores_agree_low_fo Σ' st1 st2 ->
     store_rel_n (S n) Σ' st1 st2) ->
  (* NEW: For TFn case, we need store_wf derivable from context *)
  (forall Σ' st1 st2,
     store_rel_n n Σ' st1 st2 ->
     (* Some way to get store_wf... *)
     True) ->
  val_rel_at_type Σ (store_rel_n (S n)) (val_rel_n (S n)) (store_rel_n (S n)) T v1 v2.
Proof.
  (* The issue: inside TFn case, we have store_rel_n n' Σ' st1 st2
     but need store_wf Σ' st1 to call IHstore *)
Abort.

(** ============================================================================
    SECTION 4: THE ACTUAL FIX - MODIFY val_rel_at_type DEFINITION
    ============================================================================ *)

(*
   RECOMMENDED: Modify val_rel_at_type TFn case to include store_wf
   
   In NonInterference_v2.v, find the val_rel_at_type definition and change
   the TFn case from:
   
   | TFn T1 T2 eff =>
       forall Σ' (Hext : store_ty_extends Σ Σ')
              arg1 arg2 ... (Hargrel : val_rel_n' n Σ' T1 arg1 arg2)
              st1 st2 ctx (Hstrel : store_rel_n' n Σ' st1 st2),
       exists r1 r2 st1' st2' ctx' Σ'', ...
   
   TO:
   
   | TFn T1 T2 eff =>
       forall Σ' (Hext : store_ty_extends Σ Σ')
              arg1 arg2 ... (Hargrel : val_rel_n' n Σ' T1 arg1 arg2)
              st1 st2 ctx 
              (Hstrel : store_rel_n' n Σ' st1 st2)
              (Hwf1 : store_wf Σ' st1)           (* ADD *)
              (Hwf2 : store_wf Σ' st2)           (* ADD *)
              (Hvals1 : store_has_values st1)   (* ADD *)
              (Hvals2 : store_has_values st2)   (* ADD *)
              (Hagree : stores_agree_low_fo Σ' st1 st2),  (* ADD *)
       exists r1 r2 st1' st2' ctx' Σ'',
         ... /\
         store_wf Σ'' st1' /\     (* ADD to postcondition *)
         store_wf Σ'' st2' /\     (* ADD to postcondition *)
         ...
   
   This is the STRUCTURALLY CORRECT solution.
*)


(** ============================================================================
    SECTION 5: ADMITS 284, 286 - MIXED CONSTRUCTOR CASES
    ============================================================================ *)

(*
   Context: In val_rel_at_type_fo or similar, TSum case
   
   We have:
   - v1 = EInl x1 T2  (or EInr)
   - v2 = EInr y2 T1  (opposite constructor)
   - Both are well-typed at TSum T1 T2 with PUBLIC typing
   
   The claim is this case is "impossible" - related PUBLIC values of sum type
   must have the same constructor.
   
   WHY IS THIS TRUE?
   - For val_rel at level n, if both values have PUBLIC typing for TSum T1 T2
   - And they are "related" in the logical relation sense
   - Then they must have identical structure (for FO types)
   
   PROOF APPROACH:
   - This should be provable by induction on the typing derivation
   - Or by showing val_rel_at_type_fo for TSum requires same constructor
   
   Let's check val_rel_at_type_fo for TSum:
*)

(*
   val_rel_at_type_fo T v1 v2 for TSum should be:
   
   | TSum T1 T2 =>
       (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ 
                      val_rel_at_type_fo T1 x1 x2) \/
       (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ 
                      val_rel_at_type_fo T2 y1 y2)
   
   So by DEFINITION, val_rel_at_type_fo for TSum requires SAME constructor!
   The mixed cases (EInl vs EInr) are simply NOT in the definition.
   
   Therefore, these admits should be replaced with:
*)

(* 
   REPLACEMENT FOR LINES 284, 286:
   
   (* This case is impossible by definition of val_rel_at_type_fo for TSum *)
   (* val_rel_at_type_fo (TSum T1 T2) requires both values have same constructor *)
   destruct Hrel as [[x1 [x2 [Heq1 [Heq2 _]]]] | [y1 [y2 [Heq1 [Heq2 _]]]]].
   - (* Both Inl *) subst. discriminate. (* or handle normally *)
   - (* Both Inr *) subst. discriminate. (* or handle normally *)
   
   OR if the issue is in a different context:
   
   (* The hypothesis Hrel : val_rel_... gives us same-constructor *)
   (* So the mixed case contradicts Hrel *)
   exfalso.
   destruct Hrel as [[x1 [x2 [Heq1 [Heq2 _]]]] | [y1 [y2 [Heq1 [Heq2 _]]]]].
   - subst. discriminate Heq_v2.  (* v2 = EInl but we assumed v2 = EInr *)
   - subst. discriminate Heq_v1.  (* v1 = EInr but we assumed v1 = EInl *)
*)


(** ============================================================================
    SECTION 6: ADMIT 1532 - FUNDAMENTAL THEOREM n=0
    ============================================================================ *)

(*
   Context: Proving val_rel_at_type holds from TYPING ALONE when n=0
   
   At step index 0:
   - val_rel_n 0 Σ T v1 v2 for HO types just requires:
     * value v1, value v2
     * closed_expr v1, closed_expr v2  
     * has_type nil Σ Public v1 T EffectPure
     * has_type nil Σ Public v2 T EffectPure
   
   - val_rel_at_type at level 0 uses val_rel_n 0 and store_rel_n 0
   
   For TFn T1 T2 eff:
   - Given typed lambdas v1, v2 and typed arguments arg1, arg2
   - And stores satisfying store_rel_n 0 (just store_max equality)
   - Need to show: application terminates with related results
   
   PROOF APPROACH for TFn at n=0:
   1. Use canonical_forms_fn: v1 = ELam x1 T1 body1, v2 = ELam x2 T1 body2
   2. Beta reduction: (EApp (ELam x T body) arg) --> [x := arg] body
   3. Substitution preserves typing
   4. For n=0, result only needs to be well-typed (not deeply related)
   
   KEY INSIGHT for n=0:
   - val_rel_n 0 for HO types only requires TYPING, not structural equality
   - So we just need to show the substituted bodies are well-typed
   - This IS provable from the typing hypotheses!
*)

Lemma fundamental_theorem_n0_TFn : forall Σ v1 v2 T1 T2 eff,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  has_type nil Σ Public v1 (TFn T1 T2 eff) EffectPure ->
  has_type nil Σ Public v2 (TFn T1 T2 eff) EffectPure ->
  val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) 
                  (TFn T1 T2 eff) v1 v2.
Proof.
  intros Σ v1 v2 T1 T2 eff Hv1 Hv2 Hc1 Hc2 Hty1 Hty2.
  simpl. (* Unfold val_rel_at_type for TFn *)
  
  intros Σ' Hext arg1 arg2 Hvarg1 Hvarg2 Hcarg1 Hcarg2 Hargrel st1 st2 ctx Hstrel.
  
  (* Extract lambda structure *)
  destruct (canonical_forms_fn nil Σ Public v1 T1 T2 eff EffectPure Hv1 Hty1)
    as [x1 [body1 Heq1]].
  destruct (canonical_forms_fn nil Σ Public v2 T1 T2 eff EffectPure Hv2 Hty2)
    as [x2 [body2 Heq2]].
  subst v1 v2.
  
  (* Get body typings from lambda typing inversion *)
  assert (Hbody1 : has_type ((x1, T1) :: nil) Σ Public body1 T2 eff).
  { (* Inversion on Hty1 *) admit. }
  
  assert (Hbody2 : has_type ((x2, T1) :: nil) Σ Public body2 T2 eff).
  { admit. }
  
  (* Get argument typing from val_rel_n 0 *)
  (* For HO T1: val_rel_n 0 gives has_type *)
  (* For FO T1: we need typing from context or assume it *)
  assert (Htyarg1 : has_type nil Σ' Public arg1 T1 EffectPure).
  { (* From val_rel_n 0 or assumed *) admit. }
  
  assert (Htyarg2 : has_type nil Σ' Public arg2 T1 EffectPure).
  { admit. }
  
  (* Substitution gives typed results *)
  assert (Htyresult1 : has_type nil Σ' Public ([x1 := arg1] body1) T2 eff).
  { apply substitution_preserves_typing with T1.
    - exact Hvarg1.
    - apply typing_weakening_store with Σ; [exact Htyarg1 | exact Hext].
    - apply typing_weakening_store with Σ; [exact Hbody1 | exact Hext]. }
  
  assert (Htyresult2 : has_type nil Σ' Public ([x2 := arg2] body2) T2 eff).
  { apply substitution_preserves_typing with T1.
    - exact Hvarg2.
    - apply typing_weakening_store with Σ; [exact Htyarg2 | exact Hext].
    - apply typing_weakening_store with Σ; [exact Hbody2 | exact Hext]. }
  
  (* Witnesses: substituted bodies with single beta step *)
  exists ([x1 := arg1] body1), ([x2 := arg2] body2), st1, st2, ctx, Σ'.
  
  repeat split.
  - (* store_ty_extends Σ' Σ' *) apply store_ty_extends_refl.
  - (* Multi-step for EApp *)
    apply MS_Step with ([x1 := arg1] body1, st1, ctx).
    + apply ST_AppAbs. exact Hvarg1.
    + apply MS_Refl.
  - (* Multi-step for EApp *)
    apply MS_Step with ([x2 := arg2] body2, st2, ctx).
    + apply ST_AppAbs. exact Hvarg2.
    + apply MS_Refl.
  - (* val_rel_n 0 Σ' T2 result1 result2 *)
    (* For n=0, HO types just need typing *)
    simpl. repeat split.
    + (* value *) admit. (* Depends on whether substitution produces value *)
    + admit.
    + apply typing_nil_implies_closed with Σ' Public T2 eff. exact Htyresult1.
    + apply typing_nil_implies_closed with Σ' Public T2 eff. exact Htyresult2.
    + destruct (first_order_type T2) eqn:Hfo2.
      * (* FO result - need syntactic relation *)
        (* This requires more: either determinism or further evaluation *)
        admit.
      * (* HO result - typing suffices *)
        split.
        -- apply value_has_pure_effect. admit. exact Htyresult1.
        -- apply value_has_pure_effect. admit. exact Htyresult2.
  - (* store_rel_n 0 unchanged - beta doesn't modify store *)
    exact Hstrel.
Admitted.

(** ============================================================================
    SECTION 7: COMPLETE SOLUTION SUMMARY
    ============================================================================ *)

(*
   REQUIRED CHANGES TO ELIMINATE ALL 13 ADMITS:
   
   === STRUCTURAL FIX (10 preservation admits) ===
   
   Modify val_rel_at_type TFn case to include store_wf in preconditions:
   
   Find in NonInterference_v2.v:
   | TFn T1 T2 eff =>
       forall Σ' (Hext : store_ty_extends Σ Σ') ...
              st1 st2 ctx (Hstrel : store_rel_n' n Σ' st1 st2),
       exists r1 r2 st1' st2' ctx' Σ'', ...
   
   Change to:
   | TFn T1 T2 eff =>
       forall Σ' (Hext : store_ty_extends Σ Σ') ...
              st1 st2 ctx (Hstrel : store_rel_n' n Σ' st1 st2)
              (Hwf1 : store_wf Σ' st1) (Hwf2 : store_wf Σ' st2)
              (Hvals1 : store_has_values st1) (Hvals2 : store_has_values st2)
              (Hagree : stores_agree_low_fo Σ' st1 st2),
       exists r1 r2 st1' st2' ctx' Σ'',
         store_ty_extends Σ' Σ'' /\
         ... /\
         store_wf Σ'' st1' /\ store_wf Σ'' st2' /\
         stores_agree_low_fo Σ'' st1' st2' /\
         val_rel_n' n Σ'' T2 r1 r2 /\ store_rel_n' n Σ'' st1' st2'
   
   Then update all proofs using val_rel_at_type.
   
   
   === ADMITS 284, 286 (mixed constructors) ===
   
   Replace with proof by contradiction:
   - val_rel_at_type_fo for TSum requires same constructor
   - Mixed case contradicts this
   
   
   === ADMIT 1532 (Fundamental Theorem n=0) ===
   
   Use canonical_forms + substitution_preserves_typing.
   Remaining sub-admits for "value of substitution" need separate lemma
   or evaluation completion argument.
*)

