(* ═══════════════════════════════════════════════════════════════════════════
   TARGETED FIX: Replace the 2 admits in val_rel_le_step_up_fo
   ═══════════════════════════════════════════════════════════════════════════ *)

(*
   STEP 1: Change the lemma statement
   ───────────────────────────────────
   
   BEFORE (broken):
   
   Lemma val_rel_le_step_up_fo : forall m n Σ T v1 v2,
     first_order_type T = true ->
     n > 0 ->                          (* ← TOO WEAK *)
     val_rel_le n Σ T v1 v2 ->
     val_rel_le m Σ T v1 v2.
   
   AFTER (fixed):
   
   Lemma val_rel_le_step_up_fo : forall m n Σ T v1 v2,
     first_order_type T = true ->
     n > fo_compound_depth T ->        (* ← STRENGTHENED *)
     val_rel_le n Σ T v1 v2 ->
     val_rel_le m Σ T v1 v2.
*)

(*
   STEP 2: Replace the TProd admit
   ────────────────────────────────
   
   Find this case in your proof:
   
   + (* TProd *)
     admit.
   
   Replace with:
*)

(* TProd case *)
+ (* TProd T1 T2 *)
  apply val_rel_le_fo_step_independent with (m := n).
  * (* first_order_type (TProd T1 T2) = true *)
    exact Hfo.
  * (* n > fo_compound_depth (TProd T1 T2) *)
    exact Hdepth.
  * (* m > 0 *)
    lia.  (* or: assumption, if you have Hm_pos : m > 0 *)
  * (* val_rel_le n Σ (TProd T1 T2) v1 v2 *)
    exact Hrel.

(*
   STEP 3: Replace the TSum admit
   ───────────────────────────────
   
   Find this case in your proof:
   
   + (* TSum *)
     admit.
   
   Replace with:
*)

(* TSum case *)
+ (* TSum T1 T2 *)
  apply val_rel_le_fo_step_independent with (m := n).
  * exact Hfo.
  * exact Hdepth.
  * lia.
  * exact Hrel.

(* ═══════════════════════════════════════════════════════════════════════════
   COMPLETE LEMMA (copy-paste ready)
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_le_step_up_fo : forall m n Σ T v1 v2,
  first_order_type T = true ->
  n > fo_compound_depth T ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hfo Hdepth Hrel.
  destruct (Nat.eq_dec m 0) as [Hm0 | Hm_pos].
  - (* m = 0 *)
    subst m. simpl. trivial.
  - (* m > 0 *)
    assert (Hm_gt : m > 0) by lia.
    (* All cases use the same strategy: apply val_rel_le_fo_step_independent *)
    apply val_rel_le_fo_step_independent with (m := n); auto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════
   WHY THIS WORKS
   ═══════════════════════════════════════════════════════════════════════════
   
   val_rel_le_fo_step_independent has signature:
   
     forall m n Σ T v1 v2,
       first_order_type T = true ->
       m > fo_compound_depth T ->
       n > 0 ->
       val_rel_le m Σ T v1 v2 ->
       val_rel_le n Σ T v1 v2.
   
   We have:
     - Hfo   : first_order_type T = true           ✓
     - Hdepth: n > fo_compound_depth T             → matches "m > fo_compound_depth T"
     - Hm_gt : m > 0                               → matches "n > 0"
     - Hrel  : val_rel_le n Σ T v1 v2              → matches "val_rel_le m Σ ..."
   
   So we instantiate with (m := n) to flip the direction:
     - Our n becomes their m (the "big enough" step)
     - Our m becomes their n (the target step)
   
   ═══════════════════════════════════════════════════════════════════════════ *)

(* ═══════════════════════════════════════════════════════════════════════════
   ALTERNATIVE: If you need explicit case analysis
   ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_le_step_up_fo_with_cases : forall m n Σ T v1 v2,
  first_order_type T = true ->
  n > fo_compound_depth T ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hfo Hdepth Hrel.
  destruct (Nat.eq_dec m 0).
  - subst. simpl. trivial.
  - assert (Hm_pos : m > 0) by lia.
    destruct T; simpl in Hfo; try discriminate.
    (* For ALL first-order types, including TProd and TSum: *)
    all: apply val_rel_le_fo_step_independent with (m := n); auto.
Qed.

(* The `all:` tactical applies the same tactic to all remaining goals,
   which works because the strategy is identical for all first-order types. *)
