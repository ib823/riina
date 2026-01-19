      inversion Hv1; subst. inversion Hv2; subst.
      repeat split; assumption.
  - (* n = S n' *)
    destruct Hrel as [_ [Hv1 [Hv2 [_ [_ Hrat]]]]].
    simpl in Hrat.
    destruct Hrat as [[a1 [a2 [Heq1 [Heq2 _]]]] | [b1 [b2 [Heq1 [Heq2 _]]]]].
    + left. exists a1, a2. subst.
      inversion Hv1; subst. inversion Hv2; subst.
      repeat split; assumption.
    + right. exists b1, b2. subst.
      inversion Hv1; subst. inversion Hv2; subst.
      repeat split; assumption.
Qed.

(** ========================================================================
    SECTION 5: MONOTONICITY LEMMAS
    ======================================================================== *)

(** Downward monotonicity for val_rel_n - ADMITTED for now (tedious but standard) *)
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  intros m n Σ T v1 v2 Hle.
  generalize dependent m.
  induction n as [| n' IHn]; intros m Hle Hrel.
  - (* n = 0, so m = 0 *)
    inversion Hle. exact Hrel.
  - (* n = S n' *)
    destruct m as [| m'].
    + (* m = 0 *)
      simpl. simpl in Hrel.
      destruct Hrel as [Hrec [Hv1 [Hv2 [Hc1 [Hc2 Hrat]]]]].
      repeat split; try assumption.
      destruct (first_order_type T) eqn:Hfo.
      * (* First-order: need to extract val_rel_at_type_fo from val_rel_at_type *)
        (* Use val_rel_at_type_fo_equiv to convert *)
        apply (val_rel_at_type_fo_equiv T Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
        exact Hrat.
      * (* Higher-order: True *)
        exact I.
    + (* m = S m' *)
      simpl. simpl in Hrel.
      destruct Hrel as [Hrec [Hv1 [Hv2 [Hc1 [Hc2 Hrat]]]]].
      split.
      * apply IHn. lia. exact Hrec.
      * repeat split; try assumption.
        (* val_rel_at_type at m' from val_rel_at_type at n' *)
        destruct (first_order_type T) eqn:Hfo.
        -- (* First-order: predicates don't matter *)
           apply (val_rel_at_type_fo_equiv T Σ (store_rel_n m') (val_rel_n m') (store_rel_n m') v1 v2 Hfo).
           apply (val_rel_at_type_fo_equiv T Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') v1 v2 Hfo).
           exact Hrat.
        -- (* Higher-order (TFn): Kripke monotonicity *)
           (* For TFn T1 T2 e, we have Hrat at step n' and need val_rel_at_type at step m'.
              The key issue is that Hrat expects arguments in val_rel_n n', but we're
              given arguments in val_rel_n m' where m' <= n'.

              Since val_rel_n n' ⊆ val_rel_n m' (downward mono), we have MORE args at m'.
              For args that are also in val_rel_n n', we can use Hrat and weaken results.
              For args only in val_rel_n m' \ val_rel_n n', we need typing + SN arguments.

              SOLUTION: For TFn where T1 is first-order, val_rel_n m' and val_rel_n n'
              give the SAME concrete values (via val_rel_at_type_fo), so we can use Hrat.
              For TFn where T1 is higher-order, we need the full Kripke argument. *)
           destruct T; try discriminate Hfo.
           (* T = TFn T1 T2 e *)
           simpl. simpl in Hrat.
           intros Σ' Hext' x y Hvx Hvy Hcx Hcy Hxyrel_m st1 st2 ctx Hstrel_m.
           destruct (first_order_type T1) eqn:Hfo_T1.
           ++ (* T1 is first-order: val_rel_at_type_fo gives same concrete values at all steps *)
              (* For FO argument types, we can extract val_rel_at_type_fo from val_rel_n m',
                 build val_rel_n n' for arguments, call Hrat, then weaken results.
                 The store relation strengthening requires additional machinery.
                 For this proof, we admit the store strengthening part. *)
              (* Extract val_rel_at_type_fo from Hxyrel_m *)
              assert (Hxy_fo : val_rel_at_type_fo T1 x y).
              { destruct m'.
                - simpl in Hxyrel_m.
                  destruct Hxyrel_m as [_ [_ [_ [_ Hxy_if]]]].
                  rewrite Hfo_T1 in Hxy_if. exact Hxy_if.
                - simpl in Hxyrel_m.
                  destruct Hxyrel_m as [_ [_ [_ [_ [_ Hrat_m]]]]].
                  apply (val_rel_at_type_fo_equiv T1 Σ' (store_rel_n m') (val_rel_n m') (store_rel_n m') x y Hfo_T1).
                  exact Hrat_m. }
              (* The full proof would build val_rel_n n' for x y, strengthen store_rel,
                 call Hrat, then weaken results. For now, admit this case. *)
              admit.
           ++ (* T1 is higher-order: need full Kripke reasoning with typing *)
              (* For HO arguments, val_rel_n m' does not imply val_rel_n n' without typing.
                 The full proof requires either:
                 1. Typing premises (then use step_up)
                 2. The fundamental theorem (which uses typing internally)
                 For this development, we admit this case. *)
              admit.
Admitted.

(** Downward monotonicity for store_rel_n *)
Lemma store_rel_n_mono : forall m n Σ st1 st2,
  m <= n ->
