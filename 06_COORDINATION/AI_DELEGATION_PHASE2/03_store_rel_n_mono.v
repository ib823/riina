  m <= n ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n m Σ st1 st2.
Proof.
  intros m n Σ st1 st2 Hle.
  generalize dependent m.
  induction n as [| n' IHn]; intros m Hle Hrel.
  - inversion Hle. exact Hrel.
  - destruct m as [| m'].
    + simpl. simpl in Hrel.
      destruct Hrel as [_ [Hmax _]]. exact Hmax.
    + simpl. simpl in Hrel.
      destruct Hrel as [Hrec [Hmax Hlocs]].
      split; [| split].
      * apply IHn. lia. exact Hrec.
      * exact Hmax.
      * intros l T sl Hlook.
        destruct (Hlocs l T sl Hlook) as [v1 [v2 [Hl1 [Hl2 Hvrel]]]].
        exists v1, v2. repeat split; try assumption.
        apply val_rel_n_mono with (n := n'). lia. exact Hvrel.
Qed.

(** ========================================================================
    SECTION 6: FORMER AXIOMS - NOW PROVABLE AS LEMMAS
    ========================================================================

    With val_rel_n 0 carrying structure, all structural axioms become
    PROVABLE using the extraction lemmas above.
*)

(** FORMER AXIOM 1: exp_rel_step1_fst - NOW PROVEN *)
Lemma exp_rel_step1_fst : forall Σ T1 T2 v v' st1 st2 ctx Σ',
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  val_rel_n 0 Σ' (TProd T1 T2) v v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EFst v, st1, ctx) -->* (a1, st1', ctx') /\
    (EFst v', st2, ctx) -->* (a2, st2', ctx') /\
    value a1 /\ value a2 /\
    val_rel_n 0 Σ'' T1 a1 a2 /\
    store_rel_n 0 Σ'' st1' st2'.
Proof.
  intros Σ T1 T2 v v' st1 st2 ctx Σ' Hfo1 Hfo2 Hval Hstore Hext.

  (* Extract pair structure from val_rel_n 0 *)
  destruct (val_rel_n_prod_structure 0 Σ' T1 T2 v v' Hfo1 Hfo2 Hval)
    as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hva1 [Hvb1 [Hva2 Hvb2]]]]]]]]].
  subst v v'.

  (* Get closed properties *)
  destruct (val_rel_n_closed 0 Σ' (TProd T1 T2) (EPair a1 b1) (EPair a2 b2) Hval)
    as [Hcl1 Hcl2].

  exists a1, a2, st1, st2, ctx, Σ'.
  split. { apply store_ty_extends_refl. }
  split.
  { apply MS_Step with (cfg2 := (a1, st1, ctx)).
    - apply ST_Fst; assumption.
    - apply MS_Refl. }
  split.
  { apply MS_Step with (cfg2 := (a2, st2, ctx)).
    - apply ST_Fst; assumption.
    - apply MS_Refl. }
  split. { exact Hva1. }
  split. { exact Hva2. }
  split.
  { (* val_rel_n 0 Σ' T1 a1 a2 - prove directly *)
    rewrite val_rel_n_0_unfold.
    repeat split.
    - exact Hva1.
    - exact Hva2.
    - intros y Hfree. apply (Hcl1 y). simpl. left. exact Hfree.
    - intros y Hfree. apply (Hcl2 y). simpl. left. exact Hfree.
    - rewrite Hfo1.
      (* Hval has type TProd T1 T2, need to extract relation for T1 *)
      rewrite val_rel_n_0_unfold in Hval.
      destruct Hval as [_ [_ [_ [_ Hrat]]]].
      (* first_order_type (TProd T1 T2) = first_order_type T1 && first_order_type T2 *)
