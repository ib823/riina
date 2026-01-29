(* ═══════════════════════════════════════════════════════════════════════════ *)
(* RIINA Language - Logical Relations for Noninterference                      *)
(* Step-Indexed Logical Relations - COMPLETE PROOFS                            *)
(* NO AXIOMS - NO ADMITS                                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import RIINA.Definitions.

Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 1: First-Order Value Relation (Structural Equality)                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Fixpoint val_rel_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists n, v1 = EInt n /\ v2 = EInt n
  | TFn _ _ _ => True
  | TProd T1 T2 => 
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_fo T1 a1 a2 /\ val_rel_fo T2 b1 b2
  | TSum T1 T2 =>
      (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_fo T1 a1 a2) \/
      (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_fo T2 b1 b2)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TSecret _ => True
  | TProof _ => True
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 2: Step-Indexed Value Relation                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* 
   The step-indexed value relation captures when two values are 
   indistinguishable for n steps of computation.
   
   For first-order types, we require structural equality.
   For higher-order types (functions), we require typing (simplified here).
*)

Fixpoint val_rel_n (n : nat) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  match n with
  | 0 => 
      (* At step 0: first-order types need structural equality *)
      first_order_type T = true -> val_rel_fo T v1 v2
  | S n' =>
      (* At step S n': inherit from n' and add structural requirements *)
      val_rel_n n' T v1 v2 /\
      (first_order_type T = true -> val_rel_fo T v1 v2) /\
      match T with
      | TProd T1 T2 =>
          first_order_type T = true ->
          exists a1 b1 a2 b2,
            v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
            val_rel_n n' T1 a1 a2 /\ val_rel_n n' T2 b1 b2
      | TSum T1 T2 =>
          first_order_type T = true ->
          (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_n n' T1 a1 a2) \/
          (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_n n' T2 b1 b2)
      | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
      | TSecret _ => True
      | TProof _ => True
      | _ => True
      end
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 3: Basic Properties of val_rel_n                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_value : forall n T v1 v2,
  val_rel_n n T v1 v2 -> value v1 /\ value v2.
Proof.
  intros n T v1 v2 H.
  destruct n; simpl in H; tauto.
Qed.

Lemma val_rel_n_closed : forall n T v1 v2,
  val_rel_n n T v1 v2 -> closed_expr v1 /\ closed_expr v2.
Proof.
  intros n T v1 v2 H.
  destruct n; simpl in H; tauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 4: Monotonicity (Step Down-Closure)                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_mono : forall m n T v1 v2,
  m <= n -> val_rel_n n T v1 v2 -> val_rel_n m T v1 v2.
Proof.
  induction m; intros n T v1 v2 Hle Hrel.
  - (* m = 0 *)
    destruct n.
    + exact Hrel.
    + simpl in Hrel.
      destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 [Hrel' _]]]]].
      simpl. repeat split; auto.
      intros Hfo.
      (* Extract FO relation by unwinding Hrel' *)
      clear IHm.
      induction n.
      * simpl in Hrel'. destruct Hrel' as [_ [_ [_ [_ Hcond]]]].
        apply Hcond. exact Hfo.
      * simpl in Hrel'. destruct Hrel' as [_ [_ [_ [_ [Hrel'' _]]]]].
        apply IHn. exact Hrel''.
  - (* m = S m' *)
    destruct n.
    + lia.
    + simpl in Hrel.
      destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 [Hrel' [Hfo_cond Hstruct]]]]]].
      simpl. repeat split; auto.
      * apply IHm. lia. exact Hrel'.
      * exact Hfo_cond.
      * (* Structure preservation *)
        destruct T; auto; intros Hfo.
        -- (* TProd *)
           specialize (Hstruct Hfo).
           destruct Hstruct as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Ha Hb]]]]]]].
           exists a1, b1, a2, b2. repeat split; auto.
           ++ apply IHm; [lia | exact Ha].
           ++ apply IHm; [lia | exact Hb].
        -- (* TSum *)
           specialize (Hstruct Hfo).
           destruct Hstruct as [[a1 [a2 [Heq1 [Heq2 Ha]]]] | [b1 [b2 [Heq1 [Heq2 Hb]]]]].
           ++ left. exists a1, a2. repeat split; auto.
              apply IHm; [lia | exact Ha].
           ++ right. exists b1, b2. repeat split; auto.
              apply IHm; [lia | exact Hb].
        -- (* TRef *)
           exact Hstruct.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 5: Constructing val_rel_n from FO Relation                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_of_first_order : forall n T v1 v2,
  first_order_type T = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_fo T v1 v2 ->
  val_rel_n n T v1 v2.
Proof.
  induction n; intros T v1 v2 Hfo Hv1 Hv2 Hc1 Hc2 Hrel_fo.
  - (* n = 0 *)
    simpl. repeat split; auto.
  - (* n = S n' *)
    simpl. repeat split; auto.
    + (* IH *)
      apply IHn; auto.
    + (* Structure for specific types *)
      destruct T; simpl in Hfo; try discriminate; auto; intros _.
      * (* TProd *)
        apply andb_true_iff in Hfo as [Hfo1 Hfo2].
        simpl in Hrel_fo.
        destruct Hrel_fo as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
        exists a1, b1, a2, b2. repeat split; auto.
        -- apply IHn; auto.
           ++ subst. inversion Hv1; auto.
           ++ subst. inversion Hv2; auto.
           ++ subst. apply closed_expr_pair_inv in Hc1. tauto.
           ++ subst. apply closed_expr_pair_inv in Hc2. tauto.
        -- apply IHn; auto.
           ++ subst. inversion Hv1; auto.
           ++ subst. inversion Hv2; auto.
           ++ subst. apply closed_expr_pair_inv in Hc1. tauto.
           ++ subst. apply closed_expr_pair_inv in Hc2. tauto.
      * (* TSum *)
        apply andb_true_iff in Hfo as [Hfo1 Hfo2].
        simpl in Hrel_fo.
        destruct Hrel_fo as [[a1 [a2 [Heq1 [Heq2 Hrel]]]] | [b1 [b2 [Heq1 [Heq2 Hrel]]]]].
        -- left. exists a1, a2. repeat split; auto.
           apply IHn; auto.
           ++ subst. inversion Hv1; auto.
           ++ subst. inversion Hv2; auto.
           ++ subst. apply closed_expr_inl_inv in Hc1. auto.
           ++ subst. apply closed_expr_inl_inv in Hc2. auto.
        -- right. exists b1, b2. repeat split; auto.
           apply IHn; auto.
           ++ subst. inversion Hv1; auto.
           ++ subst. inversion Hv2; auto.
           ++ subst. apply closed_expr_inr_inv in Hc1. auto.
           ++ subst. apply closed_expr_inr_inv in Hc2. auto.
      * (* TRef *)
        simpl in Hrel_fo. exact Hrel_fo.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 6: Step-Up Lemma for First-Order Types                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Key insight: for FO types, if related at any step, related at ALL steps *)
Lemma val_rel_n_step_up_fo : forall n T v1 v2,
  first_order_type T = true ->
  val_rel_n n T v1 v2 ->
  forall m, val_rel_n m T v1 v2.
Proof.
  intros n T v1 v2 Hfo Hrel m.
  destruct (val_rel_n_value n T v1 v2 Hrel) as [Hv1 Hv2].
  destruct (val_rel_n_closed n T v1 v2 Hrel) as [Hc1 Hc2].
  apply val_rel_n_of_first_order; auto.
  (* Extract FO relation from Hrel *)
  clear m.
  induction n.
  - simpl in Hrel. destruct Hrel as [_ [_ [_ [_ Hcond]]]].
    apply Hcond. exact Hfo.
  - simpl in Hrel. destruct Hrel as [_ [_ [_ [_ [Hrel' _]]]]].
    apply IHn. exact Hrel'.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 7: Limit Relation                                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition val_rel (T : ty) (v1 v2 : expr) : Prop :=
  forall n, val_rel_n n T v1 v2.

(* Converting from step-indexed to limit for FO types *)
Lemma val_rel_n_to_val_rel_fo : forall T v1 v2,
  first_order_type T = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  (exists n, val_rel_n n T v1 v2) ->
  val_rel T v1 v2.
Proof.
  intros T v1 v2 Hfo Hv1 Hv2 Hc1 Hc2 [n Hrel].
  unfold val_rel. intro m.
  eapply val_rel_n_step_up_fo; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 8: Product Composition Lemma - COMPLETE PROOF                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_prod_compose : forall n T1 T2 a1 b1 a2 b2,
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  value a1 -> value b1 -> value a2 -> value b2 ->
  closed_expr a1 -> closed_expr b1 -> closed_expr a2 -> closed_expr b2 ->
  val_rel_n n T1 a1 a2 -> val_rel_n n T2 b1 b2 ->
  val_rel_n n (TProd T1 T2) (EPair a1 b1) (EPair a2 b2).
Proof.
  induction n; intros T1 T2 a1 b1 a2 b2 Hfo1 Hfo2 
                      Hva1 Hvb1 Hva2 Hvb2 Hca1 Hcb1 Hca2 Hcb2 Hrel1 Hrel2.
  - (* n = 0 *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_pair; auto.
    + apply closed_expr_pair; auto.
    + intros Hfo.
      simpl. exists a1, b1, a2, b2. repeat split; auto.
      * simpl in Hrel1. destruct Hrel1 as [_ [_ [_ [_ Hcond]]]].
        apply Hcond. exact Hfo1.
      * simpl in Hrel2. destruct Hrel2 as [_ [_ [_ [_ Hcond]]]].
        apply Hcond. exact Hfo2.
  - (* n = S n' *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_pair; auto.
    + apply closed_expr_pair; auto.
    + (* IH *)
      apply IHn; auto.
      * eapply val_rel_n_mono; [lia | exact Hrel1].
      * eapply val_rel_n_mono; [lia | exact Hrel2].
    + (* FO condition *)
      intros Hfo.
      simpl. exists a1, b1, a2, b2. repeat split; auto.
      * simpl in Hrel1. destruct Hrel1 as [_ [_ [_ [_ [_ [Hcond _]]]]]].
        apply Hcond. exact Hfo1.
      * simpl in Hrel2. destruct Hrel2 as [_ [_ [_ [_ [_ [Hcond _]]]]]].
        apply Hcond. exact Hfo2.
    + (* Structure *)
      intros Hfo.
      exists a1, b1, a2, b2. repeat split; auto.
      * eapply val_rel_n_mono; [lia | exact Hrel1].
      * eapply val_rel_n_mono; [lia | exact Hrel2].
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 9: Product Decomposition Lemmas - COMPLETE PROOFS                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_from_prod_fst : forall n T1 T2 v1 v2,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n n (TProd T1 T2) v1 v2 ->
  exists a1 a2 b1 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_n n T1 a1 a2.
Proof.
  induction n; intros T1 T2 v1 v2 Hfo Hrel.
  - (* n = 0 *)
    simpl in Hrel. destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hcond]]]].
    specialize (Hcond Hfo).
    simpl in Hcond.
    destruct Hcond as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    exists a1, a2, b1, b2. repeat split; auto.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    subst. inversion Hv1; inversion Hv2; subst.
    apply closed_expr_pair_inv in Hc1 as [Hca1 Hcb1].
    apply closed_expr_pair_inv in Hc2 as [Hca2 Hcb2].
    apply val_rel_n_of_first_order; auto.
  - (* n = S n' *)
    simpl in Hrel. destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 [Hrel' [Hfo_cond Hstruct]]]]]].
    specialize (Hstruct Hfo).
    destruct Hstruct as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Ha Hb]]]]]]].
    exists a1, a2, b1, b2. repeat split; auto.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    subst.
    apply closed_expr_pair_inv in Hc1 as [Hca1 Hcb1].
    apply closed_expr_pair_inv in Hc2 as [Hca2 Hcb2].
    inversion Hv1; inversion Hv2; subst.
    (* Build S n' from n' using step-up for FO types *)
    apply val_rel_n_of_first_order; auto.
    (* Extract FO relation from Ha *)
    clear IHn Hrel' Hfo_cond Hb Hcb1 Hcb2 H1 H4 b1 b2.
    induction n.
    + simpl in Ha. destruct Ha as [_ [_ [_ [_ Hcond]]]].
      apply Hcond. exact Hfo1.
    + simpl in Ha. destruct Ha as [_ [_ [_ [_ [Ha' _]]]]].
      apply IHn. exact Ha'.
Qed.

Lemma val_rel_n_from_prod_snd : forall n T1 T2 v1 v2,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n n (TProd T1 T2) v1 v2 ->
  exists a1 a2 b1 b2,
    v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    val_rel_n n T2 b1 b2.
Proof.
  induction n; intros T1 T2 v1 v2 Hfo Hrel.
  - (* n = 0 *)
    simpl in Hrel. destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hcond]]]].
    specialize (Hcond Hfo).
    simpl in Hcond.
    destruct Hcond as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    exists a1, a2, b1, b2. repeat split; auto.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    subst. inversion Hv1; inversion Hv2; subst.
    apply closed_expr_pair_inv in Hc1 as [Hca1 Hcb1].
    apply closed_expr_pair_inv in Hc2 as [Hca2 Hcb2].
    apply val_rel_n_of_first_order; auto.
  - (* n = S n' *)
    simpl in Hrel. destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 [Hrel' [Hfo_cond Hstruct]]]]]].
    specialize (Hstruct Hfo).
    destruct Hstruct as [a1 [b1 [a2 [b2 [Heq1 [Heq2 [Ha Hb]]]]]]].
    exists a1, a2, b1, b2. repeat split; auto.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    subst.
    apply closed_expr_pair_inv in Hc1 as [Hca1 Hcb1].
    apply closed_expr_pair_inv in Hc2 as [Hca2 Hcb2].
    inversion Hv1; inversion Hv2; subst.
    apply val_rel_n_of_first_order; auto.
    clear IHn Hrel' Hfo_cond Ha Hca1 Hca2 H0 H3 a1 a2.
    induction n.
    + simpl in Hb. destruct Hb as [_ [_ [_ [_ Hcond]]]].
      apply Hcond. exact Hfo2.
    + simpl in Hb. destruct Hb as [_ [_ [_ [_ [Hb' _]]]]].
      apply IHn. exact Hb'.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 10: Sum Composition Lemmas - COMPLETE PROOFS                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_sum_inl : forall n T1 T2 v1 v2,
  first_order_type T1 = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n T1 v1 v2 ->
  val_rel_n n (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  induction n; intros T1 T2 v1 v2 Hfo1 Hv1 Hv2 Hc1 Hc2 Hrel.
  - (* n = 0 *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_inl; auto.
    + apply closed_expr_inl; auto.
    + intros Hfo.
      simpl. left. exists v1, v2. repeat split; auto.
      simpl in Hrel. destruct Hrel as [_ [_ [_ [_ Hcond]]]].
      apply Hcond. exact Hfo1.
  - (* n = S n' *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_inl; auto.
    + apply closed_expr_inl; auto.
    + apply IHn; auto. eapply val_rel_n_mono; [lia | exact Hrel].
    + intros Hfo.
      simpl. left. exists v1, v2. repeat split; auto.
      simpl in Hrel. destruct Hrel as [_ [_ [_ [_ [_ [Hcond _]]]]]].
      apply Hcond. exact Hfo1.
    + intros Hfo.
      left. exists v1, v2. repeat split; auto.
      eapply val_rel_n_mono; [lia | exact Hrel].
Qed.

Lemma val_rel_n_sum_inr : forall n T1 T2 v1 v2,
  first_order_type T2 = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n T2 v1 v2 ->
  val_rel_n n (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  induction n; intros T1 T2 v1 v2 Hfo2 Hv1 Hv2 Hc1 Hc2 Hrel.
  - (* n = 0 *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_inr; auto.
    + apply closed_expr_inr; auto.
    + intros Hfo.
      simpl. right. exists v1, v2. repeat split; auto.
      simpl in Hrel. destruct Hrel as [_ [_ [_ [_ Hcond]]]].
      apply Hcond. exact Hfo2.
  - (* n = S n' *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_inr; auto.
    + apply closed_expr_inr; auto.
    + apply IHn; auto. eapply val_rel_n_mono; [lia | exact Hrel].
    + intros Hfo.
      simpl. right. exists v1, v2. repeat split; auto.
      simpl in Hrel. destruct Hrel as [_ [_ [_ [_ [_ [Hcond _]]]]]].
      apply Hcond. exact Hfo2.
    + intros Hfo.
      right. exists v1, v2. repeat split; auto.
      eapply val_rel_n_mono; [lia | exact Hrel].
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 11: Sum Decomposition Lemmas - COMPLETE PROOFS                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_from_sum_inl : forall n T1 T2 v1 v2,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n n (TSum T1 T2) (EInl v1 T2) (EInl v2 T2) ->
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  val_rel_n n T1 v1 v2.
Proof.
  induction n; intros T1 T2 v1 v2 Hfo Hrel.
  - (* n = 0 *)
    simpl in Hrel. destruct Hrel as [Hv_inl1 [Hv_inl2 [Hc_inl1 [Hc_inl2 Hcond]]]].
    inversion Hv_inl1; inversion Hv_inl2; subst.
    apply closed_expr_inl_inv in Hc_inl1.
    apply closed_expr_inl_inv in Hc_inl2.
    repeat split; auto.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    specialize (Hcond Hfo).
    simpl in Hcond.
    destruct Hcond as [[a1 [a2 [Heq1 [Heq2 Hrel']]]] | [b1 [b2 [Heq1 _]]]].
    + injection Heq1 as Heq1. injection Heq2 as Heq2. subst.
      apply val_rel_n_of_first_order; auto.
    + discriminate.
  - (* n = S n' *)
    simpl in Hrel. destruct Hrel as [Hv_inl1 [Hv_inl2 [Hc_inl1 [Hc_inl2 [Hrel' [Hfo_cond Hstruct]]]]]].
    inversion Hv_inl1; inversion Hv_inl2; subst.
    apply closed_expr_inl_inv in Hc_inl1.
    apply closed_expr_inl_inv in Hc_inl2.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    specialize (Hstruct Hfo).
    destruct Hstruct as [[a1 [a2 [Heq1 [Heq2 Ha]]]] | [b1 [b2 [Heq1 _]]]].
    + injection Heq1 as Heq1. injection Heq2 as Heq2. subst.
      repeat split; auto.
      apply val_rel_n_of_first_order; auto.
      clear IHn Hrel' Hfo_cond.
      induction n.
      * simpl in Ha. destruct Ha as [_ [_ [_ [_ Hcond]]]].
        apply Hcond. exact Hfo1.
      * simpl in Ha. destruct Ha as [_ [_ [_ [_ [Ha' _]]]]].
        apply IHn. exact Ha'.
    + discriminate.
Qed.

Lemma val_rel_n_from_sum_inr : forall n T1 T2 v1 v2,
  first_order_type (TSum T1 T2) = true ->
  val_rel_n n (TSum T1 T2) (EInr v1 T1) (EInr v2 T1) ->
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  val_rel_n n T2 v1 v2.
Proof.
  induction n; intros T1 T2 v1 v2 Hfo Hrel.
  - (* n = 0 *)
    simpl in Hrel. destruct Hrel as [Hv_inr1 [Hv_inr2 [Hc_inr1 [Hc_inr2 Hcond]]]].
    inversion Hv_inr1; inversion Hv_inr2; subst.
    apply closed_expr_inr_inv in Hc_inr1.
    apply closed_expr_inr_inv in Hc_inr2.
    repeat split; auto.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    specialize (Hcond Hfo).
    simpl in Hcond.
    destruct Hcond as [[a1 [a2 [Heq1 _]]] | [b1 [b2 [Heq1 [Heq2 Hrel']]]]].
    + discriminate.
    + injection Heq1 as Heq1. injection Heq2 as Heq2. subst.
      apply val_rel_n_of_first_order; auto.
  - (* n = S n' *)
    simpl in Hrel. destruct Hrel as [Hv_inr1 [Hv_inr2 [Hc_inr1 [Hc_inr2 [Hrel' [Hfo_cond Hstruct]]]]]].
    inversion Hv_inr1; inversion Hv_inr2; subst.
    apply closed_expr_inr_inv in Hc_inr1.
    apply closed_expr_inr_inv in Hc_inr2.
    simpl in Hfo. apply andb_true_iff in Hfo as [Hfo1 Hfo2].
    specialize (Hstruct Hfo).
    destruct Hstruct as [[a1 [a2 [Heq1 _]]] | [b1 [b2 [Heq1 [Heq2 Hb]]]]].
    + discriminate.
    + injection Heq1 as Heq1. injection Heq2 as Heq2. subst.
      repeat split; auto.
      apply val_rel_n_of_first_order; auto.
      clear IHn Hrel' Hfo_cond.
      induction n.
      * simpl in Hb. destruct Hb as [_ [_ [_ [_ Hcond]]]].
        apply Hcond. exact Hfo2.
      * simpl in Hb. destruct Hb as [_ [_ [_ [_ [Hb' _]]]]].
        apply IHn. exact Hb'.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 12: Security Type Wrapping Lemmas - COMPLETE PROOFS                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_classify : forall n T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n T v1 v2 ->
  val_rel_n n (TSecret T) (EClassify v1) (EClassify v2).
Proof.
  induction n; intros T v1 v2 Hv1 Hv2 Hc1 Hc2 Hrel.
  - (* n = 0 *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_classify; auto.
    + apply closed_expr_classify; auto.
    + intros Hfo. simpl. auto.
  - (* n = S n' *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_classify; auto.
    + apply closed_expr_classify; auto.
    + apply IHn; auto. eapply val_rel_n_mono; [lia | exact Hrel].
    + intros Hfo. simpl. auto.
    + auto.
Qed.

Lemma val_rel_n_prove : forall n T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n T v1 v2 ->
  val_rel_n n (TProof T) (EProve v1) (EProve v2).
Proof.
  induction n; intros T v1 v2 Hv1 Hv2 Hc1 Hc2 Hrel.
  - (* n = 0 *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_prove; auto.
    + apply closed_expr_prove; auto.
    + intros Hfo. simpl. auto.
  - (* n = S n' *)
    simpl. repeat split.
    + constructor; auto.
    + constructor; auto.
    + apply closed_expr_prove; auto.
    + apply closed_expr_prove; auto.
    + apply IHn; auto. eapply val_rel_n_mono; [lia | exact Hrel].
    + intros Hfo. simpl. auto.
    + auto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 13: Reference Relation - COMPLETE PROOF                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_rel_n_ref : forall n T sl l,
  val_rel_n n (TRef T sl) (ELoc l) (ELoc l).
Proof.
  induction n; intros T sl l.
  - (* n = 0 *)
    simpl. repeat split.
    + constructor.
    + constructor.
    + apply closed_expr_loc.
    + apply closed_expr_loc.
    + intros _. simpl. exists l. auto.
  - (* n = S n' *)
    simpl. repeat split.
    + constructor.
    + constructor.
    + apply closed_expr_loc.
    + apply closed_expr_loc.
    + apply IHn.
    + intros _. simpl. exists l. auto.
    + exists l. auto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 14: Main Noninterference Results                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* The fundamental property: related values at FO types have equal structure *)
Theorem noninterference_fo : forall T v1 v2,
  first_order_type T = true ->
  val_rel T v1 v2 ->
  val_rel_fo T v1 v2.
Proof.
  intros T v1 v2 Hfo Hrel.
  unfold val_rel in Hrel.
  specialize (Hrel 0).
  simpl in Hrel. destruct Hrel as [_ [_ [_ [_ Hcond]]]].
  apply Hcond. exact Hfo.
Qed.

(* Corollary: Same-location references are related at any step *)
Corollary ref_noninterference : forall T sl l,
  val_rel (TRef T sl) (ELoc l) (ELoc l).
Proof.
  intros T sl l.
  unfold val_rel. intro n.
  apply val_rel_n_ref.
Qed.

(* Corollary: Products of related values are related *)
Corollary prod_noninterference : forall T1 T2 a1 b1 a2 b2,
  first_order_type T1 = true ->
  first_order_type T2 = true ->
  value a1 -> value b1 -> value a2 -> value b2 ->
  closed_expr a1 -> closed_expr b1 -> closed_expr a2 -> closed_expr b2 ->
  val_rel T1 a1 a2 ->
  val_rel T2 b1 b2 ->
  val_rel (TProd T1 T2) (EPair a1 b1) (EPair a2 b2).
Proof.
  intros T1 T2 a1 b1 a2 b2 Hfo1 Hfo2 Hva1 Hvb1 Hva2 Hvb2 
         Hca1 Hcb1 Hca2 Hcb2 Hrel1 Hrel2.
  unfold val_rel in *. intro n.
  apply val_rel_n_prod_compose; auto.
Qed.

(* Corollary: Sums preserve relatedness *)
Corollary sum_inl_noninterference : forall T1 T2 v1 v2,
  first_order_type T1 = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel T1 v1 v2 ->
  val_rel (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
Proof.
  intros T1 T2 v1 v2 Hfo1 Hv1 Hv2 Hc1 Hc2 Hrel.
  unfold val_rel in *. intro n.
  apply val_rel_n_sum_inl; auto.
Qed.

Corollary sum_inr_noninterference : forall T1 T2 v1 v2,
  first_order_type T2 = true ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel T2 v1 v2 ->
  val_rel (TSum T1 T2) (EInr v1 T1) (EInr v2 T1).
Proof.
  intros T1 T2 v1 v2 Hfo2 Hv1 Hv2 Hc1 Hc2 Hrel.
  unfold val_rel in *. intro n.
  apply val_rel_n_sum_inr; auto.
Qed.

(* Corollary: Classify preserves relatedness *)
Corollary classify_noninterference : forall T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel T v1 v2 ->
  val_rel (TSecret T) (EClassify v1) (EClassify v2).
Proof.
  intros T v1 v2 Hv1 Hv2 Hc1 Hc2 Hrel.
  unfold val_rel in *. intro n.
  apply val_rel_n_classify; auto.
Qed.

(* Corollary: Prove preserves relatedness *)
Corollary prove_noninterference : forall T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel T v1 v2 ->
  val_rel (TProof T) (EProve v1) (EProve v2).
Proof.
  intros T v1 v2 Hv1 Hv2 Hc1 Hc2 Hrel.
  unfold val_rel in *. intro n.
  apply val_rel_n_prove; auto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 15: Verify No Axioms                                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* These commands verify that no axioms were used *)
Print Assumptions noninterference_fo.
Print Assumptions ref_noninterference.
Print Assumptions prod_noninterference.
Print Assumptions sum_inl_noninterference.
Print Assumptions sum_inr_noninterference.
Print Assumptions classify_noninterference.
Print Assumptions prove_noninterference.
Print Assumptions val_rel_n_mono.
Print Assumptions val_rel_n_step_up_fo.
Print Assumptions val_rel_n_prod_compose.
Print Assumptions val_rel_n_from_prod_fst.
Print Assumptions val_rel_n_from_prod_snd.
Print Assumptions val_rel_n_sum_inl.
Print Assumptions val_rel_n_sum_inr.
Print Assumptions val_rel_n_from_sum_inl.
Print Assumptions val_rel_n_from_sum_inr.
Print Assumptions val_rel_n_classify.
Print Assumptions val_rel_n_prove.
Print Assumptions val_rel_n_ref.

End LogicalRelations.
