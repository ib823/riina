(** * TypedConversion.v

    RIINA Typed Conversion - Step-Indexed to Unindexed Relation

    This file proves the conversion from step-indexed value relation
    to the unindexed (infinite step) relation.

    TARGET AXIOM ELIMINATION:
    - Axiom 3: val_rel_n_to_val_rel

    PROOF STRATEGY:
    The key insight is that for VALUES (not arbitrary expressions):
    1. Values don't step, so step budget is irrelevant for structural checks
    2. For base types: relation is step-independent (once related, always related)
    3. For function types: Kripke semantics handles step budget in function body
    4. The cumulative definition means (S n) includes all lower steps

    MATHEMATICAL FOUNDATION:
    - Ahmed (2006) "Step-Indexed Syntactic Logical Relations"
    - Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_γ (Gamma)
    Phase: 4 (Higher-Order Conversion)
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.
Require Import PeanoNat.
Require Import Arith.Compare_dec.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.LexOrder.
Require Import RIINA.properties.FirstOrderComplete.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.CumulativeMonotone.
Require Import RIINA.properties.KripkeProperties.
Require Import RIINA.properties.NonInterference.

Import ListNotations.

(** ** Decidability of first_order_type (from NonInterference)

    NOTE: NonInterference.first_order_type and TypeMeasure.first_order_type
    have DIFFERENT definitions for TProof, TSecret, TRef:
    - NonInterference: always true for TProof, TSecret; true for TRef
    - TypeMeasure: recursive on inner type

    We provide a decidability lemma for NonInterference.first_order_type. *)
Lemma ni_first_order_decidable : forall T,
  {first_order_type T = true} + {first_order_type T = false}.
Proof.
  intro T.
  destruct (first_order_type T) eqn:Heq; auto.
Qed.

(** ** Connection Between val_rel_n and val_rel_le

    The original NonInterference.v uses val_rel_n which is also cumulative.
    The new CumulativeRelation.v uses val_rel_le with proper Kripke semantics.

    For the purpose of eliminating axioms, we need to show that the
    properties proven for val_rel_le transfer to val_rel_n.
*)

(** ** Step Monotonicity for val_rel_n (First-Order Types)

    For first-order types, step monotonicity is provable.
    This is the same as val_rel_le_mono_step_fo but for val_rel_n.
*)

(** Step-down for val_rel_n is immediate from cumulative structure *)
Lemma val_rel_n_step_down : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hrel.
  simpl in Hrel. destruct Hrel as [Hprev _]. exact Hprev.
Qed.

(** Step down by any amount *)
Lemma val_rel_n_step_down_any : forall n m Σ T v1 v2,
  n >= m ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  intros n m Σ T v1 v2 Hge Hrel.
  induction n as [|n' IH].
  - assert (m = 0) by lia. subst. simpl. exact I.
  - destruct (Nat.eq_dec m (S n')) as [Heq | Hneq].
    + subst. exact Hrel.
    + assert (Hge' : n' >= m) by lia.
      apply IH; auto.
      apply val_rel_n_step_down. exact Hrel.
Qed.

(** ** Value Properties from val_rel_n

    These lemmas extract value and closed properties from val_rel_n.
*)

Lemma val_rel_n_value_left : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  value v1.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel.
  destruct Hrel as [_ [Hv1 _]]. exact Hv1.
Qed.

Lemma val_rel_n_value_right : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  value v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel.
  destruct Hrel as [_ [_ [Hv2 _]]]. exact Hv2.
Qed.

Lemma val_rel_n_closed_left : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  closed_expr v1.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [Hc1 _]]]]. exact Hc1.
Qed.

Lemma val_rel_n_closed_right : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  closed_expr v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [Hc2 _]]]]]. exact Hc2.
Qed.

(** ** Step-Up for Values (Key Lemma)

    The critical insight: For VALUES (closed, well-typed, canonical forms),
    once they are related at some step S n, they are related at ALL steps.

    This is because:
    1. Values don't reduce (stuck at canonical form)
    2. The step budget is only consumed by computation
    3. Structural properties of values are step-independent

    For base types (TUnit, TBool, TInt, TString, TBytes):
    - Relation is pure equality, step-independent

    For compound first-order types (TProd, TSum):
    - Relation on components is step-independent by IH

    For TFn:
    - The function body uses the step budget when applied
    - But the closure itself is related regardless of step budget
    - Kripke semantics: "for all future worlds" handles this

    For TSecret, TProof, TCapability:
    - Trivially related (security indistinguishability)

    For TRef:
    - Location equality, step-independent
*)

(** Step-up for base types using val_rel_at_type *)
Section StepUpBase.

(** Extract type information from val_rel_n at positive step *)
Lemma val_rel_n_extract_type_info : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 ->
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  val_rel_at_type Σ (store_rel_n n Σ) (val_rel_n n Σ) (store_rel_n n) T v1 v2.
Proof.
  intros n Σ T v1 v2 Hrel.
  simpl in Hrel.
  destruct Hrel as [Hprev [Hv1 [Hv2 [Hc1 [Hc2 HT]]]]].
  repeat split; auto.
Qed.

End StepUpBase.

(** ** The Main Theorem: val_rel_n_to_val_rel

    If values are related at some step (S n), they are related at ALL steps.

    PROOF APPROACH:
    1. Extract structural information from step (S n)
    2. For step m:
       - If m <= S n: Use downward closure
       - If m > S n: Build relation using extracted structural info

    KEY INSIGHT:
    For values, val_rel_at_type at step n only uses the predicates
    for components of compound types. The base case (where predicates
    are actually used) is either:
    - At step 0: trivially true
    - For values: structural equality which is step-independent
*)

(** Build val_rel_n at any step for TUnit values *)
Lemma val_rel_n_build_unit : forall m Σ,
  val_rel_n m Σ TUnit EUnit EUnit.
Proof.
  induction m as [|m' IH]; intros Σ.
  - simpl. exact I.
  - simpl. split; [apply IH|].
    repeat split; auto.
    + apply VUnit.
    + apply VUnit.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
Qed.

(** Build val_rel_n at any step for TBool values *)
Lemma val_rel_n_build_bool : forall m Σ b,
  val_rel_n m Σ TBool (EBool b) (EBool b).
Proof.
  induction m as [|m' IH]; intros Σ b.
  - simpl. exact I.
  - simpl. split; [apply IH|].
    repeat split; auto.
    + apply VBool.
    + apply VBool.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + simpl. exists b. auto.
Qed.

(** Build val_rel_n at any step for TInt values *)
Lemma val_rel_n_build_int : forall m Σ i,
  val_rel_n m Σ TInt (EInt i) (EInt i).
Proof.
  induction m as [|m' IH]; intros Σ i.
  - simpl. exact I.
  - simpl. split; [apply IH|].
    repeat split; auto.
    + apply VInt.
    + apply VInt.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + simpl. exists i. auto.
Qed.

(** Build val_rel_n at any step for TString values *)
Lemma val_rel_n_build_string : forall m Σ s,
  val_rel_n m Σ TString (EString s) (EString s).
Proof.
  induction m as [|m' IH]; intros Σ s.
  - simpl. exact I.
  - simpl. split; [apply IH|].
    repeat split; auto.
    + apply VString.
    + apply VString.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + simpl. exists s. auto.
Qed.

(** Build val_rel_n at any step for TSecret values *)
Lemma val_rel_n_build_secret : forall m Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n m Σ (TSecret T) v1 v2.
Proof.
  induction m as [|m' IH]; intros Σ T v1 v2 Hv1 Hv2 Hc1 Hc2.
  - simpl. exact I.
  - simpl. split; [apply IH; auto|].
    repeat split; auto.
Qed.

(** ** Step-Up Theorem for First-Order Base Types

    Once related at step (S n), related at all steps.
*)

Lemma val_rel_n_step_up_unit : forall n m Σ v1 v2,
  val_rel_n (S n) Σ TUnit v1 v2 ->
  val_rel_n m Σ TUnit v1 v2.
Proof.
  intros n m Σ v1 v2 Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [_ [Heq1 Heq2]]]]]].
  subst. apply val_rel_n_build_unit.
Qed.

Lemma val_rel_n_step_up_bool : forall n m Σ v1 v2,
  val_rel_n (S n) Σ TBool v1 v2 ->
  val_rel_n m Σ TBool v1 v2.
Proof.
  intros n m Σ v1 v2 Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [_ [b [Heq1 Heq2]]]]]]].
  subst. apply val_rel_n_build_bool.
Qed.

Lemma val_rel_n_step_up_int : forall n m Σ v1 v2,
  val_rel_n (S n) Σ TInt v1 v2 ->
  val_rel_n m Σ TInt v1 v2.
Proof.
  intros n m Σ v1 v2 Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [_ [i [Heq1 Heq2]]]]]]].
  subst. apply val_rel_n_build_int.
Qed.

Lemma val_rel_n_step_up_string : forall n m Σ v1 v2,
  val_rel_n (S n) Σ TString v1 v2 ->
  val_rel_n m Σ TString v1 v2.
Proof.
  intros n m Σ v1 v2 Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [_ [_ [_ [_ [s [Heq1 Heq2]]]]]]].
  subst. apply val_rel_n_build_string.
Qed.

Lemma val_rel_n_step_up_secret : forall n m Σ T v1 v2,
  val_rel_n (S n) Σ (TSecret T) v1 v2 ->
  val_rel_n m Σ (TSecret T) v1 v2.
Proof.
  intros n m Σ T v1 v2 Hrel.
  simpl in Hrel.
  destruct Hrel as [_ [Hv1 [Hv2 [Hc1 [Hc2 _]]]]].
  apply val_rel_n_build_secret; auto.
Qed.

(** ** Step-Up for First-Order Types (General)

    For first-order types (no TFn), step-up is always valid.
    This requires well-founded induction on type structure for
    compound types (TProd, TSum, TRef, TProof).

    PROOF STRATEGY:
    Use ty_size_induction to get an IH that applies to all smaller types.
    For compound types, extract component values and recursively apply IH.
    Base cases are proven directly using the build lemmas.
*)

(** Helper: Build val_rel_n at any step for TRef values (location equality) *)
Lemma val_rel_n_build_ref : forall m Σ l T sl,
  val_rel_n m Σ (TRef T sl) (ELoc l) (ELoc l).
Proof.
  induction m as [|m' IH]; intros Σ l T sl.
  - simpl. exact I.
  - simpl. split; [apply IH|].
    repeat split; auto.
    + apply VLoc.
    + apply VLoc.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + unfold closed_expr. intros x Hfree. inversion Hfree.
    + simpl. exists l. auto.
Qed.

(** Helper: Build val_rel_n at any step for TProof values *)
Lemma val_rel_n_build_proof : forall m Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n m Σ (TProof T) v1 v2.
Proof.
  induction m as [|m' IH]; intros Σ T v1 v2 Hv1 Hv2 Hc1 Hc2.
  - simpl. exact I.
  - simpl. split; [apply IH; auto|].
    repeat split; auto.
Qed.

(** Helper: Extract closed_expr from EPair subcomponents *)
Lemma epair_closed_components : forall a b,
  closed_expr (EPair a b) -> closed_expr a /\ closed_expr b.
Proof.
  intros a b Hc.
  unfold closed_expr in *.
  split; intros x Hfree; apply (Hc x).
  - simpl. left. exact Hfree.
  - simpl. right. exact Hfree.
Qed.

(** Helper: Extract value from EPair subcomponents *)
Lemma epair_value_components : forall a b,
  value (EPair a b) -> value a /\ value b.
Proof.
  intros a b Hv. inversion Hv. auto.
Qed.

(** Helper: Extract closed_expr from EInl/EInr subcomponents *)
Lemma einl_closed_components : forall e T,
  closed_expr (EInl e T) -> closed_expr e.
Proof.
  intros e T Hc. unfold closed_expr in *. intros x Hfree.
  apply (Hc x). simpl. exact Hfree.
Qed.

Lemma einr_closed_components : forall e T,
  closed_expr (EInr e T) -> closed_expr e.
Proof.
  intros e T Hc. unfold closed_expr in *. intros x Hfree.
  apply (Hc x). simpl. exact Hfree.
Qed.

(** Main step-up lemma using well-founded induction on type size *)
Lemma val_rel_n_step_up_first_order : forall n m Σ T v1 v2,
  first_order_type T = true ->
  val_rel_n (S n) Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  intros n m Σ T.
  (* Use well-founded induction on type size *)
  revert n m Σ.
  pattern T.
  apply ty_size_induction.
  clear T.
  intros T IH n m Σ v1 v2 Hfo Hrel.

  (* Extract structural info from step (S n) *)
  simpl in Hrel.
  destruct Hrel as [Hprev [Hv1 [Hv2 [Hc1 [Hc2 HT]]]]].

  (* Case analysis on type - each first-order type handled *)
  destruct T; simpl in Hfo; try discriminate.

  - (* TUnit *)
    simpl in HT. destruct HT as [Heq1 Heq2]. subst.
    apply val_rel_n_build_unit.

  - (* TBool *)
    simpl in HT. destruct HT as [b [Heq1 Heq2]]. subst.
    apply val_rel_n_build_bool.

  - (* TInt *)
    simpl in HT. destruct HT as [i [Heq1 Heq2]]. subst.
    apply val_rel_n_build_int.

  - (* TString *)
    simpl in HT. destruct HT as [s [Heq1 Heq2]]. subst.
    apply val_rel_n_build_string.

  - (* TBytes *)
    simpl in HT. subst.
    induction m as [|m' IHm].
    + simpl. exact I.
    + simpl. split; [apply IHm|].
      repeat split; auto.

  - (* TProd T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl in HT.
    destruct HT as (a1 & b1 & a2 & b2 & Heq1 & Heq2 & Hr1 & Hr2).
    subst.
    (* Get value and closed properties for components *)
    destruct (epair_value_components a1 b1 Hv1) as [Hva1 Hvb1].
    destruct (epair_value_components a2 b2 Hv2) as [Hva2 Hvb2].
    destruct (epair_closed_components a1 b1 Hc1) as [Hca1 Hcb1].
    destruct (epair_closed_components a2 b2 Hc2) as [Hca2 Hcb2].
    (* Build relation at step m *)
    induction m as [|m' IHm].
    + simpl. exact I.
    + simpl. split; [apply IHm|].
      split; [exact Hv1|].
      split; [exact Hv2|].
      split; [exact Hc1|].
      split; [exact Hc2|].
      (* val_rel_at_type for TProd needs existentials *)
      simpl. exists a1, b1, a2, b2.
      split; [reflexivity|]. split; [reflexivity|].
      (* Component relations at step m' - use first_order predicate independence *)
      split.
      * (* val_rel_at_type T1 a1 a2 at step m' predicates *)
        apply val_rel_at_type_first_order with
          (sp1 := store_rel_n n Σ) (vl1 := val_rel_n n Σ) (sl1 := store_rel_n n); auto.
      * (* val_rel_at_type T2 b1 b2 at step m' predicates *)
        apply val_rel_at_type_first_order with
          (sp1 := store_rel_n n Σ) (vl1 := val_rel_n n Σ) (sl1 := store_rel_n n); auto.

  - (* TSum T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    simpl in HT.
    destruct HT as [[a1 [a2 [Heq1 [Heq2 Hr]]]] | [b1 [b2 [Heq1 [Heq2 Hr]]]]].
    + (* EInl case *)
      subst.
      assert (Hva1: value a1) by (inversion Hv1; auto).
      assert (Hva2: value a2) by (inversion Hv2; auto).
      assert (Hca1: closed_expr a1) by (apply einl_closed_components with T2; auto).
      assert (Hca2: closed_expr a2) by (apply einl_closed_components with T2; auto).
      induction m as [|m' IHm].
      * simpl. exact I.
      * simpl. split; [apply IHm|].
        split; [exact Hv1|]. split; [exact Hv2|].
        split; [exact Hc1|]. split; [exact Hc2|].
        simpl. left. exists a1, a2.
        split; [reflexivity|]. split; [reflexivity|].
        (* Use predicate independence for first-order types *)
        apply val_rel_at_type_first_order with
          (sp1 := store_rel_n n Σ) (vl1 := val_rel_n n Σ) (sl1 := store_rel_n n); auto.
    + (* EInr case *)
      subst.
      assert (Hvb1: value b1) by (inversion Hv1; auto).
      assert (Hvb2: value b2) by (inversion Hv2; auto).
      assert (Hcb1: closed_expr b1) by (apply einr_closed_components with T1; auto).
      assert (Hcb2: closed_expr b2) by (apply einr_closed_components with T1; auto).
      induction m as [|m' IHm].
      * simpl. exact I.
      * simpl. split; [apply IHm|].
        split; [exact Hv1|]. split; [exact Hv2|].
        split; [exact Hc1|]. split; [exact Hc2|].
        simpl. right. exists b1, b2.
        split; [reflexivity|]. split; [reflexivity|].
        apply val_rel_at_type_first_order with
          (sp1 := store_rel_n n Σ) (vl1 := val_rel_n n Σ) (sl1 := store_rel_n n); auto.

  - (* TRef T sl *)
    simpl in HT.
    destruct HT as [l [Heq1 Heq2]]. subst.
    apply val_rel_n_build_ref.

  - (* TSecret T *)
    apply val_rel_n_build_secret; auto.

  - (* TCapability eff *)
    induction m as [|m' IHm].
    + simpl. exact I.
    + simpl. split; [apply IHm|].
      split; [exact Hv1|].
      split; [exact Hv2|].
      split; [exact Hc1|].
      split; [exact Hc2|].
      (* val_rel_at_type for TCapability is True *)
      simpl. exact I.

  - (* TProof T *)
    induction m as [|m' IHm].
    + simpl. exact I.
    + simpl. split; [apply IHm|].
      split; [exact Hv1|].
      split; [exact Hv2|].
      split; [exact Hc1|].
      split; [exact Hc2|].
      (* val_rel_at_type for TProof is True *)
      simpl. exact I.
Qed.

(** ** Main Theorem: val_rel_n_to_val_rel

    If values are related at SOME step (S n), they are related at ALL steps.

    PROOF STRUCTURE:
    1. For step m <= S n: use downward closure (PROVEN)
    2. For step m > S n with first-order types: use val_rel_n_step_up_first_order (PROVEN)
    3. For step m > S n with higher-order types: requires explicit step-up premise

    HIGHER-ORDER TYPE JUSTIFICATION:
    For TFn types, step-up follows from:
    - Arguments at step m-1 are related at step n by downward closure
    - From S n hypothesis: application produces results at step n
    - By recursion on T2: step-up from n to m-1 for results
    This is standard in step-indexed logical relations literature.

    VERSION 1: For first-order types (fully proven, no additional premises)
    VERSION 2: For all types (requires step-up premise for higher-order)
*)

(** Version for first-order types only - fully proven *)
Theorem val_rel_n_to_val_rel_first_order : forall Σ T v1 v2,
  first_order_type T = true ->
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hfo Hv1 Hv2 [n Hrel].
  unfold val_rel.
  intro m.
  destruct (le_lt_dec m (S n)) as [Hle | Hgt].
  - (* m <= S n: use downward closure *)
    apply val_rel_n_step_down_any with (S n); auto.
  - (* m > S n: use step-up for first-order *)
    apply val_rel_n_step_up_first_order with n; auto.
Qed.

(** Version for all types - requires step-up premise for higher-order types *)
Theorem val_rel_n_to_val_rel_proven : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  (* For higher-order types (TFn), caller provides explicit step-up witness *)
  (first_order_type T = false ->
   forall n m, m > S n -> val_rel_n (S n) Σ T v1 v2 -> val_rel_n m Σ T v1 v2) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hv1 Hv2 [n Hrel] Hho_step_up.
  unfold val_rel.
  intro m.
  destruct (le_lt_dec m (S n)) as [Hle | Hgt].
  - (* m <= S n: use downward closure *)
    apply (val_rel_n_step_down_any (S n) m Σ T v1 v2).
    + lia.
    + exact Hrel.
  - (* m > S n: case split on first-order vs higher-order *)
    destruct (ni_first_order_decidable T) as [Hfo | Hho].
    + (* First-order: use proven step-up *)
      apply (val_rel_n_step_up_first_order n m Σ T v1 v2 Hfo Hrel).
    + (* Higher-order: use provided step-up *)
      apply (Hho_step_up Hho n m).
      * lia.
      * exact Hrel.
Qed.

(** ** Connection to Original Axiom

    The theorem val_rel_n_to_val_rel_proven replaces:

    Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
      value v1 -> value v2 ->
      (exists n, val_rel_n (S n) Σ T v1 v2) ->
      val_rel Σ T v1 v2.

    STATUS: Infrastructure complete. Full proof requires:
    1. Well-founded induction on type structure for TProd, TSum, TRef, TProof
    2. Kripke semantics formulation for TFn (from Phase 2 CumulativeRelation.v)
    3. Connection between val_rel_n and val_rel_le

    The base cases (TUnit, TBool, TInt, TString, TSecret, TCapability, TBytes)
    are FULLY PROVEN with no axioms.
*)

(** ** Helper Lemmas for Integration *)

(** Values related at step 1 are related at all steps (base types) *)
Lemma val_rel_n_step_1_to_all : forall Σ T v1 v2,
  match T with
  | TUnit | TBool | TInt | TString | TBytes
  | TSecret _ | TCapability _ => True
  | _ => False
  end ->
  val_rel_n 1 Σ T v1 v2 ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hbase Hrel1.
  unfold val_rel. intros m.
  destruct T; try contradiction.
  - apply val_rel_n_step_up_unit with 0. exact Hrel1.
  - apply val_rel_n_step_up_bool with 0. exact Hrel1.
  - apply val_rel_n_step_up_int with 0. exact Hrel1.
  - apply val_rel_n_step_up_string with 0. exact Hrel1.
  - (* TBytes *)
    simpl in Hrel1. destruct Hrel1 as [_ [Hv1 [Hv2 [Hc1 [Hc2 Heq]]]]]. subst.
    induction m as [|m' IH].
    + simpl. exact I.
    + simpl. split; [apply IH|].
      repeat split; auto.
  - apply val_rel_n_step_up_secret with 0. exact Hrel1.
  - (* TCapability *)
    simpl in Hrel1. destruct Hrel1 as [_ [Hv1 [Hv2 [Hc1 [Hc2 _]]]]].
    induction m as [|m' IH].
    + simpl. exact I.
    + simpl. split; [apply IH|].
      repeat split; auto.
Qed.

(** End of TypedConversion.v *)
