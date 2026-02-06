(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* LLMProofPipeline.v — LLM-Assisted Proof Generation Pipeline
   Strategic Item #3: Model a proof-checking pipeline for propositional logic.
   Spec: 06_COORDINATION/llm_proof_pipeline_design.md *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(* ========================================================================= *)
(* 1. Formula language: propositional logic                                  *)
(* ========================================================================= *)

Inductive formula : Type :=
  | FVar : nat -> formula
  | FImpl : formula -> formula -> formula
  | FConj : formula -> formula -> formula
  | FDisj : formula -> formula -> formula.

(* Decidable equality on formulas *)
Fixpoint formula_eqb (f1 f2 : formula) : bool :=
  match f1, f2 with
  | FVar n1, FVar n2 => Nat.eqb n1 n2
  | FImpl a1 b1, FImpl a2 b2 => formula_eqb a1 a2 && formula_eqb b1 b2
  | FConj a1 b1, FConj a2 b2 => formula_eqb a1 a2 && formula_eqb b1 b2
  | FDisj a1 b1, FDisj a2 b2 => formula_eqb a1 a2 && formula_eqb b1 b2
  | _, _ => false
  end.

Lemma formula_eqb_refl : forall f, formula_eqb f f = true.
Proof.
  induction f; simpl; auto.
  - apply Nat.eqb_refl.
  - rewrite IHf1, IHf2; auto.
  - rewrite IHf1, IHf2; auto.
  - rewrite IHf1, IHf2; auto.
Qed.

Lemma formula_eqb_eq : forall f1 f2, formula_eqb f1 f2 = true -> f1 = f2.
Proof.
  induction f1; destruct f2; simpl; intros H; try discriminate.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply IHf1_1 in H1. apply IHf1_2 in H2. subst. reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply IHf1_1 in H1. apply IHf1_2 in H2. subst. reflexivity.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply IHf1_1 in H1. apply IHf1_2 in H2. subst. reflexivity.
Qed.

Lemma formula_eqb_neq : forall f1 f2, formula_eqb f1 f2 = false -> f1 <> f2.
Proof.
  intros f1 f2 H Heq. subst. rewrite formula_eqb_refl in H. discriminate.
Qed.

(* ========================================================================= *)
(* 2. Semantics: valuations                                                  *)
(* ========================================================================= *)

Definition valuation := nat -> Prop.

Fixpoint sem (v : valuation) (f : formula) : Prop :=
  match f with
  | FVar n => v n
  | FImpl a b => sem v a -> sem v b
  | FConj a b => sem v a /\ sem v b
  | FDisj a b => sem v a \/ sem v b
  end.

Definition valid (f : formula) : Prop := forall v, sem v f.

(* ========================================================================= *)
(* 3. Proof terms                                                            *)
(* ========================================================================= *)

(* A context is a list of formulas (hypotheses). *)
Definition context := list formula.

(* Proof terms for natural deduction *)
Inductive proof_term : Type :=
  | PAxiom : nat -> proof_term                       (* use hypothesis by index *)
  | PImplIntro : formula -> proof_term -> proof_term  (* lambda: assume A, prove B *)
  | PImplElim : proof_term -> proof_term -> proof_term (* modus ponens *)
  | PConjIntro : proof_term -> proof_term -> proof_term
  | PConjElimL : proof_term -> proof_term
  | PConjElimR : proof_term -> proof_term.

(* ========================================================================= *)
(* 4. Type-checking / proof-checking (returns option formula)                *)
(* ========================================================================= *)

Fixpoint check (ctx : context) (p : proof_term) : option formula :=
  match p with
  | PAxiom n => nth_error ctx n
  | PImplIntro a body =>
      match check (a :: ctx) body with
      | Some b => Some (FImpl a b)
      | None => None
      end
  | PImplElim pf pa =>
      match check ctx pf, check ctx pa with
      | Some (FImpl a b), Some a' =>
          if formula_eqb a a' then Some b else None
      | _, _ => None
      end
  | PConjIntro pl pr =>
      match check ctx pl, check ctx pr with
      | Some a, Some b => Some (FConj a b)
      | _, _ => None
      end
  | PConjElimL pc =>
      match check ctx pc with
      | Some (FConj a _) => Some a
      | _ => None
      end
  | PConjElimR pc =>
      match check ctx pc with
      | Some (FConj _ b) => Some b
      | _ => None
      end
  end.

(* ========================================================================= *)
(* 5. Soundness relation: derivability in natural deduction                  *)
(* ========================================================================= *)

Inductive derives : context -> formula -> Prop :=
  | D_Ax : forall ctx n f,
      nth_error ctx n = Some f -> derives ctx f
  | D_ImplI : forall ctx a b,
      derives (a :: ctx) b -> derives ctx (FImpl a b)
  | D_ImplE : forall ctx a b,
      derives ctx (FImpl a b) -> derives ctx a -> derives ctx b
  | D_ConjI : forall ctx a b,
      derives ctx a -> derives ctx b -> derives ctx (FConj a b)
  | D_ConjEL : forall ctx a b,
      derives ctx (FConj a b) -> derives ctx a
  | D_ConjER : forall ctx a b,
      derives ctx (FConj a b) -> derives ctx b.

(* ========================================================================= *)
(* 6. Soundness of the checker w.r.t. derives                               *)
(* ========================================================================= *)

(* Theorem 1: Proof checker soundness *)
Theorem checker_soundness : forall ctx p f,
  check ctx p = Some f -> derives ctx f.
Proof.
  intros ctx p. revert ctx.
  induction p; intros ctx goal Hcheck; simpl in Hcheck.
  - (* PAxiom *)
    eapply D_Ax. exact Hcheck.
  - (* PImplIntro *)
    destruct (check (f :: ctx) p) eqn:E; [|discriminate].
    injection Hcheck as Hgoal. subst goal.
    apply D_ImplI. eapply IHp. exact E.
  - (* PImplElim *)
    destruct (check ctx p1) eqn:E1; [|discriminate].
    destruct f; try discriminate.
    destruct (check ctx p2) eqn:E2; [|discriminate].
    destruct (formula_eqb f1 f) eqn:Eeq; [|discriminate].
    injection Hcheck as Hgoal. subst goal.
    apply formula_eqb_eq in Eeq. subst.
    eapply D_ImplE; [eapply IHp1|eapply IHp2]; eauto.
  - (* PConjIntro *)
    destruct (check ctx p1) eqn:E1; [|discriminate].
    destruct (check ctx p2) eqn:E2; [|discriminate].
    injection Hcheck as Hgoal. subst goal.
    apply D_ConjI; [eapply IHp1|eapply IHp2]; eauto.
  - (* PConjElimL *)
    destruct (check ctx p) eqn:E; [|discriminate].
    destruct f; try discriminate.
    injection Hcheck as Hgoal. subst goal.
    eapply D_ConjEL. eapply IHp. exact E.
  - (* PConjElimR *)
    destruct (check ctx p) eqn:E; [|discriminate].
    destruct f; try discriminate.
    injection Hcheck as Hgoal. subst goal.
    eapply D_ConjER. eapply IHp. exact E.
Qed.

(* ========================================================================= *)
(* 7. Semantic soundness of derives                                          *)
(* ========================================================================= *)

(* A valuation satisfies a context if it satisfies every formula in it. *)
Definition satisfies_ctx (v : valuation) (ctx : context) : Prop :=
  forall n f, nth_error ctx n = Some f -> sem v f.

Lemma derives_sound : forall ctx f,
  derives ctx f -> forall v, satisfies_ctx v ctx -> sem v f.
Proof.
  induction 1; intros v Hsat; simpl.
  - apply Hsat with (n := n). exact H.
  - intro Ha. apply IHderives. intros [|k] g Hg; simpl in Hg.
    + injection Hg as <-. exact Ha.
    + apply Hsat with (n := k). exact Hg.
  - apply IHderives1; auto. apply IHderives2; auto.
  - split; [apply IHderives1|apply IHderives2]; auto.
  - destruct (IHderives v Hsat) as [Ha _]. exact Ha.
  - destruct (IHderives v Hsat) as [_ Hb]. exact Hb.
Qed.

(* ========================================================================= *)
(* Theorem 2: Identity proof A -> A is valid                                 *)
(* ========================================================================= *)

Definition identity_proof (a : formula) : proof_term :=
  PImplIntro a (PAxiom 0).

Theorem identity_proof_valid : forall a,
  check [] (identity_proof a) = Some (FImpl a a).
Proof.
  intros a. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(* Theorem 3: Composition of proofs (A->B, B->C gives A->C)                 *)
(* ========================================================================= *)

Definition compose_proof (a b c : formula) : proof_term :=
  (* In context [A->B, B->C], prove A->C *)
  (* We build a closed proof: assume A->B and B->C in context, then intro A *)
  PImplIntro a (PImplElim (PAxiom 2) (PImplElim (PAxiom 1) (PAxiom 0))).

Theorem compose_proof_valid : forall a b c,
  check [FImpl a b; FImpl b c] (compose_proof a b c) = Some (FImpl a c).
Proof.
  intros a b c. simpl.
  rewrite formula_eqb_refl.
  rewrite formula_eqb_refl.
  reflexivity.
Qed.

(* ========================================================================= *)
(* Theorem 4: Conjunction introduction is valid                              *)
(* ========================================================================= *)

Definition conj_intro_proof (a b : formula) : proof_term :=
  PConjIntro (PAxiom 0) (PAxiom 1).

Theorem conj_intro_valid : forall a b,
  check [a; b] (conj_intro_proof a b) = Some (FConj a b).
Proof.
  intros a b. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(* Theorem 5a: Conjunction elimination left                                  *)
(* ========================================================================= *)

Definition conj_elim_left (a b : formula) : proof_term :=
  PConjElimL (PAxiom 0).

Theorem conj_elim_left_valid : forall a b,
  check [FConj a b] (conj_elim_left a b) = Some a.
Proof.
  intros a b. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(* Theorem 5b: Conjunction elimination right                                 *)
(* ========================================================================= *)

Definition conj_elim_right (a b : formula) : proof_term :=
  PConjElimR (PAxiom 0).

Theorem conj_elim_right_valid : forall a b,
  check [FConj a b] (conj_elim_right a b) = Some b.
Proof.
  intros a b. simpl. reflexivity.
Qed.

(* ========================================================================= *)
(* Theorem 6: Proof checker is deterministic                                 *)
(* ========================================================================= *)

Theorem checker_deterministic : forall ctx p f1 f2,
  check ctx p = Some f1 -> check ctx p = Some f2 -> f1 = f2.
Proof.
  intros ctx p f1 f2 H1 H2. rewrite H1 in H2. injection H2. auto.
Qed.

(* ========================================================================= *)
(* Theorem 7: Invalid proofs are rejected                                    *)
(* ========================================================================= *)

(* Applying a non-implication fails *)
Theorem invalid_modus_ponens_rejected : forall ctx p1 p2 a,
  check ctx p1 = Some (FVar a) ->
  check ctx (PImplElim p1 p2) = None.
Proof.
  intros ctx p1 p2 a H. simpl.
  rewrite H. reflexivity.
Qed.

(* Axiom with out-of-range index fails *)
Theorem invalid_axiom_rejected : forall ctx n,
  nth_error ctx n = None -> check ctx (PAxiom n) = None.
Proof.
  intros ctx n H. simpl. exact H.
Qed.

(* Modus ponens with mismatched types fails *)
Theorem invalid_mismatch_rejected : forall ctx p1 p2 a a' b,
  check ctx p1 = Some (FImpl a b) ->
  check ctx p2 = Some a' ->
  formula_eqb a a' = false ->
  check ctx (PImplElim p1 p2) = None.
Proof.
  intros ctx p1 p2 a a' b H1 H2 Hneq. simpl.
  rewrite H1, H2, Hneq. reflexivity.
Qed.

(* ========================================================================= *)
(* Theorem 8: Weakening — valid proof in Γ is valid in Γ,A                   *)
(* ========================================================================= *)

(* We prove weakening for the derives relation (semantic level). *)

Lemma nth_error_insert : forall (ctx : context) (n pos : nat) (a : formula),
  pos <= n ->
  nth_error ctx n = nth_error (firstn pos ctx ++ a :: skipn pos ctx) (S n).
Proof.
  intros ctx n pos a Hle.
  revert ctx n Hle.
  induction pos; intros ctx n Hle; simpl.
  - reflexivity.
  - destruct ctx as [|h t]; simpl.
    + destruct n; simpl; [lia|]. destruct (n - pos); reflexivity.
    + destruct n as [|n']; [lia|]. simpl.
      apply IHpos. lia.
Qed.

(* A cleaner approach: prove weakening for derives directly. *)
Lemma weakening_derives : forall ctx f,
  derives ctx f -> forall a, derives (ctx ++ [a]) f.
Proof.
  induction 1; intros a0.
  - apply D_Ax with (n := n).
    rewrite nth_error_app1; auto.
    apply nth_error_Some. congruence.
  - apply D_ImplI.
    change ((a :: ctx) ++ [a0]) with (a :: (ctx ++ [a0])).
    apply IHderives.
  - eapply D_ImplE; [apply IHderives1|apply IHderives2].
  - apply D_ConjI; [apply IHderives1|apply IHderives2].
  - eapply D_ConjEL. apply IHderives.
  - eapply D_ConjER. apply IHderives.
Qed.

Theorem weakening : forall ctx f a,
  derives ctx f -> derives (ctx ++ [a]) f.
Proof.
  intros. apply weakening_derives. exact H.
Qed.

(* ========================================================================= *)
(* Theorem 9 (Bonus): Full pipeline soundness —                              *)
(*   if checker accepts in empty context, formula is valid                    *)
(* ========================================================================= *)

Theorem pipeline_soundness : forall p f,
  check [] p = Some f -> valid f.
Proof.
  intros p f Hcheck v.
  apply derives_sound with (ctx := []).
  - apply checker_soundness with (p := p). exact Hcheck.
  - intros n g Hn. destruct n; simpl in Hn; discriminate.
Qed.

(* ========================================================================= *)
(* Theorem 10 (Bonus): Identity proof produces a valid formula               *)
(* ========================================================================= *)

Theorem identity_is_valid : forall a v, sem v (FImpl a a).
Proof.
  intros a v. simpl. auto.
Qed.

(* Theorem 11: Conjunction is commutative under semantics *)
Theorem conj_comm_sem : forall a b v, sem v (FConj a b) -> sem v (FConj b a).
Proof.
  intros a b v H. simpl in *. tauto.
Qed.
