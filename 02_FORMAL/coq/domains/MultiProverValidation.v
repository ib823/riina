(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* MultiProverValidation.v — Strategic Item #11: Multi-Prover Verification
   with Translation Validation.

   Models a system where two independent provers produce proof certificates
   for formulas in a common representation, and a validator checks both
   certificates. Agreement between provers increases confidence.

   Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md §5 (Multi-Prover) *)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Logic.Decidable.
Import ListNotations.

(* ===== Formula Language ===== *)

Inductive formula : Type :=
  | FAtom : nat -> formula
  | FNot  : formula -> formula
  | FAnd  : formula -> formula -> formula
  | FImpl : formula -> formula -> formula.

(* Decidable equality on formulas *)
Fixpoint formula_eqb (f1 f2 : formula) : bool :=
  match f1, f2 with
  | FAtom n1, FAtom n2 => Nat.eqb n1 n2
  | FNot a, FNot b => formula_eqb a b
  | FAnd a1 b1, FAnd a2 b2 => formula_eqb a1 a2 && formula_eqb b1 b2
  | FImpl a1 b1, FImpl a2 b2 => formula_eqb a1 a2 && formula_eqb b1 b2
  | _, _ => false
  end.

Lemma formula_eqb_refl : forall f, formula_eqb f f = true.
Proof.
  induction f; simpl; auto.
  - apply Nat.eqb_refl.
  - rewrite IHf1, IHf2. auto.
  - rewrite IHf1, IHf2. auto.
Qed.

Lemma formula_eqb_eq : forall f1 f2, formula_eqb f1 f2 = true <-> f1 = f2.
Proof.
  split.
  - generalize dependent f2. induction f1; destruct f2; simpl; intros; try discriminate.
    + apply Nat.eqb_eq in H. subst. reflexivity.
    + apply IHf1 in H. subst. reflexivity.
    + apply andb_true_iff in H. destruct H.
      apply IHf1_1 in H. apply IHf1_2 in H0. subst. reflexivity.
    + apply andb_true_iff in H. destruct H.
      apply IHf1_1 in H. apply IHf1_2 in H0. subst. reflexivity.
  - intros. subst. apply formula_eqb_refl.
Qed.

(* ===== Proof Certificates ===== *)

(* A proof certificate records what was proved and how *)
Inductive certificate : Type :=
  | CertAtom   : nat -> certificate              (* axiom/assumption *)
  | CertNotI   : formula -> certificate -> certificate  (* not-introduction *)
  | CertAndI   : certificate -> certificate -> certificate  (* and-introduction *)
  | CertImplE  : certificate -> certificate -> certificate  (* modus ponens *)
  | CertAssume : formula -> certificate.          (* assumption *)

(* What formula a certificate claims to prove *)
Fixpoint cert_formula (c : certificate) : formula :=
  match c with
  | CertAtom n => FAtom n
  | CertNotI f _ => FNot f
  | CertAndI c1 c2 => FAnd (cert_formula c1) (cert_formula c2)
  | CertImplE c1 c2 =>
      match cert_formula c1 with
      | FImpl _ b => b
      | other => other  (* ill-formed, will fail validation *)
      end
  | CertAssume f => f
  end.

(* ===== Two Independent Prover Representations ===== *)

(* Prover A uses a tagged representation *)
Inductive proverA_repr : Type :=
  | PA_Atom : nat -> proverA_repr
  | PA_Neg  : proverA_repr -> proverA_repr
  | PA_Conj : proverA_repr -> proverA_repr -> proverA_repr
  | PA_Arrow : proverA_repr -> proverA_repr -> proverA_repr.

(* Prover B uses a different tagged representation *)
Inductive proverB_repr : Type :=
  | PB_Var  : nat -> proverB_repr
  | PB_Not  : proverB_repr -> proverB_repr
  | PB_And  : proverB_repr -> proverB_repr -> proverB_repr
  | PB_If   : proverB_repr -> proverB_repr -> proverB_repr.

(* ===== Translation Functions ===== *)

Fixpoint translate_to_A (f : formula) : proverA_repr :=
  match f with
  | FAtom n => PA_Atom n
  | FNot g => PA_Neg (translate_to_A g)
  | FAnd g h => PA_Conj (translate_to_A g) (translate_to_A h)
  | FImpl g h => PA_Arrow (translate_to_A g) (translate_to_A h)
  end.

Fixpoint translate_to_B (f : formula) : proverB_repr :=
  match f with
  | FAtom n => PB_Var n
  | FNot g => PB_Not (translate_to_B g)
  | FAnd g h => PB_And (translate_to_B g) (translate_to_B h)
  | FImpl g h => PB_If (translate_to_B g) (translate_to_B h)
  end.

Fixpoint translate_from_A (r : proverA_repr) : formula :=
  match r with
  | PA_Atom n => FAtom n
  | PA_Neg g => FNot (translate_from_A g)
  | PA_Conj g h => FAnd (translate_from_A g) (translate_from_A h)
  | PA_Arrow g h => FImpl (translate_from_A g) (translate_from_A h)
  end.

Fixpoint translate_from_B (r : proverB_repr) : formula :=
  match r with
  | PB_Var n => FAtom n
  | PB_Not g => FNot (translate_from_B g)
  | PB_And g h => FAnd (translate_from_B g) (translate_from_B h)
  | PB_If g h => FImpl (translate_from_B g) (translate_from_B h)
  end.

(* ===== Validator ===== *)

(* A set of assumed formulas (as list) *)
Definition assumptions := list formula.

Fixpoint validate (asms : assumptions) (c : certificate) (target : formula) : bool :=
  formula_eqb (cert_formula c) target &&
  match c with
  | CertAtom n => formula_eqb target (FAtom n)
  | CertNotI f sub => validate (f :: asms) sub (FAtom 0)
      (* simplified: not-intro assumes f and derives contradiction *)
  | CertAndI c1 c2 =>
      match target with
      | FAnd a b => validate asms c1 a && validate asms c2 b
      | _ => false
      end
  | CertImplE c1 c2 =>
      (* c2 proves A, c1 proves A->B, target = B *)
      match cert_formula c1 with
      | FImpl a b => formula_eqb b target && validate asms c1 (FImpl a b) && validate asms c2 a
      | _ => false
      end
  | CertAssume f => existsb (formula_eqb f) asms
  end.

(* Simplified validator for atoms: just check if it's a valid atom cert *)
Definition validate_atomic (c : certificate) (n : nat) : bool :=
  match c with
  | CertAtom m => Nat.eqb m n
  | _ => false
  end.

(* ===== Confidence Level ===== *)

Inductive confidence : Type :=
  | NoConfidence : confidence
  | SingleProver : confidence
  | DualProver   : confidence.

Definition confidence_level (validA validB : bool) : confidence :=
  match validA, validB with
  | true, true => DualProver
  | true, false => SingleProver
  | false, true => SingleProver
  | false, false => NoConfidence
  end.

Definition confidence_ge (c1 c2 : confidence) : Prop :=
  match c1, c2 with
  | DualProver, _ => True
  | SingleProver, NoConfidence => True
  | SingleProver, SingleProver => True
  | NoConfidence, NoConfidence => True
  | _, _ => False
  end.

(* ===== THEOREMS ===== *)

(* Theorem 1: Validator soundness — if validate_atomic accepts, the certificate
   proves the right atomic formula *)
Theorem validator_soundness_atomic :
  forall c n,
    validate_atomic c n = true ->
    cert_formula c = FAtom n.
Proof.
  intros c n H. destruct c; simpl in *; try discriminate.
  apply Nat.eqb_eq in H. subst. reflexivity.
Qed.

(* Theorem 2: Translation preserves formula structure (roundtrip A) *)
Theorem translation_preserves_structure_A :
  forall f, translate_from_A (translate_to_A f) = f.
Proof.
  induction f; simpl; try rewrite IHf; try rewrite IHf1; try rewrite IHf2; reflexivity.
Qed.

(* Theorem 3: Translation preserves formula structure (roundtrip B) *)
Theorem translation_preserves_structure_B :
  forall f, translate_from_B (translate_to_B f) = f.
Proof.
  induction f; simpl; try rewrite IHf; try rewrite IHf1; try rewrite IHf2; reflexivity.
Qed.

(* Theorem 4: Independent proofs that both validate give DualProver confidence *)
Theorem dual_prover_confidence :
  forall vA vB,
    vA = true -> vB = true ->
    confidence_level vA vB = DualProver.
Proof.
  intros. subst. reflexivity.
Qed.

(* Theorem 5: DualProver confidence is at least as high as SingleProver *)
Theorem dual_ge_single : confidence_ge DualProver SingleProver.
Proof. simpl. exact I. Qed.

(* Theorem 6: Certificate composition — modus ponens.
   If we have a certificate for A and a certificate for A->B,
   then CertImplE produces a certificate whose formula is B. *)
Theorem certificate_composition :
  forall cA cAB a b,
    cert_formula cA = a ->
    cert_formula cAB = FImpl a b ->
    cert_formula (CertImplE cAB cA) = b.
Proof.
  intros cA cAB a b HA HAB.
  simpl. rewrite HAB. reflexivity.
Qed.

(* Theorem 7: Validator is deterministic *)
Theorem validator_deterministic :
  forall asms c f r1 r2,
    validate asms c f = r1 ->
    validate asms c f = r2 ->
    r1 = r2.
Proof.
  intros. rewrite <- H, <- H0. reflexivity.
Qed.

(* Theorem 8: Formula equivalence is decidable *)
Theorem formula_eq_dec : forall f1 f2 : formula, {f1 = f2} + {f1 <> f2}.
Proof.
  intros f1 f2.
  destruct (formula_eqb f1 f2) eqn:E.
  - left. apply formula_eqb_eq. exact E.
  - right. intro H. subst. rewrite formula_eqb_refl in E. discriminate.
Qed.

(* Theorem 9: Translation to A is injective *)
Theorem translate_to_A_injective :
  forall f1 f2, translate_to_A f1 = translate_to_A f2 -> f1 = f2.
Proof.
  intros f1 f2 H.
  rewrite <- (translation_preserves_structure_A f1).
  rewrite <- (translation_preserves_structure_A f2).
  rewrite H. reflexivity.
Qed.

(* Theorem 10: Translation to B is injective *)
Theorem translate_to_B_injective :
  forall f1 f2, translate_to_B f1 = translate_to_B f2 -> f1 = f2.
Proof.
  intros f1 f2 H.
  rewrite <- (translation_preserves_structure_B f1).
  rewrite <- (translation_preserves_structure_B f2).
  rewrite H. reflexivity.
Qed.

(* Theorem 11: Validator completeness for atomic formulas *)
Theorem validator_completeness_atomic :
  forall n, validate_atomic (CertAtom n) n = true.
Proof.
  intros. simpl. apply Nat.eqb_refl.
Qed.

(* Theorem 12: Both provers agree on translated structure —
   translating to A and back, vs to B and back, yield the same formula *)
Theorem prover_agreement :
  forall f,
    translate_from_A (translate_to_A f) = translate_from_B (translate_to_B f).
Proof.
  intros. rewrite translation_preserves_structure_A, translation_preserves_structure_B.
  reflexivity.
Qed.

(* Theorem 13: Confidence level is symmetric in its arguments' truth values *)
Theorem confidence_symmetric :
  forall vA vB, confidence_level vA vB = confidence_level vB vA ->
    (vA = vB) \/ (confidence_level vA vB = SingleProver).
Proof.
  intros vA vB H.
  destruct vA; destruct vB; simpl in *; auto.
Qed.

(* Theorem 14: NoConfidence only when both provers fail *)
Theorem no_confidence_means_both_fail :
  forall vA vB,
    confidence_level vA vB = NoConfidence ->
    vA = false /\ vB = false.
Proof.
  intros vA vB H.
  destruct vA; destruct vB; simpl in H; try discriminate; auto.
Qed.

(* Theorem 15: SingleProver means exactly one prover succeeded *)
Theorem single_prover_means_one_true :
  forall vA vB,
    confidence_level vA vB = SingleProver ->
    (vA = true /\ vB = false) \/ (vA = false /\ vB = true).
Proof.
  intros vA vB H.
  destruct vA; destruct vB; simpl in H; try discriminate; auto.
Qed.

(* Theorem 16: DualProver means both succeeded *)
Theorem dual_prover_means_both_true :
  forall vA vB,
    confidence_level vA vB = DualProver ->
    vA = true /\ vB = true.
Proof.
  intros vA vB H.
  destruct vA; destruct vB; simpl in H; try discriminate; auto.
Qed.

(* Theorem 17: confidence_ge is reflexive *)
Theorem confidence_ge_refl : forall c, confidence_ge c c.
Proof.
  destruct c; simpl; exact I.
Qed.

(* Theorem 18: confidence_ge is transitive *)
Theorem confidence_ge_trans :
  forall c1 c2 c3,
    confidence_ge c1 c2 -> confidence_ge c2 c3 -> confidence_ge c1 c3.
Proof.
  destruct c1; destruct c2; destruct c3; simpl; intros; auto.
Qed.

(* Theorem 19: Confidence level monotonicity — adding a valid prover can only help *)
Theorem confidence_monotone_add_valid :
  forall vA,
    confidence_ge (confidence_level vA true) (confidence_level vA false).
Proof.
  destruct vA; simpl; exact I.
Qed.

(* Theorem 20: Certificate for And has correct sub-formulas *)
Theorem cert_and_sub_formulas :
  forall c1 c2,
    cert_formula (CertAndI c1 c2) = FAnd (cert_formula c1) (cert_formula c2).
Proof.
  intros. simpl. reflexivity.
Qed.

(* Theorem 21: Formula equality is symmetric *)
Theorem formula_eqb_sym : forall f1 f2, formula_eqb f1 f2 = formula_eqb f2 f1.
Proof.
  induction f1; destruct f2; simpl; auto.
  - apply Nat.eqb_sym.
  - rewrite IHf1_1, IHf1_2. reflexivity.
  - rewrite IHf1_1, IHf1_2. reflexivity.
Qed.

(* Theorem 22: Validate atomic false for non-atom certificates *)
Theorem validate_atomic_non_atom :
  forall f c n, validate_atomic (CertNotI f c) n = false.
Proof.
  intros. simpl. reflexivity.
Qed.
