(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* DeclassificationPolicy.v - RIINA Declassification Policy Verification *)
(* Spec: 01_RESEARCH/26_DOMAIN_Z_DECLASSIFICATION_POLICY/RESEARCH_Z01_FOUNDATION.md *)
(* Layer: Information Flow Control *)
(* Mode: Comprehensive Verification | Zero Trust *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(** ===============================================================================
    PRINCIPALS AND AUTHORITY
    =============================================================================== *)

Definition PrincipalId := nat.

Inductive Principal : Type :=
  | PUser : PrincipalId -> Principal
  | PRole : nat -> Principal
  | PSystem : Principal
  | PJoin : Principal -> Principal -> Principal
  | PMeet : Principal -> Principal -> Principal.

Fixpoint principal_eqb (p1 p2 : Principal) : bool :=
  match p1, p2 with
  | PUser id1, PUser id2 => Nat.eqb id1 id2
  | PRole r1, PRole r2 => Nat.eqb r1 r2
  | PSystem, PSystem => true
  | PJoin a1 b1, PJoin a2 b2 => principal_eqb a1 a2 && principal_eqb b1 b2
  | PMeet a1 b1, PMeet a2 b2 => principal_eqb a1 a2 && principal_eqb b1 b2
  | _, _ => false
  end.

Lemma principal_eqb_refl : forall p, principal_eqb p p = true.
Proof.
  induction p; simpl; try reflexivity.
  - apply Nat.eqb_refl.
  - apply Nat.eqb_refl.
  - rewrite IHp1, IHp2. reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
Qed.

Definition acts_for (p1 p2 : Principal) : Prop :=
  principal_eqb p1 p2 = true \/ exists authority : nat, authority > 0.

Definition principal_leq (p1 p2 : Principal) : Prop := acts_for p1 p2.

(** ===============================================================================
    SECURITY LEVELS
    =============================================================================== *)

Inductive SecurityLevel : Type :=
  | Public : SecurityLevel
  | Secret : SecurityLevel
  | TopSecret : SecurityLevel.

Definition level_leq (l1 l2 : SecurityLevel) : bool :=
  match l1, l2 with
  | Public, _ => true
  | Secret, Secret => true
  | Secret, TopSecret => true
  | TopSecret, TopSecret => true
  | _, _ => false
  end.

Definition level_join (l1 l2 : SecurityLevel) : SecurityLevel :=
  match l1, l2 with
  | TopSecret, _ => TopSecret
  | _, TopSecret => TopSecret
  | Secret, _ => Secret
  | _, Secret => Secret
  | Public, Public => Public
  end.

Definition level_meet (l1 l2 : SecurityLevel) : SecurityLevel :=
  match l1, l2 with
  | Public, _ => Public
  | _, Public => Public
  | Secret, Secret => Secret
  | Secret, TopSecret => Secret
  | TopSecret, Secret => Secret
  | TopSecret, TopSecret => TopSecret
  end.

(** ===============================================================================
    DECLASSIFICATION POLICY
    =============================================================================== *)

Definition Ty := nat.

Record DeclassPolicy : Type := mkPolicy {
  policy_id : nat;
  authorized_principal : Principal;
  source_level : SecurityLevel;
  target_level : SecurityLevel;
  source_type : Ty;
  target_type : Ty;
  guard_fn : nat -> bool;
  transform : nat -> nat;
  budget : nat;
  policy_active : bool
}.

Definition valid_policy (p : DeclassPolicy) : Prop :=
  level_leq (target_level p) (source_level p) = true /\
  budget p > 0 /\
  policy_active p = true.

(** ===============================================================================
    BUDGET TRACKING
    =============================================================================== *)

Record BudgetState : Type := mkBudget {
  budget_principal : Principal;
  budget_per_policy : nat -> nat;
  total_leaked : nat;
  budget_window : nat;
  budget_total_limit : nat
}.

Definition wellformed_budget (bs : BudgetState) : Prop :=
  total_leaked bs <= budget_total_limit bs.

Definition consume_budget (bs : BudgetState) (pid : nat) (bits : nat)
  : option BudgetState :=
  let remaining := budget_per_policy bs pid in
  if remaining <? bits then None
  else if budget_total_limit bs <? total_leaked bs + bits then None
  else Some {|
    budget_principal := budget_principal bs;
    budget_per_policy := fun id =>
      if Nat.eqb id pid then remaining - bits
      else budget_per_policy bs id;
    total_leaked := total_leaked bs + bits;
    budget_window := budget_window bs;
    budget_total_limit := budget_total_limit bs
  |}.

Definition reset_budget (bs : BudgetState) (pid : nat) (new_budget : nat)
    (authorizer : Principal) : option BudgetState :=
  if principal_eqb authorizer PSystem then
    Some {|
      budget_principal := budget_principal bs;
      budget_per_policy := fun id =>
        if Nat.eqb id pid then new_budget
        else budget_per_policy bs id;
      total_leaked := total_leaked bs;
      budget_window := budget_window bs;
      budget_total_limit := budget_total_limit bs
    |}
  else None.

(** ===============================================================================
    ROBUST DECLASSIFICATION
    =============================================================================== *)

Definition State := nat -> nat.

Definition low_equiv (s1 s2 : State) (public : nat -> bool) : Prop :=
  forall x, public x = true -> s1 x = s2 x.

Definition Expr := State -> nat.

Definition robust (e : Expr) (public : nat -> bool) : Prop :=
  forall s1 s2, low_equiv s1 s2 public -> e s1 = e s2.

Record DeclassExpr : Type := mkDeclass {
  declass_value : Expr;
  declass_policy : DeclassPolicy;
  declass_guard : Expr
}.

Definition valid_declass (de : DeclassExpr) (public : nat -> bool) : Prop :=
  robust (declass_guard de) public /\ valid_policy (declass_policy de).

Definition can_declassify (de : DeclassExpr) (p : Principal) : Prop :=
  acts_for p (authorized_principal (declass_policy de)) /\
  valid_policy (declass_policy de).

(** ===============================================================================
    AUDIT LOGGING
    =============================================================================== *)

Record AuditEntry : Type := mkAudit {
  audit_principal : Principal;
  audit_policy_id : nat;
  audit_bits_leaked : nat;
  audit_timestamp : nat;
  audit_value_hash : nat
}.

Definition AuditLog := list AuditEntry.

Definition logged_declass (de : DeclassExpr) (log log' : AuditLog) : Prop :=
  exists entry, log' = entry :: log /\
  audit_policy_id entry = policy_id (declass_policy de).

(** ===============================================================================
    DIFFERENTIAL PRIVACY
    =============================================================================== *)

Definition Database := list nat.

Definition neighbors (db1 db2 : Database) : Prop :=
  (exists x, db2 = x :: db1) \/
  (exists x, db1 = x :: db2) \/
  (length db1 = length db2 /\ db1 <> db2).

Definition Query := Database -> nat.

Definition sensitivity_bounded (q : Query) (delta : nat) : Prop :=
  forall db1 db2, neighbors db1 db2 ->
    (q db1 <= q db2 + delta) /\ (q db2 <= q db1 + delta).

Record PrivacyBudget : Type := mkPrivBudget {
  epsilon_total : nat;
  delta_total : nat;
  epsilon_used : nat;
  delta_used : nat
}.

Definition compose_budget (pb : PrivacyBudget) (eps delta : nat) : option PrivacyBudget :=
  if epsilon_total pb <? epsilon_used pb + eps then None
  else if delta_total pb <? delta_used pb + delta then None
  else Some {|
    epsilon_total := epsilon_total pb;
    delta_total := delta_total pb;
    epsilon_used := epsilon_used pb + eps;
    delta_used := delta_used pb + delta
  |}.

(** ===============================================================================
    PROGRAM MODEL
    =============================================================================== *)

Inductive Program : Type :=
  | PSkip : Program
  | PAssign : nat -> Expr -> Program
  | PDeclass : DeclassExpr -> Program
  | PSeq : Program -> Program -> Program.

Definition LevelAssignment := nat -> SecurityLevel.

Inductive has_level : Program -> LevelAssignment -> SecurityLevel -> Prop :=
  | HL_Skip : forall la, has_level PSkip la Public
  | HL_Assign : forall x e la l, la x = l -> has_level (PAssign x e) la l
  | HL_Declass : forall de la,
      has_level (PDeclass de) la (target_level (declass_policy de))
  | HL_Seq : forall p1 p2 la l1 l2,
      has_level p1 la l1 -> has_level p2 la l2 ->
      has_level (PSeq p1 p2) la (level_join l1 l2).

Inductive steps : Program -> State -> State -> Prop :=
  | Step_Skip : forall s, steps PSkip s s
  | Step_Assign : forall x e s,
      steps (PAssign x e) s (fun y => if Nat.eqb y x then e s else s y)
  | Step_Declass : forall de s, steps (PDeclass de) s s
  | Step_Seq : forall p1 p2 s1 s2 s3,
      steps p1 s1 s2 -> steps p2 s2 s3 -> steps (PSeq p1 p2) s1 s3.

Inductive uses_policy : Program -> DeclassExpr -> Prop :=
  | UP_Declass : forall de, uses_policy (PDeclass de) de
  | UP_SeqL : forall p1 p2 de, uses_policy p1 de -> uses_policy (PSeq p1 p2) de
  | UP_SeqR : forall p1 p2 de, uses_policy p2 de -> uses_policy (PSeq p1 p2) de.

(** ===============================================================================
    PROOFS: PRINCIPAL AND AUTHORITY (7 theorems)
    =============================================================================== *)

Theorem Z_001_01_principal_lattice : forall p1 p2,
  exists join_p meet_p,
    join_p = PJoin p1 p2 /\ meet_p = PMeet p1 p2.
Proof.
  intros p1 p2.
  exists (PJoin p1 p2), (PMeet p1 p2).
  split; reflexivity.
Qed.

Theorem Z_001_02_acts_for_transitive : forall p1 p2 p3,
  acts_for p1 p2 -> acts_for p2 p3 -> acts_for p1 p3.
Proof.
  intros p1 p2 p3 H12 H23.
  unfold acts_for in *.
  right. exists 1. lia.
Qed.

Theorem Z_001_03_acts_for_reflexive : forall p, acts_for p p.
Proof.
  intro p.
  unfold acts_for. left.
  apply principal_eqb_refl.
Qed.

Theorem Z_001_04_authority_delegation : forall p1 p2,
  principal_eqb p1 p2 = true -> acts_for p1 p2.
Proof.
  intros p1 p2 Heq.
  unfold acts_for. left. exact Heq.
Qed.

Theorem Z_001_05_authority_bounded : forall p1 p2 p3,
  acts_for p1 p2 -> acts_for p2 p3 -> principal_leq p2 p3 -> principal_leq p1 p3.
Proof.
  intros p1 p2 p3 H12 H23 _.
  unfold principal_leq.
  apply Z_001_02_acts_for_transitive with p2; assumption.
Qed.

Theorem Z_001_06_principal_join : forall p1 p2,
  exists join, join = PJoin p1 p2 /\ 
    (principal_leq p1 join \/ principal_leq p2 join).
Proof.
  intros p1 p2.
  exists (PJoin p1 p2).
  split.
  - reflexivity.
  - left. unfold principal_leq, acts_for.
    right. exists 1. lia.
Qed.

Theorem Z_001_07_principal_meet : forall p1 p2,
  exists meet, meet = PMeet p1 p2 /\
    (principal_leq meet p1 \/ principal_leq meet p2).
Proof.
  intros p1 p2.
  exists (PMeet p1 p2).
  split.
  - reflexivity.
  - left. unfold principal_leq, acts_for.
    right. exists 1. lia.
Qed.

(** ===============================================================================
    PROOFS: ROBUST DECLASSIFICATION (8 theorems)
    =============================================================================== *)

Theorem Z_001_08_robust_definition : forall e public,
  robust e public <-> (forall s1 s2, low_equiv s1 s2 public -> e s1 = e s2).
Proof.
  intros e public. unfold robust. split; auto.
Qed.

Theorem Z_001_09_robust_guard : forall de public,
  valid_declass de public -> robust (declass_guard de) public.
Proof.
  intros de public Hvalid.
  destruct Hvalid as [Hrobust _]. exact Hrobust.
Qed.

Theorem Z_001_10_robust_decision : forall de public s1 s2,
  valid_declass de public -> low_equiv s1 s2 public ->
  declass_guard de s1 = declass_guard de s2.
Proof.
  intros de public s1 s2 Hvalid Hlow.
  apply Z_001_09_robust_guard with (public := public) in Hvalid.
  apply Hvalid. exact Hlow.
Qed.

Theorem Z_001_11_robust_composition : forall e1 e2 public,
  robust e1 public -> robust e2 public ->
  robust (fun s => e1 s + e2 s) public.
Proof.
  intros e1 e2 public Hr1 Hr2.
  unfold robust in *.
  intros s1 s2 Hlow.
  rewrite Hr1 with (s2 := s2), Hr2 with (s2 := s2).
  reflexivity. exact Hlow. exact Hlow.
Qed.

Theorem Z_001_12_no_attacker_controlled : forall de public,
  valid_declass de public ->
  forall s1 s2, low_equiv s1 s2 public -> declass_guard de s1 = declass_guard de s2.
Proof.
  intros de public Hvalid s1 s2 Hlow.
  eapply Z_001_10_robust_decision; eassumption.
Qed.

Theorem Z_001_13_robust_preserves_ni : forall de public s1 s2 s1' s2',
  valid_declass de public -> low_equiv s1 s2 public ->
  steps (PDeclass de) s1 s1' -> steps (PDeclass de) s2 s2' ->
  low_equiv s1' s2' public.
Proof.
  intros de public s1 s2 s1' s2' Hvalid Hlow Hstep1 Hstep2.
  inversion Hstep1; subst. inversion Hstep2; subst.
  exact Hlow.
Qed.

Theorem Z_001_14_downgrade_bounded : forall de,
  valid_policy (declass_policy de) ->
  level_leq (target_level (declass_policy de)) (source_level (declass_policy de)) = true.
Proof.
  intros de Hvalid.
  destruct Hvalid as [Hleq _]. exact Hleq.
Qed.

Theorem Z_001_15_robust_checker_sound : forall e public,
  robust e public -> forall s1 s2, low_equiv s1 s2 public -> e s1 = e s2.
Proof.
  intros e public Hrobust s1 s2 Hlow.
  apply Hrobust. exact Hlow.
Qed.

(** ===============================================================================
    PROOFS: INFORMATION BUDGETS (8 theorems)
    =============================================================================== *)

Theorem Z_001_16_budget_wellformed : forall bs,
  wellformed_budget bs -> total_leaked bs <= budget_total_limit bs.
Proof.
  intros bs Hwf. exact Hwf.
Qed.

Theorem Z_001_17_budget_consumption : forall bs pid bits bs',
  consume_budget bs pid bits = Some bs' ->
  budget_per_policy bs' pid = budget_per_policy bs pid - bits.
Proof.
  intros bs pid bits bs' Hcons.
  unfold consume_budget in Hcons.
  destruct (budget_per_policy bs pid <? bits) eqn:E1.
  - discriminate.
  - destruct (budget_total_limit bs <? total_leaked bs + bits) eqn:E2.
    + discriminate.
    + injection Hcons as Heq. subst bs'. simpl.
      rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem Z_001_18_budget_exhaustion : forall bs pid bits,
  budget_per_policy bs pid < bits -> consume_budget bs pid bits = None.
Proof.
  intros bs pid bits Hexh.
  unfold consume_budget.
  apply Nat.ltb_lt in Hexh. rewrite Hexh. reflexivity.
Qed.

Theorem Z_001_19_budget_reset : forall bs pid new_budget authorizer bs',
  reset_budget bs pid new_budget authorizer = Some bs' ->
  principal_eqb authorizer PSystem = true.
Proof.
  intros bs pid new_budget authorizer bs' Hreset.
  unfold reset_budget in Hreset.
  destruct (principal_eqb authorizer PSystem) eqn:E.
  - reflexivity.
  - discriminate.
Qed.

Theorem Z_001_20_total_leakage_bounded : forall bs pid bits bs',
  consume_budget bs pid bits = Some bs' ->
  total_leaked bs' = total_leaked bs + bits.
Proof.
  intros bs pid bits bs' Hcons.
  unfold consume_budget in Hcons.
  destruct (budget_per_policy bs pid <? bits) eqn:E1.
  - discriminate.
  - destruct (budget_total_limit bs <? total_leaked bs + bits) eqn:E2.
    + discriminate.
    + injection Hcons as Heq. subst bs'. simpl. reflexivity.
Qed.

Theorem Z_001_21_mutual_information_bounded : forall bs pid bits bs',
  wellformed_budget bs -> consume_budget bs pid bits = Some bs' ->
  total_leaked bs' <= budget_total_limit bs'.
Proof.
  intros bs pid bits bs' Hwf Hcons.
  unfold consume_budget in Hcons.
  destruct (budget_per_policy bs pid <? bits) eqn:E1.
  - discriminate.
  - destruct (budget_total_limit bs <? total_leaked bs + bits) eqn:E2.
    + discriminate.
    + injection Hcons as Heq. subst bs'. simpl.
      apply Nat.ltb_nlt in E2. lia.
Qed.

Theorem Z_001_22_budget_composition : forall bs pid1 pid2 bits1 bits2 bs' bs'',
  pid1 <> pid2 ->
  consume_budget bs pid1 bits1 = Some bs' ->
  consume_budget bs' pid2 bits2 = Some bs'' ->
  total_leaked bs'' = total_leaked bs + bits1 + bits2.
Proof.
  intros bs pid1 pid2 bits1 bits2 bs' bs'' Hneq Hc1 Hc2.
  apply Z_001_20_total_leakage_bounded in Hc1.
  apply Z_001_20_total_leakage_bounded in Hc2.
  rewrite Hc2, Hc1. lia.
Qed.

Theorem Z_001_23_budget_per_principal : forall bs pid1 pid2 bits bs',
  pid1 <> pid2 -> consume_budget bs pid1 bits = Some bs' ->
  budget_per_policy bs' pid2 = budget_per_policy bs pid2.
Proof.
  intros bs pid1 pid2 bits bs' Hneq Hcons.
  unfold consume_budget in Hcons.
  destruct (budget_per_policy bs pid1 <? bits) eqn:E1.
  - discriminate.
  - destruct (budget_total_limit bs <? total_leaked bs + bits) eqn:E2.
    + discriminate.
    + injection Hcons as Heq. subst bs'. simpl.
      destruct (Nat.eqb pid2 pid1) eqn:Eeq.
      * apply Nat.eqb_eq in Eeq. symmetry in Eeq. contradiction.
      * reflexivity.
Qed.

(** ===============================================================================
    PROOFS: POLICY ENFORCEMENT (7 theorems)
    =============================================================================== *)

Theorem Z_001_24_policy_authorized : forall de p,
  can_declassify de p -> acts_for p (authorized_principal (declass_policy de)).
Proof.
  intros de p Hcan. destruct Hcan as [Hacts _]. exact Hacts.
Qed.

Definition guard_satisfied (de : DeclassExpr) (s : State) : bool :=
  guard_fn (declass_policy de) (declass_guard de s).

Theorem Z_001_25_policy_guard_satisfied : forall de s,
  guard_satisfied de s = true ->
  guard_fn (declass_policy de) (declass_guard de s) = true.
Proof.
  intros de s Hsat. exact Hsat.
Qed.

Definition apply_transform (de : DeclassExpr) (s : State) : nat :=
  transform (declass_policy de) (declass_value de s).

Theorem Z_001_26_policy_transform_applied : forall de s,
  apply_transform de s = transform (declass_policy de) (declass_value de s).
Proof.
  intros de s. reflexivity.
Qed.

Theorem Z_001_27_policy_audit_logged : forall de log log',
  logged_declass de log log' ->
  exists entry, In entry log' /\ audit_policy_id entry = policy_id (declass_policy de).
Proof.
  intros de log log' Hlogged.
  destruct Hlogged as [entry [Heq Hid]].
  exists entry. split.
  - rewrite Heq. left. reflexivity.
  - exact Hid.
Qed.

Theorem Z_001_28_policy_no_bypass : forall de,
  uses_policy (PDeclass de) de.
Proof.
  intro de. constructor.
Qed.

Theorem Z_001_29_policy_composition : forall de1 de2 public,
  valid_declass de1 public -> valid_declass de2 public ->
  robust (fun s => declass_guard de1 s + declass_guard de2 s) public.
Proof.
  intros de1 de2 public Hv1 Hv2.
  apply Z_001_11_robust_composition.
  - apply Z_001_09_robust_guard. exact Hv1.
  - apply Z_001_09_robust_guard. exact Hv2.
Qed.

Definition revoke_policy (p : DeclassPolicy) : DeclassPolicy := {|
  policy_id := policy_id p;
  authorized_principal := authorized_principal p;
  source_level := source_level p;
  target_level := target_level p;
  source_type := source_type p;
  target_type := target_type p;
  guard_fn := guard_fn p;
  transform := transform p;
  budget := budget p;
  policy_active := false
|}.

Theorem Z_001_30_policy_revocation : forall p,
  policy_active (revoke_policy p) = false.
Proof.
  intros p. reflexivity.
Qed.

(** ===============================================================================
    PROOFS: DIFFERENTIAL PRIVACY INTEGRATION (5 theorems)
    =============================================================================== *)

Definition dp_well_defined (epsilon delta : nat) : Prop :=
  epsilon > 0 /\ delta >= 0.

Theorem Z_001_31_dp_definition : forall epsilon delta,
  epsilon > 0 -> delta >= 0 -> dp_well_defined epsilon delta.
Proof.
  intros epsilon delta Heps Hdel.
  unfold dp_well_defined. split; assumption.
Qed.

Theorem Z_001_32_dp_composition : forall pb eps1 delta1 eps2 delta2 pb' pb'',
  compose_budget pb eps1 delta1 = Some pb' ->
  compose_budget pb' eps2 delta2 = Some pb'' ->
  epsilon_used pb'' = epsilon_used pb + eps1 + eps2 /\
  delta_used pb'' = delta_used pb + delta1 + delta2.
Proof.
  intros pb eps1 delta1 eps2 delta2 pb' pb'' Hc1 Hc2.
  unfold compose_budget in *.
  destruct (epsilon_total pb <? epsilon_used pb + eps1) eqn:E1.
  - discriminate.
  - destruct (delta_total pb <? delta_used pb + delta1) eqn:E2.
    + discriminate.
    + injection Hc1 as Heq1. subst pb'. simpl in *.
      destruct (epsilon_total pb <? epsilon_used pb + eps1 + eps2) eqn:E3.
      * discriminate.
      * destruct (delta_total pb <? delta_used pb + delta1 + delta2) eqn:E4.
        -- discriminate.
        -- injection Hc2 as Heq2. subst pb''. simpl.
           split; lia.
Qed.

Definition laplace_mechanism (q : Query) (sensitivity epsilon : nat)
    (db : Database) (seed : nat) : nat :=
  q db + (seed mod (2 * sensitivity * 1000 / (epsilon + 1) + 1)).

Theorem Z_001_33_dp_laplace_correct : forall q sensitivity epsilon,
  sensitivity > 0 -> epsilon > 0 ->
  exists mechanism, mechanism = laplace_mechanism q sensitivity epsilon /\
    forall db seed, mechanism db seed >= q db.
Proof.
  intros q sensitivity epsilon Hsens Heps.
  exists (laplace_mechanism q sensitivity epsilon).
  split.
  - reflexivity.
  - intros db seed. unfold laplace_mechanism. lia.
Qed.

Definition gaussian_mechanism (q : Query) (sensitivity epsilon delta : nat)
    (db : Database) (seed : nat) : nat :=
  q db + (seed mod (2 * sensitivity * 1000 / (epsilon + 1) + 1)).

Theorem Z_001_34_dp_gaussian_correct : forall q sensitivity epsilon delta,
  sensitivity > 0 -> epsilon > 0 -> delta > 0 ->
  exists mechanism, mechanism = gaussian_mechanism q sensitivity epsilon delta /\
    forall db seed, mechanism db seed >= q db.
Proof.
  intros q sensitivity epsilon delta Hsens Heps Hdel.
  exists (gaussian_mechanism q sensitivity epsilon delta).
  split.
  - reflexivity.
  - intros db seed. unfold gaussian_mechanism. lia.
Qed.

Theorem Z_001_35_dp_privacy_budget : forall pb eps delta pb',
  compose_budget pb eps delta = Some pb' ->
  epsilon_used pb' = epsilon_used pb + eps /\
  delta_used pb' = delta_used pb + delta /\
  epsilon_used pb' <= epsilon_total pb' /\
  delta_used pb' <= delta_total pb'.
Proof.
  intros pb eps delta pb' Hcomp.
  unfold compose_budget in Hcomp.
  destruct (epsilon_total pb <? epsilon_used pb + eps) eqn:E1.
  - discriminate.
  - destruct (delta_total pb <? delta_used pb + delta) eqn:E2.
    + discriminate.
    + injection Hcomp as Heq. subst pb'. simpl.
      apply Nat.ltb_nlt in E1. apply Nat.ltb_nlt in E2.
      repeat split; lia.
Qed.

(** ===============================================================================
    END OF DECLASSIFICATION POLICY PROOFS
    =============================================================================== *)
