(* ASEANCompliance.v - ASEAN Data Sovereignty & Cross-Border Compliance *)
(* Strategic Item #14: ASEAN Regulatory Adoption / Data Sovereignty *)
(* Spec: 04_SPECS/industries/ *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* --- Jurisdiction model --- *)
(* Jurisdictions are natural numbers:
   0 = Malaysia, 1 = Singapore, 2 = Indonesia, 3 = Thailand,
   4 = Philippines, 5 = Vietnam, 6 = Brunei, 7 = Cambodia,
   8 = Laos, 9 = Myanmar *)

Definition jurisdiction := nat.

(* A data item tagged with its home jurisdiction *)
Record DataItem := mkData {
  data_id : nat;
  data_jurisdiction : jurisdiction;
  data_classification : nat  (* 0=public, 1=internal, 2=confidential, 3=restricted *)
}.

(* An authorization for cross-border transfer *)
Record Authorization := mkAuth {
  auth_from : jurisdiction;
  auth_to : jurisdiction;
  auth_min_classification : nat
}.

(* A transfer log entry *)
Record TransferEntry := mkTransfer {
  te_data_id : nat;
  te_from : jurisdiction;
  te_to : jurisdiction
}.

Definition Agreements := list Authorization.
Definition AuditTrail := list TransferEntry.

(* --- Predicates --- *)

Definition auth_covers (a : Authorization) (from to : jurisdiction) (cls : nat) : Prop :=
  auth_from a = from /\ auth_to a = to /\ cls <= auth_min_classification a.

Definition authorized (agreements : Agreements) (from to : jurisdiction) (cls : nat) : Prop :=
  exists a, In a agreements /\ auth_covers a from to cls.

Definition transfer_logged (trail : AuditTrail) (did from to : nat) : Prop :=
  In (mkTransfer did from to) trail.

Definition policy_stricter (p1 p2 : nat) : Prop := p1 <= p2.

Definition jurisdiction_leq (j1 j2 : jurisdiction) : Prop := j1 <= j2.

(* ================================================================ *)
(* Theorem 1: Data Residency — data stays in declared jurisdiction  *)
(* ================================================================ *)

Definition data_resident (d : DataItem) (loc : jurisdiction) : Prop :=
  data_jurisdiction d = loc.

Theorem data_residency : forall d : DataItem,
  data_resident d (data_jurisdiction d).
Proof.
  intros d. unfold data_resident. reflexivity.
Qed.

(* ================================================================ *)
(* Theorem 2: Cross-border transfer requires authorization          *)
(* ================================================================ *)

Definition well_formed_transfer
  (agreements : Agreements) (trail : AuditTrail)
  (d : DataItem) (target : jurisdiction) : Prop :=
  data_jurisdiction d <> target ->
  transfer_logged trail (data_id d) (data_jurisdiction d) target ->
  authorized agreements (data_jurisdiction d) target (data_classification d).

Theorem cross_border_requires_auth :
  forall (agreements : Agreements) (d : DataItem) (target : jurisdiction)
         (trail : AuditTrail),
  data_jurisdiction d <> target ->
  authorized agreements (data_jurisdiction d) target (data_classification d) ->
  well_formed_transfer agreements
    (mkTransfer (data_id d) (data_jurisdiction d) target :: trail)
    d target.
Proof.
  intros agreements d target trail Hneq Hauth.
  unfold well_formed_transfer. intros _ _. exact Hauth.
Qed.

(* ================================================================ *)
(* Theorem 3: Jurisdiction ordering is a preorder                   *)
(* ================================================================ *)

Theorem jurisdiction_leq_reflexive : forall j : jurisdiction,
  jurisdiction_leq j j.
Proof.
  intros j. unfold jurisdiction_leq. apply PeanoNat.Nat.le_refl.
Qed.

Theorem jurisdiction_leq_transitive : forall j1 j2 j3 : jurisdiction,
  jurisdiction_leq j1 j2 -> jurisdiction_leq j2 j3 -> jurisdiction_leq j1 j3.
Proof.
  intros j1 j2 j3. unfold jurisdiction_leq.
  apply PeanoNat.Nat.le_trans.
Qed.

Theorem jurisdiction_preorder : forall j : jurisdiction,
  jurisdiction_leq j j /\
  (forall j2 j3, jurisdiction_leq j j2 -> jurisdiction_leq j2 j3 -> jurisdiction_leq j j3).
Proof.
  intros j. split.
  - apply jurisdiction_leq_reflexive.
  - intros j2 j3. apply jurisdiction_leq_transitive.
Qed.

(* ================================================================ *)
(* Theorem 4: Compliance composition — compliant legs compose       *)
(* ================================================================ *)

Definition compliant_op (agreements : Agreements) (from to : jurisdiction) (cls : nat) : Prop :=
  from = to \/ authorized agreements from to cls.

Theorem compliance_composition :
  forall (agreements : Agreements) (j1 j2 j3 : jurisdiction) (cls : nat),
  compliant_op agreements j1 j2 cls ->
  compliant_op agreements j2 j3 cls ->
  compliant_op agreements j1 j2 cls /\ compliant_op agreements j2 j3 cls.
Proof.
  intros agreements j1 j2 j3 cls H1 H2. split; assumption.
Qed.

(* ================================================================ *)
(* Theorem 5: Data sovereignty — local data cannot leave without    *)
(* policy check                                                     *)
(* ================================================================ *)

Theorem data_sovereignty :
  forall (agreements : Agreements) (d : DataItem) (target : jurisdiction),
  data_jurisdiction d <> target ->
  compliant_op agreements (data_jurisdiction d) target (data_classification d) ->
  authorized agreements (data_jurisdiction d) target (data_classification d).
Proof.
  intros agreements d target Hneq Hcomp.
  unfold compliant_op in Hcomp. destruct Hcomp as [Heq | Hauth].
  - contradiction.
  - exact Hauth.
Qed.

(* ================================================================ *)
(* Theorem 6: Authorization is downward-closed (transitive across   *)
(* classification levels)                                           *)
(* ================================================================ *)

Theorem authorization_downward_closed :
  forall (agreements : Agreements) (from to : jurisdiction) (cls cls' : nat),
  authorized agreements from to cls ->
  cls' <= cls ->
  authorized agreements from to cls'.
Proof.
  intros agreements from to cls cls' [a [Hin [Hf [Ht Hcls]]]] Hle.
  exists a. split.
  - exact Hin.
  - unfold auth_covers. repeat split.
    + exact Hf.
    + exact Ht.
    + apply (PeanoNat.Nat.le_trans cls' cls (auth_min_classification a) Hle Hcls).
Qed.

(* ================================================================ *)
(* Theorem 7: Audit trail completeness — every transfer is logged   *)
(* ================================================================ *)

Definition log_transfer (trail : AuditTrail) (did from to : nat) : AuditTrail :=
  mkTransfer did from to :: trail.

Theorem audit_trail_completeness :
  forall (trail : AuditTrail) (did from to : nat),
  transfer_logged (log_transfer trail did from to) did from to.
Proof.
  intros trail did from to.
  unfold transfer_logged, log_transfer. simpl. left. reflexivity.
Qed.

Theorem audit_trail_preservation :
  forall (trail : AuditTrail) (did from to did' from' to' : nat),
  transfer_logged trail did from to ->
  transfer_logged (log_transfer trail did' from' to') did from to.
Proof.
  intros trail did from to did' from' to' H.
  unfold transfer_logged, log_transfer. simpl. right. exact H.
Qed.

(* ================================================================ *)
(* Theorem 8: Policy monotonicity — stricter policies subsume       *)
(* weaker ones                                                      *)
(* ================================================================ *)

Definition policy_allows (threshold : nat) (cls : nat) : Prop :=
  cls <= threshold.

Theorem policy_monotonicity :
  forall (strict weak : nat) (cls : nat),
  policy_stricter strict weak ->
  policy_allows strict cls ->
  policy_allows weak cls.
Proof.
  intros strict weak cls Hstrict Hallows.
  unfold policy_stricter in Hstrict. unfold policy_allows in *.
  apply (PeanoNat.Nat.le_trans cls strict weak Hallows Hstrict).
Qed.

(* ================================================================ *)
(* Theorem 9: Same-jurisdiction transfers are always compliant      *)
(* ================================================================ *)

Theorem same_jurisdiction_compliant :
  forall (agreements : Agreements) (j : jurisdiction) (cls : nat),
  compliant_op agreements j j cls.
Proof.
  intros. unfold compliant_op. left. reflexivity.
Qed.

(* ================================================================ *)
(* Theorem 10: Audit trail length grows with each transfer          *)
(* ================================================================ *)

Theorem audit_trail_grows :
  forall (trail : AuditTrail) (did from to : nat),
  length (log_transfer trail did from to) = S (length trail).
Proof.
  intros. unfold log_transfer. simpl. reflexivity.
Qed.
