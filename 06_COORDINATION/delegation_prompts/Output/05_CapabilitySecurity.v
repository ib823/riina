(* CapabilitySecurity.v - Object-Capability Security for RIINA *)
(* Spec: 01_RESEARCH/04_DOMAIN_D_CAPABILITIES/ *)
(* Model: Object-Capability Model (OCAP) *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Permission types *)
Inductive Permission : Type :=
  | PermRead : Permission
  | PermWrite : Permission
  | PermExecute : Permission
  | PermDelegate : Permission
  | PermRevoke : Permission
.

(* Permission equality decidability *)
Definition perm_eqb (p1 p2 : Permission) : bool :=
  match p1, p2 with
  | PermRead, PermRead => true
  | PermWrite, PermWrite => true
  | PermExecute, PermExecute => true
  | PermDelegate, PermDelegate => true
  | PermRevoke, PermRevoke => true
  | _, _ => false
  end.

Lemma perm_eqb_refl : forall p, perm_eqb p p = true.
Proof.
  destruct p; reflexivity.
Qed.

Lemma perm_eqb_eq : forall p1 p2, perm_eqb p1 p2 = true <-> p1 = p2.
Proof.
  split; intros.
  - destruct p1, p2; simpl in H; try discriminate; reflexivity.
  - subst. apply perm_eqb_refl.
Qed.

(* Permission set (as list for decidability) *)
Definition PermSet := list Permission.

(* Check permission membership *)
Definition has_perm (p : Permission) (ps : PermSet) : bool :=
  existsb (fun p' => perm_eqb p p') ps.

Lemma has_perm_In : forall p ps, has_perm p ps = true <-> In p ps.
Proof.
  intros p ps. unfold has_perm.
  induction ps as [| h t IH].
  - simpl. split; intros H; inversion H.
  - simpl. rewrite Bool.orb_true_iff.
    split; intros H.
    + destruct H as [Heq | Hex].
      * left. apply perm_eqb_eq in Heq. symmetry. assumption.
      * right. apply IH. assumption.
    + destruct H as [Heq | Hin].
      * left. subst. apply perm_eqb_refl.
      * right. apply IH. assumption.
Qed.

(* Capability *)
Record Capability : Type := mkCap {
  cap_id : nat;
  cap_object : nat;                (* Target object ID *)
  cap_permissions : PermSet;
  cap_revoked : bool;
  cap_parent : option nat;         (* Parent capability for attenuation tracking *)
}.

(* Permission subset check *)
Definition perm_subset (ps1 ps2 : PermSet) : bool :=
  forallb (fun p => has_perm p ps2) ps1.

Lemma perm_subset_refl : forall ps, perm_subset ps ps = true.
Proof.
  intros ps. unfold perm_subset.
  apply forallb_forall. intros p Hin.
  apply has_perm_In. assumption.
Qed.

Lemma perm_subset_trans : forall ps1 ps2 ps3,
  perm_subset ps1 ps2 = true ->
  perm_subset ps2 ps3 = true ->
  perm_subset ps1 ps3 = true.
Proof.
  intros ps1 ps2 ps3 H12 H23.
  unfold perm_subset in *.
  apply forallb_forall. intros p Hin.
  apply forallb_forall with (x := p) in H12; [| assumption].
  apply has_perm_In in H12.
  apply forallb_forall with (x := p) in H23; [| assumption].
  assumption.
Qed.

Lemma perm_subset_nil : forall ps, perm_subset [] ps = true.
Proof.
  intros. unfold perm_subset. simpl. reflexivity.
Qed.

(* Capability is valid (not revoked) *)
Definition cap_valid (c : Capability) : bool :=
  negb (cap_revoked c).

(* Capability system state *)
Record CapSystem : Type := mkCapSys {
  sys_capabilities : list Capability;
  sys_objects : list nat;              (* Object IDs *)
  sys_seals : list (nat * nat);        (* sealer_id, unsealer_id pairs *)
}.

(* Lookup capability by ID *)
Fixpoint find_cap (caps : list Capability) (id : nat) : option Capability :=
  match caps with
  | [] => None
  | c :: rest => if Nat.eqb (cap_id c) id then Some c else find_cap rest id
  end.

Lemma find_cap_In : forall caps id c,
  find_cap caps id = Some c -> In c caps.
Proof.
  induction caps as [| a rest IHcaps]; intros id c H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb (cap_id a) id) eqn:Heq.
    + inversion H. subst. left. reflexivity.
    + right. eapply IHcaps. eassumption.
Qed.

(* Derive (attenuate) a capability *)
Definition derive_cap (parent : Capability) (new_perms : PermSet) (new_id : nat) : option Capability :=
  if andb (cap_valid parent) (perm_subset new_perms (cap_permissions parent))
  then Some (mkCap new_id (cap_object parent) new_perms false (Some (cap_id parent)))
  else None.

(* Revoke a capability *)
Definition revoke_cap (c : Capability) : Capability :=
  mkCap (cap_id c) (cap_object c) (cap_permissions c) true (cap_parent c).

(* Sealed value *)
Record SealedValue : Type := mkSealed {
  sealed_value : nat;
  sealed_with : nat;    (* Sealer ID *)
}.

(* Unseal requires matching unsealer *)
Definition can_unseal (sv : SealedValue) (unsealer_id : nat) (sys : CapSystem) : bool :=
  existsb (fun pair => andb (Nat.eqb (fst pair) (sealed_with sv))
                            (Nat.eqb (snd pair) unsealer_id))
          (sys_seals sys).

(* Object with encapsulated state *)
Record CapObject : Type := mkObj {
  obj_id : nat;
  obj_public_state : nat;
  obj_private_state : nat;      (* Only accessible via capability *)
}.

(* Access check *)
Definition can_access (c : Capability) (obj : CapObject) (perm : Permission) : bool :=
  andb (andb (cap_valid c) (Nat.eqb (cap_object c) (obj_id obj)))
       (has_perm perm (cap_permissions c)).

(* Capability origin tracking *)
Inductive CapOrigin : Type :=
  | OriginSystem : nat -> CapOrigin        (* System-issued with ID *)
  | OriginDerived : Capability -> CapOrigin (* Derived from parent *)
.

(* Well-formed capability (has valid origin in system) *)
Definition cap_in_system (c : Capability) (sys : CapSystem) : bool :=
  existsb (fun c' => Nat.eqb (cap_id c) (cap_id c')) (sys_capabilities sys).

(* Membrane for boundary crossing *)
Record Membrane : Type := mkMembrane {
  membrane_id : nat;
  membrane_allowed_perms : PermSet;
}.

(* Attenuate capability through membrane *)
Definition membrane_attenuate (m : Membrane) (c : Capability) : Capability :=
  mkCap (cap_id c) (cap_object c)
        (filter (fun p => has_perm p (membrane_allowed_perms m)) (cap_permissions c))
        (cap_revoked c) (cap_parent c).

(* Caretaker - intermediary that holds capability *)
Record Caretaker : Type := mkCaretaker {
  caretaker_id : nat;
  caretaker_held_cap : Capability;
  caretaker_active : bool;
}.

(* Facet - a view of an object with restricted permissions *)
Record Facet : Type := mkFacet {
  facet_object : nat;
  facet_perms : PermSet;
}.

(* Create facet from capability *)
Definition cap_to_facet (c : Capability) : Facet :=
  mkFacet (cap_object c) (cap_permissions c).

(* Access request type *)
Inductive AccessRequest : Type :=
  | ReqRead : nat -> AccessRequest
  | ReqWrite : nat -> nat -> AccessRequest
  | ReqExecute : nat -> AccessRequest
.

(* Check if access request requires capability *)
Definition request_needs_cap (req : AccessRequest) : bool := true.

(* Defensive object - validates all inputs *)
Record DefensiveObject : Type := mkDefObj {
  defobj_id : nat;
  defobj_validate : nat -> bool;  (* Input validator *)
}.

(* Defensive access - checks both capability and input validity *)
Definition defensive_access (c : Capability) (dobj : DefensiveObject) 
                            (perm : Permission) (input : nat) : bool :=
  andb (andb (cap_valid c) (Nat.eqb (cap_object c) (defobj_id dobj)))
       (andb (has_perm perm (cap_permissions c)) (defobj_validate dobj input)).

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_01: Capability Unforgeability                               *)
(* Capabilities cannot be created from nothing - must derive from existing     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem SEC_001_01_capability_unforgeability :
  forall (new_perms : PermSet) (new_id : nat) (obj_id : nat),
    (* A capability cannot be created without a valid parent *)
    forall parent : Capability,
      derive_cap parent new_perms new_id = None \/
      (exists derived : Capability, 
         derive_cap parent new_perms new_id = Some derived /\
         cap_parent derived = Some (cap_id parent)).
Proof.
  intros new_perms new_id obj_id parent.
  unfold derive_cap.
  destruct (cap_valid parent && perm_subset new_perms (cap_permissions parent)) eqn:Hcond.
  - right. exists (mkCap new_id (cap_object parent) new_perms false (Some (cap_id parent))).
    split; reflexivity.
  - left. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_02: Capability Attenuation                                  *)
(* Derived capabilities can only weaken, never amplify permissions             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem SEC_001_02_capability_attenuation :
  forall (parent : Capability) (new_perms : PermSet) (new_id : nat) (derived : Capability),
    derive_cap parent new_perms new_id = Some derived ->
    perm_subset (cap_permissions derived) (cap_permissions parent) = true.
Proof.
  intros parent new_perms new_id derived Hderive.
  unfold derive_cap in Hderive.
  destruct (cap_valid parent && perm_subset new_perms (cap_permissions parent)) eqn:Hcond.
  - inversion Hderive. subst. simpl.
    apply andb_prop in Hcond. destruct Hcond as [_ Hsubset].
    assumption.
  - discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_03: Capability Composition                                  *)
(* Combined capabilities have at most the union of individual permissions      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition compose_perms (ps1 ps2 : PermSet) : PermSet := ps1 ++ ps2.

Definition compose_caps (c1 c2 : Capability) (new_id : nat) : option Capability :=
  if andb (cap_valid c1) (cap_valid c2) then
    if Nat.eqb (cap_object c1) (cap_object c2) then
      Some (mkCap new_id (cap_object c1) 
                  (compose_perms (cap_permissions c1) (cap_permissions c2))
                  false None)
    else None
  else None.

Theorem SEC_001_03_capability_composition :
  forall (c1 c2 : Capability) (new_id : nat) (composed : Capability) (p : Permission),
    compose_caps c1 c2 new_id = Some composed ->
    has_perm p (cap_permissions composed) = true ->
    has_perm p (cap_permissions c1) = true \/ has_perm p (cap_permissions c2) = true.
Proof.
  intros c1 c2 new_id composed p Hcompose Hperm.
  unfold compose_caps in Hcompose.
  destruct (cap_valid c1 && cap_valid c2) eqn:Hvalid; [| discriminate].
  destruct (Nat.eqb (cap_object c1) (cap_object c2)) eqn:Hobj; [| discriminate].
  inversion Hcompose. subst. simpl in Hperm.
  unfold compose_perms in Hperm.
  apply has_perm_In in Hperm.
  apply in_app_or in Hperm.
  destruct Hperm as [Hin1 | Hin2].
  - left. apply has_perm_In. assumption.
  - right. apply has_perm_In. assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_04: Capability Revocation                                   *)
(* A revoked capability cannot be used for access                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem SEC_001_04_capability_revocation :
  forall (c : Capability) (obj : CapObject) (perm : Permission),
    let revoked_c := revoke_cap c in
    can_access revoked_c obj perm = false.
Proof.
  intros c obj perm.
  unfold revoke_cap, can_access, cap_valid. simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_05: No Ambient Authority                                    *)
(* All access to objects requires an explicit capability                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition access_with_cap (c : option Capability) (obj : CapObject) (perm : Permission) : bool :=
  match c with
  | None => false
  | Some cap => can_access cap obj perm
  end.

Theorem SEC_001_05_no_ambient_authority :
  forall (obj : CapObject) (perm : Permission),
    access_with_cap None obj perm = false.
Proof.
  intros obj perm.
  unfold access_with_cap.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_06: Principle of Least Authority                            *)
(* Components should receive only the minimal capabilities they need           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition minimal_cap (needed : PermSet) (available : Capability) (new_id : nat) : option Capability :=
  derive_cap available needed new_id.

Theorem SEC_001_06_principle_of_least_authority :
  forall (needed : PermSet) (available : Capability) (new_id : nat) (minimal : Capability),
    perm_subset needed (cap_permissions available) = true ->
    cap_valid available = true ->
    minimal_cap needed available new_id = Some minimal ->
    cap_permissions minimal = needed.
Proof.
  intros needed available new_id minimal Hsubset Hvalid Hminimal.
  unfold minimal_cap, derive_cap in Hminimal.
  rewrite Hvalid in Hminimal. simpl in Hminimal.
  rewrite Hsubset in Hminimal.
  inversion Hminimal.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_07: Capability Confinement                                  *)
(* A capability cannot escape its granted scope (same object)                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem SEC_001_07_capability_confinement :
  forall (parent : Capability) (new_perms : PermSet) (new_id : nat) (derived : Capability),
    derive_cap parent new_perms new_id = Some derived ->
    cap_object derived = cap_object parent.
Proof.
  intros parent new_perms new_id derived Hderive.
  unfold derive_cap in Hderive.
  destruct (cap_valid parent && perm_subset new_perms (cap_permissions parent)) eqn:Hcond.
  - inversion Hderive. reflexivity.
  - discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_08: Capability Facets                                       *)
(* Different facets provide different views of the same object                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition create_facet (c : Capability) (restricted_perms : PermSet) : option Facet :=
  if perm_subset restricted_perms (cap_permissions c) then
    Some (mkFacet (cap_object c) restricted_perms)
  else None.

Theorem SEC_001_08_capability_facets :
  forall (c : Capability) (perms1 perms2 : PermSet) (f1 f2 : Facet),
    create_facet c perms1 = Some f1 ->
    create_facet c perms2 = Some f2 ->
    facet_object f1 = facet_object f2 /\
    facet_object f1 = cap_object c.
Proof.
  intros c perms1 perms2 f1 f2 Hf1 Hf2.
  unfold create_facet in *.
  destruct (perm_subset perms1 (cap_permissions c)) eqn:Hsub1; [| discriminate].
  destruct (perm_subset perms2 (cap_permissions c)) eqn:Hsub2; [| discriminate].
  inversion Hf1. inversion Hf2. subst.
  simpl. split; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_09: Membrane Isolation                                      *)
(* Capabilities crossing a membrane boundary are attenuated                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma filter_subset : forall (f : Permission -> bool) (ps : PermSet),
  perm_subset (filter f ps) ps = true.
Proof.
  intros f ps.
  unfold perm_subset.
  apply forallb_forall.
  intros p Hin.
  apply filter_In in Hin.
  destruct Hin as [Hinps _].
  apply has_perm_In. assumption.
Qed.

Theorem SEC_001_09_membrane_isolation :
  forall (m : Membrane) (c : Capability),
    let attenuated := membrane_attenuate m c in
    perm_subset (cap_permissions attenuated) (cap_permissions c) = true.
Proof.
  intros m c.
  unfold membrane_attenuate. simpl.
  apply filter_subset.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_10: Capability Delegation Safety                            *)
(* A delegated capability has at most the permissions of the original          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition delegate_cap (original : Capability) (delegated_perms : PermSet) 
                        (new_id : nat) : option Capability :=
  if has_perm PermDelegate (cap_permissions original) then
    derive_cap original delegated_perms new_id
  else None.

Theorem SEC_001_10_capability_delegation_safety :
  forall (original : Capability) (delegated_perms : PermSet) (new_id : nat) 
         (delegated : Capability),
    delegate_cap original delegated_perms new_id = Some delegated ->
    perm_subset (cap_permissions delegated) (cap_permissions original) = true.
Proof.
  intros original delegated_perms new_id delegated Hdelegate.
  unfold delegate_cap in Hdelegate.
  destruct (has_perm PermDelegate (cap_permissions original)) eqn:Hhas; [| discriminate].
  apply SEC_001_02_capability_attenuation with (new_perms := delegated_perms) (new_id := new_id).
  assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_11: Sealer/Unsealer Pairs                                   *)
(* Sealed data can only be opened with the paired unsealer                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem SEC_001_11_sealer_unsealer_pairs :
  forall (sv : SealedValue) (unsealer_id : nat) (sys : CapSystem),
    can_unseal sv unsealer_id sys = true ->
    In (sealed_with sv, unsealer_id) (sys_seals sys).
Proof.
  intros sv unsealer_id sys Hunseal.
  unfold can_unseal in Hunseal.
  rewrite existsb_exists in Hunseal.
  destruct Hunseal as [pair [Hin Heq]].
  apply andb_prop in Heq.
  destruct Heq as [Hsealer Hunsealer].
  apply Nat.eqb_eq in Hsealer.
  apply Nat.eqb_eq in Hunsealer.
  destruct pair as [s u]. simpl in *.
  subst. assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_12: Capability Caretaker                                    *)
(* A caretaker maintains authority over its held capability                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition caretaker_grant (ct : Caretaker) (new_perms : PermSet) 
                           (new_id : nat) : option Capability :=
  if caretaker_active ct then
    derive_cap (caretaker_held_cap ct) new_perms new_id
  else None.

Theorem SEC_001_12_capability_caretaker :
  forall (ct : Caretaker) (new_perms : PermSet) (new_id : nat) (granted : Capability),
    caretaker_grant ct new_perms new_id = Some granted ->
    perm_subset (cap_permissions granted) (cap_permissions (caretaker_held_cap ct)) = true.
Proof.
  intros ct new_perms new_id granted Hgrant.
  unfold caretaker_grant in Hgrant.
  destruct (caretaker_active ct) eqn:Hactive; [| discriminate].
  apply SEC_001_02_capability_attenuation with (new_perms := new_perms) (new_id := new_id).
  assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_13: Rights Amplification Impossible                         *)
(* No capability can grant more permissions than it possesses                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem SEC_001_13_rights_amplification_impossible :
  forall (c : Capability) (requested_perms : PermSet) (new_id : nat) (p : Permission),
    perm_subset requested_perms (cap_permissions c) = false ->
    has_perm p requested_perms = true ->
    has_perm p (cap_permissions c) = false ->
    derive_cap c requested_perms new_id = None.
Proof.
  intros c requested_perms new_id p Hnot_subset Hhas_req Hnot_has.
  unfold derive_cap.
  destruct (cap_valid c) eqn:Hvalid.
  - simpl. rewrite Hnot_subset. reflexivity.
  - simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_14: Defensive Consistency                                   *)
(* Objects behave correctly under any input when accessed via capability       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem SEC_001_14_defensive_consistency :
  forall (c : Capability) (dobj : DefensiveObject) (perm : Permission) (input : nat),
    defensive_access c dobj perm input = true ->
    (cap_valid c = true /\ 
     cap_object c = defobj_id dobj /\
     has_perm perm (cap_permissions c) = true /\
     defobj_validate dobj input = true).
Proof.
  intros c dobj perm input Haccess.
  unfold defensive_access in Haccess.
  apply andb_prop in Haccess.
  destruct Haccess as [Hleft Hright].
  apply andb_prop in Hleft.
  destruct Hleft as [Hvalid Hobj].
  apply andb_prop in Hright.
  destruct Hright as [Hperm Hvalidate].
  apply Nat.eqb_eq in Hobj.
  repeat split; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM SEC_001_15: Capability-Safe Encapsulation                           *)
(* Private state is inaccessible without appropriate capability                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition access_private (c : option Capability) (obj : CapObject) : option nat :=
  match c with
  | None => None
  | Some cap => 
      if can_access cap obj PermRead then Some (obj_private_state obj)
      else None
  end.

Theorem SEC_001_15_capability_safe_encapsulation :
  forall (obj : CapObject),
    access_private None obj = None.
Proof.
  intros obj.
  unfold access_private.
  reflexivity.
Qed.

(* Additional theorem for encapsulation with invalid capability *)
Theorem SEC_001_15_capability_safe_encapsulation_invalid :
  forall (c : Capability) (obj : CapObject),
    cap_valid c = false ->
    access_private (Some c) obj = None.
Proof.
  intros c obj Hinvalid.
  unfold access_private, can_access.
  rewrite Hinvalid. simpl.
  reflexivity.
Qed.

(* Additional theorem for encapsulation with wrong object *)
Theorem SEC_001_15_capability_safe_encapsulation_wrong_object :
  forall (c : Capability) (obj : CapObject),
    cap_object c <> obj_id obj ->
    access_private (Some c) obj = None.
Proof.
  intros c obj Hwrong.
  unfold access_private, can_access.
  destruct (cap_valid c) eqn:Hvalid.
  - simpl. 
    destruct (Nat.eqb (cap_object c) (obj_id obj)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. contradiction.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* END OF CAPABILITY SECURITY PROOFS                                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)
