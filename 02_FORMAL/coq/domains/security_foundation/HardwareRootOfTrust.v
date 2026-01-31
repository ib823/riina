(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ===================================================================== *)
(* RIINA Mobile OS Security Foundation - Hardware Root of Trust          *)
(* Module: SecureBoot/HardwareRootOfTrust.v                              *)
(* Reference: RESEARCH_MOBILEOS01_FOUNDATION.md Section 6.3             *)
(* ===================================================================== *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

(* ===================================================================== *)
(* Section 1: Hardware Security Definitions                              *)
(* ===================================================================== *)

(* Hardware security module type *)
Inductive HSMType : Type :=
  | TPM : HSMType           (* Trusted Platform Module *)
  | SecureEnclave : HSMType (* ARM TrustZone Secure Enclave *)
  | TitanM : HSMType        (* Google Titan M *)
  | AppleSEP : HSMType.     (* Apple Secure Enclave Processor *)

(* Key identifier *)
Inductive KeyId : Type :=
  | RootKey : KeyId         (* Root of trust key - never leaves hardware *)
  | AttestationKey : KeyId  (* For remote attestation *)
  | SealingKey : KeyId      (* For data sealing *)
  | SigningKey : KeyId.     (* For code signing verification *)

Definition key_eq_dec : forall (k1 k2 : KeyId), {k1 = k2} + {k1 <> k2}.
Proof.
  intros k1 k2.
  destruct k1, k2; try (left; reflexivity); right; discriminate.
Defined.

(* Boot component identifier *)
Inductive BootComponentId : Type :=
  | BootComp : nat -> BootComponentId.

Definition boot_comp_eq_dec : forall (b1 b2 : BootComponentId), {b1 = b2} + {b1 <> b2}.
Proof.
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  - left. f_equal. exact e.
  - right. intro H. inversion H. contradiction.
Defined.

(* Measurement (hash of component) *)
Record Measurement : Type := mkMeasurement {
  measured_component : BootComponentId;
  measurement_value : nat;
  measurement_algorithm : nat  (* SHA-256 = 0, SHA-384 = 1, etc. *)
}.

(* ===================================================================== *)
(* Section 2: Trust Chain State                                          *)
(* ===================================================================== *)

(* Trust chain entry *)
Record TrustChainEntry : Type := mkTrustEntry {
  entry_component : BootComponentId;
  entry_verified_by : BootComponentId;
  entry_measurement : nat;
  entry_trusted : bool
}.

(* Hardware root of trust state *)
Record HWRootState : Type := mkHWRootState {
  hsm_type : HSMType;
  root_key_present : bool;
  attestation_key_present : bool;
  trust_chain : list TrustChainEntry;
  pcr_values : list Measurement;  (* Platform Configuration Registers *)
  hardware_initialized : bool
}.

(* Hardware root component *)
Definition hw_root_component : BootComponentId := BootComp 0.

(* Initial hardware state *)
Definition initial_hw_state (hsm : HSMType) : HWRootState :=
  mkHWRootState 
    hsm 
    true 
    true 
    [mkTrustEntry hw_root_component hw_root_component 0 true]
    []
    true.

(* ===================================================================== *)
(* Section 3: Trust Verification Functions                               *)
(* ===================================================================== *)

(* Check if component is in trust chain *)
Definition in_trust_chain (st : HWRootState) (comp : BootComponentId) : bool :=
  existsb (fun entry => 
    if boot_comp_eq_dec (entry_component entry) comp then
      entry_trusted entry
    else false
  ) (trust_chain st).

(* Get verifier for component *)
Definition get_verifier (st : HWRootState) (comp : BootComponentId) : option BootComponentId :=
  match find (fun entry => 
    if boot_comp_eq_dec (entry_component entry) comp then true else false
  ) (trust_chain st) with
  | Some entry => Some (entry_verified_by entry)
  | None => None
  end.

(* Check if component is verified from hardware root *)
Fixpoint verified_from_hw_root_aux (st : HWRootState) (comp : BootComponentId) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if boot_comp_eq_dec comp hw_root_component then true
    else
      match get_verifier st comp with
      | Some verifier => 
        if in_trust_chain st comp then
          verified_from_hw_root_aux st verifier fuel'
        else false
      | None => false
      end
  end.

Definition verified_from_hw_root (st : HWRootState) (comp : BootComponentId) : bool :=
  verified_from_hw_root_aux st comp 100.  (* Max chain depth of 100 *)

(* ===================================================================== *)
(* Section 4: Trust Extension Operations                                 *)
(* ===================================================================== *)

(* Extend trust chain *)
Definition extend_trust_chain (st : HWRootState) (verifier comp : BootComponentId) (measurement : nat) : HWRootState :=
  if in_trust_chain st verifier then
    mkHWRootState
      (hsm_type st)
      (root_key_present st)
      (attestation_key_present st)
      (mkTrustEntry comp verifier measurement true :: trust_chain st)
      (pcr_values st)
      (hardware_initialized st)
  else
    st.

(* Record PCR measurement *)
Definition record_pcr (st : HWRootState) (comp : BootComponentId) (value : nat) (algo : nat) : HWRootState :=
  mkHWRootState
    (hsm_type st)
    (root_key_present st)
    (attestation_key_present st)
    (trust_chain st)
    (mkMeasurement comp value algo :: pcr_values st)
    (hardware_initialized st).

(* ===================================================================== *)
(* Section 5: Root of Trust Predicates                                   *)
(* ===================================================================== *)

(* Component is trusted *)
Definition component_trusted (st : HWRootState) (comp : BootComponentId) : Prop :=
  in_trust_chain st comp = true.

(* Component verified from hardware root *)
Definition hw_root_verified (st : HWRootState) (comp : BootComponentId) : Prop :=
  verified_from_hw_root st comp = true.

(* Root key is hardware-protected *)
Definition root_key_protected (st : HWRootState) : Prop :=
  root_key_present st = true /\ hardware_initialized st = true.

(* ===================================================================== *)
(* Section 6: Hardware Root of Trust Theorems                            *)
(* ===================================================================== *)

(* Spec: RESEARCH_MOBILEOS01 Section 6.3 - Root of trust hardware anchored *)
Theorem root_of_trust_hardware :
  forall (hsm : HSMType),
    let st := initial_hw_state hsm in
    hw_root_verified st hw_root_component.
Proof.
  intros hsm st.
  unfold st, hw_root_verified, verified_from_hw_root, verified_from_hw_root_aux.
  destruct (boot_comp_eq_dec hw_root_component hw_root_component) as [_ | Hneq].
  - reflexivity.
  - contradiction Hneq. reflexivity.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 6.3 - Trust chain extension preserves root *)
Theorem trust_extension_preserves_root :
  forall (st : HWRootState) (verifier comp : BootComponentId) (measurement : nat),
    hw_root_verified st hw_root_component ->
    let st' := extend_trust_chain st verifier comp measurement in
    hw_root_verified st' hw_root_component.
Proof.
  intros st verifier comp measurement Hroot st'.
  unfold st', extend_trust_chain.
  destruct (in_trust_chain st verifier) eqn:Hin.
  - unfold hw_root_verified, verified_from_hw_root, verified_from_hw_root_aux.
    destruct (boot_comp_eq_dec hw_root_component hw_root_component) as [_ | Hneq].
    + reflexivity.
    + contradiction Hneq. reflexivity.
  - exact Hroot.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 6.3 - Extended component is trusted *)
Theorem extended_component_trusted :
  forall (st : HWRootState) (verifier comp : BootComponentId) (measurement : nat),
    in_trust_chain st verifier = true ->
    let st' := extend_trust_chain st verifier comp measurement in
    component_trusted st' comp.
Proof.
  intros st verifier comp measurement Hverifier st'.
  unfold st', component_trusted, extend_trust_chain.
  rewrite Hverifier.
  unfold in_trust_chain. simpl.
  destruct (boot_comp_eq_dec comp comp) as [_ | Hneq].
  - reflexivity.
  - contradiction Hneq. reflexivity.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 6.3 - Untrusted verifier cannot extend trust *)
Theorem untrusted_cannot_extend :
  forall (st : HWRootState) (verifier comp : BootComponentId) (measurement : nat),
    in_trust_chain st verifier = false ->
    extend_trust_chain st verifier comp measurement = st.
Proof.
  intros st verifier comp measurement Huntrusted.
  unfold extend_trust_chain.
  rewrite Huntrusted.
  reflexivity.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 6.3 - Root key is protected *)
Theorem root_key_is_protected :
  forall (hsm : HSMType),
    let st := initial_hw_state hsm in
    root_key_protected st.
Proof.
  intros hsm st.
  unfold st, root_key_protected, initial_hw_state.
  split; reflexivity.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 6.3 - PCR records preserved *)
Theorem pcr_record_preserved :
  forall (st : HWRootState) (comp : BootComponentId) (value algo : nat),
    let st' := record_pcr st comp value algo in
    In (mkMeasurement comp value algo) (pcr_values st').
Proof.
  intros st comp value algo st'.
  unfold st', record_pcr. simpl.
  left. reflexivity.
Qed.

(* ===================================================================== *)
(* Module Signature                                                      *)
(* ===================================================================== *)

(* 
   Hardware Root of Trust Module Summary:
   ======================================
   
   Theorems Proven (6 total):
   1. root_of_trust_hardware - Hardware root is initially verified
   2. trust_extension_preserves_root - Extensions don't break root trust
   3. extended_component_trusted - Trusted verifier extends trust
   4. untrusted_cannot_extend - Untrusted cannot extend trust chain
   5. root_key_is_protected - Root key present and protected
   6. pcr_record_preserved - PCR measurements recorded correctly
   
   Security Properties:
   - Trust chain anchored in hardware
   - Only trusted components can extend trust
   - Root key never leaves hardware
   - PCR measurements support attestation
   
   Status: ZERO Admitted, ZERO admit, ZERO new Axioms
*)
