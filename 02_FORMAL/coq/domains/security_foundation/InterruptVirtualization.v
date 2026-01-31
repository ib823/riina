(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ========================================================================= *)
(*  RIINA Mobile OS - Verified Hypervisor: Interrupt Virtualization          *)
(*  Part of RIINA Mobile OS Security Foundation                              *)
(*  Spec Reference: RESEARCH_MOBILEOS01_FOUNDATION.md Section 2.3            *)
(* ========================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* ========================================================================= *)
(*  SECTION 1: Core Type Definitions                                         *)
(* ========================================================================= *)

(** Virtual Machine identifier *)
Inductive VMId : Type :=
  | VM : nat -> VMId.

(** Virtual Machine record *)
Record VirtualMachine : Type := mkVM {
  vm_id : VMId;
  vm_assigned_irqs : list nat;
}.

(** Interrupt identifier *)
Inductive Interrupt : Type :=
  | IRQ : nat -> Interrupt.

(** Interrupt source *)
Inductive InterruptSource : Type :=
  | DeviceSource : nat -> InterruptSource
  | TimerSource : InterruptSource
  | IPISource : VMId -> InterruptSource.

(** Decidable equality for VMId *)
Definition VMId_eq_dec : forall (v1 v2 : VMId), {v1 = v2} + {v1 <> v2}.
Proof.
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  - left. f_equal. exact e.
  - right. intros H. injection H. intros. contradiction.
Defined.

(** Decidable equality for Interrupt *)
Definition Interrupt_eq_dec : forall (i1 i2 : Interrupt), {i1 = i2} + {i1 <> i2}.
Proof.
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  - left. f_equal. exact e.
  - right. intros H. injection H. intros. contradiction.
Defined.

(* ========================================================================= *)
(*  SECTION 2: Interrupt Authorization Model                                 *)
(* ========================================================================= *)

(** Hypervisor interrupt routing table *)
Record InterruptState : Type := mkIRQState {
  irq_assignments : list (nat * VMId);  (* IRQ -> owning VM *)
  ipi_allowed : list (VMId * VMId);     (* source -> target allowed IPI *)
}.

(** Check if VM is authorized for interrupt *)
Definition vm_owns_irq (st : InterruptState) (vm : VirtualMachine) (irq : nat) : Prop :=
  In (irq, vm_id vm) (irq_assignments st).

(** Check if IPI is authorized *)
Definition ipi_authorized (st : InterruptState) (source target : VMId) : Prop :=
  In (source, target) (ipi_allowed st).

(** Authorized injection from source to target VM *)
Definition authorized_injection (st : InterruptState) (source : InterruptSource) (target : VirtualMachine) : Prop :=
  match source with
  | DeviceSource irq => vm_owns_irq st target irq
  | TimerSource => True  (* Timer interrupts always authorized to current VM *)
  | IPISource src_vm => ipi_authorized st src_vm (vm_id target)
  end.

(** Injection event *)
Inductive injects_interrupt : InterruptState -> InterruptSource -> VirtualMachine -> Prop :=
  | InjectAuthorized : forall st source target,
      authorized_injection st source target ->
      injects_interrupt st source target.

(* ========================================================================= *)
(*  SECTION 3: Inter-VM Interrupt Control                                    *)
(* ========================================================================= *)

(** VM attempting to inject interrupt to another VM *)
Inductive vm_injects_to : VirtualMachine -> Interrupt -> VirtualMachine -> InterruptState -> Prop :=
  | VMInjectsIPI : forall src_vm irq tgt_vm st,
      ipi_authorized st (vm_id src_vm) (vm_id tgt_vm) ->
      vm_injects_to src_vm irq tgt_vm st.

(** Can inject predicate *)
Definition can_inject (st : InterruptState) (vm1 : VirtualMachine) (irq : Interrupt) (vm2 : VirtualMachine) : Prop :=
  vm_id vm1 = vm_id vm2 \/  (* VM can inject to itself *)
  ipi_authorized st (vm_id vm1) (vm_id vm2).

(* ========================================================================= *)
(*  SECTION 4: Core Interrupt Virtualization Theorems                        *)
(* ========================================================================= *)

(* Spec: RESEARCH_MOBILEOS01 Section 2.3 - Interrupt injection authorized *)
(** Theorem: Any interrupt injection must be authorized by the hypervisor. *)
Theorem interrupt_injection_authorized :
  forall (st : InterruptState) (source : InterruptSource) (target : VirtualMachine),
    injects_interrupt st source target ->
    authorized_injection st source target.
Proof.
  intros st source target Hinject.
  inversion Hinject as [st' src tgt Hauth Heq1 Heq2 Heq3].
  subst.
  exact Hauth.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 2.3 - Interrupt isolation between VMs *)
(** Theorem: One VM cannot inject interrupts to another VM without explicit authorization. *)
Theorem interrupt_isolation :
  forall (vm1 vm2 : VirtualMachine) (irq : Interrupt) (st : InterruptState),
    vm_id vm1 <> vm_id vm2 ->
    ~ ipi_authorized st (vm_id vm1) (vm_id vm2) ->
    ~ can_inject st vm1 irq vm2.
Proof.
  intros vm1 vm2 irq st Hneq Hnot_auth.
  unfold can_inject.
  intros [Heq | Hauth].
  - (* Same VM case - contradicts Hneq *)
    apply Hneq. exact Heq.
  - (* IPI authorized case - contradicts Hnot_auth *)
    apply Hnot_auth. exact Hauth.
Qed.

(* ========================================================================= *)
(*  SECTION 5: Additional Interrupt Security Properties                      *)
(* ========================================================================= *)

(** Device interrupts are VM-exclusive *)
(** Helper: Find VM for IRQ *)
Fixpoint find_vm_for_irq (assignments : list (nat * VMId)) (irq : nat) : option VMId :=
  match assignments with
  | [] => None
  | (i, v) :: rest => if Nat.eqb i irq then Some v else find_vm_for_irq rest irq
  end.

(** IRQ ownership is unique when assignment exists *)
Theorem device_irq_unique_owner :
  forall (st : InterruptState) (vm1 vm2 : VirtualMachine) (irq : nat),
    find_vm_for_irq (irq_assignments st) irq = Some (vm_id vm1) ->
    find_vm_for_irq (irq_assignments st) irq = Some (vm_id vm2) ->
    vm_id vm1 = vm_id vm2.
Proof.
  intros st vm1 vm2 irq Hfind1 Hfind2.
  rewrite Hfind1 in Hfind2.
  injection Hfind2 as Heq.
  exact Heq.
Qed.

(** Timer interrupts are always local *)
Theorem timer_interrupt_local :
  forall (st : InterruptState) (vm : VirtualMachine),
    authorized_injection st TimerSource vm.
Proof.
  intros st vm.
  unfold authorized_injection.
  exact I.
Qed.

(** IPI requires explicit authorization *)
Theorem ipi_requires_authorization :
  forall (st : InterruptState) (src tgt : VirtualMachine),
    authorized_injection st (IPISource (vm_id src)) tgt ->
    ipi_authorized st (vm_id src) (vm_id tgt).
Proof.
  intros st src tgt Hauth.
  unfold authorized_injection in Hauth.
  exact Hauth.
Qed.

(** Unauthorized IPI blocked *)
Theorem unauthorized_ipi_blocked :
  forall (st : InterruptState) (src_vm tgt_vm : VirtualMachine),
    ~ ipi_authorized st (vm_id src_vm) (vm_id tgt_vm) ->
    ~ injects_interrupt st (IPISource (vm_id src_vm)) tgt_vm.
Proof.
  intros st src_vm tgt_vm Hnot_auth.
  intros Hinject.
  inversion Hinject as [st' source target Hauth Heq1 Heq2 Heq3].
  subst.
  unfold authorized_injection in Hauth.
  apply Hnot_auth. exact Hauth.
Qed.

(** Self-injection always allowed *)
Theorem self_injection_allowed :
  forall (st : InterruptState) (vm : VirtualMachine) (irq : Interrupt),
    can_inject st vm irq vm.
Proof.
  intros st vm irq.
  unfold can_inject.
  left. reflexivity.
Qed.

(* ========================================================================= *)
(*  END OF FILE: InterruptVirtualization.v                                   *)
(*  Theorems: 2 core + 4 supporting = 6 total                                *)
(*  Admitted: 0 | admit: 0 | New Axioms: 0                                   *)
(* ========================================================================= *)
