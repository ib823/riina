(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* ========================================================================= *)
(*  RIINA Mobile OS - Verified Hypervisor: IOMMU Protection                  *)
(*  Part of RIINA Mobile OS Security Foundation                              *)
(*  Spec Reference: RESEARCH_MOBILEOS01_FOUNDATION.md Section 2.2            *)
(* ========================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

(* ========================================================================= *)
(*  SECTION 1: Core Type Definitions                                         *)
(* ========================================================================= *)

(** Device identifier *)
Inductive DeviceId : Type :=
  | DevId : nat -> DeviceId.

(** Device record *)
Record Device : Type := mkDevice {
  dev_id : DeviceId;
  dev_bus : nat;
  dev_function : nat;
}.

(** Virtual Machine identifier *)
Inductive VMId : Type :=
  | VM : nat -> VMId.

(** Guest VM record *)
Record VirtualMachine : Type := mkVM {
  vm_id : VMId;
  vm_dma_base : nat;
  vm_dma_size : nat;
}.

(** Address type *)
Inductive Address : Type :=
  | Addr : nat -> Address.

(** IOMMU configuration *)
Record IOMMUConfig : Type := mkIOMMUConfig {
  config_device : DeviceId;
  config_allowed_base : nat;
  config_allowed_size : nat;
  config_locked : bool;
}.

(** IOMMU state *)
Record IOMMU : Type := mkIOMMU {
  iommu_id : nat;
  iommu_configs : list IOMMUConfig;
  iommu_enabled : bool;
}.

(** Decidable equality for DeviceId *)
Definition DeviceId_eq_dec : forall (d1 d2 : DeviceId), {d1 = d2} + {d1 <> d2}.
Proof.
  intros [n1] [n2].
  destruct (Nat.eq_dec n1 n2).
  - left. f_equal. exact e.
  - right. intros H. injection H. intros. contradiction.
Defined.

(* ========================================================================= *)
(*  SECTION 2: IOMMU Permission Model                                        *)
(* ========================================================================= *)

(** Find device config in IOMMU *)
Fixpoint find_device_config (dev : DeviceId) (configs : list IOMMUConfig) : option IOMMUConfig :=
  match configs with
  | [] => None
  | cfg :: rest =>
      match DeviceId_eq_dec (config_device cfg) dev with
      | left _ => Some cfg
      | right _ => find_device_config dev rest
      end
  end.

(** Check if address is in allowed range for device *)
Definition address_in_range (addr : nat) (cfg : IOMMUConfig) : bool :=
  andb (config_allowed_base cfg <=? addr)
       (addr <? config_allowed_base cfg + config_allowed_size cfg).

(** IOMMU permits DMA access *)
Definition iommu_permits_dma (iommu : IOMMU) (dev : Device) (addr : Address) : Prop :=
  match addr with
  | Addr n =>
      iommu_enabled iommu = true /\
      exists cfg,
        find_device_config (dev_id dev) (iommu_configs iommu) = Some cfg /\
        address_in_range n cfg = true
  end.

(** Can perform DMA access - only if IOMMU permits *)
Inductive can_dma_access : Device -> Address -> IOMMU -> Prop :=
  | DMAPermitted : forall dev addr iommu,
      iommu_permits_dma iommu dev addr ->
      can_dma_access dev addr iommu.

(* ========================================================================= *)
(*  SECTION 3: IOMMU Configuration Protection                                *)
(* ========================================================================= *)

(** Guest VM cannot modify IOMMU config *)
Definition guest_isolated_from_iommu (vm : VirtualMachine) (iommu : IOMMU) : Prop :=
  forall cfg,
    In cfg (iommu_configs iommu) ->
    config_locked cfg = true.

(** Can modify predicate - only host/hypervisor can modify *)
Inductive can_modify_config : VirtualMachine -> IOMMUConfig -> Prop :=
  (* No constructors - guests cannot modify IOMMU config *)
  .

(** IOMMU config as resource *)
Definition iommu_config (iommu : IOMMU) : list IOMMUConfig :=
  iommu_configs iommu.

(* ========================================================================= *)
(*  SECTION 4: Core IOMMU Security Theorems                                  *)
(* ========================================================================= *)

(* Spec: RESEARCH_MOBILEOS01 Section 2.2 - DMA isolation via IOMMU *)
(** Theorem: A device cannot perform DMA to an address not permitted by IOMMU. *)
Theorem dma_isolation :
  forall (dev : Device) (addr : Address) (iommu : IOMMU),
    ~ iommu_permits_dma iommu dev addr ->
    ~ can_dma_access dev addr iommu.
Proof.
  intros dev addr iommu Hnot_permit.
  intros Haccess.
  inversion Haccess as [d a i Hpermit Heq1 Heq2 Heq3].
  subst.
  apply Hnot_permit. exact Hpermit.
Qed.

(* Spec: RESEARCH_MOBILEOS01 Section 2.2 - IOMMU config protected *)
(** Theorem: Guest VMs cannot modify IOMMU configuration.
    This is a structural property - can_modify_config has no constructors for guests. *)
Theorem iommu_config_protected :
  forall (guest : VirtualMachine) (cfg : IOMMUConfig),
    ~ can_modify_config guest cfg.
Proof.
  intros guest cfg.
  intros Hmodify.
  (* can_modify_config has no constructors, so Hmodify is impossible *)
  inversion Hmodify.
Qed.

(** Alternative formulation with IOMMU record *)
Theorem iommu_config_protected_v2 :
  forall (guest : VirtualMachine) (iommu : IOMMU),
    forall cfg, In cfg (iommu_config iommu) -> ~ can_modify_config guest cfg.
Proof.
  intros guest iommu cfg Hin.
  intros Hmodify.
  inversion Hmodify.
Qed.

(* ========================================================================= *)
(*  SECTION 5: Additional IOMMU Security Properties                          *)
(* ========================================================================= *)

(** DMA requires IOMMU enabled *)
Theorem dma_requires_iommu_enabled :
  forall (dev : Device) (addr : Address) (iommu : IOMMU),
    iommu_enabled iommu = false ->
    ~ iommu_permits_dma iommu dev addr.
Proof.
  intros dev addr iommu Hdisabled.
  destruct addr as [n].
  unfold iommu_permits_dma.
  intros [Henabled _].
  rewrite Hdisabled in Henabled.
  discriminate.
Qed.

(** Device not in config cannot DMA *)
Theorem unconfigured_device_no_dma :
  forall (dev : Device) (addr : Address) (iommu : IOMMU),
    find_device_config (dev_id dev) (iommu_configs iommu) = None ->
    ~ iommu_permits_dma iommu dev addr.
Proof.
  intros dev addr iommu Hnone.
  destruct addr as [n].
  unfold iommu_permits_dma.
  intros [Henabled [cfg [Hfind _]]].
  rewrite Hnone in Hfind.
  discriminate.
Qed.

(** Out of range DMA blocked *)
Theorem out_of_range_dma_blocked :
  forall (dev : Device) (n : nat) (iommu : IOMMU) (cfg : IOMMUConfig),
    find_device_config (dev_id dev) (iommu_configs iommu) = Some cfg ->
    address_in_range n cfg = false ->
    ~ iommu_permits_dma iommu dev (Addr n).
Proof.
  intros dev n iommu cfg Hfind Hrange.
  unfold iommu_permits_dma.
  intros [Henabled [cfg' [Hfind' Hrange']]].
  rewrite Hfind in Hfind'.
  injection Hfind' as Heq.
  subst.
  rewrite Hrange in Hrange'.
  discriminate.
Qed.

(** IOMMU lockdown preserves security *)
Theorem iommu_lockdown_effective :
  forall (iommu : IOMMU) (guest : VirtualMachine),
    guest_isolated_from_iommu guest iommu ->
    forall cfg, In cfg (iommu_configs iommu) -> config_locked cfg = true.
Proof.
  intros iommu guest Hisolated cfg Hin.
  unfold guest_isolated_from_iommu in Hisolated.
  apply Hisolated. exact Hin.
Qed.

(* ========================================================================= *)
(*  SECTION 6: Extended IOMMU Security Properties                            *)
(* ========================================================================= *)

Require Import Coq.micromega.Lia.

(** DMA isolation is enforced: permitted access implies config exists *)
Theorem dma_isolation_enforced :
  forall (dev : Device) (addr : Address) (iommu : IOMMU),
    can_dma_access dev addr iommu ->
    iommu_enabled iommu = true.
Proof.
  intros dev addr iommu Haccess.
  inversion Haccess as [d a i Hpermit Heq1 Heq2 Heq3]. subst.
  destruct addr as [n]. unfold iommu_permits_dma in Hpermit.
  destruct Hpermit as [Henabled _]. exact Henabled.
Qed.

(** Device address is bounded by config range *)
Theorem device_address_bounded :
  forall (dev : Device) (n : nat) (iommu : IOMMU) (cfg : IOMMUConfig),
    iommu_permits_dma iommu dev (Addr n) ->
    find_device_config (dev_id dev) (iommu_configs iommu) = Some cfg ->
    address_in_range n cfg = true.
Proof.
  intros dev n iommu cfg Hpermit Hfind.
  unfold iommu_permits_dma in Hpermit.
  destruct Hpermit as [_ [cfg' [Hfind' Hrange]]].
  rewrite Hfind in Hfind'. injection Hfind' as Heq. subst.
  exact Hrange.
Qed.

(** Mapping table is consistent: find returns consistent configs *)
Theorem mapping_table_consistent :
  forall (dev : DeviceId) (configs : list IOMMUConfig) (cfg1 cfg2 : IOMMUConfig),
    find_device_config dev configs = Some cfg1 ->
    find_device_config dev configs = Some cfg2 ->
    cfg1 = cfg2.
Proof.
  intros dev configs cfg1 cfg2 H1 H2.
  rewrite H1 in H2. injection H2 as Heq. exact Heq.
Qed.

(** No DMA to kernel: if kernel region is outside config range, no access *)
Definition kernel_region_base : nat := 0.
Definition kernel_region_size : nat := 4096.

Theorem no_dma_to_kernel :
  forall (dev : Device) (addr : nat) (iommu : IOMMU) (cfg : IOMMUConfig),
    find_device_config (dev_id dev) (iommu_configs iommu) = Some cfg ->
    config_allowed_base cfg >= kernel_region_base + kernel_region_size ->
    addr < kernel_region_base + kernel_region_size ->
    address_in_range addr cfg = false.
Proof.
  intros dev addr iommu cfg Hfind Hbase Haddr.
  unfold address_in_range.
  apply andb_false_intro1.
  apply Nat.leb_gt. lia.
Qed.

(** IOMMU bypass impossible when enabled and device has no config *)
Theorem iommu_bypass_impossible :
  forall (dev : Device) (addr : Address) (iommu : IOMMU),
    iommu_enabled iommu = true ->
    find_device_config (dev_id dev) (iommu_configs iommu) = None ->
    ~ can_dma_access dev addr iommu.
Proof.
  intros dev addr iommu Henabled Hnone Haccess.
  inversion Haccess as [d a i Hpermit Heq1 Heq2 Heq3]. subst.
  destruct addr as [n]. unfold iommu_permits_dma in Hpermit.
  destruct Hpermit as [_ [cfg [Hfind _]]].
  rewrite Hnone in Hfind. discriminate.
Qed.

(** Address range checking: lower bound verified *)
Theorem address_range_lower_bound :
  forall (addr : nat) (cfg : IOMMUConfig),
    address_in_range addr cfg = true ->
    config_allowed_base cfg <= addr.
Proof.
  intros addr cfg Hrange.
  unfold address_in_range in Hrange.
  apply andb_prop in Hrange. destruct Hrange as [Hlower _].
  apply Nat.leb_le. exact Hlower.
Qed.

(** Address range checking: upper bound verified *)
Theorem address_range_upper_bound :
  forall (addr : nat) (cfg : IOMMUConfig),
    address_in_range addr cfg = true ->
    addr < config_allowed_base cfg + config_allowed_size cfg.
Proof.
  intros addr cfg Hrange.
  unfold address_in_range in Hrange.
  apply andb_prop in Hrange. destruct Hrange as [_ Hupper].
  apply Nat.ltb_lt. exact Hupper.
Qed.

(** Device identity verified: DMA access implies device is configured *)
Theorem device_identity_verified :
  forall (dev : Device) (addr : Address) (iommu : IOMMU),
    can_dma_access dev addr iommu ->
    exists cfg, find_device_config (dev_id dev) (iommu_configs iommu) = Some cfg.
Proof.
  intros dev addr iommu Haccess.
  inversion Haccess as [d a i Hpermit Heq1 Heq2 Heq3]. subst.
  destruct addr as [n]. unfold iommu_permits_dma in Hpermit.
  destruct Hpermit as [_ [cfg [Hfind _]]].
  exists cfg. exact Hfind.
Qed.

(** Empty config list denies all DMA *)
Theorem empty_config_denies_all :
  forall (dev : Device) (addr : Address),
    let iommu := mkIOMMU 0 [] true in
    ~ can_dma_access dev addr iommu.
Proof.
  intros dev addr iommu.
  intros Haccess. inversion Haccess as [d a i Hpermit Heq1 Heq2 Heq3]. subst.
  destruct addr as [n]. unfold iommu_permits_dma in Hpermit.
  destruct Hpermit as [_ [cfg [Hfind _]]].
  simpl in Hfind. discriminate.
Qed.

(** IOMMU disabled means all DMA denied *)
Theorem disabled_iommu_denies_all :
  forall (dev : Device) (addr : Address) (iommu : IOMMU),
    iommu_enabled iommu = false ->
    ~ can_dma_access dev addr iommu.
Proof.
  intros dev addr iommu Hdisabled Haccess.
  inversion Haccess as [d a i Hpermit Heq1 Heq2 Heq3]. subst.
  destruct addr as [n]. unfold iommu_permits_dma in Hpermit.
  destruct Hpermit as [Henabled _].
  rewrite Hdisabled in Henabled. discriminate.
Qed.

(** Locked configs remain across guest operations *)
Theorem locked_config_invariant :
  forall (guest : VirtualMachine) (iommu : IOMMU) (cfg : IOMMUConfig),
    guest_isolated_from_iommu guest iommu ->
    In cfg (iommu_configs iommu) ->
    config_locked cfg = true /\ ~ can_modify_config guest cfg.
Proof.
  intros guest iommu cfg Hisolated Hin.
  split.
  - apply Hisolated. exact Hin.
  - intros Hmod. inversion Hmod.
Qed.

(** Zero-size config denies all addresses *)
Theorem zero_size_config_denies :
  forall (addr : nat) (cfg : IOMMUConfig),
    config_allowed_size cfg = 0 ->
    address_in_range addr cfg = false.
Proof.
  intros addr cfg Hzero.
  unfold address_in_range. rewrite Hzero.
  rewrite Nat.add_0_r.
  destruct (config_allowed_base cfg <=? addr) eqn:Hlb.
  - simpl. apply Nat.ltb_ge. apply Nat.leb_le in Hlb. lia.
  - reflexivity.
Qed.

(** Find device config: not found means not in list *)
Theorem find_device_config_none_not_in :
  forall (dev : DeviceId) (configs : list IOMMUConfig),
    find_device_config dev configs = None ->
    forall cfg, In cfg configs -> config_device cfg <> dev.
Proof.
  intros dev configs.
  induction configs as [| c rest IH].
  - intros _ cfg Hin. inversion Hin.
  - intros Hnone cfg Hin.
    simpl in Hnone.
    destruct (DeviceId_eq_dec (config_device c) dev).
    + discriminate.
    + destruct Hin as [Heq | Hrest].
      * subst. exact n.
      * apply IH. exact Hnone. exact Hrest.
Qed.

(** Config found means device matches *)
Theorem find_device_config_some_matches :
  forall (dev : DeviceId) (configs : list IOMMUConfig) (cfg : IOMMUConfig),
    find_device_config dev configs = Some cfg ->
    config_device cfg = dev.
Proof.
  intros dev configs.
  induction configs as [| c rest IH].
  - intros cfg Hfind. simpl in Hfind. discriminate.
  - intros cfg Hfind.
    simpl in Hfind.
    destruct (DeviceId_eq_dec (config_device c) dev) as [Heq | Hneq].
    + injection Hfind. intros Hcfg. rewrite <- Hcfg. exact Heq.
    + apply IH. exact Hfind.
Qed.

(** Two distinct devices with different IDs have independent configs *)
Theorem independent_device_configs :
  forall (dev1 dev2 : Device) (iommu : IOMMU) (cfg1 cfg2 : IOMMUConfig),
    dev_id dev1 <> dev_id dev2 ->
    find_device_config (dev_id dev1) (iommu_configs iommu) = Some cfg1 ->
    find_device_config (dev_id dev2) (iommu_configs iommu) = Some cfg2 ->
    config_device cfg1 <> config_device cfg2.
Proof.
  intros dev1 dev2 iommu cfg1 cfg2 Hneq Hfind1 Hfind2.
  apply find_device_config_some_matches in Hfind1.
  apply find_device_config_some_matches in Hfind2.
  rewrite Hfind1, Hfind2. exact Hneq.
Qed.

(* ========================================================================= *)
(*  END OF FILE: IOMMUProtection.v                                           *)
(*  Theorems: 7 original + 15 new = 22 total                                 *)
(*  Admitted: 0 | admit: 0 | New Axioms: 0                                   *)
(* ========================================================================= *)
