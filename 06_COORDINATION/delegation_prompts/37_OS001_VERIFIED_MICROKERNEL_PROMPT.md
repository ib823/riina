# DELEGATION PROMPT: OS-001 VERIFIED MICROKERNEL COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: OS-001-VERIFIED-MICROKERNEL-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — OPERATING SYSTEM LAYER (L4)
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `VerifiedMicrokernel.v` with 25 theorems (subset of ~500 total OS theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-OS, a formally verified microkernel operating system.
These proofs establish that kernel operations CANNOT be exploited — privilege escalation,
memory corruption, and confused deputy attacks are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/28_DOMAIN_RIINA_OS/RESEARCH_OS01_FOUNDATION.md

THIS IS THE STANDARD THAT MAKES seL4 LOOK LIKE A PROTOTYPE.
THIS IS THE KERNEL THAT ENDS ALL KERNEL SECURITY RESEARCH.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (25 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

CAPABILITY SYSTEM (10 theorems):
OS_001_01: cap_unforgeable — Capabilities cannot be forged
OS_001_02: cap_monotonic — Capability rights can only decrease, never increase
OS_001_03: cap_revocation_complete — Revoked capabilities are completely unusable
OS_001_04: cap_transfer_safe — Capability transfer preserves system invariants
OS_001_05: cap_derivation_sound — Derived capabilities have subset of parent rights
OS_001_06: no_confused_deputy — Process cannot use capability it doesn't hold
OS_001_07: cap_lookup_correct — Capability table lookup is correct
OS_001_08: cap_space_isolation — Capability spaces are isolated between processes
OS_001_09: cap_invoke_authorized — Only authorized invocations succeed
OS_001_10: cap_badge_integrity — Capability badges cannot be modified

MEMORY MANAGEMENT (8 theorems):
OS_001_11: address_space_isolation — Process address spaces are isolated
OS_001_12: kernel_memory_integrity — Kernel memory invariants preserved
OS_001_13: page_table_correct — Page table translation is correct
OS_001_14: no_page_table_corruption — Page tables cannot be corrupted by userspace
OS_001_15: mapping_respects_caps — Memory mappings respect capabilities
OS_001_16: unmap_complete — Unmapped pages are completely inaccessible
OS_001_17: no_kernel_data_leak — Kernel data never leaks to userspace
OS_001_18: frame_allocation_safe — Frame allocation maintains invariants

IPC SYSTEM (7 theorems):
OS_001_19: ipc_type_safe — IPC messages are type-safe
OS_001_20: ipc_cap_transfer_safe — IPC capability transfer is safe
OS_001_21: ipc_deadlock_free — IPC system is deadlock-free
OS_001_22: ipc_no_amplification — IPC cannot amplify privileges
OS_001_23: ipc_isolation — IPC maintains process isolation
OS_001_24: endpoint_protection — Endpoints are protected by capabilities
OS_001_25: notification_no_leak — Notifications don't leak information

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* VerifiedMicrokernel.v - RIINA-OS Microkernel Verification *)
(* Spec: 01_RESEARCH/28_DOMAIN_RIINA_OS/RESEARCH_OS01_FOUNDATION.md *)
(* Layer: L4 Operating System *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Import ListNotations.

(** ═══════════════════════════════════════════════════════════════════════════
    CAPABILITY SYSTEM DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Capability rights *)
Inductive Right : Type :=
  | RRead : Right
  | RWrite : Right
  | RGrant : Right
  | RRevoke : Right.

(* Capability structure *)
Record Capability : Type := mkCap {
  cap_object : nat;           (* Object reference *)
  cap_rights : list Right;    (* Rights held *)
  cap_badge : nat;            (* Unforgeable badge *)
}.

(* Process identifier *)
Definition ProcId := nat.

(* Capability table: maps slot to capability *)
Definition CapTable := list (option Capability).

(* System state *)
Record KernelState : Type := mkState {
  processes : list ProcId;
  cap_tables : ProcId -> CapTable;
  kernel_objects : list nat;
}.

(* Capability lookup *)
Definition cap_lookup (s : KernelState) (p : ProcId) (slot : nat) : option Capability :=
  nth_error (cap_tables s p) slot.

(* Holds predicate *)
Definition holds (s : KernelState) (p : ProcId) (c : Capability) : Prop :=
  exists slot, cap_lookup s p slot = Some c.

(* Rights subset *)
Definition rights_subset (r1 r2 : list Right) : Prop :=
  forall r, In r r1 -> In r r2.

(** ═══════════════════════════════════════════════════════════════════════════
    MEMORY MANAGEMENT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Virtual and physical addresses *)
Definition VAddr := nat.
Definition PAddr := nat.

(* Page permissions *)
Record PagePerms : Type := mkPerms {
  perm_read : bool;
  perm_write : bool;
  perm_execute : bool;
}.

(* Page table entry *)
Record PTE : Type := mkPTE {
  pte_paddr : PAddr;
  pte_perms : PagePerms;
  pte_valid : bool;
}.

(* Address space *)
Definition AddressSpace := VAddr -> option PTE.

(* Process has its own address space *)
Definition proc_address_space (s : KernelState) (p : ProcId) : AddressSpace :=
  fun _ => None.  (* Placeholder - real impl uses cap_tables *)

(** ═══════════════════════════════════════════════════════════════════════════
    IPC DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* IPC endpoint *)
Record Endpoint : Type := mkEndpoint {
  ep_cap : Capability;
  ep_queue : list ProcId;
}.

(* IPC message *)
Record IPCMessage : Type := mkMsg {
  msg_data : list nat;
  msg_caps : list Capability;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    CAPABILITY SYSTEM THEOREMS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* OS_001_01 through OS_001_25 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* OS_001_01: Capability unforgability *)
Theorem cap_unforgeable : forall s p c,
  holds s p c ->
  exists slot, cap_lookup s p slot = Some c.

(* OS_001_02: Capability monotonicity *)
Theorem cap_monotonic : forall c1 c2,
  derives c1 c2 ->
  rights_subset (cap_rights c2) (cap_rights c1).

(* OS_001_06: No confused deputy *)
Theorem no_confused_deputy : forall s p1 p2 c action,
  can_invoke s p1 action c ->
  holds s p1 c.

(* OS_001_11: Address space isolation *)
Theorem address_space_isolation : forall s p1 p2 vaddr,
  p1 <> p2 ->
  mapped s p1 vaddr ->
  ~ mapped s p2 vaddr \/
  shared_readonly s p1 p2 vaddr.

(* OS_001_21: IPC deadlock freedom *)
Theorem ipc_deadlock_free : forall s,
  valid_state s ->
  ~ exists cycle, ipc_wait_cycle s cycle.
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match OS_001_01 through OS_001_25
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 25 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA os/VerifiedMicrokernel.v
grep -c "Admitted\." os/VerifiedMicrokernel.v  # Must return 0
grep -c "admit\." os/VerifiedMicrokernel.v     # Must return 0
grep -c "^Axiom" os/VerifiedMicrokernel.v      # Must return 0
grep -c "^Theorem OS_001" os/VerifiedMicrokernel.v  # Must return 25
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* VerifiedMicrokernel.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
