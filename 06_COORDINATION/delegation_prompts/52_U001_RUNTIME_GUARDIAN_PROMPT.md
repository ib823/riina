# DELEGATION PROMPT: U-001 RUNTIME GUARDIAN COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
===============================================================================================================
TASK ID: U-001-RUNTIME-GUARDIAN-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — VERIFIED MICRO-HYPERVISOR
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
===============================================================================================================

OUTPUT: `RuntimeGuardian.v` with 35 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-SENTINEL — the verified micro-hypervisor that
monitors applications for integrity violations. Physics is hostile: cosmic rays flip bits,
power supplies glitch. We detect violations and halt before damage occurs.

RESEARCH REFERENCE: 01_RESEARCH/21_DOMAIN_U_RUNTIME_GUARDIAN/RESEARCH_U01_FOUNDATION.md

TRUST NOTHING. NOT EVEN THE SILICON. NOT EVEN THE ATOMS.
WE CANNOT PREVENT BIT FLIPS. WE CAN DETECT THEM.

===============================================================================================================
REQUIRED THEOREMS (35 total):
===============================================================================================================

CONTROL FLOW INTEGRITY (10 theorems):
U_001_01: cfi_cfg_wellformed — Control flow graph is well-formed
U_001_02: cfi_ip_in_cfg — Instruction pointer always in valid CFG
U_001_03: cfi_indirect_safe — Indirect jumps only to valid targets
U_001_04: cfi_return_integrity — Return addresses are valid
U_001_05: cfi_call_integrity — Call targets are valid
U_001_06: cfi_no_arbitrary_jump — No jumps to arbitrary addresses
U_001_07: cfi_shadow_stack — Shadow stack matches actual returns
U_001_08: cfi_forward_edge — Forward edges are protected
U_001_09: cfi_backward_edge — Backward edges are protected
U_001_10: cfi_violation_detected — CFI violations are detected

MEMORY INTEGRITY (8 theorems):
U_001_11: mem_checksum_correct — Memory checksums are correct
U_001_12: mem_redundant_storage — Critical data stored redundantly
U_001_13: mem_ecc_corrects — ECC corrects single-bit errors
U_001_14: mem_ecc_detects — ECC detects multi-bit errors
U_001_15: mem_bounds_enforced — Memory bounds are enforced
U_001_16: mem_readonly_protected — Read-only memory is protected
U_001_17: mem_kernel_isolated — Kernel memory is isolated
U_001_18: mem_corruption_detected — Memory corruption is detected

N-MODULAR REDUNDANCY (7 theorems):
U_001_19: nmr_variants_independent — Execution variants are independent
U_001_20: nmr_state_synchronized — States synchronized at checkpoints
U_001_21: nmr_divergence_detected — State divergence is detected
U_001_22: nmr_single_fault_tolerant — Single faults are tolerated
U_001_23: nmr_voting_correct — Voting mechanism is correct
U_001_24: nmr_recovery_sound — Recovery mechanism is sound
U_001_25: nmr_coverage — NMR covers probabilistic errors

PANIC PROTOCOL (5 theorems):
U_001_26: panic_keys_zeroized — Keys zeroized on panic
U_001_27: panic_execution_halted — Execution halted on panic
U_001_28: panic_audit_logged — Violation logged before halt
U_001_29: panic_triggered — Invariant violation triggers panic
U_001_30: panic_irreversible — Panic state is irreversible

WATCHDOG AND MONITOR (5 theorems):
U_001_31: watchdog_nmi — Watchdog uses non-maskable interrupt
U_001_32: watchdog_monitor_integrity — Watchdog verifies monitor integrity
U_001_33: monitor_unprivileged — Application cannot modify monitor
U_001_34: monitor_complete_mediation — All operations go through monitor
U_001_35: monitor_tamper_evident — Monitor tampering is evident

===============================================================================================================
REQUIRED STRUCTURE:
===============================================================================================================

```coq
(* RuntimeGuardian.v - RIINA-SENTINEL Micro-Hypervisor Verification *)
(* Spec: 01_RESEARCH/21_DOMAIN_U_RUNTIME_GUARDIAN/RESEARCH_U01_FOUNDATION.md *)
(* Layer: Runtime Monitor *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(** ===============================================================================
    CONTROL FLOW GRAPH
    =============================================================================== *)

(* Instruction address *)
Definition Addr := nat.

(* Control flow graph edge *)
Inductive CFGEdge : Type :=
  | DirectJump : Addr -> Addr -> CFGEdge
  | IndirectJump : Addr -> list Addr -> CFGEdge
  | Call : Addr -> Addr -> CFGEdge
  | Return : Addr -> CFGEdge.

(* Control flow graph *)
Record CFG : Type := mkCFG {
  cfg_nodes : list Addr;
  cfg_edges : list CFGEdge;
  cfg_entry : Addr;
}.

(* Valid CFG node *)
Definition valid_node (cfg : CFG) (a : Addr) : Prop :=
  In a (cfg_nodes cfg).

(* Valid CFG edge *)
Definition valid_edge (cfg : CFG) (src dst : Addr) : Prop :=
  exists e, In e (cfg_edges cfg) /\
  match e with
  | DirectJump s d => s = src /\ d = dst
  | IndirectJump s targets => s = src /\ In dst targets
  | Call s d => s = src /\ d = dst
  | Return s => s = src
  end.

(** ===============================================================================
    EXECUTION STATE
    =============================================================================== *)

(* Shadow stack for return addresses *)
Definition ShadowStack := list Addr.

(* Memory with checksums *)
Record ChecksummedMemory : Type := mkChkMem {
  mem_data : Addr -> nat;
  mem_checksum : nat;
}.

(* Execution state *)
Record ExecState : Type := mkExecState {
  ip : Addr;                        (* Instruction pointer *)
  shadow_stack : ShadowStack;       (* Return address stack *)
  memory : ChecksummedMemory;       (* Memory with integrity *)
}.

(* CFI check passes *)
Definition cfi_valid (cfg : CFG) (s : ExecState) : Prop :=
  valid_node cfg (ip s).

(** ===============================================================================
    N-MODULAR REDUNDANCY
    =============================================================================== *)

(* Execution variant *)
Record Variant : Type := mkVariant {
  var_id : nat;
  var_state : ExecState;
}.

(* NMR configuration *)
Record NMRConfig : Type := mkNMR {
  variants : list Variant;
  sync_points : list Addr;
  vote_threshold : nat;
}.

(* States match at synchronization point *)
Definition states_match (v1 v2 : Variant) : Prop :=
  var_state v1 = var_state v2.

(* Voting result *)
Definition nmr_vote (cfg : NMRConfig) : option ExecState :=
  match variants cfg with
  | v :: _ => Some (var_state v)  (* Placeholder - real impl does voting *)
  | [] => None
  end.

(** ===============================================================================
    PANIC PROTOCOL
    =============================================================================== *)

(* Panic state *)
Inductive PanicState : Type :=
  | Running : PanicState
  | Panicked : nat -> PanicState.  (* Reason code *)

(* System state with panic *)
Record SystemState : Type := mkSystem {
  exec : ExecState;
  panic : PanicState;
  keys_present : bool;
  audit_log : list nat;
}.

(* Zeroize keys *)
Definition zeroize_keys (s : SystemState) : SystemState :=
  mkSystem (exec s) (panic s) false (audit_log s).

(* Trigger panic *)
Definition trigger_panic (s : SystemState) (reason : nat) : SystemState :=
  mkSystem (exec s) (Panicked reason) false (reason :: audit_log s).

(** ===============================================================================
    WATCHDOG
    =============================================================================== *)

(* Watchdog state *)
Record WatchdogState : Type := mkWatchdog {
  wd_enabled : bool;
  wd_timeout : nat;
  wd_counter : nat;
  wd_monitor_hash : nat;
}.

(* Watchdog check *)
Definition watchdog_check (wd : WatchdogState) (current_hash : nat) : bool :=
  wd_enabled wd && Nat.eqb (wd_monitor_hash wd) current_hash.

(** ===============================================================================
    YOUR PROOFS: U_001_01 through U_001_35
    =============================================================================== *)

(* Implement all 35 theorems here *)
```

===============================================================================================================
THEOREM SPECIFICATIONS:
===============================================================================================================

```coq
(* U_001_02: Instruction pointer always in valid CFG *)
Theorem cfi_ip_in_cfg : forall cfg s,
  valid_system cfg s ->
  valid_node cfg (ip (exec s)).

(* U_001_10: CFI violations are detected *)
Theorem cfi_violation_detected : forall cfg s s',
  step s s' ->
  ~ cfi_valid cfg s' ->
  panic s' = Panicked CFI_VIOLATION.

(* U_001_21: State divergence is detected *)
Theorem nmr_divergence_detected : forall cfg,
  length (variants cfg) >= 2 ->
  exists v1 v2, In v1 (variants cfg) /\ In v2 (variants cfg) /\
  ~ states_match v1 v2 ->
  divergence_detected cfg = true.

(* U_001_26: Keys zeroized on panic *)
Theorem panic_keys_zeroized : forall s reason,
  trigger_panic s reason = s' ->
  keys_present s' = false.

(* U_001_32: Watchdog verifies monitor integrity *)
Theorem watchdog_monitor_integrity : forall wd hash,
  watchdog_check wd hash = true ->
  hash = wd_monitor_hash wd.
```

===============================================================================================================
FORBIDDEN ACTIONS:
===============================================================================================================

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match U_001_01 through U_001_35
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 35 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

===============================================================================================================
VERIFICATION COMMANDS (must pass):
===============================================================================================================

```bash
coqc -Q . RIINA runtime/RuntimeGuardian.v
grep -c "Admitted\." runtime/RuntimeGuardian.v  # Must return 0
grep -c "admit\." runtime/RuntimeGuardian.v     # Must return 0
grep -c "^Axiom" runtime/RuntimeGuardian.v      # Must return 0
grep -c "^Theorem U_001" runtime/RuntimeGuardian.v  # Must return 35
```

===============================================================================================================
OUTPUT FORMAT:
===============================================================================================================

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* RuntimeGuardian.v` and end with the final `Qed.`

TRUST NOTHING. NOT EVEN THE SILICON. NOT EVEN THE ATOMS.

===============================================================================================================
```
