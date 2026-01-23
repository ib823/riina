# DELEGATION PROMPT: PERF-002 BINARY SIZE BOUNDS COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: PERF-002-BINARY-SIZE-BOUNDS-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — EMBEDDED SYSTEMS SAFETY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `BinarySizeBounds.v` with 12 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Binary Size Bounds for the RIINA programming language.
Binary size bounds are CRITICAL for embedded systems where ROM/flash is limited
(medical devices, automotive ECUs, IoT sensors). Exceeding flash = device won't boot.

RESEARCH REFERENCE: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ (~200 lines on size)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (12 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

PERF_002_01: Instruction size bound (each instruction ≤ max_instr_size)
PERF_002_02: Basic block size (BB_size = Σ instruction sizes)
PERF_002_03: Function size bound (func_size = Σ basic_block sizes + prologue + epilogue)
PERF_002_04: Module size bound (module_size = Σ function sizes + data + metadata)
PERF_002_05: Program size bound (program_size = Σ module sizes + startup code)
PERF_002_06: Data section bound (data_size = Σ global variable sizes)
PERF_002_07: BSS section bound (bss_size = Σ zero-initialized sizes)
PERF_002_08: Stack frame bound (stack_frame ≤ max_locals * word_size + saved_regs)
PERF_002_09: Inline expansion bound (inline increases code size predictably)
PERF_002_10: Loop unroll bound (unroll factor n → n× body size)
PERF_002_11: Generic instantiation bound (monomorphization size predictable)
PERF_002_12: Total ROM bound (text + rodata + init_data ≤ flash_size)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* BinarySizeBounds.v - Binary Size Bounds for RIINA *)
(* Spec: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ *)
(* Safety Property: Guaranteed to fit in ROM/flash *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Size in bytes *)
Definition Size := nat.

(* Target architecture parameters *)
Record ArchParams : Type := mkArch {
  arch_word_size : Size;          (* 4 for 32-bit, 8 for 64-bit *)
  arch_max_instr_size : Size;     (* Max instruction bytes *)
  arch_call_overhead : Size;      (* Call instruction size *)
  arch_ret_overhead : Size;       (* Return instruction size *)
  arch_flash_size : Size;         (* Total flash available *)
  arch_ram_size : Size;           (* Total RAM available *)
}.

(* Common architectures *)
Definition arm_cortex_m0 : ArchParams := mkArch 4 4 4 2 65536 8192.    (* 64KB flash, 8KB RAM *)
Definition arm_cortex_m4 : ArchParams := mkArch 4 4 4 2 262144 65536.  (* 256KB flash, 64KB RAM *)
Definition riscv32 : ArchParams := mkArch 4 4 4 4 131072 32768.        (* 128KB flash, 32KB RAM *)

(* Instruction *)
Inductive Instr : Type :=
  | INop : Instr
  | IMov : Instr
  | IAdd : Instr
  | ISub : Instr
  | IMul : Instr
  | IDiv : Instr
  | ILoad : Instr
  | IStore : Instr
  | IBranch : Instr
  | ICall : Instr
  | IRet : Instr
.

(* Instruction size (conservative upper bound) *)
Definition instr_size (arch : ArchParams) (i : Instr) : Size :=
  arch_max_instr_size arch.

(* Basic block *)
Definition BasicBlock := list Instr.

(* Basic block size *)
Definition bb_size (arch : ArchParams) (bb : BasicBlock) : Size :=
  fold_left (fun acc i => acc + instr_size arch i) bb 0.

(* Function *)
Record Function : Type := mkFunc {
  func_blocks : list BasicBlock;
  func_locals : nat;              (* Local variable count *)
}.

(* Function size *)
Definition func_size (arch : ArchParams) (f : Function) : Size :=
  fold_left (fun acc bb => acc + bb_size arch bb) (func_blocks f) 0 +
  arch_call_overhead arch + arch_ret_overhead arch.

(* Module *)
Record Module : Type := mkMod {
  mod_functions : list Function;
  mod_data : Size;                (* Initialized data *)
  mod_bss : Size;                 (* Zero-initialized data *)
}.

(* Module size *)
Definition mod_size (arch : ArchParams) (m : Module) : Size :=
  fold_left (fun acc f => acc + func_size arch f) (mod_functions m) 0 +
  mod_data m.

(* Program *)
Record Program : Type := mkProg {
  prog_modules : list Module;
  prog_startup : Size;            (* Startup code size *)
}.

(* Program size *)
Definition prog_size (arch : ArchParams) (p : Program) : Size :=
  fold_left (fun acc m => acc + mod_size arch m) (prog_modules p) 0 +
  prog_startup p.

(* YOUR PROOFS HERE - ALL 12 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match PERF_002_01 through PERF_002_12
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 12 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA performance/BinarySizeBounds.v
grep -c "Admitted\." performance/BinarySizeBounds.v  # Must return 0
grep -c "admit\." performance/BinarySizeBounds.v     # Must return 0
grep -c "^Axiom" performance/BinarySizeBounds.v      # Must return 0
grep -c "^Theorem PERF_002" performance/BinarySizeBounds.v  # Must return 12
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* BinarySizeBounds.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
