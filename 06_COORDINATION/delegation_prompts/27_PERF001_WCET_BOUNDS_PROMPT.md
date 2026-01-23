# DELEGATION PROMPT: PERF-001 WCET BOUNDS COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: PERF-001-WCET-BOUNDS-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — REAL-TIME SAFETY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `WCETBounds.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Worst-Case Execution Time (WCET) bounds for the RIINA
programming language. WCET bounds are CRITICAL for safety-critical systems (automotive,
aerospace, medical) where missing a deadline can cause catastrophic failure.

RESEARCH REFERENCE: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ (~5,000 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

PERF_001_01: Constant time operation bound (unit operations take O(1))
PERF_001_02: Sequential composition bound (WCET(s1;s2) ≤ WCET(s1) + WCET(s2))
PERF_001_03: Branch bound (WCET(if) ≤ WCET(cond) + max(WCET(then), WCET(else)))
PERF_001_04: Loop bound with iteration count (WCET(for i<n) ≤ n * WCET(body) + overhead)
PERF_001_05: Function call bound (WCET(call f) ≤ WCET(f) + call_overhead)
PERF_001_06: Recursion depth bound (WCET(rec f n) ≤ n * WCET(f_body))
PERF_001_07: Memory access bound (WCET(load/store) ≤ cache_miss_latency)
PERF_001_08: Pipeline stall bound (WCET includes pipeline flush cost)
PERF_001_09: Interrupt disabled bound (critical section WCET with no preemption)
PERF_001_10: DMA transfer bound (WCET(dma) ≤ transfer_size / bandwidth)
PERF_001_11: Cache analysis bound (cache state abstraction sound)
PERF_001_12: WCET monotonicity (fewer iterations → lower WCET)
PERF_001_13: WCET additivity (parallel WCET ≤ max of components)
PERF_001_14: Safe WCET margin (reported WCET ≥ actual worst case)
PERF_001_15: Real-time schedulability (∑WCET_i/period_i ≤ utilization_bound)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* WCETBounds.v - Worst-Case Execution Time Bounds for RIINA *)
(* Spec: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ *)
(* Safety Property: Guaranteed timing bounds for real-time systems *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Time units (clock cycles) *)
Definition Time := nat.

(* Hardware parameters *)
Record HWParams : Type := mkHW {
  hw_cache_hit : Time;        (* L1 cache hit latency *)
  hw_cache_miss : Time;       (* Cache miss latency *)
  hw_call_overhead : Time;    (* Function call overhead *)
  hw_branch_penalty : Time;   (* Branch misprediction cost *)
  hw_pipeline_depth : nat;    (* Pipeline stages *)
}.

(* Default conservative parameters *)
Definition default_hw : HWParams := mkHW 1 100 5 10 5.

(* Statement types *)
Inductive Stmt : Type :=
  | SUnit : Stmt                           (* No-op *)
  | SAssign : nat -> nat -> Stmt           (* x := v *)
  | SLoad : nat -> nat -> Stmt             (* x := *ptr *)
  | SStore : nat -> nat -> Stmt            (* *ptr := v *)
  | SSeq : Stmt -> Stmt -> Stmt            (* s1; s2 *)
  | SIf : nat -> Stmt -> Stmt -> Stmt      (* if c then s1 else s2 *)
  | SFor : nat -> Stmt -> Stmt             (* for i < n do s *)
  | SCall : nat -> Stmt                    (* call f *)
.

(* WCET calculation function *)
Fixpoint wcet (hw : HWParams) (s : Stmt) : Time :=
  match s with
  | SUnit => 1
  | SAssign _ _ => 1
  | SLoad _ _ => hw_cache_miss hw    (* Conservative: assume miss *)
  | SStore _ _ => hw_cache_miss hw
  | SSeq s1 s2 => wcet hw s1 + wcet hw s2
  | SIf _ s1 s2 => 1 + hw_branch_penalty hw + max (wcet hw s1) (wcet hw s2)
  | SFor n body => n * wcet hw body + n + 1  (* Loop overhead *)
  | SCall f => hw_call_overhead hw + f       (* f is function WCET *)
  end.

(* Task model for schedulability *)
Record Task : Type := mkTask {
  task_wcet : Time;
  task_period : Time;
  task_deadline : Time
}.

(* Utilization *)
Definition utilization (t : Task) : nat :=
  (task_wcet t * 100) / task_period t.  (* Percentage *)

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
KEY INSIGHT FOR PROOFS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

WCET bounds are about UPPER BOUNDS. The proofs must show:
1. The calculated WCET is always ≥ actual execution time
2. Compositional rules preserve the bound property
3. Hardware parameters represent worst-case scenarios

Use `lia` tactic for arithmetic reasoning.
Use induction on statement structure for compositional proofs.

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match PERF_001_01 through PERF_001_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA performance/WCETBounds.v
grep -c "Admitted\." performance/WCETBounds.v  # Must return 0
grep -c "admit\." performance/WCETBounds.v     # Must return 0
grep -c "^Axiom" performance/WCETBounds.v      # Must return 0
grep -c "^Theorem PERF_001" performance/WCETBounds.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* WCETBounds.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
