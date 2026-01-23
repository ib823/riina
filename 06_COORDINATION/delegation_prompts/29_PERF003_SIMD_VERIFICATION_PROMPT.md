# DELEGATION PROMPT: PERF-003 SIMD VERIFICATION COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: PERF-003-SIMD-VERIFICATION-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — VECTORIZATION SAFETY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `SIMDVerification.v` with 12 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for SIMD (Single Instruction Multiple Data) verification
for the RIINA programming language. SIMD verification ensures vectorized code produces
the same results as scalar code - critical for performance-critical systems.

RESEARCH REFERENCE: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ (~500 lines on SIMD)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (12 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

PERF_003_01: SIMD add equivalence (vadd(a,b) = map2 (+) a b)
PERF_003_02: SIMD mul equivalence (vmul(a,b) = map2 (*) a b)
PERF_003_03: SIMD comparison equivalence (vcmp(a,b) = map2 cmp a b)
PERF_003_04: SIMD shuffle correctness (permute indices respected)
PERF_003_05: SIMD alignment requirement (aligned access ⇔ no UB)
PERF_003_06: SIMD lane independence (no cross-lane interference)
PERF_003_07: SIMD reduction equivalence (vreduce (+) v = fold (+) 0 v)
PERF_003_08: SIMD broadcast correctness (vbroadcast x = replicate n x)
PERF_003_09: SIMD gather/scatter safety (indices in bounds)
PERF_003_10: SIMD masking correctness (masked ops respect predicate)
PERF_003_11: Vectorization legality (loop vectorizable ⇔ no carried deps)
PERF_003_12: SIMD semantic preservation (scalar = vectorized)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* SIMDVerification.v - SIMD Verification for RIINA *)
(* Spec: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ *)
(* Safety Property: Vectorized code semantically equivalent to scalar *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Vectors.Vector.
Import ListNotations.
Import VectorNotations.

(* SIMD vector width *)
Definition VWidth := 4.  (* 128-bit with 32-bit elements *)

(* SIMD vector type *)
Definition SIMDVec := Vector.t nat VWidth.

(* Scalar operations *)
Definition scalar_add (a b : nat) : nat := a + b.
Definition scalar_mul (a b : nat) : nat := a * b.
Definition scalar_cmp (a b : nat) : bool := Nat.leb a b.

(* SIMD operations modeled as vector operations *)
Definition simd_add (a b : SIMDVec) : SIMDVec :=
  Vector.map2 scalar_add a b.

Definition simd_mul (a b : SIMDVec) : SIMDVec :=
  Vector.map2 scalar_mul a b.

Definition simd_cmp (a b : SIMDVec) : Vector.t bool VWidth :=
  Vector.map2 scalar_cmp a b.

(* Broadcast: replicate scalar to all lanes *)
Definition simd_broadcast (x : nat) : SIMDVec :=
  Vector.const x VWidth.

(* Reduction: fold all lanes *)
Definition simd_reduce (op : nat -> nat -> nat) (init : nat) (v : SIMDVec) : nat :=
  Vector.fold_left op init v.

(* Shuffle with permutation *)
Definition simd_shuffle (v : SIMDVec) (perm : Vector.t (Fin.t VWidth) VWidth) : SIMDVec :=
  Vector.map (fun i => Vector.nth v i) perm.

(* Alignment check *)
Definition is_aligned (addr : nat) (alignment : nat) : bool :=
  Nat.eqb (Nat.modulo addr alignment) 0.

(* Mask type *)
Definition SIMDMask := Vector.t bool VWidth.

(* Masked operation *)
Definition simd_masked_add (mask : SIMDMask) (a b old : SIMDVec) : SIMDVec :=
  Vector.map2 (fun m ab => if fst ab then snd (fst (snd ab)) + snd (snd ab) else fst (fst (snd ab)))
    (Vector.map2 pair mask (Vector.map2 (fun ov nv => (ov, nv))
      (Vector.map2 pair old a) b)) (Vector.const tt VWidth).

(* Loop with potential dependency *)
Record Loop : Type := mkLoop {
  loop_iterations : nat;
  loop_body_reads : list nat;    (* Memory locations read *)
  loop_body_writes : list nat;   (* Memory locations written *)
}.

(* Dependency check: write-after-read or read-after-write across iterations *)
Definition has_carried_dependency (l : Loop) : bool :=
  existsb (fun w => existsb (Nat.eqb w) (loop_body_reads l)) (loop_body_writes l).

(* Vectorizable iff no carried dependencies *)
Definition vectorizable (l : Loop) : bool :=
  negb (has_carried_dependency l).

(* YOUR PROOFS HERE - ALL 12 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match PERF_003_01 through PERF_003_12
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 12 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA performance/SIMDVerification.v
grep -c "Admitted\." performance/SIMDVerification.v  # Must return 0
grep -c "admit\." performance/SIMDVerification.v     # Must return 0
grep -c "^Axiom" performance/SIMDVerification.v      # Must return 0
grep -c "^Theorem PERF_003" performance/SIMDVerification.v  # Must return 12
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* SIMDVerification.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
