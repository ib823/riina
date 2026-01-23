# DELEGATION PROMPT: TYPE-003 SESSION TYPES COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: TYPE-003-SESSION-TYPES-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — COMMUNICATION SAFETY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `SessionTypes.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Session Types for the RIINA programming language.
Session types guarantee communication protocol adherence - preventing protocol violations,
deadlocks, and message type mismatches.

RESEARCH REFERENCE: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/session_types/ (~3,000 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

TYPE_003_01: Session type duality (S dual of dual(S) = S)
TYPE_003_02: Send/Receive duality (!T.S dual ↔ ?T.dual(S))
TYPE_003_03: Choice/Branch duality (⊕{l:S} dual ↔ &{l:dual(S)})
TYPE_003_04: Session end duality (end dual ↔ end)
TYPE_003_05: Session fidelity (typed process follows protocol)
TYPE_003_06: Session safety (no stuck configurations)
TYPE_003_07: Deadlock freedom (progress for session-typed processes)
TYPE_003_08: Session composition (parallel composition preserves typing)
TYPE_003_09: Channel restriction (new channel maintains invariants)
TYPE_003_10: Recursive session unfolding (μX.S = S[μX.S/X])
TYPE_003_11: Session subtyping (covariant sends, contravariant receives)
TYPE_003_12: Linearity of channels (each channel used exactly once per step)
TYPE_003_13: Session delegation (channel passing preserves types)
TYPE_003_14: Global type projection (global ↦ local types consistent)
TYPE_003_15: Multiparty session safety (n-party protocol adherence)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* SessionTypes.v - Session Types for RIINA *)
(* Spec: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/session_types/ *)
(* Security Property: Protocol adherence, deadlock freedom *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Base types for messages *)
Inductive BaseTy : Type :=
  | BTUnit : BaseTy
  | BTBool : BaseTy
  | BTNat : BaseTy
.

(* Session types *)
Inductive SessionTy : Type :=
  | SSend : BaseTy -> SessionTy -> SessionTy    (* !T.S - send T then continue as S *)
  | SRecv : BaseTy -> SessionTy -> SessionTy    (* ?T.S - receive T then continue as S *)
  | SChoice : list SessionTy -> SessionTy       (* ⊕{S₁, S₂, ...} - internal choice *)
  | SBranch : list SessionTy -> SessionTy       (* &{S₁, S₂, ...} - external choice *)
  | SEnd : SessionTy                            (* end - session termination *)
  | SRec : SessionTy -> SessionTy               (* μX.S - recursive session *)
  | SVar : nat -> SessionTy                     (* X - recursion variable *)
.

(* Duality function *)
Fixpoint dual (s : SessionTy) : SessionTy :=
  match s with
  | SSend t s' => SRecv t (dual s')
  | SRecv t s' => SSend t (dual s')
  | SChoice ss => SBranch (map dual ss)
  | SBranch ss => SChoice (map dual ss)
  | SEnd => SEnd
  | SRec s' => SRec (dual s')
  | SVar n => SVar n
  end.

(* Channel endpoints *)
Definition ChanEnv := list (nat * SessionTy).

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match TYPE_003_01 through TYPE_003_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA concurrency/SessionTypes.v
grep -c "Admitted\." concurrency/SessionTypes.v  # Must return 0
grep -c "admit\." concurrency/SessionTypes.v     # Must return 0
grep -c "^Axiom" concurrency/SessionTypes.v      # Must return 0
grep -c "^Theorem TYPE_003" concurrency/SessionTypes.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* SessionTypes.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
