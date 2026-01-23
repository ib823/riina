# DELEGATION PROMPT: COMPILE-001 TRANSLATION VALIDATION COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: COMPILE-001-TRANSLATION-VALIDATION-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — COMPILER CERTIFICATION
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `TranslationValidation.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Translation Validation for the RIINA compiler.
Translation validation proves that compiler output preserves the semantics of the
source program - essential for trusting optimized code in safety-critical systems.

RESEARCH REFERENCE: 01_RESEARCH/18_DOMAIN_R_CERTIFIED_COMPILATION/ (~113 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

COMPILE_001_01: Semantic preservation (source ≃ target behavior)
COMPILE_001_02: Type preservation (well-typed source → well-typed target)
COMPILE_001_03: Effect preservation (source effects = target effects)
COMPILE_001_04: Termination preservation (source terminates ↔ target terminates)
COMPILE_001_05: Value correspondence (source values ≃ target values)
COMPILE_001_06: Memory layout correspondence (source memory ≃ target memory)
COMPILE_001_07: Call convention compliance (ABI respected)
COMPILE_001_08: Constant propagation correctness
COMPILE_001_09: Dead code elimination correctness
COMPILE_001_10: Inlining correctness (inlined function = call)
COMPILE_001_11: Loop unrolling correctness (unrolled = original)
COMPILE_001_12: Register allocation correctness (no value corruption)
COMPILE_001_13: Instruction selection correctness (IR → machine equivalent)
COMPILE_001_14: Stack frame layout correctness
COMPILE_001_15: Whole program simulation (trace equivalence)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* TranslationValidation.v - Translation Validation for RIINA Compiler *)
(* Spec: 01_RESEARCH/18_DOMAIN_R_CERTIFIED_COMPILATION/ *)
(* Based on: CompCert methodology *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Source language (simplified RIINA) *)
Inductive SrcExpr : Type :=
  | SVar : nat -> SrcExpr
  | SConst : nat -> SrcExpr
  | SAdd : SrcExpr -> SrcExpr -> SrcExpr
  | SMul : SrcExpr -> SrcExpr -> SrcExpr
  | SIf : SrcExpr -> SrcExpr -> SrcExpr -> SrcExpr
  | SCall : nat -> list SrcExpr -> SrcExpr
  | SLet : nat -> SrcExpr -> SrcExpr -> SrcExpr
.

(* Target language (simplified IR) *)
Inductive TgtInstr : Type :=
  | TLoad : nat -> nat -> TgtInstr          (* dst, src_addr *)
  | TStore : nat -> nat -> TgtInstr         (* dst_addr, src *)
  | TAdd : nat -> nat -> nat -> TgtInstr    (* dst, src1, src2 *)
  | TMul : nat -> nat -> nat -> TgtInstr    (* dst, src1, src2 *)
  | TBranch : nat -> TgtInstr               (* target *)
  | TBranchIf : nat -> nat -> nat -> TgtInstr  (* cond, true_target, false_target *)
  | TCall : nat -> list nat -> TgtInstr     (* func_id, args *)
  | TReturn : nat -> TgtInstr               (* result *)
.

Definition TgtProgram := list TgtInstr.

(* Source values *)
Inductive SrcVal : Type :=
  | SVInt : nat -> SrcVal
  | SVBool : bool -> SrcVal
  | SVUnit : SrcVal
.

(* Target values *)
Inductive TgtVal : Type :=
  | TVInt : nat -> TgtVal
  | TVUndef : TgtVal
.

(* Value correspondence *)
Definition val_match (sv : SrcVal) (tv : TgtVal) : bool :=
  match sv, tv with
  | SVInt n, TVInt m => Nat.eqb n m
  | SVBool true, TVInt 1 => true
  | SVBool false, TVInt 0 => true
  | SVUnit, TVInt 0 => true
  | _, _ => false
  end.

(* Source environment *)
Definition SrcEnv := list (nat * SrcVal).

(* Target register file *)
Definition TgtRegs := list (nat * TgtVal).

(* Environment correspondence *)
Definition env_match (se : SrcEnv) (tr : TgtRegs) (mapping : list (nat * nat)) : bool :=
  forallb (fun pair =>
    let svar := fst pair in
    let treg := snd pair in
    match find (fun p => Nat.eqb (fst p) svar) se,
          find (fun p => Nat.eqb (fst p) treg) tr with
    | Some (_, sv), Some (_, tv) => val_match sv tv
    | _, _ => false
    end
  ) mapping.

(* Source semantics (big-step) *)
Inductive src_eval : SrcEnv -> SrcExpr -> SrcVal -> Prop :=
  | EVar : forall env x v,
      In (x, v) env -> src_eval env (SVar x) v
  | EConst : forall env n,
      src_eval env (SConst n) (SVInt n)
  | EAdd : forall env e1 e2 n1 n2,
      src_eval env e1 (SVInt n1) ->
      src_eval env e2 (SVInt n2) ->
      src_eval env (SAdd e1 e2) (SVInt (n1 + n2))
  | EMul : forall env e1 e2 n1 n2,
      src_eval env e1 (SVInt n1) ->
      src_eval env e2 (SVInt n2) ->
      src_eval env (SMul e1 e2) (SVInt (n1 * n2))
.

(* Target semantics (small-step) *)
Record TgtState : Type := mkTS {
  ts_pc : nat;
  ts_regs : TgtRegs;
  ts_memory : list (nat * TgtVal);
}.

Inductive tgt_step : TgtProgram -> TgtState -> TgtState -> Prop :=
  | StepAdd : forall prog pc regs mem dst s1 s2 v1 v2,
      nth_error prog pc = Some (TAdd dst s1 s2) ->
      In (s1, TVInt v1) regs ->
      In (s2, TVInt v2) regs ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS (S pc) ((dst, TVInt (v1 + v2)) :: regs) mem)
.

(* Simulation relation *)
Definition simulates (se : SrcEnv) (sv : SrcVal) (ts : TgtState) (result_reg : nat) : Prop :=
  exists tv, In (result_reg, tv) (ts_regs ts) /\ val_match sv tv = true.

(* Compilation function type *)
Definition compile := SrcExpr -> TgtProgram.

(* Effect type *)
Inductive Effect : Type :=
  | EffPure : Effect
  | EffRead : nat -> Effect
  | EffWrite : nat -> nat -> Effect
.

(* Trace (sequence of effects) *)
Definition Trace := list Effect.

(* Trace equivalence *)
Definition trace_equiv (t1 t2 : Trace) : bool :=
  (length t1 =? length t2) &&
  forallb (fun pair =>
    match fst pair, snd pair with
    | EffPure, EffPure => true
    | EffRead a1, EffRead a2 => Nat.eqb a1 a2
    | EffWrite a1 v1, EffWrite a2 v2 => andb (Nat.eqb a1 a2) (Nat.eqb v1 v2)
    | _, _ => false
    end
  ) (combine t1 t2).

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match COMPILE_001_01 through COMPILE_001_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA compiler/TranslationValidation.v
grep -c "Admitted\." compiler/TranslationValidation.v  # Must return 0
grep -c "admit\." compiler/TranslationValidation.v     # Must return 0
grep -c "^Axiom" compiler/TranslationValidation.v      # Must return 0
grep -c "^Theorem COMPILE_001" compiler/TranslationValidation.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* TranslationValidation.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
