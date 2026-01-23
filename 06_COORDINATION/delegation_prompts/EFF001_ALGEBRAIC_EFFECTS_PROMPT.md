# DELEGATION PROMPT: EFF-001 ALGEBRAIC EFFECTS COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: EFF-001-ALGEBRAIC-EFFECTS-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — EFFECT SYSTEM FOUNDATION
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `AlgebraicEffects.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Algebraic Effects for the RIINA programming language.
Algebraic effects provide a principled approach to side effects, enabling modular
reasoning about I/O, state, exceptions, and other computational effects.

RESEARCH REFERENCE: 01_RESEARCH/02_DOMAIN_B_EFFECTS/ (~10,192 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

EFF_001_01: Effect signature well-formedness
EFF_001_02: Operation typing (op : A → B ∈ Σ implies perform op a : B ! Σ)
EFF_001_03: Handler typing (handler h : E ! Σ → E' ! Σ')
EFF_001_04: Effect row combination (Σ₁ ∪ Σ₂ well-formed)
EFF_001_05: Effect subsumption (E ! Σ <: E ! Σ' when Σ ⊆ Σ')
EFF_001_06: Pure computation (e : A ! ∅ implies no effects)
EFF_001_07: Handler composition (h₁ ∘ h₂ correctly handles Σ₁ ∪ Σ₂)
EFF_001_08: Effect polymorphism (∀Σ. A ! Σ → B ! Σ)
EFF_001_09: Deep handler semantics (recursively handles resumed computation)
EFF_001_10: Shallow handler semantics (handles one operation, returns)
EFF_001_11: Effect masking (handler for Σ removes Σ from effect row)
EFF_001_12: Resumption linearity (continuation used exactly once)
EFF_001_13: Effect safety (unhandled effects are type errors)
EFF_001_14: Effect parametricity (effect-polymorphic functions respect effects)
EFF_001_15: Effect coherence (different evaluation orders same result for pure)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* AlgebraicEffects.v - Algebraic Effects for RIINA *)
(* Spec: 01_RESEARCH/02_DOMAIN_B_EFFECTS/ *)
(* Security Property: Controlled side effects *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Base types *)
Inductive BaseTy : Type :=
  | TUnit : BaseTy
  | TBool : BaseTy
  | TNat : BaseTy
.

(* Effect operations *)
Inductive EffectOp : Type :=
  | OpRead : EffectOp           (* State read *)
  | OpWrite : EffectOp          (* State write *)
  | OpRaise : EffectOp          (* Exception raise *)
  | OpPrint : EffectOp          (* I/O print *)
  | OpRandom : EffectOp         (* Non-determinism *)
  | OpAsync : EffectOp          (* Async operation *)
.

(* Effect signature (set of operations) *)
Definition EffectSig := list EffectOp.

(* Effect row *)
Definition EffectRow := EffectSig.

(* Computation type: A ! Σ *)
Inductive CompTy : Type :=
  | CTyPure : BaseTy -> CompTy                      (* A ! ∅ *)
  | CTyEff : BaseTy -> EffectRow -> CompTy          (* A ! Σ *)
.

(* Terms *)
Inductive Comp : Type :=
  | CReturn : nat -> Comp                           (* return v *)
  | CPerform : EffectOp -> nat -> Comp              (* perform op v *)
  | CHandle : Comp -> Handler -> Comp               (* handle c with h *)
  | CBind : Comp -> Comp -> Comp                    (* c >>= k *)
with Handler : Type :=
  | HReturn : Comp -> Handler                       (* return case *)
  | HOp : EffectOp -> Comp -> Handler -> Handler    (* operation case *)
.

(* Effect row membership *)
Definition in_row (op : EffectOp) (row : EffectRow) : bool :=
  existsb (fun o => match op, o with
    | OpRead, OpRead => true
    | OpWrite, OpWrite => true
    | OpRaise, OpRaise => true
    | OpPrint, OpPrint => true
    | OpRandom, OpRandom => true
    | OpAsync, OpAsync => true
    | _, _ => false
  end) row.

(* Effect row subset *)
Definition row_subset (r1 r2 : EffectRow) : bool :=
  forallb (fun op => in_row op r2) r1.

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match EFF_001_01 through EFF_001_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA effects/AlgebraicEffects.v
grep -c "Admitted\." effects/AlgebraicEffects.v  # Must return 0
grep -c "admit\." effects/AlgebraicEffects.v     # Must return 0
grep -c "^Axiom" effects/AlgebraicEffects.v      # Must return 0
grep -c "^Theorem EFF_001" effects/AlgebraicEffects.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* AlgebraicEffects.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
