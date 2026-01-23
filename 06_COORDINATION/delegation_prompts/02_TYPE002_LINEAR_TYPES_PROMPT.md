# DELEGATION PROMPT: TYPE-002 LINEAR TYPES COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: TYPE-002-LINEAR-TYPES-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — TYPE SYSTEM LAYER
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `LinearTypes.v` with 12 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Linear Type System for the RIINA programming language.
Linear types ensure resources are used exactly once - critical for memory safety and
preventing use-after-free vulnerabilities.

RESEARCH REFERENCE: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/linear_types/ (~5,000 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (12 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

TYPE_002_01: Linear variable used exactly once
TYPE_002_02: Unrestricted variable (!) can be used multiple times
TYPE_002_03: Linear function application consumes argument
TYPE_002_04: Affine type (used at most once) subsumes linear
TYPE_002_05: Relevant type (used at least once) subsumes linear
TYPE_002_06: Context split lemma (Γ = Γ₁ ⊎ Γ₂)
TYPE_002_07: Linear substitution preserves linearity
TYPE_002_08: Weakening forbidden for linear contexts
TYPE_002_09: Contraction forbidden for linear contexts
TYPE_002_10: Linear pairs consume both components
TYPE_002_11: Linear let-binding transfers ownership
TYPE_002_12: Resource safety (no use-after-consume)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* LinearTypes.v - Linear Type System for RIINA *)
(* Spec: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/linear_types/ *)
(* Security Property: Resource used exactly once *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Linearity qualifiers *)
Inductive Linearity : Type :=
  | Lin    (* Linear: exactly once *)
  | Aff    (* Affine: at most once *)
  | Rel    (* Relevant: at least once *)
  | Unr    (* Unrestricted: any number *)
.

(* Subqualifier relation *)
Definition subqual (q1 q2 : Linearity) : bool :=
  match q1, q2 with
  | Lin, Lin => true
  | Lin, Aff => true
  | Lin, Rel => true
  | Aff, Aff => true
  | Rel, Rel => true
  | Unr, Unr => true
  | Unr, _ => true
  | _, _ => false
  end.

(* Linear types *)
Inductive LTy : Type :=
  | LUnit : LTy
  | LBool : LTy
  | LFun : Linearity -> LTy -> LTy -> LTy    (* q A ⊸ B *)
  | LPair : Linearity -> LTy -> LTy -> LTy   (* A ⊗ B *)
  | LBang : LTy -> LTy                        (* !A *)
.

(* Usage count *)
Inductive Usage : Type :=
  | Zero : Usage
  | One : Usage
  | Many : Usage
.

(* Context with usage tracking *)
Definition LCtx := list (LTy * Usage).

(* YOUR PROOFS HERE - ALL 12 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match TYPE_002_01 through TYPE_002_12
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 12 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA foundations/LinearTypes.v
grep -c "Admitted\." foundations/LinearTypes.v  # Must return 0
grep -c "admit\." foundations/LinearTypes.v     # Must return 0
grep -c "^Axiom" foundations/LinearTypes.v      # Must return 0
grep -c "^Theorem TYPE_002" foundations/LinearTypes.v  # Must return 12
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* LinearTypes.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
