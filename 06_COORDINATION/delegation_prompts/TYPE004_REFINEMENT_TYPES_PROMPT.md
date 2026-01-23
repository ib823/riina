# DELEGATION PROMPT: TYPE-004 REFINEMENT TYPES COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: TYPE-004-REFINEMENT-TYPES-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — VERIFICATION LAYER
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `RefinementTypes.v` with 12 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Refinement Types for the RIINA programming language.
Refinement types attach logical predicates to types, enabling compile-time verification
of properties like bounds checking, non-null guarantees, and invariant preservation.

RESEARCH REFERENCE: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/refinement_types/ (~4,000 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (12 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

TYPE_004_01: Refinement subtyping ({x:B | P} <: {x:B | Q} when P ⇒ Q)
TYPE_004_02: Refinement introduction (if e:B and P[e] then e:{x:B|P})
TYPE_004_03: Refinement elimination ({x:B|P} <: B)
TYPE_004_04: Refinement conjunction ({x:B|P∧Q} ≡ {x:B|P} ∩ {x:B|Q})
TYPE_004_05: Dependent function refinement (x:{v:B|P} → {w:C|Q[x]})
TYPE_004_06: Refinement substitution (well-typed substitution preserves refinements)
TYPE_004_07: SMT decidability (refinement checking via SMT is decidable for QF_LIA)
TYPE_004_08: Bounds checking ({x:nat | 0 ≤ x < len} prevents overflow)
TYPE_004_09: Non-null refinement ({x:ptr | x ≠ null} prevents null deref)
TYPE_004_10: Array bounds safety (index:{i:nat | i < len arr} → safe access)
TYPE_004_11: Positive refinement ({x:int | x > 0} closed under multiplication)
TYPE_004_12: Refinement preservation (β-reduction preserves refinements)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* RefinementTypes.v - Refinement Types for RIINA *)
(* Spec: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/refinement_types/ *)
(* Security Property: Compile-time predicate verification *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.

(* Base types *)
Inductive BaseTy : Type :=
  | TyNat : BaseTy
  | TyInt : BaseTy
  | TyBool : BaseTy
  | TyPtr : BaseTy
.

(* Predicates (simplified for SMT decidability) *)
Inductive Pred : Type :=
  | PTrue : Pred
  | PFalse : Pred
  | PEq : nat -> nat -> Pred          (* v = n *)
  | PLt : nat -> nat -> Pred          (* v < n *)
  | PLe : nat -> nat -> Pred          (* v ≤ n *)
  | PGt : nat -> nat -> Pred          (* v > n *)
  | PGe : nat -> nat -> Pred          (* v ≥ n *)
  | PNeq : nat -> nat -> Pred         (* v ≠ n *)
  | PAnd : Pred -> Pred -> Pred       (* P ∧ Q *)
  | POr : Pred -> Pred -> Pred        (* P ∨ Q *)
  | PNot : Pred -> Pred               (* ¬P *)
  | PImpl : Pred -> Pred -> Pred      (* P ⇒ Q *)
.

(* Refinement type: {x : B | P} *)
Inductive RefTy : Type :=
  | RBase : BaseTy -> RefTy                      (* unrefined base *)
  | RRefine : BaseTy -> Pred -> RefTy            (* {x:B | P} *)
  | RFun : RefTy -> RefTy -> RefTy               (* refined function *)
  | RDepFun : RefTy -> (nat -> RefTy) -> RefTy   (* dependent function *)
.

(* Predicate satisfaction *)
Fixpoint sat_pred (v : nat) (p : Pred) : Prop :=
  match p with
  | PTrue => True
  | PFalse => False
  | PEq n m => n = m
  | PLt n m => n < m
  | PLe n m => n <= m
  | PGt n m => n > m
  | PGe n m => n >= m
  | PNeq n m => n <> m
  | PAnd p1 p2 => sat_pred v p1 /\ sat_pred v p2
  | POr p1 p2 => sat_pred v p1 \/ sat_pred v p2
  | PNot p1 => ~ sat_pred v p1
  | PImpl p1 p2 => sat_pred v p1 -> sat_pred v p2
  end.

(* YOUR PROOFS HERE - ALL 12 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match TYPE_004_01 through TYPE_004_12
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 12 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA foundations/RefinementTypes.v
grep -c "Admitted\." foundations/RefinementTypes.v  # Must return 0
grep -c "admit\." foundations/RefinementTypes.v     # Must return 0
grep -c "^Axiom" foundations/RefinementTypes.v      # Must return 0
grep -c "^Theorem TYPE_004" foundations/RefinementTypes.v  # Must return 12
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* RefinementTypes.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
