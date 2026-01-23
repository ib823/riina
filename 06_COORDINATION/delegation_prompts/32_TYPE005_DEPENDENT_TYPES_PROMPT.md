# DELEGATION PROMPT: TYPE-005 DEPENDENT TYPES COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: TYPE-005-DEPENDENT-TYPES-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — TYPE SYSTEM FOUNDATION
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `DependentTypes.v` with 14 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Dependent Types for the RIINA programming language.
Dependent types allow types to depend on values, enabling precise specifications
like "array of length n" or "sorted list" directly in the type system.

RESEARCH REFERENCE: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/dependent_types/ (~8,000 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (14 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

TYPE_005_01: Dependent function type formation (Πx:A.B[x] well-formed)
TYPE_005_02: Dependent function introduction (λx:A.b : Πx:A.B[x])
TYPE_005_03: Dependent function elimination ((f : Πx:A.B[x]) a : B[a])
TYPE_005_04: Dependent pair type formation (Σx:A.B[x] well-formed)
TYPE_005_05: Dependent pair introduction ((a,b) : Σx:A.B[x] when b:B[a])
TYPE_005_06: Dependent pair elimination (projections preserve dependencies)
TYPE_005_07: Length-indexed vector type (Vec A n type formation)
TYPE_005_08: Vector cons preserves length (cons : A → Vec A n → Vec A (S n))
TYPE_005_09: Vector head requires non-empty (head : Vec A (S n) → A)
TYPE_005_10: Dependent pattern matching (Π elimination with motive)
TYPE_005_11: Transport along equality (transport : (P : A → Type) → x = y → P x → P y)
TYPE_005_12: Congruence (f x = f y when x = y)
TYPE_005_13: Dependent induction principle (well-founded recursion)
TYPE_005_14: Decidable equality reflection (Dec (x = y) for appropriate types)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* DependentTypes.v - Dependent Types for RIINA *)
(* Spec: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/dependent_types/ *)
(* Security Property: Type-level value dependencies *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Vectors.Vector.
Require Import Coq.Logic.Eqdep_dec.
Import ListNotations.

(* Universe levels *)
Definition Universe := nat.

(* Dependent type syntax *)
Inductive DTy : Universe -> Type :=
  | DUnit : forall u, DTy u
  | DNat : forall u, DTy u
  | DPi : forall u, DTy u -> (nat -> DTy u) -> DTy u      (* Πx:A.B[x] *)
  | DSigma : forall u, DTy u -> (nat -> DTy u) -> DTy u   (* Σx:A.B[x] *)
  | DId : forall u, DTy u -> nat -> nat -> DTy u          (* x =_A y *)
  | DVec : forall u, DTy u -> nat -> DTy u                (* Vec A n *)
  | DUniv : forall u, DTy (S u)                           (* Type_u *)
.

(* Dependent terms *)
Inductive DTerm : Type :=
  | DVar : nat -> DTerm
  | DLam : DTy 0 -> DTerm -> DTerm                        (* λx:A.b *)
  | DApp : DTerm -> DTerm -> DTerm                        (* f a *)
  | DPair : DTerm -> DTerm -> DTerm                       (* (a, b) *)
  | DFst : DTerm -> DTerm                                 (* π₁ *)
  | DSnd : DTerm -> DTerm                                 (* π₂ *)
  | DRefl : DTerm                                         (* refl *)
  | DJ : DTerm -> DTerm -> DTerm -> DTerm -> DTerm        (* J eliminator *)
  | DNil : DTy 0 -> DTerm                                 (* nil : Vec A 0 *)
  | DCons : DTerm -> DTerm -> DTerm                       (* cons : A → Vec A n → Vec A (S n) *)
  | DHead : DTerm -> DTerm                                (* head : Vec A (S n) → A *)
  | DTail : DTerm -> DTerm                                (* tail : Vec A (S n) → Vec A n *)
.

(* Typing context *)
Definition DCtx := list (DTy 0).

(* YOUR PROOFS HERE - ALL 14 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match TYPE_005_01 through TYPE_005_14
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 14 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA foundations/DependentTypes.v
grep -c "Admitted\." foundations/DependentTypes.v  # Must return 0
grep -c "admit\." foundations/DependentTypes.v     # Must return 0
grep -c "^Axiom" foundations/DependentTypes.v      # Must return 0
grep -c "^Theorem TYPE_005" foundations/DependentTypes.v  # Must return 14
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* DependentTypes.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
