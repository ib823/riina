# DELEGATION PROMPT: V-001 TERMINATION GUARANTEES COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
===============================================================================================================
TASK ID: V-001-TERMINATION-GUARANTEES-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: HIGH — TERMINATION AND STRONG NORMALIZATION
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
===============================================================================================================

OUTPUT: `TerminationGuarantees.v` with 32 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA Termination Guarantees — proofs that all RIINA
programs terminate (or are explicitly marked non-terminating). The Halting Problem is
undecidable in general, but we RESTRICT the language to a decidable, terminating subset.

RESEARCH REFERENCE: 01_RESEARCH/22_DOMAIN_V_TERMINATION_GUARANTEES/RESEARCH_V01_FOUNDATION.md

THAT WHICH DOES NOT TERMINATE DOES NOT EXIST IN RIINA — UNLESS EXPLICITLY CAGED.
NO INFINITE LOOPS. NO DoS. NO RESOURCE EXHAUSTION.

===============================================================================================================
REQUIRED THEOREMS (32 total):
===============================================================================================================

STRUCTURAL RECURSION (8 theorems):
V_001_01: structural_decrease — Recursive calls on structurally smaller arguments
V_001_02: structural_termination — Structural recursion implies termination
V_001_03: nat_structural — Nat recursion terminates
V_001_04: list_structural — List recursion terminates
V_001_05: tree_structural — Tree recursion terminates
V_001_06: mutual_structural — Mutual recursion on structural decrease terminates
V_001_07: nested_structural — Nested recursion terminates if structural
V_001_08: structural_checker_sound — Structural recursion checker is sound

SIZED TYPES (8 theorems):
V_001_09: sized_type_wellformed — Sized types are well-formed
V_001_10: size_decreases — Size annotations decrease through computation
V_001_11: sized_list_terminates — Sized list operations terminate
V_001_12: sized_tree_terminates — Sized tree operations terminate
V_001_13: size_inference_correct — Size inference is correct
V_001_14: size_subtyping — Sized type subtyping is sound
V_001_15: sized_preservation — Size is preserved through evaluation
V_001_16: sized_composition — Sized types compose correctly

WELL-FOUNDED RECURSION (8 theorems):
V_001_17: measure_wellformed — Measure functions are well-founded
V_001_18: measure_decreases — Measure decreases at recursive calls
V_001_19: lexicographic_wellformed — Lexicographic ordering is well-founded
V_001_20: ackermann_terminates — Ackermann function terminates
V_001_21: complex_measure_sound — Complex measures are sound
V_001_22: measure_inference — Measure inference is correct
V_001_23: measure_composition — Measure composition is valid
V_001_24: wellfounded_checker_sound — Well-founded recursion checker is sound

PRODUCTIVITY FOR CODATA (8 theorems):
V_001_25: codata_productive — Codata definitions are productive
V_001_26: stream_productive — Stream operations are productive
V_001_27: productivity_observe — Observing k elements terminates
V_001_28: guarded_recursion — Guarded recursion is productive
V_001_29: codata_unfold — Codata unfolds productively
V_001_30: productive_composition — Productivity composes
V_001_31: non_terminating_marked — Non-terminating code is explicitly marked
V_001_32: strong_normalization — Pure RIINA subset is strongly normalizing

===============================================================================================================
REQUIRED STRUCTURE:
===============================================================================================================

```coq
(* TerminationGuarantees.v - RIINA Termination Verification *)
(* Spec: 01_RESEARCH/22_DOMAIN_V_TERMINATION_GUARANTEES/RESEARCH_V01_FOUNDATION.md *)
(* Layer: Type System Extension *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Wellfounded.Wellfounded.
Require Import Coq.Init.Wf.
Import ListNotations.

(** ===============================================================================
    STRUCTURAL RECURSION
    =============================================================================== *)

(* Expression *)
Inductive expr : Type :=
  | EVar : nat -> expr
  | EConst : nat -> expr
  | EApp : expr -> expr -> expr
  | ELam : expr -> expr
  | ERec : nat -> expr -> expr  (* Recursive binding *)
  | ECase : expr -> list (nat * expr) -> expr.

(* Structural size *)
Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EVar _ => 1
  | EConst _ => 1
  | EApp e1 e2 => 1 + expr_size e1 + expr_size e2
  | ELam e => 1 + expr_size e
  | ERec _ e => 1 + expr_size e
  | ECase e branches => 1 + expr_size e +
      fold_left (fun acc p => acc + expr_size (snd p)) branches 0
  end.

(* Structural decrease relation *)
Definition structurally_smaller (e1 e2 : expr) : Prop :=
  expr_size e1 < expr_size e2.

(* Structural recursion: recursive calls only on smaller args *)
Definition structural_recursion (e : expr) : Prop :=
  forall e_rec arg,
    recursive_call e e_rec arg ->
    structurally_smaller arg e.

(** ===============================================================================
    SIZED TYPES
    =============================================================================== *)

(* Size annotation *)
Definition Size := nat.

(* Sized type *)
Inductive sized_ty : Type :=
  | STNat : Size -> sized_ty
  | STList : sized_ty -> Size -> sized_ty
  | STTree : sized_ty -> Size -> sized_ty
  | STFun : sized_ty -> sized_ty -> sized_ty.

(* Size extraction *)
Definition get_size (st : sized_ty) : option Size :=
  match st with
  | STNat s => Some s
  | STList _ s => Some s
  | STTree _ s => Some s
  | STFun _ _ => None
  end.

(* Size subtyping *)
Definition size_subtype (s1 s2 : Size) : Prop :=
  s1 <= s2.

(** ===============================================================================
    WELL-FOUNDED RECURSION
    =============================================================================== *)

(* Measure function type *)
Definition Measure (A : Type) := A -> nat.

(* Well-founded measure *)
Definition wf_measure {A : Type} (m : Measure A) : Prop :=
  well_founded (fun x y => m x < m y).

(* Lexicographic ordering *)
Definition lex_order {A B : Type} (ma : Measure A) (mb : Measure B)
  : A * B -> A * B -> Prop :=
  fun p1 p2 =>
    ma (fst p1) < ma (fst p2) \/
    (ma (fst p1) = ma (fst p2) /\ mb (snd p1) < mb (snd p2)).

(** ===============================================================================
    CODATA AND PRODUCTIVITY
    =============================================================================== *)

(* Codata stream *)
CoInductive Stream (A : Type) : Type :=
  | SCons : A -> Stream A -> Stream A.

(* Observation depth *)
Fixpoint observe {A : Type} (n : nat) (s : Stream A) : list A :=
  match n with
  | 0 => []
  | S n' => match s with
            | SCons x xs => x :: observe n' xs
            end
  end.

(* Productivity: observing always terminates *)
Definition productive {A : Type} (s : Stream A) : Prop :=
  forall n, exists l, observe n s = l.

(* Guarded recursion marker *)
Inductive Guarded (A : Type) : Type :=
  | Later : A -> Guarded A.

(** ===============================================================================
    TERMINATION CHECKING
    =============================================================================== *)

(* Termination evidence *)
Inductive terminates : expr -> Prop :=
  | T_Var : forall n, terminates (EVar n)
  | T_Const : forall n, terminates (EConst n)
  | T_Structural : forall e,
      structural_recursion e ->
      terminates e
  | T_Measure : forall e m,
      wf_measure m ->
      decreases_on m e ->
      terminates e.

(* Termination checker *)
Definition check_termination (e : expr) : bool :=
  true.  (* Placeholder - real impl does analysis *)

(** ===============================================================================
    YOUR PROOFS: V_001_01 through V_001_32
    =============================================================================== *)

(* Implement all 32 theorems here *)
```

===============================================================================================================
THEOREM SPECIFICATIONS:
===============================================================================================================

```coq
(* V_001_02: Structural recursion implies termination *)
Theorem structural_termination : forall e,
  structural_recursion e ->
  terminates e.

(* V_001_10: Size annotations decrease through computation *)
Theorem size_decreases : forall e e' st st',
  has_sized_type e st ->
  step e e' ->
  has_sized_type e' st' ->
  recursive_call e e' ->
  size_less st' st.

(* V_001_20: Ackermann function terminates *)
Theorem ackermann_terminates : forall m n,
  exists v, ackermann m n = v.

(* V_001_27: Observing k elements terminates *)
Theorem productivity_observe : forall A (s : Stream A) k,
  exists l, observe k s = l /\ length l = k.

(* V_001_32: Pure RIINA subset is strongly normalizing *)
Theorem strong_normalization : forall e,
  pure e ->
  well_typed e ->
  exists v, eval_star e v /\ is_value v.
```

===============================================================================================================
FORBIDDEN ACTIONS:
===============================================================================================================

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match V_001_01 through V_001_32
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 32 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

===============================================================================================================
VERIFICATION COMMANDS (must pass):
===============================================================================================================

```bash
coqc -Q . RIINA termination/TerminationGuarantees.v
grep -c "Admitted\." termination/TerminationGuarantees.v  # Must return 0
grep -c "admit\." termination/TerminationGuarantees.v     # Must return 0
grep -c "^Axiom" termination/TerminationGuarantees.v      # Must return 0
grep -c "^Theorem V_001" termination/TerminationGuarantees.v  # Must return 32
```

===============================================================================================================
OUTPUT FORMAT:
===============================================================================================================

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* TerminationGuarantees.v` and end with the final `Qed.`

THAT WHICH DOES NOT TERMINATE DOES NOT EXIST IN RIINA — UNLESS EXPLICITLY CAGED.

===============================================================================================================
```
