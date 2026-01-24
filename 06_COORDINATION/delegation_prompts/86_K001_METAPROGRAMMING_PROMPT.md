# DELEGATION PROMPT: K-001 METAPROGRAMMING COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
=======================================================================================================
TASK ID: K-001-METAPROGRAMMING-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION - COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL - MACRO SECURITY AND HYGIENE
=======================================================================================================

OUTPUT: `Metaprogramming.v` with 25 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Metaprogramming and Macros for the RIINA programming language.
This covers macro foundations, declarative macros, procedural macros, hygiene, compile-time
computation, derive macros, DSLs, and security-aware macro expansion.

RESEARCH REFERENCE: 01_RESEARCH/11_DOMAIN_K_METAPROGRAMMING_AND_EXISTING_SYSTEMS/RESEARCH_DOMAIN_K_COMPLETE.md

=======================================================================================================
REQUIRED THEOREMS (25 total):
=======================================================================================================

--- METAPROGRAMMING FOUNDATIONS (K-01) ---
K_001_01: Macro well-formedness (input/output are valid AST fragments)
K_001_02: Macro expansion termination (no infinite expansion)
K_001_03: No runtime code generation guarantee

--- DECLARATIVE MACROS (K-02) ---
K_001_04: Pattern matching exhaustiveness
K_001_05: Fragment type preservation (expr stays expr, stmt stays stmt)
K_001_06: Repetition expansion correctness

--- PROCEDURAL MACROS (K-03) ---
K_001_07: TokenStream well-formedness preservation
K_001_08: Derive macro generates valid impl
K_001_09: Attribute macro preserves item structure
K_001_10: Proc macro sandbox isolation

--- MACRO HYGIENE (K-04) ---
K_001_11: Hygienic macro avoids name capture
K_001_12: Macro-introduced names in separate scope
K_001_13: $crate path resolution correctness
K_001_14: Span hygiene preserves source location

--- COMPILE-TIME COMPUTATION (K-05) ---
K_001_15: Const function evaluation termination
K_001_16: Const generic well-formedness
K_001_17: Static assertion compile-time evaluation
K_001_18: Compile-time security check soundness

--- DERIVE MACROS (K-06) ---
K_001_19: Derived trait impl satisfies trait bounds
K_001_20: Field-by-field derivation correctness
K_001_21: SecureZeroize derive guarantees memory zeroing

--- DOMAIN-SPECIFIC LANGUAGES (K-07) ---
K_001_22: DSL syntax well-formedness
K_001_23: DSL semantic preservation (DSL code matches generated code)

--- MACRO AUDITING (K-09) ---
K_001_24: Macro expansion audit trail completeness
K_001_25: Security-sensitive macro expansion logging

=======================================================================================================
REQUIRED STRUCTURE:
=======================================================================================================

```coq
(* Metaprogramming.v - Metaprogramming and Macros for RIINA *)
(* Spec: 01_RESEARCH/11_DOMAIN_K_METAPROGRAMMING_AND_EXISTING_SYSTEMS/RESEARCH_DOMAIN_K_COMPLETE.md *)
(* Security Property: Hygienic macros prevent code injection *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(* AST Fragment types *)
Inductive FragmentType : Type :=
  | FTExpr : FragmentType      (* Expression *)
  | FTStmt : FragmentType      (* Statement *)
  | FTIdent : FragmentType     (* Identifier *)
  | FTType : FragmentType      (* Type *)
  | FTPattern : FragmentType   (* Pattern *)
  | FTBlock : FragmentType     (* Block *)
.

(* Token *)
Inductive Token : Type :=
  | TkIdent : string -> Token
  | TkLiteral : nat -> Token
  | TkPunct : string -> Token
  | TkGroup : list Token -> Token
.

(* Token stream *)
Definition TokenStream := list Token.

(* AST node for simplified representation *)
Inductive AST : Type :=
  | ASTVar : nat -> AST                    (* Variable with de Bruijn index *)
  | ASTLam : AST -> AST                    (* Lambda *)
  | ASTApp : AST -> AST -> AST             (* Application *)
  | ASTLet : AST -> AST -> AST             (* Let binding *)
  | ASTBlock : list AST -> AST             (* Block of statements *)
.

(* Scope identifier for hygiene *)
Definition ScopeId := nat.

(* Scoped name (hygiene tracking) *)
Record ScopedName : Type := mkScopedName {
  sn_name : string;
  sn_scope : ScopeId;
}.

(* Macro definition *)
Record MacroDef : Type := mkMacroDef {
  macro_name : string;
  macro_patterns : list (list FragmentType);  (* Input patterns *)
  macro_templates : list TokenStream;          (* Output templates *)
}.

(* Expansion context *)
Record ExpansionContext : Type := mkExpCtx {
  ctx_scope : ScopeId;
  ctx_crate : string;
  ctx_audit : bool;
}.

(* Macro expansion step *)
Inductive ExpansionStep : Type :=
  | ESInput : TokenStream -> ExpansionStep
  | ESMatched : nat -> ExpansionStep          (* Which pattern matched *)
  | ESOutput : TokenStream -> ExpansionStep
.

(* Expansion trace for auditing *)
Definition ExpansionTrace := list ExpansionStep.

(* Check if token stream is well-formed *)
Fixpoint tokens_well_formed (ts : TokenStream) : bool :=
  match ts with
  | [] => true
  | TkIdent _ :: rest => tokens_well_formed rest
  | TkLiteral _ :: rest => tokens_well_formed rest
  | TkPunct _ :: rest => tokens_well_formed rest
  | TkGroup inner :: rest => tokens_well_formed inner && tokens_well_formed rest
  end.

(* Free variables in AST *)
Fixpoint free_vars (t : AST) (depth : nat) : list nat :=
  match t with
  | ASTVar n => if Nat.ltb n depth then [] else [n - depth]
  | ASTLam body => free_vars body (S depth)
  | ASTApp t1 t2 => free_vars t1 depth ++ free_vars t2 depth
  | ASTLet e body => free_vars e depth ++ free_vars body (S depth)
  | ASTBlock stmts => flat_map (fun s => free_vars s depth) stmts
  end.

(* Const evaluation result *)
Inductive ConstResult : Type :=
  | CRValue : nat -> ConstResult
  | CRBool : bool -> ConstResult
  | CRUnit : ConstResult
  | CRError : string -> ConstResult
.

(* YOUR PROOFS HERE - ALL 25 THEOREMS *)
```

=======================================================================================================
FORBIDDEN ACTIONS:
=======================================================================================================

1. DO NOT use `Admitted.` - proof will be rejected
2. DO NOT use `admit.` - proof will be rejected
3. DO NOT add new `Axiom` - must use only standard library axioms
4. DO NOT change theorem names - must match K_001_01 through K_001_25
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 25 theorems

=======================================================================================================
VERIFICATION COMMANDS (must pass):
=======================================================================================================

```bash
coqc -Q . RIINA metaprogramming/Metaprogramming.v
grep -c "Admitted\." metaprogramming/Metaprogramming.v  # Must return 0
grep -c "admit\." metaprogramming/Metaprogramming.v     # Must return 0
grep -c "^Axiom" metaprogramming/Metaprogramming.v      # Must return 0
grep -c "^Theorem K_001" metaprogramming/Metaprogramming.v  # Must return 25
```

=======================================================================================================
VALIDATION CHECKLIST:
=======================================================================================================

Before submitting, verify:

[ ] All 25 theorems are present and named K_001_01 through K_001_25
[ ] Zero occurrences of `Admitted.` in the file
[ ] Zero occurrences of `admit.` in the file
[ ] Zero new `Axiom` declarations
[ ] File compiles with `coqc` without errors
[ ] Each proof is complete and meaningful (not trivial workarounds)
[ ] Hygiene theorems use de Bruijn indices or explicit scopes
[ ] Termination proofs use well-founded recursion
[ ] Security-sensitive macro auditing is modeled correctly
[ ] Token stream well-formedness is preserved through expansion

=======================================================================================================
OUTPUT FORMAT:
=======================================================================================================

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* Metaprogramming.v` and end with the final `Qed.`

=======================================================================================================
```
