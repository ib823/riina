# DELEGATION PROMPT: N-001 TOOLING AND IDE COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
=======================================================================================================
TASK ID: N-001-TOOLING-IDE-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION - COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL - TOOLING SECURITY
=======================================================================================================

OUTPUT: `ToolingIDE.v` with 20 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Tooling and IDE Support for the RIINA programming language.
This covers developer tooling foundations, Language Server Protocol, code formatting, linting,
documentation generation, build systems, package management, debugging, and profiling.

RESEARCH REFERENCE: 01_RESEARCH/14_DOMAIN_N_TOOLING_IDE/RESEARCH_DOMAIN_N_COMPLETE.md

=======================================================================================================
REQUIRED THEOREMS (20 total):
=======================================================================================================

--- TOOLING FOUNDATIONS (N-01) ---
N_001_01: Tool output determinism (same input produces same output)
N_001_02: Tool composability (tool A | tool B = tool B after tool A)

--- LANGUAGE SERVER PROTOCOL (N-02) ---
N_001_03: LSP message well-formedness
N_001_04: Completion suggestions type-correct
N_001_05: Hover information accuracy (matches actual type)
N_001_06: Security diagnostic correctness (flagged code is actually insecure)

--- CODE FORMATTING (N-03) ---
N_001_07: Formatter idempotence (format(format(x)) = format(x))
N_001_08: Formatter semantic preservation (formatted code same meaning)
N_001_09: Security annotation visibility preservation

--- LINTING (N-04) ---
N_001_10: Lint rule soundness (flagged code has actual issue)
N_001_11: Security lint detection correctness
N_001_12: No false negatives for critical security rules

--- BUILD SYSTEM (N-06) ---
N_001_13: Build determinism (same source produces same binary)
N_001_14: Incremental build correctness (only changed modules rebuilt)
N_001_15: Security hardening applied correctly (RELRO, PIE, CFI)

--- PACKAGE MANAGER (N-07) ---
N_001_16: Dependency resolution termination
N_001_17: Package signature verification correctness
N_001_18: Vulnerability check completeness (all known CVEs flagged)

--- DEBUGGING (N-08) ---
N_001_19: Debug info accuracy (debug symbols match source)
N_001_20: Secure value redaction (secrets not leaked in debug output)

=======================================================================================================
REQUIRED STRUCTURE:
=======================================================================================================

```coq
(* ToolingIDE.v - Tooling and IDE Support for RIINA *)
(* Spec: 01_RESEARCH/14_DOMAIN_N_TOOLING_IDE/RESEARCH_DOMAIN_N_COMPLETE.md *)
(* Security Property: Tooling does not leak secrets or introduce vulnerabilities *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(* Source code representation *)
Definition SourceCode := string.

(* AST for tooling *)
Inductive ToolAST : Type :=
  | TASTVar : string -> ToolAST
  | TASTLit : nat -> ToolAST
  | TASTApp : ToolAST -> ToolAST -> ToolAST
  | TASTLam : string -> ToolAST -> ToolAST
  | TASTAnnot : string -> ToolAST -> ToolAST    (* Security annotation *)
.

(* Type information *)
Inductive TypeInfo : Type :=
  | TIBase : string -> TypeInfo
  | TIArrow : TypeInfo -> TypeInfo -> TypeInfo
  | TIEffectful : TypeInfo -> list string -> TypeInfo
.

(* LSP message types *)
Inductive LSPRequest : Type :=
  | LSPCompletion : nat -> nat -> LSPRequest        (* line, column *)
  | LSPHover : nat -> nat -> LSPRequest
  | LSPDefinition : nat -> nat -> LSPRequest
  | LSPDiagnostics : LSPRequest
.

Inductive LSPResponse : Type :=
  | LSPCompletionItems : list string -> LSPResponse
  | LSPHoverInfo : string -> TypeInfo -> LSPResponse
  | LSPLocation : nat -> nat -> LSPResponse
  | LSPDiagnosticList : list Diagnostic -> LSPResponse
with Diagnostic : Type :=
  | DiagError : nat -> nat -> string -> Diagnostic
  | DiagWarning : nat -> nat -> string -> Diagnostic
  | DiagSecurityWarning : nat -> nat -> string -> Diagnostic
.

(* Lint rule *)
Record LintRule : Type := mkLintRule {
  lr_name : string;
  lr_category : string;       (* "security", "style", "correctness" *)
  lr_severity : nat;          (* 1=info, 2=warning, 3=error *)
}.

(* Build configuration *)
Record BuildConfig : Type := mkBuildConfig {
  bc_optimization : nat;
  bc_debug_info : bool;
  bc_security_hardening : bool;
  bc_relro : bool;
  bc_pie : bool;
  bc_cfi : bool;
}.

(* Package *)
Record Package : Type := mkPackage {
  pkg_name : string;
  pkg_version : nat * nat * nat;  (* major, minor, patch *)
  pkg_signature : option string;   (* Cryptographic signature *)
  pkg_checksum : string;
}.

(* Vulnerability *)
Record Vulnerability : Type := mkVuln {
  vuln_id : string;
  vuln_package : string;
  vuln_severity : nat;
  vuln_fixed_version : option (nat * nat * nat);
}.

(* Debug value *)
Inductive DebugValue : Type :=
  | DVPublic : string -> DebugValue
  | DVRedacted : DebugValue               (* Secret value redacted *)
  | DVStruct : list (string * DebugValue) -> DebugValue
.

(* Semantic equivalence for formatter *)
Definition semantically_equivalent (a b : ToolAST) : Prop :=
  (* Two ASTs are semantically equivalent if they evaluate to same value *)
  True.  (* Placeholder - actual equivalence defined in proofs *)

(* Format function signature *)
Definition format_code (src : SourceCode) : SourceCode := src.  (* Placeholder *)

(* Parse function *)
Definition parse (src : SourceCode) : option ToolAST := None.  (* Placeholder *)

(* YOUR PROOFS HERE - ALL 20 THEOREMS *)
```

=======================================================================================================
FORBIDDEN ACTIONS:
=======================================================================================================

1. DO NOT use `Admitted.` - proof will be rejected
2. DO NOT use `admit.` - proof will be rejected
3. DO NOT add new `Axiom` - must use only standard library axioms
4. DO NOT change theorem names - must match N_001_01 through N_001_20
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 20 theorems

=======================================================================================================
VERIFICATION COMMANDS (must pass):
=======================================================================================================

```bash
coqc -Q . RIINA tooling/ToolingIDE.v
grep -c "Admitted\." tooling/ToolingIDE.v  # Must return 0
grep -c "admit\." tooling/ToolingIDE.v     # Must return 0
grep -c "^Axiom" tooling/ToolingIDE.v      # Must return 0
grep -c "^Theorem N_001" tooling/ToolingIDE.v  # Must return 20
```

=======================================================================================================
VALIDATION CHECKLIST:
=======================================================================================================

Before submitting, verify:

[ ] All 20 theorems are present and named N_001_01 through N_001_20
[ ] Zero occurrences of `Admitted.` in the file
[ ] Zero occurrences of `admit.` in the file
[ ] Zero new `Axiom` declarations
[ ] File compiles with `coqc` without errors
[ ] Each proof is complete and meaningful (not trivial workarounds)
[ ] LSP theorems correctly model request/response protocol
[ ] Formatter idempotence and semantic preservation proven
[ ] Security lint detection is sound (no false positives on valid code)
[ ] Debug value redaction ensures secrets never exposed

=======================================================================================================
OUTPUT FORMAT:
=======================================================================================================

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* ToolingIDE.v` and end with the final `Qed.`

=======================================================================================================
```
