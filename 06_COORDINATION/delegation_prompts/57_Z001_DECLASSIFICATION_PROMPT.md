# DELEGATION PROMPT: Z-001 DECLASSIFICATION POLICY COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
===============================================================================================================
TASK ID: Z-001-DECLASSIFICATION-POLICY-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: HIGH — ROBUST DECLASSIFICATION WITH BUDGETS
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
===============================================================================================================

OUTPUT: `DeclassificationPolicy.v` with 35 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA Declassification Policy — the formal language
for controlled information release. Non-interference is too strong; we need intentional
leaks for password checking, encryption, statistics. We make them EXPLICIT and PROVABLE.

RESEARCH REFERENCE: 01_RESEARCH/26_DOMAIN_Z_DECLASSIFICATION_POLICY/RESEARCH_Z01_FOUNDATION.md

DECLASSIFICATION IS NOT A LOOPHOLE. DECLASSIFICATION IS A POLICY, AND POLICIES ARE PROVEN.
WHO, WHAT, WHEN, HOW MUCH — ALL MUST BE SPECIFIED AND VERIFIED.

===============================================================================================================
REQUIRED THEOREMS (35 total):
===============================================================================================================

PRINCIPAL AND AUTHORITY (7 theorems):
Z_001_01: principal_lattice — Principals form a lattice
Z_001_02: acts_for_transitive — Acts-for relation is transitive
Z_001_03: acts_for_reflexive — Acts-for relation is reflexive
Z_001_04: authority_delegation — Authority can be delegated
Z_001_05: authority_bounded — Delegated authority is bounded by delegator
Z_001_06: principal_join — Principal join is least upper bound
Z_001_07: principal_meet — Principal meet is greatest lower bound

ROBUST DECLASSIFICATION (8 theorems):
Z_001_08: robust_definition — Robustness is well-defined
Z_001_09: robust_guard — Guard must be public (not secret-dependent)
Z_001_10: robust_decision — Declassification decision is robust
Z_001_11: robust_composition — Robustness composes
Z_001_12: no_attacker_controlled — Attacker cannot control declassification
Z_001_13: robust_preserves_ni — Robustness preserves non-interference elsewhere
Z_001_14: downgrade_bounded — Downgrade is bounded by policy
Z_001_15: robust_checker_sound — Robustness checker is sound

INFORMATION BUDGETS (8 theorems):
Z_001_16: budget_wellformed — Budget specification is well-formed
Z_001_17: budget_consumption — Budget is consumed on declassification
Z_001_18: budget_exhaustion — Exhausted budget prevents declassification
Z_001_19: budget_reset — Budget reset is controlled
Z_001_20: total_leakage_bounded — Total leakage is bounded by budget
Z_001_21: mutual_information_bounded — Mutual information <= budget
Z_001_22: budget_composition — Budgets compose additively
Z_001_23: budget_per_principal — Budgets are per-principal

POLICY ENFORCEMENT (7 theorems):
Z_001_24: policy_authorized — Declassification requires authorized principal
Z_001_25: policy_guard_satisfied — Guard must be satisfied
Z_001_26: policy_transform_applied — Transform function is applied
Z_001_27: policy_audit_logged — All declassifications are logged
Z_001_28: policy_no_bypass — No declassification without policy
Z_001_29: policy_composition — Policies compose safely
Z_001_30: policy_revocation — Revoked policies are ineffective

DIFFERENTIAL PRIVACY INTEGRATION (5 theorems):
Z_001_31: dp_definition — Differential privacy is well-defined
Z_001_32: dp_composition — DP composes with budget tracking
Z_001_33: dp_laplace_correct — Laplace mechanism is (eps,0)-DP
Z_001_34: dp_gaussian_correct — Gaussian mechanism is (eps,delta)-DP
Z_001_35: dp_privacy_budget — DP privacy budget is tracked

===============================================================================================================
REQUIRED STRUCTURE:
===============================================================================================================

```coq
(* DeclassificationPolicy.v - RIINA Declassification Policy Verification *)
(* Spec: 01_RESEARCH/26_DOMAIN_Z_DECLASSIFICATION_POLICY/RESEARCH_Z01_FOUNDATION.md *)
(* Layer: Information Flow Control *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(** ===============================================================================
    PRINCIPALS AND AUTHORITY
    =============================================================================== *)

(* Principal identifier *)
Definition PrincipalId := nat.

(* Principal *)
Inductive Principal : Type :=
  | PUser : PrincipalId -> Principal
  | PRole : nat -> Principal
  | PSystem : Principal
  | PJoin : Principal -> Principal -> Principal   (* Least upper bound *)
  | PMeet : Principal -> Principal -> Principal.  (* Greatest lower bound *)

(* Acts-for relation *)
Definition acts_for (p1 p2 : Principal) : Prop :=
  True.  (* Placeholder - real impl checks delegation *)

(* Principal lattice ordering *)
Definition principal_leq (p1 p2 : Principal) : Prop :=
  acts_for p1 p2.

(** ===============================================================================
    SECURITY LEVELS
    =============================================================================== *)

(* Security level *)
Inductive SecurityLevel : Type :=
  | Public : SecurityLevel
  | Secret : SecurityLevel
  | TopSecret : SecurityLevel.

(* Level ordering *)
Definition level_leq (l1 l2 : SecurityLevel) : bool :=
  match l1, l2 with
  | Public, _ => true
  | Secret, Secret => true
  | Secret, TopSecret => true
  | TopSecret, TopSecret => true
  | _, _ => false
  end.

(* Owner of a security level *)
Definition owner (l : SecurityLevel) : Principal :=
  PSystem.  (* Placeholder *)

(** ===============================================================================
    DECLASSIFICATION POLICY
    =============================================================================== *)

(* Type representation *)
Definition Ty := nat.

(* Declassification policy *)
Record DeclassPolicy : Type := mkPolicy {
  policy_id : nat;
  authorized_principal : Principal;
  source_level : SecurityLevel;
  target_level : SecurityLevel;
  source_type : Ty;
  target_type : Ty;
  guard : nat -> bool;              (* Public guard condition *)
  transform : nat -> nat;           (* Transformation function *)
  budget : nat;                     (* Information budget in bits *)
}.

(* Policy is valid *)
Definition valid_policy (p : DeclassPolicy) : Prop :=
  level_leq (target_level p) (source_level p) = true /\
  budget p > 0.

(** ===============================================================================
    BUDGET TRACKING
    =============================================================================== *)

(* Budget state *)
Record BudgetState : Type := mkBudget {
  budget_principal : Principal;
  budget_per_policy : nat -> nat;   (* policy_id -> remaining budget *)
  total_leaked : nat;               (* Total bits declassified *)
  budget_window : nat;              (* Time window for reset *)
}.

(* Consume budget *)
Definition consume_budget (bs : BudgetState) (policy_id : nat) (bits : nat)
  : option BudgetState :=
  let remaining := budget_per_policy bs policy_id in
  if remaining <? bits then None
  else Some {|
    budget_principal := budget_principal bs;
    budget_per_policy := fun id =>
      if Nat.eqb id policy_id
      then remaining - bits
      else budget_per_policy bs id;
    total_leaked := total_leaked bs + bits;
    budget_window := budget_window bs
  |}.

(** ===============================================================================
    ROBUST DECLASSIFICATION
    =============================================================================== *)

(* State *)
Definition State := nat -> nat.  (* Variable -> Value *)

(* Low equivalence (agree on public data) *)
Definition low_equiv (s1 s2 : State) (public : nat -> bool) : Prop :=
  forall x, public x = true -> s1 x = s2 x.

(* Expression *)
Definition Expr := State -> nat.

(* Robustness: declassification decision independent of secrets *)
Definition robust (e : Expr) (public : nat -> bool) : Prop :=
  forall s1 s2,
    low_equiv s1 s2 public ->
    e s1 = e s2.

(* Declassification expression *)
Record DeclassExpr : Type := mkDeclass {
  declass_value : Expr;
  declass_policy : DeclassPolicy;
  declass_guard : Expr;  (* Must be robust *)
}.

(* Valid declassification *)
Definition valid_declass (de : DeclassExpr) (public : nat -> bool) : Prop :=
  robust (declass_guard de) public /\
  valid_policy (declass_policy de).

(** ===============================================================================
    AUDIT LOGGING
    =============================================================================== *)

(* Audit entry *)
Record AuditEntry : Type := mkAudit {
  audit_principal : Principal;
  audit_policy_id : nat;
  audit_bits_leaked : nat;
  audit_timestamp : nat;
  audit_value_hash : nat;  (* Hash of declassified value *)
}.

(* Audit log *)
Definition AuditLog := list AuditEntry.

(* Declassification creates audit entry *)
Definition logged_declass (de : DeclassExpr) (log : AuditLog) (log' : AuditLog) : Prop :=
  exists entry, log' = entry :: log /\
  audit_policy_id entry = policy_id (declass_policy de).

(** ===============================================================================
    DIFFERENTIAL PRIVACY
    =============================================================================== *)

(* Database *)
Definition Database := list nat.

(* Query *)
Definition Query := Database -> nat.

(* Sensitivity of a query *)
Definition sensitivity (q : Query) : nat :=
  1.  (* Placeholder - real impl computes max difference *)

(* (epsilon, delta)-Differential Privacy *)
Definition dp_mechanism (epsilon : nat) (delta : nat)
  (q : Query) (db : Database) (noise : nat) : nat :=
  q db + noise.

(* Differential privacy holds *)
Definition satisfies_dp (m : Query -> Database -> nat)
                        (epsilon delta : nat) : Prop :=
  forall q db1 db2,
    neighbors db1 db2 ->  (* Differ in one record *)
    True.  (* Placeholder - real impl checks probability bounds *)

(** ===============================================================================
    YOUR PROOFS: Z_001_01 through Z_001_35
    =============================================================================== *)

(* Implement all 35 theorems here *)
```

===============================================================================================================
THEOREM SPECIFICATIONS:
===============================================================================================================

```coq
(* Z_001_02: Acts-for relation is transitive *)
Theorem acts_for_transitive : forall p1 p2 p3,
  acts_for p1 p2 ->
  acts_for p2 p3 ->
  acts_for p1 p3.

(* Z_001_09: Guard must be public (not secret-dependent) *)
Theorem robust_guard : forall de public,
  valid_declass de public ->
  robust (declass_guard de) public.

(* Z_001_20: Total leakage is bounded by budget *)
Theorem total_leakage_bounded : forall bs policy_id bits bs',
  consume_budget bs policy_id bits = Some bs' ->
  total_leaked bs' <= total_leaked bs + bits.

(* Z_001_24: Declassification requires authorized principal *)
Theorem policy_authorized : forall de p,
  can_declassify de p ->
  acts_for p (authorized_principal (declass_policy de)).

(* Z_001_28: No declassification without policy *)
Theorem policy_no_bypass : forall e s s' l1 l2,
  has_level e l1 ->
  steps e s s' ->
  has_level s' l2 ->
  level_leq l2 l1 = false ->
  exists de, uses_policy e de.
```

===============================================================================================================
FORBIDDEN ACTIONS:
===============================================================================================================

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match Z_001_01 through Z_001_35
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 35 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

===============================================================================================================
VERIFICATION COMMANDS (must pass):
===============================================================================================================

```bash
coqc -Q . RIINA ifc/DeclassificationPolicy.v
grep -c "Admitted\." ifc/DeclassificationPolicy.v  # Must return 0
grep -c "admit\." ifc/DeclassificationPolicy.v     # Must return 0
grep -c "^Axiom" ifc/DeclassificationPolicy.v      # Must return 0
grep -c "^Theorem Z_001" ifc/DeclassificationPolicy.v  # Must return 35
```

===============================================================================================================
OUTPUT FORMAT:
===============================================================================================================

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* DeclassificationPolicy.v` and end with the final `Qed.`

DECLASSIFICATION IS NOT A LOOPHOLE. DECLASSIFICATION IS A POLICY, AND POLICIES ARE PROVEN.

===============================================================================================================
```
