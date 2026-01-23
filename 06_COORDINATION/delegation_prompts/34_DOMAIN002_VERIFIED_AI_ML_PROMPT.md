# DELEGATION PROMPT: DOMAIN-002 VERIFIED AI/ML COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: DOMAIN-002-VERIFIED-AI-ML-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — AI SAFETY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `VerifiedAIML.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Verified AI/ML for the RIINA programming language.
These proofs ensure AI/ML systems are safe, robust, and behave within specified bounds.
Critical for autonomous vehicles, medical AI, financial trading systems.

RESEARCH REFERENCE: 01_RESEARCH/15_DOMAIN_ν_VERIFIED_AI/ (~600 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

DOMAIN_002_01: Neural network output bounded (outputs ∈ [min, max])
DOMAIN_002_02: Lipschitz continuity (small input change → bounded output change)
DOMAIN_002_03: Adversarial robustness (ε-perturbation doesn't change classification)
DOMAIN_002_04: Softmax normalization (outputs sum to 1)
DOMAIN_002_05: ReLU monotonicity (x ≤ y → ReLU(x) ≤ ReLU(y))
DOMAIN_002_06: Matrix multiplication associativity (verified linear algebra)
DOMAIN_002_07: Gradient descent convergence (loss decreases under conditions)
DOMAIN_002_08: Inference determinism (same input → same output)
DOMAIN_002_09: Numerical stability (no NaN/Inf in computation)
DOMAIN_002_10: Model integrity (weights unchanged during inference)
DOMAIN_002_11: Input validation (reject out-of-distribution inputs)
DOMAIN_002_12: Confidence calibration (confidence reflects accuracy)
DOMAIN_002_13: Fairness constraint (predictions satisfy fairness metric)
DOMAIN_002_14: Explanation faithfulness (LIME/SHAP reflects true importance)
DOMAIN_002_15: Safe action space (autonomous system actions within bounds)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* VerifiedAIML.v - Verified AI/ML for RIINA *)
(* Spec: 01_RESEARCH/15_DOMAIN_ν_VERIFIED_AI/ *)
(* Domain: Autonomous vehicles, medical AI, trading systems *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

(* Fixed-point representation for numerical stability *)
(* Using nat * nat for (integer, fractional) parts *)
Record FixedPoint : Type := mkFP {
  fp_int : Z;
  fp_frac : nat;      (* Fractional part, scaled by 10000 *)
  fp_scale : nat;     (* Scale factor *)
}.

(* Simplified real number operations using rationals *)
Definition RVal := (Z * Z)%type.  (* Numerator / Denominator *)

Definition rval_add (a b : RVal) : RVal :=
  let (an, ad) := a in
  let (bn, bd) := b in
  ((an * bd + bn * ad)%Z, (ad * bd)%Z).

(* Neural network layer *)
Inductive Layer : Type :=
  | Dense : nat -> nat -> Layer           (* input_dim, output_dim *)
  | ReLU : Layer
  | Softmax : Layer
  | Sigmoid : Layer
.

(* Neural network *)
Definition Network := list Layer.

(* Activation functions (simplified integer approximation) *)
Definition relu (x : Z) : Z := Z.max 0 x.

Definition sigmoid_approx (x : Z) : Z :=
  (* Approximation: 0 if x < -4, 1 if x > 4, linear in between *)
  if Z.ltb x (-4) then 0
  else if Z.ltb 4 x then 1000  (* Scaled by 1000 *)
  else (500 + x * 125)%Z.      (* Linear approximation *)

(* Softmax normalization check *)
Definition softmax_valid (outputs : list Z) (scale : Z) : bool :=
  Z.eqb (fold_left Z.add outputs 0%Z) scale.

(* Lipschitz constant *)
Definition lipschitz_bound (weights : list Z) : Z :=
  fold_left Z.max (map Z.abs weights) 0%Z.

(* Adversarial perturbation *)
Definition within_epsilon (x1 x2 : Z) (epsilon : Z) : bool :=
  Z.leb (Z.abs (x1 - x2)) epsilon.

(* Input validation (in-distribution check) *)
Record InputBounds : Type := mkBounds {
  ib_min : Z;
  ib_max : Z;
}.

Definition input_valid (x : Z) (bounds : InputBounds) : bool :=
  andb (Z.leb (ib_min bounds) x) (Z.leb x (ib_max bounds)).

(* Model weights (immutable during inference) *)
Record Model : Type := mkModel {
  model_weights : list Z;
  model_hash : nat;                 (* For integrity check *)
}.

Definition model_integrity (m : Model) (expected_hash : nat) : bool :=
  Nat.eqb (model_hash m) expected_hash.

(* Confidence score *)
Definition confidence_calibrated (confidence : Z) (accuracy : Z) (tolerance : Z) : bool :=
  Z.leb (Z.abs (confidence - accuracy)) tolerance.

(* Fairness metric (demographic parity) *)
Definition demographic_parity (group_a_rate group_b_rate : Z) (threshold : Z) : bool :=
  Z.leb (Z.abs (group_a_rate - group_b_rate)) threshold.

(* Safe action bounds for autonomous systems *)
Record ActionSpace : Type := mkAction {
  action_min : Z;
  action_max : Z;
  action_rate_limit : Z;    (* Max change per step *)
}.

Definition action_safe (action prev_action : Z) (space : ActionSpace) : bool :=
  andb (andb (Z.leb (action_min space) action)
             (Z.leb action (action_max space)))
       (Z.leb (Z.abs (action - prev_action)) (action_rate_limit space)).

(* Output bounds *)
Definition output_bounded (output : Z) (min max : Z) : bool :=
  andb (Z.leb min output) (Z.leb output max).

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match DOMAIN_002_01 through DOMAIN_002_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA domains/VerifiedAIML.v
grep -c "Admitted\." domains/VerifiedAIML.v  # Must return 0
grep -c "admit\." domains/VerifiedAIML.v     # Must return 0
grep -c "^Axiom" domains/VerifiedAIML.v      # Must return 0
grep -c "^Theorem DOMAIN_002" domains/VerifiedAIML.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* VerifiedAIML.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
