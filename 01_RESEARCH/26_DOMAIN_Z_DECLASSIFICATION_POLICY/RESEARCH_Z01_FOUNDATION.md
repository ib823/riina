# TERAS-LANG Research Domain Z: Declassification Policy Language

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-Z-DECLASSIFICATION-POLICY |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | Z: Declassification Policy Language |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# Z-01: The "Intentional Leak" Problem & The TERAS Solution

## 1. The Existential Threat

**Context:**
Non-interference says: "Secrets cannot influence public outputs."
**The Reality:**
Sometimes we MUST release information:
- Password checking: Must reveal "correct" or "incorrect"
- Encryption: Ciphertext is derived from plaintext
- Statistics: Aggregate data from individual records
- Logging: Error messages may contain sensitive context

**The Problem:**
Without controlled declassification, non-interference is too strong—it forbids ALL useful programs that process secrets.

**The Current TERAS Reality:**
`EDeclassify` in `Syntax.v` requires a proof (`declass_ok`), but this is just a syntactic check. It does not express:
- WHO is authorized to declassify
- WHAT data can be declassified
- WHEN declassification is permitted
- HOW MUCH can be declassified (budgets)

**The Goal:**
Define a **Declassification Policy Language** that makes intentional releases:
- Explicit (visible in code)
- Authorized (checked against policy)
- Auditable (logged)
- Bounded (limited by budgets)

## 2. The Solution: Principled Declassification

### 2.1 The Four Dimensions of Declassification

| Dimension | Question | Mechanism |
|-----------|----------|-----------|
| **WHO** | Who can declassify? | Principal-based authorization |
| **WHAT** | What data? | Data type restrictions |
| **WHEN** | Under what conditions? | Guard predicates |
| **HOW MUCH** | Quantitative limit? | Information budgets |

### 2.2 Policy Language Syntax

```
policy PasswordCheck {
  principal: Authenticator
  what: Hash<Password>
  when: login_attempt_count < MAX_ATTEMPTS
  budget: 1 bit per attempt (accept/reject)
}

policy AggregateStats {
  principal: DataAnalyst
  what: Aggregate<UserData>
  when: group_size >= K_ANONYMITY_THRESHOLD
  budget: epsilon-differential privacy
}

policy ErrorLogging {
  principal: Logger
  what: ErrorContext
  when: is_sanitized(context)
  budget: unlimited (sanitized data only)
}
```

### 2.3 Robust Declassification

**Key Property:** The DECISION to declassify cannot depend on secret data.

**BAD (attacker-controlled):**
```
if (secret_bit) {
  declassify(secret);  // Attacker can probe secret_bit
}
```

**GOOD (robust):**
```
// Public condition
if (user_requested_data && is_authorized(user)) {
  declassify(compute_public_summary(secret));
}
```

**Formal Definition:**
$$
\text{robust}(e) \iff \forall s_1, s_2. \text{low\_equiv}(s_1, s_2) \implies \text{declassifies}(e, s_1) = \text{declassifies}(e, s_2)
$$

The set of declassified values is the same regardless of secret inputs.

## 3. The Mathematical Framework

### 3.1 Principals and Authority

```coq
(* Principals form a lattice *)
Inductive principal : Type :=
  | User : user_id -> principal
  | Role : role_name -> principal
  | System : principal
  | Join : principal -> principal -> principal  (* p1 ⊔ p2 *)
  | Meet : principal -> principal -> principal. (* p1 ⊓ p2 *)

(* Acts-for relation *)
Definition acts_for (p1 p2 : principal) : Prop := ...

(* Declassification authority *)
Definition can_declassify (p : principal) (l_from l_to : security_level) : Prop :=
  acts_for p (owner l_from) /\ level_leq l_to (clearance p).
```

### 3.2 Declassification Policies

```coq
Record DeclassPolicy := {
  (* Who can invoke this policy *)
  authorized_principal : principal;

  (* What type of data *)
  source_type : ty;
  target_type : ty;

  (* Transformation function *)
  transform : source_type -> target_type;

  (* Guard predicate (must be public) *)
  guard : public_state -> bool;

  (* Budget (bits of information) *)
  budget : nat;

  (* Proof that transform is bounded *)
  transform_bounded : forall x, mutual_information(x, transform(x)) <= budget;

  (* Proof that guard is robust *)
  guard_robust : forall s1 s2, low_equiv(s1, s2) -> guard(s1) = guard(s2);
}.
```

### 3.3 Extended Typing Rule

```coq
| T_Declassify_Policy : forall G S D e policy proof_term,
    (* Expression has secret type *)
    has_type G S D e (TSecret policy.source_type) eps1 ->

    (* Principal is authorized *)
    can_declassify (current_principal D) Secret Public ->

    (* Policy guard is satisfied *)
    has_type G S D (policy.guard) TBool EffectPure ->
    eval (policy.guard) = true ->

    (* Budget not exceeded *)
    budget_remaining D >= policy.budget ->

    (* Proof of authorization *)
    valid_auth_proof proof_term policy (current_principal D) ->

    (* Result is declassified *)
    has_type G S D
      (EDeclassify_Policy e policy proof_term)
      policy.target_type
      eps1
```

## 4. Architecture of Domain Z

### 4.1 Policy Enforcement Points

```
┌─────────────────────────────────────────┐
│         Application Code                 │
│     declassify(secret, policy)          │
├─────────────────────────────────────────┤
│       Policy Checker (Compile-Time)      │
│  - Authorization verification           │
│  - Guard robustness check               │
│  - Budget static analysis               │
├─────────────────────────────────────────┤
│       Runtime Monitor (Track U)          │
│  - Dynamic budget tracking              │
│  - Audit logging                        │
│  - Rate limiting                        │
├─────────────────────────────────────────┤
│       Audit Log (Immutable)             │
│  - WHO declassified                     │
│  - WHAT was declassified                │
│  - WHEN it happened                     │
│  - HOW MUCH budget consumed             │
└─────────────────────────────────────────┘
```

### 4.2 Budget Tracking

```coq
(* Budget state per principal *)
Record BudgetState := {
  principal : principal;
  policy_budgets : policy_id -> nat;  (* Remaining budget per policy *)
  total_leaked : nat;                  (* Total bits declassified *)
  time_window : timestamp;            (* Reset period *)
}.

(* Budget consumption *)
Definition consume_budget (bs: BudgetState) (policy: DeclassPolicy) (bits: nat)
  : option BudgetState :=
  if bs.policy_budgets(policy.id) >= bits then
    Some {| bs with
      policy_budgets := update bs.policy_budgets policy.id (minus bits);
      total_leaked := bs.total_leaked + bits
    |}
  else
    None.  (* Budget exceeded, declassification denied *)
```

### 4.3 Differential Privacy Integration

For statistical queries, integrate differential privacy:

```coq
(* Differential privacy mechanism *)
Definition dp_declassify (epsilon delta : R) (query : Database -> R) (db : Database)
  : R :=
  let sensitivity := compute_sensitivity query in
  let noise := laplace_noise (sensitivity / epsilon) in
  query db + noise.

(* Privacy budget tracking *)
Theorem dp_composition : forall epsilon1 epsilon2 delta1 delta2 q1 q2 db,
  (epsilon1, delta1)-DP(q1, db) ->
  (epsilon2, delta2)-DP(q2, db) ->
  (epsilon1 + epsilon2, delta1 + delta2)-DP(compose q1 q2, db).
```

## 5. Security Properties

### 5.1 Gradual Release

Information is released only as permitted by policies:

$$
\text{released}(e, s) \subseteq \bigcup_{p \in \text{policies}} \text{allowed}(p, s)
$$

### 5.2 Bounded Leakage

Total information leaked is bounded:

$$
I(\text{secrets}; \text{outputs}) \leq \sum_{p \in \text{used\_policies}} \text{budget}(p)
$$

### 5.3 Robustness

Attacker cannot influence what gets declassified:

$$
\forall s_1, s_2. \text{low\_equiv}(s_1, s_2) \implies \text{public\_output}(P, s_1) = \text{public\_output}(P, s_2)
$$

### 5.4 Non-Circumvention

No declassification without policy:

$$
\forall e. \text{type}(e) = \text{Secret } T \implies \text{Public}(\text{eval}(e)) \text{ only via } \text{EDeclassify\_Policy}
$$

## 6. Implementation Strategy (Infinite Timeline)

1. **Step 1: Define Policy Language**
   - Syntax and semantics in Coq
   - Parser for policy files
   - Integration with type system

2. **Step 2: Implement Robustness Checker**
   - Static analysis for guard conditions
   - Prove guards don't depend on secrets

3. **Step 3: Budget System**
   - Compile-time budget analysis
   - Runtime budget enforcement
   - Budget reset mechanisms

4. **Step 4: Audit System**
   - Tamper-proof logging
   - Query interface for auditors
   - Compliance reporting

5. **Step 5: Advanced Policies**
   - Differential privacy integration
   - Multi-party declassification
   - Time-based policies

## 7. Obsolescence of Threats

- **Covert Channels:** MITIGATED. Budget limits information flow.
- **Side Channel via Declassification:** OBSOLETE. Robustness ensures attacker can't probe.
- **Unauthorized Disclosure:** OBSOLETE. Principal-based authorization enforced.
- **Audit Evasion:** OBSOLETE. All declassifications logged immutably.
- **Budget Exhaustion Attacks:** MITIGATED. Rate limiting and alerts.
- **Policy Circumvention:** OBSOLETE. Type system enforces policy use.

## 8. Dependencies

| Dependency | Direction | Nature |
|------------|-----------|--------|
| Track A (Formal) | Z extends A | Security type system |
| Track A (Non-interference) | Z extends | Declassification semantics |
| Track U (Guardian) | Z integrates with U | Runtime budget enforcement |
| Track Y (Stdlib) | Z feeds Y | Crypto declassification policies |

## 9. Example Policies

### 9.1 Password Checking
```
policy password_check {
  principal: AuthenticationService
  what: bool  // Only accept/reject
  when: attempts_in_window < 5
  budget: 1 bit
  audit: REQUIRED
}
```

### 9.2 Medical Data Analytics
```
policy medical_aggregate {
  principal: ResearchAnalyst
  what: Aggregate<PatientRecord>
  when: cohort_size >= 100  // K-anonymity
  budget: (1.0, 1e-5)-differential_privacy
  audit: REQUIRED
  approval: IRB_NUMBER_12345
}
```

### 9.3 Error Logging
```
policy error_log {
  principal: SystemLogger
  what: SanitizedError
  when: is_sanitized(error) && !contains_pii(error)
  budget: unlimited  // Sanitized data is public
  audit: OPTIONAL
}
```

---

**"Declassification is not a loophole. Declassification is a POLICY, and policies are PROVEN."**
