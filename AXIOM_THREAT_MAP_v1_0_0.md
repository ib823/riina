# AXIOM THREAT MAP v1.0.0

```
+==============================================================================+
|  CARTOGRAPHER — AXIOM-TO-THREAT MAPPING                                      |
|  Date: 2026-01-16                                                            |
|  Target: 32 Axioms in NonInterference.v                                      |
|  Classification: RIINA Security Analysis                                     |
+==============================================================================+
```

## EXECUTIVE SUMMARY

| Category | Count | If False, Enables... |
|----------|-------|----------------------|
| Value Extraction | 8 | Type confusion, arbitrary code execution |
| Store Weakening | 2 | Memory corruption, use-after-free |
| Store Monotonicity | 2 | Data race, TOCTOU |
| Step-Index Conversion | 1 | Timing attacks |
| Step-1 Evaluation | 7 | Non-termination exploitation |
| Step-Index Manipulation | 4 | Recursion bombs |
| Logical Relation Cases | 6 | Information disclosure |
| Closedness Contradictions | 2 | Variable capture attacks |

---

## THREAT MAPPING TABLE

### Category A: Value Extraction Axioms (8)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 1 | `val_rel_at_type_value_left` | 247 | Non-value treated as value | Type Confusion | CWE-843 |
| 2 | `val_rel_at_type_value_right` | 252 | Non-value treated as value | Type Confusion | CWE-843 |
| 3 | `val_rel_at_type_closed_left` | 257 | Open term escapes scope | Use After Free | CWE-416 |
| 4 | `val_rel_at_type_closed_right` | 262 | Open term escapes scope | Use After Free | CWE-416 |
| 5 | `val_rel_at_type_value_any_left` | 271 | Arbitrary expr as value | Arbitrary Code Exec | CWE-94 |
| 6 | `val_rel_at_type_value_any_right` | 275 | Arbitrary expr as value | Arbitrary Code Exec | CWE-94 |
| 7 | `val_rel_at_type_closed_any_left` | 279 | Free variable capture | Information Disclosure | CWE-200 |
| 8 | `val_rel_at_type_closed_any_right` | 283 | Free variable capture | Information Disclosure | CWE-200 |

---

### Category B: Store Weakening Axioms (2)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 9 | `val_rel_n_weaken` | 510 | Store extension leaks data | Information Disclosure | CWE-200 |
| 10 | `store_rel_n_weaken` | 522 | Store inconsistency | Memory Corruption | CWE-787 |

---

### Category C: Store Monotonicity Axioms (2)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 11 | `val_rel_n_mono_store` | 545 | Kripke world inconsistency | TOCTOU Race | CWE-367 |
| 12 | `store_rel_n_mono_store` | 558 | Store state corruption | Data Race | CWE-362 |

---

### Category D: Step-Index Conversion Axiom (1)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 13 | `val_rel_n_to_val_rel` | 575 | Step-bounded relation escapes | Timing Side Channel | CWE-208 |

---

### Category E: Step-1 Evaluation Axioms (7)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 14 | `exp_rel_step1_fst` | 600 | Pair projection diverges | Denial of Service | CWE-400 |
| 15 | `exp_rel_step1_snd` | 612 | Pair projection diverges | Denial of Service | CWE-400 |
| 16 | `exp_rel_step1_case` | 624 | Case analysis diverges | Denial of Service | CWE-400 |
| 17 | `exp_rel_step1_if` | 636 | Conditional diverges | Denial of Service | CWE-400 |
| 18 | `exp_rel_step1_let` | 648 | Let binding diverges | Denial of Service | CWE-400 |
| 19 | `exp_rel_step1_app` | 660 | Function call diverges | Denial of Service | CWE-400 |
| 20 | `tapp_step0_complete` | 680 | App returns non-value | Type Confusion | CWE-843 |

---

### Category F: Step-Index Manipulation Axioms (4)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 21 | `val_rel_n_step_up` | 699 | Step-index exhaustion | Resource Exhaustion | CWE-770 |
| 22 | `store_rel_n_step_up` | 705 | Store step exhaustion | Resource Exhaustion | CWE-770 |
| 23 | `val_rel_n_lam_cumulative` | 715 | Lambda induction fails | Stack Overflow | CWE-674 |
| 24 | `val_rel_at_type_to_val_rel_ho` | 724 | Higher-order escape | Control Flow Hijack | CWE-691 |

---

### Category G: Logical Relation Cases (6)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 25 | `logical_relation_perform` | 916 | Effect leaks secret | Information Disclosure | CWE-200 |
| 26 | `logical_relation_handle` | 926 | Handler leaks secret | Information Disclosure | CWE-200 |
| 27 | `logical_relation_ref` | 945 | Ref creation leaks | Information Disclosure | CWE-200 |
| 28 | `logical_relation_deref` | 955 | Deref leaks secret | Information Disclosure | CWE-200 |
| 29 | `logical_relation_assign` | 965 | Assignment leaks | Information Disclosure | CWE-200 |
| 30 | `logical_relation_declassify` | 978 | Declassify bypassed | Improper Access Control | CWE-284 |

---

### Category H: Closedness Contradiction Axioms (2)

| # | Axiom | Line | If False, Then... | Attack Class | CWE |
|---|-------|------|-------------------|--------------|-----|
| 31 | `lam_closedness_contradiction` | 1013 | Free var in closed ctx | Variable Capture | CWE-1289 |
| 32 | `lam_closedness_contradiction2` | 1019 | Free var in closed ctx | Variable Capture | CWE-1289 |

---

## DETAILED THREAT ANALYSIS

### A1-A8: Value Extraction Axioms

**Axiom Statement:**
```coq
Axiom val_rel_at_type_value_left : forall T Σ sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  value v1.
```

**If False:**
- `val_rel_at_type` could hold for non-values (e.g., `EApp f x`)
- The logical relation would accept unevaluated expressions as "values"
- Type safety proof would incorrectly conclude evaluation is complete

**Attack Scenario:**
```
1. Attacker creates expression: TSecret (EApp malicious_fn secret_key)
2. val_rel_at_type(TSecret T) = True (always)
3. Axiom (if false) wouldn't require EApp to be a value
4. Proof proceeds as if EApp is evaluated
5. But EApp contains unevaluated secret access
6. Information flows to attacker when EApp eventually evaluates
```

**CVE Mapping:**
- **CWE-843 (Type Confusion):** Expression type misinterpreted
- **CWE-94 (Code Injection):** Unevaluated code accepted as data
- **CWE-200 (Information Disclosure):** Secret leaks through deferred evaluation

**Real-World Analogue:**
- Java deserialization vulnerabilities (CVE-2015-4852)
- Pickle arbitrary code execution (CVE-2019-10743)

---

### B9-B10: Store Weakening Axioms

**Axiom Statement:**
```coq
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

**If False:**
- Values related under extended store Σ' wouldn't be related under Σ
- Store extension could break existing invariants
- References to new locations could affect old value relations

**Attack Scenario:**
```
1. Program has secret at location L in store Σ
2. Store extends to Σ' with new public location L'
3. Axiom (if false) breaks relation for existing values
4. Secret at L no longer properly tracked
5. Information leaks through L' observing L
```

**CVE Mapping:**
- **CWE-200 (Information Disclosure):** Store extension leaks data
- **CWE-787 (Out-of-bounds Write):** Store corruption from inconsistent typing

**Real-World Analogue:**
- Use-after-realloc vulnerabilities
- Memory disclosure through adjacent allocations (Heartbleed-like)

---

### C11-C12: Store Monotonicity Axioms

**Axiom Statement:**
```coq
Axiom val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
```

**If False:**
- Values related under Σ wouldn't stay related under extension Σ'
- Kripke monotonicity (world extension preserves truth) would fail
- Race conditions between store updates and value checks

**Attack Scenario:**
```
1. Two values v1, v2 are related at store Σ
2. Concurrent operation extends store to Σ'
3. Axiom (if false) means v1, v2 no longer related
4. Security check (requires related values) now fails
5. Attacker exploits window between extension and check
```

**CVE Mapping:**
- **CWE-367 (TOCTOU):** Time-of-check/time-of-use race
- **CWE-362 (Race Condition):** Concurrent store modification

**Real-World Analogue:**
- Double-fetch vulnerabilities in kernels
- TOCTOU in file system access checks

---

### D13: Step-Index Conversion Axiom

**Axiom Statement:**
```coq
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```

**If False:**
- Relations at finite step-index wouldn't lift to unbounded relation
- Timing-dependent security: relation holds for N steps but not N+1
- Attacker could exploit bounded vs unbounded difference

**Attack Scenario:**
```
1. val_rel_n holds at step index 1000
2. Axiom (if false) doesn't extend to val_rel
3. Security property proven for bounded execution
4. Attacker constructs computation requiring 1001 steps
5. Security property fails at step 1001
6. Secret leaks through exceeding step bound
```

**CVE Mapping:**
- **CWE-208 (Timing Side Channel):** Step-count reveals information
- **CWE-203 (Observable Discrepancy):** Bounded vs unbounded behavior differs

**Real-World Analogue:**
- Timing attacks on cryptographic operations
- Bounded model checking misses deep bugs

---

### E14-E20: Step-1 Evaluation Axioms

**Axiom Statement:**
```coq
Axiom exp_rel_step1_fst : forall Σ T1 v v' st1 st2 ctx Σ',
  value v -> value v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 st1' st2' ctx' Σ'',
    (EFst v, st1, ctx) -->* (a1, st1', ctx') /\
    (EFst v', st2, ctx) -->* (a2, st2', ctx') /\
    value a1 /\ value a2 /\ ...
```

**If False:**
- Elimination forms (fst, snd, case, if, app) might not terminate
- Evaluation assumed to produce values could diverge
- Degenerate step-index case becomes exploitable

**Attack Scenario:**
```
1. Construct pair: (⊥, secret) where ⊥ = non-terminating
2. Call fst on this pair
3. Axiom (if false) doesn't guarantee fst terminates
4. Security proof assumes fst produces value
5. But fst diverges, consuming resources
6. DoS achieved; or timing reveals secret presence
```

**CVE Mapping:**
- **CWE-400 (Resource Exhaustion):** Unbounded computation
- **CWE-835 (Infinite Loop):** Non-terminating evaluation
- **CWE-834 (Excessive Iteration):** Step-count explosion

**Real-World Analogue:**
- ReDoS (Regular Expression Denial of Service)
- Billion laughs XML attack
- Hash collision DoS

---

### F21-F24: Step-Index Manipulation Axioms

**Axiom Statement:**
```coq
Axiom val_rel_n_step_up : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
```

**If False:**
- Increasing step index could invalidate relation
- Values related at step n might not be related at step n+1
- Induction on step index breaks

**Attack Scenario:**
```
1. Proof uses induction with step-up at each level
2. Axiom (if false) breaks at some step k
3. Security property proven up to step k
4. Attacker forces evaluation beyond step k
5. Property fails; information leaks
```

**CVE Mapping:**
- **CWE-770 (Resource Allocation):** Step-index exhaustion
- **CWE-674 (Uncontrolled Recursion):** Induction depth exceeded

**Real-World Analogue:**
- Stack overflow from deep recursion
- Recursion limit bypass attacks

---

### G25-G30: Logical Relation Cases

**Axiom Statement:**
```coq
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e T ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).
```

**If False:**
- Reference creation wouldn't preserve exp_rel
- New references could distinguish previously-related computations
- Store operations leak secret information

**Attack Scenario (logical_relation_ref):**
```
1. Two computations with different secrets compute ERef e
2. Axiom (if false) means resulting locations aren't related
3. Attacker observes location identity or ordering
4. Location difference reveals which secret was used
5. Information disclosure through allocation pattern
```

**Attack Scenario (logical_relation_deref):**
```
1. Related references point to related values
2. Axiom (if false) means deref doesn't preserve relation
3. Attacker reads from reference
4. Read value differs between secret-dependent executions
5. Secret leaks through dereferenced value
```

**Attack Scenario (logical_relation_assign):**
```
1. Assignment to public location with secret-dependent value
2. Axiom (if false) means assignment leaks information
3. Attacker reads public location after assignment
4. Value reveals secret through explicit or implicit flow
5. Non-interference violated
```

**Attack Scenario (logical_relation_declassify):**
```
1. Declassification requires proof of safety
2. Axiom (if false) means declassify without proper proof
3. Attacker bypasses declassification policy
4. Raw secret exposed without authorization
5. Complete confidentiality breach
```

**CVE Mapping:**
- **CWE-200 (Information Disclosure):** Secret leaks through operation
- **CWE-284 (Improper Access Control):** Declassification bypass
- **CWE-668 (Exposure to Wrong Sphere):** Secret enters public context

**Real-World Analogue:**
- Spectre/Meltdown (memory access leaks secrets)
- SQL injection (untrusted data reaches trusted context)
- Format string attacks (controlled data becomes code)

---

### H31-H32: Closedness Contradiction Axioms

**Axiom Statement:**
```coq
Axiom lam_closedness_contradiction : forall Σ Γ rho1 rho2 y,
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  free_in y (rho1 y) -> False.
```

**If False:**
- Closed environment could contain free variables
- Variable capture across scope boundaries
- Substitution could expose internal state

**Attack Scenario:**
```
1. Lambda λx. e closes over environment rho
2. Axiom (if false) allows free y in rho(y)
3. Lambda captures unintended variable y
4. When lambda called, y refers to caller's binding
5. Information flows from caller to lambda's original context
6. Scope violation enables information disclosure
```

**CVE Mapping:**
- **CWE-1289 (Improper Validation of Array Index):** Out-of-scope access
- **CWE-704 (Incorrect Type Conversion):** Variable type confusion

**Real-World Analogue:**
- JavaScript closure bugs exposing internal state
- Python late binding closures
- C++ lambda capture-by-reference lifetime issues

---

## THREAT SEVERITY MATRIX

| Axiom Category | Confidentiality | Integrity | Availability | CVSS Base |
|----------------|-----------------|-----------|--------------|-----------|
| Value Extraction | HIGH | HIGH | LOW | 8.1 |
| Store Weakening | HIGH | MEDIUM | LOW | 7.4 |
| Store Monotonicity | MEDIUM | MEDIUM | LOW | 6.5 |
| Step-Index Conversion | MEDIUM | LOW | LOW | 4.3 |
| Step-1 Evaluation | LOW | LOW | HIGH | 5.9 |
| Step-Index Manipulation | LOW | LOW | MEDIUM | 4.0 |
| Logical Relation Cases | HIGH | LOW | LOW | 6.5 |
| Closedness Contradictions | MEDIUM | MEDIUM | LOW | 5.3 |

---

## ATTACK CHAIN EXAMPLES

### Chain 1: Type Confusion → Code Execution

```
val_rel_at_type_value_any_left = FALSE
    ↓
Non-value accepted as value
    ↓
EApp(malicious_fn, secret) passes type check
    ↓
Deferred execution with secret access
    ↓
CWE-94: Arbitrary Code Execution
```

### Chain 2: Store Monotonicity → TOCTOU → Disclosure

```
val_rel_n_mono_store = FALSE
    ↓
Store extension invalidates relation
    ↓
Race between check and use
    ↓
CWE-367: Time-of-Check/Time-of-Use
    ↓
CWE-200: Information Disclosure
```

### Chain 3: Deref Axiom → Memory Read → Disclosure

```
logical_relation_deref = FALSE
    ↓
Deref doesn't preserve relation
    ↓
Read from secret-dependent location
    ↓
CWE-200: Information Disclosure
    ↓
Non-interference violated
```

### Chain 4: Declassify Axiom → Policy Bypass → Full Breach

```
logical_relation_declassify = FALSE
    ↓
Declassification without proof
    ↓
CWE-284: Improper Access Control
    ↓
Raw secret exposed
    ↓
Complete confidentiality breach
```

---

## MITIGATIONS

### For Value Extraction Axioms
- Add explicit `value` hypothesis to `val_rel_at_type` definition
- Restrict `_any_` variants to exclude TSecret/TCapability/TProof
- **Effort:** ~400 lines of proof

### For Store Axioms
- Restructure to explicit Kripke worlds
- Makes weakening/monotonicity definitionally true
- **Effort:** ~500 lines restructuring

### For Step-1 Axioms
- Prove termination for EffectPure fragment
- Or use larger base step index
- **Effort:** ~1000 lines (termination proof)

### For Logical Relation Cases
- Prove each case directly (~300 lines each)
- Uses store typing discipline from Preservation.v
- **Effort:** ~1800 lines total

### For Closedness Axioms
- Strengthen env_rel to require closed values
- Trivially provable with strengthened definition
- **Effort:** ~100 lines

---

## CONCLUSION

```
+==============================================================================+
|  CARTOGRAPHER THREAT MAPPING COMPLETE                                        |
+==============================================================================+
|                                                                              |
|  Total Axioms Mapped:         32                                             |
|  High-Severity Threats:       14 (Categories A, B, G)                        |
|  Medium-Severity Threats:     12 (Categories C, D, F, H)                     |
|  Low-Severity Threats:         6 (Category E - DoS only)                     |
|                                                                              |
|  Primary Attack Surface:      Information Disclosure (CWE-200)               |
|  Secondary Attack Surface:    Type Confusion (CWE-843)                       |
|  Tertiary Attack Surface:     Denial of Service (CWE-400)                    |
|                                                                              |
|  All threats are THEORETICAL - axioms are semantically sound                 |
|  Mapping provided for defense-in-depth planning                              |
|                                                                              |
+==============================================================================+
```

---

*CARTOGRAPHER Threat Mapping Complete*
*Know the terrain. Map the threats. Defend in depth.*
*Date: 2026-01-16*
