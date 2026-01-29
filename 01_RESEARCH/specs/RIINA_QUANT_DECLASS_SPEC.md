# RIINA Quantitative Declassification Specification v1.0.0

**Document ID:** `RIINA_QUANT_DECLASS_SPEC_v1_0_0`  
**Status:** Draft — Theorems marked `Admitted` pending full proofs  
**Companion File:** `RIINA_QUANT_DECLASS_SPEC_v1_0_0.v` (Coq source)

---

## Executive Summary

This specification defines **quantitative declassification** for the RIINA programming language — believed to be the **first programming language** to provide type-level quantitative information flow control with compile-time budget verification.

### Key Innovation

Traditional information flow control is **qualitative**: data is either "secret" or "public." RIINA introduces **quantitative** bounds:

```
┌─────────────────────────────────────────────────────────────────┐
│  Traditional IFC:  Secret ──[declassify]──► Public              │
│                    (All or nothing)                             │
│                                                                 │
│  RIINA Quant IFC:  Secret ──[declassify, 1 bit]──► Public       │
│                    (Bounded leakage with compile-time check)    │
└─────────────────────────────────────────────────────────────────┘
```

### Core Guarantee

> **Quantitative Non-Interference Theorem:**  
> For any well-typed program with budget B bits, the mutual information between secret inputs and public outputs is at most B bits.

---

## Specification Contents

| Section | Topic | Key Definitions |
|---------|-------|-----------------|
| §2 | Information-Theoretic Foundations | Min-entropy, channel leakage, mutual information |
| §3 | Security Lattice | `LAwam ⊑ LDalaman ⊑ LSesi ⊑ LPengguna ⊑ LSistem ⊑ LRahsia` |
| §4 | Type System | Base types, labeled types, `TRahsia`, `TBukti` |
| §5 | Declassification Policies | `declassification_policy` record with budgets |
| §6 | Expressions | `EDeclassifyBudget` — the key new expression |
| §7 | Typing Rules | `T_DeclassifyBudget` — budget-consuming rule |
| §8 | Operational Semantics | `E_DeclassifyBudget` — runtime reduction |
| §9 | Security Theorems | Quantitative non-interference |
| §10 | Budget Composition | Sequential (add), branching (max+1), loops (multiply) |
| §11 | Static Analysis | Abstract budget domain, `analyze_budget` |
| §12 | Bahasa Melayu Examples | Source code patterns |
| §13 | Related Work Comparison | Jif, CHM'07, Smith'09, Mardziel'14, LIO |

---

## Declassification Policy Structure

```coq
Record declassification_policy := mkPolicy {
  policy_name : string;              (* Unique identifier *)
  leaked_type : riina_type;          (* What type escapes *)
  bit_budget : nat;                  (* Max bits per call *)
  rate : rate_limit;                 (* Invocations/window *)
  audit : audit_level;               (* Logging requirement *)
  authorized : principal;            (* Who can invoke *)
  source_level : security_level;     (* From level *)
  target_level : security_level;     (* To level *)
}.
```

### Example: Password Verification Policy

```
dasar pengesahan_kata {
    apa: Benar,                        // Leaked type: boolean
    bajet: 1 bit setiap percubaan,     // Budget: 1 bit per attempt
    had: 5 percubaan setiap minit,     // Rate limit: 5/minute
    audit: Wajib,                      // Mandatory audit
    prinsipal: PerkhidmatanPengesahan, // Auth service only
}
```

**Information-theoretic justification:** A boolean can distinguish at most 2 equivalence classes on secrets, therefore leaks at most log₂(2) = 1 bit.

---

## Budget Composition Rules

| Control Flow | Budget Rule | Intuition |
|--------------|-------------|-----------|
| Sequential `e₁; e₂` | `B₁ + B₂` | Observer sees both outputs |
| Branching `if c then e₁ else e₂` | `max(B₁, B₂) + 1` | +1 for which branch taken |
| Loop `for i in 1..n do e` | `n × B` | Each iteration leaks B |
| Function call `f(x)` | `Bf` | Callee's budget charged to caller |

---

## Type-Level Budget Checking

The typing rule `T_DeclassifyBudget` enforces:

1. **Type Consistency:** Leaked type matches policy declaration
2. **Budget Consistency:** `type_bits(τ) ≤ bit_budget(policy)`
3. **Budget Availability:** Remaining budget ≥ policy budget
4. **Authorization:** Current principal ⊇ policy principal
5. **Well-formedness:** Policy passes validation

```coq
| T_DeclassifyBudget : forall Γ B B' P e_secret e_proof pol τ,
    Γ; B; P ⊢ e_secret ∷ TLabeled τ (source_level pol) ->
    Γ; B; P ⊢ e_proof ∷ TBukti (TBase TBool) ->
    τ = leaked_type pol ->
    type_bits τ <= bit_budget pol ->
    consume_budget B (bit_budget pol) = Some B' ->
    principal_subsumes P (authorized pol) = true ->
    policy_wellformed pol = true ->
    Γ; B'; P ⊢ EDeclassifyBudget e_secret e_proof pol ∷ 
             TLabeled (leaked_type pol) (target_level pol)
```

---

## Comparison with Prior Work

| System | Quantitative? | Compile-time? | Type-level budgets? |
|--------|---------------|---------------|---------------------|
| Jif | ✗ | ✓ | ✗ |
| FlowCaml | ✗ | ✓ | ✗ |
| LIO | ✗ | ✗ | ✗ |
| CHM'07 (analysis) | ✓ | ✗ | ✗ |
| Smith'09 (theory) | ✓ | N/A | N/A |
| Mardziel'14 | ✓ | ✗ | ✗ |
| **RIINA** | **✓** | **✓** | **✓** |

---

## Proof Status

| Theorem | Status | Notes |
|---------|--------|-------|
| `quantitative_noninterference` | Admitted | Core security theorem |
| `leakage_equals_budget` | Admitted | Corollary |
| `rate_limit_security` | Proved | Simple arithmetic |
| `budget_analysis_sound` | Admitted | Soundness of static analysis |
| `progress` | Admitted | Standard |
| `preservation` | Admitted | Standard + budget tracking |

---

## Bahasa Melayu Glossary

| Malay | English | Coq Identifier |
|-------|---------|----------------|
| rahsia | secret | `TRahsia`, `LRahsia` |
| dedah | declassify | `EDeclassifyBudget` |
| dasar | policy | `declassification_policy` |
| bukti | proof | `TBukti` |
| bajet | budget | `bit_budget` |
| Wajib | mandatory | `AuditWajib` |
| awam | public | `LAwam` |
| dalaman | internal | `LDalaman` |
| sesi | session | `LSesi` |
| pengguna | user | `LPengguna` |
| sistem | system | `LSistem` |

---

## Usage

To use this specification:

1. **Compile with Coq:** `coqc RIINA_QUANT_DECLASS_SPEC_v1_0_0.v`
2. **Extend:** Add domain-specific policies by instantiating `declassification_policy`
3. **Prove:** Complete the `Admitted` theorems for full verification

---

*End of Document*