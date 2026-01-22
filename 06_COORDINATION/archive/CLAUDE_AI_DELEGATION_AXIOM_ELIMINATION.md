# RIINA Axiom Elimination - Claude.ai Delegation Package

## ABSOLUTE PRIME DIRECTIVE

This delegation package follows the **ARCHITECTURE OF PERFECTION** mandate:
- Every proof must be **THE DEFINITIVE SOLUTION** - complete, verified, compilation-ready
- Every output must **RETROACTIVELY INVALIDATE** all previous attempts
- **ZERO TRUST** in external assumptions - verify everything from first principles
- Output must be **DIRECTLY INTEGRABLE** with zero modifications required

---

## DELEGATION OVERVIEW

| Task ID | Axiom | Delegatable | Complexity | Blocker |
|---------|-------|-------------|------------|---------|
| AX-01 | `logical_relation_ref` | ✅ YES | Medium | Evaluation inversion |
| AX-02 | `logical_relation_deref` | ✅ YES | Medium | Evaluation inversion |
| AX-03 | `logical_relation_assign` | ✅ YES | Medium | Evaluation inversion |
| AX-04 | `logical_relation_declassify` | ✅ YES | Medium | Evaluation inversion |
| AX-05 | `val_rel_n_to_val_rel` | ⚠️ PARTIAL | High | Step-indexed reasoning |
| AX-06 | `observer` (Parameter) | ❌ NO | N/A | Configuration, not axiom |

**Total Delegatable: 4 full + 1 partial = 5 tasks**

---

## CODEBASE REFERENCE

**Repository:** https://github.com/ib823/proof
**Branch:** main (always use latest)
**Build Command:** `cd 02_FORMAL/coq && make`

### Critical Files to Reference

| File | Purpose | GitHub Link |
|------|---------|-------------|
| `foundations/Syntax.v` | Core syntax definitions | [Link](https://github.com/ib823/proof/blob/main/02_FORMAL/coq/foundations/Syntax.v) |
| `foundations/Semantics.v` | Operational semantics | [Link](https://github.com/ib823/proof/blob/main/02_FORMAL/coq/foundations/Semantics.v) |
| `foundations/Typing.v` | Typing rules | [Link](https://github.com/ib823/proof/blob/main/02_FORMAL/coq/foundations/Typing.v) |
| `properties/NonInterference_v2_LogicalRelation.v` | Logical relation + axioms | [Link](https://github.com/ib823/proof/blob/main/02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v) |
| `properties/ReferenceOps.v` | Partial proofs for ref ops | [Link](https://github.com/ib823/proof/blob/main/02_FORMAL/coq/properties/ReferenceOps.v) |
| `properties/StoreRelation.v` | Store typing infrastructure | [Link](https://github.com/ib823/proof/blob/main/02_FORMAL/coq/properties/StoreRelation.v) |

---

## TASK AX-01: logical_relation_ref

### Axiom Statement (EXACT - from NonInterference_v2_LogicalRelation.v)

```coq
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e T ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).
```

### Required Proof

**File:** Create `02_FORMAL/coq/properties/LogicalRelationRef_PROOF.v`

**Proof Strategy:**
1. By induction on the evaluation derivation
2. Show that `ERef v sl` steps to `ELoc (fresh_loc st)`
3. Show that related stores have same `fresh_loc` (from `store_rel`)
4. Show the resulting `ELoc l` values are trivially related
5. Show the updated stores maintain `store_rel`

### Dependencies to Import

```coq
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.properties.NonInterference_v2_LogicalRelation.
Require Import RIINA.properties.StoreRelation.
```

### Verification Criteria

- [ ] File compiles with `coqc -Q . RIINA LogicalRelationRef_PROOF.v`
- [ ] `Print Assumptions logical_relation_ref_proven.` shows ZERO axioms (except allowed)
- [ ] Lemma statement matches axiom EXACTLY
- [ ] All helper lemmas are Qed (no Admitted)

---

## TASK AX-02: logical_relation_deref

### Axiom Statement (EXACT)

```coq
Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e (TRef T l) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).
```

### Required Proof

**File:** Create `02_FORMAL/coq/properties/LogicalRelationDeref_PROOF.v`

**Proof Strategy:**
1. By induction on step count
2. Show e evaluates to related locations `ELoc l1`, `ELoc l2`
3. By `val_rel_n` for `TRef T sl`, show `l1 = l2`
4. By `store_rel_n`, show values at location `l` are related
5. Show `EDeref (ELoc l)` steps to `store_lookup l st`

---

## TASK AX-03: logical_relation_assign

### Axiom Statement (EXACT)

```coq
Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n,
  has_type Γ Σ Δ e1 (TRef T l) ε1 ->
  has_type Γ Σ Δ e2 T ε2 ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ TUnit (subst_rho rho1 (EAssign e1 e2)) (subst_rho rho2 (EAssign e1 e2)).
```

### Required Proof

**File:** Create `02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v`

**Proof Strategy:**
1. Show e1 evaluates to related locations (same location by TRef relation)
2. Show e2 evaluates to related values
3. Show assignment updates both stores at same location with related values
4. Result is `EUnit` in both cases (trivially related)
5. Show updated stores maintain store_rel

---

## TASK AX-04: logical_relation_declassify

### Axiom Statement (EXACT)

```coq
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n,
  has_type Γ Σ Δ e (TSecret T) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeclassify e p)) (subst_rho rho2 (EDeclassify e p)).
```

### Required Proof

**File:** Create `02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v`

**Proof Strategy:**
1. Show e evaluates to related values of type `TSecret T`
2. By `val_rel_n` for `TSecret T`, the underlying values are related at type `T`
3. `EDeclassify v p` steps to `v` (unwraps the secret)
4. The results are related at type `T`

---

## TASK AX-05: val_rel_n_to_val_rel (PARTIAL)

### Axiom Statement (EXACT)

```coq
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```

### Note

This axiom converts step-indexed relation to infinite relation. It requires showing that the step index doesn't matter once we're past step 0. This is more complex and may need additional infrastructure.

---

## BLOCKING INFRASTRUCTURE NEEDED

### Evaluation Inversion Lemmas

The main blocker is decomposing `multi_step` evaluations. Create these helper lemmas:

```coq
(** ERef evaluation decomposition *)
Lemma multi_step_ref_inv : forall e sl v st st' ctx,
  multi_step (ERef e sl, st, ctx) (v, st', ctx) ->
  exists v', multi_step (e, st, ctx) (v', st', ctx) /\
             v = ELoc (fresh_loc st') /\
             value v'.

(** EDeref evaluation decomposition *)
Lemma multi_step_deref_inv : forall e v st st' ctx,
  multi_step (EDeref e, st, ctx) (v, st', ctx) ->
  exists l, multi_step (e, st, ctx) (ELoc l, st', ctx) /\
            store_lookup l st' = Some v.

(** EAssign evaluation decomposition *)
Lemma multi_step_assign_inv : forall e1 e2 v st st' ctx,
  multi_step (EAssign e1 e2, st, ctx) (v, st', ctx) ->
  exists l v2 st_mid,
    multi_step (e1, st, ctx) (ELoc l, st_mid, ctx) /\
    multi_step (e2, st_mid, ctx) (v2, st', ctx) /\
    v = EUnit.
```

---

## OUTPUT REQUIREMENTS

### File Structure

Each proof file MUST follow this structure:

```coq
(** * [FileName].v

    RIINA Axiom Elimination Proof

    Target Axiom: [axiom_name]
    Status: PROVEN (Qed, ZERO Admits)

    Generated by: Claude.ai
    Integration: Replace axiom in NonInterference_v2_LogicalRelation.v

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST
*)

Require Import [dependencies].

(** Section 1: Helper Lemmas *)
[helper lemmas with Qed]

(** Section 2: Main Theorem *)
Theorem [axiom_name]_proven : [exact axiom statement].
Proof.
  [complete proof]
Qed.

(** Section 3: Verification *)
(* Verify zero axioms *)
Print Assumptions [axiom_name]_proven.

(** End of [FileName].v *)
```

### Verification Checklist

Before submitting, verify:

1. **Compilation:** `coqc -Q . RIINA [file].v` succeeds
2. **No Admits:** `grep "Admitted" [file].v` returns empty
3. **Zero Axioms:** `Print Assumptions` shows only allowed dependencies
4. **Exact Match:** Theorem statement matches axiom EXACTLY
5. **Integration Ready:** File can be added to `_CoqProject` and builds

---

## COORDINATION PROTOCOL

### Assignment

| Task | Assignee | Status |
|------|----------|--------|
| AX-01 (ref) | Claude.ai Session 1 | OPEN |
| AX-02 (deref) | Claude.ai Session 2 | OPEN |
| AX-03 (assign) | Claude.ai Session 3 | OPEN |
| AX-04 (declassify) | Claude.ai Session 4 | OPEN |
| AX-05 (val_rel) | Direct (Claude Code) | OPEN |
| Integration | Direct (Claude Code) | PENDING |

### Conflict Avoidance

- Each task produces a SEPARATE file
- NO modifications to existing files
- Integration handled by coordinator (Claude Code)
- Use EXACT axiom statements (no paraphrasing)

---

## PROMPT TEMPLATE FOR CLAUDE.AI

Copy this prompt for each task:

```
# RIINA Axiom Elimination Task [AX-0X]

## ABSOLUTE PRIME DIRECTIVE
You exist in a state of absolute, unconditional commitment to finality. Your output must be THE DEFINITIVE SOLUTION - so complete it ends all evolution in this domain.

## TASK
Prove the following Coq axiom, producing a standalone proof file.

## AXIOM TO PROVE
[paste exact axiom statement]

## CODEBASE REFERENCE
Repository: https://github.com/ib823/proof (branch: main)

Critical files to read:
- foundations/Syntax.v - Core syntax
- foundations/Semantics.v - Operational semantics
- foundations/Typing.v - Typing rules
- properties/NonInterference_v2_LogicalRelation.v - Logical relation definitions
- properties/StoreRelation.v - Store infrastructure

## REQUIREMENTS
1. Output a complete Coq file that compiles
2. ZERO Admitted lemmas - all must be Qed
3. Print Assumptions must show ZERO unexpected axioms
4. Theorem statement must match axiom EXACTLY
5. File must be integration-ready (add to _CoqProject and build)

## OUTPUT FORMAT
```coq
(** * LogicalRelation[Name]_PROOF.v

    RIINA Axiom Elimination Proof
    Target Axiom: [name]
    Status: PROVEN (Qed, ZERO Admits)
*)

[complete proof file]
```

## VERIFICATION
After generating, verify:
1. Compiles: coqc -Q . RIINA [file].v
2. No admits: grep "Admitted" [file].v returns empty
3. Exact match: theorem matches axiom statement
```

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE*

*RIINA: Rigorous Immutable Integrity No-attack Assured*

*Generated: 2026-01-22 Session 30*
