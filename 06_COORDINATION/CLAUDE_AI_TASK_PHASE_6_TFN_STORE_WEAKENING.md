# Claude.ai Research Task - Phase 6: TFn Store-Weakening Complete Solution

## CRITICAL CONTEXT

This is the FINAL blocking issue for completing the RIINA `master_theorem`. All other cases are proven except TFn store-weakening (Property D).

## The Problem

**Store Weakening for TFn**: Given `store_ty_extends Σ Σ'` (meaning Σ ⊆ Σ'), prove:
```coq
val_rel_le n Σ' (TFn T1 T2 eff) v1 v2 -> val_rel_le n Σ (TFn T1 T2 eff) v1 v2
```

### Why This Is Hard

TFn uses **Kripke-style quantification** in its structural definition:

```coq
val_rel_struct R Σ (TFn T1 T2 eff) v1 v2 :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  forall Σ' (Hext : store_ty_extends Σ Σ') arg1 arg2,
    value arg1 -> value arg2 -> closed_expr arg1 -> closed_expr arg2 ->
    R Σ' T1 arg1 arg2 ->
    forall st1 st2 ctx, store_rel_simple Σ' st1 st2 ->
      exists res1 res2 st1' st2' ctx' Σ'',
        store_ty_extends Σ' Σ'' /\
        (EApp v1 arg1, st1, ctx) -->* (res1, st1', ctx') /\
        (EApp v2 arg2, st2, ctx) -->* (res2, st2', ctx') /\
        value res1 /\ value res2 /\
        R Σ'' T2 res1 res2 /\
        store_rel_simple Σ'' st1' st2'
```

**The Challenge**:
- **Hypothesis (from Σ')**: Function works for all store extensions Σ'' ⊇ Σ'
- **Goal (at Σ)**: Function works for all store extensions Σ'' ⊇ Σ

Since Σ ⊆ Σ', the extensions of Σ **INCLUDE** extensions of Σ' **PLUS MORE** (stores that extend Σ but not Σ'). The goal is STRONGER - we need to prove more with less.

## Available Induction Hypotheses

From the combined_properties proof by induction on ty_size:
```coq
(* For T1, T2 (smaller than TFn T1 T2 eff) *)
StoreStr1 : forall n Σ Σ' v1 v2, store_ty_extends Σ Σ' -> val_rel_le n Σ T1 v1 v2 -> val_rel_le n Σ' T1 v1 v2
StoreWeak1 : forall n Σ Σ' v1 v2, store_ty_extends Σ Σ' -> val_rel_le n Σ' T1 v1 v2 -> val_rel_le n Σ T1 v1 v2
StoreStr2, StoreWeak2 : (same for T2)
```

## Key Definitions

```coq
(* Store typing extension *)
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T, lookup_store_ty Σ l = Some T -> lookup_store_ty Σ' l = Some T.

(* Store typing is a list of (location, (type, security_level)) *)
Definition store_ty := list (nat * (ty * security_level)).

(* Lookup in store typing *)
Fixpoint lookup_store_ty (l : nat) (Σ : store_ty) : option (ty * security_level) :=
  match Σ with
  | [] => None
  | (l', entry) :: rest => if Nat.eqb l l' then Some entry else lookup_store_ty l rest
  end.
```

## Required Analysis

### Question 1: Does store_ty_extends form a directed set?

Given:
- Σ ⊆ Σ' (store_ty_extends Σ Σ')
- Σ ⊆ Σ'' (store_ty_extends Σ Σ'')

Does there exist Σ''' such that:
- Σ' ⊆ Σ'''
- Σ'' ⊆ Σ'''

**If YES**: Provide the construction and proof.
**If NO**: Explain why not and what constraints would make it work.

### Question 2: Is there an alternative approach?

Consider these alternatives:
1. **Contrapositive**: Maybe we don't need to handle ALL extensions of Σ
2. **Semantic argument**: At step n, what constraints does store typing actually impose?
3. **Induction on n**: Maybe store weakening becomes easier at specific step levels

## Proof Strategy Options

### Option A: Directed Join Construction
If store typings form a directed set:
1. For any Σ'' ⊇ Σ (in the goal), construct Σ''' = join(Σ', Σ'')
2. Convert args from Σ'' to Σ''' using StoreStr1
3. Apply hypothesis at Σ''' (which extends Σ')
4. Results at Σ'''' ⊇ Σ''' ⊇ Σ''

### Option B: Step Induction
1. Base case (n=0): val_rel_le 0 = True, trivial
2. Step case (n+1):
   - Cumulative part: recursive call
   - Structural part: extract structural from Σ', show it works at Σ

### Option C: Alternative Characterization
Maybe the structural part can be reformulated to avoid the problematic quantification.

## Constraints

1. **COMPLETE PROOF**: Must provide complete Coq tactics, not sketches
2. **NO NEW AXIOMS**: Cannot add new assumptions beyond what's in the codebase
3. **USE AVAILABLE IH**: Must leverage StoreWeak1, StoreWeak2, StoreStr1, StoreStr2
4. **INFRASTRUCTURE OK**: If you need new lemmas about store_ty, provide their complete proofs

## What Already Works (Context)

- TFn Step-Up (Property B): COMPLETE - lines 682-886 of MasterTheorem.v
- TProd/TSum store-weakening: COMPLETE - uses IH on components
- Base types store-weakening: COMPLETE - first-order types are store-independent
- All security types (TSecret, TLabeled, etc.): COMPLETE - relation is True

## Deliverable

1. **Analysis**: Determine if directed join exists and what infrastructure is needed
2. **Complete Proof**: Provide exact Coq tactics for the TFn store-weakening case
3. **Any Required Lemmas**: With complete proofs

## Rules to Apply

1. **Revolutionary Solution**: The proof must be the definitive mathematical solution.

2. **Zero Vulnerabilities**: Every case and sub-case must be explicitly handled.

3. **Ultra Paranoid Verification**: Each step must be justified by definitions and available lemmas. No hand-waving.

4. **No Shortcuts**: If infrastructure is missing, provide complete proofs for all required lemmas.

5. **Foundational Correctness**: Based on the exact definitions in the codebase, not intuition.

## Current State in MasterTheorem.v

Line 1014 (approximate after edits):
```coq
+ (* Property D: Store Weakening for TFn *)
  intros n Σ Σ' v1 v2 Hext Hrel.
  (* TFn uses Kripke quantification over store extensions *)
  (* Weakening: Σ ⊆ Σ' means Σ has fewer constraints *)
  (* This is the harder direction *)
  admit.
```

## Final Notes

This is the LAST major obstacle to completing the master_theorem. With this case proven:
- All 19 axioms can be eliminated
- The RIINA proof is complete at the foundation level

The solution here will complete Phase 1 of the RIINA verification.
