# Claude.ai Research Task - Phase 5A: TFn Step-Up Coq Integration

## Context

We are completing the `master_theorem` in `/workspaces/proof/02_FORMAL/coq/properties/MasterTheorem.v`. Phase 4 provided the proof STRATEGY for TFn step-up. This task requires converting that strategy into ACTUAL COQ TACTICS.

## Current State

The TFn case is at line 682-711 with this structure:
```coq
+ (* Property B: Step Up for TFn (m, n >= 2) - step independence *)
  intros m n Σ v1 v2 Hm Hn Hrel.
  (* Detailed documentation of proof strategy *)
  admit.
```

## Available Lemmas (ALREADY PROVEN)

```coq
(* From CumulativeRelation.v - step down for any type *)
val_rel_le_mono_step : forall n m Σ T v1 v2,
  m <= n -> val_rel_le n Σ T v1 v2 -> val_rel_le m Σ T v1 v2

(* From MasterTheorem.v - edge case bridges *)
step_0_to_1 : forall Σ T v1 v2,
  value v1 -> value v2 -> closed_expr v1 -> closed_expr v2 ->
  val_rel_le 0 Σ T v1 v2 -> val_rel_le 1 Σ T v1 v2

step_1_to_2 : forall Σ T v1 v2,
  val_rel_le 1 Σ T v1 v2 -> val_rel_le 2 Σ T v1 v2

(* From IH - available in context after destruct *)
StepDown1 : forall m n Σ v1 v2, m <= n -> val_rel_le n Σ T1 v1 v2 -> val_rel_le m Σ T1 v1 v2
StepUp1 : forall m n Σ v1 v2, m >= 2 -> n >= 2 -> val_rel_le m Σ T1 v1 v2 -> val_rel_le n Σ T1 v1 v2
StepDown2 : forall m n Σ v1 v2, m <= n -> val_rel_le n Σ T2 v1 v2 -> val_rel_le m Σ T2 v1 v2
StepUp2 : forall m n Σ v1 v2, m >= 2 -> n >= 2 -> val_rel_le m Σ T2 v1 v2 -> val_rel_le n Σ T2 v1 v2

(* Well-founded induction *)
lt_wf : well_founded lt
```

## The Phase 4 Strategy (Reference)

From CLAUDE_AI_RESEARCH_OUTPUT_4.md:
1. Destruct m, n to S (S m''), S (S n'')
2. Extract cumulative (Hcum_m) and structural (Hstruct_m)
3. Build cumulative part:
   - If S n'' <= S m'': use val_rel_le_mono_step
   - If S n'' > S m'': use well_founded_ind lt_wf
4. Build structural part:
   - Convert args: S n'' to S m'' (contravariant)
   - Apply Hfn_m to get results at S m''
   - Convert results: S m'' to S n'' (covariant)

## Your Task

Produce EXACT COQ TACTICS that can replace the `admit.` at line 711.

### Requirements

1. **EXACT SYNTAX**: The output must be copy-pasteable Coq that compiles
2. **NO AXIOMS**: Cannot use `Admitted`, `admit`, or declare axioms
3. **USE AVAILABLE LEMMAS**: Only use lemmas listed above + standard library
4. **EXPLICIT PARAMETERS**: When Coq can't infer, use `apply (lemma param1 param2 ...)`
5. **HANDLE ALL CASES**: Every `destruct` must handle all branches

### Key Adaptation Notes

1. **step_1_to_2_T1/T2**: Use `apply step_1_to_2` directly (works for any type)
2. **StepDown for TFn**: Use `val_rel_le_mono_step` (not recursive call to StepDown)
3. **val_rel_struct**: After `unfold val_rel_struct`, the TFn case gives a function specification

### val_rel_struct for TFn (Reference)

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

## Deliverable

A complete proof term starting from `intros m n Σ v1 v2 Hm Hn Hrel.` and ending with `Qed.` that proves Property B for TFn.

## Constraints

1. Must handle all 9 sub-cases from verification checklist
2. Use bullet points (`+`, `-`, `*`, `--`, `++`) or braces `{ }` for sub-goals
3. Keep proofs modular - use `assert` for key intermediate goals
4. The proof may be long (100+ lines) - that's expected

## Rules to Apply

1. **Revolutionary Solution**: The proof must be the definitive, mathematically perfect Coq proof for TFn step-independence.

2. **Zero Vulnerabilities**: Every edge case (m=2, n=2, m<n, m>n, m=n, m-1=1, n-1=1) must be explicitly handled with correct tactics.

3. **Ultra Paranoid Verification**: Each tactic must be justified by the available lemmas. No "this should work" - only "this DOES work because...".

4. **No Shortcuts**: Every case must be spelled out. If there are 9 sub-cases, write 9 proof branches.

5. **Foundational Correctness**: The proof must follow from the definition of val_rel_le and val_rel_struct, not intuition.
