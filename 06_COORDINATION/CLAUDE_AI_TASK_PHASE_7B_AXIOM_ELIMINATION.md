# Claude.ai Research Task - Phase 7B: Axiom Elimination via master_theorem

## CRITICAL CONTEXT

The master_theorem in MasterTheorem.v has been proven (with one justified semantic axiom for TFn store-weakening). This theorem provides corollaries that can REPLACE axioms in NonInterference.v.

**Current axiom count: 20 (19 in NonInterference.v + 1 justified in MasterTheorem.v)**
**Target: Eliminate the 19 legacy axioms**

## The master_theorem Structure

```coq
Theorem master_theorem : forall T, combined_properties T.

Definition combined_properties (T : ty) : Prop :=
  (* Property A: Step Down *)
  (forall m n Σ v1 v2, m <= n -> val_rel_le n Σ T v1 v2 -> val_rel_le m Σ T v1 v2) /\
  (* Property B: Step Up (for n >= 2) *)
  (forall m n Σ v1 v2, m >= 2 -> n >= 2 -> val_rel_le m Σ T v1 v2 -> val_rel_le n Σ T v1 v2) /\
  (* Property C: Store Strengthening *)
  (forall n Σ Σ' v1 v2, store_ty_extends Σ Σ' -> val_rel_le n Σ T v1 v2 -> val_rel_le n Σ' T v1 v2) /\
  (* Property D: Store Weakening *)
  (forall n Σ Σ' v1 v2, store_ty_extends Σ Σ' -> val_rel_le n Σ' T v1 v2 -> val_rel_le n Σ T v1 v2).
```

## Available Corollaries (ALREADY PROVEN in MasterTheorem.v)

```coq
(** Replaces Axiom 1: val_rel_n_weaken (store weakening) *)
Lemma val_rel_weaken_proven : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_le n Σ' T v1 v2 ->
  val_rel_le n Σ T v1 v2.

(** Replaces Axiom 2: val_rel_n_mono_store (store strengthening) *)
Lemma val_rel_mono_store_proven : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le n Σ' T v1 v2.

(** Replaces Axiom 12: val_rel_n_step_up *)
Lemma val_rel_step_up_proven : forall T m n Σ v1 v2,
  m >= 2 -> n >= 2 ->
  val_rel_le m Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
```

## Axioms to Eliminate (in NonInterference.v)

### Priority 1: Directly Replaceable (3 axioms)

```coq
(* Line 682 *)
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.

(* Line 789 *)
Axiom val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.

(* Line 1076 *)
Axiom val_rel_n_step_up : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
```

### Priority 2: Derivable from Priority 1 (2 axioms)

```coq
(* Line 1082 - Derivable from val_rel_n_weaken *)
Axiom store_rel_n_step_up : forall n Σ st1 st2,
  n > 0 ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n (S n) Σ st1 st2.

(* Line 1092 - Derivable from step-up *)
Axiom val_rel_n_lam_cumulative : forall n Σ T1 T2 ε x body1 body2,
  val_rel_n n Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2) ->
  val_rel_n (S n) Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2).
```

### Priority 3: Step-1 Termination (7 axioms)

These require showing that well-typed expressions reduce in one step:

```coq
Axiom exp_rel_step1_fst : forall Σ T1 v v' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_snd : forall Σ T2 v v' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_case : forall Σ T v v' x1 e1 e1' x2 e2 e2' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_if : forall Σ T v v' e2 e2' e3 e3' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_let : forall Σ T v v' x e2 e2' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_handle : forall Σ T v v' x h h' st1 st2 ctx Σ', ...
Axiom exp_rel_step1_app : forall Σ T2 f f' a a' st1 st2 ctx Σ', ...
```

### Priority 4: Higher-Order Conversion (2 axioms)

```coq
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2, ...
Axiom val_rel_at_type_to_val_rel_ho : forall Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2, ...
```

### Priority 5: Semantic Typing (4 axioms)

```coq
Axiom logical_relation_ref : ...
Axiom logical_relation_deref : ...
Axiom logical_relation_assign : ...
Axiom logical_relation_declassify : ...
```

### Priority 6: Application Completeness (1 axiom)

```coq
Axiom tapp_step0_complete : forall Σ' Σ''' T2 ...
```

## Your Task

### Task 1: Provide Replacement Strategy

For EACH of the 19 axioms, provide:

1. **Classification**: Which priority level (1-6)?
2. **Replacement lemma**: What proven lemma replaces it?
3. **Proof sketch**: How to derive from master_theorem corollaries?
4. **Dependencies**: What other axioms/lemmas are needed?

### Task 2: Priority 1 Elimination (Detailed)

For the 3 directly replaceable axioms, provide EXACT Coq code showing:

1. How to import from MasterTheorem.v
2. The replacement lemma with proof
3. Any notation/alias needed for compatibility

Example format:
```coq
(* In NonInterference.v, replace: *)

(* OLD:
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
*)

(* NEW: *)
Require Import RIINA.properties.MasterTheorem.

Lemma val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  intros n Σ Σ' T v1 v2 Hext Hrel.
  (* val_rel_n is alias for val_rel_le *)
  apply val_rel_weaken_proven with Σ'; auto.
Qed.
```

### Task 3: Priority 2 Derivations

For the 2 derivable axioms, show how they follow from Priority 1:

```coq
(* store_rel_n_step_up derivation *)
Lemma store_rel_n_step_up : forall n Σ st1 st2,
  n > 0 ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n (S n) Σ st1 st2.
Proof.
  (* Use val_rel_n_step_up at each location *)
  [provide exact proof]
Qed.
```

### Task 4: Priority 3-6 Analysis

For each remaining axiom category, provide:

1. **What infrastructure is needed** to prove it
2. **Whether it's provable** from current definitions
3. **If not provable**, what semantic property is missing

## Key Insight: val_rel_n vs val_rel_le

In NonInterference.v:
```coq
Definition val_rel_n := val_rel_le.  (* They're the same! *)
```

So `val_rel_n_weaken` is exactly `val_rel_weaken_proven` with a different name.

## Constraints

1. **COMPLETE ANALYSIS**: Address ALL 19 axioms
2. **EXECUTABLE CODE**: Provide working Coq for Priority 1-2
3. **CLEAR DEPENDENCIES**: Show what depends on what
4. **REALISTIC ASSESSMENT**: Don't claim something is provable if it requires missing infrastructure

## Rules to Apply

1. **Revolutionary Solution**: Eliminate as many axioms as possible with complete proofs.

2. **Zero Vulnerabilities**: Every replacement must be mathematically sound.

3. **Ultra Paranoid Verification**: Each proof step must be justified.

4. **No Shortcuts**: If an axiom can't be eliminated yet, explain exactly why.

5. **Foundational Correctness**: Based on exact definitions in codebase.

## Deliverable

1. Complete classification of all 19 axioms
2. Exact Coq code for Priority 1 replacements (3 axioms)
3. Exact Coq code for Priority 2 derivations (2 axioms)
4. Analysis of Priority 3-6 with infrastructure requirements
5. Dependency graph showing elimination order
