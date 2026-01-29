# Delegation Prompt: Eliminate `fundamental_theorem_step_0` Axiom in NonInterference_v2.v

## TASK

Produce a **drop-in replacement** for `NonInterference_v2.v` that eliminates the single remaining axiom (`fundamental_theorem_step_0`) by making `val_rel_at_type` step-indexed (returning `True` at step 0).

## CONSTRAINTS

1. **Must use project imports** — keep all `Require Import RIINA.*` lines exactly as-is
2. **Must compile with Coq 8.18** under the existing `_CoqProject` (namespace `RIINA`)
3. **Zero axioms, zero admits** — the output file must have no `Axiom`, `Admitted`, or `admit`
4. **Preserve all existing lemma names and signatures** — downstream files depend on them
5. **Preserve the `val_rel_n` / `store_rel_n` mutual fixpoint structure** — other files pattern-match on these
6. **Output the COMPLETE file** — every line, not excerpts

## THE KEY INSIGHT (from Prompt 6 reference)

The axiom at line 1504 states:

```coq
Axiom fundamental_theorem_step_0 : forall T Σ v1 v2,
  first_order_type T = false ->
  val_rel_n 0 Σ T v1 v2 ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2.
```

This axiom is needed because at step 0, `val_rel_n 0` for HO types only carries typing — but `val_rel_at_type` demands structural/behavioral content (e.g., for TFn, a universal quantification over arguments and stores).

**The fix**: Make `val_rel_at_type` step-indexed. At step 0, it returns `True`. At step `S n'`, it returns the original structural requirements. Then:
- `fundamental_theorem_step_0` becomes trivially provable: `simpl. exact I. Qed.`
- The rest of `combined_step_up_all` needs updating because `val_rel_at_type` now takes a step index

## WHAT TO CHANGE

### Change 1: Replace `Section ValRelAtN` with `Fixpoint val_rel_at_type_n`

Current (lines 321-377):
```coq
Section ValRelAtN.
  Variable Σ : store_ty.
  Variable store_rel_pred : store_ty -> store -> store -> Prop.
  Variable val_rel_lower : store_ty -> ty -> expr -> expr -> Prop.
  Variable store_rel_lower : store_ty -> store -> store -> Prop.

  Fixpoint val_rel_at_type (T : ty) (v1 v2 : expr) {struct T} : Prop :=
    match T with
    | TUnit => v1 = EUnit /\ v2 = EUnit
    ...
    | TFn T1 T2 eff =>
        forall Σ', store_ty_extends Σ Σ' -> ...
    ...
    end.
End ValRelAtN.
```

Replace with a `Fixpoint` that takes step index `n`:
```coq
Fixpoint val_rel_at_type_n
    (n : nat)
    (Σ : store_ty)
    (store_rel_pred : store_ty -> store -> store -> Prop)
    (val_rel_lower : store_ty -> ty -> expr -> expr -> Prop)
    (store_rel_lower : store_ty -> store -> store -> Prop)
    (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      match T with
      | TUnit => v1 = EUnit /\ v2 = EUnit
      | TBool => exists b, v1 = EBool b /\ v2 = EBool b
      ... (* same as current val_rel_at_type body *)
      | TFn T1 T2 eff =>
          forall Σ', store_ty_extends Σ Σ' ->
            forall x y,
              value x -> value y -> closed_expr x -> closed_expr y ->
              val_rel_lower Σ' T1 x y ->
              forall st1 st2 ctx,
                store_rel_pred Σ' st1 st2 ->
                store_wf Σ' st1 -> store_wf Σ' st2 ->
                stores_agree_low_fo Σ' st1 st2 ->
                exists v1' v2' st1' st2' ctx' Σ'',
                  store_ty_extends Σ' Σ'' /\
                  (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
                  (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
                  val_rel_lower Σ'' T2 v1' v2' /\
                  store_rel_lower Σ'' st1' st2' /\
                  store_wf Σ'' st1' /\ store_wf Σ'' st2' /\
                  stores_agree_low_fo Σ'' st1' st2'
      ... (* rest same as current *)
      end
  end.
```

**CRITICAL**: The `{struct T}` must still work. The outer match on `n` doesn't recurse — the inner match on `T` does (for TProd/TSum). Coq should accept this because the recursive calls in TProd/TSum are on strict subterms of `T`.

**ALTERNATIVE if `{struct T}` fails**: Use `{struct n}` and don't recurse on `T` components at step `S n'` — instead call `val_rel_at_type_n n'` for TProd/TSum subcomponents. This matches the Prompt 6 approach.

### Change 2: Update `val_rel_n` / `store_rel_n` mutual fixpoint

Current `val_rel_n` at step `S n'` (line 405):
```coq
val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
```

Change to:
```coq
val_rel_at_type_n (S n') Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
```

**OR** (if using a unified approach): embed `val_rel_at_type_n n` at ALL steps (not just `S n'`), passing `n` as the step index. The Prompt 6 reference shows this approach.

### Change 3: Delete the axiom, add the lemma

Delete lines 1504-1509 (the `Axiom fundamental_theorem_step_0`).

Add:
```coq
Lemma fundamental_theorem_step_0 : forall T Σ v1 v2,
  first_order_type T = false ->
  val_rel_n 0 Σ T v1 v2 ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  val_rel_at_type_n 0 Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2.
Proof.
  intros T Σ v1 v2 Hho Hrel Hty1 Hty2.
  simpl. exact I.
Qed.
```

### Change 4: Update all references to `val_rel_at_type`

Every occurrence of `@val_rel_at_type Σ ...` becomes `val_rel_at_type_n ... Σ ...` with the appropriate step index. Key locations:

- `val_rel_n_S_unfold` (line 439-448)
- `val_rel_at_type_fo_equiv` (line 480-527) — now needs step index parameter
- `val_rel_at_type_fo_step_invariant` (line 1245-1253)
- `val_rel_at_type_step_up_with_IH` (line 1263-1376)
- `combined_step_up_all` (lines 1512-2086) — the n=0 case becomes trivial
- `val_rel_at_type_TFn_step_0_bridge` (lines 2413-2464)

### Change 5: Simplify `combined_step_up_all` n=0 case

The n=0 HO case (line 1556-1560) currently uses the axiom:
```coq
apply fundamental_theorem_step_0; assumption.
```

With the new definition, `val_rel_at_type_n 0 ...` = `True`, so this becomes:
```coq
simpl. exact I.
```

**BUT**: You also need to check that the `val_rel_n_S_unfold` now refers to `val_rel_at_type_n (S n')` not `val_rel_at_type`. If the step index in `val_rel_at_type_n` is `S n'` (matching the step in `val_rel_n (S n')`), then for the n=0 case of `combined_step_up_all`, we're proving `val_rel_n 1`:
- `val_rel_n 1` includes `val_rel_at_type_n 1 ...` (which has the full structural content)
- At n=0 in `combined_step_up_all`, `Hrel` is `val_rel_n 0` — no `val_rel_at_type` content
- So we still need the fundamental theorem to go from typing to `val_rel_at_type_n 1`

**THIS IS THE CRITICAL SUBTLETY**. Two approaches:

**Approach A** (Prompt 6 style): Make `val_rel_n` embed `val_rel_at_type_n n` at ALL steps (including step 0). Then `val_rel_n 0` includes `val_rel_at_type_n 0 = True`, and when proving `val_rel_n 1`, the `val_rel_at_type_n 1` content must be established. The n=0 case of `combined_step_up_all` becomes: we have `val_rel_n 0` (which includes `val_rel_at_type_n 0 = True`), and we need to build `val_rel_at_type_n 1`. This still requires the fundamental theorem for TFn.

**Approach B** (Keep current structure): The current `val_rel_n 0` does NOT include `val_rel_at_type`. Only `val_rel_n (S n')` includes it. So `combined_step_up_all` at n=0 needs to produce `val_rel_at_type_n 1 ...` from typing alone. This is still the fundamental theorem.

**THE ACTUAL FIX**: The Prompt 6 approach works IF we change the `val_rel_n` step-0 definition to also include `val_rel_at_type_n 0` (which is `True`). Then in `combined_step_up_all`, the n=0 case proves `val_rel_n 1` which needs `val_rel_at_type_n 1`. But we can use `val_rel_at_type_TFn_step_0_bridge` (already proven at line 2413-2464) to establish this! The bridge lemma:
1. Builds `val_rel_n 0` for TFn from typing
2. Steps up to `val_rel_n 1` via `combined_step_up_all` (which is what we're proving!)

**This is circular!** The bridge lemma calls `combined_step_up_all` which is what we're trying to prove.

**THE REAL FIX**: Look at the bridge lemma more carefully (lines 2436-2464). It builds `val_rel_n 0`, then steps up to `val_rel_n 1` using `val_rel_n_step_up_from_combined`. This calls `combined_step_up_all 0`. So the bridge IS the proof of the n=0 case.

The key realization: `val_rel_at_type_TFn_step_0_bridge` already proves exactly what the axiom states. It uses `combined_step_up_all` to step from `val_rel_n 0` to `val_rel_n 1`, then extracts `val_rel_at_type` from `val_rel_n 1`.

**But wait** — `combined_step_up_all` at n=0 USES the axiom! So the bridge and `combined_step_up_all` are mutually dependent.

**THE ACTUAL ACTUAL FIX**: Make `val_rel_at_type_n` step-indexed with `{struct n}` where TProd/TSum recurse at step `n'` (not `n`). Then at `val_rel_n (S n')`, include `val_rel_at_type_n (S n') ...`. For n=0 case of `combined_step_up_all`:
- We prove `val_rel_n 1` from `val_rel_n 0`
- `val_rel_n 1` includes `val_rel_at_type_n 1`
- `val_rel_at_type_n 1` for TFn requires: given val_rel_n 0 arguments and store_rel_n 0 stores, produce val_rel_n 0 results
- We have typing for v1, v2 from `val_rel_n 0`'s HO branch
- We can extract lambda structure via canonical_forms_fn
- We can beta-reduce
- We need val_rel_n 0 for the result — this follows from preservation + the val_rel_n 0 definition (typing for HO, structure for FO)

**So the n=0 TFn case becomes provable WITHOUT the axiom if `val_rel_at_type_n 1` for TFn only requires producing `val_rel_n 0` results** (not `val_rel_n n'` results).

This is exactly what happens if `val_rel_at_type_n` uses `val_rel_lower` (which is `val_rel_n n'` = `val_rel_n 0` when we're at step `S 0 = 1`).

**CONCLUSION**: The fix works. At n=0 in `combined_step_up_all`:
- Goal: `val_rel_at_type_n 1 Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2`
- For TFn: given `val_rel_n 0` arguments, produce `val_rel_n 0` results
- This is provable from typing via canonical_forms + beta reduction + preservation
- For TProd/TSum: `val_rel_at_type_n 0 ... = True` for subcomponents (if using `n'`)

**Wait** — if TProd/TSum in `val_rel_at_type_n (S n')` recurse at step `n'`, then at step 1 the TProd/TSum components are at step 0 = True. This is too weak! We lose structural information for first-order products.

**BETTER APPROACH**: Keep `{struct T}` recursion for TProd/TSum (same step index), and only the outer `n` controls the TFn case. Like:

```coq
Fixpoint val_rel_at_type_n (n : nat) (Σ : store_ty) ... (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  | TUnit => match n with 0 => True | S _ => v1 = EUnit /\ v2 = EUnit end
  | ...
  | TProd T1 T2 => match n with 0 => True | S _ =>
      exists ..., val_rel_at_type_n n Σ ... T1 x1 x2 /\ val_rel_at_type_n n Σ ... T2 y1 y2 end
  | TFn T1 T2 eff => match n with 0 => True | S _ => ... end
  ...
  end.
```

But Coq won't accept this — `{struct T}` requires recursive calls on strict subterms of `T`, which is fine for TProd/TSum, but the `n` parameter doesn't decrease. Since `n` is not the structural argument, this should be fine — Coq checks structural decrease on `T` only.

**Actually this might work!** The function is structurally recursive on `T`. The `n` parameter is just carried through. Let me verify: in the TProd case, `val_rel_at_type_n n Σ sp vl sl T1 x1 x2` — `T1` is a subterm of `TProd T1 T2`, and `n` stays the same. Coq should accept this.

So the definition would be `{struct T}` with `match n` inside each case, and TProd/TSum recurse on `T` subterms at the same `n`. This preserves full structural information for FO types at all step indices while making everything `True` at step 0.

## REFERENCE: Prompt 6 Output (Standalone)

The Prompt 6 file (`Prompt6_NonInterference_v2_Final.v`) is a standalone reimplementation that demonstrates the approach but redefines all types. Key sections to study:

- `val_rel_at_type_n` definition (lines 244-302): step-indexed with `{struct n}`
- `val_rel_n` / `store_rel_n` mutual fixpoint (lines 308-332)
- `fundamental_theorem_step_0` as trivial lemma (lines 340-351)

**Do NOT copy this file directly** — it uses standalone type definitions, not the project's `RIINA.*` imports.

## CURRENT FILE: NonInterference_v2.v (2481 lines)

The file you must modify is the actual codebase file with `Require Import RIINA.*` imports. Here is its complete content:

<FILE_START path="02_FORMAL/coq/properties/NonInterference_v2.v">
(see the file at /workspaces/proof/02_FORMAL/coq/properties/NonInterference_v2.v — 2481 lines)
</FILE_START>

**IMPORTANT**: The file is too large to embed inline. You MUST use the content from my project's `02_FORMAL/coq/properties/NonInterference_v2.v` as the base. I will paste the full file content in a follow-up message if needed, or you can work from the structure described above.

## IMPORTS AND DEPENDENCIES

The file imports from:
```coq
Require Import RIINA.foundations.Syntax.       (* ty, expr, value, loc, security_level, etc. *)
Require Import RIINA.foundations.Semantics.     (* step, multi_step, store, store_lookup, etc. *)
Require Import RIINA.foundations.Typing.        (* has_type, store_wf, store_ty, canonical_forms_*, etc. *)
Require Import RIINA.type_system.Preservation.  (* preservation, free_in_context *)
Require Import RIINA.termination.ReducibilityFull. (* well_typed_SN, SN_app *)
Require Import RIINA.properties.TypeMeasure.   (* ty_size_induction *)
```

Key definitions from imports:
- `ty` has 22 constructors (TUnit, TBool, TInt, TString, TBytes, TFn, TProd, TSum, TList, TOption, TRef, TSecret, TLabeled, TTainted, TSanitized, TProof, TCapability, TCapabilityFull, TChan, TSecureChan, TConstantTime, TZeroizing)
- `store_ty := list (loc * ty * security_level)`
- `store := list (loc * expr)`
- `store_wf` requires bidirectional typed values
- `canonical_forms_fn`, `canonical_forms_prod`, `canonical_forms_sum`, `canonical_forms_ref`, `canonical_forms_unit`, `canonical_forms_bool`, `canonical_forms_int`, `canonical_forms_string` — all proven
- `value_has_pure_effect` — proven
- `store_has_values` — defined in Semantics
- `store_ty_extends` — lookup preservation
- `free_in` — free variable predicate
- `free_in_context` — free vars have types in context

## DELIVERABLE

Output the **complete** modified `NonInterference_v2.v` file (all ~2500 lines) with:
1. `val_rel_at_type` replaced by step-indexed `val_rel_at_type_n`
2. `val_rel_n`/`store_rel_n` updated to use `val_rel_at_type_n`
3. `fundamental_theorem_step_0` changed from `Axiom` to `Lemma` with trivial proof
4. All downstream lemmas updated (unfolding lemmas, equivalence lemmas, step-up lemmas, `combined_step_up_all`, bridge lemma)
5. All proofs complete — zero admits, zero axioms (except `observer : security_level` which is a Parameter, not an axiom)
6. All existing lemma names preserved

**Compile-test your output mentally** — ensure every `Qed` will succeed.
