# DELEGATION PROMPT: Priority 1 - n=0 Case (Fundamental Theorem)

## OBJECTIVE
Fill the admit at `NonInterference_v2.v:1140` - the n=0 case for higher-order types in `val_rel_n_step_up_by_type`.

## CONTEXT

### The Problem
At step n=0 for function types (TFn T1 T2 ε), we need to prove that function applications produce related results. This requires the **Fundamental Theorem of Logical Relations**.

### Location
- **File:** `02_FORMAL/coq/properties/NonInterference_v2.v`
- **Line:** 1140
- **Function:** `val_rel_n_step_up_by_type`
- **Case:** n=0, T = TFn T1 T2 ε (higher-order)

### Available Hypotheses at Line 1140
```coq
(* From outer context *)
T : ty                                     (* = TFn T1 T2 ε *)
IH : forall T', ty_size T' < ty_size T -> (* IH on smaller types *)
     forall n Σ v1 v2, val_rel_n n Σ T' v1 v2 -> ... -> val_rel_n (S n) Σ T' v1 v2
n : nat                                    (* = 0 in this case *)
Σ : store_ty
v1, v2 : expr                              (* lambda values *)
Hrel : val_rel_n 0 Σ (TFn T1 T2 ε) v1 v2
Hty1 : first_order_type (TFn T1 T2 ε) = false -> has_type nil Σ Public v1 (TFn T1 T2 ε) EffectPure
Hty2 : first_order_type (TFn T1 T2 ε) = false -> has_type nil Σ Public v2 (TFn T1 T2 ε) EffectPure

(* From val_rel_at_type intro *)
Σ' : store_ty
Hext : store_ty_extends Σ Σ'
x, y : expr                                (* argument values *)
Hvx : value x
Hvy : value y
Hcx : closed_expr x
Hcy : closed_expr y
Hxyrel : val_rel_n 1 Σ' T1 x y             (* arguments related at step 1 *)
st1, st2 : store
ctx : effect_ctx
Hstrel : store_rel_n 1 Σ' st1 st2          (* stores related at step 1 *)
```

### Goal at Line 1140
```coq
exists v1' v2' st1' st2' ctx' Σ'',
  store_ty_extends Σ' Σ'' /\
  (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
  (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
  val_rel_n 0 Σ'' T2 v1' v2' /\
  store_rel_n 0 Σ'' st1' st2'
```

### What val_rel_n 0 Means
```coq
(* For FO T2: requires structural equality *)
val_rel_n 0 Σ'' T2 v1' v2' = val_rel_at_type_fo T2 v1' v2'

(* For HO T2: just typing *)
val_rel_n 0 Σ'' T2 v1' v2' =
  value v1' /\ value v2' /\ closed v1' /\ closed v2' /\
  has_type nil Σ'' Public v1' T2 EffectPure /\
  has_type nil Σ'' Public v2' T2 EffectPure

(* store_rel_n 0: just size equality *)
store_rel_n 0 Σ'' st1' st2' = (store_max st1' = store_max st2')
```

## APPROACH

### Strategy: Use Type Safety + Semantic Justification

1. **For HO T2**: Use progress + preservation
   - Progress: `EApp v1 x` steps (v1 is lambda, x is value)
   - Preservation: result is well-typed at T2
   - This gives val_rel_n 0 for HO T2

2. **For FO T2**: Requires non-interference property
   - Semantic justification: In actual use, v1 = v2 (Fundamental Theorem relates term to itself)
   - With v1 = v2 and x related to y, results are deterministically equal

### Key Lemmas Available
```coq
(* From type_system/Progress.v *)
Theorem progress : forall e T ε st ctx Σ,
  has_type nil Σ Public e T ε -> store_wf Σ st ->
  value e \/ exists e' st' ctx', (e, st, ctx) --> (e', st', ctx').

(* From type_system/Preservation.v *)
Theorem preservation : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε -> store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  exists Σ' ε', store_ty_extends Σ Σ' /\ store_wf Σ' st' /\
                has_type nil Σ' Public e' T ε'.

(* From type_system/Preservation.v - for values *)
Lemma value_has_pure_effect : forall v T ε Σ,
  value v -> has_type nil Σ Public v T ε ->
  has_type nil Σ Public v T EffectPure.

(* Multi-step preservation - already proven *)
Lemma multi_step_preservation : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε -> store_wf Σ st ->
  (e, st, ctx) -->* (e', st', ctx') ->
  exists Σ', store_ty_extends Σ Σ' /\ store_wf Σ' st' /\
             has_type nil Σ' Public e' T ε.
```

### Proof Sketch
```coq
(* At line 1140, n = 0, T = TFn T1 T2 ε *)

(* Step 1: Get typing for v1 and v2 *)
assert (Hty_v1: has_type nil Σ Public v1 (TFn T1 T2 ε) EffectPure).
{ apply Hty1. reflexivity. }
assert (Hty_v2: has_type nil Σ Public v2 (TFn T1 T2 ε) EffectPure).
{ apply Hty2. reflexivity. }

(* Step 2: Get typing for applications *)
(* EApp v1 x has type T2 *)
assert (Hty_app1: has_type nil Σ' Public (EApp v1 x) T2 _).
{ eapply T_App; [apply store_ty_extends_typing; eassumption | ...]. }

(* Step 3: Use progress - applications step *)
(* v1 is a value of function type, so by canonical forms it's a lambda *)
(* EApp lambda x steps via ST_AppAbs *)

(* Step 4: Use multi_step_preservation for termination + typing *)
(* Applications terminate with well-typed results *)

(* Step 5: For store_rel_n 0, show store_max equality *)
(* This follows from determinism if stores only grow monotonically *)

(* Step 6: For val_rel_n 0 at T2:
   - If T2 is HO: typing from preservation suffices
   - If T2 is FO: need structural equality - SEMANTIC ASSUMPTION:
     In non-interference, v1 = v2 (same program on both sides)
     With v1 = v2, x related to y (at step 1 FO means x = y),
     results are deterministically equal *)
```

## DELIVERABLE

Provide a complete Coq proof that fills the admit at line 1140. The proof should:

1. Use progress/preservation for termination and typing
2. Handle both HO T2 (typing suffices) and FO T2 (structural equality) cases
3. Document any semantic assumptions clearly
4. Be self-contained and ready to paste into the file

If the proof requires additional lemmas, provide them as well.

## CONSTRAINTS

- Do NOT change the definition of val_rel_n or other core definitions
- Do NOT add new axioms
- Use only lemmas already in the codebase (Progress.v, Preservation.v, NonInterference_v2.v)
- If absolutely necessary, add admits with clear semantic justification

## REFERENCE FILES
- `02_FORMAL/coq/properties/NonInterference_v2.v` (main file)
- `02_FORMAL/coq/type_system/Progress.v` (progress theorem)
- `02_FORMAL/coq/type_system/Preservation.v` (preservation, multi_step_preservation)
- `02_FORMAL/coq/foundations/Syntax.v` (types, expressions)
- `02_FORMAL/coq/foundations/Semantics.v` (step relation)
- `02_FORMAL/coq/foundations/Typing.v` (typing rules)
