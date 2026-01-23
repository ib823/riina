# DELEGATION PROMPT: Priority 2 - store_rel Step-Up

## OBJECTIVE
Fill the admit at `NonInterference_v2.v:1209` - store_rel_n step-up within val_rel_n_step_up_by_type.

## CONTEXT

### The Problem
In the higher-order (TFn) case of `val_rel_n_step_up_by_type`, after showing function applications produce related results, we need to step up the store relation from `store_rel_n n'` to `store_rel_n (S n')`.

### Location
- **File:** `02_FORMAL/coq/properties/NonInterference_v2.v`
- **Line:** 1209
- **Function:** `val_rel_n_step_up_by_type`
- **Case:** n = S n', T = TFn T1 T2 ε, stepping up store relation

### Available Hypotheses at Line 1209
```coq
(* From outer context *)
T : ty                                     (* = TFn T1 T2 ε *)
IH : forall T', ty_size T' < ty_size T -> ... -> val_rel_n (S n) Σ T' v1 v2
n' : nat
Σ'' : store_ty
st1', st2' : store
Hstrel_n'' : store_rel_n n' Σ'' st1' st2'  (* stores related at step n' *)

(* From function application context *)
Hext' : store_ty_extends Σ' Σ''
(* Plus various typing and value hypotheses *)
```

### Goal at Line 1209
```coq
store_rel_n (S n') Σ'' st1' st2'
```

### What store_rel_n (S n') Means
```coq
store_rel_n (S n') Σ'' st1' st2' =
  store_rel_n n' Σ'' st1' st2' /\
  store_max st1' = store_max st2' /\
  (forall l T sl,
    store_ty_lookup l Σ'' = Some (T, sl) ->
    exists v1 v2,
      store_lookup l st1' = Some v1 /\
      store_lookup l st2' = Some v2 /\
      val_rel_n n' Σ'' T v1 v2)
```

## APPROACH

### Strategy: Use store_rel_n_step_up Lemma

There's already a `store_rel_n_step_up` lemma at line 1379:

```coq
Lemma store_rel_n_step_up : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_wf Σ st1 ->
  store_wf Σ st2 ->
  store_has_values st1 ->
  store_has_values st2 ->
  stores_agree_low_fo Σ st1 st2 ->  (* Required for n=0 LOW FO bootstrap *)
  store_rel_n (S n) Σ st1 st2.
```

### Key Issue: Preconditions

To use `store_rel_n_step_up`, we need:
1. `store_wf Σ'' st1'` - store well-formedness preserved through evaluation
2. `store_wf Σ'' st2'` - store well-formedness preserved through evaluation
3. `store_has_values st1'` - stores contain only values
4. `store_has_values st2'` - stores contain only values
5. `stores_agree_low_fo Σ'' st1' st2'` - low FO locations agree

### Available Supporting Lemmas

```coq
(* From Preservation.v *)
Theorem preservation : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε -> store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  exists Σ' ε', store_ty_extends Σ Σ' /\ store_wf Σ' st' /\ ...

(* Multi-step version *)
Lemma multi_step_preservation : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε -> store_wf Σ st ->
  (e, st, ctx) -->* (e', st', ctx') ->
  exists Σ', store_ty_extends Σ Σ' /\ store_wf Σ' st' /\ ...

(* store_has_values should be preserved through well-typed evaluation *)
(* stores_agree_low_fo should be preserved if operations don't write to low FO locations *)
```

### Proof Sketch
```coq
(* At line 1209, goal: store_rel_n (S n') Σ'' st1' st2' *)
(* We have: Hstrel_n'' : store_rel_n n' Σ'' st1' st2' *)

(* Step 1: Establish store_wf for st1' and st2' *)
(* Use multi_step_preservation on the application steps *)
assert (Hwf1': store_wf Σ'' st1').
{ (* From Hstep1 : (EApp v1 x, st1, ctx) -->* (v1', st1', ctx')
     and preservation *) ... }
assert (Hwf2': store_wf Σ'' st2').
{ (* Similarly from Hstep2 *) ... }

(* Step 2: Establish store_has_values *)
assert (Hvals1': store_has_values st1').
{ (* Values are preserved through evaluation *) ... }
assert (Hvals2': store_has_values st2').
{ ... }

(* Step 3: Establish stores_agree_low_fo *)
assert (Hagree': stores_agree_low_fo Σ'' st1' st2').
{ (* Low FO locations are not modified by pure function application,
     or if modified, both sides write the same value *) ... }

(* Step 4: Apply store_rel_n_step_up *)
apply store_rel_n_step_up; assumption.
```

## DELIVERABLE

Provide a complete Coq proof that fills the admit at line 1209. The proof should:

1. Establish all preconditions for `store_rel_n_step_up`
2. Use preservation lemmas to maintain store_wf
3. Show store_has_values is preserved
4. Show stores_agree_low_fo is preserved (or add as hypothesis if needed)

If additional lemmas are needed (e.g., `store_has_values_preserved`, `stores_agree_low_fo_preserved`), provide them.

## KEY INSIGHT

The main challenge is showing `stores_agree_low_fo` is preserved through function application. For pure functions:
- If no store operations occur, stores are unchanged
- If store operations occur (ref/assign), they must write the same values to low FO locations for related arguments

This is a consequence of non-interference: related inputs produce related outputs including store effects.

## CONSTRAINTS

- Do NOT change the definition of store_rel_n or val_rel_n
- Use existing lemmas from Preservation.v where possible
- If new lemmas are needed, provide complete proofs
- Document any semantic assumptions

## REFERENCE FILES
- `02_FORMAL/coq/properties/NonInterference_v2.v` (lines 1194-1210, 1379-1466)
- `02_FORMAL/coq/type_system/Preservation.v`
- `02_FORMAL/coq/foundations/Semantics.v`
