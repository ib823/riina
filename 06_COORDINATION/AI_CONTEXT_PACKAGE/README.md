# AI Context Package for RIINA Proof Delegation

## Contents

| File | Description | Lines |
|------|-------------|-------|
| `01_NonInterference_Definitions.v` | Core logical relation definitions | 400 |
| `02_Syntax.v` | Type and expression syntax | 300 |
| `03_Semantics.v` | Operational semantics | 200 |
| `04_StoreRelation.v` | Store typing and relations | 200 |
| `05_CumulativeRelation.v` | Cumulative step-indexed relations | 250 |

## Key Definitions to Understand

### val_rel_n (Step-Indexed Value Relation)
```coq
(* Values v1, v2 are related at type T with step index n *)
val_rel_n : nat -> store_typing -> type -> expr -> expr -> Prop

val_rel_n 0 Σ T v1 v2 :=
  (* Base case - structural information only *)

val_rel_n (S n) Σ T v1 v2 :=
  val_rel_n n Σ T v1 v2 /\ val_rel_struct Σ ... T v1 v2
```

### first_order_type
```coq
(* Returns true if type has no function arrows *)
first_order_type : type -> bool

first_order_type TUnit = true
first_order_type TInt = true
first_order_type TBool = true
first_order_type (TFn _ _ _ _) = false  (* Functions are higher-order *)
first_order_type (TProd T1 T2) = first_order_type T1 && first_order_type T2
first_order_type (TSum T1 T2) = first_order_type T1 && first_order_type T2
```

### store_rel_n (Step-Indexed Store Relation)
```coq
(* Stores st1, st2 are related with step index n *)
store_rel_n : nat -> store_typing -> store -> store -> Prop

store_rel_n 0 Σ st1 st2 := True
store_rel_n (S n) Σ st1 st2 :=
  store_rel_n n Σ st1 st2 /\
  max_loc st1 = max_loc st2 /\
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
    exists v1 v2, store_lookup l st1 = Some v1 /\
                  store_lookup l st2 = Some v2 /\
                  val_rel_n n Σ T v1 v2
```

## How to Use

1. Copy relevant context file(s) to your AI prompt
2. Add the lemma statement from `AI_DELEGATION_PROMPTS.md`
3. Include the proof strategy hints
4. Request a complete Coq proof with `Qed.`

## Validation

After receiving a proof:
1. Paste into the original `.v` file
2. Run `coqc` to verify compilation
3. Check that `Qed.` succeeds (not `Admitted.`)

## Priority Order

1. **P0 (3 lemmas):** val_rel_n_mono, val_rel_n_step_up, store_rel_n_step_up
2. **P1 (12 lemmas):** Bridge lemmas, reference operations
3. **P2 (30 lemmas):** Everything else

Start with P0 - they unblock the most downstream work.
