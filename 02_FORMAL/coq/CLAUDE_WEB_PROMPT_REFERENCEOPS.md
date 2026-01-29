# PROMPT: Fix 6 Admits in ReferenceOps.v

You are working on a Coq 8.18+ (also compiles with Rocq 9.1) formal verification codebase called RIINA. You must fix ALL 6 `Admitted` statements in the file `properties/ReferenceOps.v`.

**CRITICAL RULES:**
- Output the COMPLETE replacement file (all 249 lines, modified)
- Every `Admitted.` must become `Qed.` with a complete proof
- Do NOT change any existing `Qed.` proofs — they already compile
- Do NOT add new axioms
- Do NOT change lemma signatures
- Use ONLY the available infrastructure listed below

---

## THE FILE TO FIX (properties/ReferenceOps.v)

```coq
(** * ReferenceOps.v

    RIINA Reference Operations Semantic Typing Proofs

    This file proves the semantic typing lemmas for reference operations:
    - logical_relation_ref (Axiom 16): Reference creation preserves relation
    - logical_relation_deref (Axiom 17): Dereference preserves relation
    - logical_relation_assign (Axiom 18): Assignment preserves relation
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.
Require Import Arith.PeanoNat.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.type_system.Preservation.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.LexOrder.
Require Import RIINA.properties.FirstOrderComplete.
Require Import RIINA.properties.CumulativeRelation.
Require Import RIINA.properties.CumulativeMonotone.
Require Import RIINA.properties.KripkeProperties.
Require Import RIINA.properties.StoreRelation.

Import ListNotations.
```

### THE 6 ADMITS TO FIX

**Admit 1 (line 63): multi_step_ref_inversion**
```coq
Lemma multi_step_ref_inversion : forall e sl st v st' ctx,
  multi_step (ERef e sl, st, ctx) (v, st', ctx) ->
  value v ->
  exists v_inner st_mid l,
    multi_step (e, st, ctx) (v_inner, st_mid, ctx) /\
    value v_inner /\
    v = ELoc l /\
    st' = store_update l v_inner st_mid /\
    l = fresh_loc st_mid.
```

**Admit 2 (line 76): multi_step_deref_inversion**
```coq
Lemma multi_step_deref_inversion : forall e st v st' ctx,
  multi_step (EDeref e, st, ctx) (v, st', ctx) ->
  value v ->
  exists l st_mid,
    multi_step (e, st, ctx) (ELoc l, st_mid, ctx) /\
    st' = st_mid /\
    store_lookup l st_mid = Some v.
```

**Admit 3 (line 91): multi_step_assign_inversion**
```coq
Lemma multi_step_assign_inversion : forall e1 e2 st v st' ctx,
  multi_step (EAssign e1 e2, st, ctx) (v, st', ctx) ->
  value v ->
  exists l v_val st_mid1 st_mid2,
    multi_step (e1, st, ctx) (ELoc l, st_mid1, ctx) /\
    multi_step (e2, st_mid1, ctx) (v_val, st_mid2, ctx) /\
    value v_val /\
    v = EUnit /\
    st' = store_update l v_val st_mid2.
```

**Admit 4 (line 156): exp_rel_le_ref**
```coq
Lemma exp_rel_le_ref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ T e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ (TRef T sl) (ERef e1 sl) (ERef e2 sl) st1 st2 ctx.
```

**Admit 5 (line 192): exp_rel_le_deref**
```coq
Lemma exp_rel_le_deref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ T (EDeref e1) (EDeref e2) st1 st2 ctx.
```

**Admit 6 (line 234): exp_rel_le_assign**
```coq
Lemma exp_rel_le_assign : forall n Σ T sl e1 e2 e1' e2' st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  exp_rel_le n Σ T e1' e2' st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ TUnit (EAssign e1 e1') (EAssign e2 e2') st1 st2 ctx.
```

---

## AVAILABLE INFRASTRUCTURE (from dependency files — these are PROVEN and available)

### From Semantics.v — Step Rules for References

```coq
(* ERef steps *)
| ST_RefStep : forall e e' l st st' ctx ctx',
    (e, st, ctx) --> (e', st', ctx') ->
    (ERef e l, st, ctx) --> (ERef e' l, st', ctx')
| ST_RefValue : forall v sl st ctx l,
    value v ->
    l = fresh_loc st ->
    (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)

(* EDeref steps *)
| ST_DerefStep : forall e e' st st' ctx ctx',
    (e, st, ctx) --> (e', st', ctx') ->
    (EDeref e, st, ctx) --> (EDeref e', st', ctx')
| ST_DerefLoc : forall v l st ctx,
    store_lookup l st = Some v ->
    (EDeref (ELoc l), st, ctx) --> (v, st, ctx)

(* EAssign steps *)
| ST_Assign1 : forall e1 e1' e2 st st' ctx ctx',
    (e1, st, ctx) --> (e1', st', ctx') ->
    (EAssign e1 e2, st, ctx) --> (EAssign e1' e2, st', ctx')
| ST_Assign2 : forall v1 e2 e2' st st' ctx ctx',
    value v1 ->
    (e2, st, ctx) --> (e2', st', ctx') ->
    (EAssign v1 e2, st, ctx) --> (EAssign v1 e2', st', ctx')
| ST_AssignLoc : forall v1 l st ctx,
    store_lookup l st = Some v1 ->
    forall v2, value v2 ->
    (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)
```

### From Semantics.v — Multi-step and Determinism

```coq
Inductive multi_step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.

(* PROVEN — available to use *)
Lemma value_not_step : forall v st ctx cfg, value v -> ~ ((v, st, ctx) --> cfg).
Theorem step_deterministic_cfg : forall cfg cfg1 cfg2, step cfg cfg1 -> step cfg cfg2 -> cfg1 = cfg2.
```

### From Semantics.v — Values (IMPORTANT: ERef, EDeref, EAssign are NOT values)

```coq
Inductive value : expr -> Prop :=
  | VUnit   : value EUnit
  | VBool   : forall b, value (EBool b)
  | VInt    : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc    : forall l, value (ELoc l)
  | VLam    : forall x T e, value (ELam x T e)
  | VPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl    : forall v T, value v -> value (EInl v T)
  | VInr    : forall v T, value v -> value (EInr v T)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve  : forall v, value v -> value (EProve v).
```

### From CumulativeRelation.v — exp_rel_le definition

```coq
Definition exp_rel_le (n : nat) (Σ : store_ty) (T : ty)
    (e1 e2 : expr) (st1 st2 : store) (ctx : effect_ctx) : Prop :=
  forall k v1 v2 st1' st2' ctx',
    k <= n ->
    multi_step (e1, st1, ctx) (v1, st1', ctx') ->
    multi_step (e2, st2, ctx) (v2, st2', ctx') ->
    value v1 -> value v2 ->
    exists Σ',
      store_ty_extends Σ Σ' /\
      val_rel_le k Σ' T v1 v2 /\
      store_rel_simple Σ' st1' st2'.
```

### From CumulativeRelation.v / StoreRelation.v — Available helper lemmas

```coq
(* All PROVEN — available *)
Lemma val_rel_le_build_ref : ... (* builds val_rel_le for TRef *)
Lemma val_rel_le_unit : ... (* val_rel_le for TUnit *)
Lemma store_rel_le_lookup : forall n Σ st1 st2 l T sl,
  store_rel_le n Σ st1 st2 ->
  store_ty_lookup l Σ = Some (T, sl) ->
  exists v1 v2,
    store_lookup l st1 = Some v1 /\
    store_lookup l st2 = Some v2 /\
    val_rel_le n Σ T v1 v2.
Lemma store_rel_le_update : ... (* store_rel_le after update *)
Lemma store_max_update_eq : ... (* store_max preserved by updates *)
Lemma store_alloc_same : forall Σ st1 st2, store_rel_simple Σ st1 st2 -> fresh_loc st1 = fresh_loc st2.
Lemma store_ty_extends_alloc : ... (* extending store_ty *)
Lemma fresh_loc_not_in_store_ty : ... (* fresh loc not in store typing *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3, store_ty_extends Σ1 Σ2 -> store_ty_extends Σ2 Σ3 -> store_ty_extends Σ1 Σ3.
```

---

## PROOF STRATEGY

### For Admits 1-3 (multi_step inversion):

Use `remember` + induction on `multi_step`. Pattern:

1. `remember (ERef e sl, st, ctx) as start`. `remember (v, st', ctx) as finish`.
2. Induction on `H : multi_step start finish`.
3. **MS_Refl case**: `start = finish`, so `ERef e sl = v`. But `v` is a value and `ERef` is NOT a value constructor — contradiction via `inversion` on the value hypothesis.
4. **MS_Step case**: `start --> cfg2 -->* finish`. `inversion` on `start --> cfg2`:
   - **ST_RefStep**: `cfg2 = (ERef e' sl, st'', ctx')`. The sub-expression stepped. Apply IH. Build up the multi_step for `e`.
   - **ST_RefValue**: `e` is already a value `v_inner`. `cfg2 = (ELoc l, store_update l v_inner st, ctx)`. Then `cfg2 -->* finish` with `ELoc l` being a value. So `finish = cfg2` (by value_not_step on further steps). Extract witnesses.
   - Other step constructors: impossible (ERef only matches ST_RefStep and ST_RefValue).

**IMPORTANT**: When doing `inversion` on `(ERef e sl, st, ctx) --> cfg2`, you need to handle the fact that `ctx` and `ctx'` may differ. The step relation allows `ctx --> ctx'`. The conclusion requires `ctx = ctx` (same context throughout). You need to track that the context is preserved.

### For Admits 4-6 (exp_rel_le composition):

Unfold `exp_rel_le`. Given evaluations of `ERef e1 sl` and `ERef e2 sl`, use multi_step_ref_inversion to decompose into evaluations of `e1` and `e2`. Apply the hypothesis `exp_rel_le n Σ T e1 e2 st1 st2 ctx` to get related values. Then apply `logical_relation_ref_proven` to get the final result.

---

## OUTPUT

Provide the COMPLETE `properties/ReferenceOps.v` file with all 6 admits replaced by proofs ending in `Qed.`. Keep all existing comments and proven lemmas unchanged. The file must compile with the listed imports.
