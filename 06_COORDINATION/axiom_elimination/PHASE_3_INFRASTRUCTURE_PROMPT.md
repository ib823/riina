# PHASE 3: Infrastructure Helper Lemmas - COMPLETE PROMPT

**Mode:** ULTRA KIASU | ZERO TRUST | QED ETERNUM
**Target:** 6 Infrastructure Admits from Phase 2 Patch
**Context:** These lemmas support `val_rel_at_type_TFn_step_0_bridge` in NonInterference_v2.v

---

## CRITICAL CONTEXT

### Phase 2 Outcome (SUCCESSFUL)
Phase 2 eliminated 3 main admits from NonInterference_v2.v:
1. `val_rel_at_type_step_up_with_IH` (line 1376) - Already complete, just Admitted → Qed
2. `combined_step_up_all` (line 1541 + 2067) - Uses bridge lemma
3. `val_rel_at_type_TFn_step_0_bridge` (line 2437) - Uses `well_typed_SN`

### Key Dependency: well_typed_SN (PROVEN)
```coq
(* From ReducibilityFull_FINAL.v - PROVEN *)
Theorem well_typed_SN : forall Σ pc e T ε,
  has_type nil Σ pc e T ε -> SN_expr e.
Proof. (* ... *) Qed.
```

### The Bridge Lemma (Complete Proof Structure)
```coq
Lemma val_rel_at_type_TFn_step_0_bridge : forall Σ T1 T2 eff v1 v2,
  has_type nil Σ Public v1 (TFn T1 T2 eff) EffectPure ->
  has_type nil Σ Public v2 (TFn T1 T2 eff) EffectPure ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  forall Σ', store_ty_extends Σ Σ' ->
    forall x y,
      value x -> value y -> closed_expr x -> closed_expr y ->
      val_rel_n 0 Σ' T1 x y ->
      forall st1 st2 ctx,
        store_rel_n 0 Σ' st1 st2 ->
        store_wf Σ' st1 ->
        store_wf Σ' st2 ->
        stores_agree_low_fo Σ' st1 st2 ->
        exists v1' v2' st1' st2' ctx' Σ'',
          (* ... all the existentials ... *)
```

---

## 6 HELPER LEMMAS TO PROVE

### Lemma 1: store_ty_extends_has_type (Store Typing Weakening)
```coq
Lemma store_ty_extends_has_type : forall Γ Σ Σ' pc e T ε,
  has_type Γ Σ pc e T ε ->
  store_ty_extends Σ Σ' ->
  has_type Γ Σ' pc e T ε.
```

**PROOF STRATEGY:**
- Standard weakening lemma
- Induction on typing derivation `has_type Γ Σ pc e T ε`
- Most cases are structural (IH application)
- Key cases:
  - `T_Loc`: Need `store_ty_extends` to carry `store_ty_lookup l Σ` to `store_ty_lookup l Σ'`
  - `T_Ref`: Similar store typing preservation
  - `T_Deref`, `T_Assign`: Need location type preservation

**HINT:** `store_ty_extends Σ Σ'` means `∀ l T sl, store_ty_lookup l Σ = Some (T, sl) → store_ty_lookup l Σ' = Some (T, sl)`

---

### Lemma 2: value_typing_from_val_rel_FO (Value Typing from FO Relation)
```coq
Lemma value_typing_from_val_rel_FO : forall Σ v1 v2 T,
  value v1 ->
  val_rel_n 0 Σ T v1 v2 ->
  first_order_type T = true ->
  has_type nil Σ Public v1 T EffectPure.
```

**PROOF STRATEGY:**
- For FO types, `val_rel_n 0` gives `val_rel_at_type_fo` which is structural equality
- Use `canonical_forms` lemmas to extract structure
- Reconstruct typing from value structure

**STRUCTURE of val_rel_n 0 for FO types:**
```coq
val_rel_n 0 Σ T v1 v2 =
  value v1 ∧ value v2 ∧ closed_expr v1 ∧ closed_expr v2 ∧
  val_rel_at_type_fo T v1 v2
```

Where `val_rel_at_type_fo` gives structural equality:
- `TUnit`: `v1 = EUnit ∧ v2 = EUnit`
- `TBool`: `v1 = EBool b ∧ v2 = EBool b` (same b)
- `TInt`: `v1 = EInt n ∧ v2 = EInt n` (same n)
- `TProd T1 T2`: `v1 = EPair x1 y1 ∧ v2 = EPair x2 y2` with recursive relation

---

### Lemma 3: val_rel_n_0_symmetric_FO (FO Relation is Symmetric)
```coq
Lemma val_rel_n_0_symmetric_FO : forall Σ T v1 v2,
  first_order_type T = true ->
  val_rel_n 0 Σ T v1 v2 ->
  val_rel_n 0 Σ T v2 v1.
```

**PROOF STRATEGY:**
- Induction on type T (with `first_order_type T = true` constraint)
- For base types: structural equality is symmetric
- For TProd/TSum: recursive application of symmetry
- Key insight: `val_rel_at_type_fo` is structural equality, which is symmetric

**CASES:**
```coq
| TUnit => v1 = EUnit ∧ v2 = EUnit  (* trivially symmetric *)
| TBool => v1 = EBool b ∧ v2 = EBool b  (* symmetric *)
| TInt => v1 = EInt n ∧ v2 = EInt n  (* symmetric *)
| TProd T1 T2 => ∃ components with recursive val_rel_at_type_fo  (* IH *)
| TSum T1 T2 => same branch with recursive  (* IH *)
```

---

### Lemma 4: FO_noninterference_pure (First-Order Non-Interference)
```coq
Lemma FO_noninterference_pure : forall Σ T1 T2 eff x1 x2 body1 body2 arg1 arg2 st1 st2 ctx r1 r2,
  first_order_type T2 = true ->
  val_rel_n 0 Σ T1 arg1 arg2 ->
  stores_agree_low_fo Σ st1 st2 ->
  (EApp (ELam x1 T1 body1) arg1, st1, ctx) -->* (r1, _, _) ->
  (EApp (ELam x2 T1 body2) arg2, st2, ctx) -->* (r2, _, _) ->
  value r1 -> value r2 ->
  @val_rel_at_type_fo T2 r1 r2.
```

**PROOF STRATEGY:**
This is the key non-interference lemma for first-order results:
1. For FO types, evaluation is determined by observable (low) parts of input
2. `val_rel_n 0` for FO T1 means `arg1` and `arg2` are structurally equal
3. `stores_agree_low_fo` means low parts of stores are equal
4. Pure evaluation (`EffectPure`) doesn't read high data
5. Therefore results must be structurally equal

**SIMPLIFICATION:** If `arg1 = arg2` (which holds for FO types with `val_rel_n 0`), then:
- Same function bodies with same arguments in agreeing stores
- Deterministic evaluation produces same results
- `r1 = r2` (or at least structurally equal at FO type T2)

**NOTE:** This may need more infrastructure if bodies differ. For the bridge lemma, we actually need same-expression non-interference, which is simpler.

---

### Lemma 5: store_rel_preserved_pure (Pure Preserves Store Relation)
```coq
Lemma store_rel_preserved_pure : forall st1 st2 st1' st2' Σ eff,
  store_rel_n 0 Σ st1 st2 ->
  (* Pure evaluations don't modify stores observably *)
  store_rel_n 0 Σ st1' st2'.
```

**PROOF STRATEGY:**
- For pure effects, stores are not modified at all
- `st1' = st1` and `st2' = st2`
- Therefore `store_rel_n 0 Σ st1' st2' = store_rel_n 0 Σ st1 st2`

**STRONGER VERSION (if needed):**
```coq
Lemma store_rel_preserved_pure : forall e1 e2 st1 st2 st1' st2' v1 v2 ctx ctx' Σ T eff,
  store_rel_n 0 Σ st1 st2 ->
  has_type nil Σ Public e1 T EffectPure ->  (* Key: EffectPure *)
  has_type nil Σ Public e2 T EffectPure ->
  (e1, st1, ctx) -->* (v1, st1', ctx') ->
  (e2, st2, ctx) -->* (v2, st2', ctx') ->
  store_rel_n 0 Σ st1' st2'.
Proof.
  (* Pure effect means no store writes, so st1' = st1, st2' = st2 *)
  intros.
  (* Use pure_no_store_modification lemma if available *)
  (* Otherwise: trace through evaluation showing stores unchanged *)
```

---

### Lemma 6: stores_agree_preserved_pure (Pure Preserves Agreement)
```coq
Lemma stores_agree_preserved_pure : forall Σ st1 st2 st1' st2',
  stores_agree_low_fo Σ st1 st2 ->
  (* Pure evaluations preserve agreement *)
  stores_agree_low_fo Σ st1' st2'.
```

**PROOF STRATEGY:**
- Same as Lemma 5: pure effects don't modify stores
- `st1' = st1` and `st2' = st2` for pure evaluation
- Agreement is trivially preserved

**NOTE:** Both Lemmas 5 and 6 rely on:
```coq
Lemma pure_no_store_modification : forall e v st st' ctx ctx' Σ T,
  has_type nil Σ Public e T EffectPure ->
  (e, st, ctx) -->* (v, st', ctx') ->
  st' = st.
```
This should exist or be easily provable from the operational semantics.

---

## KEY DEFINITIONS NEEDED

### store_ty_extends
```coq
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
                 store_ty_lookup l Σ' = Some (T, sl).
```

### val_rel_n 0 structure for FO types
```coq
val_rel_n 0 Σ T v1 v2 :=
  if first_order_type T then
    value v1 ∧ value v2 ∧ closed_expr v1 ∧ closed_expr v2 ∧
    val_rel_at_type_fo T v1 v2
  else
    value v1 ∧ value v2 ∧ closed_expr v1 ∧ closed_expr v2 ∧
    has_type nil Σ Public v1 T EffectPure ∧
    has_type nil Σ Public v2 T EffectPure
```

### stores_agree_low_fo
```coq
Definition stores_agree_low_fo (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    is_low sl ->
    first_order_type T = true ->
    store_lookup l st1 = store_lookup l st2.
```

---

## DELIVERABLES

For each lemma, provide:
1. **Complete Qed proof** in Coq
2. **Any additional helper lemmas** needed (with proofs)

### OUTPUT FORMAT
```coq
(** ============================================================
    LEMMA 1: store_ty_extends_has_type
    ============================================================ *)

Lemma store_ty_extends_has_type : forall Γ Σ Σ' pc e T ε,
  has_type Γ Σ pc e T ε ->
  store_ty_extends Σ Σ' ->
  has_type Γ Σ' pc e T ε.
Proof.
  (* Your complete proof here *)
Qed.

(** ============================================================
    LEMMA 2: value_typing_from_val_rel_FO
    ============================================================ *)
(* ... etc ... *)
```

---

## PRIORITY ORDER

1. **store_ty_extends_has_type** - Standard weakening, most foundational
2. **value_typing_from_val_rel_FO** - Needed for argument typing
3. **val_rel_n_0_symmetric_FO** - Needed for symmetric argument typing
4. **store_rel_preserved_pure** - Needed for result store relation
5. **stores_agree_preserved_pure** - Needed for result agreement
6. **FO_noninterference_pure** - Most complex, may need simplification

---

## AVAILABLE INFRASTRUCTURE

From the RIINA codebase:
- `canonical_forms_*` lemmas for extracting value structure
- `substitution_preserves_typing` for typing after substitution
- `preservation_typing` for single-step preservation
- `typing_nil_implies_closed` for closed from nil-context typing
- `val_rel_n_0_unfold`, `val_rel_n_S_unfold` for relation unfolding
- `store_rel_n_0_unfold`, `store_rel_n_S_unfold` for store relation unfolding
- `first_order_type` function for FO type check

---

**Mode:** ULTRA KIASU | ZERO TRUST | QED ETERNUM
**Goal:** 6 infrastructure admits → 0 admits
