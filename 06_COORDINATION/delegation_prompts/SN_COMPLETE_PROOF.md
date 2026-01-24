# Strong Normalization Complete Proof Delegation

## STATUS: ACTIVE DELEGATION
## Priority: P0 - Critical Path

## OBJECTIVE
Prove Strong Normalization for well-typed RIINA terms, eliminating the 2 remaining admits in ReducibilityFull.v, which will enable eliminating the final admit in NonInterference_v2.v.

## CURRENT STATE

### Files Involved
1. **`02_FORMAL/coq/termination/ReducibilityFull.v`** - Main reducibility proof (2 admits)
2. **`02_FORMAL/coq/properties/SN_Closure.v`** - SN closure lemmas (COMPLETE)
3. **`02_FORMAL/coq/properties/NonInterference_v2.v`** - Uses SN (1 admit remaining)

### The 2 Admits in ReducibilityFull.v

#### Admit 1 (Line 546): T_App Beta Case
```
Context: Inside fundamental_reducibility, T_App case, after beta reduction
Goal: Show substituted body [x := arg] body is SN
Problem: SN_app requires: forall x body v st' ctx', value v -> SN ([x := v] body, st', ctx')
         This is a universal premise for ANY lambda body, but we only have IH for e1 (the function)

Available:
  - IHHty1 : forall ρ, env_reducible Γ ρ -> SN_expr (subst_env ρ e1)
  - IHHty2 : forall ρ, env_reducible Γ ρ -> SN_expr (subst_env ρ e2)
  - substitution_preserves_typing: PROVEN in Preservation.v (line 512)

Issue: We need IH for the BODY of whatever lambda e1 reduces to, but we only have IH for e1.
       The lambda body's typing is encapsulated in the T_Lam derivation inside T_App.

Potential Fixes:
  1. Use type-directed Reducible definition (standard Tait/Girard approach)
  2. Do induction on typing derivation + preservation to extract body typing
  3. Add explicit beta-reducibility premise to fundamental theorem
```

#### Admit 2 (Line 627): T_Deref Store Invariant
```
Context: Inside fundamental_reducibility, T_Deref case
Goal: Show that store_lookup returns a value (for SN_deref premise)
Problem: SN_deref requires: forall l v st', store_lookup l st' = Some v -> value v
         This is universal over ALL stores st', not just well-formed ones

Current Situation:
  - fundamental_reducibility proves: forall st ctx, SN (subst_env ρ e, st, ctx)
  - This quantifies over all stores, including malformed ones
  - We can't prove store well-formedness holds for arbitrary stores

Potential Fixes:
  1. Thread store_wf as a hypothesis through fundamental_reducibility
  2. Modify SN_deref to only require well-formedness for the specific store
  3. Use evaluation semantics that only work with well-formed stores

Note: Typing.v store_wf (line 215) already proves: store_ty_lookup l Σ = Some (T, sl)
      implies exists v such that store_lookup l st = Some v /\ value v /\ has_type ...
```

## PROOF STRUCTURE

### Reducibility Definition (Already in file)
```coq
(* Reducible expressions are SN and reduce to reducible values *)
Fixpoint Reducible (Σ : store_ty) (T : ty) (e : expr) : Prop :=
  SN_expr e /\
  match T with
  | TUnit => True
  | TBool => True
  | TInt => True
  | TFn T1 T2 _ =>
      forall a, Reducible Σ T1 a ->
        forall st ctx, Reducible Σ T2 (EApp e a) (* needs refinement *)
  | TProd T1 T2 =>
      (exists v1 v2, ... /\ Reducible Σ T1 v1 /\ Reducible Σ T2 v2)
  | TSum T1 T2 =>
      (exists v, value v /\ (Inl case \/ Inr case))
  | TRef T => True (* locations are values *)
  | ... (* other types *)
  end.
```

### Key Lemmas Needed

#### 1. Substitution Preserves Typing
```coq
Lemma substitution_preserves_typing : forall Γ Σ pc x T1 e T ε v,
  has_type ((x, T1) :: Γ) Σ pc e T ε ->
  has_type nil Σ pc v T1 EffectPure ->
  value v ->
  has_type Γ Σ pc ([x := v] e) T ε.
```
This should already exist in `type_system/Preservation.v` or similar.

#### 2. Store Typing Invariant
```coq
Lemma store_wf_lookup_typed : forall Σ st l T sl v,
  store_wf Σ st ->
  store_ty_lookup l Σ = Some (T, sl) ->
  store_lookup l st = Some v ->
  has_type nil Σ Public v T EffectPure /\ value v.
```
This follows from the definition of store_wf.

#### 3. Reducibility Backward Closure
```coq
Lemma Reducible_step_back : forall Σ T e e' st st' ctx ctx',
  (e, st, ctx) --> (e', st', ctx') ->
  Reducible Σ T e' ->
  Reducible Σ T e.
```
This is the key: reducibility is closed under reverse evaluation.

## PROOF APPROACH

### For Admit 1 (T_App):
1. We have `has_type ((x, T1) :: Γ) Σ pc body T2 ε` (from T_Lam typing)
2. We have `Reducible Σ T1 arg` (from IH on argument)
3. Reducible implies `has_type nil Σ pc arg T1 EffectPure` and `value arg`
4. Apply substitution_preserves_typing to get typing for `[x := arg] body`
5. Apply IH for body with environment substitution ρ[x := arg]

### For Admit 2 (T_Deref):
1. We have `store_wf Σ st` (from evaluation premise)
2. We have `store_ty_lookup l Σ = Some (T, sl)` (from T_Ref typing)
3. Apply store_wf_lookup_typed to get `has_type nil Σ Public v T EffectPure`
4. Use fundamental_reducibility (IH) to get `Reducible Σ T v`

## EXISTING INFRASTRUCTURE

### In SN_Closure.v (COMPLETE):
- `value_SN` - values are SN
- `SN_app` - application closure (needs beta premise)
- `SN_pair`, `SN_fst`, `SN_snd` - pair operations
- `SN_inl`, `SN_inr`, `SN_case` - sum operations
- `SN_if`, `SN_let` - control flow
- `SN_ref`, `SN_deref`, `SN_assign` - references
- `SN_handle`, `SN_classify`, `SN_declassify` - effects

### In Preservation.v:
- `preservation` - single step preserves typing
- `multi_step_preservation` - multi-step version
- Look for `substitution_preserves_typing` or similar

### In Typing.v:
- `canonical_forms_*` - extract value structure from typing
- `store_wf` definition

## DELIVERABLES

1. **Fix Admit 1 (Line 546)**:
   - Find or prove `substitution_preserves_typing`
   - Complete the T_App beta case

2. **Fix Admit 2 (Line 627)**:
   - Prove `store_wf_lookup_typed` lemma
   - Complete the T_Deref case

3. **Verify Build**:
   - `make` in `02_FORMAL/coq/` must pass
   - `well_typed_SN` theorem must be usable

## SUCCESS CRITERIA

After completion:
- ReducibilityFull.v: 0 admits
- `well_typed_SN` theorem proven
- Can use `well_typed_SN` to prove NonInterference_v2.v line 1541

## COMMANDS TO VERIFY

```bash
cd /workspaces/proof/02_FORMAL/coq
make termination/ReducibilityFull.vo
grep -n "admit\." termination/ReducibilityFull.v  # Should be empty
```

## ESTIMATED EFFORT
- Admit 1 (substitution): 2-4 hours
- Admit 2 (store invariant): 1-2 hours
- Integration testing: 1 hour
- Total: 4-7 hours focused work
