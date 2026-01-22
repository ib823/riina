# Package N: Termination & Miscellaneous Admits

## Task

Prove the 6 remaining admits related to termination and miscellaneous properties.

## Files & Admits

| File | Admits | Focus |
|------|--------|-------|
| `ReducibilityFull.v` | 2 | Full reducibility for termination |
| `NonInterference_v2.v` | 2 | Core NI (val_rel_n_step_up for HO) |
| `SN_Closure.v` | 1 | Strong normalization closure |
| `ValRelStepLimit_PROOF.v` | 1 | Step limit for val_rel |

## Key Concepts

### Reducibility / Strong Normalization

Reducibility is the technique for proving termination (strong normalization):

```coq
(* A term is reducible if all its reducts are reducible *)
Fixpoint reducible (n : nat) (T : ty) (e : expr) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      value e \/
      (exists e', step e e' /\ reducible n' T e')
  end.

(* Strong normalization: well-typed terms are reducible *)
Theorem strong_normalization : forall Γ Σ e T ε,
  has_type Γ Σ Public e T ε ->
  forall n, reducible n T e.
```

### val_rel_n_step_up (The Key Blocker)

```coq
(* THE critical axiom that blocks many proofs *)
Axiom val_rel_n_step_up : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 ->
  (first_order_type T = false -> has_type [] Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type [] Σ Public v2 T EffectPure) ->
  val_rel_n (S n) Σ T v1 v2.
```

**Why it's hard:** For TFn types, showing `val_rel_n (S n)` requires showing that applying the function to related arguments produces related results. This is circular without termination.

**FO case is PROVEN:** The first-order case of `val_rel_n_step_up` is already proven in `NonInterference_v2.v`.

### Step Limit

```coq
(* Relating step-indexed to operational steps *)
Lemma val_rel_n_implies_terminates_in_n : forall n Σ T e1 e2,
  exp_rel_n n Σ T e1 e2 ->
  (* e1 and e2 terminate within n steps to related values *)
  ...
```

## Strategy

### For ReducibilityFull admits

Check if these are:
1. Structural induction cases (provable)
2. Or depend on strong normalization (blocked)

### For NonInterference_v2 admits

The 2 admits here are likely related to `val_rel_n_step_up`:
- FO case: Already proven
- HO case: Needs termination

**Approach:** Document that HO case requires Track V (Termination Guarantees) completion.

### For SN_Closure

Strong normalization closure properties:
- May be provable from basic induction
- Or may need SN theorem

### For ValRelStepLimit

Likely connecting step-indexed semantics to operational semantics:
- Check if it's definitional
- Or if it needs specific termination lemmas

## Known Blockers

The fundamental blocker is **termination for higher-order types**:

1. `val_rel_n_step_up` for TFn needs to show function application terminates
2. Function application termination needs strong normalization
3. Strong normalization is Track V (not yet complete)

**Recommendation:** For this package, clearly separate:
- What CAN be proven now (FO cases, structural lemmas)
- What is BLOCKED by termination (HO cases)

## Expected Output

| Admit | Likely Status |
|-------|---------------|
| ReducibilityFull #1 | Possibly provable |
| ReducibilityFull #2 | Possibly provable |
| NonInterference_v2 #1 | Blocked (HO step-up) |
| NonInterference_v2 #2 | Blocked (HO step-up) |
| SN_Closure | Check if structural |
| ValRelStepLimit | Check if definitional |

## Deliverables

1. **Prove** any admits that don't require termination
2. **Document** which admits are blocked and why
3. **Dependency map** showing what's needed for blocked admits

## File Locations

```
/workspaces/proof/02_FORMAL/coq/
├── termination/ReducibilityFull.v
├── properties/NonInterference_v2.v
├── properties/SN_Closure.v
└── properties/ValRelStepLimit_PROOF.v
```

## Notes on Track V Integration

Track V (Termination Guarantees) will provide:
- Sized types for termination tracking
- Strong normalization theorem
- Reducibility candidates

Once Track V is complete, the HO cases in this package become provable.
