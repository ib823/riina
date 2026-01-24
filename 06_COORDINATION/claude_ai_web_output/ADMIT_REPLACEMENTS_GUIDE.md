# RIINA Admit Replacements - Based on Supplement

## Critical Discovery: `store_wf ≡ store_has_values`

Both definitions are identical:
```coq
forall l v, store_lookup l st = Some v -> value v
```

This means **ADMITS 2-5 ARE THE SAME PROBLEM** and the `preservation` theorem already solves them!

---

## ADMIT 1 (Line 1332): Fundamental Theorem n=0

**Context:** Base case, HO type, need `val_rel_at_type` from typing alone.

**Replace:**
```coq
admit.
```

**With:**
```coq
destruct (first_order_type T) eqn:Hfo.
+ (* FO type *)
  eapply val_rel_at_type_fo_equiv. exact Hfo.
  destruct Hcond; assumption.
+ (* HO type *)
  apply fundamental_theorem_n0; try assumption.
  * exact Hfo.
  * apply Hty1; exact Hfo.
  * apply Hty2; exact Hfo.
```

**Required lemma:**
```coq
Lemma fundamental_theorem_n0 : forall T Σ v1 v2,
  first_order_type T = false ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2.
```

---

## ADMITS 2-5 (Lines 1393, 1395, 1397, 1399): Store Preservation

**Context:** After function application, need store properties preserved.

**Key insight:** Since `preservation` already gives `store_wf Σ' st'`, these are trivial!

**For store_wf (Lines 1393, 1395):**
```coq
destruct (preservation e e' T ε st st' ctx ctx' Σ Hty Hwf Hstep) 
  as [Σ' [ε' [Hext [Hwf' Hty']]]].
exact Hwf'.
```

**For store_has_values (Lines 1397, 1399):**
```coq
(* SAME AS ABOVE - they're identical! *)
destruct (preservation e e' T ε st st' ctx ctx' Σ Hty Hwf Hstep) 
  as [Σ' [ε' [Hext [Hwf' Hty']]]].
exact Hwf'.
```

---

## ADMIT 6 (Line 1401): `stores_agree_low_fo` Preservation

**Context:** After related evaluations, low FO agreement preserved.

**Replace:**
```coq
admit.
```

**With:**
```coq
apply preservation_stores_agree_low_fo_multi; try assumption.
```

**Required lemma:**
```coq
Lemma preservation_stores_agree_low_fo_multi :
  forall e1 e2 v1 v2 st1 st2 st1' st2' ctx ctx' Σ T ε,
  (* conditions *)
  stores_agree_low_fo Σ st1 st2 ->
  (* evaluation *)
  (e1, st1, ctx) -->* (v1, st1', ctx') ->
  (e2, st2, ctx) -->* (v2, st2', ctx') ->
  (* result *)
  exists Σ', store_ty_extends Σ Σ' /\ stores_agree_low_fo Σ' st1' st2'.
```

**Note:** For pure function application (β-reduction), the store is unchanged, so this is trivial:
```coq
exists Σ. split. apply store_ty_extends_refl. assumption.
```

---

## ADMITS 7-14 (Nested TProd/TSum): Type Step-Up

**Context:** When T contains nested HO components.

**Replace each with:**
```coq
apply val_rel_at_type_step_up with n; try assumption.
- exact Hty1.
- exact Hty2.  
- exact IHval.
- exact IHstore.
```

**Required lemma:**
```coq
Lemma val_rel_at_type_step_up : forall T n Σ v1 v2,
  val_rel_at_type Σ (store_rel_n n) (val_rel_n n) (store_rel_n n) T v1 v2 ->
  (* value, closed, typing conditions *)
  (* IH for val_rel_n step-up *)
  (* IH for store_rel_n step-up *)
  val_rel_at_type Σ (store_rel_n (S n)) (val_rel_n (S n)) (store_rel_n (S n)) T v1 v2.
Proof.
  induction T; ...
  (* Base types: exact Hrel *)
  (* TFn: downcast with monotonicity, apply Hrel, upcast with IH *)
  (* TProd/TSum: use val_rel_at_type_fo_equiv for FO, IHT1/IHT2 for HO *)
```

---

## Available Lemmas (from Supplement)

### Already Proven:
- `val_rel_n_mono` (NonInterference_v2.v:782)
- `store_rel_n_mono` (NonInterference_v2.v:824)
- `canonical_forms_fn` (Typing.v:526)
- `canonical_forms_prod` (Typing.v:537)
- `canonical_forms_sum` (Typing.v:548)
- `preservation` (Preservation.v:1196)
- `substitution_preserves_typing` (Preservation.v:517)
- `value_has_pure_effect` (Preservation.v:738)

### Key Signatures:
```coq
(* Lambda syntax is ELam, not EFn *)
canonical_forms_fn : ... v = ELam x T1 body

(* Substitution notation *)
substitution_preserves_typing : ... ([z := v] e) ...

(* Step relation *)
ST_AppAbs : (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
```

---

## Proof Structure Summary

```
combined_step_up_all
├── n = 0
│   ├── Part 1 (val_rel): Use fundamental_theorem_n0 [ADMIT 1]
│   └── Part 2 (store_rel): Standard location analysis
│
└── n = S n'  
    ├── Part 1 (val_rel): Use val_rel_at_type_step_up [ADMITS 7-14]
    │   └── Internally uses preservation for store properties [ADMITS 2-6]
    │
    └── Part 2 (store_rel): Use IHstore + IHval for locations
```

---

## Final Verification Checklist

- [ ] `preservation` theorem accessible
- [ ] `val_rel_at_type_fo_equiv` available for FO predicate independence  
- [ ] `typing_nil_implies_closed` or equivalent
- [ ] `store_ty_extends_refl`, `store_ty_extends_trans`
- [ ] `typing_weakening_store` for store type extension
