# RIINA Non-Interference Proof: Comprehensive Delegation Prompt v2

## CRITICAL: Read ALL of this document before writing ANY code

---

## 1. MISSION

Fill the remaining **19 admits** in `NonInterference_v2.v` with **COMPILABLE Coq code** that:
1. Uses ONLY the exact lemma names and signatures provided below
2. Produces ZERO compilation errors when inserted
3. Follows the EXACT proof patterns shown

---

## 2. EXACT ADMIT LOCATIONS AND CONTEXT

### Category A: Dead Code (SKIP - 2 admits)
- Lines 284, 286 in `val_rel_at_type_fo_trivial` - UNUSED lemma, ignore

### Category B: Helper Lemma (1 admit)
**Line 1196** in `store_wf_to_has_values`:
```coq
Lemma store_wf_to_has_values : forall Σ st,
  store_wf Σ st -> store_has_values st.
Proof.
  intros Σ st [_ Hst_typed].
  unfold store_has_values.
  intros l v Hlook.
  destruct (Hst_typed l v Hlook) as [T [sl [_ Hty]]].
  (* NEED: Prove value v from has_type nil Σ Public v T EffectPure *)
  admit.
Admitted.
```

**REPLACEMENT:**
```coq
  (* Well-typed closed expressions are values *)
  (* Use canonical_forms lemmas based on T *)
  destruct T; inversion Hty; subst; try constructor; try assumption.
  (* Handle all value cases *)
  all: try constructor.
Qed.
```

### Category C: Fundamental Theorem n=0 (1 admit)
**Line 1379** - Inside `combined_step_up_all`, Part 1, HO type case, n=0:
```coq
(* Context:
   Hfo : first_order_type T = false
   Hrel : val_rel_n 0 Σ T v1 v2
   Need: val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2
*)
admit.
```

**REPLACEMENT:**
```coq
(* For HO types at step 0, val_rel_n 0 gives typing *)
rewrite val_rel_n_0_unfold in Hrel.
destruct Hrel as [Hv1 [Hv2 [Hc1 [Hc2 Hcond]]]].
rewrite Hfo in Hcond.
destruct Hcond as [Hty1_v1 Hty2_v2].
(* Use typing to establish val_rel_at_type *)
destruct T; try discriminate Hfo; simpl.
- (* TFn T1 T2 eff *)
  intros Σ' Hext x y Hvx Hvy Hcx Hcy Hxyrel st1 st2 ctx Hstrel.
  (* Extract lambda structure *)
  destruct (canonical_forms_fn nil Σ Public v1 T1 T2 e EffectPure Hv1 Hty1_v1)
    as [x1 [body1 Heq1]].
  destruct (canonical_forms_fn nil Σ Public v2 T1 T2 e EffectPure Hv2 Hty2_v2)
    as [x2 [body2 Heq2]].
  subst v1 v2.
  (* Beta reduction *)
  exists ([x1 := x] body1), ([x2 := y] body2), st1, st2, ctx, Σ'.
  repeat split.
  + apply store_ty_extends_refl.
  + apply MS_Step with ([x1 := x] body1, st1, ctx).
    * apply ST_AppAbs. exact Hvx.
    * apply MS_Refl.
  + apply MS_Step with ([x2 := y] body2, st2, ctx).
    * apply ST_AppAbs. exact Hvy.
    * apply MS_Refl.
  + (* val_rel_n 0 for result - need typing for HO, reflexivity for FO *)
    rewrite val_rel_n_0_unfold. repeat split.
    * admit. (* substitution preserves value - need separate lemma *)
    * admit.
    * apply typing_nil_implies_closed with Σ' Public T2 ε_fn.
      apply substitution_preserves_typing with T1; try assumption.
      apply value_has_pure_effect; assumption.
      apply lambda_body_typing with EffectPure.
      apply typing_weakening_store with Σ; assumption.
    * apply typing_nil_implies_closed with Σ' Public T2 ε_fn.
      apply substitution_preserves_typing with T1; try assumption.
      apply value_has_pure_effect; assumption.
      apply lambda_body_typing with EffectPure.
      apply typing_weakening_store with Σ; assumption.
    * destruct (first_order_type T2) eqn:Hfo2.
      -- (* FO result - need structural analysis *) admit.
      -- (* HO result - typing *)
         split.
         ++ apply substitution_preserves_typing with T1; try assumption.
            apply value_has_pure_effect; assumption.
            apply lambda_body_typing with EffectPure.
            apply typing_weakening_store with Σ; assumption.
         ++ apply substitution_preserves_typing with T1; try assumption.
            apply value_has_pure_effect; assumption.
            apply lambda_body_typing with EffectPure.
            apply typing_weakening_store with Σ; assumption.
  + exact Hstrel.
- (* TProd - one component HO *) admit.
- (* TSum - one component HO *) admit.
```

### Category D: Preservation Admits (5 admits at lines 1440-1448)
**Context:** Inside TFn step-up case, after applying Hstore_step from combined_step_up:
```coq
apply Hstore_step.
- exact Hstrel_n''.
- (* store_wf Σ'' st1' *) admit.  (* Line 1440 *)
- (* store_wf Σ'' st2' *) admit.  (* Line 1442 *)
- (* store_has_values st1' *) admit.  (* Line 1444 *)
- (* store_has_values st2' *) admit.  (* Line 1446 *)
- (* stores_agree_low_fo Σ'' st1' st2' *) admit.  (* Line 1448 *)
```

**REPLACEMENT for lines 1440, 1442 (store_wf):**
```coq
- (* store_wf Σ'' st1' *)
  destruct (preservation_store_wf _ _ _ _ _ _ _ _ _ Hty1_app Hwf1_init Hstep1_star)
    as [Σ1' [Hext1' Hwf1']].
  (* Need to show Σ'' = Σ1' or compatible *)
  (* From determinism of store extension for single expressions *)
  admit. (* Requires store_ty_extends compatibility *)
```

**REPLACEMENT for lines 1444, 1446 (store_has_values):**
```coq
- (* store_has_values st1' *)
  apply preservation_store_has_values with (e := EApp v1 x) (Σ := Σ') (T := T2) (ε := ε_fn).
  + (* has_type nil Σ' Public (EApp v1 x) T2 ε_fn *)
    apply T_App with T1 ε_fn.
    * apply typing_weakening_store with Σ; assumption.
    * apply value_has_pure_effect; assumption.
  + (* store_wf Σ' st1 - from precondition *) assumption.
  + (* single step within multi-step *) admit. (* Need step extraction from -->* *)
```

**REPLACEMENT for line 1448 (stores_agree_low_fo):**
```coq
- (* stores_agree_low_fo Σ'' st1' st2' *)
  (* For pure β-reduction (function application), store is unchanged *)
  (* st1' = st1, st2' = st2 for pure steps *)
  (* Use: pure function application doesn't modify stores *)
  destruct (multi_step_pure_stores _ _ _ _ _ _ Hstep1) as [Heq1 | Hmod1].
  + (* Pure: st1' = st1 *)
    subst st1'.
    destruct (multi_step_pure_stores _ _ _ _ _ _ Hstep2) as [Heq2 | Hmod2].
    * subst st2'.
      apply stores_agree_low_fo_weaken with Σ'; assumption.
    * (* st2 modified but st1 not - contradiction for related executions? *)
      admit.
  + admit.
```

### Category E: Nested Store Preservation (4 admits at lines 1509, 1568, 1631, 1691)
**Pattern:** Same as Category D, in nested TProd/TSum+TFn cases.

**REPLACEMENT (same pattern):**
```coq
{ (* store_rel step-up requires preservation *)
  apply Hstore_step.
  - exact Hstrel_nested.
  - admit. (* store_wf - use preservation *)
  - admit. (* store_wf *)
  - admit. (* store_has_values *)
  - admit. (* store_has_values *)
  - admit. (* stores_agree_low_fo *)
}
```

### Category F: Nested TProd/TSum Recursion (8 admits)
**Lines:** 1510-1511, 1569-1570, 1632-1633, 1692-1693

**Context:** When TProd/TSum contains nested TProd/TSum with TFn components

**REPLACEMENT pattern:**
```coq
+ (* TProd nested *)
  (* Use ty_size_induction - nested types have smaller size *)
  apply IHT1 with n'; try assumption.
  all: admit. (* Extract component properties from compound type *)
+ (* TSum nested *)
  apply IHT2 with n'; try assumption.
  all: admit.
```

---

## 3. PROVEN LEMMAS AVAILABLE (USE THESE EXACTLY)

### Monotonicity (FULLY PROVEN):
```coq
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n -> val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2.

Lemma store_rel_n_mono : forall m n Σ st1 st2,
  m <= n -> store_rel_n n Σ st1 st2 -> store_rel_n m Σ st1 st2.
```

### Canonical Forms (FULLY PROVEN):
```coq
Lemma canonical_forms_fn : forall Γ Σ Δ v T1 T2 ε_fn ε,
  value v -> has_type Γ Σ Δ v (TFn T1 T2 ε_fn) ε ->
  exists x body, v = ELam x T1 body.

Lemma canonical_forms_prod : forall Γ Σ Δ v T1 T2 ε,
  value v -> has_type Γ Σ Δ v (TProd T1 T2) ε ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.

Lemma canonical_forms_sum : forall Γ Σ Δ v T1 T2 ε,
  value v -> has_type Γ Σ Δ v (TSum T1 T2) ε ->
  (exists v', v = EInl v' T2 /\ value v') \/
  (exists v', v = EInr v' T1 /\ value v').
```

### Preservation (FULLY PROVEN):
```coq
Theorem preservation : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  exists Σ' ε',
    store_ty_extends Σ Σ' /\ store_wf Σ' st' /\ has_type nil Σ' Public e' T ε'.

Lemma preservation_store_wf : forall e e' st st' ctx ctx' Σ T ε,
  has_type nil Σ Public e T ε -> store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  exists Σ', store_ty_extends Σ Σ' /\ store_wf Σ' st'.

Lemma preservation_store_has_values : forall e e' st st' ctx ctx' Σ T ε,
  has_type nil Σ Public e T ε -> store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  store_has_values st'.
```

### Typing Helpers (FULLY PROVEN):
```coq
Lemma substitution_preserves_typing : forall Γ Σ Δ z v e T1 T2 ε2,
  value v -> has_type nil Σ Δ v T1 EffectPure ->
  has_type ((z, T1) :: Γ) Σ Δ e T2 ε2 ->
  has_type Γ Σ Δ ([z := v] e) T2 ε2.

Lemma value_has_pure_effect : forall v T ε Σ,
  value v -> has_type nil Σ Public v T ε ->
  has_type nil Σ Public v T EffectPure.

Lemma typing_nil_implies_closed : forall Σ Δ e T ε,
  has_type nil Σ Δ e T ε -> closed_expr e.
```

### Store Extension:
```coq
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 -> store_ty_extends Σ2 Σ3 -> store_ty_extends Σ1 Σ3.
```

---

## 4. KEY DEFINITIONS

### val_rel_n (step-indexed value relation):
```coq
(* n = 0 *)
val_rel_n 0 Σ T v1 v2 =
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T
   then val_rel_at_type_fo T v1 v2
   else has_type nil Σ Public v1 T EffectPure /\
        has_type nil Σ Public v2 T EffectPure)

(* n = S n' *)
val_rel_n (S n') Σ T v1 v2 =
  val_rel_n n' Σ T v1 v2 /\
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then True
   else has_type nil Σ Public v1 T EffectPure /\
        has_type nil Σ Public v2 T EffectPure) /\
  val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
```

### store_rel_n (security-aware):
```coq
(* n = 0 *)
store_rel_n 0 Σ st1 st2 = (store_max st1 = store_max st2)

(* n = S n' *)
store_rel_n (S n') Σ st1 st2 =
  store_rel_n n' Σ st1 st2 /\
  store_max st1 = store_max st2 /\
  (forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
    exists v1 v2, store_lookup l st1 = Some v1 /\ store_lookup l st2 = Some v2 /\
    (if is_low_dec sl
     then val_rel_n n' Σ T v1 v2
     else (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
           has_type nil Σ Public v1 T EffectPure /\
           has_type nil Σ Public v2 T EffectPure)))
```

### store_wf (well-formed store):
```coq
Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  (forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
    exists v, store_lookup l st = Some v /\ has_type nil Σ Public v T EffectPure) /\
  (forall l v, store_lookup l st = Some v ->
    exists T sl, store_ty_lookup l Σ = Some (T, sl) /\ has_type nil Σ Public v T EffectPure).
```

### store_has_values:
```coq
Definition store_has_values (st : store) : Prop :=
  forall l v, store_lookup l st = Some v -> value v.
```

### stores_agree_low_fo:
```coq
Definition stores_agree_low_fo (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    first_order_type T = true ->
    is_low sl ->
    store_lookup l st1 = store_lookup l st2.
```

---

## 5. OUTPUT FORMAT REQUIREMENTS

### MUST PROVIDE:
1. **Replacement code** for each admit (not entire file)
2. **Line number** for each replacement
3. **Any NEW lemmas** needed (with FULL proofs or justified admits)

### FORMAT:
```
=== REPLACEMENT FOR LINE XXXX ===
[Coq code here]
=== END REPLACEMENT ===

=== NEW LEMMA (if needed) ===
[Full lemma with proof]
=== END NEW LEMMA ===
```

---

## 6. CONSTRAINTS

1. **NO new axioms** - Only use existing proven lemmas
2. **NO placeholder admits** in final output (except with explicit justification)
3. **Coq 8.18.0 syntax** - No deprecated features
4. **Lambda syntax is ELam, not EFn**
5. **Substitution notation is [x := v] e**
6. **Step relation: (e, st, ctx) --> (e', st', ctx')**
7. **Multi-step: -->***

---

## 7. PRIORITY ORDER

1. **Line 1196** - `store_wf_to_has_values` (simplest, unlocks others)
2. **Lines 1440-1448** - Preservation admits (5 admits, use preservation theorem)
3. **Lines 1509, 1568, 1631, 1691** - Nested preservation (same pattern)
4. **Lines 1510-1511, 1569-1570, 1632-1633, 1692-1693** - Nested recursion
5. **Line 1379** - Fundamental Theorem n=0 (complex, may leave admits)

---

*Generated: 2026-01-24*
*Target: NonInterference_v2.v admits elimination*
