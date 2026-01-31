# AXIOM ELIMINATION: Step-Indexed Logical Relation for RIINA (Coq/Rocq 9.1)

## MISSION

Eliminate axioms from a step-indexed logical relation proof of noninterference in Coq (Rocq 9.1). The codebase is at **https://github.com/ib823/proof** — the two files you must work with are:

- `02_FORMAL/coq/properties/NonInterference_v2.v` (2644 lines) — contains definitions + 1 axiom
- `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v` (4468 lines) — contains 4 axioms

**Fetch both files from the GitHub repo to see the full code.** Below I provide the critical definitions and axioms, but you MUST read the full files to produce correct, compilable code.

Build command: `cd 02_FORMAL/coq && make clean && make -j4`

---

## CURRENT STATE (PASSING BUILD)

- 5 axioms, 0 `admit.`, 0 `Admitted.`
- `make` passes clean
- `non_interference_stmt` is the top-level theorem

## THE 5 AXIOMS

### Axiom 1: `fundamental_theorem_step_0` (NonInterference_v2.v, line 992)

```coq
Axiom fundamental_theorem_step_0 : forall T Σ v1 v2,
  first_order_type T = false ->
  val_rel_n 0 Σ T v1 v2 ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2.
```

**Why it exists:** At step 0, `val_rel_n 0` for HO types gives `True` for the structural part. But `val_rel_at_type` for `TFn` requires a Kripke-like property (for any related inputs/stores, application produces related outputs). This property can't be derived from `True`.

**Key insight for elimination:** `val_rel_at_type` for `TFn T1 T2 eff` at step 0 requires producing `val_rel_n 0` and `store_rel_n 0` in the conclusion. But `exp_rel_n 0 = True`. So the existential witnesses in the TFn case might be satisfiable vacuously IF the store_rel_pred/val_rel_lower/store_rel_lower parameters (which are `store_rel_n 0`/`val_rel_n 0`/`store_rel_n 0`) make the preconditions unsatisfiable or the conclusions trivial.

**Check this:** Look at `val_rel_at_type` for `TFn` — it universally quantifies over stores satisfying `store_rel_pred Σ' st1 st2` (which is `store_rel_n 0 Σ' st1 st2 = store_max st1 = store_max st2`). The conclusion requires existential witnesses satisfying `val_rel_lower Σ'' T2 v1' v2'` (which is `val_rel_n 0 Σ'' T2 v1' v2'` — requires value, closed, typing, and FO structure). This is NON-TRIVIAL even at step 0 because it requires actual witnesses with typing proofs. So the axiom may not be vacuously true.

---

### Axiom 2: `logical_relation_ref` (NI_v2_LogicalRelation.v, line 779)

```coq
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e T ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).
```

### Axiom 3: `logical_relation_deref` (NI_v2_LogicalRelation.v, line 795)

```coq
Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e (TRef T l) ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).
```

### Axiom 4: `logical_relation_assign` (NI_v2_LogicalRelation.v, line 811)

```coq
Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e1 (TRef T l) ε1 ->
  has_type Γ Σ Δ e2 T ε2 ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base TUnit (subst_rho rho1 (EAssign e1 e2)) (subst_rho rho2 (EAssign e1 e2)).
```

### Axiom 5: `logical_relation_declassify` (NI_v2_LogicalRelation.v, line 828)

```coq
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e (TSecret T) ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base T (subst_rho rho1 (EDeclassify e p)) (subst_rho rho2 (EDeclassify e p)).
```

**Declassify is a POLICY AXIOM** — it intentionally breaks noninterference. Keep it unless you have a genuinely sound proof.

---

## KEY DEFINITIONS

### val_rel_n / store_rel_n (mutual fixpoint, NI_v2.v lines 400-439)

```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 =>
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      has_type nil Σ Public v1 T EffectPure /\
      has_type nil Σ Public v2 T EffectPure /\
      (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      has_type nil Σ Public v1 T EffectPure /\
      has_type nil Σ Public v2 T EffectPure /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end
with store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => store_max st1 = store_max st2
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\ store_lookup l st2 = Some v2 /\
          (if is_low_dec sl
           then val_rel_n n' Σ T v1 v2
           else (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
                 has_type nil Σ Public v1 T EffectPure /\
                 has_type nil Σ Public v2 T EffectPure)))
  end.
```

**Critical:** `store_rel_n` splits on `is_low_dec sl`:
- **LOW:** full `val_rel_n` (structural + typing)
- **HIGH:** typing only (observer can't see)

### exp_rel_n (NI_v2.v lines 2366-2387)

```coq
Fixpoint exp_rel_n (n : nat) (Σ : store_ty) (T : ty) (e1 e2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      forall Σ_cur st1 st2 ctx,
        store_ty_extends Σ Σ_cur ->
        store_rel_n n' Σ_cur st1 st2 ->
        store_wf Σ_cur st1 -> store_wf Σ_cur st2 ->
        stores_agree_low_fo Σ_cur st1 st2 ->
        exists v1 v2 st1' st2' ctx' Σ',
          store_ty_extends Σ_cur Σ' /\
          (e1, st1, ctx) -->* (v1, st1', ctx') /\
          (e2, st2, ctx) -->* (v2, st2', ctx') /\
          value v1 /\ value v2 /\
          val_rel_n n' Σ' T v1 v2 /\
          store_rel_n n' Σ' st1' st2' /\
          store_wf Σ' st1' /\ store_wf Σ' st2' /\
          stores_agree_low_fo Σ' st1' st2'
  end.
```

### val_rel_at_type for TFn (NI_v2.v lines 327-376, inside Section)

```coq
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
```

When called from `val_rel_n (S n')`:
- `store_rel_pred` = `store_rel_n n'`
- `val_rel_lower` = `val_rel_n n'`
- `store_rel_lower` = `store_rel_n n'`

When called from `fundamental_theorem_step_0` (step 0):
- `store_rel_pred` = `store_rel_n 0` = `store_max st1 = store_max st2`
- `val_rel_lower` = `val_rel_n 0` = value + closed + typing + FO structure
- `store_rel_lower` = `store_rel_n 0` = `store_max st1 = store_max st2`

### val_rel_at_type_fo (NI_v2.v lines 112-141)

Returns `True` for: TSecret, TLabeled, TTainted, TSanitized, TList, TOption, TProof, TCapability, TCapabilityFull, TConstantTime, TZeroizing.

Returns structural equality for: TUnit, TBool, TInt, TString, TBytes, TRef (same location), TProd (recursive), TSum (matching constructor + recursive).

### stores_agree_low_fo (NI_v2.v line 314)

```coq
Definition stores_agree_low_fo (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
    first_order_type T = true -> is_low sl ->
    store_lookup l st1 = store_lookup l st2.
```

### first_order_type (NI_v2.v lines 79-99)

Returns `true` for base types, TProd/TSum (recursive), TList/TOption/TRef/TSecret/TLabeled/TTainted/TSanitized/TProof/TCapability/TCapabilityFull/TConstantTime/TZeroizing (recursive).
Returns `false` for TFn, TChan, TSecureChan.

---

## HOW AXIOMS ARE USED (NI_v2_LogicalRelation.v lines 4225-4289)

The `logical_relation` theorem is by induction on `has_type G Σ Public e T eps`. Each axiom handles one case. The induction hypothesis `IHHty` gives `exp_rel` for subexpressions.

```coq
  - (* T_Ref *)
    simpl. unfold exp_rel. intro n.
    eapply logical_relation_ref.
    + eassumption.  + exact Henv.  + exact Hno1.  + exact Hno2.
  - (* T_Deref *)
    simpl. unfold exp_rel. intro n.
    eapply logical_relation_deref.
    + eassumption.  + exact Henv.  + exact Hno1.  + exact Hno2.
  - (* T_Assign *)
    simpl. unfold exp_rel. intro n.
    eapply logical_relation_assign.
    + eassumption.  + eassumption.  + exact Henv.  + exact Hno1.  + exact Hno2.
  - (* T_Declassify *)
    simpl. unfold exp_rel. intro n.
    eapply logical_relation_declassify.
    + eassumption.  + exact Henv.  + exact Hno1.  + exact Hno2.
```

**You may add premises** to the replacement lemmas (like `exp_rel` for subexpressions from IHHty). Update the usage sites accordingly.

---

## KNOWN BLOCKERS FROM PREVIOUS ATTEMPTS

### 1. `val_rel_at_type_fo` does NOT imply syntactic equality for wrapper types

For `TList T'`, `TConstantTime T'`, `TZeroizing T'`, etc.:
- `first_order_type` returns `true` (recursive on inner type)
- `val_rel_at_type_fo` returns `True`

So `val_rel_at_type_fo T v1 v2` does NOT imply `v1 = v2` for these types. This means:
- `stores_agree_low_fo` requires `store_lookup l st1 = store_lookup l st2` for LOW+FO locations
- But `val_rel_n` only gives `val_rel_at_type_fo` which is `True` for wrapper FO types
- So you CANNOT derive syntactic equality from the logical relation for these types

### 2. Removing `is_low_dec` from `store_rel_n` breaks everything

Tried: track `val_rel_n` for ALL locations (not just LOW). This changes the mutual fixpoint definition, cascading through ~4000 lines of existing proofs. The unfolding lemmas change, monotonicity lemmas break, and every `destruct` pattern on `store_rel_n` needs updating.

### 3. The deref HIGH case

For HIGH locations, `store_rel_n` only gives typing (not `val_rel_n`). The deref case needs `val_rel_n` for the result. For HO types this is fine (`True` at step 0), but for FO types at HIGH security, you need `val_rel_at_type_fo` which requires structural content not available from typing alone.

### 4. The assign stores_agree_low_fo case

After assignment to a LOW+FO location, `stores_agree_low_fo` requires the new values to be syntactically equal. But the logical relation only guarantees `val_rel_n` (semantic relatedness), and for wrapper FO types, `val_rel_at_type_fo` is `True` — not syntactic equality.

---

## POSSIBLE STRATEGIES (NOT YET TRIED)

### A. Weaken `stores_agree_low_fo`

Change the definition to only require agreement on "truly structural" FO types (those where `val_rel_at_type_fo` gives structural equality, not `True`). This means excluding TList, TOption, TSecret, TLabeled, TTainted, TSanitized, TProof, TCapability, TCapabilityFull, TConstantTime, TZeroizing from the agreement requirement.

You could define `truly_structural_fo T` that returns `true` only for TUnit, TBool, TInt, TString, TBytes, TRef, and recursively for TProd/TSum where components are truly structural.

**Risk:** Need to verify that `stores_agree_low_fo` is only needed for truly structural FO types throughout the entire proof development.

### B. Strengthen `val_rel_at_type_fo` for wrapper types

Make `val_rel_at_type_fo (TList T')` = `val_rel_at_type_fo T'` (not `True`). Similarly for other wrapper types.

**Risk:** This changes the meaning of the FO relation and may break the `val_rel_at_type_fo_equiv` lemma (which proves FO relation is predicate-independent). Need to verify TProd/TSum structural recursion still works.

### C. Add `exp_rel` premises and prove ref/deref/assign with the LOW-only case

The LOW case is provable because `store_rel_n` gives `val_rel_n` for LOW locations. The HIGH case might be handled by:
- For deref: the result type is `T`, and if `T` is HO, `val_rel_n` at `True` is easy. If `T` is FO, need structural content from typing alone (possible via canonical forms + `val_rel_at_type_fo_refl` for the same value... but v1 ≠ v2 for HIGH).

### D. Split the deref/assign proofs by security level

For `logical_relation_deref`:
- If `l` is LOW: `store_rel_n` gives `val_rel_n` directly
- If `l` is HIGH: the typing derivation is `has_type Γ Σ pc e (TRef T l)` where `pc = Public`. Since `pc = Public` and `l` is HIGH, the program can't actually observe the reference content. The noninterference guarantee for HIGH deref is that BOTH runs produce SOME well-typed value, but they don't need to agree. Construct `val_rel_n` from typing alone for HO types (trivial), and for FO types show both sides produce the same value (this is the hard part — may need `stores_agree_low_fo` to not apply for HIGH+FO).

---

## CONSTRAINTS

1. **NO `admit.`** — every tactic proof must be complete
2. **NO `Admitted.`** — every lemma must end with `Qed.`
3. **New axioms are acceptable** only if strictly simpler/more justified than replaced ones
4. **You may modify definitions** but must fix ALL downstream proofs
5. **Build must pass:** `make clean && make -j4` in `02_FORMAL/coq/`
6. **Rocq 9.1 compatibility:** `inversion; subst` may rename variables differently
7. **`change (NonInterference_v2.X) with (X)` tactic** is used throughout the LR file — the imports of `CumulativeRelation` and `TypeMeasure` cause name shadowing that makes these `change` tactics necessary. If you remove those imports, every `change` line must be replaced with `unfold`/`fold`.
8. **Do NOT introduce helper lemmas that reference undefined functions.** Every function/lemma you use must either already exist in the codebase or be defined by you.

---

## DELIVERABLES

For each axiom you can eliminate:
1. The replacement `Lemma` statement (may have new premises)
2. The complete, compilable proof
3. Updated usage site in `logical_relation`
4. Any helper lemmas needed (with complete proofs)
5. Any definition changes and the cascade of fixes

For axioms you CANNOT eliminate:
1. Precise explanation of why
2. Whether a weaker/simpler axiom could replace it

**The goal is to reduce from 5 axioms to as few as possible, with a passing `make` build.**

---

## FILE STRUCTURE

```
02_FORMAL/coq/
├── _CoqProject          # -Q . RIINA
├── Makefile             # Generated by rocq makefile
├── foundations/
│   ├── Syntax.v         # Types, expressions, security_level
│   ├── Semantics.v      # Small-step semantics, store operations
│   └── Typing.v         # has_type, store_wf, store_ty_extends
├── type_system/
│   └── Preservation.v   # Type preservation, canonical forms
├── properties/
│   ├── NonInterference_v2.v              # Definitions + axiom 1
│   ├── NonInterference_v2_Monotone.v     # Monotonicity lemmas
│   ├── NonInterference_v2_LogicalRelation.v  # Main proof + axioms 2-5
│   ├── CumulativeRelation.v              # Imported by LR file
│   └── TypeMeasure.v                     # Imported by LR file
└── ...
```

Fetch the full files from `https://github.com/ib823/proof` to begin.
