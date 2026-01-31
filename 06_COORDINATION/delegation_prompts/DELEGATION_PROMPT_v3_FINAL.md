# DELEGATION PROMPT: Eliminate 3 Axioms from RIINA Noninterference Proof

## YOUR TASK

Produce **two complete, compilable Coq files** that I can drop into my codebase to eliminate 3 of 5 axioms. The files must compile with `make clean && make -j4` with ZERO errors.

**Repository:** https://github.com/ib823/proof (branch: `main`)
**Coq version:** Rocq 9.1 (Coq 8.21)
**Build:** `cd 02_FORMAL/coq && make clean && make -j4`

---

## THE 3 AXIOMS TO ELIMINATE

All in `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v`:

```coq
(* Line 779 *)
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e T ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).

(* Line 795 *)
Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e (TRef T l) ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).

(* Line 811 *)
Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e1 (TRef T l) ε1 ->
  has_type Γ Σ Δ e2 T ε2 ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base TUnit (subst_rho rho1 (EAssign e1 e2)) (subst_rho rho2 (EAssign e1 e2)).
```

**Keep unchanged:** `logical_relation_declassify` (line 828) and `fundamental_theorem_step_0` (in NonInterference_v2.v line 992).

---

## THE APPROACH: Remove `is_low_dec` from `store_rel_n`

### Why the axioms exist

`store_rel_n` currently splits on security level:
- LOW locations: `val_rel_n n' Σ T v1 v2` (full value relation)
- HIGH locations: just `value`, `closed_expr`, `has_type` (no value relation)

This means when you deref a HIGH location, you get typing but NOT `val_rel_n`. The axioms bridge this gap.

### The fix

Remove the `is_low_dec` conditional. Track `val_rel_n` for ALL locations (both LOW and HIGH). Then:
- `deref` always gets `val_rel_n` from `store_rel_n` → axiom eliminated
- `ref` stores `val_rel_n` values (from IH) → axiom eliminated
- `assign` updates with `val_rel_n` values (from IH) → axiom eliminated

### Why this is safe

In `non_interference_stmt`, execution starts with EMPTY stores. Every `ref` stores values from `exp_rel_n` (which provides `val_rel_n`). Every `assign` stores values from `exp_rel_n`. So the strengthened invariant is always satisfiable.

---

## CRITICAL BLOCKERS (PREVIOUS ATTEMPTS FAILED ON THESE)

### Blocker 1: `stores_agree_low_fo`

```coq
(* Line 314, NonInterference_v2.v *)
Definition stores_agree_low_fo (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    first_order_type T = true ->
    is_low sl ->
    store_lookup l st1 = store_lookup l st2.
```

This requires **syntactic equality** (`store_lookup l st1 = store_lookup l st2`) for LOW+FO locations. But `val_rel_n` does NOT guarantee syntactic equality for all FO types. Specifically, `val_rel_at_type_fo` returns `True` for:
- `TList T'`, `TOption T'`, `TSecret T'`, `TLabeled T' _`, `TTainted T' _`, `TSanitized T' _`, `TConstantTime T'`, `TZeroizing T'`, `TCapability _`, `TCapabilityFull _`, `TProof _`

So `val_rel_n n Σ (TList TInt) v1 v2` does NOT imply `v1 = v2`.

**SOLUTION:** `stores_agree_low_fo` is carried as a SEPARATE invariant in `exp_rel_n` (see below). It is maintained independently of `store_rel_n`. When extending/updating stores in the ref/deref/assign proofs, you need to prove `stores_agree_low_fo` is preserved. For `ref`: the new location has the same value in both stores IF it's LOW+FO (this follows from `val_rel_n` for the specific types that `stores_agree_low_fo` cares about — base types like TUnit, TBool, TInt, TString, TBytes, TProd, TSum, TRef — where `val_rel_at_type_fo` DOES give structural equality). For `assign`: similar reasoning. The wrapper types (TList etc.) are NOT a problem because `stores_agree_low_fo` only applies to LOW locations, and the non-interference theorem only needs it for the final output (which has a specific type, not an arbitrary wrapper type).

**ACTUALLY, the simplest solution:** You do NOT need to prove `v1 = v2` for ALL FO types. You need `store_lookup l st1 = store_lookup l st2`, which is `Some v1 = Some v2`, i.e., `v1 = v2`. For the ref case, the values ARE the same expressions from the IH. Wait — no, they are RELATED but not necessarily equal.

**THE REAL SOLUTION FOR `stores_agree_low_fo`:**

Look at how `exp_rel_n` is defined:

```coq
(* The output of exp_rel_n at S n' includes: *)
exists v1 v2 st1' st2' ctx' Σ',
  store_ty_extends Σ_cur Σ' /\
  (e1, st1, ctx) -->* (v1, st1', ctx') /\
  (e2, st2, ctx) -->* (v2, st2', ctx') /\
  value v1 /\ value v2 /\
  val_rel_n n' Σ' T v1 v2 /\
  store_rel_n n' Σ' st1' st2' /\
  store_wf Σ' st1' /\
  store_wf Σ' st2' /\
  stores_agree_low_fo Σ' st1' st2'   (* ← THIS IS A SEPARATE OUTPUT *)
```

So `stores_agree_low_fo` is maintained as a separate conjunct. When proving the ref/deref/assign cases, you receive `stores_agree_low_fo Σ' st1' st2'` from the IH evaluation, and must produce `stores_agree_low_fo Σ_new st1_new st2_new`.

For **deref**: stores don't change, so `stores_agree_low_fo` is inherited.
For **ref**: `st1_new = store_update (fresh_loc st1') v1 st1'` and similarly for st2. Fresh location is the same (from `store_rel_n` domain equality). For the new location: if it's LOW+FO, then `val_rel_n` for the stored type at step 0 gives `val_rel_at_type_fo T v1 v2`, which for base types gives `v1 = v2`. For existing locations: inherited from `stores_agree_low_fo Σ' st1' st2'`.
For **assign**: Updated location: if LOW+FO, same reasoning. Other locations: unchanged.

**BUT WAIT**: For wrapper FO types like `TList TInt` (where `first_order_type` is `true` but `val_rel_at_type_fo` returns `True`), `v1 = v2` does NOT follow.

**THE ACTUAL FIX**: We need `val_rel_at_type_fo` to guarantee equality for ALL types where `first_order_type = true`. Currently it doesn't (it returns `True` for TList, etc.). Two options:

**Option A**: Change `val_rel_at_type_fo` to give structural equality for TList etc. This cascades.
**Option B**: Change `stores_agree_low_fo` to only require equality for STRICT base types (TUnit, TBool, TInt, TString, TBytes, TProd of strict, TSum of strict). Then verify all downstream uses are ok.
**Option C (BEST)**: Leave `stores_agree_low_fo` alone. In the ref/assign proofs for the `stores_agree_low_fo` obligation, you don't need `val_rel_n → v1 = v2` in general. You need it for the SPECIFIC location being added/updated. If that location is LOW+FO with a wrapper type like TList, then `val_rel_at_type_fo (TList T') v1 v2 = True`, but you ALSO have `store_lookup l st1 = store_lookup l st2` from the input `stores_agree_low_fo`. Wait — for ref, the location is NEW (fresh), so there's no prior agreement. For assign, the location EXISTS and may have had agreement.

**DEFINITIVE SOLUTION**: The issue only arises for `ref` (creating new LOW+FO locations with wrapper types where val_rel_at_type_fo = True). But in practice, `ERef e sl` creates a location with security label `sl`. If `sl` is HIGH, then `is_low sl = false` and `stores_agree_low_fo` doesn't apply. If `sl` is LOW, then we need `v1 = v2`.

For LOW refs at PUBLIC pc (which is what we have — the typing rule requires Public pc for this theorem), the IH gives `val_rel_n` for the stored value. For LOW+FO wrapper types, `val_rel_n` gives `True`, which doesn't help.

**HOWEVER**: Check if this situation can actually occur. Can you have `ERef e Low` where `e : TList TInt`? Yes, you can. And `val_rel_n n Σ (TList TInt) v1 v2` at step 0 gives `val_rel_at_type_fo (TList TInt) v1 v2 = True`. So `v1` and `v2` could differ, violating `stores_agree_low_fo`.

**THIS IS A GENUINE PROBLEM.** The wrapper FO types have a trivial relation, so `stores_agree_low_fo` can be violated.

**THE REAL FIX (DO THIS):** Change `stores_agree_low_fo` to use `val_rel_at_type_fo` instead of syntactic equality:

```coq
Definition stores_agree_low_fo (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    first_order_type T = true ->
    is_low sl ->
    forall v1 v2,
      store_lookup l st1 = Some v1 ->
      store_lookup l st2 = Some v2 ->
      val_rel_at_type_fo T v1 v2.
```

**OR EVEN SIMPLER:** Just remove `stores_agree_low_fo` entirely and derive it from `store_rel_n` (since after the fix, `store_rel_n` gives `val_rel_n` for ALL locations, which subsumes LOW+FO agreement for base types). Then change `exp_rel_n` to drop the `stores_agree_low_fo` conjunct (since it's derivable from `store_rel_n`).

**NO — THAT IS TOO INVASIVE.** `stores_agree_low_fo` is used in `val_rel_at_type` for function types (the function body must preserve low-FO agreement). Removing it changes the logical relation fundamentally.

### Blocker 2: `val_rel_n_store_ty_mono` (store typing monotonicity)

When extending the store typing, existing `val_rel_n` values need to remain valid under the extended typing. This was previously an axiom (`val_rel_store_weaken_back`) that was eliminated. You'll need it as a lemma. It's provable because `val_rel_n` at step 0 only uses typing (which is monotonic in store typing via weakening), and at step S n' the behavioral part uses `exp_rel_n` which quantifies over all extensions anyway.

---

## WHAT I NEED YOU TO DELIVER

### Deliverable 1: Complete replacement `NonInterference_v2.v`

Clone the repo, read the file at `02_FORMAL/coq/properties/NonInterference_v2.v` (2644 lines). Make EXACTLY these changes:

**Change 1 (line 420-439):** Remove `is_low_dec` from `store_rel_n`:
```
BEFORE:
          (if is_low_dec sl
           then val_rel_n n' Σ T v1 v2
           else (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
                 has_type nil Σ Public v1 T EffectPure /\
                 has_type nil Σ Public v2 T EffectPure)))

AFTER:
          val_rel_n n' Σ T v1 v2)
```

**Change 2 (line 466-480):** Update `store_rel_n_S_unfold` to match (same removal of is_low_dec).

**Change 3 (line 858-884):** Fix `store_rel_n_mono` proof — remove `destruct (is_low_dec sl)` case split, always use `val_rel_n_mono`.

**Change 4 (line 1644-1688):** Fix `store_rel_n_step_up_from_IH` proof — remove `destruct (is_low_dec sl)` case split, always use `IH_val`.

**Change 5:** Fix ALL other proofs that break. Search for `is_low_dec` — there are uses at approximately lines 879, 1676, and 2203. Each one needs the HIGH branch removed.

**Change 6:** If `stores_agree_low_fo` causes problems (see Blocker 1), you may need to adjust its definition or the proofs that establish it.

### Deliverable 2: Complete replacement `NonInterference_v2_LogicalRelation.v`

Read the file at `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v` (4468 lines). Make EXACTLY these changes:

**Change 1:** Delete axioms `logical_relation_ref`, `logical_relation_deref`, `logical_relation_assign` (lines 779-818). Replace with proven lemmas. The new lemmas should take `exp_rel_n` as an additional premise (the IH).

**Change 2:** Update the T_Ref/T_Deref/T_Assign cases in the `logical_relation` theorem (lines 4225-4252) to call the proven lemmas and pass the IH.

---

## EXACT DEFINITIONS YOU NEED (from the codebase)

### Store types (list-based)
```coq
(* store = list (loc * expr) *)
(* store_ty = list (loc * ty * security_level) *)

Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.

Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

Definition fresh_loc (st : store) : loc := S (store_max st).
```

### Step rules for ref/deref/assign
```coq
| ST_RefValue : forall v sl st ctx l,
    value v ->
    l = fresh_loc st ->
    (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)

| ST_DerefLoc : forall v l st ctx,
    store_lookup l st = Some v ->
    (EDeref (ELoc l), st, ctx) --> (v, st, ctx)

| ST_AssignLoc : forall v1 l st ctx,
    store_lookup l st = Some v1 ->
    forall v2, value v2 ->
    (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)
```

**IMPORTANT:** There is NO `store_extend` function. Ref uses `store_update l v st` where `l = fresh_loc st` (which inserts because fresh_loc is not in the store).

### Store typing
```coq
Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * security_level) :=
  match Σ with
  | nil => None
  | (l', T, sl) :: Σ' =>
      if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l Σ'
  end.

Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).
```

### store_wf
```coq
Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  (forall l T sl,
     store_ty_lookup l Σ = Some (T, sl) ->
     exists v, store_lookup l st = Some v /\ value v /\ has_type nil Σ Public v T EffectPure) /\
  (forall l v,
     store_lookup l st = Some v ->
     exists T sl, store_ty_lookup l Σ = Some (T, sl) /\ value v /\ has_type nil Σ Public v T EffectPure).
```

### exp_rel_n (the output format)
```coq
Fixpoint exp_rel_n (n : nat) (Σ : store_ty) (T : ty) (e1 e2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      forall Σ_cur st1 st2 ctx,
        store_ty_extends Σ Σ_cur ->
        store_rel_n n' Σ_cur st1 st2 ->
        store_wf Σ_cur st1 ->
        store_wf Σ_cur st2 ->
        stores_agree_low_fo Σ_cur st1 st2 ->
        exists v1 v2 st1' st2' ctx' Σ',
          store_ty_extends Σ_cur Σ' /\
          (e1, st1, ctx) -->* (v1, st1', ctx') /\
          (e2, st2, ctx) -->* (v2, st2', ctx') /\
          value v1 /\ value v2 /\
          val_rel_n n' Σ' T v1 v2 /\
          store_rel_n n' Σ' st1' st2' /\
          store_wf Σ' st1' /\
          store_wf Σ' st2' /\
          stores_agree_low_fo Σ' st1' st2'
  end.
```

### val_rel_n structure
```coq
(* At step 0: *)
val_rel_n 0 Σ T v1 v2 =
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  has_type nil Σ Public v1 T EffectPure /\
  has_type nil Σ Public v2 T EffectPure /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)

(* At step S n': *)
val_rel_n (S n') Σ T v1 v2 =
  val_rel_n n' Σ T v1 v2 /\
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  has_type nil Σ Public v1 T EffectPure /\
  has_type nil Σ Public v2 T EffectPure /\
  (if first_order_type T
   then val_rel_at_type_fo T v1 v2
   else val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2)

(* For TRef: val_rel_at_type_fo (TRef T' _) v1 v2 = exists l, v1 = ELoc l /\ v2 = ELoc l *)
(* For TRef at S n': val_rel_at_type ... (TRef T' _) v1 v2 = exists l, v1 = ELoc l /\ v2 = ELoc l *)
```

### Existing lemmas you can use
```coq
Lemma val_rel_n_mono : forall m n Σ T v1 v2, m <= n -> val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2.
Lemma val_rel_n_typing : forall n Σ T v1 v2, val_rel_n n Σ T v1 v2 -> has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure.
Lemma val_rel_n_value : forall n Σ T v1 v2, val_rel_n n Σ T v1 v2 -> value v1 /\ value v2.
Lemma val_rel_n_closed : forall n Σ T v1 v2, val_rel_n n Σ T v1 v2 -> closed_expr v1 /\ closed_expr v2.
Lemma val_rel_n_0_unfold / val_rel_n_S_unfold / store_rel_n_0_unfold / store_rel_n_S_unfold  (* reflexivity lemmas *)
Lemma val_rel_n_unit : forall n Σ, val_rel_n n Σ TUnit EUnit EUnit.
Lemma val_rel_n_prod_structure : forall n Σ T1 T2 v1 v2, ... (* extracts EPair components *)
Lemma val_rel_n_bool_structure : forall n Σ v1 v2, ... (* same bool *)
Lemma val_rel_n_sum_structure : forall n Σ T1 T2 v1 v2, ... (* same injection *)

(* Multi-step congruences (in the LR file itself, lines 1659-1710) *)
Lemma multi_step_ref : forall e e' sl st st' ctx ctx', (e, st, ctx) -->* (e', st', ctx') -> (ERef e sl, st, ctx) -->* (ERef e' sl, st', ctx').
Lemma multi_step_deref : forall e e' st st' ctx ctx', (e, st, ctx) -->* (e', st', ctx') -> (EDeref e, st, ctx) -->* (EDeref e', st', ctx').
Lemma multi_step_assign1 : forall e1 e1' e2 st st' ctx ctx', (e1, st, ctx) -->* (e1', st', ctx') -> (EAssign e1 e2, st, ctx) -->* (EAssign e1' e2, st', ctx').
Lemma multi_step_assign2 : forall v1 e2 e2' st st' ctx ctx', value v1 -> (e2, st, ctx) -->* (e2', st', ctx') -> (EAssign v1 e2, st, ctx) -->* (EAssign v1 e2', st', ctx').

(* Existing store lemmas (in Semantics.v) *)
Lemma store_update_lookup_eq : forall st l v, store_lookup l (store_update l v st) = Some v.
Lemma store_update_lookup_neq : forall st l l' v, l <> l' -> store_lookup l' (store_update l v st) = store_lookup l' st.
Lemma fresh_loc_not_in_store : forall st, store_lookup (fresh_loc st) st = None.
Lemma store_update_preserves_values : forall st l v, store_has_values st -> value v -> store_has_values (store_update l v st).
```

### Axiom usage sites (lines 4225-4252 in LR file)

```coq
  - (* T_Ref *)
    simpl. unfold exp_rel. intro n.
    eapply logical_relation_ref.
    + eassumption.
    + exact Henv.
    + exact Hno1.
    + exact Hno2.
  - (* T_Deref *)
    simpl. unfold exp_rel. intro n.
    eapply logical_relation_deref.
    + eassumption.
    + exact Henv.
    + exact Hno1.
    + exact Hno2.
  - (* T_Assign *)
    simpl. unfold exp_rel. intro n.
    eapply logical_relation_assign.
    + eassumption.
    + eassumption.
    + exact Henv.
    + exact Hno1.
    + exact Hno2.
```

Note: the axioms currently take `store_ty_extends Σ Σ_base` but the `eapply` unifies it. The `Hext_base` hypothesis IS available in scope (from the theorem's `forall Σ_base, store_ty_extends Σ Σ_base ->`).

---

## CONSTRAINTS

1. **NO `Admitted.`** — Every proof must end with `Qed.`
2. **NO `admit.`** — No tactical admits
3. **NO new `Axiom` declarations** — Only eliminate, never add
4. **NO undefined helpers** — Every lemma you use must either exist in the codebase already OR be proven in the file you deliver
5. **The build must pass** — `make clean && make -j4` in `02_FORMAL/coq/`
6. **Minimal changes** — Don't refactor code that doesn't need changing. Don't rename variables. Don't reformat. Surgical precision.
7. **Keep axioms 4 and 5** — `logical_relation_declassify` and `fundamental_theorem_step_0` stay as-is

---

## STRATEGY GUIDANCE

The approach that works:

1. Change `store_rel_n` (remove `is_low_dec`) — 1 line change in definition
2. Update `store_rel_n_S_unfold` — 1 line change
3. Fix `store_rel_n_mono` — remove case split, always `val_rel_n_mono`
4. Fix `store_rel_n_step_up_from_IH` — remove case split, always `IH_val`
5. Fix `combined_step_up_all` (~line 2203) — remove case split
6. For the 3 axiom replacements: make them Lemmas with an extra `exp_rel_n` premise (the IH). The IH is available at the usage sites from the `logical_relation` theorem's induction.
7. For `stores_agree_low_fo` preservation in ref/assign: The key insight is that `store_update` on a fresh location preserves `stores_agree_low_fo` because: (a) for existing locations, the lookups are unchanged, (b) for the new location, you need `store_lookup (fresh_loc st1') (store_update (fresh_loc st1') v1 st1') = store_lookup (fresh_loc st2') (store_update (fresh_loc st2') v2 st2')` which is `Some v1 = Some v2`, requiring `v1 = v2`. For base FO types (TUnit, TBool, TInt, TString, TBytes), `val_rel_at_type_fo` gives `v1 = v2`. For TProd/TSum, it gives structural equality recursively. For wrapper types where `val_rel_at_type_fo = True` (TList, TOption, etc.): these CAN'T actually be stored at LOW+FO because `val_rel_at_type_fo` returns True, not equality, BUT `stores_agree_low_fo` requires equality. **If this is truly a problem, you may need to weaken `stores_agree_low_fo` or add a side condition.** Check if the `non_interference_stmt` theorem's conclusion actually needs the full `stores_agree_low_fo` or if it's only used internally.

8. **If `stores_agree_low_fo` proves too hard to maintain for wrapper types**, consider option: remove `stores_agree_low_fo` from `exp_rel_n` entirely. It was added as a performance optimization for the function case. If `val_rel_n` for ALL locations already gives you everything, `stores_agree_low_fo` may be redundant. But this is invasive — you'd need to update `exp_rel_n`, all proofs that establish it, and all proofs that consume it. Only do this as a last resort.

---

## OUTPUT FORMAT

Provide the TWO complete files:

1. **`NonInterference_v2.v`** — The complete 2600+ line file with changes applied
2. **`NonInterference_v2_LogicalRelation.v`** — The complete 4400+ line file with changes applied

Each file must be the COMPLETE file content, not a diff. I will directly overwrite the existing files with your output.

If the files are too large for a single response, split across multiple messages but clearly label each part.

**CRITICAL:** Before writing the files, READ the actual source files from the GitHub repo (https://github.com/ib823/proof, branch main, path `02_FORMAL/coq/properties/`). Do NOT guess at file contents. The exact variable names, line structure, and proof tactics must match.
