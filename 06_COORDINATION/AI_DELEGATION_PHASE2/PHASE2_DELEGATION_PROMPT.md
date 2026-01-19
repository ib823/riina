# PHASE 2: Mutual Induction Proof Delegation

## Target AIs: Claude AI, DeepSeek, Grok

---

## TASK OVERVIEW

Prove `val_rel_n_mono` (downward monotonicity for ALL types) using mutual induction with `store_rel_n_mono`.

**Why Mutual Induction?**
- `val_rel_n_mono` for TFn needs `store_rel_n` stepping (Kripke clause)
- `store_rel_n_mono` needs `val_rel_n_mono` for stored values
- Circular dependency → solve together

---

## THE TWO LEMMAS TO PROVE

### Lemma 1: val_rel_n_mono
```coq
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
```

### Lemma 2: store_rel_n_mono
```coq
Lemma store_rel_n_mono : forall m n Σ st1 st2,
  m <= n ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n m Σ st1 st2.
```

---

## KEY DEFINITIONS

### val_rel_n (Step-Indexed Value Relation)
```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 =>
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end.
```

### store_rel_n (Step-Indexed Store Relation)
```coq
Fixpoint store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  match n with
  | 0 => store_max st1 = store_max st2
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' Σ T v1 v2)
  end.
```

### val_rel_at_type for TFn (THE HARD CASE)
```coq
| TFn T1 T2 eff =>
    forall Σ', store_ty_extends Σ Σ' ->
      forall x y,
        value x -> value y -> closed_expr x -> closed_expr y ->
        val_rel_lower Σ' T1 x y ->           (* Uses val_rel_n n' *)
        forall st1 st2 ctx,
          store_rel_pred Σ' st1 st2 ->       (* Uses store_rel_n n' *)
          exists v1' v2' st1' st2' ctx' Σ'',
            store_ty_extends Σ' Σ'' /\
            (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
            (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
            val_rel_lower Σ'' T2 v1' v2' /\
            store_rel_lower Σ'' st1' st2'
```

---

## ALREADY PROVEN (USE THESE)

### 1. val_rel_n_mono_fo (FO-only version)
```coq
Lemma val_rel_n_mono_fo : forall m n Σ T v1 v2,
  first_order_type T = true ->
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
(* PROVEN with Qed *)
```

### 2. val_rel_at_type_fo_equiv
```coq
Lemma val_rel_at_type_fo_equiv : forall T Σ SR VR SR' v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ SR VR SR' T v1 v2 <-> val_rel_at_type_fo T v1 v2.
(* PROVEN with Qed *)
```

### 3. Unfolding lemmas
```coq
Lemma val_rel_n_0_unfold, val_rel_n_S_unfold
Lemma store_rel_n_0_unfold, store_rel_n_S_unfold
(* All PROVEN with Qed *)
```

---

## THE PROBLEM: TFn Case in val_rel_n_mono

Current partial proof has TWO admits in the TFn case:

### Admit 1: FO argument type (T1 is first-order)
```coq
(* We have: Hxyrel_m : val_rel_n m' Σ' T1 x y *)
(* We have: Hstrel_m : store_rel_n m' Σ' st1 st2 *)
(* Hrat expects: val_rel_n n' and store_rel_n n' *)
(* Need to step UP from m' to n' for both *)
admit.  (* Line 541 *)
```

### Admit 2: HO argument type (T1 is higher-order)
```coq
(* T1 has functions, so val_rel_n m' ≠ val_rel_n n' in general *)
(* Need typing + Kripke reasoning *)
admit.  (* Line 548 *)
```

---

## PROOF STRATEGY: Mutual Induction

### Approach A: Combined Lemma
```coq
Lemma val_store_rel_n_mono : forall m n,
  m <= n ->
  (forall Σ T v1 v2, val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2) /\
  (forall Σ st1 st2, store_rel_n n Σ st1 st2 -> store_rel_n m Σ st1 st2).
Proof.
  intros m n Hle.
  (* Strong induction on (n - m) *)
  remember (n - m) as d.
  generalize dependent n. generalize dependent m.
  induction d as [|d' IHd]; intros m n Heqd Hle.
  - (* d = 0: m = n, trivial *)
    assert (m = n) by lia. subst. split; auto.
  - (* d = S d': need to step down from n *)
    (* Key: use IH with (n-1) *)
    ...
Qed.
```

### Approach B: Prove store_rel_n_mono first (it's simpler)
```coq
(* store_rel_n only stores values, doesn't have Kripke clause *)
Lemma store_rel_n_mono : forall m n Σ st1 st2,
  m <= n ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n m Σ st1 st2.
Proof.
  intros m n. generalize dependent m.
  induction n as [|n' IHn]; intros m Σ st1 st2 Hle Hn.
  - inversion Hle. exact Hn.
  - destruct m as [|m'].
    + (* m = 0 *)
      rewrite store_rel_n_0_unfold.
      rewrite store_rel_n_S_unfold in Hn.
      destruct Hn as [_ [Hmax _]]. exact Hmax.
    + (* m = S m' *)
      rewrite store_rel_n_S_unfold.
      rewrite store_rel_n_S_unfold in Hn.
      destruct Hn as [Hrec [Hmax Hlocs]].
      split; [|split].
      * apply IHn; [lia | exact Hrec].
      * exact Hmax.
      * intros l T sl Hlook.
        specialize (Hlocs l T sl Hlook) as [v1 [v2 [Hst1 [Hst2 Hvrel]]]].
        exists v1, v2. repeat split; auto.
        (* Need: val_rel_n m' from val_rel_n n' *)
        (* THIS IS WHERE WE NEED val_rel_n_mono! *)
        (* But we're proving it... circular! *)
        (* SOLUTION: For stored values, use val_rel_n_mono_fo if T is FO *)
        (* For HO stored values, need the mutual induction *)
        ...
Qed.
```

---

## HINT: The Key Insight

For TFn at step (S n'), the Kripke clause says:
- Given args at val_rel_n n' and stores at store_rel_n n'
- Outputs are at val_rel_n n' and store_rel_n n'

When stepping down to (S m') where m' < n':
- We receive args at val_rel_n m' (MORE values than n')
- We receive stores at store_rel_n m' (MORE stores than n')

The key insight is:
1. For FO args: val_rel_n m' = val_rel_n n' = val_rel_at_type_fo (USE val_rel_n_mono_fo)
2. For HO args: Need to BUILD val_rel_n n' from val_rel_n m'
   - This requires val_rel_n_step_up which needs TYPING
   - Without typing, we cannot prove this case
   - SOLUTION: The TFn case may need to be AXIOMATIZED for HO args

---

## DELIVERABLE

Provide ONE of:

### Option 1: Complete Mutual Induction Proof
```coq
(* Full proof of both lemmas together *)
Lemma val_store_rel_n_mono : ...
Proof.
  ...
Qed.

(* Then derive individual lemmas *)
Lemma val_rel_n_mono : ... := proj1 (val_store_rel_n_mono ...).
Lemma store_rel_n_mono : ... := proj2 (val_store_rel_n_mono ...).
```

### Option 2: Proof with Documented Limitation
```coq
(* Prove as much as possible, document what's unprovable *)
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  ...
  (* TFn case with HO arguments cannot be proven without typing *)
  (* See LIMITATION.md for details *)
Admitted.
```

### Option 3: Strengthened Statement
```coq
(* Add typing precondition to make it provable *)
Lemma val_rel_n_mono_typed : forall m n Σ T v1 v2,
  m <= n ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  ...
Qed.
```

---

## VALIDATION

After receiving proof, test with:
```bash
cd /workspaces/proof/02_FORMAL/coq
# Replace the Admitted proof in NonInterference_v2.v
coqc -Q . RIINA properties/NonInterference_v2.v
# Should compile without errors
```

---

## FILES INCLUDED

1. `01_Definitions.v` - All definitions (450 lines)
2. `02_Current_val_rel_n_mono.v` - Current partial proof
3. `03_store_rel_n_mono.v` - Store relation mono proof
4. `PHASE2_DELEGATION_PROMPT.md` - This file

---

*Generated for RIINA Phase 2 Mutual Induction*
*Priority: P0 - Blocks fundamental theorem*
