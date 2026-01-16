# Track A: Proof Completion Specification

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  SPECIFICATION: PROOF COMPLETION FOR TRACK A                                     ║
║  Version: 1.0.0                                                                  ║
║  Date: 2026-01-16                                                                ║
║  Status: SPECIFICATION - Ready for Implementation                                ║
║                                                                                  ║
║  Goal: Eliminate ALL axioms (6) and admitted lemmas (8) from 02_FORMAL/coq/      ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

## 1. Current State Audit

### 1.1 Axioms to Eliminate (6 total)

| # | Axiom | File | Purpose |
|---|-------|------|---------|
| 1 | `val_rel_n_weaken` | NonInterference.v:490 | Value relation contravariant in store typing |
| 2 | `store_rel_n_weaken` | NonInterference.v:501 | Store relation contravariant in store typing |
| 3 | `val_rel_n_mono_store` | NonInterference.v:~510 | Kripke monotonicity for values |
| 4 | `store_rel_n_mono_store` | NonInterference.v:~520 | Kripke monotonicity for stores |
| 5 | `val_rel_at_type_value_left` | NonInterference.v:247 | First-order types yield values |
| 6 | `val_rel_at_type_value_right` | NonInterference.v:252 | First-order types yield values |
| 7 | `val_rel_at_type_closed_left` | NonInterference.v:257 | First-order types are closed |
| 8 | `val_rel_at_type_closed_right` | NonInterference.v:262 | First-order types are closed |

*Note: 4 axioms are `val_rel_at_type_*` helpers, can be proven directly*

### 1.2 Admitted Lemmas (8 total)

| # | Lemma | File | Blocking Reason |
|---|-------|------|-----------------|
| 1 | `gate_enforcement` | EffectGate.v | Missing effect typing formalization |
| 2 | `core_effects_within` | EffectSystem.v | Missing effect context model |
| 3 | `effect_safety` | EffectSystem.v | Depends on #2 |
| 4 | `val_rel_pair` | Composition.v | Step-index mismatch in products |
| 5 | `val_rel_inl` | Composition.v | Step-index mismatch in sums |
| 6 | `val_rel_inr` | Composition.v | Step-index mismatch in sums |
| 7 | `logical_relation` | NonInterference.v | Fundamental theorem incomplete |
| 8 | `non_interference_stmt` | NonInterference.v | Depends on #7 |

---

## 2. Root Cause Analysis

### 2.1 The Step-Index Problem

The current definition of `val_rel_n` and `store_rel_n` uses mutual recursion:

```coq
Fixpoint val_rel_n (n : nat) ... : Prop :=
  match n with
  | S n' => ... val_rel_at_type ... (val_rel_n n' Σ) ...
  end
with store_rel_n (n : nat) ... : Prop :=
  match n with
  | S n' => ... val_rel_n n' Σ T v1 v2 ...
  end.
```

**Problem:** For function types, `val_rel_at_type` needs to call `val_rel_lower` at index `n-1`, but also needs `store_rel_lower` at `n-1`. The mutual recursion makes Kripke-style weakening (where store typing can grow) unprovable without axioms.

### 2.2 The Weakening Problem

Current attempt:
```coq
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

**Why unprovable:** When `T = TFn T1 T2 eff`, the function body needs to work in ANY future world `Σ''` extending `Σ'`. But we only have `Σ'` extending `Σ`, not transitivity through `Σ''`.

### 2.3 The First-Order Helper Problem

```coq
Axiom val_rel_at_type_value_left : forall T Σ sp vl sl v1 v2,
  first_order_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  value v1.
```

**Why currently axiom:** Tedious case analysis over all first-order types. Should be provable but is left as axiom for engineering convenience.

---

## 3. Solution Architecture

### 3.1 Restructure to Kripke Worlds

**Key Insight:** Make the "world" (step count + store typing) explicit and quantify universally over future worlds in function types.

```coq
(* NEW: World structure *)
Record World := mkWorld {
  w_n : nat;           (* Step index *)
  w_Σ : store_ty;      (* Store typing *)
}.

(* NEW: World ordering - future worlds have LOWER step count and LARGER store *)
Definition world_future (w w' : World) : Prop :=
  w'.(w_n) <= w.(w_n) /\ store_ty_extends w.(w_Σ) w'.(w_Σ).

(* World ordering is transitive *)
Lemma world_future_trans : forall w1 w2 w3,
  world_future w1 w2 -> world_future w2 w3 -> world_future w1 w3.
Proof.
  intros [n1 Σ1] [n2 Σ2] [n3 Σ3] [Hn12 HΣ12] [Hn23 HΣ23].
  unfold world_future. split.
  - lia.
  - eapply store_ty_extends_trans; eauto.
Qed.
```

### 3.2 New Value Relation Definition

```coq
(* Value relation indexed by world *)
Fixpoint val_rel_w (w : World) (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret T' => True  (* Secret values always related *)

  | TRef T' sl =>
      exists l, v1 = ELoc l /\ v2 = ELoc l

  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_w w T1 x1 x2 /\ val_rel_w w T2 y1 y2

  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_w w T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_w w T2 y1 y2)

  | TFn T1 T2 eff =>
      (* KEY CHANGE: Universal quantification over future worlds *)
      forall w', world_future w w' ->
        forall x y, val_rel_w w' T1 x y ->
          forall st1 st2 ctx,
            store_rel_w w' st1 st2 ->
            (* Function application terminates and results related in some future world *)
            exists v1' v2' st1' st2' ctx' w'',
              world_future w' w'' /\
              (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
              (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
              val_rel_w w'' T2 v1' v2' /\
              store_rel_w w'' st1' st2'

  | TCapability _ => True
  | TProof _ => True
  end

with store_rel_w (w : World) (st1 st2 : store) {struct w} : Prop :=
  match w.(w_n) with
  | 0 => True
  | S n' =>
      let w' := mkWorld n' w.(w_Σ) in
      store_rel_w w' st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l w.(w_Σ) = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_w w' T v1 v2)
  end.
```

**Why this fixes the axiom problem:**

The `TFn` case now says: "for ALL future worlds w', if arguments are related at w', then results are related at SOME even further world w''."

Weakening becomes trivial:
- If `val_rel_w w T v1 v2` and `world_future w0 w`, we need `val_rel_w w0 T v1 v2`
- For `TFn`: The premise gives us relatedness for all worlds future-from-w
- Since `world_future w0 w`, any world future-from-w0 is also future-from-w
- So we can just use the same witnesses

### 3.3 Weakening Proof

```coq
Lemma val_rel_w_weaken : forall w w' T v1 v2,
  world_future w' w ->
  val_rel_w w T v1 v2 ->
  val_rel_w w' T v1 v2.
Proof.
  intros w w' T. revert w w'.
  induction T; intros w w' v1 v2 Hfut Hrel; simpl in *.

  - (* TUnit *) exact Hrel.
  - (* TBool *) exact Hrel.
  - (* TInt *) exact Hrel.
  - (* TString *) exact Hrel.
  - (* TBytes *) exact Hrel.

  - (* TFn *)
    (* KEY: Use transitivity of world_future *)
    intros w'' Hfut' x y Hxy st1 st2 ctx Hst.
    (* w'' is future of w', which is future of w *)
    (* So w'' is future of w, and we can use the hypothesis *)
    apply Hrel.
    + eapply world_future_trans; eauto.
    + exact Hxy.
    + exact Hst.

  - (* TProd *)
    destruct Hrel as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    exists x1, y1, x2, y2. repeat split; auto.
    + apply IHT1 with w; auto.
    + apply IHT2 with w; auto.

  - (* TSum *)
    destruct Hrel as [[x1 [x2 [Heq1 [Heq2 Hrel1]]]] | [y1 [y2 [Heq1 [Heq2 Hrel2]]]]].
    + left. exists x1, x2. repeat split; auto. apply IHT1 with w; auto.
    + right. exists y1, y2. repeat split; auto. apply IHT2 with w; auto.

  - (* TRef *) exact Hrel.
  - (* TSecret *) exact I.
  - (* TCapability *) exact I.
  - (* TProof *) exact I.
Qed.
```

### 3.4 First-Order Helper Proofs

These are straightforward once we do the case analysis:

```coq
Lemma val_rel_w_value_first_order : forall T w v1 v2,
  first_order_type T = true ->
  val_rel_w w T v1 v2 ->
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2.
Proof.
  induction T; intros w v1 v2 Hfo Hrel; simpl in *.

  - (* TUnit *)
    destruct Hrel as [Heq1 Heq2]. subst.
    repeat split; constructor.

  - (* TBool *)
    destruct Hrel as [b [Heq1 Heq2]]. subst.
    repeat split; try constructor.
    (* closed_expr for EBool *)
    intros x Hfree. simpl in Hfree. contradiction.
    intros x Hfree. simpl in Hfree. contradiction.

  - (* TInt *)
    destruct Hrel as [i [Heq1 Heq2]]. subst.
    repeat split; try constructor.
    intros x Hfree. simpl in Hfree. contradiction.
    intros x Hfree. simpl in Hfree. contradiction.

  (* ... similar for TString, TBytes *)

  - (* TFn - contradiction, not first-order *)
    discriminate.

  - (* TProd *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    destruct Hrel as [x1 [y1 [x2 [y2 [Heq1 [Heq2 [Hrel1 Hrel2]]]]]]].
    subst.
    specialize (IHT1 w x1 x2 Hfo1 Hrel1) as [Hv1 [Hv1' [Hc1 Hc1']]].
    specialize (IHT2 w y1 y2 Hfo2 Hrel2) as [Hv2 [Hv2' [Hc2 Hc2']]].
    repeat split.
    + constructor; assumption.
    + constructor; assumption.
    + apply closed_expr_pair; assumption.
    + apply closed_expr_pair; assumption.

  (* ... similar for TSum, TRef, TSecret, TCapability, TProof *)
Qed.
```

---

## 4. Implementation Plan

### 4.1 Step 1: Create New File Structure

```
02_FORMAL/coq/properties/
├── NonInterference.v          (CURRENT - will be deprecated)
├── KripkeWorlds.v             (NEW - world definitions)
├── ValueRelation.v            (NEW - val_rel_w definition)
├── StoreRelation.v            (NEW - store_rel_w definition)
├── RelationWeakening.v        (NEW - weakening proofs)
├── FundamentalTheorem.v       (NEW - logical_relation)
└── NonInterferenceNew.v       (NEW - final theorem)
```

### 4.2 Step 2: Implementation Order

1. **KripkeWorlds.v** - World definitions, ordering, transitivity
2. **ValueRelation.v** - New val_rel_w definition
3. **StoreRelation.v** - New store_rel_w definition
4. **RelationWeakening.v** - Prove weakening lemmas (no axioms!)
5. **FundamentalTheorem.v** - Complete all 20 cases
6. **NonInterferenceNew.v** - Final non-interference theorem

### 4.3 Step 3: Migrate and Delete

1. Update imports in all files to use new modules
2. Verify all proofs compile
3. Delete NonInterference.v
4. Rename NonInterferenceNew.v to NonInterference.v

---

## 5. Case-by-Case Proof Strategy for Fundamental Theorem

### 5.1 T_Unit, T_Bool, T_Int, T_String (Easy)

**Strategy:** Direct application of val_rel_w definition.

```coq
Case "T_Unit":
  (* Γ; Σ ⊢ EUnit : TUnit @ Pure *)
  intros w st1 st2 ctx Hst.
  exists EUnit, EUnit, st1, st2, ctx, w.
  repeat split; try reflexivity.
  - apply MS_Refl.
  - apply MS_Refl.
  - simpl. auto.
  - exact Hst.
```

### 5.2 T_Var (Medium)

**Strategy:** Use related substitution.

```coq
Case "T_Var":
  (* Γ(x) = T, so γ1(x) and γ2(x) are related by val_rel_w w T *)
  intros w st1 st2 ctx Hst.
  (* Get relatedness from substitution *)
  specialize (Hγ x) as [v1 [v2 [Hγ1 [Hγ2 Hrel]]]].
  (* Variables step to their substitution values *)
  exists v1, v2, st1, st2, ctx, w.
  repeat split.
  - (* reduction *) rewrite Hγ1. apply MS_Refl.
  - (* reduction *) rewrite Hγ2. apply MS_Refl.
  - exact Hrel.
  - exact Hst.
```

### 5.3 T_Lam (Hard)

**Strategy:** Build function value, show it satisfies val_rel_w for TFn.

```coq
Case "T_Lam":
  (* Γ, x:T1; Σ ⊢ body : T2 @ eff *)
  (* Need: val_rel_w w (TFn T1 T2 eff) (γ1(λx.body)) (γ2(λx.body)) *)
  intros w st1 st2 ctx Hst.

  (* Lambda values: γ(λx.body) = λx.γ(body) for variables not x *)
  set (v1 := ELam x T1 (subst_except x γ1 body)).
  set (v2 := ELam x T2 (subst_except x γ2 body)).

  exists v1, v2, st1, st2, ctx, w.
  repeat split.
  - apply MS_Refl. (* lambdas are values *)
  - apply MS_Refl.
  - (* val_rel_w for TFn *)
    simpl. intros w' Hfut arg1 arg2 Harg st1' st2' ctx' Hst'.
    (* Extend substitution with argument *)
    set (γ1' := extend γ1 x arg1).
    set (γ2' := extend γ2 x arg2).
    (* Apply IH for body *)
    specialize (IHbody (γ1', γ2') w' ...) as [v1' [v2' ...]].
    (* Beta reduction: (λx.body) arg -->* body[arg/x] -->* v *)
    (* ... complete the proof *)
  - exact Hst.
```

### 5.4 T_App (Very Hard)

**Strategy:** Use IH for function and argument, then use function's val_rel_w.

```coq
Case "T_App":
  (* Γ; Σ ⊢ e1 : T1 → T2 @ eff1 *)
  (* Γ; Σ ⊢ e2 : T1 @ eff2 *)
  intros w st1 st2 ctx Hst.

  (* Step 1: Evaluate e1 to function values *)
  specialize (IHe1 γ w st1 st2 ctx Hst) as
    [f1 [f2 [st1_1 [st2_1 [ctx1 [w1 [Hfut1 [Hstep_f1 [Hstep_f2 [Hrel_f Hst1]]]]]]]]]].

  (* Step 2: Evaluate e2 to argument values in updated stores *)
  specialize (IHe2 γ w1 st1_1 st2_1 ctx1 Hst1) as
    [a1 [a2 [st1_2 [st2_2 [ctx2 [w2 [Hfut2 [Hstep_a1 [Hstep_a2 [Hrel_a Hst2]]]]]]]]]].

  (* Step 3: Apply function relatedness *)
  (* f1, f2 : TFn T1 T2 eff, so val_rel_w w1 (TFn T1 T2 eff) f1 f2 *)
  (* Need to weaken to w2 first *)
  assert (val_rel_w w2 (TFn T1 T2 eff) f1 f2) as Hrel_f'.
  { apply val_rel_w_weaken with w1; auto. }

  (* Now apply the function relation *)
  specialize (Hrel_f' w2 (world_future_refl w2) a1 a2 Hrel_a st1_2 st2_2 ctx2 Hst2)
    as [v1 [v2 [st1' [st2' [ctx' [w' ...]]]]]].

  (* Compose reductions: e1 e2 -->* f1 a1 -->* v1 *)
  (* ... *)
```

### 5.5 T_Ref, T_Deref, T_Assign (Store Operations)

**Strategy:** Track store extensions through evaluation.

These cases require careful handling of store typing extensions:
1. T_Ref allocates a new location, extending Σ
2. T_Deref reads from store, must show related values at that location
3. T_Assign updates store, must show store relation preserved

### 5.6 T_Declassify (Security-Critical)

**Strategy:** Declassification must be identity on related secrets.

```coq
Case "T_Declassify":
  (* declassify (classify v) with proof = v *)
  (* Secret values are always related (True in val_rel_w) *)
  (* After declassification, underlying values must be related *)
  (* This case requires the proof object to be valid *)
```

---

## 6. Effect System Completion

### 6.1 New Effect Model

Replace admitted lemmas in EffectSystem.v and EffectGate.v with:

```coq
(* Effect context as permission set *)
Definition eff_ctx_allows (ctx : effect_ctx) (eff : effect) : Prop :=
  eff.(eff_read) = true -> has_capability ctx CapRead /\
  eff.(eff_write) = true -> has_capability ctx CapWrite /\
  (* ... etc *)

(* Effect safety: well-typed programs only perform allowed effects *)
Theorem effect_safety : forall Γ Σ e T eff ctx st,
  has_type Γ Σ e T eff ->
  eff_ctx_allows ctx eff ->
  forall e' st' ctx',
    (e, st, ctx) -->* (e', st', ctx') ->
    eff_ctx_allows ctx' eff.
Proof.
  (* Induction on typing derivation *)
  (* Each reduction rule preserves effect allowance *)
Qed.
```

---

## 7. Verification Criteria

### 7.1 Axiom Count

**Current:** 6-8 axioms
**Target:** 0 axioms

**Verification Command:**
```bash
cd 02_FORMAL/coq && grep -r "Axiom" *.v properties/*.v
```

**Expected Output:** Empty (no matches)

### 7.2 Admitted Count

**Current:** 8 admitted lemmas
**Target:** 0 admitted lemmas

**Verification Command:**
```bash
cd 02_FORMAL/coq && grep -r "Admitted\|admit\." *.v **/*.v
```

**Expected Output:** Empty (no matches)

### 7.3 Compilation

**Verification Command:**
```bash
cd 02_FORMAL/coq && make clean && make
```

**Expected Output:** Successful compilation with no errors

### 7.4 Proof Checking

After implementation, verify with:
```bash
coqchk -Q . RIINA RIINA.properties.NonInterference
```

This checks the entire proof development is valid.

---

## 8. Estimated Effort

| Task | Complexity Units | Dependencies |
|------|------------------|--------------|
| KripkeWorlds.v | 15 | None |
| ValueRelation.v | 25 | KripkeWorlds.v |
| StoreRelation.v | 20 | KripkeWorlds.v |
| RelationWeakening.v | 30 | Value/StoreRelation.v |
| FundamentalTheorem.v | 100 | All above |
| Effect system fixes | 40 | None |
| Migration & cleanup | 20 | All above |
| **Total** | **250** | |

---

## 9. Risk Mitigation

### 9.1 Termination Risk

The new `val_rel_w` uses structural recursion on `T`, but `TFn` calls itself with `T1` and `T2`. Coq should accept this, but verify early.

**Mitigation:** If Coq rejects, use Program Fixpoint with manual measure.

### 9.2 Store Relation Recursion Risk

`store_rel_w` is defined by recursion on `w.(w_n)`, calling `val_rel_w` on a "smaller" world. Need to ensure termination.

**Mitigation:** Use well-founded recursion on `(w_n, T)` lexicographically if needed.

### 9.3 Integration Risk

New definitions must be compatible with existing Progress/Preservation proofs.

**Mitigation:** Keep original NonInterference.v until new version is complete and tested.

---

*Document Status: SPECIFICATION - Ready for Implementation*
*Last Updated: 2026-01-16*
