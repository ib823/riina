# AXIOM ELIMINATION — DETAILED ATTACK PLAN

## Current State
- **Axioms:** 31
- **Admitted:** 0
- **Target:** 8-12 foundational axioms

---

## TIER 1: IMMEDIATELY ATTACKABLE (5 axioms)

### 1.1 Language Constructs — T_Handle (1 axiom)

**Axiom:**
```coq
Axiom logical_relation_handle : forall Γ Σ e x h T2 rho1 rho2 n,
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ T2 (subst_rho rho1 (EHandle e x h))
                   (subst_rho rho2 (EHandle e x h)).
```

**Attack Strategy:**
1. Use IH on e to get exp_rel for guarded expression
2. When e evaluates to v, EHandle v x h --> [x := v] h
3. Need to show: exp_rel for [x := v1] h and [x := v2] h
4. Key lemma needed: `subst_preserves_exp_rel`

**Proof Sketch:**
```coq
Lemma logical_relation_handle_proof : ...
Proof.
  intros. specialize (IHHty1 rho1 rho2 Henv Hno1 Hno2) as He_rel.
  unfold exp_rel in *. intros n.
  destruct n as [| n']; [simpl; trivial |].
  simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore.
  specialize (He_rel (S n') ...) as [v1 [v2 ...]].
  (* After e -->* v, need to evaluate [x := v] h *)
  (* Use IH on h with extended env_rel *)
  exists ..., ..., ..., ..., ..., ...
  (* Key: env_rel ((x,T1)::Γ) for substituted h *)
Qed.
```

**Difficulty:** MEDIUM — Requires env_rel extension lemma

---

### 1.2 Closedness Contradictions (2 axioms)

**Axioms:**
```coq
Axiom lam_closedness_contradiction : forall Σ Γ rho1 rho2 y,
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  free_in y (rho1 y) -> False.

Axiom lam_closedness_contradiction2 : (* symmetric *)
```

**Attack Strategy:**
1. Add "free variables in context" lemma:
```coq
Lemma free_in_typing : forall Γ Σ Δ e T ε x,
  has_type Γ Σ Δ e T ε ->
  free_in x e ->
  exists T', lookup x Γ = Some T'.
```

2. In lam_closedness proof context:
   - We have `free_in z e` where e is well-typed in `((x,T1)::Γ)`
   - If z = y and z ≠ x, then `lookup y Γ = Some T`
   - By `env_rel_rho_closed`, `closed_expr (rho1 y)`
   - This contradicts `free_in y (rho1 y)`

**Proof Sketch:**
```coq
Lemma lam_closedness_contradiction_proof : forall Σ Γ rho1 rho2 y,
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  lookup y Γ <> None ->  (* ADDED PREMISE *)
  free_in y (rho1 y) -> False.
Proof.
  intros. destruct (lookup y Γ) as [T|] eqn:Hlook.
  - apply (env_rel_rho_closed _ _ _ _ y T H Hlook).
    exact H2.
  - contradiction.
Qed.
```

**Difficulty:** MEDIUM — Requires adding `free_in_typing` lemma OR modifying call site

---

### 1.3 Step-1 Evaluation — EFst/ESnd (2 axioms)

**Axioms:**
```coq
Axiom exp_rel_step1_fst : forall Σ T1 v v' st1 st2 ctx Σ',
  value v -> value v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 st1' st2' ctx' Σ'',
    ... (EFst v, st1, ctx) -->* (a1, st1', ctx') ...
```

**Attack Strategy:**
1. Values v, v' must be pairs (by typing in original context)
2. Add typing premise to axiom OR track typing through relation
3. Use canonical_pair from Progress.v

**Option A — Add Typing Premise:**
```coq
Lemma exp_rel_step1_fst_typed : forall Σ T1 T2 v v' st1 st2 ctx Σ',
  has_type nil Σ' Public v (TProd T1 T2) EffectPure ->
  has_type nil Σ' Public v' (TProd T1 T2) EffectPure ->
  value v -> value v' ->
  store_rel_n 0 Σ' st1 st2 ->
  store_ty_extends Σ Σ' ->
  exists a1 a2 ...
Proof.
  intros.
  destruct (canonical_pair v T1 T2 EffectPure Σ' H H1) as [a1 [b1 [Heq1 _]]].
  destruct (canonical_pair v' T1 T2 EffectPure Σ' H0 H2) as [a2 [b2 [Heq2 _]]].
  subst. exists a1, a2, st1, st2, ctx, Σ'.
  split. { reflexivity. }
  split. { eapply MS_Step. apply ST_FstPair. ... apply MS_Refl. }
  ...
Qed.
```

**Difficulty:** MEDIUM — Requires refactoring call sites to pass typing

---

## TIER 2: REQUIRES INFRASTRUCTURE (12 axioms)

### 2.1 Value Extraction (8 axioms)

**Axioms:**
```coq
val_rel_at_type_value_left      val_rel_at_type_value_right
val_rel_at_type_closed_left     val_rel_at_type_closed_right
val_rel_at_type_value_any_left  val_rel_at_type_value_any_right
val_rel_at_type_closed_any_left val_rel_at_type_closed_any_right
```

**Problem Analysis:**
- val_rel_at_type for TBytes = `v1 = v2` (no value constraint)
- val_rel_at_type for TSecret = `True` (no constraint at all)
- val_rel_at_type for TCapability = `True`
- val_rel_at_type for TProof = `True`

**Attack Strategy A — Restrict to Structural Types:**
```coq
Fixpoint structural_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString => true
  | TRef T' _ => true
  | TProd T1 T2 => structural_type T1 && structural_type T2
  | TSum T1 T2 => structural_type T1 && structural_type T2
  | TFn _ _ _ => true  (* lambdas are values *)
  | _ => false  (* TBytes, TSecret, TCapability, TProof *)
  end.

Lemma val_rel_at_type_value_left_structural : forall T Σ sp vl sl v1 v2,
  structural_type T = true ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  value v1.
```

**Attack Strategy B — Use val_rel_n instead:**
- val_rel_n (S n') explicitly includes `value v1 /\ value v2`
- Refactor uses to require val_rel_n at step > 0

**Difficulty:** HIGH — Requires understanding all call sites

---

### 2.2 Weakening Axioms (4 axioms)

**Axioms:**
```coq
val_rel_n_weaken      (* Σ' ⊇ Σ → val_rel_n Σ' → val_rel_n Σ *)
store_rel_n_weaken    (* mutual *)
val_rel_n_mono_store  (* Σ' ⊇ Σ → val_rel_n Σ → val_rel_n Σ' *)
store_rel_n_mono_store (* mutual *)
```

**Attack Strategy:**
1. Mutual induction on (n, structure of T)
2. For TFn: contravariance in T1, covariance in T2
3. Need well-founded recursion on (n, type_size T)

**Proof Sketch:**
```coq
Lemma val_store_mono_store :
  (forall n Σ Σ' T v1 v2,
    store_ty_extends Σ Σ' ->
    val_rel_n n Σ T v1 v2 ->
    val_rel_n n Σ' T v1 v2) /\
  (forall n Σ Σ' st1 st2,
    store_ty_extends Σ Σ' ->
    store_rel_n n Σ st1 st2 ->
    store_rel_n n Σ' st1 st2).
Proof.
  apply (nat_ind2 (fun n => ... /\ ...)).
  - (* n = 0 *) split; intros; simpl; trivial.
  - (* n = S n' *) intros n' [IHval IHstore]. split.
    + (* val_rel_n *) intros. destruct H0 as [Hcum [Hv1 [Hv2 [Hc1 [Hc2 Hrat]]]]].
      split. { apply IHval; assumption. }
      split. { exact Hv1. } ...
      (* For TFn case: need contravariance argument *)
    + (* store_rel_n *) ...
Qed.
```

**Difficulty:** HIGH — TFn contravariance requires careful handling

---

## TIER 3: FOUNDATIONAL — DO NOT ATTACK (8 axioms)

These represent irreducible semantic assumptions:

| Axiom | Justification | Reference |
|-------|---------------|-----------|
| `val_rel_n_to_val_rel` | Step-up closure | Ahmed 2006 |
| `val_rel_n_step_up` | Step index lifting | Appel & McAllester 2001 |
| `store_rel_n_step_up` | Mutual with above | Appel & McAllester 2001 |
| `val_rel_n_lam_cumulative` | Lambda step-up | Ahmed 2006 |
| `val_rel_at_type_to_val_rel_ho` | HO type lifting | Dreyer 2011 |
| `tapp_step0_complete` | App termination | Standard |
| `logical_relation_declassify` | Trust boundary | By design |
| (one more if needed) | | |

**Recommended Action:** Add literature citations in comments, mark as `(** FOUNDATIONAL AXIOM **)`.

---

## TIER 4: REQUIRES MAJOR REFACTORING (6 axioms)

### 4.1 Step-1 Evaluation — Complex (4 axioms)
```
exp_rel_step1_case
exp_rel_step1_if
exp_rel_step1_let
exp_rel_step1_app
```

**Problem:** These require tracking typing through the logical relation.

**Attack Strategy — Type-Indexed Logical Relation:**
```coq
(* Current: *)
Definition exp_rel_n n Σ T e1 e2 := ...

(* Refactored: *)
Definition exp_rel_n n Σ Γ e T e1 e2 :=
  has_type Γ Σ Public e T EffectPure ->
  ... (* can now use canonical forms *)
```

**Difficulty:** VERY HIGH — Major architectural change

---

### 4.2 Store Operations (3 axioms)
```
logical_relation_ref
logical_relation_deref
logical_relation_assign
```

**Problem:** Depend on weakening axioms + store typing manipulation.

**Attack Strategy:**
1. First prove weakening axioms (Tier 2.2)
2. Then inline proofs using store_ty_extends lemmas

**Proof Sketch for T_Ref:**
```coq
(* After eliminating weakening axioms *)
- (* T_Ref *)
  specialize (IHHty rho1 rho2 Henv Hno1 Hno2) as He_rel.
  unfold exp_rel in *. intros n.
  destruct n as [| n']; [simpl; trivial |].
  simpl. intros Σ_cur st1 st2 ctx Hext_cur Hstore.
  specialize (He_rel (S n') ...) as [v1 [v2 ...]].
  (* Allocate new location l *)
  set (l := fresh_loc st1').
  set (Σ'' := extend_store_ty Σ' l T sl).
  exists (ELoc l), (ELoc l), (store_update l v1 st1'), ...
  split. { (* store_ty_extends Σ' Σ'' *) ... }
  split. { (* ERef steps *) apply multi_step_ref. ... }
  ...
  (* Use val_rel_n_mono_store for extended Σ'' *)
```

**Difficulty:** HIGH — Chain of dependencies

---

## ATTACK PRIORITY ORDER

```
PHASE 1 (Quick Wins — 3-5 axioms):
  1. lam_closedness_contradiction (with free_in_typing lemma)
  2. lam_closedness_contradiction2
  3. logical_relation_handle (if env_rel extension works)

PHASE 2 (Medium Effort — 4-6 axioms):
  4. exp_rel_step1_fst (add typing premise)
  5. exp_rel_step1_snd
  6. val_rel_at_type_* (restrict to structural types)

PHASE 3 (High Effort — 4 axioms):
  7. val_rel_n_weaken
  8. store_rel_n_weaken
  9. val_rel_n_mono_store
  10. store_rel_n_mono_store

PHASE 4 (Store Operations — 3 axioms):
  11. logical_relation_ref
  12. logical_relation_deref
  13. logical_relation_assign

PHASE 5 (Accept as Foundational — 8 axioms):
  - Document with literature references
  - Mark as semantic assumptions
```

---

## ESTIMATED OUTCOME

| Phase | Axioms Eliminated | Remaining |
|-------|-------------------|-----------|
| Start | 0 | 31 |
| Phase 1 | 2-3 | 28-29 |
| Phase 2 | 4-6 | 22-25 |
| Phase 3 | 4 | 18-21 |
| Phase 4 | 3 | 15-18 |
| Final | — | **8-12 foundational** |

---

## IMMEDIATE NEXT ACTIONS

1. **Add `free_in_typing` lemma** to Typing.v
2. **Prove `lam_closedness_contradiction`** with added lookup premise
3. **Refactor call site** in T_Lam case to provide lookup evidence
4. **Repeat for `lam_closedness_contradiction2`**

```bash
# Start with:
grep -n "lam_closedness_contradiction" 02_FORMAL/coq/properties/NonInterference.v
```
