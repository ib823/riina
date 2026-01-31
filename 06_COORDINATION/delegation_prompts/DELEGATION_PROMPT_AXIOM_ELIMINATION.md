# COMPREHENSIVE DELEGATION PROMPT: Eliminate Axioms in Step-Indexed Logical Relation (Coq/Rocq 9.1)

## MISSION

You are working on a Coq/Rocq 9.1 proof development for a security-typed programming language called RIINA. The goal is to **eliminate 5 axioms** from a step-indexed logical relation proof of noninterference, replacing each with a fully proven lemma (`Qed`, no `admit.`, no `Admitted.`).

**You must produce complete, compilable replacement code** for each axiom. The code must integrate into the existing codebase without breaking any existing proofs.

---

## THE 5 AXIOMS TO ELIMINATE

### Axiom 1: `fundamental_theorem_step_0` (in NonInterference_v2.v)

```coq
Axiom fundamental_theorem_step_0 : forall T Σ v1 v2,
  first_order_type T = false ->
  val_rel_n 0 Σ T v1 v2 ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2.
```

**Why it exists:** At step 0, `val_rel_n 0` for non-first-order types (functions, channels) gives `True` for the structural component (via `if first_order_type T then val_rel_at_type_fo T v1 v2 else True`). But `val_rel_at_type` at step 0 for function types requires: "for any related inputs and related stores, applying the function produces related outputs." This Kripke-like property cannot be derived from `True` alone—it needs the actual function behavior. The axiom bridges this gap.

**Where it's used:** In the `T_App` case of the `logical_relation` theorem (line ~3156-3164 of the LR file), when n'=0, to extract the function application behavior from step-0 value relatedness.

**Potential approach to eliminate:**
- At step 0, `exp_rel_n 0` is `True`, so the function case could vacuously hold
- Or restructure `val_rel_n 0` to include structural content for HO types
- Key insight: `val_rel_at_type` for `TFn` at step 0 requires producing `exp_rel_n 0` outputs, which are `True`—so the conclusion might be trivially satisfiable

---

### Axiom 2: `logical_relation_ref` (in NonInterference_v2_LogicalRelation.v)

```coq
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e T ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).
```

**Why it exists:** Creating a reference allocates a fresh location and stores a value. The proof needs to show the resulting stores are still related (`store_rel_n`) after extending with the new location. For LOW locations, `store_rel_n` requires `val_rel_n` for the stored value. For HIGH locations, it only requires typing. The fundamental difficulty is constructing the extended `Σ'` (store typing) and proving `store_ty_extends`.

**Where it's used:** In the `T_Ref` case of `logical_relation` (line ~4225-4233).

**Critical note:** The axiom does NOT take an `exp_rel` premise for the subexpression `e`, but the `logical_relation` proof has `IHHty` available (from induction on typing). A replacement lemma CAN add this premise.

---

### Axiom 3: `logical_relation_deref` (in NonInterference_v2_LogicalRelation.v)

```coq
Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e (TRef T l) ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).
```

**Why it exists:** Dereferencing a location `l` reads from the store. If `l` is LOW, `store_rel_n` gives `val_rel_n` directly. If `l` is HIGH, `store_rel_n` only gives typing (not `val_rel_n`). The axiom asserts that dereferencing always produces related values regardless of security level.

**Where it's used:** In the `T_Deref` case of `logical_relation` (line ~4234-4242).

---

### Axiom 4: `logical_relation_assign` (in NonInterference_v2_LogicalRelation.v)

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

**Why it exists:** Assignment updates a store location. Proving `store_rel_n` is preserved after update requires showing the new value satisfies the location's invariant. For LOW+FO locations, `stores_agree_low_fo` requires `store_lookup l st1 = store_lookup l st2` (syntactic equality), but `val_rel_at_type_fo` for wrapper types (TList, TConstantTime, etc.) returns `True`, not syntactic equality.

**Where it's used:** In the `T_Assign` case of `logical_relation` (line ~4243-4252).

---

### Axiom 5: `logical_relation_declassify` (in NonInterference_v2_LogicalRelation.v)

```coq
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n Σ_base,
  has_type Γ Σ Δ e (TSecret T) ε ->
  store_ty_extends Σ Σ_base ->
  env_rel Σ_base Γ rho1 rho2 ->
  rho_no_free_all rho1 ->
  rho_no_free_all rho2 ->
  exp_rel_n n Σ_base T (subst_rho rho1 (EDeclassify e p)) (subst_rho rho2 (EDeclassify e p)).
```

**Why it exists:** Declassification intentionally breaks noninterference. `e : TSecret T` evaluates to `EClassify w1`, `EClassify w2` where `w1 ≠ w2` in general (secret values differ between runs). `val_rel` at `T` for `w1, w2` is NOT guaranteed. This axiom encodes the programmer's declassification policy.

**IMPORTANT:** This axiom is a **POLICY AXIOM**—it is semantically correct to keep it as an axiom because declassification is inherently axiomatic (it's a trust boundary). However, if you can prove it under reasonable semantic assumptions, that would be a bonus.

---

## KEY DEFINITIONS

### The Mutual Fixpoint (val_rel_n / store_rel_n)

```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 =>
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      has_type nil Σ Public v1 T EffectPure /\
      has_type nil Σ Public v2 T EffectPure /\
      (if first_order_type T
       then val_rel_at_type_fo T v1 v2
       else True)
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
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          (if is_low_dec sl
           then val_rel_n n' Σ T v1 v2
           else (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
                 has_type nil Σ Public v1 T EffectPure /\
                 has_type nil Σ Public v2 T EffectPure)))
  end.
```

**Key observation:** `store_rel_n` uses `is_low_dec sl` to split behavior:
- **LOW locations:** require full `val_rel_n n'` (structural + typing)
- **HIGH locations:** only require typing (the observer can't see them)

This split is the root cause of difficulty for ref/deref/assign axioms.

### exp_rel_n

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

### Limit definitions

```coq
Definition val_rel (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  forall n, val_rel_n n Σ T v1 v2.

Definition exp_rel (Σ : store_ty) (T : ty) (e1 e2 : expr) : Prop :=
  forall n, exp_rel_n n Σ T e1 e2.

Definition env_rel (Σ : store_ty) (G : type_env) (rho1 rho2 : ident -> expr) : Prop :=
  forall n, env_rel_n n Σ G rho1 rho2.
```

### val_rel_at_type (parametric, inside a Section)

```coq
Fixpoint val_rel_at_type (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret T' => True
  | TLabeled T' _ => True | TTainted T' _ => True
  | TSanitized T' _ => True
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList T' => True | TOption T' => True
  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type T1 x1 x2 /\ val_rel_at_type T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type T2 y1 y2)
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
  | TCapability _ | TCapabilityFull _ | TProof _ => True
  | TChan _ | TSecureChan _ _ => True
  | TConstantTime T' => True | TZeroizing T' => True
  end.
```

Note: The section variables are `Σ`, `store_rel_pred`, `val_rel_lower`, `store_rel_lower`. When called from `val_rel_n (S n')`, these are instantiated as:
```
val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
```

### val_rel_at_type_fo

```coq
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret T' => True | TLabeled T' _ => True | TTainted T' _ => True
  | TSanitized T' _ => True
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList T' => True | TOption T' => True
  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type_fo T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type_fo T2 y1 y2)
  | TFn _ _ _ => True
  | TCapability _ | TCapabilityFull _ | TProof _ => True
  | TChan _ | TSecureChan _ _ => True
  | TConstantTime T' => True | TZeroizing T' => True
  end.
```

### first_order_type

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList T' => first_order_type T'
  | TOption T' => first_order_type T'
  | TRef T' _ => first_order_type T'
  | TSecret T' => first_order_type T'
  | TLabeled T' _ => first_order_type T'
  | TTainted T' _ => first_order_type T'
  | TSanitized T' _ => first_order_type T'
  | TProof T' => first_order_type T'
  | TCapability _ => true
  | TCapabilityFull _ => true
  | TChan _ => false
  | TSecureChan _ _ => false
  | TConstantTime T' => first_order_type T'
  | TZeroizing T' => first_order_type T'
  end.
```

### stores_agree_low_fo

```coq
Definition stores_agree_low_fo (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    first_order_type T = true ->
    is_low sl ->
    store_lookup l st1 = store_lookup l st2.
```

### store_wf

```coq
Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  (forall l T sl,
     store_ty_lookup l Σ = Some (T, sl) ->
     exists v, store_lookup l st = Some v /\ value v /\ has_type nil Σ Public v T EffectPure)
  /\
  (forall l v,
     store_lookup l st = Some v ->
     exists T sl, store_ty_lookup l Σ = Some (T, sl) /\ value v /\ has_type nil Σ Public v T EffectPure).
```

### store_ty_extends

```coq
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).
```

### Operational semantics (key reduction rules)

```
ST_RefValue:  value v -> (ERef v l, st, ctx) --> (ELoc (fresh_loc st), store_update (fresh_loc st) v st, ctx)
ST_DerefLoc:  store_lookup l st = Some v -> (EDeref (ELoc l), st, ctx) --> (v, st, ctx)
ST_AssignLoc: value v -> store_lookup l st = Some _ -> (EAssign (ELoc l) v, st, ctx) --> (EUnit, store_update l v st, ctx)
ST_Classify:  value v -> (EClassify v, st, ctx) --> (EClassify v, st, ctx)  [already a value]
ST_Declassify: value v -> (EDeclassify (EClassify v) p, st, ctx) --> (v, st, ctx)
```

### Unfolding lemmas (proven by reflexivity)

```coq
Lemma val_rel_n_0_unfold  : ... = (...). Proof. reflexivity. Qed.
Lemma val_rel_n_S_unfold  : ... = (...). Proof. reflexivity. Qed.
Lemma store_rel_n_0_unfold : ... = (store_max st1 = store_max st2). Proof. reflexivity. Qed.
Lemma store_rel_n_S_unfold : ... = (...). Proof. reflexivity. Qed.
```

### Helper lemmas available (already proven)

```coq
(* Extract properties from val_rel_n *)
Lemma val_rel_n_typing : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 -> has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure.

Lemma val_rel_n_closed : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 -> closed_expr v1 /\ closed_expr v2.

Lemma val_rel_n_value : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 -> value v1 /\ value v2.

(* Monotonicity *)
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n -> val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2.

Lemma store_rel_n_mono : forall m n Σ st1 st2,
  m <= n -> store_rel_n n Σ st1 st2 -> store_rel_n m Σ st1 st2.

Lemma val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' -> val_rel_n n Σ T v1 v2 -> val_rel_n n Σ' T v1 v2.
  (* NOTE: This may or may not exist — check before relying on it *)

(* Domain equality from store_rel_n *)
Lemma store_rel_n_0_domain : forall Σ st1 st2,
  store_rel_n 0 Σ st1 st2 -> store_max st1 = store_max st2.

(* Multi-step congruence lemmas *)
Lemma multi_step_ref : forall e1 e2 l st1 st2 ctx1 ctx2,
  (e1, st1, ctx1) -->* (e2, st2, ctx2) ->
  (ERef e1 l, st1, ctx1) -->* (ERef e2 l, st2, ctx2).

Lemma multi_step_deref : forall e1 e2 st1 st2 ctx1 ctx2,
  (e1, st1, ctx1) -->* (e2, st2, ctx2) ->
  (EDeref e1, st1, ctx1) -->* (EDeref e2, st2, ctx2).

Lemma multi_step_assign1 : forall e1 e1' e2 st1 st2 ctx1 ctx2,
  (e1, st1, ctx1) -->* (e1', st2, ctx2) ->
  (EAssign e1 e2, st1, ctx1) -->* (EAssign e1' e2, st2, ctx2).

Lemma multi_step_assign2 : forall v e2 e2' st1 st2 ctx1 ctx2,
  value v ->
  (e2, st1, ctx1) -->* (e2', st2, ctx2) ->
  (EAssign v e2, st1, ctx1) -->* (EAssign v e2', st2, ctx2).

Lemma multi_step_trans : forall cfg1 cfg2 cfg3,
  cfg1 -->* cfg2 -> cfg2 -->* cfg3 -> cfg1 -->* cfg3.

Lemma multi_step_classify : forall e1 e2 st1 st2 ctx1 ctx2,
  (e1, st1, ctx1) -->* (e2, st2, ctx2) ->
  (EClassify e1, st1, ctx1) -->* (EClassify e2, st2, ctx2).

Lemma multi_step_declassify : forall e1 e2 p st1 st2 ctx1 ctx2,
  (e1, st1, ctx1) -->* (e2, st2, ctx2) ->
  (EDeclassify e1 p, st1, ctx1) -->* (EDeclassify e2 p, st2, ctx2).
```

---

## HOW THE AXIOMS ARE INVOKED

In the `logical_relation` theorem (proven by induction on the typing derivation `has_type G Σ Public e T eps`), each axiom handles one typing rule case:

```coq
(* T_Ref case — the IH gives: IHHty : exp_rel Σ_base T (subst_rho rho1 e) (subst_rho rho2 e) *)
- simpl. unfold exp_rel. intro n.
  eapply logical_relation_ref.
  + eassumption.  (* has_type for e *)
  + exact Henv.
  + exact Hno1.
  + exact Hno2.

(* T_Deref case — IHHty : exp_rel Σ_base (TRef T l) (subst_rho rho1 e) (subst_rho rho2 e) *)
- simpl. unfold exp_rel. intro n.
  eapply logical_relation_deref.
  + eassumption.
  + exact Henv.
  + exact Hno1.
  + exact Hno2.

(* T_Assign case — IHHty1 : exp_rel ... (TRef T l) ..., IHHty2 : exp_rel ... T ... *)
- simpl. unfold exp_rel. intro n.
  eapply logical_relation_assign.
  + eassumption.
  + eassumption.
  + exact Henv.
  + exact Hno1.
  + exact Hno2.

(* T_Declassify case — IHHty : exp_rel ... (TSecret T) ... *)
- simpl. unfold exp_rel. intro n.
  eapply logical_relation_declassify.
  + eassumption.
  + exact Henv.
  + exact Hno1.
  + exact Hno2.
```

**CRITICAL:** When replacing an axiom with a lemma, you may ADD premises (like `exp_rel` for subexpressions), since the `logical_relation` proof has `IHHty` available from the induction hypothesis. Just update the usage site to pass the IH.

---

## KNOWN DIFFICULTIES AND FAILED APPROACHES

### 1. Removing `is_low_dec` from `store_rel_n`

**Tried:** Change `store_rel_n` to track `val_rel_n` for ALL locations (not just LOW ones).

**Failed because:** This changes the mutual fixpoint definition, which cascades through EVERY existing proof that pattern-matches on `store_rel_n`. The unfolding lemmas change, the monotonicity lemmas change, and ~4000 lines of existing proof scripts break.

### 2. `val_rel_at_type_fo` does NOT imply syntactic equality for wrapper types

**Key insight:** For types like `TList T'`, `TConstantTime T'`, `TZeroizing T'`, etc., `first_order_type` returns `true` (recursing into `T'`), but `val_rel_at_type_fo` returns `True` (not structural equality). So `val_rel_at_type_fo` does NOT imply `v1 = v2` for these types.

This means `stores_agree_low_fo` (which requires `store_lookup l st1 = store_lookup l st2` for LOW+FO locations) CANNOT be derived from `val_rel_at_type_fo` alone for wrapper FO types.

### 3. The `stores_agree_low_fo` invariant

`exp_rel_n` requires preserving `stores_agree_low_fo` through evaluation. For assignment to a LOW+FO location, you need to show the new values are syntactically equal. But the logical relation only guarantees `val_rel_n` (semantic relatedness), not syntactic equality, for these wrapper FO types.

---

## CONSTRAINTS

1. **NO `admit.`** — Every tactic proof must be complete
2. **NO `Admitted.`** — Every lemma/theorem must end with `Qed.`
3. **You may add new Axioms ONLY if they are strictly simpler/more justified than the ones being replaced** (e.g., splitting one axiom into smaller pieces is OK)
4. **You may modify the definitions** of `val_rel_n`, `store_rel_n`, `val_rel_at_type_fo`, `first_order_type`, `stores_agree_low_fo`, etc. **BUT** you must also fix all downstream proofs that break
5. **The final `non_interference_stmt` theorem must still be proven** (it's the top-level result)
6. **Rocq 9.1 compatibility:** Use `Stdlib` imports, be aware that `inversion; subst` may rename variables differently than older Coq versions
7. **The `change (NonInterference_v2.X) with (X)` tactic pattern** is used throughout the LR file. If you modify definitions in NI_v2.v, these `change` tactics may break under `make` (where .vo files create module-qualified names). Prefer `unfold`/`fold` over `change`.

---

## RECOMMENDED STRATEGY

### For `fundamental_theorem_step_0`:

At step 0, `val_rel_at_type` for `TFn T1 T2 eff` says: "for any related stores and related inputs, applying the function produces related outputs." But the outputs only need to satisfy `val_rel_n 0` and `store_rel_n 0` (since the section variables are instantiated with step-0 relations). `exp_rel_n 0` is `True`, so if the function application relation at step 0 just needs to produce ANY result (which `True` satisfies), this might be provable by case analysis on the type.

**Check:** Does `val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2` for `T = TFn T1 T2 eff` actually require producing witnesses? If the conclusion contains existentials, you need witnesses. If it's universally quantified, you need to handle all inputs.

### For ref/deref/assign:

The cleanest approach is to **add `exp_rel` premises** for subexpressions (available from the IH) and structure the proof as:

1. Use the IH to evaluate subexpressions to related values
2. For **ref**: Show `fresh_loc st1 = fresh_loc st2` (from `store_rel_n` domain equality), construct extended `Σ'`, prove `store_rel_n` for updated stores
3. For **deref**: Extract the value from `store_rel_n` (LOW case gives `val_rel_n`, HIGH case gives typing—but at Public pc both sides reduce the same way)
4. For **assign**: Use IH for both e1 (location) and e2 (value), update stores, prove `store_rel_n` preserved

**The main challenge** for all three is maintaining `stores_agree_low_fo` after store operations. Consider whether you can:
- Weaken `stores_agree_low_fo` to only require agreement on "truly first-order" types (exclude wrapper types)
- Or strengthen `val_rel_at_type_fo` to give syntactic equality for wrapper FO types
- Or restructure the proof to not need `stores_agree_low_fo` as a separate invariant

### For declassify:

This is genuinely a policy axiom. If you cannot prove it, document why and keep it as a justified axiom.

---

## DELIVERABLES

For each axiom you eliminate, provide:

1. **The replacement `Lemma` statement** (with any new premises)
2. **The complete proof** (compilable Coq/Rocq 9.1 code)
3. **The updated usage site** in the `logical_relation` proof
4. **Any helper lemmas** needed
5. **Any definition changes** and the cascade of fixes

If an axiom truly cannot be eliminated, explain precisely why and whether a weaker/simpler axiom could replace it.

---

## TYPE SYSTEM REFERENCE

```coq
Inductive ty : Type :=
  | TUnit | TBool | TInt | TString | TBytes
  | TFn : ty -> ty -> effect -> ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> security_level -> ty
  | TSecret : ty -> ty
  | TLabeled : ty -> security_level -> ty
  | TTainted : ty -> taint_source -> ty
  | TSanitized : ty -> sanitizer -> ty
  | TProof : ty -> ty
  | TCapability : capability_kind -> ty
  | TCapabilityFull : capability -> ty
  | TChan : session_type -> ty
  | TSecureChan : session_type -> security_level -> ty
  | TConstantTime : ty -> ty
  | TZeroizing : ty -> ty.

Inductive security_level : Type :=
  | LPublic | LInternal | LSession | LUser | LSystem | LSecret.
```

### Key typing rules (relevant to axioms):

```
T_Ref:    has_type G Σ pc e T ε  ->  has_type G Σ pc (ERef e l) (TRef T l) ε
T_Deref:  has_type G Σ pc e (TRef T l) ε  ->  has_type G Σ pc (EDeref e) T ε
T_Assign: has_type G Σ pc e1 (TRef T l) ε1  ->  has_type G Σ pc e2 T ε2  ->
          has_type G Σ pc (EAssign e1 e2) TUnit (effect_join ε1 ε2)
T_Classify:   has_type G Σ pc e T ε  ->  has_type G Σ pc (EClassify e) (TSecret T) ε
T_Declassify: has_type G Σ pc e (TSecret T) ε  ->  has_type G Σ pc (EDeclassify e p) T ε
```

---

## STORE OPERATIONS

```coq
Definition store := list (loc * expr).
Definition store_ty := list (loc * ty * security_level).

Fixpoint store_lookup (l : loc) (st : store) : option expr := ...
Fixpoint store_update (l : loc) (v : expr) (st : store) : store := ...
Fixpoint store_max (st : store) : loc := max of all locations in st.
Definition fresh_loc (st : store) : loc := S (store_max st).

Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * security_level) := ...
```
