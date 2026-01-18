# ULTIMATE AXIOM ELIMINATION PROMPT FOR RIINA

## CRITICAL: DO NOT ASSUME ANYTHING - USE ONLY EXACT DEFINITIONS PROVIDED

---

## TASK: Prove the 17 remaining axioms in NonInterference.v

You must provide **complete Coq proofs** for each axiom. Do not invent infrastructure - use ONLY what is provided.

---

## EXACT DEFINITIONS FROM THE CODEBASE

### 1. Store Typing Extension (EXACT)
```coq
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).
```

### 2. val_rel_n (Step-Indexed Value Relation) - EXACT
```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      val_rel_n n' Σ T v1 v2 /\  (* Cumulative *)
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end
with store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      store_rel_n n' Σ st1 st2 /\  (* Cumulative *)
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          val_rel_n n' Σ T v1 v2)
  end.
```

### 3. val_rel_at_type for TFn (WITH KRIPKE SEMANTICS) - EXACT
```coq
| TFn T1 T2 eff =>
    forall Σ', store_ty_extends Σ Σ' ->
      forall x y,
        value x -> value y -> closed_expr x -> closed_expr y ->
        val_rel_lower Σ' T1 x y ->  (* Arguments at EXTENDED store Σ' *)
        forall st1 st2 ctx,
          store_rel_pred Σ' st1 st2 ->  (* Store relation at EXTENDED store Σ' *)
          exists (v1' : expr) (v2' : expr) (st1' : store) (st2' : store)
                 (ctx' : effect_ctx) (Σ'' : store_ty),
            store_ty_extends Σ' Σ'' /\
            (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
            (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
            val_rel_lower Σ'' T2 v1' v2' /\
            store_rel_lower Σ'' st1' st2'
```

### 4. val_rel (Infinite/Limit Relation) - EXACT
```coq
Definition val_rel (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  forall n, val_rel_n n Σ T v1 v2.
```

---

## AVAILABLE PROVEN LEMMAS (USE THESE)

```coq
(* Already proven - you can use these *)
Lemma val_rel_n_mono : forall n m Σ T v1 v2,
  m <= n -> val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2.

Lemma store_rel_n_mono : forall n m Σ st1 st2,
  m <= n -> store_rel_n n Σ st1 st2 -> store_rel_n m Σ st1 st2.

Lemma val_rel_n_mono_store : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' -> val_rel_n n Σ T v1 v2 -> val_rel_n n Σ' T v1 v2.

Lemma val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' -> val_rel_n n Σ' T v1 v2 -> val_rel_n n Σ T v1 v2.
  (* Partial proof - has admits *)

Lemma store_ty_extends_trans_early : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 -> store_ty_extends Σ2 Σ3 -> store_ty_extends Σ1 Σ3.

Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.

Lemma val_rel_at_type_mono_store : forall T Σ Σ' sp vl sl v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_at_type Σ sp vl sl T v1 v2 ->
  val_rel_at_type Σ' sp vl sl T v1 v2.

Lemma first_order_decidable : forall T,
  {first_order_type T = true} + {first_order_type T = false}.

Lemma ty_size_induction : forall P : ty -> Type,
  (forall T, (forall T', ty_size T' < ty_size T -> P T') -> P T) ->
  forall T, P T.
```

---

## THE 17 AXIOMS TO PROVE

### Category A: Step Conversion (3 axioms)

**Axiom 1: val_rel_n_to_val_rel**
```coq
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```
- SEMANTICS: If values are related at some step, they are related at all steps
- HINT: Use cumulative structure - val_rel_n (S n) contains val_rel_n n

**Axiom 2: val_rel_n_step_up**
```coq
Axiom val_rel_n_step_up : forall n Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n (S n) Σ T v1 v2.
```
- SEMANTICS: Values related at step n are related at step (S n)
- KEY: Need to show val_rel_at_type at step n holds
- WARNING: For TFn at n=0, predicates are (fun _ => True), so need termination

**Axiom 3: store_rel_n_step_up**
```coq
Axiom store_rel_n_step_up : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_rel_n (S n) Σ st1 st2.
```
- SEMANTICS: Store relation steps up
- HINT: Requires val_rel_n_step_up for stored values

---

### Category B: Step-1 Termination (7 axioms)

These axioms state that certain elimination forms terminate in 1 step when given related values.

**Axiom 4-10: exp_rel_step1_X** (X = fst, snd, case, if, let, handle, app)

Example (fst):
```coq
Axiom exp_rel_step1_fst : forall Σ T1 v v' st1 st2 ctx Σ',
  store_ty_extends Σ Σ' ->
  val_rel_n 1 Σ' (TProd T1 T2) v v' ->
  store_rel_n 1 Σ' st1 st2 ->
  exists v1' v2' st1' st2' ctx' Σ'',
    store_ty_extends Σ' Σ'' /\
    (EFst v, st1, ctx) -->* (v1', st1', ctx') /\
    (EFst v', st2, ctx) -->* (v2', st2', ctx') /\
    val_rel_n 1 Σ'' T1 v1' v2' /\
    store_rel_n 1 Σ'' st1' st2'.
```
- SEMANTICS: Elimination of products/sums/etc preserves relation
- KEY: These are the "stepping" lemmas used in the fundamental theorem

---

### Category C: Application Completeness (1 axiom)

**Axiom 11: tapp_step0_complete**
```coq
Axiom tapp_step0_complete : forall Σ' Σ''' T2
  (v1 v2 arg1 arg2 res1 res2 : expr) (st1 st2 st1' st2' : store)
  (ctx ctx' : effect_ctx),
  (* various premises about stepping and relations *)
  val_rel_n 0 Σ''' T2 res1 res2.
```
- This is trivially True since val_rel_n 0 = True

---

### Category D: Higher-Order Helpers (2 axioms)

**Axiom 12: val_rel_n_lam_cumulative**
```coq
Axiom val_rel_n_lam_cumulative : forall n Σ T1 T2 ε x body1 body2,
  val_rel_n n Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2) ->
  val_rel_n (S n) Σ (TFn T1 T2 ε) (ELam x T1 body1) (ELam x T1 body2).
```
- SEMANTICS: Lambda relatedness steps up
- HINT: Related to val_rel_n_step_up specialized for lambdas

**Axiom 13: val_rel_at_type_to_val_rel_ho**
```coq
Axiom val_rel_at_type_to_val_rel_ho : forall Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2,
  val_rel_at_type Σ store_rel_lower val_rel_lower store_rel_any T arg1 arg2 ->
  value arg1 -> value arg2 ->
  val_rel Σ T arg1 arg2.
```
- SEMANTICS: Structural relation implies infinite relation
- WARNING: This is STRONG - needs careful proof using type structure

---

### Category E: Reference Operations (4 axioms)

**Axiom 14-17: logical_relation_X** (X = ref, deref, assign, declassify)

Example (ref):
```coq
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  (* If e is in the logical relation, then ref e is too *)
  exp_rel_n n Σ Γ Δ e T ε rho1 rho2 ->
  exp_rel_n n Σ Γ Δ (ERef e l) (TRef T l) (ε_union ε ε_alloc) rho1 rho2.
```
- SEMANTICS: Reference operations preserve the logical relation
- KEY: These extend the store typing when allocating

---

## OUTPUT FORMAT

For EACH axiom, provide:

1. **The complete Coq proof** starting with `Proof.` and ending with `Qed.`
2. **Brief explanation** of the proof strategy (1-2 sentences)
3. **Any required helper lemmas** with their complete proofs

Example:
```coq
(* Axiom 11: tapp_step0_complete - trivially true *)
Lemma tapp_step0_complete_proof : forall Σ' Σ''' T2 v1 v2 arg1 arg2 res1 res2 st1 st2 st1' st2' ctx ctx',
  val_rel_n 0 Σ''' T2 res1 res2.
Proof.
  intros. simpl. exact I.
Qed.
(* Strategy: val_rel_n 0 = True by definition *)
```

---

## CONSTRAINTS

1. **NO new axioms** - prove everything from definitions
2. **NO assumptions** - if something is missing, state it explicitly
3. **MUST compile** - test each proof in Coq
4. **USE EXACT NAMES** - val_rel_n not val_rel_le, store_rel_n not store_rel_le

---

## PRIORITY ORDER

1. **tapp_step0_complete** (trivial)
2. **store_rel_n_step_up** (depends on val_rel_n_step_up)
3. **val_rel_n_step_up** (core step-up lemma)
4. **val_rel_n_to_val_rel** (uses step-up)
5. **val_rel_n_lam_cumulative** (specialized step-up)
6. **exp_rel_step1_X** (7 axioms, pattern similar)
7. **val_rel_at_type_to_val_rel_ho** (complex)
8. **logical_relation_X** (4 axioms, need store extension)

---

## BEGIN PROOFS NOW

Start with the trivial axiom (tapp_step0_complete), then proceed in priority order.
