# Package B: MasterTheorem Composition Lemmas

## Task

Prove composition lemmas in MasterTheorem.v that build the final non-interference theorem.

## Background

MasterTheorem.v composes all the component proofs into the main security theorem. The admits are typically about:
1. Composing value relations
2. Handling store extensions
3. Multi-step evaluation preservation

## Key Structure

```coq
(* The main theorem structure *)
Theorem non_interference : forall Γ Σ e T ε,
  has_type Γ Σ Public e T ε ->
  forall rho1 rho2 st1 st2,
    env_rel Γ Σ rho1 rho2 ->
    store_rel Σ st1 st2 ->
    exp_rel Σ T (subst_rho rho1 e) (subst_rho rho2 e).

(* Where exp_rel is the "infinite" relation *)
Definition exp_rel Σ T e1 e2 :=
  forall n, exp_rel_n n Σ T e1 e2.

(* And val_rel similarly *)
Definition val_rel Σ T v1 v2 :=
  forall n, val_rel_n n Σ T v1 v2.
```

## Lemmas to Prove

### Lemma 1: exp_rel_from_step_indexed

```coq
(* If related at all steps, then related *)
Lemma exp_rel_from_step_indexed : forall Σ T e1 e2,
  (forall n, exp_rel_n n Σ T e1 e2) ->
  exp_rel Σ T e1 e2.
Proof.
  intros Σ T e1 e2 Hall.
  unfold exp_rel.
  exact Hall.
Qed.
```

### Lemma 2: val_rel_from_step_indexed

```coq
Lemma val_rel_from_step_indexed : forall Σ T v1 v2,
  (forall n, val_rel_n n Σ T v1 v2) ->
  val_rel Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hall.
  unfold val_rel.
  exact Hall.
Qed.
```

### Lemma 3: exp_rel_n_step_down

```coq
(* If related at step n, related at any step m ≤ n *)
Lemma exp_rel_n_step_down : forall n m Σ T e1 e2,
  m <= n ->
  exp_rel_n n Σ T e1 e2 ->
  exp_rel_n m Σ T e1 e2.
Proof.
  (* Induction on n, using the step-down property of the definition *)
Admitted.
```

### Lemma 4: val_rel_n_step_down

```coq
Lemma val_rel_n_step_down : forall n m Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  (* Similar to exp_rel_n_step_down *)
Admitted.
```

### Lemma 5: store_rel_n_step_down

```coq
Lemma store_rel_n_step_down : forall n m Σ st1 st2,
  m <= n ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n m Σ st1 st2.
Proof.
  (* Induction on n *)
Admitted.
```

### Lemma 6: exp_rel_n_bind (Monadic Composition)

```coq
(* If e1, e2 are related, and f preserves relation, then (bind e f) is related *)
Lemma exp_rel_n_bind : forall n Σ T1 T2 e1 e2 f1 f2,
  exp_rel_n n Σ T1 e1 e2 ->
  (forall v1 v2 Σ',
    store_ty_extends Σ Σ' ->
    val_rel_n n Σ' T1 v1 v2 ->
    exp_rel_n n Σ' T2 (f1 v1) (f2 v2)) ->
  exp_rel_n n Σ T2 (bind e1 f1) (bind e2 f2).
Proof.
  (* This depends on how bind is defined in your semantics *)
Admitted.
```

### Lemma 7: env_rel_extends

```coq
(* Environment relation is preserved under store extension *)
Lemma env_rel_extends : forall Γ Σ Σ' rho1 rho2,
  store_ty_extends Σ Σ' ->
  env_rel Γ Σ rho1 rho2 ->
  env_rel Γ Σ' rho1 rho2.
Proof.
  (* env_rel is defined in terms of val_rel, use Kripke monotonicity *)
Admitted.
```

### Lemma 8: fundamental_lemma_composition

```coq
(* Composing the fundamental lemma for sequential expressions *)
Lemma fundamental_lemma_composition : forall Γ Σ e1 e2 T1 T2 ε1 ε2 x,
  has_type Γ Σ Public e1 T1 ε1 ->
  has_type ((x, T1) :: Γ) Σ Public e2 T2 ε2 ->
  (forall rho1 rho2 n,
    env_rel Γ Σ rho1 rho2 ->
    exp_rel_n n Σ T1 (subst_rho rho1 e1) (subst_rho rho2 e1)) ->
  (forall rho1 rho2 n v1 v2,
    env_rel ((x, T1) :: Γ) Σ rho1 rho2 ->
    val_rel_n n Σ T1 v1 v2 ->
    exp_rel_n n Σ T2 (subst_rho (extend rho1 x v1) e2)
                     (subst_rho (extend rho2 x v2) e2)) ->
  forall rho1 rho2 n,
    env_rel Γ Σ rho1 rho2 ->
    exp_rel_n n Σ T2 (subst_rho rho1 (ELet x e1 e2))
                     (subst_rho rho2 (ELet x e1 e2)).
Proof.
  (* Use exp_rel_n_bind or direct construction *)
Admitted.
```

### Lemma 9: multi_step_preserves_rel

```coq
(* Multi-step evaluation preserves expression relation *)
Lemma multi_step_preserves_rel : forall n Σ T e1 e2 e1' e2' st1 st2 st1' st2' ctx ctx',
  exp_rel_n n Σ T e1 e2 ->
  (e1, st1, ctx) -->* (e1', st1', ctx') ->
  (e2, st2, ctx) -->* (e2', st2', ctx') ->
  store_rel_n n Σ st1 st2 ->
  exists Σ',
    store_ty_extends Σ Σ' /\
    exp_rel_n n Σ' T e1' e2' /\
    store_rel_n n Σ' st1' st2'.
Proof.
  (* This is the key preservation lemma - may be quite complex *)
Admitted.
```

## Proof Strategy

For step-down lemmas:
1. Induction on n
2. For S n case, use the definition which includes the n case

For composition lemmas:
1. Use the definitions of exp_rel_n and val_rel_n
2. Apply Kripke monotonicity for store extensions
3. Use the fundamental lemma induction hypothesis

## Expected Output

Proofs for:
1. exp_rel_from_step_indexed - PROVEN
2. val_rel_from_step_indexed - PROVEN
3. exp_rel_n_step_down - PROVEN
4. val_rel_n_step_down - PROVEN
5. store_rel_n_step_down - PROVEN

The more complex composition lemmas (6-9) may need Admitted with detailed notes on what's needed.

## Notes

These lemmas build on each other:
- Step-down lemmas are foundational
- env_rel_extends needs Kripke monotonicity
- fundamental_lemma_composition needs all of the above
- multi_step_preserves_rel is the culmination

Focus on the simpler lemmas first to establish the foundation.
