# Package C: ReferenceOps - Reference Operation Properties

## Task

Prove properties about reference operations (allocation, lookup, update) for RIINA's memory model.

## Background

RIINA's store model uses:
- `store_max st`: The next available location (fresh location)
- `store_lookup l st`: Get value at location l
- `store_update l v st`: Update location l to value v
- `fresh_loc st = store_max st`: The fresh location is store_max

## Key Definitions

```coq
(* Store is a finite map from locations to values *)
Definition store := loc -> option expr.

(* Store typing maps locations to (type, security_level) *)
Definition store_typing := loc -> option (ty * security_level).

(* Fresh location is the maximum + 1 *)
Definition fresh_loc (st : store) : loc := store_max st.

(* Store lookup *)
Definition store_lookup (l : loc) (st : store) : option expr := st l.

(* Store typing lookup *)
Definition store_ty_lookup (l : loc) (Σ : store_typing) : option (ty * security_level) := Σ l.

(* Well-formed store: all locations < store_max have values *)
Definition store_well_formed (st : store) : Prop :=
  forall l, l < store_max st -> exists v, store_lookup l st = Some v.

(* Store typing well-formed: typed locations are < store_max *)
Definition store_ty_well_formed (Σ : store_typing) (st : store) : Prop :=
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) -> l < store_max st.
```

## Lemmas to Prove

### Lemma 1: fresh_loc_not_in_store

```coq
(* The fresh location is not in the current store *)
Lemma fresh_loc_not_in_store : forall st,
  store_well_formed st ->
  store_lookup (fresh_loc st) st = None.
Proof.
  (* fresh_loc st = store_max st, and store only has locations < store_max *)
Admitted.
```

**Proof Sketch**:
- fresh_loc st = store_max st by definition
- Well-formed store only has entries for l < store_max
- Therefore store_max has no entry

### Lemma 2: fresh_loc_not_in_typing

```coq
(* The fresh location is not in the store typing *)
Lemma fresh_loc_not_in_typing : forall Σ st,
  store_ty_well_formed Σ st ->
  store_ty_lookup (fresh_loc st) Σ = None.
Proof.
  (* Similar reasoning: fresh_loc >= store_max, typing only has l < store_max *)
Admitted.
```

### Lemma 3: store_update_preserves_other

```coq
(* Updating location l doesn't affect location l' ≠ l *)
Lemma store_update_preserves_other : forall st l l' v,
  l <> l' ->
  store_lookup l' (store_update l v st) = store_lookup l' st.
Proof.
  (* By definition of store_update as a function update *)
Admitted.
```

### Lemma 4: store_update_at_loc

```coq
(* Updating location l gives v at location l *)
Lemma store_update_at_loc : forall st l v,
  store_lookup l (store_update l v st) = Some v.
Proof.
  (* By definition of store_update *)
Admitted.
```

### Lemma 5: store_alloc_fresh

```coq
(* Allocation returns the fresh location *)
Lemma store_alloc_fresh : forall st v,
  fst (store_alloc v st) = fresh_loc st.
Proof.
  (* By definition of store_alloc *)
Admitted.
```

### Lemma 6: store_alloc_extends_max

```coq
(* Allocation increases store_max by 1 *)
Lemma store_alloc_extends_max : forall st v st',
  st' = snd (store_alloc v st) ->
  store_max st' = S (store_max st).
Proof.
  (* By definition of store_alloc *)
Admitted.
```

## For Store Relations

### Lemma 7: store_rel_n_same_fresh

```coq
(* Related stores have the same fresh location *)
Lemma store_rel_n_same_fresh : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  fresh_loc st1 = fresh_loc st2.
Proof.
  intros n Σ st1 st2 Hrel.
  unfold fresh_loc.
  (* store_rel_n requires store_max st1 = store_max st2 *)
  destruct n.
  - rewrite store_rel_n_0_unfold in Hrel. exact Hrel.
  - rewrite store_rel_n_S_unfold in Hrel.
    destruct Hrel as [_ [Hmax _]]. exact Hmax.
Qed.
```

### Lemma 8: store_rel_n_after_update

```coq
(* If stores are related and we update same location with related values,
   the resulting stores are related *)
Lemma store_rel_n_after_update : forall n Σ st1 st2 l v1 v2 T sl,
  store_rel_n n Σ st1 st2 ->
  store_ty_lookup l Σ = Some (T, sl) ->
  val_rel_n n Σ T v1 v2 ->
  store_rel_n n Σ (store_update l v1 st1) (store_update l v2 st2).
Proof.
  (* Induction on n, using store_rel_n definition *)
Admitted.
```

## Expected Output

Complete Coq proofs for all 8 lemmas, ending with `Qed.`

## Notes

- The exact definitions of store_update, store_alloc may vary in your codebase
- Check the actual definitions in foundations/Semantics.v
- Use `unfold` to expand definitions as needed
- Use `destruct` for case analysis on options
