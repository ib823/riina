# Exact Context for Each Admit

## properties/FundamentalTheorem.v

### Line 424: compat_pair
```coq
Lemma compat_pair : forall n Σ T1 T2 e1 e1' e2 e2',
  exp_rel_le n Σ T1 e1 e1' ->
  exp_rel_le n Σ T2 e2 e2' ->
  exp_rel_le n Σ (TProd T1 T2) (EPair e1 e2) (EPair e1' e2').
Proof.
  intros n Σ T1 T2 e1 e1' e2 e2' Hrel1 Hrel2.
  unfold exp_rel_le in *.
  intros k v1 v2 st1 st2 ctx Hk Heval1 Heval2 Hst.
  (* Need: invert pair evaluation, apply IH, reconstruct *)
Admitted.
```

### Line 465: compat_fst
```coq
Lemma compat_fst : forall n Σ T1 T2 e e',
  exp_rel_le n Σ (TProd T1 T2) e e' ->
  exp_rel_le n Σ T1 (EFst e) (EFst e').
Proof.
  intros n Σ T1 T2 e e' Hrel.
  unfold exp_rel_le in *.
  intros k v1 v2 st1 st2 ctx Hk Heval1 Heval2 Hst.
  (* Need: invert fst evaluation, get pair, extract first component *)
Admitted.
```

## properties/AxiomEliminationVerified.v

### Line 174: exp_rel_step1_app_typed (KEY LEMMA)
```coq
Lemma exp_rel_step1_app_typed : forall Γ Σ Σ' T1 T2 ε_fn ε f f' a a' st1 st2 ctx,
  has_type Γ Σ Public f (TFn T1 T2 ε_fn) ε ->
  has_type Γ Σ Public a T1 ε ->
  value f -> value f' -> value a -> value a' ->
  val_rel_n 1 Σ (TFn T1 T2 ε_fn) f f' ->
  val_rel_n 1 Σ T1 a a' ->
  store_rel_n 1 Σ st1 st2 ->
  store_ty_extends Σ Σ' ->
  exp_rel_le 1 Σ' T2 (EApp f a) (EApp f' a').
Proof.
  intros Γ Σ Σ' T1 T2 ε_fn ε f f' a a' st1 st2 ctx
         Hty_f Hty_a Hval_f Hval_f' Hval_a Hval_a' Hrel_f Hrel_a Hst Hext.
  (* This is the beta reduction case - apply function to argument *)
  (* f must be ELam, apply substitution *)
Admitted.
```

## Key Patterns

### Pattern: exp_rel_le proofs
```coq
(* Standard structure for exp_rel_le proofs *)
unfold exp_rel_le.
intros k v1 v2 st1 st2 ctx Hk Heval1 Heval2 Hst.
(* k is remaining steps, Heval1/2 are evaluations, Hst is store relation *)
(* Typically: *)
(* 1. Invert evaluations to get subterm evaluations *)
(* 2. Apply IH with reduced step count *)
(* 3. Use val_rel_le properties to conclude *)
```

### Pattern: val_rel_n construction
```coq
(* For step n > 0 *)
simpl. (* Unfolds to (val_rel_le (n-1) ...) /\ val_rel_struct ... *)
split.
- (* Cumulative part: use val_rel_le_monotone or IH *)
- (* Structural part: case on type, build relation *)
```

### Pattern: Store relation
```coq
(* store_rel_le n Σ st1 st2 means:
   - Same domain
   - Each location l : T in Σ has val_rel_le n Σ T (st1 l) (st2 l) *)
```
