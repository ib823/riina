# Package D: NonInterferenceZero - Zero-Step Base Cases

## Task

Prove the zero-step base case lemmas for the step-indexed logical relation in RIINA.

## Background

In RIINA's v2 semantics, val_rel_n 0 is NOT trivially True. It requires:
- Both expressions are values
- Both expressions are closed
- For first-order types: structural equality (val_rel_at_type_fo)

## Key Definitions

```coq
(* The v2 definition of val_rel_n 0 *)
Lemma val_rel_n_0_unfold : forall Σ T v1 v2,
  val_rel_n 0 Σ T v1 v2 =
  (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T then val_rel_at_type_fo T v1 v2 else True)).

(* First-order type check *)
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList T' | TOption T' | TRef T' _ => first_order_type T'
  | TSecret T' | TLabeled T' _ | TTainted T' _ => first_order_type T'
  | TFn _ _ _ => false  (* Functions are higher-order *)
  | _ => true
  end.

(* val_rel_at_type_fo for common types *)
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TSecret _ => True  (* Secrets are indistinguishable *)
  | TProd T1 T2 =>
      exists x1 y1 x2 y2,
        v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | _ => True
  end.
```

## Lemmas to Prove

### Lemma 1: val_rel_n_0_from_typed_values

```coq
(* If two values have the same type and satisfy structural equality,
   they are related at step 0 *)
Lemma val_rel_n_0_from_typed_values : forall Σ T v1 v2,
  value v1 -> value v2 ->
  closed_expr v1 -> closed_expr v2 ->
  val_rel_at_type_fo T v1 v2 ->
  first_order_type T = true ->
  val_rel_n 0 Σ T v1 v2.
Proof.
  intros Σ T v1 v2 Hv1 Hv2 Hc1 Hc2 Hrel Hfo.
  rewrite val_rel_n_0_unfold.
  repeat split; try assumption.
  rewrite Hfo. exact Hrel.
Qed.
```

### Lemma 2: val_rel_n_0_unit

```coq
Lemma val_rel_n_0_unit : forall Σ,
  val_rel_n 0 Σ TUnit EUnit EUnit.
Proof.
  intros Σ.
  rewrite val_rel_n_0_unfold.
  repeat split.
  - (* value EUnit *) constructor.
  - (* value EUnit *) constructor.
  - (* closed_expr EUnit *) intros x Hfree. inversion Hfree.
  - (* closed_expr EUnit *) intros x Hfree. inversion Hfree.
  - (* first_order_type TUnit = true, so need val_rel_at_type_fo *)
    simpl. split; reflexivity.
Qed.
```

### Lemma 3: val_rel_n_0_bool

```coq
Lemma val_rel_n_0_bool : forall Σ b,
  val_rel_n 0 Σ TBool (EBool b) (EBool b).
Proof.
  intros Σ b.
  rewrite val_rel_n_0_unfold.
  repeat split.
  - constructor.
  - constructor.
  - intros x Hfree. inversion Hfree.
  - intros x Hfree. inversion Hfree.
  - simpl. exists b. split; reflexivity.
Qed.
```

### Lemma 4: val_rel_n_0_int

```coq
Lemma val_rel_n_0_int : forall Σ i,
  val_rel_n 0 Σ TInt (EInt i) (EInt i).
Proof.
  (* Similar to val_rel_n_0_bool *)
Admitted.
```

### Lemma 5: val_rel_n_0_loc (for references)

```coq
Lemma val_rel_n_0_loc : forall Σ T sl l,
  store_ty_lookup l Σ = Some (T, sl) ->
  val_rel_n 0 Σ (TRef T sl) (ELoc l) (ELoc l).
Proof.
  intros Σ T sl l Hlookup.
  rewrite val_rel_n_0_unfold.
  repeat split.
  - constructor.  (* value (ELoc l) *)
  - constructor.
  - intros x Hfree. inversion Hfree.  (* closed *)
  - intros x Hfree. inversion Hfree.
  - (* val_rel_at_type_fo (TRef T sl) *)
    simpl. exists l. split; reflexivity.
Qed.
```

## Proof Pattern

For each base type:
1. Rewrite with val_rel_n_0_unfold
2. Use `repeat split` to break conjunction
3. Prove `value` using constructor
4. Prove `closed_expr` by showing no free variables
5. For the type-specific part:
   - Check if first_order_type T = true
   - If yes, prove val_rel_at_type_fo T v1 v2
   - If no (higher-order), prove True

## Expected Output

Complete Coq proofs for:
1. val_rel_n_0_from_typed_values
2. val_rel_n_0_unit
3. val_rel_n_0_bool
4. val_rel_n_0_int
5. val_rel_n_0_loc

All ending with `Qed.`
