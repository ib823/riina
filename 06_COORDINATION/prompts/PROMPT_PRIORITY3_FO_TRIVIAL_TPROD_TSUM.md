# DELEGATION PROMPT: Priority 3 - TProd/TSum in val_rel_at_type_fo_trivial

## OBJECTIVE
Fill the 2 admits at `NonInterference_v2.v:1351` and `1356` for TProd and TSum cases in `val_rel_at_type_fo_trivial`.

## CONTEXT

### The Problem
The lemma `val_rel_at_type_fo_trivial` says: for types where `fo_type_has_trivial_rel T = true`, any two values satisfy `val_rel_at_type_fo T v1 v2`. The base cases (TSecret, TList, TOption, etc.) are trivial because `val_rel_at_type_fo` returns `True`. But TProd and TSum require structural decomposition.

### Location
- **File:** `02_FORMAL/coq/properties/NonInterference_v2.v`
- **Lines:** 1351 (TProd), 1356 (TSum)
- **Function:** `val_rel_at_type_fo_trivial`

### Current Lemma State
```coq
Lemma val_rel_at_type_fo_trivial : forall T v1 v2,
  first_order_type T = true ->
  fo_type_has_trivial_rel T = true ->
  val_rel_at_type_fo T v1 v2.
Proof.
  intros T v1 v2 Hfo Htriv.
  destruct T; simpl in *; try congruence.
  - (* TProd T1 T2 - both must be trivial *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    apply Bool.andb_true_iff in Htriv. destruct Htriv as [Htr1 Htr2].
    (* For val_rel_at_type_fo at TProd, we need:
       exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\ ...
       But we don't know the structure of v1 and v2. *)
    admit.  (* LINE 1351 *)
  - (* TSum T1 T2 - both must be trivial *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    apply Bool.andb_true_iff in Htriv. destruct Htriv as [Htr1 Htr2].
    (* Same issue as TProd - we need structural info about v1, v2 *)
    admit.  (* LINE 1356 *)
  - (* TList *) exact I.
  - (* TOption *) exact I.
  (* ... other trivial cases ... *)
Admitted.
```

### The Issue

For TProd, `val_rel_at_type_fo` requires:
```coq
val_rel_at_type_fo (TProd T1 T2) v1 v2 =
  exists x1 y1 x2 y2,
    v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
    val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
```

For TSum, it requires:
```coq
val_rel_at_type_fo (TSum T1 T2) v1 v2 =
  (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type_fo T1 x1 x2) \/
  (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type_fo T2 y1 y2)
```

The lemma doesn't have typing information about v1 and v2, so we can't use canonical forms to decompose them.

## APPROACH

### Strategy 1: Add Typing Precondition

Change the lemma to require typing:
```coq
Lemma val_rel_at_type_fo_trivial : forall T Σ v1 v2,
  first_order_type T = true ->
  fo_type_has_trivial_rel T = true ->
  value v1 -> value v2 ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_at_type_fo T v1 v2.
```

With typing, we can use canonical forms to decompose pairs and sums.

### Strategy 2: Accept Semantic Limitation

The current lemma is used in `store_rel_n_step_up` for HIGH security FO types with trivial relations. For TProd/TSum with trivial components, the HIGH security case semantically means the data is not observable, so any relation holds.

We could add:
```coq
(* For HIGH security composite trivial types, the relation is semantically trivial
   because high data is not observable. We admit this as a justified semantic property. *)
```

### Strategy 3: Prove with Induction

Use induction on T with the IH:
```coq
Proof.
  intros T.
  induction T; intros v1 v2 Hfo Htriv; simpl in *; try congruence.
  - (* TProd *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    apply Bool.andb_true_iff in Htriv. destruct Htriv as [Htr1 Htr2].
    (* Need to show: exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\ ... *)
    (* Without typing, we can't decompose v1 and v2 *)
    (* But if T1 and T2 are both trivial, val_rel_at_type_fo T1/T2 is True *)
    (* So we need: v1 = EPair _ _ and v2 = EPair _ _ with True /\ True *)
    (* This still requires structural info about v1, v2 *)
```

## RECOMMENDED APPROACH

**Strategy 1 is recommended**: Add typing preconditions. This matches how the lemma is used in `store_rel_n_step_up` where we have `store_wf` providing typing for store values.

### Updated Lemma
```coq
Lemma val_rel_at_type_fo_trivial : forall T Σ v1 v2,
  first_order_type T = true ->
  fo_type_has_trivial_rel T = true ->
  value v1 -> value v2 ->
  has_type nil Σ Public v1 T EffectPure ->
  has_type nil Σ Public v2 T EffectPure ->
  val_rel_at_type_fo T v1 v2.
Proof.
  intros T.
  induction T; intros Σ v1 v2 Hfo Htriv Hval1 Hval2 Hty1 Hty2;
    simpl in *; try congruence.
  - (* TProd T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    apply Bool.andb_true_iff in Htriv. destruct Htriv as [Htr1 Htr2].
    (* Use canonical_forms_prod *)
    destruct (canonical_forms_prod nil Σ Public v1 T1 T2 EffectPure Hval1 Hty1)
      as [x1 [y1 [Heq1 [Hvx1 Hvy1]]]].
    destruct (canonical_forms_prod nil Σ Public v2 T1 T2 EffectPure Hval2 Hty2)
      as [x2 [y2 [Heq2 [Hvx2 Hvy2]]]].
    subst v1 v2.
    (* Get typing for components via inversion *)
    inversion Hty1; subst.
    inversion Hty2; subst.
    exists x1, y1, x2, y2.
    repeat split; try reflexivity.
    + (* val_rel_at_type_fo T1 x1 x2 *)
      apply IHT1 with Σ; try assumption.
      * eapply value_has_pure_effect; eassumption.
      * eapply value_has_pure_effect; eassumption.
    + (* val_rel_at_type_fo T2 y1 y2 *)
      apply IHT2 with Σ; try assumption.
      * eapply value_has_pure_effect; eassumption.
      * eapply value_has_pure_effect; eassumption.
  - (* TSum T1 T2 - similar structure *)
    (* ... *)
  - (* TList *) exact I.
  (* ... *)
Qed.
```

### Update Call Site

In `store_rel_n_step_up` around line 1424, update the call:
```coq
(* OLD *)
apply val_rel_at_type_fo_trivial; assumption.

(* NEW *)
apply val_rel_at_type_fo_trivial with Σ; try assumption.
(* Add value and typing hypotheses *)
```

## DELIVERABLE

1. **Updated `val_rel_at_type_fo_trivial` lemma** with typing preconditions and complete proof
2. **Updated call site** in `store_rel_n_step_up` (around line 1424)
3. If the call site changes are complex, provide the complete updated proof for `store_rel_n_step_up`

## CONSTRAINTS

- Keep the same semantic meaning (trivial types have trivial relations)
- Use canonical forms for structural decomposition
- Use value_has_pure_effect for effect normalization
- Do NOT add new axioms

## REFERENCE FILES
- `02_FORMAL/coq/properties/NonInterference_v2.v` (lines 1337-1368, 1379-1466)
- `02_FORMAL/coq/foundations/Typing.v` (canonical_forms_prod, canonical_forms_sum)
- `02_FORMAL/coq/type_system/Preservation.v` (value_has_pure_effect)
