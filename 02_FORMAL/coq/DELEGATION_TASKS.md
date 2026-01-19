# DELEGATION TASKS FOR CLAUDE AI (WEB)

## TASK 1: exp_rel_step1_fst

**Insert this in Section 5 of CLAUDE_AI_DELEGATION_PROMPT.md:**

```
Prove exp_rel_step1_fst: when two pairs are related at base level (first-order),
projecting the first component produces related results.

Use val_rel_n_base_prod_fo to extract pair structure, then apply ST_Fst.

Theorem exp_rel_step1_fst : forall Sigma T1 T2 v v' st1 st2 ctx,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Sigma (TProd T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (EFst v, st1, ctx) -->* (r1, st1', ctx') /\
    (EFst v', st2, ctx) -->* (r2, st2', ctx').

Follow the template from exp_rel_step1_if. Output complete proof with Qed.
```

---

## TASK 2: exp_rel_step1_snd

**Insert this in Section 5:**

```
Prove exp_rel_step1_snd: when two pairs are related at base level (first-order),
projecting the second component produces related results.

Use val_rel_n_base_prod_fo to extract pair structure, then apply ST_Snd.

Theorem exp_rel_step1_snd : forall Sigma T1 T2 v v' st1 st2 ctx,
  first_order_type (TProd T1 T2) = true ->
  val_rel_n_base Sigma (TProd T1 T2) v v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists r1 r2 st1' st2' ctx',
    (ESnd v, st1, ctx) -->* (r1, st1', ctx') /\
    (ESnd v', st2, ctx) -->* (r2, st2', ctx').

Follow the template from exp_rel_step1_if. Output complete proof with Qed.
```

---

## TASK 3: val_rel_n_base_int (Extraction Lemma)

**Insert this in Section 5:**

```
Prove val_rel_n_base_int: extract the SAME integer from related values at TInt.

Lemma val_rel_n_base_int : forall Sigma v1 v2,
  val_rel_n_base Sigma TInt v1 v2 ->
  exists i, v1 = EInt i /\ v2 = EInt i.

Follow the template from val_rel_n_base_bool. The proof is nearly identical
since first_order_type TInt = true.
```

---

## TASK 4: val_rel_n_base_unit (Extraction Lemma)

**Insert this in Section 5:**

```
Prove val_rel_n_base_unit: extract EUnit from related values at TUnit.

Lemma val_rel_n_base_unit : forall Sigma v1 v2,
  val_rel_n_base Sigma TUnit v1 v2 ->
  v1 = EUnit /\ v2 = EUnit.

Follow the template from val_rel_n_base_bool. The proof extracts from
val_rel_at_type_fo TUnit which gives v1 = EUnit /\ v2 = EUnit directly.
```

---

## TASK 5: val_rel_n_base_ref (Extraction Lemma)

**Insert this in Section 5:**

```
Prove val_rel_n_base_ref: extract SAME location from related reference values.

Lemma val_rel_n_base_ref : forall Sigma T sl v1 v2,
  first_order_type (TRef T sl) = true ->
  val_rel_n_base Sigma (TRef T sl) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l.

This extracts from val_rel_at_type_fo (TRef T sl) which gives
exists l, v1 = ELoc l /\ v2 = ELoc l.
```

---

## INTEGRATION INSTRUCTIONS

After receiving proofs from Claude AI (web):

1. **Create new file**: `02_FORMAL/coq/properties/BaseExtractionLemmas.v`

2. **Add the proofs** with proper imports:
```coq
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.properties.NonInterference_v3.
```

3. **Verify compilation**: `make`

4. **Commit**: `git commit -m "[TRACK_A] PROOF: Add extraction lemmas from delegation"`

---

## EXPECTED OUTPUT FROM EACH TASK

Each task should produce:
- Complete lemma/theorem statement
- Full proof with all tactics
- Ending with `Qed.` (NOT `Admitted.`)
- No placeholders or `...`

---

## PRIORITY ORDER

1. **Task 1 & 2** (exp_rel_step1_fst/snd) - Direct axiom elimination
2. **Task 3-5** (extraction lemmas) - Infrastructure for future proofs

**Total Impact**: 2 axioms eliminated + 3 infrastructure lemmas
