# Claude.ai Research Task - Phase 7C: First-Order Store Weakening

## CRITICAL CONTEXT

This lemma is used by `combined_properties_first_order` to establish the base case for the master_theorem induction. Currently admitted.

## The Problem

```coq
Lemma val_rel_le_store_weaken_fo : forall T,
  first_order_type T = true ->
  forall n Σ Σ' v1 v2,
    store_ty_extends Σ Σ' ->
    val_rel_le n Σ' T v1 v2 ->
    val_rel_le n Σ T v1 v2.
```

**Key Insight**: First-order types don't use Kripke quantification in their structural part. The val_rel_struct for first-order types only checks syntactic equality (same values), not store contents.

## First-Order Type Definition

```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false  (* Functions are higher-order *)
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

## val_rel_struct for First-Order Types

Looking at CumulativeRelation.v, the structural part for first-order types:

```coq
Definition val_rel_struct (val_rel_prev : store_ty -> ty -> expr -> expr -> Prop)
                          (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  match T with
  (* Primitive types - NO store dependency *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2

  (* Security types - NO store dependency (just True) *)
  | TSecret _ => True
  | TLabeled _ _ => True
  | TTainted _ _ => True
  | TSanitized _ _ => True
  | TCapability _ => True
  | TCapabilityFull _ => True
  | TProof _ => True
  | TConstantTime _ => True
  | TZeroizing _ => True

  (* Reference types - NO store dependency (just location equality) *)
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l

  (* Compound types - recursive on val_rel_prev, but NO direct Σ usage *)
  | TProd T1 T2 =>
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_prev Σ T1 a1 a2 /\
        val_rel_prev Σ T2 b1 b2
  | TSum T1 T2 =>
      (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_prev Σ T1 a1 a2) \/
      (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_prev Σ T2 b1 b2)

  (* TFn - HAS store dependency (Kripke quantification) - NOT first-order *)
  | TFn T1 T2 eff => forall Σ', store_ty_extends Σ Σ' -> ...
  ...
  end.
```

## Key Observation

For first-order types:
1. **Primitive types** (TUnit, TBool, TInt, TString, TBytes): structural part is just value equality, NO Σ usage
2. **Security/capability types**: structural part is `True`, NO Σ usage
3. **TRef**: structural part is location equality, NO Σ usage
4. **Compound types** (TProd, TSum): recursive calls to val_rel_prev with Σ, but for first-order components these recursively don't use Σ either

**Therefore**: For first-order T, `val_rel_struct (val_rel_le n') Σ T v1 v2` is equivalent to `val_rel_struct (val_rel_le n') Σ' T v1 v2` for any Σ, Σ'.

## Proof Strategy

### Approach 1: Direct Induction on T

```coq
Lemma val_rel_le_store_weaken_fo : forall T,
  first_order_type T = true ->
  forall n Σ Σ' v1 v2,
    store_ty_extends Σ Σ' ->
    val_rel_le n Σ' T v1 v2 ->
    val_rel_le n Σ T v1 v2.
Proof.
  intros T.
  induction T; intros Hfo n Σ Σ' v1 v2 Hext Hrel; simpl in Hfo; try discriminate.

  - (* TUnit *)
    (* val_rel_struct for TUnit doesn't use Σ at all *)
    induction n; [simpl; trivial|].
    simpl in Hrel |- *. destruct Hrel as [Hcum Hstruct].
    split.
    + apply IHn; assumption.
    + unfold val_rel_struct in Hstruct |- *.
      (* Structural part: value, closed, v1=EUnit, v2=EUnit - no Σ dependency *)
      exact Hstruct.

  - (* TBool *) [similar]
  - (* TInt *) [similar]
  - (* TString *) [similar]
  - (* TBytes *) [similar]

  - (* TProd T1 T2 *)
    apply Bool.andb_true_iff in Hfo. destruct Hfo as [Hfo1 Hfo2].
    induction n; [simpl; trivial|].
    simpl in Hrel |- *. destruct Hrel as [Hcum Hstruct].
    split.
    + apply IHn; assumption.
    + unfold val_rel_struct in Hstruct |- *.
      destruct Hstruct as (Hv1 & Hv2 & Hc1 & Hc2 & (a1 & b1 & a2 & b2 & Heq1 & Heq2 & Ha & Hb)).
      repeat split; auto.
      exists a1, b1, a2, b2.
      repeat split; auto.
      * (* Convert Ha from Σ' to Σ using IH *)
        apply IHT1 with Σ'; auto.
      * (* Convert Hb from Σ' to Σ using IH *)
        apply IHT2 with Σ'; auto.

  - (* TSum T1 T2 *) [similar to TProd]

  - (* TRef T' _ *)
    (* structural part is: exists l, v1 = ELoc l /\ v2 = ELoc l *)
    (* NO Σ dependency! *)
    induction n; [simpl; trivial|].
    simpl in Hrel |- *. destruct Hrel as [Hcum Hstruct].
    split.
    + apply IHn; assumption.
    + exact Hstruct.  (* No conversion needed *)

  - (* TSecret T' *) [structural is True, no conversion needed]
  - (* TLabeled T' _ *) [structural is True]
  (* ... etc for all first-order types ... *)
Qed.
```

### Approach 2: Prove Store Independence Lemma First

```coq
(* First prove that val_rel_struct is Σ-independent for first-order types *)
Lemma val_rel_struct_fo_store_indep : forall T,
  first_order_type T = true ->
  forall (R : store_ty -> ty -> expr -> expr -> Prop) Σ Σ' v1 v2,
    (* Assuming R is itself Σ-independent for first-order types *)
    (forall T', first_order_type T' = true -> forall Σ1 Σ2 v1' v2',
       R Σ1 T' v1' v2' <-> R Σ2 T' v1' v2') ->
    val_rel_struct R Σ T v1 v2 <-> val_rel_struct R Σ' T v1 v2.
Proof.
  (* By case analysis on T *)
  ...
Qed.

(* Then the main lemma follows easily *)
Lemma val_rel_le_store_weaken_fo : forall T,
  first_order_type T = true ->
  forall n Σ Σ' v1 v2,
    store_ty_extends Σ Σ' ->
    val_rel_le n Σ' T v1 v2 ->
    val_rel_le n Σ T v1 v2.
Proof.
  intros T Hfo.
  induction n as [|n' IHn]; intros Σ Σ' v1 v2 Hext Hrel.
  - simpl. trivial.
  - simpl in Hrel |- *. destruct Hrel as [Hcum Hstruct].
    split.
    + apply IHn with Σ'; assumption.
    + apply val_rel_struct_fo_store_indep with Σ'; auto.
      (* Show that val_rel_le n' is Σ-independent for FO types *)
      intros T' Hfo' Σ1 Σ2 v1' v2'.
      split; intro H.
      * apply IHn with Σ1; [apply store_ty_extends_refl | exact H].
      * apply IHn with Σ2; [apply store_ty_extends_refl | exact H].
Qed.
```

## Your Task

Provide a COMPLETE Coq proof for `val_rel_le_store_weaken_fo` using one of the approaches above.

### Requirements

1. **Handle all first-order type cases**: TUnit, TBool, TInt, TString, TBytes, TProd, TSum, TList, TOption, TRef, TSecret, TLabeled, TTainted, TSanitized, TProof, TCapability, TCapabilityFull, TConstantTime, TZeroizing

2. **Use structural induction on T** or prove auxiliary lemma first

3. **For compound types** (TProd, TSum, TList, TOption): use IH on components

4. **For wrapper types** (TRef, TSecret, TLabeled, etc.): show structural part doesn't change with Σ

## Constraints

1. **COMPLETE**: Handle all first-order type cases
2. **NO AXIOMS**: Must be fully proven
3. **EXPLICIT**: Each case clearly shown

## Rules to Apply

1. **Revolutionary Solution**: Complete proof with all cases.

2. **Zero Vulnerabilities**: Every first-order type handled.

3. **Ultra Paranoid Verification**: Each tactic justified.

4. **No Shortcuts**: All ~20 type cases must be explicit.

5. **Foundational Correctness**: Based on actual val_rel_struct definition.

## Deliverable

Complete Coq proof for val_rel_le_store_weaken_fo.
