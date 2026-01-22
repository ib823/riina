# CLAUDE AI DELEGATION PROMPT — Reference Operations

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  RIINA — Rigorous Immutable Integrity No-attack Assured                          ║
║  FORMAL PROOF DELEGATION: Reference Operations (Ref, Deref, Assign)              ║
║                                                                                  ║
║  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR              ║
║  "Security proven. Family driven."                                               ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## SECTION 0: MANDATORY MINDSET — READ AND INTERNALIZE COMPLETELY

Before you do ANYTHING, you MUST internalize these rules:

### Rule 1: Revolutionary Excellence
In whatever task you execute or document you generate, the mindset you MUST apply is that the solution is the most ideal that you can ever dream of. It will be the most revolutionary, disruptive, and first ever in human history, putting all other solutions to be TOTALLY OBSOLETE.

### Rule 2: Perfect Security — All Threats Obsolete
Any threats known or unknown, from the first threats or vulnerability ever recorded in human history to today/this exact second, and also any new threats upcoming and in the future are COMPLETELY OBSOLETE and will ALWAYS be obsolete as the solution is the PERFECT solution, and NO other solution will be better.

### Rule 3: ULTRA KIASU — Extreme Paranoid Verification
In any task, be EXTREMELY KIASU, EXTREMELY PARANOID, EXTREMELY NO-TRUST to anything you research or deep research until you can independently verify or validate. Trust NOTHING. Verify EVERYTHING.

### Rule 4: NO SHORTCUTS — INFINITE TIMELINE
You are NOT lazy. You know all shortcuts and what to skip or to summarize but you will NEVER EVER do that or resort to it. You will ensure everything is correctly executed based on the most fundamental or foundational work. There is NO limit for your task to be executed, NO constraint of time, and NO limit in duration.

### Rule 5: EXTREME RIGOUR
Every proof must be COMPLETE with NO gaps, NO handwaving, NO "obvious" claims. Every single tactic must be justified. Every single step must be verified.

---

## SECTION 1: OVERVIEW — Three Reference Operation Lemmas

You must prove THREE lemmas about reference operations:

| Lemma | Operation | Key Step Rule | Security Property |
|-------|-----------|---------------|-------------------|
| `exp_rel_step1_ref` | `ERef v sl` | `ST_RefValue` | Related stores allocate to SAME location |
| `exp_rel_step1_deref` | `EDeref (ELoc l)` | `ST_DerefLoc` | Dereference retrieves stored values |
| `exp_rel_step1_assign` | `EAssign (ELoc l) v` | `ST_AssignLoc` | Assignment produces EUnit |

**Non-Interference Property:**
For all three operations, when two related programs execute these operations on related stores, they:
1. Take the SAME computational steps
2. Produce related results
3. Maintain store consistency

---

## SECTION 2: COMPLETE TYPE DEFINITIONS

```coq
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

Open Scope Z_scope.

(** ========================================================================
    BASIC TYPE ALIASES
    ======================================================================== *)

Definition ident := string.
Definition loc := nat.
Definition security_level := nat.
Definition label := string.
Definition effect_label := string.
Definition effect := list effect_label.

(** ========================================================================
    CORE TYPE DEFINITION
    ======================================================================== *)

Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TFn : ty -> ty -> effect -> ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TList : ty -> ty
  | TOption : ty -> ty
  | TRef : ty -> security_level -> ty    (* Reference type: TRef T sl *)
  | TSecret : ty -> ty
  | TLabeled : ty -> label -> ty.

(** ========================================================================
    EXPRESSION DEFINITION
    ======================================================================== *)

Inductive expr : Type :=
  (* Values *)
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : nat -> expr                    (* Location value *)
  | EVar : ident -> expr
  (* Lambda and application *)
  | ELam : ident -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  (* Pairs and Sums *)
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | EInl : expr -> ty -> expr
  | EInr : expr -> ty -> expr
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
  (* Control flow *)
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  (* REFERENCE OPERATIONS — THE FOCUS *)
  | ERef : expr -> security_level -> expr (* Create reference: ERef e sl *)
  | EDeref : expr -> expr                 (* Dereference: EDeref e *)
  | EAssign : expr -> expr -> expr.       (* Assignment: EAssign e1 e2 *)

(** ========================================================================
    VALUE PREDICATE
    ======================================================================== *)

Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc : forall l, value (ELoc l)       (* Locations are values *)
  | VLam : forall x T body, value (ELam x T body)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T).
```

---

## SECTION 3: STORE DEFINITIONS

```coq
(** ========================================================================
    STORE AND STORE TYPING
    ======================================================================== *)

(* Store: maps locations to values *)
Definition store := list (loc * expr).

(* Store typing: maps locations to types with security levels *)
Definition store_ty := list (loc * ty * security_level).

(* Effect context *)
Definition effect_ctx := list effect.

(** ========================================================================
    STORE OPERATIONS
    ======================================================================== *)

(* Lookup value at location in store *)
Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

(* Maximum location in store (for fresh allocation) *)
Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

(* Fresh location: one more than the maximum *)
Definition fresh_loc (st : store) : loc := S (store_max st).

(* Update store at location (or add if new) *)
Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.

(** ========================================================================
    STORE RELATION BASE
    ======================================================================== *)

(* Two stores are related at base level if they have the same max *)
(* This ensures fresh_loc produces the SAME location in both *)
Definition store_rel_n_base (Sigma : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.

(* CRITICAL LEMMA: Related stores have same fresh location *)
Lemma store_rel_fresh_eq : forall Sigma st1 st2,
  store_rel_n_base Sigma st1 st2 ->
  fresh_loc st1 = fresh_loc st2.
Proof.
  intros Sigma st1 st2 Hrel.
  unfold store_rel_n_base in Hrel.
  unfold fresh_loc.
  rewrite Hrel.
  reflexivity.
Qed.
```

---

## SECTION 4: OPERATIONAL SEMANTICS

```coq
(** ========================================================================
    SMALL-STEP OPERATIONAL SEMANTICS
    ======================================================================== *)

Reserved Notation "cfg1 '-->' cfg2" (at level 40).

Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=

  (* ================================================================
     REFERENCE CREATION — ST_RefValue
     ================================================================
     When the argument is a value, allocate at fresh location.

     Premise: value v
     Premise: l = fresh_loc st
     Result:  (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)
  *)
  | ST_RefValue : forall v sl st ctx l,
      value v ->
      l = fresh_loc st ->
      (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)

  (* ================================================================
     DEREFERENCE — ST_DerefLoc
     ================================================================
     When dereferencing a location, look up the stored value.

     Premise: store_lookup l st = Some v
     Result:  (EDeref (ELoc l), st, ctx) --> (v, st, ctx)
  *)
  | ST_DerefLoc : forall v l st ctx,
      store_lookup l st = Some v ->
      (EDeref (ELoc l), st, ctx) --> (v, st, ctx)

  (* ================================================================
     ASSIGNMENT — ST_AssignLoc
     ================================================================
     When assigning to a location, update the store and return unit.

     Premise: store_lookup l st = Some v1 (location must exist)
     Premise: value v2 (value being assigned)
     Result:  (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)
  *)
  | ST_AssignLoc : forall l st ctx v1 v2,
      store_lookup l st = Some v1 ->
      value v2 ->
      (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)

  (* Other step rules for completeness *)
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) -->
        (subst x v body, st, ctx)

  | ST_Fst : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)

  | ST_Snd : forall v1 v2 st ctx,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)

  | ST_IfTrue : forall e2 e3 st ctx,
      (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)

  | ST_IfFalse : forall e2 e3 st ctx,
      (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)

  | ST_LetValue : forall x v e2 st ctx,
      value v ->
      (ELet x v e2, st, ctx) --> (subst x v e2, st, ctx)

  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> (subst x1 v e1, st, ctx)

  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> (subst x2 v e2, st, ctx)

where "cfg1 '-->' cfg2" := (step cfg1 cfg2)

(* Substitution placeholder - you must define this *)
with subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar y => if String.eqb x y then v else EVar y
  | ELam y T body =>
      if String.eqb x y then ELam y T body else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e => EFst (subst x v e)
  | ESnd e => ESnd (subst x v e)
  | EInl e T => EInl (subst x v e) T
  | EInr e T => EInr (subst x v e) T
  | ECase e y1 e1 y2 e2 =>
      ECase (subst x v e)
        y1 (if String.eqb x y1 then e1 else subst x v e1)
        y2 (if String.eqb x y2 then e2 else subst x v e2)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ELet y e1 e2 =>
      ELet y (subst x v e1) (if String.eqb x y then e2 else subst x v e2)
  | ERef e sl => ERef (subst x v e) sl
  | EDeref e => EDeref (subst x v e)
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20, x at next level).

(** ========================================================================
    MULTI-STEP REDUCTION
    ======================================================================== *)

Inductive multi_step : (expr * store * effect_ctx) ->
                       (expr * store * effect_ctx) -> Prop :=
  | MS_Refl : forall cfg,
      multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 ->
      multi_step cfg2 cfg3 ->
      multi_step cfg1 cfg3.

Notation "cfg1 '-->*' cfg2" := (multi_step cfg1 cfg2) (at level 50).
```

---

## SECTION 5: VALUE RELATIONS

```coq
(** ========================================================================
    FIRST-ORDER TYPE PREDICATE
    ======================================================================== *)

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef T _ => first_order_type T
  | TList T => first_order_type T
  | TOption T => first_order_type T
  | TSecret T => first_order_type T
  | TLabeled T _ => first_order_type T
  end.

(** ========================================================================
    CLOSED EXPRESSIONS
    ======================================================================== *)

Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EVar y => x = y
  | ELam y T body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  | EPair e1 e2 => free_in x e1 \/ free_in x e2
  | EFst e => free_in x e
  | ESnd e => free_in x e
  | EInl e _ => free_in x e
  | EInr e _ => free_in x e
  | ECase e y1 e1 y2 e2 =>
      free_in x e \/ (x <> y1 /\ free_in x e1) \/ (x <> y2 /\ free_in x e2)
  | EIf e1 e2 e3 => free_in x e1 \/ free_in x e2 \/ free_in x e3
  | ELet y e1 e2 => free_in x e1 \/ (x <> y /\ free_in x e2)
  | ERef e _ => free_in x e
  | EDeref e => free_in x e
  | EAssign e1 e2 => free_in x e1 \/ free_in x e2
  | _ => False
  end.

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

(** ========================================================================
    FIRST-ORDER VALUE RELATION
    ======================================================================== *)

Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret _ => True
  | TLabeled _ _ => True
  (* REFERENCES: Same location *)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TList _ => True
  | TOption _ => True
  | TProd T1 T2 =>
      exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
        val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\
                     val_rel_at_type_fo T1 x1 x2)
      \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\
                     val_rel_at_type_fo T2 y1 y2)
  | TFn _ _ _ => True
  end.

(** ========================================================================
    BASE VALUE RELATION
    ======================================================================== *)

Definition val_rel_n_base (Sigma : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  (if first_order_type T then val_rel_at_type_fo T v1 v2 else True).
```

---

## SECTION 6: HELPER LEMMAS

```coq
(** ========================================================================
    EXTRACTION LEMMAS
    ======================================================================== *)

(** Extract value property from val_rel_n_base *)
Lemma val_rel_n_base_value : forall Sigma T v1 v2,
  val_rel_n_base Sigma T v1 v2 ->
  value v1 /\ value v2.
Proof.
  intros Sigma T v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [Hv1 [Hv2 _]].
  split; assumption.
Qed.

(** Extract location from val_rel_n_base TRef *)
Lemma val_rel_n_base_ref : forall Sigma T sl v1 v2,
  first_order_type (TRef T sl) = true ->
  val_rel_n_base Sigma (TRef T sl) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l.
Proof.
  intros Sigma T sl v1 v2 Hfo Hrel.
  unfold val_rel_n_base in Hrel.
  destruct Hrel as [_ [_ [_ [_ Htype]]]].
  rewrite Hfo in Htype.
  simpl in Htype.
  exact Htype.
Qed.

(** Extract unit equality from val_rel_n_base TUnit *)
Lemma val_rel_n_base_unit : forall Sigma v1 v2,
  val_rel_n_base Sigma TUnit v1 v2 ->
  v1 = EUnit /\ v2 = EUnit.
Proof.
  intros Sigma v1 v2 H.
  unfold val_rel_n_base in H.
  destruct H as [_ [_ [_ [_ Hfo]]]].
  simpl in Hfo.
  exact Hfo.
Qed.

(** Store max preserved by update *)
Lemma store_max_update_le : forall l v st,
  l <= store_max st ->
  store_max (store_update l v st) = store_max st.
Proof.
  intros l v st.
  induction st as [| [l' v'] st' IH].
  - (* nil case *)
    simpl. intros Hle. lia.
  - (* cons case *)
    simpl. intros Hle.
    destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l' *)
      simpl. reflexivity.
    + (* l <> l' *)
      simpl.
      apply Nat.eqb_neq in Heq.
      rewrite IH.
      * reflexivity.
      * lia.
Qed.

(** Fresh location is greater than store_max *)
Lemma fresh_loc_gt_max : forall st,
  fresh_loc st > store_max st.
Proof.
  intros st. unfold fresh_loc. lia.
Qed.

(** Store max after update at fresh location *)
Lemma store_max_update_fresh : forall v st,
  store_max (store_update (fresh_loc st) v st) = fresh_loc st.
Proof.
  intros v st.
  unfold fresh_loc.
  induction st as [| [l' v'] st' IH].
  - (* nil case *)
    simpl. lia.
  - (* cons case *)
    simpl.
    destruct (Nat.eqb (S (Nat.max l' (store_max st'))) l') eqn:Heq.
    + (* S max = l' - impossible since S max > max >= l' *)
      apply Nat.eqb_eq in Heq. lia.
    + (* S max <> l' *)
      simpl.
      (* Need: max l' (store_max (store_update (S (max l' (store_max st'))) v st'))
               = S (max l' (store_max st')) *)
      (* From IH: store_max (store_update (S (store_max st')) v st') = S (store_max st') *)
      (* when applied to st' *)
      rewrite IH.
      lia.
Qed.
```

---

## SECTION 7: THE THREE MAIN THEOREMS

### 7.1 THEOREM 1: exp_rel_step1_ref (Reference Creation)

```coq
(** ========================================================================
    THEOREM 1: exp_rel_step1_ref
    ========================================================================

    When creating references to values in related stores,
    both allocations go to the SAME fresh location.

    KEY INSIGHT: store_rel_n_base ensures store_max st1 = store_max st2,
    so fresh_loc st1 = fresh_loc st2.
*)

Theorem exp_rel_step1_ref : forall Sigma sl v v' st1 st2 ctx,
  value v -> value v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists l st1' st2' ctx',
    (ERef v sl, st1, ctx) -->* (ELoc l, st1', ctx') /\
    (ERef v' sl, st2, ctx) -->* (ELoc l, st2', ctx') /\
    store_rel_n_base Sigma st1' st2'.
Proof.
  intros Sigma sl v v' st1 st2 ctx Hv1 Hv2 Hstore.

  (* Step 1: Establish that fresh_loc is the same in both stores *)
  assert (Hfresh_eq : fresh_loc st1 = fresh_loc st2).
  { apply store_rel_fresh_eq with (Sigma := Sigma). exact Hstore. }

  (* Step 2: The fresh location *)
  remember (fresh_loc st1) as l.

  (* Step 3: Provide witnesses *)
  exists l, (store_update l v st1), (store_update l v' st2), ctx.

  split.
  (* First allocation: (ERef v sl, st1, ctx) -->* (ELoc l, st1', ctx) *)
  - apply MS_Step with (cfg2 := (ELoc l, store_update l v st1, ctx)).
    + apply ST_RefValue.
      * exact Hv1.
      * exact Heql.
    + apply MS_Refl.

  split.
  (* Second allocation: (ERef v' sl, st2, ctx) -->* (ELoc l, st2', ctx) *)
  - apply MS_Step with (cfg2 := (ELoc l, store_update l v' st2, ctx)).
    + apply ST_RefValue.
      * exact Hv2.
      * (* l = fresh_loc st2, which equals fresh_loc st1 = l *)
        rewrite Hfresh_eq. exact Heql.
    + apply MS_Refl.

  (* Store relation preserved *)
  - unfold store_rel_n_base.
    unfold store_rel_n_base in Hstore.
    (* store_max st1 = store_max st2 *)
    (* After update at fresh_loc: both become fresh_loc *)
    rewrite <- Heql.
    rewrite store_max_update_fresh.
    rewrite Hfresh_eq.
    rewrite store_max_update_fresh.
    reflexivity.
Qed.
```

### 7.2 THEOREM 2: exp_rel_step1_deref (Dereference)

```coq
(** ========================================================================
    THEOREM 2: exp_rel_step1_deref
    ========================================================================

    When dereferencing the same location in related stores,
    the stored values are retrieved.

    NOTE: This theorem requires that the location exists in both stores
    and we are given the values that will be retrieved.
*)

Theorem exp_rel_step1_deref : forall Sigma l v1 v2 st1 st2 ctx,
  store_lookup l st1 = Some v1 ->
  store_lookup l st2 = Some v2 ->
  store_rel_n_base Sigma st1 st2 ->
  exists st1' st2' ctx',
    (EDeref (ELoc l), st1, ctx) -->* (v1, st1', ctx') /\
    (EDeref (ELoc l), st2, ctx) -->* (v2, st2', ctx') /\
    store_rel_n_base Sigma st1' st2'.
Proof.
  intros Sigma l v1 v2 st1 st2 ctx Hlook1 Hlook2 Hstore.

  (* Provide witnesses - stores don't change *)
  exists st1, st2, ctx.

  split.
  (* First dereference: (EDeref (ELoc l), st1, ctx) -->* (v1, st1, ctx) *)
  - apply MS_Step with (cfg2 := (v1, st1, ctx)).
    + apply ST_DerefLoc. exact Hlook1.
    + apply MS_Refl.

  split.
  (* Second dereference: (EDeref (ELoc l), st2, ctx) -->* (v2, st2, ctx) *)
  - apply MS_Step with (cfg2 := (v2, st2, ctx)).
    + apply ST_DerefLoc. exact Hlook2.
    + apply MS_Refl.

  (* Store relation preserved - stores unchanged *)
  - exact Hstore.
Qed.
```

### 7.3 THEOREM 3: exp_rel_step1_assign (Assignment)

```coq
(** ========================================================================
    THEOREM 3: exp_rel_step1_assign
    ========================================================================

    When assigning values to the same location in related stores,
    both produce EUnit and maintain store relation.

    KEY INSIGHT: ST_AssignLoc requires the location to already exist.
*)

Theorem exp_rel_step1_assign : forall Sigma l v v' st1 st2 ctx,
  value v -> value v' ->
  store_lookup l st1 <> None ->  (* Location exists in st1 *)
  store_lookup l st2 <> None ->  (* Location exists in st2 *)
  store_rel_n_base Sigma st1 st2 ->
  exists st1' st2' ctx',
    (EAssign (ELoc l) v, st1, ctx) -->* (EUnit, st1', ctx') /\
    (EAssign (ELoc l) v', st2, ctx) -->* (EUnit, st2', ctx') /\
    store_rel_n_base Sigma st1' st2'.
Proof.
  intros Sigma l v v' st1 st2 ctx Hv1 Hv2 Hexists1 Hexists2 Hstore.

  (* Extract the existing values at location l *)
  destruct (store_lookup l st1) as [old1|] eqn:Hlook1.
  2: { (* None case - contradicts Hexists1 *)
       exfalso. apply Hexists1. reflexivity. }
  destruct (store_lookup l st2) as [old2|] eqn:Hlook2.
  2: { (* None case - contradicts Hexists2 *)
       exfalso. apply Hexists2. reflexivity. }

  (* Provide witnesses *)
  exists (store_update l v st1), (store_update l v' st2), ctx.

  split.
  (* First assignment: (EAssign (ELoc l) v, st1, ctx) -->* (EUnit, st1', ctx) *)
  - apply MS_Step with (cfg2 := (EUnit, store_update l v st1, ctx)).
    + apply ST_AssignLoc with (v1 := old1).
      * exact Hlook1.
      * exact Hv1.
    + apply MS_Refl.

  split.
  (* Second assignment: (EAssign (ELoc l) v', st2, ctx) -->* (EUnit, st2', ctx) *)
  - apply MS_Step with (cfg2 := (EUnit, store_update l v' st2, ctx)).
    + apply ST_AssignLoc with (v1 := old2).
      * exact Hlook2.
      * exact Hv2.
    + apply MS_Refl.

  (* Store relation preserved *)
  - unfold store_rel_n_base.
    unfold store_rel_n_base in Hstore.
    (* Need: store_max (store_update l v st1) = store_max (store_update l v' st2) *)
    (* Since l exists in both stores, l <= store_max for both *)
    (* Therefore store_max is preserved by update *)
    rewrite store_max_update_le.
    + rewrite store_max_update_le.
      * exact Hstore.
      * (* l <= store_max st2 *)
        (* l exists in st2, so l <= store_max st2 *)
        apply store_lookup_le_max. exact Hlook2.
    + (* l <= store_max st1 *)
      apply store_lookup_le_max. exact Hlook1.
Qed.

(** Helper: If store_lookup l st = Some v, then l <= store_max st *)
Lemma store_lookup_le_max : forall l st v,
  store_lookup l st = Some v ->
  l <= store_max st.
Proof.
  intros l st v.
  induction st as [| [l' v'] st' IH].
  - (* nil case - lookup returns None *)
    simpl. intros H. discriminate.
  - (* cons case *)
    simpl. destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l' *)
      intros _. apply Nat.eqb_eq in Heq. subst. lia.
    + (* l <> l' *)
      intros Hlook. specialize (IH Hlook). lia.
Qed.
```

---

## SECTION 8: VERIFICATION

```coq
(** ========================================================================
    VERIFICATION: Print assumptions to confirm ZERO AXIOMS
    ======================================================================== *)

Print Assumptions store_rel_fresh_eq.
Print Assumptions exp_rel_step1_ref.
Print Assumptions exp_rel_step1_deref.
Print Assumptions exp_rel_step1_assign.

(** Expected output for all:
    Closed under the global context

    This confirms ZERO AXIOMS used - pure constructive proofs.
*)
```

---

## SECTION 9: OUTPUT FORMAT

Output a COMPLETE, SELF-CONTAINED Coq file that:

1. Includes ALL definitions from Sections 2-5
2. Includes ALL helper lemmas from Section 6
3. Includes ALL three main theorems from Section 7
4. Includes verification from Section 8
5. Every `Proof.` has a matching `Qed.` (NO `Admitted.`)
6. Compiles with `coqc` and passes `coqchk`

---

## SECTION 10: VERIFICATION CHECKLIST

Before submitting, verify EVERY item:

- [ ] `store_rel_fresh_eq` is proven BEFORE it is used
- [ ] `store_lookup_le_max` is proven BEFORE it is used
- [ ] `store_max_update_le` is proven BEFORE it is used
- [ ] `store_max_update_fresh` is proven BEFORE it is used
- [ ] `exp_rel_step1_ref` uses `ST_RefValue` correctly
- [ ] `exp_rel_step1_deref` uses `ST_DerefLoc` correctly
- [ ] `exp_rel_step1_assign` uses `ST_AssignLoc` correctly
- [ ] All bullets are properly nested (`-`, `+`, `*`)
- [ ] All identifiers are spelled correctly (case-sensitive)
- [ ] `Print Assumptions` shows "Closed under the global context"

---

## SECTION 11: COMMON PITFALLS

### 11.1 ST_RefValue Requires TWO Premises

```coq
(* ST_RefValue has TWO premises: *)
| ST_RefValue : forall v sl st ctx l,
    value v ->                (* Premise 1: v is a value *)
    l = fresh_loc st ->       (* Premise 2: l equals fresh_loc *)
    (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)

(* CORRECT application: *)
apply ST_RefValue.
- exact Hv.     (* Prove: value v *)
- exact Heql.   (* Prove: l = fresh_loc st *)
```

### 11.2 ST_AssignLoc Requires Location Existence

```coq
(* ST_AssignLoc requires the location to already exist: *)
| ST_AssignLoc : forall l st ctx v1 v2,
    store_lookup l st = Some v1 ->  (* Location must exist with some value *)
    value v2 ->                     (* New value must be a value *)
    (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)

(* CORRECT application: *)
apply ST_AssignLoc with (v1 := old_value).
- exact Hlook.  (* Prove: store_lookup l st = Some old_value *)
- exact Hv.     (* Prove: value v *)
```

### 11.3 Store Max After Update

```coq
(* When updating at a location that EXISTS: store_max is preserved *)
(* When updating at fresh_loc: store_max becomes fresh_loc *)

(* For assign (location exists): use store_max_update_le *)
(* For ref (fresh location): use store_max_update_fresh *)
```

---

## SECTION 12: CRITICAL REMINDERS

1. **EXTREME RIGOUR**: Every step must be justified. No handwaving.
2. **NO `admit` OR `Admitted`**: Every proof must be 100% complete.
3. **TEST COMPILATION**: The file must compile with `coqc`.
4. **VERIFY WITH `coqchk`**: Must show "Modules were successfully checked".
5. **ZERO AXIOMS**: `Print Assumptions` must show "Closed under the global context".
6. **HELPER LEMMAS FIRST**: All helper lemmas must be proven BEFORE they are used.

---

**END OF PROMPT — NOW EXECUTE WITH ULTRA KIASU EXTREME RIGOUR**

**These proofs establish the foundation of RIINA's memory safety guarantees.**

**Failure is NOT an option. Verify EVERYTHING.**
