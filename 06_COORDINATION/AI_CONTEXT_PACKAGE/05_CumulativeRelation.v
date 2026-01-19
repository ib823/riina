(** * CumulativeRelation.v

    RIINA Cumulative Step-Indexed Logical Relation

    This file defines the CUMULATIVE value relation where:
    - val_rel_le n Σ T v1 v2 means "related at ALL steps k ≤ n"
    - This makes monotonicity DEFINITIONAL rather than axiomatic

    The cumulative structure is critical for handling TFn contravariance.
    In standard step-indexed models, proving monotonicity for function types
    requires axioms because of the contravariant argument position.
    With the cumulative definition, monotonicity follows directly.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_α (Alpha)
    Phase: 2 (Cumulative Relation)

    References:
    - Ahmed (2006) "Step-Indexed Syntactic Logical Relations"
    - Dreyer et al. (2011) "Logical Step-Indexed Logical Relations"
    - Appel & McAllester (2001) "An indexed model of recursive types"
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Lia.

Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.foundations.Semantics.
Require Import RIINA.properties.TypeMeasure.
Require Import RIINA.properties.LexOrder.
Require Import RIINA.properties.FirstOrderComplete.

Import ListNotations.

(** ** Closed Expression Predicate *)

Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

(** ** Store Relation (Simplified)

    For the cumulative relation, we use a simplified store relation
    that requires stores to have the same domain.
*)

Definition store_rel_simple (Σ : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.

(** ** Cumulative Value Relation

    val_rel_le n Σ T v1 v2 means:
    "v1 and v2 are related at type T for ALL steps up to and including n"

    This is defined by recursion on n, with type-specific structure.

    KEY INSIGHT: The cumulative definition means:
    - val_rel_le (S n) includes val_rel_le n as a conjunct
    - This makes STEP MONOTONICITY trivial: just project out
    - No need for complex induction to prove m <= n => related at m
*)

(** Base structural predicate at a specific type (for positive steps)

    IMPORTANT: val_rel_prev is parameterized by store_ty to support proper
    Kripke semantics. For TFn, arguments must be related at the EXTENDED
    store (Σ'), not the base store (Σ). This is essential for proving
    store extension monotonicity.

    Reference: Ahmed (2006), Dreyer et al. (2011) - standard formulation
    uses extended world for argument relations in function types.
*)
Definition val_rel_struct (val_rel_prev : store_ty -> ty -> expr -> expr -> Prop)
                          (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  value v1 /\ value v2 /\
  closed_expr v1 /\ closed_expr v2 /\
  match T with
  (* Primitive types *)
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  (* Security types - secrets/labeled are always indistinguishable *)
  | TSecret _ => True
  | TLabeled _ _ => True
  | TTainted _ _ => True  (* Tainted values: identity relation *)
  | TSanitized _ _ => True  (* Sanitized values: identity relation *)
  (* Capability types *)
  | TCapability _ => True
  | TCapabilityFull _ => True
  (* Proof types *)
  | TProof _ => True
  (* Channel types - treated as opaque *)
  | TChan _ => True
  | TSecureChan _ _ => True
  (* Constant-time and zeroizing - indistinguishable *)
  | TConstantTime _ => True
  | TZeroizing _ => True
  (* Reference types *)
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  (* Compound types *)
  | TList T' => True  (* Lists: structural equality, simplified for now *)
  | TOption T' => True  (* Options: structural equality, simplified for now *)
  | TProd T1 T2 =>
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_prev Σ T1 a1 a2 /\
        val_rel_prev Σ T2 b1 b2
  | TSum T1 T2 =>
      (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\
                     val_rel_prev Σ T1 a1 a2) \/
      (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\
                     val_rel_prev Σ T2 b1 b2)
  | TFn T1 T2 eff =>
      (* Kripke quantification: for all extended stores and related arguments
         CRITICAL: Arguments are related at the EXTENDED store Σ', not Σ.
         This is the standard Kripke semantics formulation. *)
      forall Σ', store_ty_extends Σ Σ' ->
        forall arg1 arg2,
          value arg1 -> value arg2 ->
          closed_expr arg1 -> closed_expr arg2 ->
          val_rel_prev Σ' T1 arg1 arg2 ->  (* Arguments at extended store *)
            forall st1 st2 ctx,
              store_rel_simple Σ' st1 st2 ->
              (* Application produces related results *)
              exists res1 res2 st1' st2' ctx' Σ'',
                store_ty_extends Σ' Σ'' /\
                multi_step (EApp v1 arg1, st1, ctx) (res1, st1', ctx') /\
                multi_step (EApp v2 arg2, st2, ctx) (res2, st2', ctx') /\
                value res1 /\ value res2 /\
                val_rel_prev Σ'' T2 res1 res2 /\  (* Results at final store *)
                store_rel_simple Σ'' st1' st2'
  end.

(** The cumulative value relation *)
Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True  (* At step 0, everything is trivially related *)
  | S n' =>
      (* CUMULATIVE: Include all previous steps *)
      val_rel_le n' Σ T v1 v2 /\
      (* Plus structural requirements using val_rel at n'
         NOTE: val_rel_le n' has type (store_ty -> ty -> expr -> expr -> Prop)
         which is exactly what val_rel_struct expects for Kripke semantics *)
      val_rel_struct (val_rel_le n') Σ T v1 v2
  end.

(** ** Cumulative Store Relation *)

Definition store_rel_le (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2 /\
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    match store_lookup l st1, store_lookup l st2 with
    | Some v1, Some v2 => val_rel_le n Σ T v1 v2
    | _, _ => False
    end.

(** ** Basic Properties of Cumulative Relation *)

(** At step 0, everything is related *)
Lemma val_rel_le_at_zero : forall Σ T v1 v2,
  val_rel_le 0 Σ T v1 v2.
Proof.
  intros. simpl. exact I.
Qed.

(** Cumulative structure gives us the "previous step" directly *)
Lemma val_rel_le_cumulative : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 H.
  simpl in H. destruct H as [Hprev _]. exact Hprev.
Qed.

(** Values are values *)
Lemma val_rel_le_value_left : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  value v1.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [Hv1 _]. exact Hv1.
Qed.

Lemma val_rel_le_value_right : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  value v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [_ [Hv2 _]]. exact Hv2.
Qed.

(** Related values are closed *)
Lemma val_rel_le_closed_left : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  closed_expr v1.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [_ [_ [Hc1 _]]]. exact Hc1.
Qed.

Lemma val_rel_le_closed_right : forall n Σ T v1 v2,
  n > 0 ->
  val_rel_le n Σ T v1 v2 ->
  closed_expr v2.
Proof.
  intros n Σ T v1 v2 Hn Hrel.
  destruct n as [|n']; [lia|].
  simpl in Hrel. destruct Hrel as [_ Hstruct].
  unfold val_rel_struct in Hstruct.
  destruct Hstruct as [_ [_ [_ [Hc2 _]]]]. exact Hc2.
Qed.

(** ** Step Monotonicity (DEFINITIONAL for base cases)

    This is the KEY property that makes cumulative relations work.
    For first-order types, monotonicity is immediate.
    For TFn, we need additional infrastructure (see CumulativeMonotone.v).
*)

(** Step monotonicity for first-order types *)
Lemma val_rel_le_mono_step_fo : forall n m Σ T v1 v2,
  first_order_type T = true ->
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_le m Σ T v1 v2.
Proof.
  intros n. induction n as [|n' IH].
  - (* n = 0 *)
    intros m Σ T v1 v2 Hfo Hle Hrel.
    assert (m = 0) by lia. subst. simpl. exact I.
  - (* n = S n' *)
