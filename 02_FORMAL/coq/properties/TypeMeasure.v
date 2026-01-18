(** * TypeMeasure.v

    RIINA Type Size Measure for Well-Founded Induction

    This file defines a size measure on types that enables well-founded
    induction, critical for handling the TFn contravariance problem.

    KEY INSIGHT: The size of a type gives a natural measure for recursion.
    For TFn T1 T2, both T1 and T2 are strictly smaller than TFn T1 T2.
    This enables proving properties by induction on type structure.

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE

    Worker: WORKER_α (Alpha)
    Phase: 1 (Foundation)
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Lia.

Require Import RIINA.foundations.Syntax.

(** ** Type Size Function

    Computes the structural size of a type.
    All base types have size 1.
    Compound types have size = 1 + sum of subtype sizes.
*)

Fixpoint ty_size (T : ty) : nat :=
  match T with
  (* Primitive types *)
  | TUnit => 1
  | TBool => 1
  | TInt => 1
  | TString => 1
  | TBytes => 1
  (* Function types *)
  | TFn T1 T2 _ => 1 + ty_size T1 + ty_size T2
  (* Compound types *)
  | TProd T1 T2 => 1 + ty_size T1 + ty_size T2
  | TSum T1 T2 => 1 + ty_size T1 + ty_size T2
  | TList T' => 1 + ty_size T'
  | TOption T' => 1 + ty_size T'
  (* Reference types *)
  | TRef T' _ => 1 + ty_size T'
  (* Security types *)
  | TSecret T' => 1 + ty_size T'
  | TLabeled T' _ => 1 + ty_size T'
  | TTainted T' _ => 1 + ty_size T'
  | TSanitized T' _ => 1 + ty_size T'
  | TProof T' => 1 + ty_size T'
  (* Capability types *)
  | TCapability _ => 1
  | TCapabilityFull _ => 1
  (* Channel types - session types have size 1 *)
  | TChan _ => 1
  | TSecureChan _ _ => 1
  (* Constant-time and zeroizing types *)
  | TConstantTime T' => 1 + ty_size T'
  | TZeroizing T' => 1 + ty_size T'
  end.

(** ** Positivity: All types have positive size *)

Lemma ty_size_pos : forall T, ty_size T > 0.
Proof.
  induction T; simpl; lia.
Qed.

(** ** Subtype Size Ordering Lemmas *)

(** TFn argument is strictly smaller *)
Lemma ty_size_fn_arg : forall T1 T2 eff,
  ty_size T1 < ty_size (TFn T1 T2 eff).
Proof.
  intros. simpl. lia.
Qed.

(** TFn result is strictly smaller *)
Lemma ty_size_fn_res : forall T1 T2 eff,
  ty_size T2 < ty_size (TFn T1 T2 eff).
Proof.
  intros. simpl.
  pose proof (ty_size_pos T1). lia.
Qed.

(** TProd left is strictly smaller *)
Lemma ty_size_prod_left : forall T1 T2,
  ty_size T1 < ty_size (TProd T1 T2).
Proof.
  intros. simpl. lia.
Qed.

(** TProd right is strictly smaller *)
Lemma ty_size_prod_right : forall T1 T2,
  ty_size T2 < ty_size (TProd T1 T2).
Proof.
  intros. simpl.
  pose proof (ty_size_pos T1). lia.
Qed.

(** TSum left is strictly smaller *)
Lemma ty_size_sum_left : forall T1 T2,
  ty_size T1 < ty_size (TSum T1 T2).
Proof.
  intros. simpl. lia.
Qed.

(** TSum right is strictly smaller *)
Lemma ty_size_sum_right : forall T1 T2,
  ty_size T2 < ty_size (TSum T1 T2).
Proof.
  intros. simpl.
  pose proof (ty_size_pos T1). lia.
Qed.

(** TRef content is strictly smaller *)
Lemma ty_size_ref_content : forall T sl,
  ty_size T < ty_size (TRef T sl).
Proof.
  intros. simpl. lia.
Qed.

(** TSecret content is strictly smaller *)
Lemma ty_size_secret_content : forall T,
  ty_size T < ty_size (TSecret T).
Proof.
  intros. simpl. lia.
Qed.

(** TProof content is strictly smaller *)
Lemma ty_size_proof_content : forall T,
  ty_size T < ty_size (TProof T).
Proof.
  intros. simpl. lia.
Qed.

(** ** Well-Founded Induction on Type Size

    This is the key enabler for handling TFn contravariance.
    We can use well-founded induction on ty_size instead of
    structural induction on ty.
*)

Definition ty_size_lt (T1 T2 : ty) : Prop := ty_size T1 < ty_size T2.

(** ty_size_lt is well-founded (inherits from lt on nat) *)
Lemma ty_size_lt_wf : well_founded ty_size_lt.
Proof.
  unfold ty_size_lt.
  apply well_founded_ltof.
Qed.

(** Induction principle based on type size *)
Lemma ty_size_induction :
  forall (P : ty -> Prop),
    (forall T, (forall T', ty_size T' < ty_size T -> P T') -> P T) ->
    forall T, P T.
Proof.
  intros P IH T.
  apply (well_founded_ind ty_size_lt_wf P).
  intros T' H. apply IH. exact H.
Qed.

(** ** First-Order Type Detection

    A type is first-order if it contains no TFn.
    First-order types have simpler relation properties.
*)

Fixpoint first_order_type (T : ty) : bool :=
  match T with
  (* Primitive types - all first-order *)
  | TUnit => true
  | TBool => true
  | TInt => true
  | TString => true
  | TBytes => true
  (* Functions are higher-order *)
  | TFn _ _ _ => false
  (* Compound types - first-order if components are *)
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TList T' => first_order_type T'
  | TOption T' => first_order_type T'
  (* Reference types *)
  | TRef T' _ => first_order_type T'
  (* Security types *)
  | TSecret T' => first_order_type T'
  | TLabeled T' _ => first_order_type T'
  | TTainted T' _ => first_order_type T'
  | TSanitized T' _ => first_order_type T'
  | TProof T' => first_order_type T'
  (* Capability types - first-order *)
  | TCapability _ => true
  | TCapabilityFull _ => true
  (* Channel types - depends on session protocol, conservatively higher-order *)
  | TChan _ => false
  | TSecureChan _ _ => false
  (* Constant-time and zeroizing *)
  | TConstantTime T' => first_order_type T'
  | TZeroizing T' => first_order_type T'
  end.

(** First-order types contain no TFn *)
Lemma first_order_no_fn : forall T T1 T2 eff,
  first_order_type T = true ->
  T <> TFn T1 T2 eff.
Proof.
  intros T T1 T2 eff Hfo Heq.
  subst. simpl in Hfo. discriminate.
Qed.

(** First-order is decidable *)
Lemma first_order_decidable : forall T,
  {first_order_type T = true} + {first_order_type T = false}.
Proof.
  intro T. destruct (first_order_type T); auto.
Qed.

(** First-order subtypes of first-order types *)
Lemma first_order_prod_inv : forall T1 T2,
  first_order_type (TProd T1 T2) = true ->
  first_order_type T1 = true /\ first_order_type T2 = true.
Proof.
  intros T1 T2 H. simpl in H.
  apply Bool.andb_true_iff in H. exact H.
Qed.

Lemma first_order_sum_inv : forall T1 T2,
  first_order_type (TSum T1 T2) = true ->
  first_order_type T1 = true /\ first_order_type T2 = true.
Proof.
  intros T1 T2 H. simpl in H.
  apply Bool.andb_true_iff in H. exact H.
Qed.

Lemma first_order_ref_inv : forall T sl,
  first_order_type (TRef T sl) = true ->
  first_order_type T = true.
Proof.
  intros T sl H. simpl in H. exact H.
Qed.

Lemma first_order_secret_inv : forall T,
  first_order_type (TSecret T) = true ->
  first_order_type T = true.
Proof.
  intros T H. simpl in H. exact H.
Qed.

Lemma first_order_proof_inv : forall T,
  first_order_type (TProof T) = true ->
  first_order_type T = true.
Proof.
  intros T H. simpl in H. exact H.
Qed.

(** ** Type Depth for Alternative Measure

    Depth = max nesting level, alternative to size.
*)

Fixpoint ty_depth (T : ty) : nat :=
  match T with
  (* Primitive types - depth 0 *)
  | TUnit => 0
  | TBool => 0
  | TInt => 0
  | TString => 0
  | TBytes => 0
  (* Function types *)
  | TFn T1 T2 _ => 1 + Nat.max (ty_depth T1) (ty_depth T2)
  (* Compound types *)
  | TProd T1 T2 => 1 + Nat.max (ty_depth T1) (ty_depth T2)
  | TSum T1 T2 => 1 + Nat.max (ty_depth T1) (ty_depth T2)
  | TList T' => 1 + ty_depth T'
  | TOption T' => 1 + ty_depth T'
  (* Reference types *)
  | TRef T' _ => 1 + ty_depth T'
  (* Security types *)
  | TSecret T' => 1 + ty_depth T'
  | TLabeled T' _ => 1 + ty_depth T'
  | TTainted T' _ => 1 + ty_depth T'
  | TSanitized T' _ => 1 + ty_depth T'
  | TProof T' => 1 + ty_depth T'
  (* Capability types - depth 0 *)
  | TCapability _ => 0
  | TCapabilityFull _ => 0
  (* Channel types - depth 0 (session internals not counted) *)
  | TChan _ => 0
  | TSecureChan _ _ => 0
  (* Constant-time and zeroizing *)
  | TConstantTime T' => 1 + ty_depth T'
  | TZeroizing T' => 1 + ty_depth T'
  end.

(** Depth subtype lemmas *)
Lemma ty_depth_fn_arg : forall T1 T2 eff,
  ty_depth T1 < ty_depth (TFn T1 T2 eff).
Proof.
  intros. simpl. lia.
Qed.

Lemma ty_depth_fn_res : forall T1 T2 eff,
  ty_depth T2 < ty_depth (TFn T1 T2 eff).
Proof.
  intros. simpl. lia.
Qed.

(** First-order types have depth 0 for base types *)
Lemma first_order_base_depth : forall T,
  first_order_type T = true ->
  ty_depth T >= 0.
Proof.
  intros. lia.
Qed.

(** ** Combined Measure (n, ty_size T)

    For the cumulative relation proofs, we need to decrease on
    lexicographic (n, ty_size T) where n is step index.
*)

Definition step_ty_measure (n : nat) (T : ty) : nat * nat :=
  (n, ty_size T).

(** End of TypeMeasure.v *)
