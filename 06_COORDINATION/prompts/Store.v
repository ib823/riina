(** * Store: Store Typing for TERAS-LANG *)

Require Import TerasLang.Prelude.Prelude.
Require Import TerasLang.Prelude.Syntax.

(** ** Store Typing *)

(** A store type maps locations to their types and security labels *)

Definition store_ty := list (loc * ty * sec_label).

(** Lookup a location in the store type *)

Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * sec_label) :=
  match Σ with
  | nil => None
  | (l', T, sl) :: rest =>
      if Nat.eqb l l' then Some (T, sl)
      else store_ty_lookup l rest
  end.

(** Store type membership *)

Definition store_ty_contains (l : loc) (T : ty) (sl : sec_label) (Σ : store_ty) : Prop :=
  store_ty_lookup l Σ = Some (T, sl).

(** Store type extension *)

Definition store_ty_extends (Σ1 Σ2 : store_ty) : Prop :=
  forall l T sl, store_ty_lookup l Σ1 = Some (T, sl) ->
                 store_ty_lookup l Σ2 = Some (T, sl).

(** Store type extension is reflexive *)

Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Proof.
  unfold store_ty_extends. intros. assumption.
Qed.

(** Store type extension is transitive *)

Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
Proof.
  unfold store_ty_extends. intros Σ1 Σ2 Σ3 H12 H23 l T sl Hl.
  apply H23. apply H12. assumption.
Qed.
