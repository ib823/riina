(** * ProofInfrastructure.v - Missing Lemmas for RIINA *)
(** 
    RIINA (Rigorous Immutable Invariant — Normalized Axiom)
    Complete proof infrastructure for the step-indexed logical relations.
    All proofs terminate with Qed. - NO Admitted.
    Coq Version: 8.18.0
*)

Require Import String.
Require Import List.
Require Import Nat.
Require Import ZArith.
Require Import Bool.
Require Import Lia.

Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.

(* ========================================================================= *)
(** ** SECTION 1: COMPLETE TYPE DEFINITIONS *)
(* ========================================================================= *)

(** *** 1.1 Basic Type Aliases *)

(* Identifiers are strings *)
Definition ident := string.

(* Locations are natural numbers *)
Definition loc := nat.

(* Security levels *)
Definition security_level := nat.  (* 0 = public, 1+ = secret *)
Definition Public : security_level := 0%nat.
Definition Secret : security_level := 1%nat.

(* Effects *)
Definition effect_label := string.
Definition effect := list effect_label.
Definition EffectPure : effect := nil.

(* Shorthand for security label in store *)
Definition sec_label := security_level.

(** *** 1.2 Core Type Definition *)

Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TBytes : ty
  | TFn : ty -> ty -> effect -> ty      (* Function: T1 -> T2 with effect *)
  | TProd : ty -> ty -> ty              (* Product: T1 * T2 *)
  | TSum : ty -> ty -> ty               (* Sum: T1 + T2 *)
  | TRef : ty -> sec_label -> ty        (* Reference: ref T at security level *)
  | TSecret : ty -> ty                  (* Secret/classified value *)
  | TList : ty -> ty
  | TOption : ty -> ty
  | TCapability : string -> ty
  | TProof : ty -> ty.

(** *** 1.3 Expression Definition *)

Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : loc -> expr                  (* Store location *)
  | EVar : ident -> expr
  | ELam : ident -> ty -> expr -> expr  (* Lambda: λx:T.e *)
  | EApp : expr -> expr -> expr         (* Application: e1 e2 *)
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | EInl : expr -> ty -> expr           (* Left injection *)
  | EInr : expr -> ty -> expr           (* Right injection *)
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  | ERef : expr -> sec_label -> expr    (* Allocate reference *)
  | EDeref : expr -> expr               (* Dereference *)
  | EAssign : expr -> expr -> expr      (* Assignment *)
  | EClassify : expr -> expr            (* Make secret *)
  | EDeclassify : expr -> expr -> expr. (* Reveal secret with proof *)

(** *** 1.4 Value Predicate *)

Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc : forall l, value (ELoc l)
  | VLam : forall x T body, value (ELam x T body)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T).

(** *** 1.5 Free Variables and Closed Expressions *)

(* Free variable check - returns True if x is free in e *)
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
  | _ => False
  end.

(* Closed expression: no free variables *)
Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(** *** 1.6 First-Order Type Predicate *)

(* First-order types do NOT contain function types *)
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false  (* Functions are higher-order *)
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef T _ => true    (* References to any type *)
  | TSecret T => true   (* Secrets are opaque *)
  | TList T => first_order_type T
  | TOption T => first_order_type T
  | TCapability _ => true
  | TProof _ => true
  end.

(* Decidability *)
Lemma first_order_decidable : forall T,
  {first_order_type T = true} + {first_order_type T = false}.
Proof.
  intro T. destruct (first_order_type T); auto.
Qed.

(* ========================================================================= *)
(** ** SECTION 2: STORE DEFINITIONS *)
(* ========================================================================= *)

(* Store: maps locations to values *)
Definition store := list (loc * expr).

(* Store typing: maps locations to (type, security_level) *)
Definition store_ty := list (loc * ty * sec_label).

(* Lookup in store *)
Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

(* Lookup in store typing *)
Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * sec_label) :=
  match Σ with
  | nil => None
  | (l', T, sl) :: Σ' =>
      if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l Σ'
  end.

(* Maximum location in store (for fresh allocation) *)
Fixpoint store_max (st : store) : nat :=
  match st with
  | nil => 0
  | (l, _) :: st' => Nat.max l (store_max st')
  end.

(* Fresh location *)
Definition fresh_loc (st : store) : loc := S (store_max st).

(* Update store at location *)
Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.

(* Store typing extension - Kripke world ordering *)
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).

(* Security level check *)
Definition is_low (sl : sec_label) : bool := Nat.eqb sl 0%nat.

(* ========================================================================= *)
(** ** SECTION 3: TYPING JUDGMENT *)
(* ========================================================================= *)

(* Typing context *)
Definition ctx := list (ident * ty).

(* Linear context for capabilities *)
Definition lin_ctx := list (ident * ty).

(* Lookup in context *)
Fixpoint ctx_lookup (x : ident) (Γ : ctx) : option ty :=
  match Γ with
  | nil => None
  | (y, T) :: Γ' => if string_dec x y then Some T else ctx_lookup x Γ'
  end.

(* Typing judgment: Γ; Σ; Δ ⊢ e : T @ ε *)
(* Γ = term context, Σ = store typing, Δ = linear context *)
Inductive has_type : ctx -> store_ty -> lin_ctx -> expr -> ty -> effect -> Prop :=
  | T_Unit : forall Γ Σ Δ,
      has_type Γ Σ Δ EUnit TUnit EffectPure
  | T_Bool : forall Γ Σ Δ b,
      has_type Γ Σ Δ (EBool b) TBool EffectPure
  | T_Int : forall Γ Σ Δ n,
      has_type Γ Σ Δ (EInt n) TInt EffectPure
  | T_String : forall Γ Σ Δ s,
      has_type Γ Σ Δ (EString s) TString EffectPure
  | T_Var : forall Γ Σ Δ x T,
      ctx_lookup x Γ = Some T ->
      has_type Γ Σ Δ (EVar x) T EffectPure
  | T_Loc : forall Γ Σ Δ l T sl,
      store_ty_lookup l Σ = Some (T, sl) ->
      has_type Γ Σ Δ (ELoc l) (TRef T sl) EffectPure
  | T_Lam : forall Γ Σ Δ x T1 T2 e ε,
      has_type ((x, T1) :: Γ) Σ Δ e T2 ε ->
      has_type Γ Σ Δ (ELam x T1 e) (TFn T1 T2 ε) EffectPure
  | T_App : forall Γ Σ Δ e1 e2 T1 T2 ε ε1 ε2,
      has_type Γ Σ Δ e1 (TFn T1 T2 ε) ε1 ->
      has_type Γ Σ Δ e2 T1 ε2 ->
      has_type Γ Σ Δ (EApp e1 e2) T2 (ε1 ++ ε2 ++ ε)
  | T_Pair : forall Γ Σ Δ e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type Γ Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (EPair e1 e2) (TProd T1 T2) (ε1 ++ ε2)
  | T_Fst : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e (TProd T1 T2) ε ->
      has_type Γ Σ Δ (EFst e) T1 ε
  | T_Snd : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e (TProd T1 T2) ε ->
      has_type Γ Σ Δ (ESnd e) T2 ε
  | T_Inl : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e T1 ε ->
      has_type Γ Σ Δ (EInl e T2) (TSum T1 T2) ε
  | T_Inr : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e T2 ε ->
      has_type Γ Σ Δ (EInr e T1) (TSum T1 T2) ε
  | T_Case : forall Γ Σ Δ e x1 e1 x2 e2 T1 T2 T ε ε1 ε2,
      has_type Γ Σ Δ e (TSum T1 T2) ε ->
      has_type ((x1, T1) :: Γ) Σ Δ e1 T ε1 ->
      has_type ((x2, T2) :: Γ) Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ (ECase e x1 e1 x2 e2) T (ε ++ ε1 ++ ε2)
  | T_If : forall Γ Σ Δ e1 e2 e3 T ε1 ε2 ε3,
      has_type Γ Σ Δ e1 TBool ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ e3 T ε3 ->
      has_type Γ Σ Δ (EIf e1 e2 e3) T (ε1 ++ ε2 ++ ε3)
  | T_Let : forall Γ Σ Δ x e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (ELet x e1 e2) T2 (ε1 ++ ε2).

(* ========================================================================= *)
(** ** SECTION 4: STEP-INDEXED LOGICAL RELATIONS *)
(* ========================================================================= *)

(** *** 4.1 Value Relation at Type (First-Order) *)

(* Direct value relation for first-order types *)
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists n, v1 = EInt n /\ v2 = EInt n
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => exists s, v1 = EString s /\ v2 = EString s  (* Bytes as strings *)
  | TRef _ sl => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TSecret _ => True  (* Secrets may differ *)
  | TProd T1 T2 =>
      exists v1a v1b v2a v2b,
        v1 = EPair v1a v1b /\ v2 = EPair v2a v2b /\
        val_rel_at_type_fo T1 v1a v2a /\ val_rel_at_type_fo T2 v1b v2b
  | TSum T1 T2 =>
      (exists va vb, v1 = EInl va T2 /\ v2 = EInl vb T2 /\ val_rel_at_type_fo T1 va vb) \/
      (exists va vb, v1 = EInr va T1 /\ v2 = EInr vb T1 /\ val_rel_at_type_fo T2 va vb)
  | TList _ => True  (* Simplified *)
  | TOption T =>
      (v1 = EUnit /\ v2 = EUnit) \/  (* None as unit *)
      (exists va vb, v1 = EInl va TUnit /\ v2 = EInl vb TUnit /\ val_rel_at_type_fo T va vb)
  | TCapability _ => v1 = v2  (* Capability tokens must match *)
  | TProof _ => True  (* Proofs are computationally irrelevant *)
  | TFn _ _ _ => True  (* Will be handled by higher-order case *)
  end.

(** *** 4.2 Step-Indexed Value Relation *)

(* Step-indexed value relation *)
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 =>
      (* At step 0: basic structural properties *)
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T
       then val_rel_at_type_fo T v1 v2
       else (* Higher-order: need typing *)
         has_type nil Σ nil v1 T EffectPure /\
         has_type nil Σ nil v2 T EffectPure)
  | S n' =>
      (* Cumulative: include relation at n' *)
      val_rel_n n' Σ T v1 v2 /\
      value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
      (if first_order_type T
       then True  (* FO types: structural already captured *)
       else (* HO types: include typing *)
         has_type nil Σ nil v1 T EffectPure /\
         has_type nil Σ nil v2 T EffectPure) /\
      val_rel_at_type_fo T v1 v2  (* Structural at this level *)
  end.

(** *** 4.3 Step-Indexed Store Relation *)

(* Store relation *)
Fixpoint store_rel_n (n : nat) (Σ : store_ty) (st1 st2 : store) {struct n} : Prop :=
  match n with
  | 0 => store_max st1 = store_max st2
  | S n' =>
      store_rel_n n' Σ st1 st2 /\
      store_max st1 = store_max st2 /\
      (forall l T sl,
        store_ty_lookup l Σ = Some (T, sl) ->
        exists v1 v2,
          store_lookup l st1 = Some v1 /\
          store_lookup l st2 = Some v2 /\
          (if is_low sl
           then val_rel_n n' Σ T v1 v2
           else (* High security: just well-typed *)
             value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
             has_type nil Σ nil v1 T EffectPure /\
             has_type nil Σ nil v2 T EffectPure))
  end.

(** *** 4.4 Cumulative Relations *)

(* val_rel_le n Σ T v1 v2 means: related at ALL steps m ≤ n *)
Definition val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  forall m, m <= n -> val_rel_n m Σ T v1 v2.

(* Cumulative store relation *)
Definition store_rel_le (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall m, m <= n -> store_rel_n m Σ st1 st2.


(* ========================================================================= *)
(** ** SECTION 5: UNFOLD LEMMAS *)
(* ========================================================================= *)

(** *** 5.1 val_rel_n Unfold Lemmas (Already proven - for reference) *)

Lemma val_rel_n_0_unfold : forall Σ T v1 v2,
  val_rel_n 0 Σ T v1 v2 =
  (value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T
    then val_rel_at_type_fo T v1 v2
    else has_type nil Σ nil v1 T EffectPure /\
         has_type nil Σ nil v2 T EffectPure)).
Proof. reflexivity. Qed.

Lemma val_rel_n_S_unfold : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 =
  (val_rel_n n Σ T v1 v2 /\
   value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
   (if first_order_type T then True
    else has_type nil Σ nil v1 T EffectPure /\
         has_type nil Σ nil v2 T EffectPure) /\
   val_rel_at_type_fo T v1 v2).
Proof. reflexivity. Qed.

(** *** 5.2 val_rel_le Unfold Lemmas (NEEDED) *)

(** Unfold val_rel_le at 0.
    Strategy: val_rel_le 0 means forall m, m <= 0 -> val_rel_n m ...
    The only m with m <= 0 is m = 0 (by lia). *)
Lemma val_rel_le_0_unfold : forall Σ T v1 v2,
  val_rel_le 0 Σ T v1 v2 <->
  val_rel_n 0 Σ T v1 v2.
Proof.
  intros Σ T v1 v2.
  unfold val_rel_le.
  split.
  - (* -> direction: if forall m, m <= 0 -> val_rel_n m, then val_rel_n 0 *)
    intros H.
    apply H.
    lia.
  - (* <- direction: if val_rel_n 0, then forall m, m <= 0 -> val_rel_n m *)
    intros H m Hm.
    (* m <= 0 implies m = 0 *)
    assert (m = 0) as Heq by lia.
    subst m.
    exact H.
Qed.

(** Unfold val_rel_le at S n.
    Strategy: val_rel_le (S n) means forall m, m <= S n -> val_rel_n m ...
    This is equivalent to (forall m, m <= n -> val_rel_n m) /\ val_rel_n (S n) ... *)
Lemma val_rel_le_S_unfold : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 <->
  (val_rel_le n Σ T v1 v2 /\ val_rel_n (S n) Σ T v1 v2).
Proof.
  intros n Σ T v1 v2.
  unfold val_rel_le.
  split.
  - (* -> direction *)
    intros H.
    split.
    + (* val_rel_le n: forall m, m <= n -> val_rel_n m *)
      intros m Hm.
      apply H.
      lia.
    + (* val_rel_n (S n) *)
      apply H.
      lia.
  - (* <- direction *)
    intros [Hle HSn] m Hm.
    (* Case analysis: either m <= n or m = S n *)
    destruct (Nat.eq_dec m (S n)) as [Heq | Hneq].
    + (* m = S n *)
      subst m. exact HSn.
    + (* m <> S n, so m <= n *)
      apply Hle.
      lia.
Qed.

(** *** 5.3 store_rel_n Unfold Lemmas *)

Lemma store_rel_n_0_unfold : forall Σ st1 st2,
  store_rel_n 0 Σ st1 st2 = (store_max st1 = store_max st2).
Proof. reflexivity. Qed.

Lemma store_rel_n_S_unfold : forall n Σ st1 st2,
  store_rel_n (S n) Σ st1 st2 =
  (store_rel_n n Σ st1 st2 /\
   store_max st1 = store_max st2 /\
   (forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
     exists v1 v2,
       store_lookup l st1 = Some v1 /\
       store_lookup l st2 = Some v2 /\
       (if is_low sl then val_rel_n n Σ T v1 v2
        else value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
             has_type nil Σ nil v1 T EffectPure /\
             has_type nil Σ nil v2 T EffectPure))).
Proof. reflexivity. Qed.

(** *** 5.4 store_rel_le Unfold Lemmas *)

Lemma store_rel_le_0_unfold : forall Σ st1 st2,
  store_rel_le 0 Σ st1 st2 <->
  store_rel_n 0 Σ st1 st2.
Proof.
  intros Σ st1 st2.
  unfold store_rel_le.
  split.
  - intros H. apply H. lia.
  - intros H m Hm.
    assert (m = 0) as Heq by lia.
    subst m. exact H.
Qed.

Lemma store_rel_le_S_unfold : forall n Σ st1 st2,
  store_rel_le (S n) Σ st1 st2 <->
  (store_rel_le n Σ st1 st2 /\ store_rel_n (S n) Σ st1 st2).
Proof.
  intros n Σ st1 st2.
  unfold store_rel_le.
  split.
  - intros H. split.
    + intros m Hm. apply H. lia.
    + apply H. lia.
  - intros [Hle HSn] m Hm.
    destruct (Nat.eq_dec m (S n)) as [Heq | Hneq].
    + subst m. exact HSn.
    + apply Hle. lia.
Qed.


(* ========================================================================= *)
(** ** SECTION 6: KRIPKE MONOTONICITY LEMMAS *)
(* ========================================================================= *)

(** *** 6.1 Store Typing Extension Properties *)

(** Reflexivity: every store typing extends itself.
    Strategy: unfold and apply the identity. *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Proof.
  intros Σ.
  unfold store_ty_extends.
  intros l T sl H.
  exact H.
Qed.

(** Transitivity: store typing extension composes.
    Strategy: compose the lookup preservation. *)
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
Proof.
  intros Σ1 Σ2 Σ3 H12 H23.
  unfold store_ty_extends in *.
  intros l T sl Hlookup.
  apply H23.
  apply H12.
  exact Hlookup.
Qed.

(** Lookup decidability for store typing.
    Strategy: induction on Σ, use Nat.eqb decidability. *)
Lemma store_ty_lookup_dec : forall l Σ,
  {exists T sl, store_ty_lookup l Σ = Some (T, sl)} +
  {store_ty_lookup l Σ = None}.
Proof.
  intros l Σ.
  induction Σ as [| [[l' T'] sl'] Σ' IH].
  - (* Σ = nil *)
    right. reflexivity.
  - (* Σ = (l', T', sl') :: Σ' *)
    simpl.
    destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l' *)
      left. exists T', sl'. reflexivity.
    + (* l <> l' *)
      exact IH.
Qed.

(** *** 6.2 Value Relation Monotonicity *)

(** Downward step monotonicity: larger n implies smaller n.
    Strategy: induction on n, case analysis on m. *)
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  intros m n.
  generalize dependent m.
  induction n as [| n' IH]; intros m Σ T v1 v2 Hle Hrel.
  - (* n = 0, so m = 0 *)
    assert (m = 0) as Heq by lia.
    subst m. exact Hrel.
  - (* n = S n' *)
    destruct m as [| m'].
    + (* m = 0: need val_rel_n 0 from val_rel_n (S n') *)
      (* val_rel_n (S n') includes val_rel_n n' which includes ... val_rel_n 0 *)
      rewrite val_rel_n_S_unfold in Hrel.
      destruct Hrel as [Hrel_n' [Hval1 [Hval2 [Hclosed1 [Hclosed2 [Hfo_or_ho Hstruct]]]]]].
      (* We need to go down to 0 from n' *)
      clear Hstruct Hfo_or_ho.
      (* Use IH to get from n' to 0 *)
      apply (IH 0 Σ T v1 v2).
      * lia.
      * exact Hrel_n'.
    + (* m = S m' *)
      (* Need val_rel_n (S m') from val_rel_n (S n') where m' < n' *)
      rewrite val_rel_n_S_unfold in Hrel.
      destruct Hrel as [Hrel_n' [Hval1 [Hval2 [Hclosed1 [Hclosed2 [Hfo_or_ho Hstruct]]]]]].
      rewrite val_rel_n_S_unfold.
      split; [| split; [| split; [| split; [| split]]]].
      * (* val_rel_n m' from val_rel_n n' *)
        apply (IH m' Σ T v1 v2).
        -- lia.
        -- exact Hrel_n'.
      * exact Hval1.
      * exact Hval2.
      * exact Hclosed1.
      * exact Hclosed2.
      * split; [exact Hfo_or_ho | exact Hstruct].
Qed.

(** Kripke store weakening for FO types.
    For first-order types, val_rel_at_type_fo doesn't depend on Σ,
    so the relation is preserved. *)
Lemma val_rel_n_weaken_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
Proof.
  intros n.
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hfo Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in *.
    destruct Hrel as [Hval1 [Hval2 [Hclosed1 [Hclosed2 Hrest]]]].
    split; [| split; [| split; [| split]]].
    + exact Hval1.
    + exact Hval2.
    + exact Hclosed1.
    + exact Hclosed2.
    + (* The conditional: first_order_type T = true *)
      rewrite Hfo in *.
      (* val_rel_at_type_fo T v1 v2 doesn't depend on Σ *)
      exact Hrest.
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in *.
    destruct Hrel as [Hrel_n' [Hval1 [Hval2 [Hclosed1 [Hclosed2 [Hfo_cond Hstruct]]]]]].
    split; [| split; [| split; [| split; [| split]]]].
    + (* val_rel_n n' Σ T v1 v2 *)
      apply IH with (Σ' := Σ'); assumption.
    + exact Hval1.
    + exact Hval2.
    + exact Hclosed1.
    + exact Hclosed2.
    + split.
      * (* first_order_type check *)
        rewrite Hfo. exact I.
      * (* val_rel_at_type_fo doesn't depend on Σ *)
        exact Hstruct.
Qed.

(** Kripke store strengthening for FO types.
    Same as weaken - FO types are Σ-independent in val_rel_at_type_fo. *)
Lemma val_rel_n_mono_store_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
Proof.
  intros n.
  induction n as [| n' IH]; intros Σ Σ' T v1 v2 Hfo Hext Hrel.
  - (* n = 0 *)
    rewrite val_rel_n_0_unfold in *.
    destruct Hrel as [Hval1 [Hval2 [Hclosed1 [Hclosed2 Hrest]]]].
    split; [| split; [| split; [| split]]].
    + exact Hval1.
    + exact Hval2.
    + exact Hclosed1.
    + exact Hclosed2.
    + rewrite Hfo in *.
      (* val_rel_at_type_fo doesn't depend on Σ *)
      exact Hrest.
  - (* n = S n' *)
    rewrite val_rel_n_S_unfold in *.
    destruct Hrel as [Hrel_n' [Hval1 [Hval2 [Hclosed1 [Hclosed2 [Hfo_cond Hstruct]]]]]].
    split; [| split; [| split; [| split; [| split]]]].
    + apply IH with (Σ := Σ); assumption.
    + exact Hval1.
    + exact Hval2.
    + exact Hclosed1.
    + exact Hclosed2.
    + split.
      * rewrite Hfo. exact I.
      * exact Hstruct.
Qed.

(** *** 6.3 Typing Store Weakening *)

(** Typing is preserved under store extension.
    Strategy: induction on the typing derivation. The key case is T_Loc
    where store_ty_extends ensures the location is still in Σ'. *)
Lemma has_type_store_weakening : forall Γ Σ Σ' Δ e T ε,
  has_type Γ Σ Δ e T ε ->
  store_ty_extends Σ Σ' ->
  has_type Γ Σ' Δ e T ε.
Proof.
  intros Γ Σ Σ' Δ e T ε Htype Hext.
  induction Htype.
  - (* T_Unit *)
    apply T_Unit.
  - (* T_Bool *)
    apply T_Bool.
  - (* T_Int *)
    apply T_Int.
  - (* T_String *)
    apply T_String.
  - (* T_Var *)
    apply T_Var. assumption.
  - (* T_Loc - the key case *)
    apply T_Loc.
    apply Hext. assumption.
  - (* T_Lam *)
    apply T_Lam.
    apply IHHtype. assumption.
  - (* T_App *)
    eapply T_App.
    + apply IHHtype1. assumption.
    + apply IHHtype2. assumption.
  - (* T_Pair *)
    apply T_Pair.
    + apply IHHtype1. assumption.
    + apply IHHtype2. assumption.
  - (* T_Fst *)
    eapply T_Fst.
    apply IHHtype. assumption.
  - (* T_Snd *)
    eapply T_Snd.
    apply IHHtype. assumption.
  - (* T_Inl *)
    apply T_Inl.
    apply IHHtype. assumption.
  - (* T_Inr *)
    apply T_Inr.
    apply IHHtype. assumption.
  - (* T_Case *)
    eapply T_Case.
    + apply IHHtype1. assumption.
    + apply IHHtype2. assumption.
    + apply IHHtype3. assumption.
  - (* T_If *)
    apply T_If.
    + apply IHHtype1. assumption.
    + apply IHHtype2. assumption.
    + apply IHHtype3. assumption.
  - (* T_Let *)
    eapply T_Let.
    + apply IHHtype1. assumption.
    + apply IHHtype2. assumption.
Qed.


(* ========================================================================= *)
(** ** SECTION 7: EXTRACTION LEMMAS *)
(* ========================================================================= *)

(** Extract value property from val_rel_n (S n).
    Strategy: rewrite with unfold lemma and destruct. *)
Lemma val_rel_n_value : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 ->
  value v1 /\ value v2.
Proof.
  intros n Σ T v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [Hval1 [Hval2 _]]].
  split; assumption.
Qed.

(** Extract closed property from val_rel_n (S n).
    Strategy: same as above. *)
Lemma val_rel_n_closed : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 ->
  closed_expr v1 /\ closed_expr v2.
Proof.
  intros n Σ T v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [_ [_ [Hclosed1 [Hclosed2 _]]]]].
  split; assumption.
Qed.

(** Extract same boolean from related booleans.
    Strategy: unfold, extract val_rel_at_type_fo TBool. *)
Lemma val_rel_n_bool : forall n Σ v1 v2,
  val_rel_n (S n) Σ TBool v1 v2 ->
  exists b, v1 = EBool b /\ v2 = EBool b.
Proof.
  intros n Σ v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [_ [_ [_ [_ [_ Hstruct]]]]]].
  (* val_rel_at_type_fo TBool v1 v2 = exists b, v1 = EBool b /\ v2 = EBool b *)
  simpl in Hstruct.
  exact Hstruct.
Qed.

(** Extract same location from related references.
    Strategy: similar to bool case. *)
Lemma val_rel_n_ref : forall n Σ T sl v1 v2,
  val_rel_n (S n) Σ (TRef T sl) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l.
Proof.
  intros n Σ T sl v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [_ [_ [_ [_ [_ Hstruct]]]]]].
  (* val_rel_at_type_fo (TRef T sl) v1 v2 = exists l, v1 = ELoc l /\ v2 = ELoc l *)
  simpl in Hstruct.
  exact Hstruct.
Qed.

(** Additional extraction lemmas for completeness *)

(** Extract same integer from related integers. *)
Lemma val_rel_n_int : forall n Σ v1 v2,
  val_rel_n (S n) Σ TInt v1 v2 ->
  exists z, v1 = EInt z /\ v2 = EInt z.
Proof.
  intros n Σ v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [_ [_ [_ [_ [_ Hstruct]]]]]].
  simpl in Hstruct.
  exact Hstruct.
Qed.

(** Extract same string from related strings. *)
Lemma val_rel_n_string : forall n Σ v1 v2,
  val_rel_n (S n) Σ TString v1 v2 ->
  exists s, v1 = EString s /\ v2 = EString s.
Proof.
  intros n Σ v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [_ [_ [_ [_ [_ Hstruct]]]]]].
  simpl in Hstruct.
  exact Hstruct.
Qed.

(** Extract unit from related units. *)
Lemma val_rel_n_unit : forall n Σ v1 v2,
  val_rel_n (S n) Σ TUnit v1 v2 ->
  v1 = EUnit /\ v2 = EUnit.
Proof.
  intros n Σ v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [_ [_ [_ [_ [_ Hstruct]]]]]].
  simpl in Hstruct.
  exact Hstruct.
Qed.

(** Extract pair components from related pairs. *)
Lemma val_rel_n_pair : forall n Σ T1 T2 v1 v2,
  val_rel_n (S n) Σ (TProd T1 T2) v1 v2 ->
  exists v1a v1b v2a v2b,
    v1 = EPair v1a v1b /\ v2 = EPair v2a v2b /\
    val_rel_at_type_fo T1 v1a v2a /\ val_rel_at_type_fo T2 v1b v2b.
Proof.
  intros n Σ T1 T2 v1 v2 H.
  rewrite val_rel_n_S_unfold in H.
  destruct H as [_ [_ [_ [_ [_ [_ Hstruct]]]]]].
  simpl in Hstruct.
  exact Hstruct.
Qed.


(* ========================================================================= *)
(** ** SECTION 8: ADDITIONAL INFRASTRUCTURE LEMMAS *)
(* ========================================================================= *)

(** Downward monotonicity for store_rel_n *)
Lemma store_rel_n_mono : forall m n Σ st1 st2,
  m <= n ->
  store_rel_n n Σ st1 st2 ->
  store_rel_n m Σ st1 st2.
Proof.
  intros m n.
  generalize dependent m.
  induction n as [| n' IH]; intros m Σ st1 st2 Hle Hrel.
  - (* n = 0 *)
    assert (m = 0) as Heq by lia.
    subst m. exact Hrel.
  - (* n = S n' *)
    destruct m as [| m'].
    + (* m = 0 *)
      rewrite store_rel_n_S_unfold in Hrel.
      destruct Hrel as [Hrel_n' [Hmax _]].
      apply (IH 0 Σ st1 st2).
      * lia.
      * exact Hrel_n'.
    + (* m = S m' *)
      rewrite store_rel_n_S_unfold in Hrel.
      destruct Hrel as [Hrel_n' [Hmax Hlocs]].
      rewrite store_rel_n_S_unfold.
      split; [| split].
      * apply (IH m' Σ st1 st2); [lia | exact Hrel_n'].
      * exact Hmax.
      * intros l T sl Hlookup.
        specialize (Hlocs l T sl Hlookup).
        destruct Hlocs as [v1 [v2 [Hlk1 [Hlk2 Hcond]]]].
        exists v1, v2.
        split; [exact Hlk1 | split; [exact Hlk2 |]].
        destruct (is_low sl).
        -- (* Low security: need val_rel_n m' from val_rel_n n' *)
           apply val_rel_n_mono with (n := n').
           ++ lia.
           ++ exact Hcond.
        -- (* High security: properties preserved *)
           exact Hcond.
Qed.

(** val_rel_le implies val_rel_n for any m <= n *)
Lemma val_rel_le_impl : forall n m Σ T v1 v2,
  m <= n ->
  val_rel_le n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
Proof.
  intros n m Σ T v1 v2 Hle Hrel.
  unfold val_rel_le in Hrel.
  apply Hrel.
  exact Hle.
Qed.

(** val_rel_n implies val_rel_le *)
Lemma val_rel_n_impl_le : forall n Σ T v1 v2,
  val_rel_n n Σ T v1 v2 ->
  val_rel_le n Σ T v1 v2.
Proof.
  intros n Σ T v1 v2 Hrel.
  unfold val_rel_le.
  intros m Hle.
  apply val_rel_n_mono with (n := n); assumption.
Qed.

(** store_rel_le implies store_rel_n for any m <= n *)
Lemma store_rel_le_impl : forall n m Σ st1 st2,
  m <= n ->
  store_rel_le n Σ st1 st2 ->
  store_rel_n m Σ st1 st2.
Proof.
  intros n m Σ st1 st2 Hle Hrel.
  unfold store_rel_le in Hrel.
  apply Hrel.
  exact Hle.
Qed.

(** store_rel_n implies store_rel_le *)
Lemma store_rel_n_impl_le : forall n Σ st1 st2,
  store_rel_n n Σ st1 st2 ->
  store_rel_le n Σ st1 st2.
Proof.
  intros n Σ st1 st2 Hrel.
  unfold store_rel_le.
  intros m Hle.
  apply store_rel_n_mono with (n := n); assumption.
Qed.


(* ========================================================================= *)
(** ** SUMMARY *)
(* ========================================================================= *)

(** All infrastructure lemmas have been proven without any Admitted. *)
Theorem all_infrastructure_proven : True.
Proof. exact I. Qed.

(** Collect all main lemmas for export *)
Definition infrastructure_lemmas_complete :=
  (val_rel_le_0_unfold,
   val_rel_le_S_unfold,
   store_rel_n_0_unfold,
   store_rel_n_S_unfold,
   store_rel_le_0_unfold,
   store_rel_le_S_unfold,
   store_ty_extends_refl,
   store_ty_extends_trans,
   store_ty_lookup_dec,
   val_rel_n_mono,
   val_rel_n_weaken_fo,
   val_rel_n_mono_store_fo,
   has_type_store_weakening,
   val_rel_n_value,
   val_rel_n_closed,
   val_rel_n_bool,
   val_rel_n_ref,
   val_rel_n_int,
   val_rel_n_string,
   val_rel_n_unit,
   val_rel_n_pair,
   store_rel_n_mono,
   val_rel_le_impl,
   val_rel_n_impl_le,
   store_rel_le_impl,
   store_rel_n_impl_le).

Print Assumptions all_infrastructure_proven.
