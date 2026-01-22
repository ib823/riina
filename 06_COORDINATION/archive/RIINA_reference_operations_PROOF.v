(** * RIINA: Reference Operations Proofs
    
    Three theorems about reference operations:
    1. exp_rel_step1_ref    - Reference creation allocates to SAME location
    2. exp_rel_step1_deref  - Dereference retrieves stored values
    3. exp_rel_step1_assign - Assignment produces EUnit and preserves store relation
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | EXTREME RIGOUR
    
    Generated: 2026-01-19
    Status: COMPLETE - Qed - ZERO AXIOMS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Import ListNotations.

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
  | TRef : ty -> security_level -> ty
  | TSecret : ty -> ty
  | TLabeled : ty -> label -> ty.

(** ========================================================================
    EXPRESSION DEFINITION
    ======================================================================== *)

Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : Z -> expr
  | EString : string -> expr
  | ELoc : nat -> expr
  | EVar : ident -> expr
  | ELam : ident -> ty -> expr -> expr
  | EApp : expr -> expr -> expr
  | EPair : expr -> expr -> expr
  | EFst : expr -> expr
  | ESnd : expr -> expr
  | EInl : expr -> ty -> expr
  | EInr : expr -> ty -> expr
  | ECase : expr -> ident -> expr -> ident -> expr -> expr
  | EIf : expr -> expr -> expr -> expr
  | ELet : ident -> expr -> expr -> expr
  | ERef : expr -> security_level -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr.

(** ========================================================================
    VALUE PREDICATE
    ======================================================================== *)

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

(** ========================================================================
    STORE DEFINITIONS
    ======================================================================== *)

Definition store := list (loc * expr).
Definition store_ty := list (loc * ty * security_level).
Definition effect_ctx := list effect.

(** Lookup value at location in store *)
Fixpoint store_lookup (l : loc) (st : store) : option expr :=
  match st with
  | nil => None
  | (l', v) :: st' => if Nat.eqb l l' then Some v else store_lookup l st'
  end.

(** Store size (number of entries) *)
Definition store_size (st : store) : nat := length st.

(** Fresh location: based on store size *)
Definition fresh_loc (st : store) : loc := store_size st.

(** Extend store with new value at fresh location *)
Definition store_extend (v : expr) (st : store) : store := 
  st ++ ((fresh_loc st, v) :: nil).

(** Update store at location *)
Fixpoint store_update (l : loc) (v : expr) (st : store) : store :=
  match st with
  | nil => (l, v) :: nil
  | (l', v') :: st' =>
      if Nat.eqb l l' then (l, v) :: st' else (l', v') :: store_update l v st'
  end.

(** Store relation: same size ensures same fresh location *)
Definition store_rel_n_base (Sigma : store_ty) (st1 st2 : store) : Prop :=
  store_size st1 = store_size st2.

(** ========================================================================
    SUBSTITUTION
    ======================================================================== *)

Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
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
    OPERATIONAL SEMANTICS
    ======================================================================== *)

Reserved Notation "cfg1 '-->' cfg2" (at level 40).

Inductive step : (expr * store * effect_ctx) -> (expr * store * effect_ctx) -> Prop :=
  (* REFERENCE CREATION - uses store_extend *)
  | ST_RefValue : forall v sl st ctx,
      value v ->
      (ERef v sl, st, ctx) --> (ELoc (fresh_loc st), store_extend v st, ctx)
  
  (* DEREFERENCE *)
  | ST_DerefLoc : forall v l st ctx,
      store_lookup l st = Some v ->
      (EDeref (ELoc l), st, ctx) --> (v, st, ctx)
  
  (* ASSIGNMENT *)
  | ST_AssignLoc : forall l st ctx v1 v2,
      store_lookup l st = Some v1 ->
      value v2 ->
      (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)
  
  (* Other rules *)
  | ST_AppAbs : forall x T body v st ctx,
      value v ->
      (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
  
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
      (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)
  
  | ST_CaseInl : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
  
  | ST_CaseInr : forall v T x1 e1 x2 e2 st ctx,
      value v ->
      (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)

where "cfg1 '-->' cfg2" := (step cfg1 cfg2).

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

(** ========================================================================
    HELPER LEMMAS
    ======================================================================== *)

(** Related stores have same fresh location *)
Lemma store_rel_fresh_eq : forall Sigma st1 st2,
  store_rel_n_base Sigma st1 st2 ->
  fresh_loc st1 = fresh_loc st2.
Proof.
  intros Sigma st1 st2 Hrel.
  unfold store_rel_n_base, fresh_loc, store_size in *.
  exact Hrel.
Qed.

(** Store extend increases size by 1 *)
Lemma store_extend_size : forall v st,
  store_size (store_extend v st) = S (store_size st).
Proof.
  intros v st.
  unfold store_extend, store_size, fresh_loc.
  rewrite app_length.
  simpl. 
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(** Store update preserves size - needed for assign *)
Lemma store_update_size_helper : forall l v st,
  store_size (store_update l v st) <= S (store_size st).
Proof.
  intros l v st.
  unfold store_size.
  induction st as [| [l' v'] st' IH].
  - simpl. apply Nat.le_refl.
  - simpl. destruct (Nat.eqb l l') eqn:Heq.
    + (* l = l', update in place, size stays same *)
      simpl. apply le_S. apply Nat.le_refl.
    + (* l <> l', recurse *)
      simpl. apply le_n_S. 
      apply Nat.le_trans with (S (length st')).
      * exact IH.
      * apply Nat.le_refl.
Qed.

(** Store lookup implies entry exists in store *)
Lemma store_lookup_in : forall l st v,
  store_lookup l st = Some v ->
  In (l, v) st.
Proof.
  intros l st v.
  induction st as [| [l' v'] st' IH].
  - simpl. intros H. discriminate.
  - simpl. destruct (Nat.eqb l l') eqn:Heq.
    + intros H. injection H as H'. subst.
      apply Nat.eqb_eq in Heq. subst.
      left. reflexivity.
    + intros H. right. apply IH. exact H.
Qed.

(** If entry is in store, update at that location preserves size *)
Lemma store_update_preserves_size : forall l v st,
  (exists v', In (l, v') st) ->
  store_size (store_update l v st) = store_size st.
Proof.
  intros l v st [v' Hin].
  unfold store_size.
  induction st as [| [l' v''] st' IH].
  - inversion Hin.
  - simpl in Hin. destruct Hin as [Heq | Hin'].
    + injection Heq as Hl Hv. subst l'.
      simpl. rewrite Nat.eqb_refl. simpl. reflexivity.
    + simpl. destruct (Nat.eqb l l') eqn:Heq'.
      * simpl. reflexivity.
      * simpl. f_equal. apply IH. exact Hin'.
Qed.

(** ========================================================================
    THEOREM 1: exp_rel_step1_ref (Reference Creation)
    ======================================================================== *)

Theorem exp_rel_step1_ref : forall Sigma sl v v' st1 st2 ctx,
  value v -> value v' ->
  store_rel_n_base Sigma st1 st2 ->
  exists l st1' st2' ctx',
    (ERef v sl, st1, ctx) -->* (ELoc l, st1', ctx') /\
    (ERef v' sl, st2, ctx) -->* (ELoc l, st2', ctx') /\
    store_rel_n_base Sigma st1' st2'.
Proof.
  intros Sigma sl v v' st1 st2 ctx Hv1 Hv2 Hstore.

  (* Establish that fresh_loc is the same in both stores *)
  assert (Hfresh_eq : fresh_loc st1 = fresh_loc st2).
  { apply store_rel_fresh_eq with (Sigma := Sigma). exact Hstore. }

  (* Provide witnesses *)
  exists (fresh_loc st1), (store_extend v st1), (store_extend v' st2), ctx.

  split.
  (* First allocation *)
  - apply MS_Step with (cfg2 := (ELoc (fresh_loc st1), store_extend v st1, ctx)).
    + apply ST_RefValue. exact Hv1.
    + apply MS_Refl.

  - split.
    (* Second allocation *)
    + apply MS_Step with (cfg2 := (ELoc (fresh_loc st2), store_extend v' st2, ctx)).
      * apply ST_RefValue. exact Hv2.
      * rewrite <- Hfresh_eq. apply MS_Refl.

    (* Store relation preserved *)
    + unfold store_rel_n_base.
      unfold store_rel_n_base in Hstore.
      rewrite store_extend_size.
      rewrite store_extend_size.
      rewrite Hstore.
      reflexivity.
Qed.

(** ========================================================================
    THEOREM 2: exp_rel_step1_deref (Dereference)
    ======================================================================== *)

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
  (* First dereference *)
  - apply MS_Step with (cfg2 := (v1, st1, ctx)).
    + apply ST_DerefLoc. exact Hlook1.
    + apply MS_Refl.

  - split.
    (* Second dereference *)
    + apply MS_Step with (cfg2 := (v2, st2, ctx)).
      * apply ST_DerefLoc. exact Hlook2.
      * apply MS_Refl.

    (* Store relation preserved - stores unchanged *)
    + exact Hstore.
Qed.

(** ========================================================================
    THEOREM 3: exp_rel_step1_assign (Assignment)
    ======================================================================== *)

Theorem exp_rel_step1_assign : forall Sigma l v v' st1 st2 ctx,
  value v -> value v' ->
  store_lookup l st1 <> None ->
  store_lookup l st2 <> None ->
  store_rel_n_base Sigma st1 st2 ->
  exists st1' st2' ctx',
    (EAssign (ELoc l) v, st1, ctx) -->* (EUnit, st1', ctx') /\
    (EAssign (ELoc l) v', st2, ctx) -->* (EUnit, st2', ctx') /\
    store_rel_n_base Sigma st1' st2'.
Proof.
  intros Sigma l v v' st1 st2 ctx Hv1 Hv2 Hexists1 Hexists2 Hstore.

  (* Extract the existing values at location l *)
  destruct (store_lookup l st1) as [old1|] eqn:Hlook1.
  2: { exfalso. apply Hexists1. reflexivity. }
  destruct (store_lookup l st2) as [old2|] eqn:Hlook2.
  2: { exfalso. apply Hexists2. reflexivity. }

  (* Provide witnesses *)
  exists (store_update l v st1), (store_update l v' st2), ctx.

  split.
  (* First assignment *)
  - apply MS_Step with (cfg2 := (EUnit, store_update l v st1, ctx)).
    + apply ST_AssignLoc with (v1 := old1).
      * exact Hlook1.
      * exact Hv1.
    + apply MS_Refl.

  - split.
    (* Second assignment *)
    + apply MS_Step with (cfg2 := (EUnit, store_update l v' st2, ctx)).
      * apply ST_AssignLoc with (v1 := old2).
        -- exact Hlook2.
        -- exact Hv2.
      * apply MS_Refl.

    (* Store relation preserved *)
    + unfold store_rel_n_base.
      unfold store_rel_n_base in Hstore.
      (* Use the fact that l exists in both stores *)
      rewrite store_update_preserves_size.
      * rewrite store_update_preserves_size.
        -- exact Hstore.
        -- exists old2. apply store_lookup_in. exact Hlook2.
      * exists old1. apply store_lookup_in. exact Hlook1.
Qed.

(** ========================================================================
    VERIFICATION — ZERO AXIOMS
    ======================================================================== *)

Print Assumptions store_rel_fresh_eq.
Print Assumptions exp_rel_step1_ref.
Print Assumptions exp_rel_step1_deref.
Print Assumptions exp_rel_step1_assign.

(** End of RIINA_reference_operations_PROOF.v *)
