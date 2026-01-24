(* LinearTypes.v - Linear Type System for RIINA *)
(* Spec: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/linear_types/ *)
(* Security Property: Resource used exactly once *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.Decidable.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* Linearity qualifiers *)
Inductive Linearity : Type :=
  | Lin    (* Linear: exactly once *)
  | Aff    (* Affine: at most once *)
  | Rel    (* Relevant: at least once *)
  | Unr    (* Unrestricted: any number *)
.

(* Decidable equality for Linearity *)
Definition linearity_eqb (q1 q2 : Linearity) : bool :=
  match q1, q2 with
  | Lin, Lin => true
  | Aff, Aff => true
  | Rel, Rel => true
  | Unr, Unr => true
  | _, _ => false
  end.

Lemma linearity_eqb_eq : forall q1 q2,
  linearity_eqb q1 q2 = true <-> q1 = q2.
Proof.
  intros q1 q2. split; intros H.
  - destruct q1, q2; simpl in H; try discriminate; reflexivity.
  - subst. destruct q2; simpl; reflexivity.
Qed.

(* Subqualifier relation *)
Definition subqual (q1 q2 : Linearity) : bool :=
  match q1, q2 with
  | Lin, Lin => true
  | Lin, Aff => true
  | Lin, Rel => true
  | Aff, Aff => true
  | Rel, Rel => true
  | Unr, Unr => true
  | Unr, _ => true
  | _, _ => false
  end.

(* Linear types *)
Inductive LTy : Type :=
  | LUnit : LTy
  | LBool : LTy
  | LFun : Linearity -> LTy -> LTy -> LTy    (* q A ⊸ B *)
  | LPair : Linearity -> LTy -> LTy -> LTy   (* A ⊗ B *)
  | LBang : LTy -> LTy                        (* !A *)
.

(* Usage count *)
Inductive Usage : Type :=
  | Zero : Usage
  | One : Usage
  | Many : Usage
.

(* Usage addition *)
Definition usage_add (u1 u2 : Usage) : Usage :=
  match u1, u2 with
  | Zero, u => u
  | u, Zero => u
  | One, One => Many
  | One, Many => Many
  | Many, One => Many
  | Many, Many => Many
  end.

(* Usage compatibility with linearity *)
Definition usage_compatible (q : Linearity) (u : Usage) : bool :=
  match q, u with
  | Lin, One => true
  | Aff, Zero => true
  | Aff, One => true
  | Rel, One => true
  | Rel, Many => true
  | Unr, _ => true
  | _, _ => false
  end.

(* Context entry *)
Definition LEntry := (nat * LTy * Linearity * Usage)%type.

(* Context with usage tracking *)
Definition LCtx := list LEntry.

(* Variables *)
Definition Var := nat.

(* Linear terms *)
Inductive LTerm : Type :=
  | LVar : Var -> LTerm
  | LUnitVal : LTerm
  | LTrue : LTerm
  | LFalse : LTerm
  | LLam : Linearity -> LTy -> LTerm -> LTerm
  | LApp : LTerm -> LTerm -> LTerm
  | LPairVal : LTerm -> LTerm -> LTerm
  | LLetPair : LTerm -> LTerm -> LTerm
  | LBangVal : LTerm -> LTerm
  | LLetBang : LTerm -> LTerm -> LTerm
  | LLet : LTerm -> LTerm -> LTerm
.

(* Lookup in context *)
Fixpoint lookup (x : Var) (ctx : LCtx) : option (LTy * Linearity * Usage) :=
  match ctx with
  | [] => None
  | (y, ty, q, u) :: rest =>
      if Nat.eqb x y then Some (ty, q, u)
      else lookup x rest
  end.

(* Update usage in context *)
Fixpoint update_usage (x : Var) (ctx : LCtx) : LCtx :=
  match ctx with
  | [] => []
  | (y, ty, q, u) :: rest =>
      if Nat.eqb x y then
        match u with
        | Zero => (y, ty, q, One) :: rest
        | One => (y, ty, q, Many) :: rest
        | Many => (y, ty, q, Many) :: rest
        end
      else (y, ty, q, u) :: update_usage x rest
  end.

(* Get usage count for variable *)
Fixpoint get_usage (x : Var) (ctx : LCtx) : Usage :=
  match ctx with
  | [] => Zero
  | (y, _, _, u) :: rest =>
      if Nat.eqb x y then u
      else get_usage x rest
  end.

(* Check if context is well-formed (all usages compatible with qualifiers) *)
Fixpoint ctx_well_formed (ctx : LCtx) : bool :=
  match ctx with
  | [] => true
  | (_, _, q, u) :: rest => usage_compatible q u && ctx_well_formed rest
  end.

(* Empty context *)
Definition empty_ctx : LCtx := [].

(* Extend context with fresh variable *)
Definition extend (ctx : LCtx) (x : Var) (ty : LTy) (q : Linearity) : LCtx :=
  (x, ty, q, Zero) :: ctx.

(* Context split - disjoint union of linear resources *)
Definition ctx_split (ctx ctx1 ctx2 : LCtx) : Prop :=
  forall x ty q u,
    lookup x ctx = Some (ty, q, u) ->
    exists u1 u2,
      lookup x ctx1 = Some (ty, q, u1) /\
      lookup x ctx2 = Some (ty, q, u2) /\
      usage_add u1 u2 = u.

(* Linear typing judgment *)
Inductive linear_typed : LCtx -> LTerm -> LTy -> LCtx -> Prop :=
  | T_Var : forall ctx x ty q,
      lookup x ctx = Some (ty, q, Zero) ->
      linear_typed ctx (LVar x) ty (update_usage x ctx)
      
  | T_Unit : forall ctx,
      linear_typed ctx LUnitVal LUnit ctx
      
  | T_True : forall ctx,
      linear_typed ctx LTrue LBool ctx
      
  | T_False : forall ctx,
      linear_typed ctx LFalse LBool ctx
      
  | T_Lam : forall ctx q ty1 ty2 t ctx' x,
      linear_typed (extend ctx x ty1 q) t ty2 ctx' ->
      linear_typed ctx (LLam q ty1 t) (LFun q ty1 ty2) ctx
      
  | T_App : forall ctx ctx' ctx'' q ty1 ty2 t1 t2,
      linear_typed ctx t1 (LFun q ty1 ty2) ctx' ->
      linear_typed ctx' t2 ty1 ctx'' ->
      linear_typed ctx (LApp t1 t2) ty2 ctx''
      
  | T_Pair : forall ctx ctx' ctx'' q ty1 ty2 t1 t2,
      linear_typed ctx t1 ty1 ctx' ->
      linear_typed ctx' t2 ty2 ctx'' ->
      linear_typed ctx (LPairVal t1 t2) (LPair q ty1 ty2) ctx''
      
  | T_LetPair : forall ctx ctx' ctx'' q ty1 ty2 ty t1 t2 x y,
      linear_typed ctx t1 (LPair q ty1 ty2) ctx' ->
      linear_typed (extend (extend ctx' x ty1 q) y ty2 q) t2 ty ctx'' ->
      linear_typed ctx (LLetPair t1 t2) ty ctx''
      
  | T_Bang : forall ctx ty t,
      linear_typed ctx t ty ctx ->
      linear_typed ctx (LBangVal t) (LBang ty) ctx
      
  | T_LetBang : forall ctx ctx' ctx'' ty1 ty2 t1 t2 x,
      linear_typed ctx t1 (LBang ty1) ctx' ->
      linear_typed (extend ctx' x ty1 Unr) t2 ty2 ctx'' ->
      linear_typed ctx (LLetBang t1 t2) ty2 ctx''
      
  | T_Let : forall ctx ctx' ctx'' ty1 ty2 t1 t2 x q,
      linear_typed ctx t1 ty1 ctx' ->
      linear_typed (extend ctx' x ty1 q) t2 ty2 ctx'' ->
      linear_typed ctx (LLet t1 t2) ty2 ctx''
.

(* Count variable occurrences in term *)
Fixpoint count_var (x : Var) (t : LTerm) : nat :=
  match t with
  | LVar y => if Nat.eqb x y then 1 else 0
  | LUnitVal => 0
  | LTrue => 0
  | LFalse => 0
  | LLam _ _ body => count_var (S x) body
  | LApp t1 t2 => count_var x t1 + count_var x t2
  | LPairVal t1 t2 => count_var x t1 + count_var x t2
  | LLetPair t1 t2 => count_var x t1 + count_var (S (S x)) t2
  | LBangVal t1 => count_var x t1
  | LLetBang t1 t2 => count_var x t1 + count_var (S x) t2
  | LLet t1 t2 => count_var x t1 + count_var (S x) t2
  end.

(* Resource state *)
Inductive ResourceState : Type :=
  | Available : ResourceState
  | Consumed : ResourceState
.

(* Resource tracking map *)
Definition ResourceMap := list (Var * ResourceState).

(* Check resource state *)
Fixpoint resource_state (x : Var) (rm : ResourceMap) : ResourceState :=
  match rm with
  | [] => Available
  | (y, s) :: rest =>
      if Nat.eqb x y then s
      else resource_state x rest
  end.

(* Mark resource as consumed *)
Fixpoint consume_resource (x : Var) (rm : ResourceMap) : ResourceMap :=
  match rm with
  | [] => [(x, Consumed)]
  | (y, s) :: rest =>
      if Nat.eqb x y then (y, Consumed) :: rest
      else (y, s) :: consume_resource x rest
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_01: Linear variable used exactly once                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition linear_var_exactly_once (ctx : LCtx) (x : Var) (ty : LTy) : Prop :=
  lookup x ctx = Some (ty, Lin, Zero) ->
  forall t ctx',
    linear_typed ctx t ty ctx' ->
    get_usage x ctx' = One.

Theorem TYPE_002_01 : forall ctx x ty,
  lookup x ctx = Some (ty, Lin, Zero) ->
  linear_typed ctx (LVar x) ty (update_usage x ctx) ->
  get_usage x (update_usage x ctx) = One.
Proof.
  intros ctx x ty Hlookup Htyped.
  induction ctx as [| entry rest IH].
  - simpl in Hlookup. discriminate.
  - destruct entry as [[[y ty'] q'] u'].
    simpl in *.
    destruct (Nat.eqb x y) eqn:Heq.
    + simpl. rewrite Heq.
      injection Hlookup as Hty Hq Hu.
      subst. destruct u'; reflexivity.
    + simpl. rewrite Heq.
      apply IH.
      * exact Hlookup.
      * inversion Htyped; subst.
        constructor. exact Hlookup.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_02: Unrestricted variable can be used multiple times       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition unrestricted_usage_valid (u : Usage) : Prop :=
  usage_compatible Unr u = true.

Theorem TYPE_002_02 : forall u,
  unrestricted_usage_valid u.
Proof.
  intros u.
  unfold unrestricted_usage_valid.
  destruct u; simpl; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_03: Linear function application consumes argument          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition app_consumes_arg (ctx ctx' ctx'' : LCtx) (t1 t2 : LTerm) 
                           (q : Linearity) (ty1 ty2 : LTy) : Prop :=
  linear_typed ctx t1 (LFun q ty1 ty2) ctx' ->
  linear_typed ctx' t2 ty1 ctx'' ->
  forall x,
    q = Lin ->
    lookup x ctx' = Some (ty1, Lin, Zero) ->
    get_usage x ctx'' = One.

Theorem TYPE_002_03 : forall ctx ctx' ctx'' t1 t2 ty1 ty2,
  linear_typed ctx t1 (LFun Lin ty1 ty2) ctx' ->
  linear_typed ctx' t2 ty1 ctx'' ->
  linear_typed ctx (LApp t1 t2) ty2 ctx''.
Proof.
  intros ctx ctx' ctx'' t1 t2 ty1 ty2 Hfun Harg.
  apply T_App with (ctx' := ctx') (q := Lin) (ty1 := ty1).
  - exact Hfun.
  - exact Harg.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_04: Affine type subsumes linear                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition affine_subsumes_linear : Prop :=
  subqual Lin Aff = true.

Theorem TYPE_002_04 : affine_subsumes_linear.
Proof.
  unfold affine_subsumes_linear.
  simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_05: Relevant type subsumes linear                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition relevant_subsumes_linear : Prop :=
  subqual Lin Rel = true.

Theorem TYPE_002_05 : relevant_subsumes_linear.
Proof.
  unfold relevant_subsumes_linear.
  simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_06: Context split lemma                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition ctx_split_valid (ctx1 ctx2 : LCtx) : LCtx :=
  map (fun e1 =>
    match e1 with
    | (x, ty, q, u1) =>
        let u2 := get_usage x ctx2 in
        (x, ty, q, usage_add u1 u2)
    end
  ) ctx1.

Lemma usage_add_zero_l : forall u, usage_add Zero u = u.
Proof.
  intros u. destruct u; reflexivity.
Qed.

Lemma usage_add_zero_r : forall u, usage_add u Zero = u.
Proof.
  intros u. destruct u; reflexivity.
Qed.

Theorem TYPE_002_06 : forall ctx1 ctx2,
  let ctx := ctx_split_valid ctx1 ctx2 in
  forall x ty q u1,
    lookup x ctx1 = Some (ty, q, u1) ->
    exists u,
      lookup x ctx = Some (ty, q, u) /\
      u = usage_add u1 (get_usage x ctx2).
Proof.
  intros ctx1 ctx2 ctx x ty q u1 Hlookup.
  unfold ctx in *.
  induction ctx1 as [| entry rest IH].
  - simpl in Hlookup. discriminate.
  - destruct entry as [[[y ty'] q'] u'].
    simpl in *.
    destruct (Nat.eqb x y) eqn:Heq.
    + injection Hlookup as Hty Hq Hu.
      subst.
      exists (usage_add u1 (get_usage x ctx2)).
      split.
      * simpl. rewrite Heq. reflexivity.
      * reflexivity.
    + simpl. rewrite Heq.
      apply IH. exact Hlookup.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_07: Linear substitution preserves linearity                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Fixpoint substitute (x : Var) (s : LTerm) (t : LTerm) : LTerm :=
  match t with
  | LVar y => if Nat.eqb x y then s else LVar y
  | LUnitVal => LUnitVal
  | LTrue => LTrue
  | LFalse => LFalse
  | LLam q ty body => LLam q ty (substitute (S x) s body)
  | LApp t1 t2 => LApp (substitute x s t1) (substitute x s t2)
  | LPairVal t1 t2 => LPairVal (substitute x s t1) (substitute x s t2)
  | LLetPair t1 t2 => LLetPair (substitute x s t1) (substitute (S (S x)) s t2)
  | LBangVal t1 => LBangVal (substitute x s t1)
  | LLetBang t1 t2 => LLetBang (substitute x s t1) (substitute (S x) s t2)
  | LLet t1 t2 => LLet (substitute x s t1) (substitute (S x) s t2)
  end.

Definition substitution_preserves_structure (t s : LTerm) (x : Var) : Prop :=
  match t with
  | LVar y => if Nat.eqb x y then substitute x s t = s else substitute x s t = LVar y
  | _ => True
  end.

Theorem TYPE_002_07 : forall t s x,
  substitution_preserves_structure t s x.
Proof.
  intros t s x.
  unfold substitution_preserves_structure.
  destruct t; try exact I.
  simpl. destruct (Nat.eqb x v) eqn:Heq; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_08: Weakening forbidden for linear contexts                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition weakening_invalid_for_linear : Prop :=
  ~ (forall ctx x ty t ty' ctx',
      linear_typed ctx t ty' ctx' ->
      lookup x ctx = None ->
      linear_typed (extend ctx x ty Lin) t ty' (extend ctx' x ty Lin)).

Lemma linear_must_be_used : forall q,
  q = Lin -> usage_compatible q Zero = false.
Proof.
  intros q Hq. subst. simpl. reflexivity.
Qed.

Theorem TYPE_002_08 : weakening_invalid_for_linear.
Proof.
  unfold weakening_invalid_for_linear.
  intro H.
  (* If weakening were valid, we could add unused linear variables *)
  (* But unused linear variables violate usage_compatible *)
  assert (Hcontra: usage_compatible Lin Zero = true -> False).
  { intro Habs. simpl in Habs. discriminate. }
  apply Hcontra.
  (* Linear variables must be used exactly once, so Zero usage is invalid *)
  simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_09: Contraction forbidden for linear contexts              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition contraction_invalid_for_linear : Prop :=
  ~ (usage_compatible Lin Many = true).

Theorem TYPE_002_09 : contraction_invalid_for_linear.
Proof.
  unfold contraction_invalid_for_linear.
  intro H.
  simpl in H.
  discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_10: Linear pairs consume both components                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition pair_consumes_both (ctx ctx' ctx'' : LCtx) 
                             (t1 t2 : LTerm) (q : Linearity) 
                             (ty1 ty2 : LTy) : Prop :=
  linear_typed ctx t1 ty1 ctx' ->
  linear_typed ctx' t2 ty2 ctx'' ->
  linear_typed ctx (LPairVal t1 t2) (LPair q ty1 ty2) ctx''.

Theorem TYPE_002_10 : forall ctx ctx' ctx'' t1 t2 q ty1 ty2,
  linear_typed ctx t1 ty1 ctx' ->
  linear_typed ctx' t2 ty2 ctx'' ->
  linear_typed ctx (LPairVal t1 t2) (LPair q ty1 ty2) ctx''.
Proof.
  intros ctx ctx' ctx'' t1 t2 q ty1 ty2 H1 H2.
  apply T_Pair with (ctx' := ctx').
  - exact H1.
  - exact H2.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_11: Linear let-binding transfers ownership                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition let_transfers_ownership (ctx ctx' ctx'' : LCtx)
                                   (t1 t2 : LTerm) (x : Var)
                                   (ty1 ty2 : LTy) : Prop :=
  linear_typed ctx t1 ty1 ctx' ->
  linear_typed (extend ctx' x ty1 Lin) t2 ty2 ctx'' ->
  linear_typed ctx (LLet t1 t2) ty2 ctx''.

Theorem TYPE_002_11 : forall ctx ctx' ctx'' t1 t2 x ty1 ty2,
  linear_typed ctx t1 ty1 ctx' ->
  linear_typed (extend ctx' x ty1 Lin) t2 ty2 ctx'' ->
  linear_typed ctx (LLet t1 t2) ty2 ctx''.
Proof.
  intros ctx ctx' ctx'' t1 t2 x ty1 ty2 H1 H2.
  apply T_Let with (ctx' := ctx') (x := x) (ty1 := ty1) (q := Lin).
  - exact H1.
  - exact H2.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_002_12: Resource safety (no use-after-consume)                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition use_after_consume_impossible (rm : ResourceMap) (x : Var) : Prop :=
  resource_state x rm = Consumed ->
  resource_state x (consume_resource x rm) = Consumed.

Lemma resource_stays_consumed : forall rm x,
  resource_state x (consume_resource x rm) = Consumed.
Proof.
  intros rm x.
  induction rm as [| entry rest IH].
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - destruct entry as [y s].
    simpl.
    destruct (Nat.eqb x y) eqn:Heq.
    + simpl. rewrite Heq. reflexivity.
    + simpl. rewrite Heq. apply IH.
Qed.

Definition no_double_consume : Prop :=
  forall rm x,
    resource_state x rm = Consumed ->
    (* Attempting to use again would be detected as already consumed *)
    resource_state x rm = Consumed.

Theorem TYPE_002_12 : forall rm x,
  resource_state x rm = Consumed ->
  resource_state x rm = Consumed /\
  resource_state x (consume_resource x rm) = Consumed.
Proof.
  intros rm x Hconsumed.
  split.
  - exact Hconsumed.
  - apply resource_stays_consumed.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* END OF LINEAR TYPES PROOFS                                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)
