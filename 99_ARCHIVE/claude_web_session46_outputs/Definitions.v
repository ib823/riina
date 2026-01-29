(* ═══════════════════════════════════════════════════════════════════════════ *)
(* RIINA Language - Base Definitions                                           *)
(* NonInterference via Step-Indexed Logical Relations                          *)
(* Coq 8.18+ Compatible - NO AXIOMS, NO ADMITS                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Lia.

Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 1: Basic Definitions                                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition ident := string.
Definition loc := nat.

Inductive security_level : Type :=
  | Public : security_level
  | Secret : security_level.

Definition security_level_eq_dec : forall (s1 s2 : security_level), {s1 = s2} + {s1 <> s2}.
Proof. decide equality. Defined.

Inductive effect : Type :=
  | EffectPure : effect
  | EffectState : effect
  | EffectIO : effect
  | EffectAll : effect.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 2: Types                                                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TFn : ty -> ty -> effect -> ty
  | TProd : ty -> ty -> ty
  | TSum : ty -> ty -> ty
  | TRef : ty -> security_level -> ty
  | TSecret : ty -> ty
  | TProof : ty -> ty.

Lemma effect_eq_dec : forall (e1 e2 : effect), {e1 = e2} + {e1 <> e2}.
Proof. decide equality. Defined.

Lemma ty_eq_dec : forall (T1 T2 : ty), {T1 = T2} + {T1 <> T2}.
Proof.
  intros T1 T2.
  decide equality.
  - apply effect_eq_dec.
  - apply security_level_eq_dec.
Defined.

(* First-order type predicate *)
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt => true
  | TFn _ _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef _ _ => true
  | TSecret T' | TProof T' => first_order_type T'
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 3: Expressions                                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : nat -> expr
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
  | ERef : expr -> security_level -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  | ELoc : loc -> expr
  | EClassify : expr -> expr
  | EDeclassify : expr -> expr -> expr
  | EProve : expr -> expr.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 4: Values                                                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall i, value (EInt i)
  | VLam : forall x T body, value (ELam x T body)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T)
  | VLoc : forall l, value (ELoc l)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve : forall v, value v -> value (EProve v).

Lemma value_pair_inv : forall a b, value (EPair a b) -> value a /\ value b.
Proof. intros. inversion H; auto. Qed.

Lemma value_inl_inv : forall v T, value (EInl v T) -> value v.
Proof. intros. inversion H; auto. Qed.

Lemma value_inr_inv : forall v T, value (EInr v T) -> value v.
Proof. intros. inversion H; auto. Qed.

Lemma value_classify_inv : forall v, value (EClassify v) -> value v.
Proof. intros. inversion H; auto. Qed.

Lemma value_prove_inv : forall v, value (EProve v) -> value v.
Proof. intros. inversion H; auto. Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 5: Free Variables and Closedness                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Fixpoint free_vars (e : expr) : list ident :=
  match e with
  | EUnit | EBool _ | EInt _ | ELoc _ => []
  | EVar x => [x]
  | ELam x _ body => remove string_dec x (free_vars body)
  | EApp e1 e2 | EPair e1 e2 | EAssign e1 e2 | EDeclassify e1 e2 =>
      free_vars e1 ++ free_vars e2
  | EFst e | ESnd e | EInl e _ | EInr e _ | ERef e _ | EDeref e 
  | EClassify e | EProve e => free_vars e
  | ECase e x1 e1 x2 e2 => 
      free_vars e ++ remove string_dec x1 (free_vars e1) 
                  ++ remove string_dec x2 (free_vars e2)
  | EIf e1 e2 e3 => free_vars e1 ++ free_vars e2 ++ free_vars e3
  end.

Definition closed_expr (e : expr) : Prop := free_vars e = [].

(* Helper lemma *)
Lemma app_nil_inv : forall {A : Type} (l1 l2 : list A),
  l1 ++ l2 = [] -> l1 = [] /\ l2 = [].
Proof.
  intros A l1 l2 H.
  destruct l1; destruct l2; simpl in *; auto; discriminate.
Qed.

(* Closedness lemmas - ALL PROVEN *)
Lemma closed_expr_unit : closed_expr EUnit.
Proof. reflexivity. Qed.

Lemma closed_expr_bool : forall b, closed_expr (EBool b).
Proof. reflexivity. Qed.

Lemma closed_expr_int : forall i, closed_expr (EInt i).
Proof. reflexivity. Qed.

Lemma closed_expr_loc : forall l, closed_expr (ELoc l).
Proof. reflexivity. Qed.

Lemma closed_expr_pair : forall a b,
  closed_expr a -> closed_expr b -> closed_expr (EPair a b).
Proof.
  unfold closed_expr. simpl. intros a b Ha Hb.
  rewrite Ha, Hb. reflexivity.
Qed.

Lemma closed_expr_pair_inv : forall a b,
  closed_expr (EPair a b) -> closed_expr a /\ closed_expr b.
Proof.
  unfold closed_expr. simpl. intros a b H.
  apply app_nil_inv. exact H.
Qed.

Lemma closed_expr_inl : forall v T,
  closed_expr v -> closed_expr (EInl v T).
Proof.
  unfold closed_expr. simpl. auto.
Qed.

Lemma closed_expr_inl_inv : forall v T,
  closed_expr (EInl v T) -> closed_expr v.
Proof.
  unfold closed_expr. simpl. auto.
Qed.

Lemma closed_expr_inr : forall v T,
  closed_expr v -> closed_expr (EInr v T).
Proof.
  unfold closed_expr. simpl. auto.
Qed.

Lemma closed_expr_inr_inv : forall v T,
  closed_expr (EInr v T) -> closed_expr v.
Proof.
  unfold closed_expr. simpl. auto.
Qed.

Lemma closed_expr_classify : forall v,
  closed_expr v -> closed_expr (EClassify v).
Proof.
  unfold closed_expr. simpl. auto.
Qed.

Lemma closed_expr_classify_inv : forall v,
  closed_expr (EClassify v) -> closed_expr v.
Proof.
  unfold closed_expr. simpl. auto.
Qed.

Lemma closed_expr_prove : forall v,
  closed_expr v -> closed_expr (EProve v).
Proof.
  unfold closed_expr. simpl. auto.
Qed.

Lemma closed_expr_prove_inv : forall v,
  closed_expr (EProve v) -> closed_expr v.
Proof.
  unfold closed_expr. simpl. auto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 6: Stores and Store Typing                                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition store := loc -> option expr.
Definition empty_store : store := fun _ => None.
Definition store_lookup (st : store) (l : loc) : option expr := st l.
Definition store_update (st : store) (l : loc) (v : expr) : store :=
  fun l' => if Nat.eq_dec l l' then Some v else st l'.

Definition store_ty := loc -> option (ty * security_level).
Definition empty_store_ty : store_ty := fun _ => None.
Definition store_ty_lookup (Σ : store_ty) (l : loc) : option (ty * security_level) := Σ l.
Definition store_ty_extend (Σ : store_ty) (l : loc) (T : ty) (sl : security_level) : store_ty :=
  fun l' => if Nat.eq_dec l l' then Some (T, sl) else Σ l'.

Definition store_ty_extends (Σ1 Σ2 : store_ty) : Prop :=
  forall l T sl, Σ1 l = Some (T, sl) -> Σ2 l = Some (T, sl).

Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
Proof. unfold store_ty_extends. auto. Qed.

Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 -> store_ty_extends Σ2 Σ3 -> store_ty_extends Σ1 Σ3.
Proof. unfold store_ty_extends. auto. Qed.

Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  forall l T sl, Σ l = Some (T, sl) -> exists v, st l = Some v /\ value v.

Definition stores_agree_low (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall l T, Σ l = Some (T, Public) -> st1 l = st2 l.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SECTION 7: Operational Semantics (Simplified)                               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt i => EInt i
  | ELoc l => ELoc l
  | EVar y => if string_dec x y then v else EVar y
  | ELam y T body => 
      if string_dec x y then ELam y T body 
      else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e => EFst (subst x v e)
  | ESnd e => ESnd (subst x v e)
  | EInl e T => EInl (subst x v e) T
  | EInr e T => EInr (subst x v e) T
  | ECase e y1 e1 y2 e2 =>
      ECase (subst x v e)
            y1 (if string_dec x y1 then e1 else subst x v e1)
            y2 (if string_dec x y2 then e2 else subst x v e2)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ERef e sl => ERef (subst x v e) sl
  | EDeref e => EDeref (subst x v e)
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  | EClassify e => EClassify (subst x v e)
  | EDeclassify e1 e2 => EDeclassify (subst x v e1) (subst x v e2)
  | EProve e => EProve (subst x v e)
  end.

Reserved Notation "e1 '-->' e2" (at level 40).

Inductive step : (expr * store) -> (expr * store) -> Prop :=
  | ST_AppAbs : forall x T body v st,
      value v ->
      (EApp (ELam x T body) v, st) --> (subst x v body, st)
  | ST_App1 : forall e1 e1' e2 st st',
      (e1, st) --> (e1', st') ->
      (EApp e1 e2, st) --> (EApp e1' e2, st')
  | ST_App2 : forall v1 e2 e2' st st',
      value v1 ->
      (e2, st) --> (e2', st') ->
      (EApp v1 e2, st) --> (EApp v1 e2', st')
  | ST_FstPair : forall v1 v2 st,
      value v1 -> value v2 ->
      (EFst (EPair v1 v2), st) --> (v1, st)
  | ST_SndPair : forall v1 v2 st,
      value v1 -> value v2 ->
      (ESnd (EPair v1 v2), st) --> (v2, st)
  | ST_Fst : forall e e' st st',
      (e, st) --> (e', st') ->
      (EFst e, st) --> (EFst e', st')
  | ST_Snd : forall e e' st st',
      (e, st) --> (e', st') ->
      (ESnd e, st) --> (ESnd e', st')
  | ST_Pair1 : forall e1 e1' e2 st st',
      (e1, st) --> (e1', st') ->
      (EPair e1 e2, st) --> (EPair e1' e2, st')
  | ST_Pair2 : forall v1 e2 e2' st st',
      value v1 ->
      (e2, st) --> (e2', st') ->
      (EPair v1 e2, st) --> (EPair v1 e2', st')
  | ST_CaseInl : forall v T2 x1 e1 x2 e2 st,
      value v ->
      (ECase (EInl v T2) x1 e1 x2 e2, st) --> (subst x1 v e1, st)
  | ST_CaseInr : forall v T1 x1 e1 x2 e2 st,
      value v ->
      (ECase (EInr v T1) x1 e1 x2 e2, st) --> (subst x2 v e2, st)
  | ST_Case : forall e e' x1 e1 x2 e2 st st',
      (e, st) --> (e', st') ->
      (ECase e x1 e1 x2 e2, st) --> (ECase e' x1 e1 x2 e2, st')
  | ST_Inl : forall e e' T st st',
      (e, st) --> (e', st') ->
      (EInl e T, st) --> (EInl e' T, st')
  | ST_Inr : forall e e' T st st',
      (e, st) --> (e', st') ->
      (EInr e T, st) --> (EInr e' T, st')
  | ST_IfTrue : forall e2 e3 st,
      (EIf (EBool true) e2 e3, st) --> (e2, st)
  | ST_IfFalse : forall e2 e3 st,
      (EIf (EBool false) e2 e3, st) --> (e3, st)
  | ST_If : forall e1 e1' e2 e3 st st',
      (e1, st) --> (e1', st') ->
      (EIf e1 e2 e3, st) --> (EIf e1' e2 e3, st')
  | ST_RefValue : forall v l sl st,
      value v ->
      store_lookup st l = None ->
      (ERef v sl, st) --> (ELoc l, store_update st l v)
  | ST_Ref : forall e e' sl st st',
      (e, st) --> (e', st') ->
      (ERef e sl, st) --> (ERef e' sl, st')
  | ST_DerefLoc : forall l v st,
      store_lookup st l = Some v ->
      (EDeref (ELoc l), st) --> (v, st)
  | ST_Deref : forall e e' st st',
      (e, st) --> (e', st') ->
      (EDeref e, st) --> (EDeref e', st')
  | ST_AssignLoc : forall l v st,
      value v ->
      (EAssign (ELoc l) v, st) --> (EUnit, store_update st l v)
  | ST_Assign1 : forall e1 e1' e2 st st',
      (e1, st) --> (e1', st') ->
      (EAssign e1 e2, st) --> (EAssign e1' e2, st')
  | ST_Assign2 : forall v1 e2 e2' st st',
      value v1 ->
      (e2, st) --> (e2', st') ->
      (EAssign v1 e2, st) --> (EAssign v1 e2', st')
  | ST_Classify : forall e e' st st',
      (e, st) --> (e', st') ->
      (EClassify e, st) --> (EClassify e', st')
  | ST_DeclassifyValue : forall v p st,
      value v -> value p ->
      (EDeclassify (EClassify v) p, st) --> (v, st)
  | ST_Declassify1 : forall e1 e1' e2 st st',
      (e1, st) --> (e1', st') ->
      (EDeclassify e1 e2, st) --> (EDeclassify e1' e2, st')
  | ST_Declassify2 : forall v1 e2 e2' st st',
      value v1 ->
      (e2, st) --> (e2', st') ->
      (EDeclassify v1 e2, st) --> (EDeclassify v1 e2', st')
  | ST_Prove : forall e e' st st',
      (e, st) --> (e', st') ->
      (EProve e, st) --> (EProve e', st')

where "e1 '-->' e2" := (step e1 e2).

Inductive multi_step : (expr * store) -> (expr * store) -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3,
      step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.

Notation "e1 '-->*' e2" := (multi_step e1 e2) (at level 40).

Lemma multi_step_trans : forall cfg1 cfg2 cfg3,
  cfg1 -->* cfg2 -> cfg2 -->* cfg3 -> cfg1 -->* cfg3.
Proof.
  intros cfg1 cfg2 cfg3 H12 H23.
  induction H12.
  - exact H23.
  - eapply MS_Step; eauto.
Qed.
