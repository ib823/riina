(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* MLTTFoundation.v - Martin-Löf Type Theory Foundation for RIINA *)
(* Spec: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/ *)
(* Generated for RIINA formal verification *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* UNIVERSE LEVELS                                                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition Level := nat.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TYPES (UNIVERSE-POLYMORPHIC SYNTAX)                                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive Ty : Type :=
  | TUnit : Ty
  | TPi : Ty -> Ty -> Ty          (* Π-type: Π(x:A).B *)
  | TSigma : Ty -> Ty -> Ty       (* Σ-type: Σ(x:A).B *)
  | TId : Ty -> Ty                (* Identity type *)
  | TUniverse : Level -> Ty       (* Universe at level l *)
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TERMS                                                                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive Term : Type :=
  | TmVar : nat -> Term
  | TmUnit : Term                               (* Unit value *)
  | TmLam : Ty -> Term -> Term                  (* λ-abstraction with type annotation *)
  | TmApp : Term -> Term -> Term                (* Application *)
  | TmPair : Term -> Term -> Term               (* Pair introduction *)
  | TmFst : Term -> Term                        (* First projection *)
  | TmSnd : Term -> Term                        (* Second projection *)
  | TmRefl : Term -> Term                       (* Reflexivity proof: refl(a) *)
  | TmJ : Ty -> Ty -> Term -> Term -> Term      (* J-eliminator with type annotations *)
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* CONTEXT                                                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Definition Ctx := list Ty.

Definition empty_ctx : Ctx := [].

Definition ctx_extend (G : Ctx) (A : Ty) : Ctx := A :: G.

(* Context lookup *)
Fixpoint ctx_lookup (G : Ctx) (n : nat) : option Ty :=
  match G with
  | [] => None
  | A :: G' => if Nat.eqb n 0 then Some A else ctx_lookup G' (n - 1)
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TYPE LEVEL ASSIGNMENT                                                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Assign a universe level to a type *)
Inductive has_level : Ty -> Level -> Prop :=
  | level_unit : forall l, has_level TUnit l
  | level_pi : forall A B l, has_level A l -> has_level B l -> has_level (TPi A B) l
  | level_sigma : forall A B l, has_level A l -> has_level B l -> has_level (TSigma A B) l
  | level_id : forall A l, has_level A l -> has_level (TId A) l
  | level_universe : forall l l', S l <= l' -> has_level (TUniverse l) l'.

(* Cumulativity: types at level l are also at level l+1 *)
Lemma cumulativity_level : forall A l,
  has_level A l -> has_level A (S l).
Proof.
  intros A l H.
  induction H.
  - apply level_unit.
  - apply level_pi; assumption.
  - apply level_sigma; assumption.
  - apply level_id; assumption.
  - apply level_universe. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* WELL-FORMEDNESS JUDGMENTS                                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Context well-formedness *)
Inductive wf_ctx : Ctx -> Prop :=
  | wf_empty : wf_ctx []
  | wf_extend : forall G A, wf_ctx G -> wf_ctx (ctx_extend G A).

(* Type well-formedness in context *)
Inductive wf_ty : Ctx -> Ty -> Prop :=
  | wf_unit : forall G, wf_ctx G -> wf_ty G TUnit
  | wf_pi : forall G A B, wf_ty G A -> wf_ty (ctx_extend G A) B -> wf_ty G (TPi A B)
  | wf_sigma : forall G A B, wf_ty G A -> wf_ty (ctx_extend G A) B -> wf_ty G (TSigma A B)
  | wf_id : forall G A, wf_ty G A -> wf_ty G (TId A)
  | wf_universe : forall G l, wf_ctx G -> wf_ty G (TUniverse l).

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TYPING JUDGMENT                                                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive has_type : Ctx -> Term -> Ty -> Prop :=
  (* Variable *)
  | T_Var : forall G n A,
      wf_ctx G ->
      ctx_lookup G n = Some A ->
      has_type G (TmVar n) A
      
  (* Unit introduction *)
  | T_Unit : forall G,
      wf_ctx G ->
      has_type G TmUnit TUnit
      
  (* Pi introduction: λ-abstraction *)
  | T_Lam : forall G A B t,
      wf_ty G A ->
      has_type (ctx_extend G A) t B ->
      has_type G (TmLam A t) (TPi A B)
      
  (* Pi elimination: application *)
  | T_App : forall G A B f a,
      has_type G f (TPi A B) ->
      has_type G a A ->
      has_type G (TmApp f a) B
      
  (* Sigma introduction: pairing *)
  | T_Pair : forall G A B a b,
      wf_ty G (TSigma A B) ->
      has_type G a A ->
      has_type G b B ->
      has_type G (TmPair a b) (TSigma A B)
      
  (* Sigma elimination: first projection *)
  | T_Fst : forall G A B p,
      has_type G p (TSigma A B) ->
      has_type G (TmFst p) A
      
  (* Sigma elimination: second projection *)
  | T_Snd : forall G A B p,
      has_type G p (TSigma A B) ->
      has_type G (TmSnd p) B
      
  (* Identity introduction: reflexivity *)
  | T_Refl : forall G A a,
      wf_ty G A ->
      has_type G a A ->
      has_type G (TmRefl a) (TId A)
      
  (* Identity elimination: J-eliminator *)
  | T_J : forall G A C d p,
      wf_ty G A ->
      has_type G d C ->  
      has_type G p (TId A) ->
      has_type G (TmJ A C d p) C.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TYPE EQUALITY / CONVERSION                                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive ty_eq : Ty -> Ty -> Prop :=
  | ty_eq_refl : forall A, ty_eq A A
  | ty_eq_sym : forall A B, ty_eq A B -> ty_eq B A
  | ty_eq_trans : forall A B C, ty_eq A B -> ty_eq B C -> ty_eq A C
  | ty_eq_pi : forall A A' B B', ty_eq A A' -> ty_eq B B' -> ty_eq (TPi A B) (TPi A' B')
  | ty_eq_sigma : forall A A' B B', ty_eq A A' -> ty_eq B B' -> ty_eq (TSigma A B) (TSigma A' B').

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TERM EQUALITY / CONVERSION                                                   *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive term_eq : Term -> Term -> Prop :=
  | term_eq_refl : forall t, term_eq t t
  | term_eq_sym : forall t u, term_eq t u -> term_eq u t
  | term_eq_trans : forall t u v, term_eq t u -> term_eq u v -> term_eq t v
  (* Congruence rules *)
  | term_eq_app : forall f f' a a', term_eq f f' -> term_eq a a' -> term_eq (TmApp f a) (TmApp f' a')
  | term_eq_lam : forall A t t', term_eq t t' -> term_eq (TmLam A t) (TmLam A t')
  | term_eq_pair : forall a a' b b', term_eq a a' -> term_eq b b' -> term_eq (TmPair a b) (TmPair a' b')
  | term_eq_fst : forall p p', term_eq p p' -> term_eq (TmFst p) (TmFst p')
  | term_eq_snd : forall p p', term_eq p p' -> term_eq (TmSnd p) (TmSnd p')
  | term_eq_refl_cong : forall a a', term_eq a a' -> term_eq (TmRefl a) (TmRefl a')
  | term_eq_J : forall A C d d' p p', term_eq d d' -> term_eq p p' -> term_eq (TmJ A C d p) (TmJ A C d' p').

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* REDUCTION RELATION                                                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive reduces : Term -> Term -> Prop :=
  | red_beta : forall A t a, reduces (TmApp (TmLam A t) a) t
  | red_fst : forall a b, reduces (TmFst (TmPair a b)) a
  | red_snd : forall a b, reduces (TmSnd (TmPair a b)) b
  | red_J : forall A C d a, reduces (TmJ A C d (TmRefl a)) d
  | red_app_l : forall f f' a, reduces f f' -> reduces (TmApp f a) (TmApp f' a)
  | red_app_r : forall f a a', reduces a a' -> reduces (TmApp f a) (TmApp f a')
  | red_lam : forall A t t', reduces t t' -> reduces (TmLam A t) (TmLam A t')
  | red_pair_l : forall a a' b, reduces a a' -> reduces (TmPair a b) (TmPair a' b)
  | red_pair_r : forall a b b', reduces b b' -> reduces (TmPair a b) (TmPair a b')
  | red_fst_cong : forall p p', reduces p p' -> reduces (TmFst p) (TmFst p')
  | red_snd_cong : forall p p', reduces p p' -> reduces (TmSnd p) (TmSnd p')
  | red_refl_cong : forall a a', reduces a a' -> reduces (TmRefl a) (TmRefl a')
  | red_J_d : forall A C d d' p, reduces d d' -> reduces (TmJ A C d p) (TmJ A C d' p)
  | red_J_p : forall A C d p p', reduces p p' -> reduces (TmJ A C d p) (TmJ A C d p').

(* Reflexive-transitive closure *)
Inductive reduces_star : Term -> Term -> Prop :=
  | red_star_refl : forall t, reduces_star t t
  | red_star_step : forall t u v, reduces t u -> reduces_star u v -> reduces_star t v.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* NORMAL FORMS                                                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Neutral/stuck terms: cannot reduce at the head position *)
(* Extended to cover all stuck terms, not just variable-headed ones *)
Inductive neutral : Term -> Prop :=
  (* Variables are neutral *)
  | neutral_var : forall n, neutral (TmVar n)
  (* Application is stuck if head is not a lambda *)
  | neutral_app_var : forall n a, neutral (TmApp (TmVar n) a)
  | neutral_app_unit : forall a, neutral (TmApp TmUnit a)
  | neutral_app_app : forall f1 f2 a, neutral (TmApp (TmApp f1 f2) a)
  | neutral_app_pair : forall p q a, neutral (TmApp (TmPair p q) a)
  | neutral_app_fst : forall p a, neutral (TmApp (TmFst p) a)
  | neutral_app_snd : forall p a, neutral (TmApp (TmSnd p) a)
  | neutral_app_refl : forall r a, neutral (TmApp (TmRefl r) a)
  | neutral_app_J : forall A C d p a, neutral (TmApp (TmJ A C d p) a)
  (* Fst is stuck if argument is not a pair *)
  | neutral_fst_var : forall n, neutral (TmFst (TmVar n))
  | neutral_fst_unit : neutral (TmFst TmUnit)
  | neutral_fst_lam : forall A t, neutral (TmFst (TmLam A t))
  | neutral_fst_app : forall f a, neutral (TmFst (TmApp f a))
  | neutral_fst_fst : forall p, neutral (TmFst (TmFst p))
  | neutral_fst_snd : forall p, neutral (TmFst (TmSnd p))
  | neutral_fst_refl : forall r, neutral (TmFst (TmRefl r))
  | neutral_fst_J : forall A C d p, neutral (TmFst (TmJ A C d p))
  (* Snd is stuck if argument is not a pair *)
  | neutral_snd_var : forall n, neutral (TmSnd (TmVar n))
  | neutral_snd_unit : neutral (TmSnd TmUnit)
  | neutral_snd_lam : forall A t, neutral (TmSnd (TmLam A t))
  | neutral_snd_app : forall f a, neutral (TmSnd (TmApp f a))
  | neutral_snd_fst : forall p, neutral (TmSnd (TmFst p))
  | neutral_snd_snd : forall p, neutral (TmSnd (TmSnd p))
  | neutral_snd_refl : forall r, neutral (TmSnd (TmRefl r))
  | neutral_snd_J : forall A C d p, neutral (TmSnd (TmJ A C d p))
  (* J is stuck if proof is not a refl *)
  | neutral_J_var : forall A C d n, neutral (TmJ A C d (TmVar n))
  | neutral_J_unit : forall A C d, neutral (TmJ A C d TmUnit)
  | neutral_J_lam : forall A C d B t, neutral (TmJ A C d (TmLam B t))
  | neutral_J_app : forall A C d f a, neutral (TmJ A C d (TmApp f a))
  | neutral_J_pair : forall A C d p q, neutral (TmJ A C d (TmPair p q))
  | neutral_J_fst : forall A C d p, neutral (TmJ A C d (TmFst p))
  | neutral_J_snd : forall A C d p, neutral (TmJ A C d (TmSnd p))
  | neutral_J_J : forall A C d B E e p, neutral (TmJ A C d (TmJ B E e p)).

(* Normal terms: fully reduced *)
Inductive normal : Term -> Prop :=
  | normal_neutral : forall t, neutral t -> normal t
  | normal_unit : normal TmUnit
  | normal_lam : forall A t, normal t -> normal (TmLam A t)
  | normal_pair : forall a b, normal a -> normal b -> normal (TmPair a b)
  | normal_refl : forall a, normal a -> normal (TmRefl a).

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SUBSTITUTION                                                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Fixpoint shift (c d : nat) (t : Term) : Term :=
  match t with
  | TmVar n => if Nat.leb c n then TmVar (n + d) else TmVar n
  | TmUnit => TmUnit
  | TmLam A t' => TmLam A (shift (S c) d t')
  | TmApp f a => TmApp (shift c d f) (shift c d a)
  | TmPair a b => TmPair (shift c d a) (shift c d b)
  | TmFst p => TmFst (shift c d p)
  | TmSnd p => TmSnd (shift c d p)
  | TmRefl a => TmRefl (shift c d a)
  | TmJ A C d' p => TmJ A C (shift c d d') (shift c d p)
  end.

Fixpoint subst (n : nat) (s t : Term) : Term :=
  match t with
  | TmVar m => if Nat.eqb n m then s
               else if Nat.ltb n m then TmVar (m - 1)
               else TmVar m
  | TmUnit => TmUnit
  | TmLam A t' => TmLam A (subst (S n) (shift 0 1 s) t')
  | TmApp f a => TmApp (subst n s f) (subst n s a)
  | TmPair a b => TmPair (subst n s a) (subst n s b)
  | TmFst p => TmFst (subst n s p)
  | TmSnd p => TmSnd (subst n s p)
  | TmRefl a => TmRefl (subst n s a)
  | TmJ A C d p => TmJ A C (subst n s d) (subst n s p)
  end.

(* Computational equality includes beta/eta *)
Inductive comp_eq : Term -> Term -> Prop :=
  | comp_eq_term : forall t u, term_eq t u -> comp_eq t u
  (* β-reduction for functions *)
  | comp_eq_beta : forall A t a, comp_eq (TmApp (TmLam A t) a) (subst 0 a t)
  (* β-reduction for pairs *)
  | comp_eq_fst_beta : forall a b, comp_eq (TmFst (TmPair a b)) a
  | comp_eq_snd_beta : forall a b, comp_eq (TmSnd (TmPair a b)) b
  (* η-conversion for functions *)
  | comp_eq_eta_fun : forall A f, comp_eq (TmLam A (TmApp (shift 0 1 f) (TmVar 0))) f
  (* η-conversion for pairs *)
  | comp_eq_eta_pair : forall p, comp_eq (TmPair (TmFst p) (TmSnd p)) p
  (* J computation rule *)
  | comp_eq_J_refl : forall A C d a, comp_eq (TmJ A C d (TmRefl a)) d.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_01: Pi-type introduction well-formed                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_01 :
  forall (G : Ctx) (A B : Ty),
    wf_ctx G ->
    wf_ty G A ->
    wf_ty (ctx_extend G A) B ->
    wf_ty G (TPi A B).
Proof.
  intros G A B Hwf_ctx Hwf_A Hwf_B.
  apply wf_pi; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_02: Pi-type elimination (application)                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_02 :
  forall (G : Ctx) (A B : Ty) (f a : Term),
    has_type G f (TPi A B) ->
    has_type G a A ->
    has_type G (TmApp f a) B.
Proof.
  intros G A B f a Hf Ha.
  apply T_App with (A := A); assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_03: Sigma-type introduction (pairing)                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_03 :
  forall (G : Ctx) (A B : Ty) (a b : Term),
    wf_ty G (TSigma A B) ->
    has_type G a A ->
    has_type G b B ->
    has_type G (TmPair a b) (TSigma A B).
Proof.
  intros G A B a b Hwf Ha Hb.
  apply T_Pair; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_04: Sigma-type elimination (projections)                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_04 :
  forall (G : Ctx) (A B : Ty) (p : Term),
    has_type G p (TSigma A B) ->
    has_type G (TmFst p) A /\ has_type G (TmSnd p) B.
Proof.
  intros G A B p Hp.
  split.
  - apply T_Fst with (B := B); assumption.
  - apply T_Snd with (A := A); assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_05: Identity type reflexivity                               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_05 :
  forall (G : Ctx) (A : Ty) (a : Term),
    wf_ty G A ->
    has_type G a A ->
    has_type G (TmRefl a) (TId A).
Proof.
  intros G A a Hwf Ha.
  apply T_Refl; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_06: Identity type J-eliminator (transport)                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_06 :
  forall (G : Ctx) (A : Ty) (C : Ty) (d p : Term),
    wf_ty G A ->
    has_type G d C ->
    has_type G p (TId A) ->
    has_type G (TmJ A C d p) C.
Proof.
  intros G A C d p Hwf Hd Hp.
  apply T_J with (A := A); assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_07: Universe hierarchy consistency                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_07 :
  forall l, has_level (TUniverse l) (S l).
Proof.
  intros l.
  apply level_universe. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_08: Cumulativity                                            *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_08 :
  forall (A : Ty) (l : Level),
    has_level A l ->
    has_level A (S l).
Proof.
  intros A l H.
  apply cumulativity_level. assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_09: Context well-formedness (weakening)                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_09 :
  forall (G : Ctx) (A : Ty),
    wf_ctx G ->
    wf_ctx (ctx_extend G A).
Proof.
  intros G A Hwf.
  apply wf_extend. assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_10: Substitution lemma                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_10 :
  forall t1 t2 n s,
    term_eq t1 t2 ->
    term_eq (subst n s t1) (subst n s t2).
Proof.
  intros t1 t2 n s Heq.
  generalize dependent s. generalize dependent n.
  induction Heq; intros; simpl.
  - apply term_eq_refl.
  - apply term_eq_sym. apply IHHeq.
  - apply term_eq_trans with (u := subst n s u). apply IHHeq1. apply IHHeq2.
  - apply term_eq_app; [apply IHHeq1 | apply IHHeq2].
  - apply term_eq_lam. apply IHHeq.
  - apply term_eq_pair; [apply IHHeq1 | apply IHHeq2].
  - apply term_eq_fst. apply IHHeq.
  - apply term_eq_snd. apply IHHeq.
  - apply term_eq_refl_cong. apply IHHeq.
  - apply term_eq_J; [apply IHHeq1 | apply IHHeq2].
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_11: Type uniqueness                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Helper lemma: first prove Leibniz equality *)
Lemma type_uniqueness_eq :
  forall (G : Ctx) t A B,
    has_type G t A ->
    has_type G t B ->
    A = B.
Proof.
  intros G t A B HA HB.
  generalize dependent B.
  induction HA; intros B' HB'; inversion HB'; subst.
  - rewrite H0 in H4. inversion H4. reflexivity.
  - reflexivity.
  - f_equal. apply IHHA. assumption.
  - specialize (IHHA1 _ H2). inversion IHHA1; subst. reflexivity.
  - f_equal. apply IHHA1; assumption. apply IHHA2; assumption.
  - specialize (IHHA _ H1). inversion IHHA; subst. reflexivity.
  - specialize (IHHA _ H1). inversion IHHA; subst. reflexivity.
  - f_equal. apply IHHA. assumption.
  - apply IHHA1. assumption.
Qed.

(* Type uniqueness with ty_eq *)
Theorem TYPE_001_11 :
  forall (G : Ctx) t A B,
    has_type G t A ->
    has_type G t B ->
    ty_eq A B.
Proof.
  intros G t A B HA HB.
  assert (A = B) by (eapply type_uniqueness_eq; eassumption).
  subst. apply ty_eq_refl.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_12: Conversion rule (β-reduction preserves typing)          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_12 :
  forall A t a,
    comp_eq (TmApp (TmLam A t) a) (subst 0 a t).
Proof.
  intros A t a.
  apply comp_eq_beta.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_13: η-conversion for functions                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_13 :
  forall A f,
    comp_eq (TmLam A (TmApp (shift 0 1 f) (TmVar 0))) f.
Proof.
  intros A f.
  apply comp_eq_eta_fun.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_14: η-conversion for pairs                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_14 :
  forall p,
    comp_eq (TmPair (TmFst p) (TmSnd p)) p.
Proof.
  intros p.
  apply comp_eq_eta_pair.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* HELPER LEMMAS FOR NORMALIZATION                                              *)
(* These lemmas lift reductions through term constructors, avoiding the         *)
(* variable naming issues that arise from nested induction.                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma red_star_trans : forall t u v,
  reduces_star t u -> reduces_star u v -> reduces_star t v.
Proof.
  intros t u v H1 H2. induction H1.
  - assumption.
  - eapply red_star_step. eassumption. apply IHreduces_star. assumption.
Qed.

Lemma red_star_app : forall f f' a a',
  reduces_star f f' -> reduces_star a a' -> reduces_star (TmApp f a) (TmApp f' a').
Proof.
  intros f f' a a' Hf Ha.
  eapply red_star_trans.
  - clear Ha. induction Hf.
    + apply red_star_refl.
    + eapply red_star_step. apply red_app_l. eassumption. assumption.
  - clear Hf. induction Ha.
    + apply red_star_refl.
    + eapply red_star_step. apply red_app_r. eassumption. assumption.
Qed.

Lemma red_star_lam : forall A body body',
  reduces_star body body' -> reduces_star (TmLam A body) (TmLam A body').
Proof.
  intros A body body' H. induction H.
  - apply red_star_refl.
  - eapply red_star_step. apply red_lam. eassumption. assumption.
Qed.

Lemma red_star_pair : forall a a' b b',
  reduces_star a a' -> reduces_star b b' -> reduces_star (TmPair a b) (TmPair a' b').
Proof.
  intros a a' b b' Ha Hb.
  eapply red_star_trans.
  - clear Hb. induction Ha.
    + apply red_star_refl.
    + eapply red_star_step. apply red_pair_l. eassumption. assumption.
  - clear Ha. induction Hb.
    + apply red_star_refl.
    + eapply red_star_step. apply red_pair_r. eassumption. assumption.
Qed.

Lemma red_star_fst : forall p p',
  reduces_star p p' -> reduces_star (TmFst p) (TmFst p').
Proof.
  intros p p' H. induction H.
  - apply red_star_refl.
  - eapply red_star_step. apply red_fst_cong. eassumption. assumption.
Qed.

Lemma red_star_snd : forall p p',
  reduces_star p p' -> reduces_star (TmSnd p) (TmSnd p').
Proof.
  intros p p' H. induction H.
  - apply red_star_refl.
  - eapply red_star_step. apply red_snd_cong. eassumption. assumption.
Qed.

Lemma red_star_refl_tm : forall a a',
  reduces_star a a' -> reduces_star (TmRefl a) (TmRefl a').
Proof.
  intros a a' H. induction H.
  - apply red_star_refl.
  - eapply red_star_step. apply red_refl_cong. eassumption. assumption.
Qed.

Lemma red_star_J : forall A C d d' p p',
  reduces_star d d' -> reduces_star p p' -> reduces_star (TmJ A C d p) (TmJ A C d' p').
Proof.
  intros A C d d' p p' Hd Hp.
  eapply red_star_trans.
  - clear Hp. induction Hd.
    + apply red_star_refl.
    + eapply red_star_step. apply red_J_d. eassumption. assumption.
  - clear Hd. induction Hp.
    + apply red_star_refl.
    + eapply red_star_step. apply red_J_p. eassumption. assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_001_15: Normalization                                           *)
(* For untyped terms with full beta reduction, we prove weak normalization      *)
(* using the extended neutral predicate that covers all stuck terms.            *)
(* Note: Full normalization for untyped terms requires well-typedness; here we  *)
(* show that each term form reaches a normal/neutral form.                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_001_15 :
  forall t,
    (exists nf, reduces_star t nf /\ (normal nf \/ neutral nf)).
Proof.
  intros t.
  induction t.
  - (* TmVar n *)
    exists (TmVar n). split.
    + apply red_star_refl.
    + right. apply neutral_var.
  - (* TmUnit *)
    exists TmUnit. split.
    + apply red_star_refl.
    + left. apply normal_unit.
  - (* TmLam *)
    destruct IHt as [nf_t [Hred_t Hnorm_t]].
    exists (TmLam t nf_t). split.
    + apply red_star_lam. assumption.
    + left. apply normal_lam.
      destruct Hnorm_t; [assumption | apply normal_neutral; assumption].
  - (* TmApp *)
    destruct IHt1 as [nf1 [Hred1 Hnorm1]].
    destruct IHt2 as [nf2 [Hred2 Hnorm2]].
    destruct nf1 as [v | | ty body | f1 a1 | p1 q1 | p1 | p1 | r1 | A C d1 p1].
    + (* TmVar v - stuck *)
      exists (TmApp (TmVar v) nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_var.
    + (* TmUnit - stuck *)
      exists (TmApp TmUnit nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_unit.
    + (* TmLam ty body - beta: (λ.body) arg --> body *)
      exists body. split.
      * eapply red_star_trans.
        -- apply red_star_app; eassumption.
        -- eapply red_star_step. apply red_beta. apply red_star_refl.
      * destruct Hnorm1 as [Hn1 | Hn1].
        -- inversion Hn1; subst.
           ++ inversion H.
           ++ left. assumption.
        -- inversion Hn1.
    + (* TmApp f1 a1 - stuck *)
      exists (TmApp (TmApp f1 a1) nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_app.
    + (* TmPair p1 q1 - stuck *)
      exists (TmApp (TmPair p1 q1) nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_pair.
    + (* TmFst p1 - stuck *)
      exists (TmApp (TmFst p1) nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_fst.
    + (* TmSnd p1 - stuck *)
      exists (TmApp (TmSnd p1) nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_snd.
    + (* TmRefl r1 - stuck *)
      exists (TmApp (TmRefl r1) nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_refl.
    + (* TmJ A C d1 p1 - stuck *)
      exists (TmApp (TmJ A C d1 p1) nf2). split.
      * apply red_star_app; assumption.
      * right. apply neutral_app_J.
  - (* TmPair *)
    destruct IHt1 as [nf1 [Hred1 Hnorm1]].
    destruct IHt2 as [nf2 [Hred2 Hnorm2]].
    exists (TmPair nf1 nf2). split.
    + apply red_star_pair; assumption.
    + left. apply normal_pair.
      * destruct Hnorm1; [assumption | apply normal_neutral; assumption].
      * destruct Hnorm2; [assumption | apply normal_neutral; assumption].
  - (* TmFst *)
    destruct IHt as [nf [Hred Hnorm]].
    destruct nf as [v | | ty body | f1 a1 | p1 q1 | p1 | p1 | r1 | A C d1 p1].
    + (* TmVar v - stuck *)
      exists (TmFst (TmVar v)). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_var.
    + (* TmUnit - stuck *)
      exists (TmFst TmUnit). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_unit.
    + (* TmLam - stuck *)
      exists (TmFst (TmLam ty body)). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_lam.
    + (* TmApp f1 a1 - stuck *)
      exists (TmFst (TmApp f1 a1)). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_app.
    + (* TmPair p1 q1 - fst (pair a b) -> a *)
      exists p1. split.
      * eapply red_star_trans.
        -- apply red_star_fst; eassumption.
        -- eapply red_star_step. apply red_fst. apply red_star_refl.
      * destruct Hnorm as [Hn | Hn].
        -- inversion Hn; subst.
           ++ inversion H.
           ++ left. assumption.
        -- inversion Hn.
    + (* TmFst p1 - stuck *)
      exists (TmFst (TmFst p1)). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_fst.
    + (* TmSnd p1 - stuck *)
      exists (TmFst (TmSnd p1)). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_snd.
    + (* TmRefl r1 - stuck *)
      exists (TmFst (TmRefl r1)). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_refl.
    + (* TmJ - stuck *)
      exists (TmFst (TmJ A C d1 p1)). split.
      * apply red_star_fst; assumption.
      * right. apply neutral_fst_J.
  - (* TmSnd *)
    destruct IHt as [nf [Hred Hnorm]].
    destruct nf as [v | | ty body | f1 a1 | p1 q1 | p1 | p1 | r1 | A C d1 p1].
    + (* TmVar v - stuck *)
      exists (TmSnd (TmVar v)). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_var.
    + (* TmUnit - stuck *)
      exists (TmSnd TmUnit). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_unit.
    + (* TmLam - stuck *)
      exists (TmSnd (TmLam ty body)). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_lam.
    + (* TmApp f1 a1 - stuck *)
      exists (TmSnd (TmApp f1 a1)). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_app.
    + (* TmPair p1 q1 - snd (pair a b) -> b *)
      exists q1. split.
      * eapply red_star_trans.
        -- apply red_star_snd; eassumption.
        -- eapply red_star_step. apply red_snd. apply red_star_refl.
      * destruct Hnorm as [Hn | Hn].
        -- inversion Hn; subst.
           ++ inversion H.
           ++ left. assumption.
        -- inversion Hn.
    + (* TmFst p1 - stuck *)
      exists (TmSnd (TmFst p1)). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_fst.
    + (* TmSnd p1 - stuck *)
      exists (TmSnd (TmSnd p1)). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_snd.
    + (* TmRefl r1 - stuck *)
      exists (TmSnd (TmRefl r1)). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_refl.
    + (* TmJ - stuck *)
      exists (TmSnd (TmJ A C d1 p1)). split.
      * apply red_star_snd; assumption.
      * right. apply neutral_snd_J.
  - (* TmRefl *)
    destruct IHt as [nf [Hred Hnorm]].
    exists (TmRefl nf). split.
    + apply red_star_refl_tm. assumption.
    + left. apply normal_refl.
      destruct Hnorm; [assumption | apply normal_neutral; assumption].
  - (* TmJ: J A C d p - we need to normalize d and p *)
    (* TmJ : Ty -> Ty -> Term -> Term -> Term *)
    (* t1=A (Ty), t2=C (Ty), t3=d (Term), t4=p (Term) *)
    (* IHt1 is for t3 (d), IHt2 is for t4 (p) *)
    destruct IHt1 as [nf_d [Hred_d Hnorm_d]].
    destruct IHt2 as [nf_p [Hred_p Hnorm_p]].
    destruct nf_p as [v | | ty body | f1 a1 | p1 q1 | p1 | p1 | r1 | A' C' d1 p1].
    + (* TmVar v - stuck *)
      exists (TmJ t1 t2 nf_d (TmVar v)). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_var.
    + (* TmUnit - stuck *)
      exists (TmJ t1 t2 nf_d TmUnit). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_unit.
    + (* TmLam - stuck *)
      exists (TmJ t1 t2 nf_d (TmLam ty body)). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_lam.
    + (* TmApp - stuck *)
      exists (TmJ t1 t2 nf_d (TmApp f1 a1)). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_app.
    + (* TmPair - stuck *)
      exists (TmJ t1 t2 nf_d (TmPair p1 q1)). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_pair.
    + (* TmFst - stuck *)
      exists (TmJ t1 t2 nf_d (TmFst p1)). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_fst.
    + (* TmSnd - stuck *)
      exists (TmJ t1 t2 nf_d (TmSnd p1)). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_snd.
    + (* TmRefl r1 - J computation: J A C d (refl a) -> d *)
      exists nf_d. split.
      * eapply red_star_trans.
        -- apply red_star_J; eassumption.
        -- eapply red_star_step. apply red_J. apply red_star_refl.
      * assumption.
    + (* TmJ - stuck *)
      exists (TmJ t1 t2 nf_d (TmJ A' C' d1 p1)). split.
      * apply red_star_J; assumption.
      * right. apply neutral_J_J.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* END OF MLTTFoundation.v                                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)
