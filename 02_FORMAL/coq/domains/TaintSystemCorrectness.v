(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* TaintSystemCorrectness.v *)
(* Worker E Task 7: Type-system-level taint tracking correctness *)
(* Proves type preservation, progress, and sanitization soundness *)
(* for RIINA's Tainted/Sanitized type constructors *)
(*
   Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md §5 (Type System)
   Rust: 03_PROTO/crates/riina-typechecker/src/lib.rs (taint checking)
   Related: domains/InjectionPrevention.v (SQL/Shell/LDAP models)
            domains/XSSPrevention.v (context-specific XSS)
            domains/SQLInjectionPrevention.v (parameterized queries)
*)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 1: TAINT TYPE SYSTEM MODEL                                      *)
(* Mirrors: foundations/Syntax.v taint_source, sanitizer, TTainted,        *)
(*          TSanitized constructors                                         *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Taint sources — mirrors Syntax.v taint_source *)
Inductive taint_source : Type :=
  | TaintNetworkExternal : taint_source
  | TaintNetworkInternal : taint_source
  | TaintUserInput       : taint_source
  | TaintFileSystem      : taint_source
  | TaintDatabase        : taint_source
  | TaintEnvironment     : taint_source.

(** Sanitizer kinds — mirrors Syntax.v sanitizer *)
Inductive sanitizer : Type :=
  | SanSqlParam      : sanitizer   (* SQL parameterized query *)
  | SanHtmlEscape    : sanitizer   (* HTML entity encoding *)
  | SanJsEscape      : sanitizer   (* JavaScript string escaping *)
  | SanCssEscape     : sanitizer   (* CSS value escaping *)
  | SanUrlEncode     : sanitizer   (* URL percent-encoding *)
  | SanCommandEscape : sanitizer   (* Shell command escaping *)
  | SanLdapEscape    : sanitizer   (* LDAP filter escaping *)
  | SanPathSanitize  : sanitizer   (* Path traversal prevention *)
  | SanCsrfToken     : sanitizer.  (* CSRF token validation *)

(** Decidable equality on taint_source *)
Definition taint_source_eqb (t1 t2 : taint_source) : bool :=
  match t1, t2 with
  | TaintNetworkExternal, TaintNetworkExternal => true
  | TaintNetworkInternal, TaintNetworkInternal => true
  | TaintUserInput, TaintUserInput => true
  | TaintFileSystem, TaintFileSystem => true
  | TaintDatabase, TaintDatabase => true
  | TaintEnvironment, TaintEnvironment => true
  | _, _ => false
  end.

(** Decidable equality on sanitizer *)
Definition sanitizer_eqb (s1 s2 : sanitizer) : bool :=
  match s1, s2 with
  | SanSqlParam, SanSqlParam => true
  | SanHtmlEscape, SanHtmlEscape => true
  | SanJsEscape, SanJsEscape => true
  | SanCssEscape, SanCssEscape => true
  | SanUrlEncode, SanUrlEncode => true
  | SanCommandEscape, SanCommandEscape => true
  | SanLdapEscape, SanLdapEscape => true
  | SanPathSanitize, SanPathSanitize => true
  | SanCsrfToken, SanCsrfToken => true
  | _, _ => false
  end.

(** Types — simplified model of Syntax.v ty focused on taint *)
Inductive ty : Type :=
  | TUnit    : ty
  | TBool    : ty
  | TInt     : ty
  | TString  : ty
  | TFn      : ty -> ty -> ty              (* T1 -> T2 *)
  | TProd    : ty -> ty -> ty              (* T1 * T2 *)
  | TList    : ty -> ty                    (* List T *)
  | TTainted : ty -> taint_source -> ty    (* Tainted<T, src> *)
  | TSanitized : ty -> sanitizer -> ty.    (* Sanitized<T, san> *)

(** Expressions — simplified, focused on taint-relevant operations *)
Inductive expr : Type :=
  | EUnit    : expr
  | ETrue    : expr
  | EFalse   : expr
  | EInt     : nat -> expr
  | EStr     : string -> expr
  | EVar     : string -> expr
  | EAbs     : string -> ty -> expr -> expr   (* λx:T. e *)
  | EApp     : expr -> expr -> expr            (* e1 e2 *)
  | ELet     : string -> expr -> expr -> expr  (* let x = e1 in e2 *)
  | EIf      : expr -> expr -> expr -> expr    (* if e1 then e2 else e3 *)
  | EPair    : expr -> expr -> expr            (* (e1, e2) *)
  | EFst     : expr -> expr                    (* fst e *)
  | ESnd     : expr -> expr                    (* snd e *)
  (* Taint-specific operations *)
  | ETaint   : taint_source -> expr -> expr    (* Mark data as tainted *)
  | ESanitize : sanitizer -> expr -> expr      (* Apply sanitizer *)
  | EUseSink : sanitizer -> expr -> expr.      (* Use at sensitive sink *)

(** Values *)
Inductive value : expr -> Prop :=
  | v_unit   : value EUnit
  | v_true   : value ETrue
  | v_false  : value EFalse
  | v_int    : forall n, value (EInt n)
  | v_str    : forall s, value (EStr s)
  | v_abs    : forall x T e, value (EAbs x T e)
  | v_pair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  (* Tainted and sanitized values *)
  | v_taint  : forall src v, value v -> value (ETaint src v)
  | v_sanitize : forall san v, value v -> value (ESanitize san v).

(** Typing environment *)
Definition env := list (string * ty).

Fixpoint lookup (x : string) (Γ : env) : option ty :=
  match Γ with
  | nil => None
  | (y, T) :: rest => if String.eqb x y then Some T else lookup x rest
  end.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 2: TYPING RULES                                                  *)
(* Mirrors: riina-typechecker check_taint + types_compatible               *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Typing judgment: Γ ⊢ e : T *)
Inductive has_type : env -> expr -> ty -> Prop :=
  (* Standard rules *)
  | T_Unit   : forall Γ, has_type Γ EUnit TUnit
  | T_True   : forall Γ, has_type Γ ETrue TBool
  | T_False  : forall Γ, has_type Γ EFalse TBool
  | T_Int    : forall Γ n, has_type Γ (EInt n) TInt
  | T_Str    : forall Γ s, has_type Γ (EStr s) TString
  | T_Var    : forall Γ x T,
      lookup x Γ = Some T ->
      has_type Γ (EVar x) T
  | T_Abs    : forall Γ x T1 T2 e,
      has_type ((x, T1) :: Γ) e T2 ->
      has_type Γ (EAbs x T1 e) (TFn T1 T2)
  | T_App    : forall Γ e1 e2 T1 T2,
      has_type Γ e1 (TFn T1 T2) ->
      has_type Γ e2 T1 ->
      has_type Γ (EApp e1 e2) T2
  | T_Let    : forall Γ x e1 e2 T1 T2,
      has_type Γ e1 T1 ->
      has_type ((x, T1) :: Γ) e2 T2 ->
      has_type Γ (ELet x e1 e2) T2
  | T_If     : forall Γ e1 e2 e3 T,
      has_type Γ e1 TBool ->
      has_type Γ e2 T ->
      has_type Γ e3 T ->
      has_type Γ (EIf e1 e2 e3) T
  | T_Pair   : forall Γ e1 e2 T1 T2,
      has_type Γ e1 T1 ->
      has_type Γ e2 T2 ->
      has_type Γ (EPair e1 e2) (TProd T1 T2)
  | T_Fst    : forall Γ e T1 T2,
      has_type Γ e (TProd T1 T2) ->
      has_type Γ (EFst e) T1
  | T_Snd    : forall Γ e T1 T2,
      has_type Γ e (TProd T1 T2) ->
      has_type Γ (ESnd e) T2

  (* ════ TAINT RULES (Worker E core) ════ *)

  (* T_Taint: Marking data as tainted wraps type *)
  (* Matches: Rust Ty::Tainted(Box::new(inner), source) *)
  | T_Taint  : forall Γ src e T,
      has_type Γ e T ->
      has_type Γ (ETaint src e) (TTainted T src)

  (* T_Sanitize: Sanitizing removes taint and wraps with sanitizer *)
  (* CRITICAL: Only accepts Tainted input *)
  (* Matches: Rust sanitize_sql/sanitize_html/etc. builtins *)
  | T_Sanitize : forall Γ san e T src,
      has_type Γ e (TTainted T src) ->
      has_type Γ (ESanitize san e) (TSanitized T san)

  (* T_UseSink: Using sanitized data at a sink requires matching sanitizer *)
  (* CRITICAL: san must match — SanSqlParam for SQL, SanHtmlEscape for HTML *)
  (* Matches: Rust TaintViolation/SanitizerMismatch errors *)
  | T_UseSink : forall Γ san e T,
      has_type Γ e (TSanitized T san) ->
      has_type Γ (EUseSink san e) T.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 3: SUBSTITUTION                                                  *)
(* ═══════════════════════════════════════════════════════════════════════ *)

Fixpoint subst (x : string) (s : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | ETrue => ETrue
  | EFalse => EFalse
  | EInt n => EInt n
  | EStr st => EStr st
  | EVar y => if String.eqb x y then s else EVar y
  | EAbs y T body =>
      if String.eqb x y then EAbs y T body
      else EAbs y T (subst x s body)
  | EApp e1 e2 => EApp (subst x s e1) (subst x s e2)
  | ELet y e1 e2 =>
      ELet y (subst x s e1)
        (if String.eqb x y then e2 else subst x s e2)
  | EIf e1 e2 e3 => EIf (subst x s e1) (subst x s e2) (subst x s e3)
  | EPair e1 e2 => EPair (subst x s e1) (subst x s e2)
  | EFst e => EFst (subst x s e)
  | ESnd e => ESnd (subst x s e)
  | ETaint src e => ETaint src (subst x s e)
  | ESanitize san e => ESanitize san (subst x s e)
  | EUseSink san e => EUseSink san (subst x s e)
  end.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 4: SMALL-STEP SEMANTICS                                          *)
(* ═══════════════════════════════════════════════════════════════════════ *)

Inductive step : expr -> expr -> Prop :=
  (* Beta reduction *)
  | S_AppAbs : forall x T body v,
      value v ->
      step (EApp (EAbs x T body) v) (subst x v body)
  | S_App1 : forall e1 e1' e2,
      step e1 e1' ->
      step (EApp e1 e2) (EApp e1' e2)
  | S_App2 : forall v1 e2 e2',
      value v1 ->
      step e2 e2' ->
      step (EApp v1 e2) (EApp v1 e2')
  (* Let *)
  | S_LetVal : forall x v e2,
      value v ->
      step (ELet x v e2) (subst x v e2)
  | S_Let1 : forall x e1 e1' e2,
      step e1 e1' ->
      step (ELet x e1 e2) (ELet x e1' e2)
  (* If *)
  | S_IfTrue : forall e2 e3,
      step (EIf ETrue e2 e3) e2
  | S_IfFalse : forall e2 e3,
      step (EIf EFalse e2 e3) e3
  | S_If1 : forall e1 e1' e2 e3,
      step e1 e1' ->
      step (EIf e1 e2 e3) (EIf e1' e2 e3)
  (* Pair *)
  | S_Pair1 : forall e1 e1' e2,
      step e1 e1' ->
      step (EPair e1 e2) (EPair e1' e2)
  | S_Pair2 : forall v1 e2 e2',
      value v1 ->
      step e2 e2' ->
      step (EPair v1 e2) (EPair v1 e2')
  | S_FstPair : forall v1 v2,
      value v1 -> value v2 ->
      step (EFst (EPair v1 v2)) v1
  | S_Fst : forall e e',
      step e e' ->
      step (EFst e) (EFst e')
  | S_SndPair : forall v1 v2,
      value v1 -> value v2 ->
      step (ESnd (EPair v1 v2)) v2
  | S_Snd : forall e e',
      step e e' ->
      step (ESnd e) (ESnd e')
  (* Taint: evaluate inner, then wrap *)
  | S_Taint : forall src e e',
      step e e' ->
      step (ETaint src e) (ETaint src e')
  (* Sanitize: evaluate inner, then wrap *)
  | S_Sanitize : forall san e e',
      step e e' ->
      step (ESanitize san e) (ESanitize san e')
  (* UseSink: unwrap both sanitize + taint layers to extract clean value *)
  (* ESanitize san (ETaint src v) is the canonical sanitized+tainted value *)
  (* EUseSink san strips both wrappers, producing the clean inner value *)
  | S_UseSinkVal : forall san src v,
      value v ->
      step (EUseSink san (ESanitize san (ETaint src v))) v
  | S_UseSink : forall san e e',
      step e e' ->
      step (EUseSink san e) (EUseSink san e').

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 5: TAINT SAFETY — Core Theorems                                  *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Theorem: Tainted data cannot be used at a sink without sanitization.
    This is the fundamental injection prevention guarantee. *)

(** No typing derivation exists for ETaint src e at a sink expecting
    TSanitized T san. The type system rejects it structurally. *)

Lemma taint_source_eqb_refl : forall t, taint_source_eqb t t = true.
Proof.
  destruct t; simpl; reflexivity.
Qed.

Lemma sanitizer_eqb_refl : forall s, sanitizer_eqb s s = true.
Proof.
  destruct s; simpl; reflexivity.
Qed.

Lemma taint_source_eqb_eq : forall t1 t2,
  taint_source_eqb t1 t2 = true -> t1 = t2.
Proof.
  intros t1 t2 H; destruct t1, t2; simpl in H; try discriminate; reflexivity.
Qed.

Lemma sanitizer_eqb_eq : forall s1 s2,
  sanitizer_eqb s1 s2 = true -> s1 = s2.
Proof.
  intros s1 s2 H; destruct s1, s2; simpl in H; try discriminate; reflexivity.
Qed.

(** Key structural lemma: TTainted <> TSanitized *)
Lemma tainted_not_sanitized : forall T1 T2 src san,
  TTainted T1 src <> TSanitized T2 san.
Proof.
  intros. discriminate.
Qed.

(** Tainted types are not base types *)
Lemma tainted_not_base : forall T src,
  TTainted T src <> TUnit /\
  TTainted T src <> TBool /\
  TTainted T src <> TInt /\
  TTainted T src <> TString.
Proof.
  intros. repeat split; discriminate.
Qed.

(** Sanitized types are not base types *)
Lemma sanitized_not_base : forall T san,
  TSanitized T san <> TUnit /\
  TSanitized T san <> TBool /\
  TSanitized T san <> TInt /\
  TSanitized T san <> TString.
Proof.
  intros. repeat split; discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 6: CANONICAL FORMS                                                *)
(* ═══════════════════════════════════════════════════════════════════════ *)

Lemma canonical_tainted : forall Γ v T src,
  value v -> has_type Γ v (TTainted T src) ->
  exists v', v = ETaint src v' /\ value v'.
Proof.
  intros Γ v T src Hval Htype.
  inversion Htype; subst; try solve [inversion Hval].
  eexists. split; eauto. inversion Hval; subst; auto.
Qed.

Lemma canonical_sanitized : forall Γ v T san,
  value v -> has_type Γ v (TSanitized T san) ->
  exists v', v = ESanitize san v' /\ value v'.
Proof.
  intros Γ v T san Hval Htype.
  inversion Htype; subst; try solve [inversion Hval].
  eexists. split; eauto. inversion Hval; subst; auto.
Qed.

Lemma canonical_fn : forall Γ v T1 T2,
  value v -> has_type Γ v (TFn T1 T2) ->
  exists x body, v = EAbs x T1 body.
Proof.
  intros Γ v T1 T2 Hval Htype.
  inversion Htype; subst; try solve [inversion Hval].
  eexists. eexists. reflexivity.
Qed.

Lemma canonical_bool : forall Γ v,
  value v -> has_type Γ v TBool ->
  v = ETrue \/ v = EFalse.
Proof.
  intros Γ v Hval Htype.
  inversion Htype; subst; try solve [inversion Hval]; auto.
Qed.

Lemma canonical_pair : forall Γ v T1 T2,
  value v -> has_type Γ v (TProd T1 T2) ->
  exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros Γ v T1 T2 Hval Htype.
  inversion Htype; subst; try solve [inversion Hval].
  inversion Hval; subst. eexists. eexists. split; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 7: PROGRESS — well-typed closed terms are values or can step    *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** A term is closed if it typechecks in the empty environment *)
Definition closed (e : expr) := exists T, has_type nil e T.

(** Progress theorem for taint-aware type system *)
Theorem taint_progress : forall e T,
  has_type nil e T ->
  value e \/ exists e', step e e'.
Proof.
  intros e T Htype.
  remember nil as Γ.
  induction Htype; subst.
  (* T_Unit *) - left. constructor.
  (* T_True *) - left. constructor.
  (* T_False *) - left. constructor.
  (* T_Int *) - left. constructor.
  (* T_Str *) - left. constructor.
  (* T_Var *) - simpl in H. discriminate.
  (* T_Abs *) - left. constructor.
  (* T_App *)
  - right.
    destruct IHHtype1 as [Hv1 | [e1' Hs1]]; auto.
    + destruct IHHtype2 as [Hv2 | [e2' Hs2]]; auto.
      * (* Both values: beta reduction *)
        destruct (canonical_fn _ _ _ _ Hv1 Htype1) as [x [body Heq]].
        subst. exists (subst x e2 body). constructor. assumption.
      * (* e2 steps *)
        exists (EApp e1 e2'). constructor; assumption.
    + (* e1 steps *)
      exists (EApp e1' e2). constructor. assumption.
  (* T_Let *)
  - right.
    destruct IHHtype1 as [Hv1 | [e1' Hs1]]; auto.
    + exists (subst x e1 e2). constructor. assumption.
    + exists (ELet x e1' e2). constructor. assumption.
  (* T_If *)
  - right.
    destruct IHHtype1 as [Hv1 | [e1' Hs1]]; auto.
    + destruct (canonical_bool _ _ Hv1 Htype1) as [Ht | Hf]; subst.
      * exists e2. constructor.
      * exists e3. constructor.
    + exists (EIf e1' e2 e3). constructor. assumption.
  (* T_Pair *)
  - destruct IHHtype1 as [Hv1 | [e1' Hs1]]; auto.
    + destruct IHHtype2 as [Hv2 | [e2' Hs2]]; auto.
      * left. constructor; assumption.
      * right. exists (EPair e1 e2'). constructor; assumption.
    + right. exists (EPair e1' e2). constructor. assumption.
  (* T_Fst *)
  - right.
    destruct IHHtype as [Hv | [e' Hs]]; auto.
    + destruct (canonical_pair _ _ _ _ Hv Htype) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. exists v1. constructor; assumption.
    + exists (EFst e'). constructor. assumption.
  (* T_Snd *)
  - right.
    destruct IHHtype as [Hv | [e' Hs]]; auto.
    + destruct (canonical_pair _ _ _ _ Hv Htype) as [v1 [v2 [Heq [Hv1 Hv2]]]].
      subst. exists v2. constructor; assumption.
    + exists (ESnd e'). constructor. assumption.
  (* T_Taint — value or step inner *)
  - destruct IHHtype as [Hv | [e' Hs]]; auto.
    + left. constructor. assumption.
    + right. exists (ETaint src e'). constructor. assumption.
  (* T_Sanitize — value or step inner *)
  - destruct IHHtype as [Hv | [e' Hs]]; auto.
    + left. constructor.
      destruct (canonical_tainted _ _ _ _ Hv Htype) as [v' [Heq Hv']].
      subst. inversion Hv; subst. assumption.
    + right. exists (ESanitize san e'). constructor. assumption.
  (* T_UseSink — step to unwrap or step inner *)
  - right.
    destruct IHHtype as [Hv | [e' Hs]]; auto.
    + destruct (canonical_sanitized _ _ _ _ Hv Htype) as [v' [Heq Hv']].
      subst. (* e = ESanitize san v', v' is a value with type TTainted T src *)
      inversion Htype; subst.
      match goal with
      | [ Htaint : has_type _ v' (TTainted _ _) |- _ ] =>
          destruct (canonical_tainted _ _ _ _ Hv' Htaint) as [v'' [Heq2 Hv'']];
          subst; exists v''; constructor; assumption
      end.
    + exists (EUseSink san e'). constructor. assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 8: SUBSTITUTION LEMMA — fully proven                            *)
(* Standard STLC substitution preservation, extended to taint/sanitize.    *)
(* Proof follows Pierce TAPL Ch. 9 / Software Foundations structure.       *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Free variable predicate for the taint expression language *)
Inductive appears_free_in : string -> expr -> Prop :=
  | afi_var   : forall x, appears_free_in x (EVar x)
  | afi_abs   : forall x y T e, x <> y -> appears_free_in x e ->
                  appears_free_in x (EAbs y T e)
  | afi_app1  : forall x e1 e2, appears_free_in x e1 ->
                  appears_free_in x (EApp e1 e2)
  | afi_app2  : forall x e1 e2, appears_free_in x e2 ->
                  appears_free_in x (EApp e1 e2)
  | afi_let1  : forall x y e1 e2, appears_free_in x e1 ->
                  appears_free_in x (ELet y e1 e2)
  | afi_let2  : forall x y e1 e2, x <> y -> appears_free_in x e2 ->
                  appears_free_in x (ELet y e1 e2)
  | afi_if1   : forall x e1 e2 e3, appears_free_in x e1 ->
                  appears_free_in x (EIf e1 e2 e3)
  | afi_if2   : forall x e1 e2 e3, appears_free_in x e2 ->
                  appears_free_in x (EIf e1 e2 e3)
  | afi_if3   : forall x e1 e2 e3, appears_free_in x e3 ->
                  appears_free_in x (EIf e1 e2 e3)
  | afi_pair1 : forall x e1 e2, appears_free_in x e1 ->
                  appears_free_in x (EPair e1 e2)
  | afi_pair2 : forall x e1 e2, appears_free_in x e2 ->
                  appears_free_in x (EPair e1 e2)
  | afi_fst   : forall x e, appears_free_in x e ->
                  appears_free_in x (EFst e)
  | afi_snd   : forall x e, appears_free_in x e ->
                  appears_free_in x (ESnd e)
  | afi_taint : forall x src e, appears_free_in x e ->
                  appears_free_in x (ETaint src e)
  | afi_san   : forall x san e, appears_free_in x e ->
                  appears_free_in x (ESanitize san e)
  | afi_sink  : forall x san e, appears_free_in x e ->
                  appears_free_in x (EUseSink san e).

Hint Constructors appears_free_in : core.

(** Free variables of well-typed terms exist in the context *)
Lemma free_in_context : forall x e Γ T,
  appears_free_in x e -> has_type Γ e T ->
  exists T', lookup x Γ = Some T'.
Proof.
  intros x e Γ T Hfree Htype.
  induction Htype; inversion Hfree; subst; eauto;
    match goal with
    | [ IH : appears_free_in ?y _ -> exists _, _ = _,
        Hafi : appears_free_in ?y _,
        Hneq : ?y <> ?z |- _ ] =>
        destruct (IH Hafi) as [T' Hlk];
        simpl in Hlk; destruct (String.eqb_spec y z); [contradiction | eauto]
    end.
Qed.

(** Context invariance: typing depends only on free variable lookups *)
Lemma context_invariance : forall Γ Γ' e T,
  has_type Γ e T ->
  (forall x, appears_free_in x e -> lookup x Γ = lookup x Γ') ->
  has_type Γ' e T.
Proof.
  intros Γ Γ' e T Htype. generalize dependent Γ'.
  induction Htype; intros Γ' Heq; try (econstructor; eauto; fail).
  - (* T_Var *)
    constructor. rewrite <- (Heq x); auto.
  - (* T_Abs *)
    constructor. apply IHHtype. intros y Hy. simpl.
    destruct (String.eqb_spec y x); [reflexivity | auto].
  - (* T_Let *)
    econstructor; eauto.
    apply IHHtype2. intros y Hy. simpl.
    destruct (String.eqb_spec y x); [reflexivity | auto].
Qed.

(** Terms typed in empty context have no free variables *)
Corollary typable_empty_closed : forall e T x,
  has_type nil e T -> ~ appears_free_in x e.
Proof.
  intros e T x Hty Hfree.
  destruct (free_in_context _ _ _ _ Hfree Hty) as [? Hlk].
  discriminate.
Qed.

(** Weakening from empty context to any context *)
Lemma weakening_empty : forall Γ e T,
  has_type nil e T -> has_type Γ e T.
Proof.
  intros. eapply context_invariance; eauto.
  intros x Hfree. exfalso. eapply typable_empty_closed; eauto.
Qed.

(** Substitution preserves typing — fully proven.
    Replaces the former axiom. Proof by induction on expression structure. *)
Lemma substitution_preserves_typing : forall Γ x U e v T,
  has_type ((x, U) :: Γ) e T ->
  has_type nil v U ->
  has_type Γ (subst x v e) T.
Proof.
  intros Γ x U e.
  generalize dependent Γ. generalize dependent U. generalize dependent x.
  induction e; intros x U Γ v T Hty Hv;
    simpl; inversion Hty; subst; try (econstructor; eauto; fail).
  - (* EVar s *)
    simpl. destruct (String.eqb_spec x s).
    + (* x = s: substitute *)
      subst. match goal with
      | [ H : lookup ?s ((?s, _) :: _) = Some _ |- _ ] =>
          simpl in H; rewrite String.eqb_refl in H;
          injection H as <-; apply weakening_empty; assumption
      end.
    + (* x <> s: variable unchanged *)
      constructor. match goal with
      | [ H : lookup s ((?x, _) :: ?G) = Some ?T |- lookup s ?G = Some ?T ] =>
          simpl in H; destruct (String.eqb_spec s x);
          [subst; contradiction | assumption]
      end.
  - (* EAbs s t e — binder case *)
    destruct (String.eqb_spec x s).
    + (* x = s: shadowed, body unchanged *)
      subst. constructor. eapply context_invariance; eauto.
      intros y Hy. simpl.
      destruct (String.eqb_spec y s); reflexivity.
    + (* x <> s: substitute into body *)
      constructor. apply IHe with U; auto.
      eapply context_invariance; eauto.
      intros y Hy. simpl.
      destruct (String.eqb_spec y s).
      * subst. simpl. destruct (String.eqb_spec s x).
        -- exfalso; auto.
        -- reflexivity.
      * reflexivity.
  - (* ELet s e1 e2 — binder case *)
    destruct (String.eqb_spec x s).
    + (* x = s: shadowed in e2 *)
      subst. econstructor; eauto. eapply context_invariance; eauto.
      intros y Hy. simpl.
      destruct (String.eqb_spec y s); reflexivity.
    + (* x <> s: substitute into both *)
      econstructor; eauto. apply IHe2 with U; auto.
      eapply context_invariance; eauto.
      intros y Hy. simpl.
      destruct (String.eqb_spec y s).
      * subst. simpl. destruct (String.eqb_spec s x).
        -- exfalso; auto.
        -- reflexivity.
      * reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 9: PRESERVATION — types are maintained through reduction          *)
(* ═══════════════════════════════════════════════════════════════════════ *)

Theorem taint_preservation : forall e e' Ty0,
  has_type nil e Ty0 ->
  step e e' ->
  has_type nil e' Ty0.
Proof.
  intros e e' Ty0 Htype Hstep.
  generalize dependent Ty0.
  induction Hstep; intros Ty0 Htype; inversion Htype; subst;
    try (econstructor; eauto; fail).
  (* S_AppAbs: beta reduction *)
  - match goal with
    | [ H : has_type _ (EAbs _ _ _) (TFn _ _) |- _ ] =>
        inversion H; subst; eapply substitution_preserves_typing; eauto
    end.
  (* S_LetVal: let reduction *)
  - eapply substitution_preserves_typing; eauto.
  (* S_IfTrue *)
  - assumption.
  (* S_IfFalse *)
  - assumption.
  (* S_FstPair: project first *)
  - match goal with
    | [ H : has_type _ (EPair _ _) (TProd _ _) |- _ ] =>
        inversion H; subst; assumption
    end.
  (* S_SndPair: project second *)
  - match goal with
    | [ H : has_type _ (EPair _ _) (TProd _ _) |- _ ] =>
        inversion H; subst; assumption
    end.
  (* S_UseSinkVal: unwrap both sanitize + taint wrappers *)
  (* EUseSink san (ESanitize san (ETaint src v)) → v *)
  (* Htype: has_type nil (EUseSink san (ESanitize san (ETaint src v))) Ty0 *)
  (* By T_UseSink: ESanitize san (ETaint src v) : TSanitized Ty0 san *)
  (* By T_Sanitize: ETaint src v : TTainted Ty0 src *)
  (* By T_Taint: v : Ty0 *)
  - match goal with
    | [ H : has_type _ (ESanitize _ (ETaint _ _)) (TSanitized _ _) |- _ ] =>
        inversion H; subst;
        match goal with
        | [ H2 : has_type _ (ETaint _ _) (TTainted _ _) |- _ ] =>
            inversion H2; subst; assumption
        end
    end.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 10: TYPE SAFETY — Progress + Preservation combined               *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Multi-step reduction *)
Inductive multi_step : expr -> expr -> Prop :=
  | multi_refl  : forall e, multi_step e e
  | multi_step1 : forall e1 e2 e3,
      step e1 e2 -> multi_step e2 e3 -> multi_step e1 e3.

Theorem taint_type_safety : forall e e' T,
  has_type nil e T ->
  multi_step e e' ->
  value e' \/ exists e'', step e' e''.
Proof.
  intros e e' T Htype Hsteps.
  induction Hsteps.
  - eapply taint_progress; eauto.
  - apply IHHsteps.
    eapply taint_preservation; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 11: TAINT NONINTERFERENCE — Sanitized sinks never see taint      *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Fundamental guarantee: No well-typed program can pass unsanitized
    tainted data to a sensitive sink. This is the injection prevention theorem. *)

(** If e has type T in the empty context, and e reduces to EUseSink san v
    where v is a value, then v must be ESanitize san v' for some v'. *)

(** If a well-typed program reaches EUseSink san e where e is a value,
    then e must be a sanitized+tainted value (ESanitize san (ETaint src v')). *)
Theorem injection_prevention : forall san e0 T,
  has_type nil (EUseSink san e0) T ->
  value e0 ->
  exists san' v' src, e0 = ESanitize san' (ETaint src v') /\ value v' /\ san = san'.
Proof.
  intros san e0 T Htype Hval.
  inversion Htype; subst.
  match goal with
  | [ Hsan : has_type _ e0 (TSanitized _ _) |- _ ] =>
      destruct (canonical_sanitized _ _ _ _ Hval Hsan) as [inner [Heq Hinner]];
      subst; inversion Hsan; subst;
      match goal with
      | [ Htaint : has_type _ inner (TTainted _ _) |- _ ] =>
          destruct (canonical_tainted _ _ _ _ Hinner Htaint) as [v' [Heq2 Hv']];
          subst; eexists; eexists; eexists; eauto
      end
  end.
Qed.

(** Corollary: Tainted values without sanitization cannot reach sinks *)
Corollary tainted_cannot_reach_sink : forall Γ src san e T,
  ~ has_type Γ (EUseSink san (ETaint src e)) T.
Proof.
  intros Γ src san e T Htype.
  inversion Htype; subst.
  match goal with
  | [ H : has_type _ (ETaint _ _) (TSanitized _ _) |- _ ] =>
      inversion H; subst; discriminate
  end.
Qed.

(** Stronger formulation: direct structural impossibility *)
Lemma taint_sink_structural_impossibility : forall Γ src san e T,
  has_type Γ (ETaint src e) (TSanitized T san) -> False.
Proof.
  intros Γ src san e T Htype.
  inversion Htype.
Qed.

(** Key lemma: TTainted and TSanitized are structurally disjoint types *)
Lemma tainted_neq_sanitized : forall T1 T2 src san,
  TTainted T1 src <> TSanitized T2 san.
Proof.
  intros. discriminate.
Qed.

(** An ETaint expression cannot have a TSanitized type *)
Theorem taint_expr_not_sanitized : forall Γ src e T san,
  has_type Γ (ETaint src e) (TSanitized T san) -> False.
Proof.
  intros. inversion H.
Qed.

(** An ESanitize expression cannot have a TTainted type *)
Theorem sanitize_expr_not_tainted : forall Γ san e T src,
  has_type Γ (ESanitize san e) (TTainted T src) -> False.
Proof.
  intros. inversion H.
Qed.

(** Combined: For value expressions, tainted and sanitized are disjoint *)
Theorem taint_sanitize_disjointness_values : forall Γ v T1 T2 src san,
  value v ->
  has_type Γ v (TTainted T1 src) ->
  has_type Γ v (TSanitized T2 san) ->
  False.
Proof.
  intros Γ v T1 T2 src san Hval Ht Hs.
  destruct v; try solve [inversion Hval]; inversion Ht; subst; inversion Hs; subst; discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 12: TAINT PROPAGATION THROUGH OPERATIONS                          *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Taint is preserved through pair construction *)
Lemma taint_preserved_pair_fst : forall Γ e1 e2 T1 T2 src,
  has_type Γ e1 (TTainted T1 src) ->
  has_type Γ e2 T2 ->
  has_type Γ (EPair e1 e2) (TProd (TTainted T1 src) T2).
Proof.
  intros. constructor; assumption.
Qed.

Lemma taint_preserved_pair_snd : forall Γ e1 e2 T1 T2 src,
  has_type Γ e1 T1 ->
  has_type Γ e2 (TTainted T2 src) ->
  has_type Γ (EPair e1 e2) (TProd T1 (TTainted T2 src)).
Proof.
  intros. constructor; assumption.
Qed.

(** Taint is preserved through let bindings *)
Lemma taint_preserved_let : forall Γ x e1 e2 T1 src T2,
  has_type Γ e1 (TTainted T1 src) ->
  has_type ((x, TTainted T1 src) :: Γ) e2 T2 ->
  has_type Γ (ELet x e1 e2) T2.
Proof.
  intros. econstructor; eauto.
Qed.

(** Sanitization is preserved through let bindings *)
Lemma sanitized_preserved_let : forall Γ x e1 e2 T san T2,
  has_type Γ e1 (TSanitized T san) ->
  has_type ((x, TSanitized T san) :: Γ) e2 T2 ->
  has_type Γ (ELet x e1 e2) T2.
Proof.
  intros. econstructor; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 13: SANITIZER MATCHING                                            *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Correct sanitizer for SQL context *)
Lemma sql_requires_sql_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanSqlParam e) T ->
  has_type Γ e (TSanitized T SanSqlParam).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for HTML context *)
Lemma html_requires_html_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanHtmlEscape e) T ->
  has_type Γ e (TSanitized T SanHtmlEscape).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for JS context *)
Lemma js_requires_js_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanJsEscape e) T ->
  has_type Γ e (TSanitized T SanJsEscape).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for command context *)
Lemma cmd_requires_cmd_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanCommandEscape e) T ->
  has_type Γ e (TSanitized T SanCommandEscape).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for LDAP context *)
Lemma ldap_requires_ldap_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanLdapEscape e) T ->
  has_type Γ e (TSanitized T SanLdapEscape).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for URL context *)
Lemma url_requires_url_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanUrlEncode e) T ->
  has_type Γ e (TSanitized T SanUrlEncode).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for CSS context *)
Lemma css_requires_css_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanCssEscape e) T ->
  has_type Γ e (TSanitized T SanCssEscape).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for path context *)
Lemma path_requires_path_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanPathSanitize e) T ->
  has_type Γ e (TSanitized T SanPathSanitize).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(** Correct sanitizer for CSRF context *)
Lemma csrf_requires_csrf_sanitizer : forall Γ e T,
  has_type Γ (EUseSink SanCsrfToken e) T ->
  has_type Γ e (TSanitized T SanCsrfToken).
Proof.
  intros Γ e T Htype.
  inversion Htype; subst. assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 13.5: UNIQUENESS OF TYPING                                        *)
(* The type system is syntax-directed: each expression has exactly one       *)
(* type in a given context. This is the key lemma enabling all attack        *)
(* impossibility proofs — if e : TTainted T src, then e cannot also          *)
(* have type TSanitized T' san in the same context.                          *)
(* ═══════════════════════════════════════════════════════════════════════ *)

Lemma lookup_deterministic : forall x Γ T1 T2,
  lookup x Γ = Some T1 -> lookup x Γ = Some T2 -> T1 = T2.
Proof.
  intros x Γ T1 T2 H1 H2. rewrite H1 in H2. congruence.
Qed.

(** Uniqueness of typing: each expression has at most one type.
    This holds because our type system is syntax-directed (no subtyping,
    no implicit coercions, no overloading). *)
Theorem typing_unique : forall Γ e T1 T2,
  has_type Γ e T1 -> has_type Γ e T2 -> T1 = T2.
Proof.
  intros Γ e T1 T2 H1. generalize dependent T2.
  induction H1; intros ? H2; inversion H2; subst;
    try reflexivity;
    (* T_Var: lookup determinism *)
    try (match goal with
         | [H1: lookup ?x ?G = Some _, H2: lookup ?x ?G = Some _ |- _] =>
             rewrite H1 in H2; congruence
         end);
    (* Type constructors: T_Abs, T_Pair, T_Taint *)
    try (f_equal; eauto; fail);
    (* Eliminators needing IH + congruence: T_App, T_Fst, T_Snd,
       T_Sanitize, T_UseSink *)
    try (match goal with
         | [IH: forall T, has_type ?G ?e T -> ?X = T,
            H: has_type ?G ?e _ |- _] =>
             pose proof (IH _ H); congruence
         end);
    (* Compound cases needing IH + subst + eauto: T_Let, T_If *)
    try (match goal with
         | [IH: forall T, has_type ?G ?e T -> ?X = T,
            H: has_type ?G ?e _ |- _] =>
             pose proof (IH _ H); subst; eauto
         end).
Qed.

(** Wrong sanitizer is rejected: HTML sanitizer cannot satisfy SQL sink.
    Proved trivially via typing_unique. *)
Lemma wrong_sanitizer_rejected : forall Γ e T,
  has_type Γ e (TSanitized T SanHtmlEscape) ->
  ~ has_type Γ (EUseSink SanSqlParam e) T.
Proof.
  intros Γ e T Htype Hwrong.
  inversion Hwrong; subst.
  match goal with
  | [ H : has_type _ e (TSanitized _ SanSqlParam) |- _ ] =>
      pose proof (typing_unique _ _ _ _ Htype H); congruence
  end.
Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 14: ATTACK CLASS IMPOSSIBILITY THEOREMS                           *)
(* All follow from typing_unique: if e has type TTainted T src, it cannot    *)
(* also have type TSanitized T san (different type constructors).             *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Tactic for proving attack impossibility:
    Given e : TTainted T src and EUseSink san e : T,
    invert UseSink to get e : TSanitized T san,
    then typing_unique gives TTainted = TSanitized, contradiction. *)
Ltac attack_impossible :=
  intros ? ? ? ? Htaint Hsink;
  inversion Hsink; subst;
  match goal with
  | [ H : has_type _ _ (TSanitized _ _) |- _ ] =>
      pose proof (typing_unique _ _ _ _ Htaint H); congruence
  end.

(** SQL Injection Prevention (CVSS 9.8 → IMPOSSIBLE)
    No well-typed RIINA program can pass unsanitized user input to a SQL query. *)
Theorem sql_injection_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanSqlParam e) T.
Proof. attack_impossible. Qed.

(** XSS Prevention — HTML context (CVSS 7.5 → IMPOSSIBLE) *)
Theorem xss_html_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanHtmlEscape e) T.
Proof. attack_impossible. Qed.

(** XSS Prevention — JavaScript context *)
Theorem xss_js_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanJsEscape e) T.
Proof. attack_impossible. Qed.

(** XSS Prevention — CSS context *)
Theorem xss_css_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanCssEscape e) T.
Proof. attack_impossible. Qed.

(** XSS Prevention — URL context *)
Theorem xss_url_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanUrlEncode e) T.
Proof. attack_impossible. Qed.

(** Command Injection Prevention (CVSS 9.8 → IMPOSSIBLE) *)
Theorem command_injection_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanCommandEscape e) T.
Proof. attack_impossible. Qed.

(** LDAP Injection Prevention *)
Theorem ldap_injection_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanLdapEscape e) T.
Proof. attack_impossible. Qed.

(** Path Traversal Prevention *)
Theorem path_traversal_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanPathSanitize e) T.
Proof. attack_impossible. Qed.

(** CSRF Prevention *)
Theorem csrf_impossible : forall Γ e T src,
  has_type Γ e (TTainted T src) ->
  ~ has_type Γ (EUseSink SanCsrfToken e) T.
Proof. attack_impossible. Qed.

(* ═══════════════════════════════════════════════════════════════════════ *)
(* SECTION 15: SUMMARY                                                       *)
(* ═══════════════════════════════════════════════════════════════════════ *)

(** Summary of proven properties:
    1. Progress (taint_progress): Well-typed closed terms are values or can step
    2. Preservation (taint_preservation): Types are maintained through reduction
    3. Type Safety (taint_type_safety): Well-typed programs don't get stuck
    4. Uniqueness of Typing (typing_unique): Each expression has exactly one type
    5. Injection Prevention (injection_prevention): Sink usage requires sanitization
    6. Taint/Sanitize Disjointness: A term cannot be both tainted and sanitized
    7. Structural Impossibility: 9 attack classes proven impossible:
       - SQL injection (CVSS 9.8)
       - XSS in 4 contexts: HTML, JS, CSS, URL (CVSS 7.5)
       - Command injection (CVSS 9.8)
       - LDAP injection
       - Path traversal
       - CSRF
    8. Sanitizer Matching: Each sink requires its specific sanitizer
    9. Wrong Sanitizer Rejection: Mismatched sanitizers are type errors
*)
