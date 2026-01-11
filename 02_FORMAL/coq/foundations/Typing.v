(** * TERAS-LANG Typing Rules

    Type system for TERAS-LANG.

    Reference: CTSS_v1_0_1.md, Section 4

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Import ListNotations.

(** ** Type Environments *)

Definition type_env := list (ident * ty).

(** Lookup in type environment *)
Fixpoint lookup (x : ident) (Γ : type_env) : option ty :=
  match Γ with
  | nil => None
  | (y, T) :: Γ' => if String.eqb x y then Some T else lookup x Γ'
  end.

(** ** Store Typing *)

Definition store_ty := list (loc * ty * security_level).

(** ** Free Variables

    Predicate to check if a variable occurs free in an expression.
    This is essential for the substitution lemma.
*)

Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EUnit => False
  | EBool _ => False
  | EInt _ => False
  | EString _ => False
  | EVar y => x = y
  | ELam y _ body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  | EPair e1 e2 => free_in x e1 \/ free_in x e2
  | EFst e0 => free_in x e0
  | ESnd e0 => free_in x e0
  | EInl e0 _ => free_in x e0
  | EInr e0 _ => free_in x e0
  | ECase e0 y1 e1 y2 e2 =>
      free_in x e0 \/ (x <> y1 /\ free_in x e1) \/ (x <> y2 /\ free_in x e2)
  | EIf e1 e2 e3 => free_in x e1 \/ free_in x e2 \/ free_in x e3
  | ELet y e1 e2 => free_in x e1 \/ (x <> y /\ free_in x e2)
  | EPerform _ e0 => free_in x e0
  | EHandle e0 y h => free_in x e0 \/ (x <> y /\ free_in x h)
  | ERef e0 _ => free_in x e0
  | EDeref e0 => free_in x e0
  | EAssign e1 e2 => free_in x e1 \/ free_in x e2
  | EClassify e0 => free_in x e0
  | EDeclassify e1 e2 => free_in x e1 \/ free_in x e2
  | EProve e0 => free_in x e0
  | ERequire _ e0 => free_in x e0
  | EGrant _ e0 => free_in x e0
  end.

(** ** Typing Judgment

    has_type Γ Σ Δ e T ε means: under environment Γ, store typing Σ,
    and security context Δ, expression e has type T with effect ε.
*)

Inductive has_type : type_env -> store_ty -> security_level ->
                      expr -> ty -> effect -> Prop :=
  (* Values *)
  | T_Unit : forall Γ Σ Δ,
      has_type Γ Σ Δ EUnit TUnit EffectPure

  | T_Bool : forall Γ Σ Δ b,
      has_type Γ Σ Δ (EBool b) TBool EffectPure

  | T_Int : forall Γ Σ Δ n,
      has_type Γ Σ Δ (EInt n) TInt EffectPure

  | T_String : forall Γ Σ Δ s,
      has_type Γ Σ Δ (EString s) TString EffectPure

  | T_Var : forall Γ Σ Δ x T,
      lookup x Γ = Some T ->
      has_type Γ Σ Δ (EVar x) T EffectPure

  (* Functions *)
  | T_Lam : forall Γ Σ Δ x T1 T2 e ε,
      has_type ((x, T1) :: Γ) Σ Δ e T2 ε ->
      has_type Γ Σ Δ (ELam x T1 e) (TFn T1 T2 ε) EffectPure

  | T_App : forall Γ Σ Δ e1 e2 T1 T2 ε ε1 ε2,
      has_type Γ Σ Δ e1 (TFn T1 T2 ε) ε1 ->
      has_type Γ Σ Δ e2 T1 ε2 ->
      has_type Γ Σ Δ (EApp e1 e2) T2 ε

  (* Products *)
  | T_Pair : forall Γ Σ Δ e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type Γ Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (EPair e1 e2) (TProd T1 T2) EffectPure

  | T_Fst : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e (TProd T1 T2) ε ->
      has_type Γ Σ Δ (EFst e) T1 ε

  | T_Snd : forall Γ Σ Δ e T1 T2 ε,
      has_type Γ Σ Δ e (TProd T1 T2) ε ->
      has_type Γ Σ Δ (ESnd e) T2 ε

  (* Sums *)
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
      has_type Γ Σ Δ (ECase e x1 e1 x2 e2) T ε

  (* Control *)
  | T_If : forall Γ Σ Δ e1 e2 e3 T ε1 ε2 ε3,
      has_type Γ Σ Δ e1 TBool ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ e3 T ε3 ->
      has_type Γ Σ Δ (EIf e1 e2 e3) T ε1

  | T_Let : forall Γ Σ Δ x e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (ELet x e1 e2) T2 ε1.

(** ** Type Uniqueness

    The type system is syntax-directed, so each expression has at most
    one type derivable from a given context.

    NOTE: Proof temporarily admitted. The proof strategy is standard
    induction on the first typing derivation with inversion on the second.
    TODO: Complete this proof.
*)

Lemma type_uniqueness : forall Γ Σ Δ e T1 T2 ε1 ε2,
  has_type Γ Σ Δ e T1 ε1 ->
  has_type Γ Σ Δ e T2 ε2 ->
  T1 = T2.
Proof.
  intros Γ Σ Δ e T1 T2 ε1 ε2 H1 H2.
  generalize dependent ε2.
  generalize dependent T2.
  induction H1; intros T2' ε2' H2; inversion H2; subst;
    try reflexivity;
    eauto.
Admitted. (* TODO: Complete type uniqueness proof *)

(** End of Typing.v *)
