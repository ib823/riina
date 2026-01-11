(** * TERAS-LANG Typing Rules
    
    Type system for TERAS-LANG.
    
    Reference: CTSS_v1_0_1.md, Section 4
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TERAS.foundations.Syntax.
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

(** ** Typing Judgment
    
    Γ; Σ; Δ ⊢ e : T ! ε
    
    - Γ: type environment
    - Σ: store typing
    - Δ: security context (current security level)
    - e: expression
    - T: type
    - ε: effect
*)

Reserved Notation "Γ ';' Σ ';' Δ '⊢' e ':' T '!' ε" (at level 40).

Inductive has_type : type_env -> store_ty -> security_level -> 
                      expr -> ty -> effect -> Prop :=
  (* Values *)
  | T_Unit : forall Γ Σ Δ,
      Γ; Σ; Δ ⊢ EUnit : TUnit ! EffectPure
  
  | T_Bool : forall Γ Σ Δ b,
      Γ; Σ; Δ ⊢ (EBool b) : TBool ! EffectPure
  
  | T_Int : forall Γ Σ Δ n,
      Γ; Σ; Δ ⊢ (EInt n) : TInt ! EffectPure
  
  | T_String : forall Γ Σ Δ s,
      Γ; Σ; Δ ⊢ (EString s) : TString ! EffectPure
  
  | T_Var : forall Γ Σ Δ x T,
      lookup x Γ = Some T ->
      Γ; Σ; Δ ⊢ (EVar x) : T ! EffectPure
  
  (* Functions *)
  | T_Lam : forall Γ Σ Δ x T1 T2 e ε,
      ((x, T1) :: Γ); Σ; Δ ⊢ e : T2 ! ε ->
      Γ; Σ; Δ ⊢ (ELam x T1 e) : (TFn T1 T2 ε) ! EffectPure
  
  | T_App : forall Γ Σ Δ e1 e2 T1 T2 ε ε1 ε2,
      Γ; Σ; Δ ⊢ e1 : (TFn T1 T2 ε) ! ε1 ->
      Γ; Σ; Δ ⊢ e2 : T1 ! ε2 ->
      Γ; Σ; Δ ⊢ (EApp e1 e2) : T2 ! ε  (* Effect from function body *)
  
  (* Products *)
  | T_Pair : forall Γ Σ Δ e1 e2 T1 T2 ε1 ε2,
      Γ; Σ; Δ ⊢ e1 : T1 ! ε1 ->
      Γ; Σ; Δ ⊢ e2 : T2 ! ε2 ->
      Γ; Σ; Δ ⊢ (EPair e1 e2) : (TProd T1 T2) ! EffectPure
  
  | T_Fst : forall Γ Σ Δ e T1 T2 ε,
      Γ; Σ; Δ ⊢ e : (TProd T1 T2) ! ε ->
      Γ; Σ; Δ ⊢ (EFst e) : T1 ! ε
  
  | T_Snd : forall Γ Σ Δ e T1 T2 ε,
      Γ; Σ; Δ ⊢ e : (TProd T1 T2) ! ε ->
      Γ; Σ; Δ ⊢ (ESnd e) : T2 ! ε
  
  (* Sums *)
  | T_Inl : forall Γ Σ Δ e T1 T2 ε,
      Γ; Σ; Δ ⊢ e : T1 ! ε ->
      Γ; Σ; Δ ⊢ (EInl e T2) : (TSum T1 T2) ! ε
  
  | T_Inr : forall Γ Σ Δ e T1 T2 ε,
      Γ; Σ; Δ ⊢ e : T2 ! ε ->
      Γ; Σ; Δ ⊢ (EInr e T1) : (TSum T1 T2) ! ε
  
  | T_Case : forall Γ Σ Δ e x1 e1 x2 e2 T1 T2 T ε ε1 ε2,
      Γ; Σ; Δ ⊢ e : (TSum T1 T2) ! ε ->
      ((x1, T1) :: Γ); Σ; Δ ⊢ e1 : T ! ε1 ->
      ((x2, T2) :: Γ); Σ; Δ ⊢ e2 : T ! ε2 ->
      Γ; Σ; Δ ⊢ (ECase e x1 e1 x2 e2) : T ! ε
  
  (* Control *)
  | T_If : forall Γ Σ Δ e1 e2 e3 T ε1 ε2 ε3,
      Γ; Σ; Δ ⊢ e1 : TBool ! ε1 ->
      Γ; Σ; Δ ⊢ e2 : T ! ε2 ->
      Γ; Σ; Δ ⊢ e3 : T ! ε3 ->
      Γ; Σ; Δ ⊢ (EIf e1 e2 e3) : T ! ε1
  
  | T_Let : forall Γ Σ Δ x e1 e2 T1 T2 ε1 ε2,
      Γ; Σ; Δ ⊢ e1 : T1 ! ε1 ->
      ((x, T1) :: Γ); Σ; Δ ⊢ e2 : T2 ! ε2 ->
      Γ; Σ; Δ ⊢ (ELet x e1 e2) : T2 ! ε1

where "Γ ';' Σ ';' Δ '⊢' e ':' T '!' ε" := (has_type Γ Σ Δ e T ε).

(** ** Type Uniqueness *)

Lemma type_uniqueness : forall Γ Σ Δ e T1 T2 ε1 ε2,
  Γ; Σ; Δ ⊢ e : T1 ! ε1 ->
  Γ; Σ; Δ ⊢ e : T2 ! ε2 ->
  T1 = T2.
Proof.
  intros Γ Σ Δ e T1 T2 ε1 ε2 H1 H2.
  generalize dependent ε2.
  generalize dependent T2.
  induction H1; intros T2 ε2 H2; inversion H2; subst; try reflexivity.
  - (* Var *)
    rewrite H in H3. inversion H3. reflexivity.
  - (* Lam *)
    apply IHhas_type in H4. subst. reflexivity.
  - (* App *)
    apply IHhas_type1 in H3. inversion H3. subst. reflexivity.
  - (* Pair *)
    apply IHhas_type1 in H4. apply IHhas_type2 in H6. subst. reflexivity.
  - (* Fst *)
    apply IHhas_type in H3. inversion H3. reflexivity.
  - (* Snd *)
    apply IHhas_type in H3. inversion H3. reflexivity.
  - (* Inl *)
    apply IHhas_type in H3. subst. reflexivity.
  - (* Inr *)
    apply IHhas_type in H3. subst. reflexivity.
  - (* Case *)
    apply IHhas_type2 in H8. subst. reflexivity.
  - (* If *)
    apply IHhas_type2 in H6. subst. reflexivity.
  - (* Let *)
    apply IHhas_type2 in H5. subst. reflexivity.
Qed.

(** End of Typing.v *)
