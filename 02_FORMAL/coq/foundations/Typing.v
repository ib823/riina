(** * RIINA Typing Rules

    Type system for RIINA.

    Reference: CTSS_v1_0_1.md, Section 4

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Semantics.
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

(** Lookup in store typing *)
Fixpoint store_ty_lookup (l : loc) (Σ : store_ty) : option (ty * security_level) :=
  match Σ with
  | nil => None
  | (l', T, sl) :: Σ' =>
      if Nat.eqb l l' then Some (T, sl) else store_ty_lookup l Σ'
  end.

(** Update store typing *)
Fixpoint store_ty_update (l : loc) (T : ty) (sl : security_level) (Σ : store_ty) : store_ty :=
  match Σ with
  | nil => (l, T, sl) :: nil
  | (l', T', sl') :: Σ' =>
      if Nat.eqb l l' then (l, T, sl) :: Σ' else (l', T', sl') :: store_ty_update l T sl Σ'
  end.

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
  | ELoc _ => False
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

  | T_Loc : forall Γ Σ Δ l T sl,
      store_ty_lookup l Σ = Some (T, sl) ->
      has_type Γ Σ Δ (ELoc l) (TRef T sl) EffectPure

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
      has_type Γ Σ Δ (EApp e1 e2) T2 (effect_join ε (effect_join ε1 ε2))

  (* Products *)
  | T_Pair : forall Γ Σ Δ e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type Γ Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (EPair e1 e2) (TProd T1 T2) (effect_join ε1 ε2)

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
      has_type Γ Σ Δ (ECase e x1 e1 x2 e2) T (effect_join ε (effect_join ε1 ε2))

  (* Control *)
  | T_If : forall Γ Σ Δ e1 e2 e3 T ε1 ε2 ε3,
      has_type Γ Σ Δ e1 TBool ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ e3 T ε3 ->
      has_type Γ Σ Δ (EIf e1 e2 e3) T (effect_join ε1 (effect_join ε2 ε3))

  | T_Let : forall Γ Σ Δ x e1 e2 T1 T2 ε1 ε2,
      has_type Γ Σ Δ e1 T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ e2 T2 ε2 ->
      has_type Γ Σ Δ (ELet x e1 e2) T2 (effect_join ε1 ε2)

  (* Effects *)
  | T_Perform : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EPerform eff e) T (effect_join ε eff)

  | T_Handle : forall Γ Σ Δ e x h T1 T2 ε1 ε2,
      has_type Γ Σ Δ e T1 ε1 ->
      has_type ((x, T1) :: Γ) Σ Δ h T2 ε2 ->
      has_type Γ Σ Δ (EHandle e x h) T2 (effect_join ε1 ε2)

  (* References *)
  | T_Ref : forall Γ Σ Δ e T l ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (ERef e l) (TRef T l) (effect_join ε EffectWrite)

  | T_Deref : forall Γ Σ Δ e T l ε,
      has_type Γ Σ Δ e (TRef T l) ε ->
      has_type Γ Σ Δ (EDeref e) T (effect_join ε EffectRead)

  | T_Assign : forall Γ Σ Δ e1 e2 T l ε1 ε2,
      has_type Γ Σ Δ e1 (TRef T l) ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ (EAssign e1 e2) TUnit (effect_join ε1 (effect_join ε2 EffectWrite))

  (* Security *)
  | T_Classify : forall Γ Σ Δ e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EClassify e) (TSecret T) ε

  | T_Declassify : forall Γ Σ Δ e1 e2 T ε1 ε2,
      has_type Γ Σ Δ e1 (TSecret T) ε1 ->
      has_type Γ Σ Δ e2 (TProof (TSecret T)) ε2 ->
      declass_ok e1 e2 ->
      has_type Γ Σ Δ (EDeclassify e1 e2) T (effect_join ε1 ε2)

  | T_Prove : forall Γ Σ Δ e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EProve e) (TProof T) ε

  (* Capabilities *)
  | T_Require : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (ERequire eff e) T (effect_join ε eff)

  | T_Grant : forall Γ Σ Δ eff e T ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (EGrant eff e) T ε.

(** Well-typed store: every typed location has a well-typed value in the store. *)
Definition store_wf (Σ : store_ty) (st : store) : Prop :=
  (forall l T sl,
     store_ty_lookup l Σ = Some (T, sl) ->
     exists v, store_lookup l st = Some v /\ has_type nil Σ Public v T EffectPure)
  /\
  (forall l v,
     store_lookup l st = Some v ->
     exists T sl, store_ty_lookup l Σ = Some (T, sl) /\ has_type nil Σ Public v T EffectPure).

(** Store typing extension *)
Definition store_ty_extends (Σ Σ' : store_ty) : Prop :=
  forall l T sl,
    store_ty_lookup l Σ = Some (T, sl) ->
    store_ty_lookup l Σ' = Some (T, sl).

(** ** Type Uniqueness

    The type system is syntax-directed, so each expression has at most
    one type derivable from a given context.
*)

Lemma type_uniqueness : forall Γ Σ Δ e T1 T2 ε1 ε2,
  has_type Γ Σ Δ e T1 ε1 ->
  has_type Γ Σ Δ e T2 ε2 ->
  T1 = T2 /\ ε1 = ε2.
Proof.
  intros Γ Σ Δ e T1 T2 ε1 ε2 H1 H2.
  generalize dependent T2.
  generalize dependent ε2.
  induction H1 as
    [ G S D
    | G S D b
    | G S D n
    | G S D s
    | G S D l T sl Hlookup
    | G S D x T Hlookup
    | G S D x T1 T2 e ε Ht IHt
    | G S D e1 e2 T1 T2 ε ε1 ε2 Ht1 IHt1 Ht2 IHt2
    | G S D e1 e2 T1 T2 ε1 ε2 Ht1 IHt1 Ht2 IHt2
    | G S D e T1 T2 ε Ht IHt
    | G S D e T1 T2 ε Ht IHt
    | G S D e T1 T2 ε Ht IHt
    | G S D e T1 T2 ε Ht IHt
    | G S D e x1 e1 x2 e2 T1 T2 T ε ε1 ε2 Ht1 IHt1 Ht2 IHt2 Ht3 IHt3
    | G S D e1 e2 e3 T ε1 ε2 ε3 Ht1 IHt1 Ht2 IHt2 Ht3 IHt3
    | G S D x e1 e2 T1 T2 ε1 ε2 Ht1 IHt1 Ht2 IHt2
    | G S D eff e T ε Ht IHt
    | G S D e x h T1 T2 ε1 ε2 Ht1 IHt1 Ht2 IHt2
    | G S D e T l ε Ht IHt
    | G S D e T l ε Ht IHt
    | G S D e1 e2 T l ε1 ε2 Ht1 IHt1 Ht2 IHt2
    | G S D e T ε Ht IHt
    | G S D e1 e2 T ε1 ε2 Ht1 IHt1 Ht2 IHt2 Hok
    | G S D e T ε Ht IHt
    | G S D eff e T ε Ht IHt
    | G S D eff e T ε Ht IHt
    ]; intros ε2' T2' H2; inversion H2; subst; try (split; reflexivity).
  - (* T_Loc *)
    match goal with
    | H1 : store_ty_lookup _ _ = Some _,
      H2 : store_ty_lookup _ _ = Some _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; split; reflexivity
    end.
  - (* T_Var *)
    match goal with
    | H1 : lookup _ _ = Some _,
      H2 : lookup _ _ = Some _ |- _ =>
        rewrite H1 in H2; inversion H2; subst; split; reflexivity
    end.
  - (* T_Lam *)
    match goal with
    | Hb : has_type ((?x, ?T1) :: _) _ _ _ _ _ |- _ =>
        specialize (IHt _ _ Hb) as [HT Heps]; subst; split; reflexivity
    end.
  - (* T_App *)
    match goal with
    | Ht1' : has_type _ _ _ _ _ _,
      Ht2' : has_type _ _ _ _ _ _ |- _ =>
        specialize (IHt1 _ _ Ht1') as [HT1 Heps1];
        specialize (IHt2 _ _ Ht2') as [HT2 Heps2];
        inversion HT1; subst; split; reflexivity
    end.
  - (* T_Pair *)
    repeat match goal with
    | Ht : has_type _ _ _ _ _ _ |- _ =>
        first
          [ specialize (IHt1 _ _ Ht) as [HT1 Heps1]; subst
          | specialize (IHt2 _ _ Ht) as [HT2 Heps2]; subst
          ]
    end;
    split; reflexivity.
  - (* T_Fst *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    inversion HT; subst; split; reflexivity.
  - (* T_Snd *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    inversion HT; subst; split; reflexivity.
  - (* T_Inl *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    subst; split; reflexivity.
  - (* T_Inr *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    subst; split; reflexivity.
  - (* T_Case *)
    specialize (IHt1 _ _ H10) as [HT0 Heps0].
    inversion HT0; subst.
    specialize (IHt2 _ _ H11) as [HT1 Heps1].
    specialize (IHt3 _ _ H12) as [HT2 Heps2].
    subst; split; reflexivity.
  - (* T_If *)
    first
      [ specialize (IHt1 _ _ H5) as [HT1 Heps1]
      | specialize (IHt1 _ _ H6) as [HT1 Heps1]
      | specialize (IHt1 _ _ H7) as [HT1 Heps1]
      ];
    first
      [ specialize (IHt2 _ _ H7) as [HT2 Heps2]
      | specialize (IHt2 _ _ H8) as [HT2 Heps2]
      | specialize (IHt2 _ _ H9) as [HT2 Heps2]
      ];
    first
      [ specialize (IHt3 _ _ H8) as [HT3 Heps3]
      | specialize (IHt3 _ _ H9) as [HT3 Heps3]
      | specialize (IHt3 _ _ H10) as [HT3 Heps3]
      ];
    rewrite HT2.
    rewrite Heps1, Heps2, Heps3.
    split; reflexivity.
  - (* T_Let *)
    inversion H2; subst; clear H2.
    specialize (IHt1 _ _ H7) as [HT1eq Heps1].
    rewrite HT1eq in *.
    specialize (IHt2 _ _ H11) as [HT2eq Heps2].
    rewrite Heps1, Heps2.
    subst.
    split; reflexivity.
  - (* T_Perform *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    subst; split; reflexivity.
  - (* T_Handle *)
    specialize (IHt1 _ _ H8) as [HT1eq Heps1].
    rewrite HT1eq in *.
    specialize (IHt2 _ _ H9) as [HT2eq Heps2].
    rewrite Heps1, Heps2.
    subst.
    split; reflexivity.
  - (* T_Ref *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    subst; split; reflexivity.
  - (* T_Deref *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    inversion HT; subst; split; reflexivity.
  - (* T_Assign *)
    match goal with
    | Ht1' : has_type _ _ _ _ _ _,
      Ht2' : has_type _ _ _ _ _ _ |- _ =>
        specialize (IHt1 _ _ Ht1') as [HT1 Heps1];
        specialize (IHt2 _ _ Ht2') as [HT2 Heps2];
        inversion HT1; subst; split; reflexivity
    end.
  - (* T_Classify *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    subst; split; reflexivity.
  - (* T_Declassify *)
    match goal with
    | Ht1' : has_type _ _ _ _ _ _,
      Ht2' : has_type _ _ _ _ _ _ |- _ =>
        specialize (IHt1 _ _ Ht1') as [HT1 Heps1];
        specialize (IHt2 _ _ Ht2') as [HT2 Heps2];
        inversion HT1; subst; split; reflexivity
    end.
  - (* T_Prove *)
    first
      [ specialize (IHt _ _ H4) as [HT Heps]
      | specialize (IHt _ _ H5) as [HT Heps]
      | specialize (IHt _ _ H6) as [HT Heps]
      | specialize (IHt _ _ H7) as [HT Heps]
      | specialize (IHt _ _ H8) as [HT Heps]
      | specialize (IHt _ _ H9) as [HT Heps]
      | specialize (IHt _ _ H10) as [HT Heps]
      ];
    subst; split; reflexivity.
  - (* T_Require *)
    match goal with
    | Ht' : has_type _ _ _ _ _ _ |- _ =>
        specialize (IHt _ _ Ht') as [HT Heps];
        subst; split; reflexivity
    end.
  - (* T_Grant *)
    match goal with
    | Ht' : has_type _ _ _ _ _ _ |- _ =>
        specialize (IHt _ _ Ht') as [HT Heps];
        subst; split; reflexivity
    end.
Qed.

(** End of Typing.v *)
