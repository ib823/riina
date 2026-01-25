# CLAUDE AI WEB DELEGATION PROMPT — Missing Proof Infrastructure

**IMPORTANT: This prompt is 100% self-contained. Claude AI Web has NO access to any codebase files and NO prior knowledge of RIINA. ALL necessary definitions and context are provided below.**

---

## SECTION 0: WHAT IS RIINA?

RIINA (Rigorous Immutable Invariant — Normalized Axiom) is a formally verified programming language where ALL security properties are mathematically proven in Coq. The type system guarantees non-interference at compile time, meaning secret data cannot leak to public outputs.

**Environment:**
- Coq Version: 8.18.0
- All proofs must compile with `coqc`
- All proofs must end in `Qed.` (NO `Admitted.`)

---

## SECTION 1: COMPLETE TYPE DEFINITIONS

### 1.1 Basic Type Aliases

```coq
Require Import String.
Require Import List.
Require Import Nat.
Require Import ZArith.
Require Import Bool.
Require Import Lia.

(* Identifiers are strings *)
Definition ident := string.

(* Locations are natural numbers *)
Definition loc := nat.

(* Security levels *)
Definition security_level := nat.  (* 0 = public, 1+ = secret *)
Definition Public : security_level := 0.
Definition Secret : security_level := 1.

(* Effects *)
Definition effect_label := string.
Definition effect := list effect_label.
Definition EffectPure : effect := nil.

(* Shorthand for security label in store *)
Definition sec_label := security_level.
```

### 1.2 Core Type Definition

```coq
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
```

### 1.3 Expression Definition

```coq
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
```

### 1.4 Value Predicate

```coq
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
```

### 1.5 Free Variables and Closed Expressions

```coq
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
```

### 1.6 First-Order Type Predicate

```coq
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
```

---

## SECTION 2: STORE DEFINITIONS

```coq
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
Definition is_low (sl : sec_label) : bool := Nat.eqb sl 0.
```

---

## SECTION 3: TYPING JUDGMENT

```coq
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
  | T_Ref : forall Γ Σ Δ e T sl ε,
      has_type Γ Σ Δ e T ε ->
      has_type Γ Σ Δ (ERef e sl) (TRef T sl) ε
  | T_Deref : forall Γ Σ Δ e T sl ε,
      has_type Γ Σ Δ e (TRef T sl) ε ->
      has_type Γ Σ Δ (EDeref e) T ε
  | T_Assign : forall Γ Σ Δ e1 e2 T sl ε1 ε2,
      has_type Γ Σ Δ e1 (TRef T sl) ε1 ->
      has_type Γ Σ Δ e2 T ε2 ->
      has_type Γ Σ Δ (EAssign e1 e2) TUnit (ε1 ++ ε2).
```

---

## SECTION 4: STEP-INDEXED LOGICAL RELATIONS

### 4.1 Core Definition

The value relation `val_rel_n n Σ T v1 v2` holds when values `v1` and `v2` are indistinguishable at type `T` for `n` steps under store typing `Σ`.

```coq
(* First-order structural relation (no step indexing needed) *)
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists n, v1 = EInt n /\ v2 = EInt n
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TBytes => v1 = v2
  | TSecret _ => True  (* Secrets are always indistinguishable *)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | TCapability _ => True
  | TProof _ => True
  | TProd T1 T2 =>
      exists a1 b1 a2 b2,
        v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
        val_rel_at_type_fo T1 a1 a2 /\ val_rel_at_type_fo T2 b1 b2
  | TSum T1 T2 =>
      (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_at_type_fo T1 a1 a2) \/
      (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_at_type_fo T2 b1 b2)
  | TList T => True  (* Lists: simplified *)
  | TOption T => True
  | TFn _ _ _ => True  (* Deferred to step-indexed *)
  end.

(* Mutually recursive step-indexed relations *)
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
```

### 4.2 Cumulative Value Relation

```coq
(* val_rel_le n Σ T v1 v2 means: related at ALL steps m ≤ n *)
Definition val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  forall m, m <= n -> val_rel_n m Σ T v1 v2.

(* Cumulative store relation *)
Definition store_rel_le (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  forall m, m <= n -> store_rel_n m Σ st1 st2.
```

---

## SECTION 5: UNFOLD LEMMAS NEEDED

The proofs need these unfold lemmas. Provide COMPLETE proofs.

### 5.1 val_rel_n Unfold Lemmas (ALREADY PROVEN - for reference)

```coq
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
```

### 5.2 val_rel_le Unfold Lemmas (NEEDED)

**TASK: Prove these lemmas.**

```coq
(* Unfold val_rel_le at 0 *)
Lemma val_rel_le_0_unfold : forall Σ T v1 v2,
  val_rel_le 0 Σ T v1 v2 <->
  val_rel_n 0 Σ T v1 v2.
(* Hint: val_rel_le 0 means forall m, m <= 0 -> val_rel_n m ...
   The only m with m <= 0 is m = 0. *)

(* Unfold val_rel_le at S n *)
Lemma val_rel_le_S_unfold : forall n Σ T v1 v2,
  val_rel_le (S n) Σ T v1 v2 <->
  (val_rel_le n Σ T v1 v2 /\ val_rel_n (S n) Σ T v1 v2).
(* Hint: val_rel_le (S n) means forall m, m <= S n -> ...
   This is equivalent to (forall m, m <= n -> ...) /\ val_rel_n (S n) ... *)
```

### 5.3 store_rel_n Unfold Lemmas (NEEDED)

```coq
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
```

---

## SECTION 6: KRIPKE MONOTONICITY LEMMAS (NEEDED)

These lemmas establish that the relations respect store typing extension.

### 6.1 Store Typing Extension Properties

```coq
(* Reflexivity *)
Lemma store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
(* Hint: Unfold store_ty_extends. The identity function works. *)

(* Transitivity *)
Lemma store_ty_extends_trans : forall Σ1 Σ2 Σ3,
  store_ty_extends Σ1 Σ2 ->
  store_ty_extends Σ2 Σ3 ->
  store_ty_extends Σ1 Σ3.
(* Hint: Compose the lookup preservation. *)

(* Lookup decidability *)
Lemma store_ty_lookup_dec : forall l Σ,
  {exists T sl, store_ty_lookup l Σ = Some (T, sl)} +
  {store_ty_lookup l Σ = None}.
(* Hint: Induction on Σ, use Nat.eqb decidability. *)
```

### 6.2 Value Relation Monotonicity

```coq
(* Downward step monotonicity: larger n implies smaller n *)
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.
(* Hint: Induction on n, destruct m <= n cases. *)

(* Kripke store weakening for FO types *)
Lemma val_rel_n_weaken_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
(* Hint: For FO types, val_rel_at_type_fo doesn't depend on Σ. *)

(* Kripke store strengthening for FO types *)
Lemma val_rel_n_mono_store_fo : forall n Σ Σ' T v1 v2,
  first_order_type T = true ->
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ' T v1 v2.
(* Hint: Same as weaken - FO types are Σ-independent. *)
```

### 6.3 Typing Store Weakening

```coq
(* Typing is preserved under store extension *)
Lemma has_type_store_weakening : forall Γ Σ Σ' Δ e T ε,
  has_type Γ Σ Δ e T ε ->
  store_ty_extends Σ Σ' ->
  has_type Γ Σ' Δ e T ε.
(* Hint: Induction on the typing derivation. The key case is T_Loc
   where store_ty_extends ensures the location is still in Σ'. *)
```

---

## SECTION 7: EXTRACTION LEMMAS (NEEDED)

These lemmas extract properties from the relations.

```coq
(* Extract value property *)
Lemma val_rel_n_value : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 ->
  value v1 /\ value v2.
(* Hint: Rewrite with val_rel_n_S_unfold, destruct. *)

(* Extract closed property *)
Lemma val_rel_n_closed : forall n Σ T v1 v2,
  val_rel_n (S n) Σ T v1 v2 ->
  closed_expr v1 /\ closed_expr v2.
(* Hint: Same as above. *)

(* Extract same boolean from related booleans *)
Lemma val_rel_n_bool : forall n Σ v1 v2,
  val_rel_n (S n) Σ TBool v1 v2 ->
  exists b, v1 = EBool b /\ v2 = EBool b.
(* Hint: Unfold, extract val_rel_at_type_fo TBool. *)

(* Extract same location from related references *)
Lemma val_rel_n_ref : forall n Σ T sl v1 v2,
  val_rel_n (S n) Σ (TRef T sl) v1 v2 ->
  exists l, v1 = ELoc l /\ v2 = ELoc l.
(* Hint: Similar to bool case. *)
```

---

## SECTION 8: OUTPUT FORMAT

Provide a single Coq file named `ProofInfrastructure.v` with:

1. **All lemmas from Section 5-7 with COMPLETE proofs**
2. Each proof must end in `Qed.` (NO `Admitted.`)
3. Use standard tactics: `intros`, `destruct`, `induction`, `simpl`, `reflexivity`, `auto`, `lia`, `split`, `exists`, `apply`, `exact`, `rewrite`
4. Include brief comments explaining the proof strategy

**File structure:**
```coq
(** * ProofInfrastructure.v - Missing Lemmas for RIINA *)

Require Import String List Nat ZArith Bool Lia.

(* Include all type definitions from Section 1-4 *)

(** Section 5: Unfold Lemmas *)
(* ... proofs ... *)

(** Section 6: Kripke Monotonicity *)
(* ... proofs ... *)

(** Section 7: Extraction Lemmas *)
(* ... proofs ... *)

(** Summary *)
Theorem all_infrastructure_proven : True.
Proof. exact I. Qed.
```

---

**END OF PROMPT**
