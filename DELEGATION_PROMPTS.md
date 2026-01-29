# Claude AI Web Delegation Prompts — Track A Axiom/Admit Elimination

## Overview

6 independent prompts, one per file. Each can run in parallel with no dependencies.

**Remaining work:**
| # | File | Admits | Axioms |
|---|------|--------|--------|
| 1 | NonInterference_v2_LogicalRelation.v | 11 | 5 |
| 2 | ReferenceOps.v | 6 | 0 |
| 3 | Declassification.v | 3 | 0 |
| 4 | KripkeProperties.v | 2 | 0 |
| 5 | ReducibilityFull.v | 0 | 3 |
| 6 | NonInterference_v2.v | 0 | 1 |

---

# ═══════════════════════════════════════════════════════════════
# PROMPT 1: NonInterference_v2_LogicalRelation.v (11 admits, 5 axioms)
# ═══════════════════════════════════════════════════════════════

```
I need you to analyze 5 axioms and 11 admitted lemmas in a Coq 8.18 step-indexed logical relations proof for the RIINA programming language. For each, either:
(A) Provide the COMPLETE Coq proof, OR
(B) Explain precisely WHY it's unprovable and suggest the MINIMAL fix.

CRITICAL: Your proofs must use ONLY tactics and lemmas listed in this prompt. Do NOT invent lemma names.

## CORE DEFINITIONS

### Types
```coq
Inductive ty : Type :=
  | TUnit | TBool | TInt | TString | TBytes
  | TFn (T1 T2 : ty) (eff : effect)
  | TProd (T1 T2 : ty) | TSum (T1 T2 : ty)
  | TList (T : ty) | TOption (T : ty)
  | TRef (T : ty) (sl : security_level) | TSecret (T : ty)
  | TLabeled (T : ty) (sl : security_level)
  | TTainted (T : ty) (sl : security_level)
  | TSanitized (T : ty) (sl : security_level)
  | TProof (T : ty) | TCapability (cap : capability)
  | TCapabilityFull (cap : capability)
  | TChan (T : ty) | TSecureChan (T : ty) (sl : security_level)
  | TConstantTime (T : ty) | TZeroizing (T : ty).
```

### Expressions (key constructors)
```coq
EUnit, EBool b, EInt i, EString s, EVar x, ELam x T body,
EApp e1 e2, ELet x e1 e2, EPair e1 e2, EFst e, ESnd e,
EInl e T, EInr e T, ECase e x1 e1 x2 e2, EIf e1 e2 e3,
ERef e sl, EDeref e, EAssign e1 e2, ELoc l,
EHandle e x h, EClassify e, EDeclassify e1 e2,
EPerform eff e, ERequire eff e, EGrant eff e, EProve e
```

### Values
```coq
Inductive value : expr -> Prop :=
  | VUnit : value EUnit | VBool : forall b, value (EBool b)
  | VInt : forall i, value (EInt i) | VString : forall s, value (EString s)
  | VLam : forall x T body, value (ELam x T body)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T)
  | VLoc : forall l, value (ELoc l)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve : forall v, value v -> value (EProve v).
```

### Step Relation (key rules)
```coq
ST_AppAbs : value v -> step (EApp (ELam x T body) v, st, ctx) (subst x v body, st, ctx)
ST_FstPair : value v1 -> value v2 -> step (EFst (EPair v1 v2), st, ctx) (v1, st, ctx)
ST_SndPair : value v1 -> value v2 -> step (ESnd (EPair v1 v2), st, ctx) (v2, st, ctx)
ST_LetValue : value v -> step (ELet x v e2, st, ctx) (subst x v e2, st, ctx)
ST_CaseInl : value v -> step (ECase (EInl v T2) x1 e1 x2 e2, st, ctx) (subst x1 v e1, st, ctx)
ST_CaseInr : value v -> step (ECase (EInr v T1) x1 e1 x2 e2, st, ctx) (subst x2 v e2, st, ctx)
MS_Refl : multi_step cfg cfg
MS_Step : step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3
```

### first_order_type
```coq
Fixpoint first_order_type (T : ty) : bool :=
  match T with
  | TUnit | TBool | TInt | TString | TBytes => true
  | TFn _ _ _ => false | TChan _ => false | TSecureChan _ _ => false
  | TProd T1 T2 => first_order_type T1 && first_order_type T2
  | TSum T1 T2 => first_order_type T1 && first_order_type T2
  | TRef _ _ => true | TCapability _ | TCapabilityFull _ => true
  | TList T' | TOption T' | TSecret T' | TLabeled T' _ | TTainted T' _
  | TSanitized T' _ | TProof T' | TConstantTime T' | TZeroizing T' => first_order_type T'
  end.
```

### val_rel_at_type (non-trivial cases only)
```coq
Section ValRelAtN.
  Variables (Σ : store_ty) (store_rel_pred val_rel_lower store_rel_lower : ...).

  (* TFn: Kripke function property *)
  | TFn T1 T2 eff =>
      forall Σ', store_ty_extends Σ Σ' ->
        forall x y, value x -> value y -> closed_expr x -> closed_expr y ->
          val_rel_lower Σ' T1 x y ->
          forall st1 st2 ctx,
            store_rel_pred Σ' st1 st2 ->
            store_wf Σ' st1 -> store_wf Σ' st2 ->
            stores_agree_low_fo Σ' st1 st2 ->
            exists v1' v2' st1' st2' ctx' Σ'',
              store_ty_extends Σ' Σ'' /\
              (EApp v1 x, st1, ctx) -->* (v1', st1', ctx') /\
              (EApp v2 y, st2, ctx) -->* (v2', st2', ctx') /\
              val_rel_lower Σ'' T2 v1' v2' /\ store_rel_lower Σ'' st1' st2' /\
              store_wf Σ'' st1' /\ store_wf Σ'' st2' /\ stores_agree_low_fo Σ'' st1' st2'
  (* TProd: structural *)
  | TProd T1 T2 => exists a1 b1 a2 b2, v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
      val_rel_lower Σ T1 a1 a2 /\ val_rel_lower Σ T2 b1 b2
  (* TSum: structural *)
  | TSum T1 T2 =>
      (exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ val_rel_lower Σ T1 a1 a2) \/
      (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ val_rel_lower Σ T2 b1 b2)
  (* TRef: same location *)
  | TRef T' _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  (* All other types: True *)
End ValRelAtN.
```

### val_rel_n (step-indexed value relation)
```coq
Fixpoint val_rel_n (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) {struct n} : Prop :=
  match n with
  | 0 => value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
         (if first_order_type T then val_rel_at_type_fo T v1 v2
          else has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure)
  | S n' => val_rel_n n' Σ T v1 v2 /\ value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
         (if first_order_type T then True
          else has_type nil Σ Public v1 T EffectPure /\ has_type nil Σ Public v2 T EffectPure) /\
         val_rel_at_type Σ (store_rel_n n') (val_rel_n n') (store_rel_n n') T v1 v2
  end.
```

### exp_rel_n (step-indexed expression relation)
```coq
Fixpoint exp_rel_n (n : nat) (Σ : store_ty) (T : ty) (e1 e2 : expr) {struct n} : Prop :=
  match n with
  | 0 => True
  | S n' =>
      forall Σ_cur st1 st2 ctx,
        store_ty_extends Σ Σ_cur ->
        store_rel_n n' Σ_cur st1 st2 ->
        exists v1 v2 st1' st2' ctx' Σ',
          store_ty_extends Σ_cur Σ' /\
          (e1, st1, ctx) -->* (v1, st1', ctx') /\
          (e2, st2, ctx) -->* (v2, st2', ctx') /\
          value v1 /\ value v2 /\
          val_rel_n n' Σ' T v1 v2 /\
          store_rel_n n' Σ' st1' st2'
  end.
```

### val_rel (limit)
```coq
Definition val_rel (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop := forall n, val_rel_n n Σ T v1 v2.
Definition exp_rel (Σ : store_ty) (T : ty) (e1 e2 : expr) : Prop := forall n, exp_rel_n n Σ T e1 e2.
```

### Environment relations
```coq
Definition env_rel_n (n : nat) (Σ : store_ty) (G : type_env) (rho1 rho2 : ident -> expr) : Prop :=
  forall x T, lookup x G = Some T -> val_rel_n n Σ T (rho1 x) (rho2 x).
Definition env_rel (Σ : store_ty) (G : type_env) (rho1 rho2 : ident -> expr) : Prop :=
  forall n, env_rel_n n Σ G rho1 rho2.
Definition env_typed (Σ : store_ty) (Γ : type_env) (rho : ident -> expr) : Prop :=
  forall x T, lookup x Γ = Some T -> value (rho x) /\ has_type nil Σ Public (rho x) T EffectPure.
```

### subst_rho (multi-substitution)
```coq
(* Applies an environment substitution rho to an expression *)
Definition subst_rho (rho : ident -> expr) (e : expr) : expr := ... (* standard multi-subst *)
```

### val_rel_at_type_fo (first-order structural relation)
```coq
Fixpoint val_rel_at_type_fo (T : ty) (v1 v2 : expr) : Prop :=
  match T with
  | TUnit => v1 = EUnit /\ v2 = EUnit
  | TBool => exists b, v1 = EBool b /\ v2 = EBool b
  | TInt => exists i, v1 = EInt i /\ v2 = EInt i
  | TString => exists s, v1 = EString s /\ v2 = EString s
  | TProd T1 T2 => exists x1 y1 x2 y2, v1 = EPair x1 y1 /\ v2 = EPair x2 y2 /\
      val_rel_at_type_fo T1 x1 x2 /\ val_rel_at_type_fo T2 y1 y2
  | TSum T1 T2 =>
      (exists x1 x2, v1 = EInl x1 T2 /\ v2 = EInl x2 T2 /\ val_rel_at_type_fo T1 x1 x2) \/
      (exists y1 y2, v1 = EInr y1 T1 /\ v2 = EInr y2 T1 /\ val_rel_at_type_fo T2 y1 y2)
  | TRef _ _ => exists l, v1 = ELoc l /\ v2 = ELoc l
  | _ => True
  end.
```

## AVAILABLE PROVEN LEMMAS (you may use these)

```coq
(* Value/closed extraction from val_rel_n *)
val_rel_n_value : forall n Σ T v1 v2, val_rel_n n Σ T v1 v2 -> value v1 /\ value v2. (* n > 0 case *)
val_rel_n_closed : forall n Σ T v1 v2, val_rel_n n Σ T v1 v2 -> closed_expr v1 /\ closed_expr v2. (* n > 0 *)
val_rel_n_mono : forall m n Σ T v1 v2, m <= n -> val_rel_n n Σ T v1 v2 -> val_rel_n m Σ T v1 v2.
val_rel_n_mono_store : forall n Σ Σ' T v1 v2, store_ty_extends Σ Σ' -> val_rel_n n Σ T v1 v2 -> val_rel_n n Σ' T v1 v2.
store_rel_n_mono : forall m n Σ st1 st2, m <= n -> store_rel_n n Σ st1 st2 -> store_rel_n m Σ st1 st2.
val_rel_n_step_up_from_combined : forall n T Σ v1 v2,
  val_rel_n n Σ T v1 v2 ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  val_rel_n (S n) Σ T v1 v2.
val_rel_n_step_up_fo : forall n Σ T v1 v2,
  first_order_type T = true -> val_rel_n (S n) Σ T v1 v2 -> forall m, val_rel_n m Σ T v1 v2.
val_rel_n_of_first_order : forall T Σ v1 v2 n,
  first_order_type T = true -> value v1 -> value v2 -> closed_expr v1 -> closed_expr v2 ->
  val_rel_at_type_fo T v1 v2 -> val_rel_n n Σ T v1 v2.

(* Unfold lemmas *)
val_rel_n_0_unfold, val_rel_n_S_unfold : ... (* definitional unfolding *)

(* Canonical forms *)
canonical_forms_fn : forall v T1 T2 ε ε' Σ, has_type nil Σ Public v (TFn T1 T2 ε) ε' -> value v -> exists x body, v = ELam x T1 body.
canonical_forms_prod : forall v T1 T2 ε Σ, has_type nil Σ Public v (TProd T1 T2) ε -> value v -> exists v1 v2, v = EPair v1 v2 /\ value v1 /\ value v2.
canonical_forms_sum : ...
canonical_forms_ref : ...

(* Typing *)
typing_nil_implies_closed : forall Σ Δ e T ε, has_type nil Σ Δ e T ε -> closed_expr e.
store_ty_extends_refl : forall Σ, store_ty_extends Σ Σ.
store_ty_extends_trans : forall Σ1 Σ2 Σ3, store_ty_extends Σ1 Σ2 -> store_ty_extends Σ2 Σ3 -> store_ty_extends Σ1 Σ3.

(* val_rel_at_type equivalence for FO types *)
val_rel_at_type_fo_equiv : forall T Σ sp vl sl v1 v2,
  first_order_type T = true -> val_rel_at_type Σ sp vl sl T v1 v2 <-> val_rel_at_type_fo T v1 v2.

(* Typing inversion *)
(* Standard inversion on has_type gives subtyping judgments for pair/sum/etc components *)
```

## THE 5 AXIOMS TO ANALYZE

### AXIOM 1: logical_relation_ref
```coq
Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e T ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ (TRef T l) (subst_rho rho1 (ERef e l)) (subst_rho rho2 (ERef e l)).
```
Context: This is the fundamental theorem case for ERef. It states: if e is well-typed at T, and rho1/rho2 are related environments, then (subst_rho rho1 (ERef e l)) and (subst_rho rho2 (ERef e l)) are expression-related at TRef T l.

### AXIOM 2: logical_relation_deref
```coq
Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n,
  has_type Γ Σ Δ e (TRef T l) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeref e)) (subst_rho rho2 (EDeref e)).
```

### AXIOM 3: logical_relation_assign
```coq
Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n,
  has_type Γ Σ Δ e1 (TRef T l) ε1 ->
  has_type Γ Σ Δ e2 T ε2 ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ TUnit (subst_rho rho1 (EAssign e1 e2)) (subst_rho rho2 (EAssign e1 e2)).
```

### AXIOM 4: logical_relation_declassify
```coq
Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n,
  has_type Γ Σ Δ e (TSecret T) ε ->
  env_rel Σ Γ rho1 rho2 ->
  rho_no_free_all rho1 -> rho_no_free_all rho2 ->
  exp_rel_n n Σ T (subst_rho rho1 (EDeclassify e p)) (subst_rho rho2 (EDeclassify e p)).
```

### AXIOM 5: val_rel_n_to_val_rel
```coq
Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
  value v1 -> value v2 ->
  (exists n, val_rel_n (S n) Σ T v1 v2) ->
  val_rel Σ T v1 v2.
```
Context: Converts step-indexed relation to limit relation for ALL types. For first-order types this is proven (val_rel_n_to_val_rel_fo). For higher-order types (TFn), the issue is: from val_rel_n (S n) you have val_rel_at_type at step n with predicates val_rel_n n/store_rel_n n, but val_rel needs it for ALL m.

## THE 11 ADMITTED LEMMAS

### ADMIT GROUP A: Product composition/decomposition (5 lemmas)

#### val_rel_n_prod_compose (2 admits inside)
```coq
Lemma val_rel_n_prod_compose : forall n Σ T1 T2 a1 b1 a2 b2,
  value a1 -> value b1 -> value a2 -> value b2 ->
  closed_expr a1 -> closed_expr b1 -> closed_expr a2 -> closed_expr b2 ->
  val_rel_n n Σ T1 a1 a2 -> val_rel_n n Σ T2 b1 b2 ->
  val_rel_n n Σ (TProd T1 T2) (EPair a1 b1) (EPair a2 b2).
```
Analysis: Needs to construct val_rel_n for TProd from component relations. For FO types straightforward. For HO types at step 0, needs typing for EPair (requires typing for components). Admits are in HO handling.

#### val_rel_n_from_prod_fst (3 admits inside)
```coq
Lemma val_rel_n_from_prod_fst : forall n Σ T1 T2 v1 v2,
  val_rel_n n Σ (TProd T1 T2) v1 v2 ->
  exists a1 a2, v1 = EPair a1 _ /\ v2 = EPair a2 _ /\ val_rel_n n Σ T1 a1 a2.
```

#### val_rel_n_from_prod_snd (similar to fst)

### ADMIT GROUP B: Sum composition/decomposition (4 lemmas)

#### val_rel_n_sum_inl (2 admits)
```coq
Lemma val_rel_n_sum_inl : forall n Σ T1 T2 v1 v2,
  value v1 -> value v2 -> closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T1 v1 v2 ->
  val_rel_n n Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2).
```

#### val_rel_n_sum_inr (2 admits)
Similar to inl for right injection.

#### val_rel_n_from_sum_inl (1 admit - empty proof)
```coq
Lemma val_rel_n_from_sum_inl : forall n Σ T1 T2 v1 v2,
  val_rel_n n Σ (TSum T1 T2) (EInl v1 T2) (EInl v2 T2) ->
  val_rel_n n Σ T1 v1 v2.
```

#### val_rel_n_from_sum_inr (1 admit - empty proof)

### ADMIT GROUP C: Security type wrapping (2 lemmas)

#### val_rel_n_classify
```coq
Lemma val_rel_n_classify : forall n Σ T v1 v2,
  value v1 -> value v2 -> closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ (TSecret T) (EClassify v1) (EClassify v2).
```

#### val_rel_n_prove
```coq
Lemma val_rel_n_prove : forall n Σ T v1 v2,
  value v1 -> value v2 -> closed_expr v1 -> closed_expr v2 ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n n Σ (TProof T) (EProve v1) (EProve v2).
```

## INSTRUCTIONS

For EACH axiom and admitted lemma:

1. If PROVABLE: provide the complete proof between Proof. and Qed.
2. If UNPROVABLE: state WHY and provide corrected signature + proof.
3. For axioms: determine if they can be proven as lemmas from the available infrastructure, or if they represent genuinely new proof obligations (like the fundamental theorem cases for ref/deref/assign/declassify).

Format:
```
=== ITEM N: [name] ===
STATUS: PROVABLE / UNPROVABLE / AXIOM-JUSTIFIED
PROOF or ANALYSIS:
```

Focus on items that CAN be proven. For axioms 1-4 (fundamental theorem cases), they likely CANNOT be proven without the full fundamental theorem proof infrastructure — explain what would be needed.
```

---

# ═══════════════════════════════════════════════════════════════
# PROMPT 2: ReferenceOps.v (6 admits)
# ═══════════════════════════════════════════════════════════════

```
I need you to prove or analyze 6 admitted lemmas in a Coq 8.18 step-indexed logical relations proof. The file deals with reference operations (ref, deref, assign) in a simple imperative lambda calculus.

CRITICAL: Proofs must compile in Coq 8.18. Only use tactics listed here.

## DEFINITIONS

### Expressions
```coq
Inductive expr : Type :=
  | EUnit | EBool (b : bool) | EInt (i : Z) | EString (s : string)
  | EVar (x : ident) | ELam (x : ident) (T : ty) (body : expr)
  | EApp (e1 e2 : expr) | ELet (x : ident) (e1 e2 : expr)
  | EPair (e1 e2 : expr) | EFst (e : expr) | ESnd (e : expr)
  | EInl (e : expr) (T : ty) | EInr (e : expr) (T : ty)
  | ECase (e : expr) (x1 : ident) (e1 : expr) (x2 : ident) (e2 : expr)
  | EIf (e1 e2 e3 : expr) | ERef (e : expr) (sl : security_level)
  | EDeref (e : expr) | EAssign (e1 e2 : expr) | ELoc (l : nat)
  | EHandle (e : expr) (x : ident) (h : expr)
  | EDeclassify (e : expr) (p : declassify_proof).
```

### Values
```coq
Inductive value : expr -> Prop :=
  | VUnit : value EUnit | VBool : forall b, value (EBool b)
  | VInt : forall i, value (EInt i) | VString : forall s, value (EString s)
  | VLam : forall x T body, value (ELam x T body)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T)
  | VLoc : forall l, value (ELoc l).
```

### Store operations
```coq
Definition store := list (nat * expr).
Definition store_lookup (l : nat) (st : store) : option expr := ... (* standard list lookup *)
Definition store_update (l : nat) (v : expr) (st : store) : store := ... (* update or append *)
Definition fresh_loc (st : store) : nat := store_max st. (* next unused location *)
Definition store_max (st : store) : nat := ... (* max location + 1 *)
```

### Step relation (reference-specific rules)
```coq
(* Ref *)
ST_RefValue : forall v sl st ctx,
  value v -> step (ERef v sl, st, ctx) (ELoc (fresh_loc st), store_update (fresh_loc st) v st, ctx)
ST_RefStep : forall e e' sl st st' ctx ctx',
  step (e, st, ctx) (e', st', ctx') -> step (ERef e sl, st, ctx) (ERef e' sl, st', ctx')

(* Deref *)
ST_DerefLoc : forall l v st ctx,
  store_lookup l st = Some v -> step (EDeref (ELoc l), st, ctx) (v, st, ctx)
ST_DerefStep : forall e e' st st' ctx ctx',
  step (e, st, ctx) (e', st', ctx') -> step (EDeref e, st, ctx) (EDeref e', st', ctx')

(* Assign *)
ST_AssignLoc : forall l v v_old st ctx,
  value v -> store_lookup l st = Some v_old ->
  step (EAssign (ELoc l) v, st, ctx) (EUnit, store_update l v st, ctx)
ST_Assign1 : step (e1, st, ctx) (e1', st', ctx') -> step (EAssign e1 e2, ...) (EAssign e1' e2, ...)
ST_Assign2 : value v1 -> step (e2, st, ctx) (e2', st', ctx') -> step (EAssign v1 e2, ...) (EAssign v1 e2', ...)
```

### Multi-step
```coq
Inductive multi_step : config -> config -> Prop :=
  | MS_Refl : forall cfg, multi_step cfg cfg
  | MS_Step : forall cfg1 cfg2 cfg3, step cfg1 cfg2 -> multi_step cfg2 cfg3 -> multi_step cfg1 cfg3.
```

### Key property: values don't step
```coq
(* NOT in file, but true by inspection of step rules *)
Lemma value_does_not_step : forall v st ctx cfg', value v -> ~ step (v, st, ctx) cfg'.
(* Provable by inversion on step *)
```

### Cumulative relations (from CumulativeRelation.v)
```coq
Definition store_rel_simple (Σ : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2.

Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True
  | S n' => val_rel_le n' Σ T v1 v2 /\ val_rel_struct (val_rel_le n') Σ T v1 v2
  end.

Definition store_rel_le (n : nat) (Σ : store_ty) (st1 st2 : store) : Prop :=
  store_max st1 = store_max st2 /\
  forall l T sl, store_ty_lookup l Σ = Some (T, sl) ->
    match store_lookup l st1, store_lookup l st2 with
    | Some v1, Some v2 => val_rel_le n Σ T v1 v2
    | _, _ => False
    end.

Definition exp_rel_le (n : nat) (Σ : store_ty) (T : ty)
    (e1 e2 : expr) (st1 st2 : store) (ctx : effect_ctx) : Prop :=
  forall k v1 v2 st1' st2' ctx',
    k <= n ->
    multi_step (e1, st1, ctx) (v1, st1', ctx') ->
    multi_step (e2, st2, ctx) (v2, st2', ctx') ->
    value v1 -> value v2 ->
    exists Σ', store_ty_extends Σ Σ' /\ val_rel_le k Σ' T v1 v2 /\ store_rel_simple Σ' st1' st2'.
```

## THE 6 LEMMAS

### LEMMA 1: multi_step_ref_inversion
```coq
Lemma multi_step_ref_inversion : forall e sl st v st' ctx,
  multi_step (ERef e sl, st, ctx) (v, st', ctx) ->
  value v ->
  exists v_inner st_mid l,
    multi_step (e, st, ctx) (v_inner, st_mid, ctx) /\
    value v_inner /\
    v = ELoc l /\
    st' = store_update l v_inner st_mid /\
    l = fresh_loc st_mid.
```
Analysis: Decompose multi-step evaluation of ERef. The evaluation proceeds by stepping e to a value v_inner, then ST_RefValue creates ELoc l. Key insight: ERef v_inner sl is NOT a value, so evaluation must proceed through ST_RefValue. Need strong induction on multi_step or the evaluation derivation.

### LEMMA 2: multi_step_deref_inversion
```coq
Lemma multi_step_deref_inversion : forall e st v st' ctx,
  multi_step (EDeref e, st, ctx) (v, st', ctx) ->
  value v ->
  exists l st_mid,
    multi_step (e, st, ctx) (ELoc l, st_mid, ctx) /\
    st' = st_mid /\
    store_lookup l st_mid = Some v.
```

### LEMMA 3: multi_step_assign_inversion
```coq
Lemma multi_step_assign_inversion : forall e1 e2 st v st' ctx,
  multi_step (EAssign e1 e2, st, ctx) (v, st', ctx) ->
  value v ->
  exists l v_val st_mid1 st_mid2,
    multi_step (e1, st, ctx) (ELoc l, st_mid1, ctx) /\
    multi_step (e2, st_mid1, ctx) (v_val, st_mid2, ctx) /\
    value v_val /\
    v = EUnit /\
    st' = store_update l v_val st_mid2.
```

### LEMMA 4: exp_rel_le_ref
```coq
Lemma exp_rel_le_ref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ T e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ (TRef T sl) (ERef e1 sl) (ERef e2 sl) st1 st2 ctx.
```

### LEMMA 5: exp_rel_le_deref
```coq
Lemma exp_rel_le_deref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ T (EDeref e1) (EDeref e2) st1 st2 ctx.
```

### LEMMA 6: exp_rel_le_assign
```coq
Lemma exp_rel_le_assign : forall n Σ T sl e1 e2 e1' e2' st1 st2 ctx,
  exp_rel_le n Σ (TRef T sl) e1 e2 st1 st2 ctx ->
  exp_rel_le n Σ T e1' e2' st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ TUnit (EAssign e1 e1') (EAssign e2 e2') st1 st2 ctx.
```

## INSTRUCTIONS

For each lemma:
1. PROVABLE: provide complete proof.
2. UNPROVABLE: explain why, provide corrected signature + proof.

Key challenge for lemmas 1-3: These are multi-step inversion lemmas. The standard approach is:
- For ERef: ERef is not a value, so multi_step must go through at least one step. The first step is either ST_RefStep (congruence on subexpression) or ST_RefValue (if subexpression is a value). Induction on multi_step with the invariant that the expression has ERef shape.
- Similarly for EDeref and EAssign.

Key challenge for lemmas 4-6: These compose the inversion lemmas with the proven helper lemmas (logical_relation_ref_proven, logical_relation_deref_proven, logical_relation_assign_proven).

IMPORTANT: The inversion lemmas (1-3) assume that the context `ctx` doesn't change during evaluation. Verify this is consistent with the step rules above (it is — ref/deref/assign steps preserve ctx).
```

---

# ═══════════════════════════════════════════════════════════════
# PROMPT 3: Declassification.v (3 admits)
# ═══════════════════════════════════════════════════════════════

```
I need you to analyze 3 admitted lemmas in a Coq 8.18 proof about declassification soundness in a step-indexed logical relations framework.

## DEFINITIONS

### Core types and expressions (same as other prompts)
Types: TUnit, TBool, TInt, TString, TFn T1 T2 eff, TProd T1 T2, TSum T1 T2, TRef T sl, TSecret T, ...
Expressions: EUnit, EBool b, ELam x T body, EApp e1 e2, EPair e1 e2, EClassify e, EDeclassify e1 e2, ...
Values: VUnit, VBool, VLam, VPair, VInl, VInr, VLoc, VClassify v (value v -> value (EClassify v))

### Declassification stepping
```coq
ST_DeclassifyValue : forall v p st ctx,
  value v ->
  (* EDeclassify expects a secret value (EClassify v') and proof *)
  exists v', v = EClassify v' ->
  step (EDeclassify v p, st, ctx) (v', st, ctx)
```

### Cumulative relations (val_rel_le, store_rel_le, exp_rel_le)
Same definitions as in Prompt 2 (ReferenceOps).

### val_rel_struct for TSecret
```coq
val_rel_struct ... TSecret _ := True  (* Secret values are ALWAYS indistinguishable *)
```
This means: at any positive step, val_rel_le (S n) Σ (TSecret T) v1 v2 holds for ANY two values v1, v2 (as long as they satisfy value, closed_expr). The inner type T is irrelevant for the secret relation.

## THE 3 LEMMAS

### LEMMA 1: eval_deterministic
```coq
Lemma eval_deterministic : forall e st ctx v1 st1 v2 st2,
  multi_step (e, st, ctx) (v1, st1, ctx) ->
  multi_step (e, st, ctx) (v2, st2, ctx) ->
  value v1 -> value v2 ->
  v1 = v2 /\ st1 = st2.
```
Analysis: This IS provable. It's the determinism of evaluation. The step relation is deterministic (each configuration has at most one successor). Proof approach:
1. Prove step is deterministic: step c1 c2 -> step c1 c3 -> c2 = c3
2. Prove multi_step to values is deterministic by induction on the first derivation, using that values don't step.

### LEMMA 2: same_expr_related_stores_related_results
```coq
Lemma same_expr_related_stores_related_results : forall n Σ T e st1 st2 ctx v1 v2 st1' st2',
  store_rel_le n Σ st1 st2 ->
  multi_step (e, st1, ctx) (v1, st1', ctx) ->
  multi_step (e, st2, ctx) (v2, st2', ctx) ->
  value v1 -> value v2 ->
  val_rel_le n Σ T v1 v2.
```
Analysis: This is FALSE. Counterexample: e = EDeref (ELoc 0), st1 has loc 0 -> EInt 5, st2 has loc 0 -> EInt 7. Both evaluate, v1 = EInt 5, v2 = EInt 7. val_rel_le at TInt requires same int, which fails.

### LEMMA 3: exp_rel_le_declassify
```coq
Lemma exp_rel_le_declassify : forall n Σ T e1 e2 p st1 st2 ctx,
  exp_rel_le n Σ (TSecret T) e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  e1 = e2 ->
  exp_rel_le n Σ T (EDeclassify e1 p) (EDeclassify e2 p) st1 st2 ctx.
```
Analysis: The key insight is e1 = e2 (same expression). Since val_rel_le for TSecret is trivially True, the exp_rel_le premise gives us that both copies evaluate. Since e1 = e2 and contexts match, by determinism both produce the same results, making val_rel_le at T hold reflexively. BUT: this only works if the expression is pure (doesn't read from store). If it reads from different stores, results differ.

## INSTRUCTIONS

For each lemma:
1. PROVABLE: provide complete proof.
2. UNPROVABLE: explain why, provide corrected signature + proof.

For lemma 1, prove step determinism first as a helper lemma, then use it.
For lemma 2, provide counterexample and corrected version.
For lemma 3, analyze what additional premises would make it provable.
```

---

# ═══════════════════════════════════════════════════════════════
# PROMPT 4: KripkeProperties.v (2 admits)
# ═══════════════════════════════════════════════════════════════

```
I need you to fix 2 admits in a Coq 8.18 proof about step-independence of the cumulative value relation for first-order compound types (TProd and TSum).

## CONTEXT

The lemma `val_rel_le_step_up_fo` proves that for first-order types, if values are related at step n > 0, they're related at any step m. All 22 type cases are handled except TProd and TSum.

### The problem
For TProd at step n=1: val_rel_le 1 Σ (TProd T1 T2) v1 v2 gives val_rel_le 0 components, which is True. Cannot reconstruct structural info from True.

### The solution
The lemma needs a STRONGER premise: n > fo_compound_depth T instead of n > 0.

## DEFINITIONS

### fo_compound_depth
```coq
Fixpoint fo_compound_depth (T : ty) : nat :=
  match T with
  | TProd T1 T2 => 1 + Nat.max (fo_compound_depth T1) (fo_compound_depth T2)
  | TSum T1 T2 => 1 + Nat.max (fo_compound_depth T1) (fo_compound_depth T2)
  | _ => 0
  end.
```

### val_rel_le (cumulative)
```coq
Fixpoint val_rel_le (n : nat) (Σ : store_ty) (T : ty) (v1 v2 : expr) : Prop :=
  match n with
  | 0 => True
  | S n' => val_rel_le n' Σ T v1 v2 /\ val_rel_struct (val_rel_le n') Σ T v1 v2
  end.
```

### val_rel_struct for TProd/TSum
```coq
val_rel_struct vr Σ (TProd T1 T2) v1 v2 :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  exists a1 b1 a2 b2, v1 = EPair a1 b1 /\ v2 = EPair a2 b2 /\
    vr Σ T1 a1 a2 /\ vr Σ T2 b1 b2.

val_rel_struct vr Σ (TSum T1 T2) v1 v2 :=
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\
  ((exists a1 a2, v1 = EInl a1 T2 /\ v2 = EInl a2 T2 /\ vr Σ T1 a1 a2) \/
   (exists b1 b2, v1 = EInr b1 T1 /\ v2 = EInr b2 T1 /\ vr Σ T2 b1 b2)).
```

### Available proven lemmas
```coq
val_rel_le_fo_step_independent : forall m n Σ T v1 v2,
  first_order_type T = true -> m > fo_compound_depth T -> n > 0 ->
  val_rel_le m Σ T v1 v2 -> val_rel_le n Σ T v1 v2.

val_rel_le_extract_fo : forall T m Σ v1 v2,
  first_order_type T = true -> m > fo_compound_depth T ->
  val_rel_le m Σ T v1 v2 ->
  value v1 /\ value v2 /\ closed_expr v1 /\ closed_expr v2 /\ val_rel_at_type_fo T v1 v2.

val_rel_le_construct_fo : forall T n Σ v1 v2,
  first_order_type T = true -> n > 0 ->
  value v1 -> value v2 -> closed_expr v1 -> closed_expr v2 ->
  val_rel_at_type_fo T v1 v2 -> val_rel_le n Σ T v1 v2.
```

## TASK

Provide ONE of these solutions:

**Option A:** Fix the lemma by strengthening the premise from `n > 0` to `n > fo_compound_depth T`. Provide the corrected lemma statement and complete proof including the TProd and TSum cases.

**Option B:** If the original statement with `n > 0` IS provable for TProd/TSum through some other approach, provide that proof.

For Option A, the TProd case should use val_rel_le_fo_step_independent (which already handles the depth requirement). The key is just replacing the admits with applications of that lemma.
```

---

# ═══════════════════════════════════════════════════════════════
# PROMPT 5: ReducibilityFull.v (3 axioms)
# ═══════════════════════════════════════════════════════════════

```
I need you to analyze 3 axioms in a Coq 8.18 strong normalization proof for a typed lambda calculus with references. Determine if each axiom can be PROVEN as a lemma or if it must remain as a justified axiom.

## CONTEXT

The file proves well_typed_SN: well-typed closed terms are strongly normalizing (SN). SN is defined via Acc (accessibility predicate) on the inverse step relation.

```coq
Definition SN (cfg : config) : Prop := Acc (fun c2 c1 => step c1 c2) cfg.
Definition SN_expr (e : expr) : Prop := forall st ctx, SN (e, st, ctx).
```

The proof uses reducibility candidates (Girard's method):
- Define reducibility predicate RED(T) for each type T
- Show RED(T) ⊆ SN for all T
- Show well-typed terms are in RED(T)

## THE 3 AXIOMS

### AXIOM 1: env_reducible_closed
```coq
Axiom env_reducible_closed : forall Γ ρ, env_reducible Γ ρ -> closed_rho ρ.
```
Where:
```coq
Definition env_reducible (Γ : type_env) (ρ : ident -> expr) : Prop :=
  forall x T, lookup x Γ = Some T -> reducible T (ρ x).
Definition closed_rho (ρ : ident -> expr) : Prop :=
  forall x, closed_expr (ρ x).
Definition reducible (T : ty) (e : expr) : Prop := SN_expr e /\ ... (* type-specific conditions *)
```

Analysis: env_reducible means every variable in Γ maps to a reducible term. Reducible terms are SN. But does SN imply closed_expr? NO — SN is about step termination, not about free variables. A term like (EVar "x") is trivially SN (it doesn't step) but NOT closed. HOWEVER: if reducible(T) implies closed_expr (which it should, since reducible terms must be well-typed closed values), then this follows.

Question: Does your definition of `reducible` include `closed_expr` as a conjunct? If reducible(T)(e) implies closed_expr(e), then this axiom is provable. If not, it needs to be added to the definition of reducible.

### AXIOM 2: lambda_body_SN
```coq
Axiom lambda_body_SN : forall x (T : ty) body v st ctx,
  value v -> SN_expr v ->
  SN (([x := v] body), st, ctx).
```

Analysis: This says substituting an SN value into a body produces an SN term. This is a STANDARD result in strong normalization theory but requires:
1. Substitution preserves reduction sequences (if body reduces, so does [x:=v]body)
2. SN is closed under expansion (if reducing a redex gives an SN term, the original is SN)
3. Key challenge: the body itself might not be SN before substitution (it could have free variable x)

This is provable via the "Girard's candidates" technique but requires substantial infrastructure (compatibility lemmas, backward closure under expansion). It's typically one of the hardest lemmas in SN proofs.

### AXIOM 3: store_values_are_values
```coq
Axiom store_values_are_values : forall loc val st,
  store_lookup loc st = Some val -> value val.
```

Analysis: This says stores only contain values. This is a RUNTIME INVARIANT, not a logical truth. An arbitrary store could contain non-values. This should be:
- Either a PRECONDITION on well-formed stores (store_wf st := forall l v, store_lookup l st = Some v -> value v)
- Or provable from preservation (if the initial store is well-formed and each step maintains well-formedness)

## INSTRUCTIONS

For each axiom, determine:
1. Can it be PROVEN from existing infrastructure? If so, sketch the proof.
2. If NOT, is it a JUSTIFIED axiom (standard result that's too complex to formalize here)?
3. If NOT justified, is it FALSE and needs correction?

Provide your analysis as:
```
=== AXIOM N: [name] ===
STATUS: PROVABLE / JUSTIFIED / FALSE
ANALYSIS: [detailed explanation]
RECOMMENDATION: [what to do]
```
```

---

# ═══════════════════════════════════════════════════════════════
# PROMPT 6: NonInterference_v2.v (1 axiom)
# ═══════════════════════════════════════════════════════════════

```
I need you to analyze 1 axiom in a Coq 8.18 step-indexed logical relations proof. Determine if it can be proven as a lemma or must remain as a justified axiom.

## THE AXIOM

```coq
Axiom fundamental_theorem_step_0 : forall T Σ v1 v2,
  first_order_type T = false ->
  val_rel_n 0 Σ T v1 v2 ->
  (first_order_type T = false -> has_type nil Σ Public v1 T EffectPure) ->
  (first_order_type T = false -> has_type nil Σ Public v2 T EffectPure) ->
  val_rel_at_type Σ (store_rel_n 0) (val_rel_n 0) (store_rel_n 0) T v1 v2.
```

## CONTEXT

This axiom is used in the proof of `combined_step_up_all` (the central step-up lemma for the logical relation). It handles the n=0 case for higher-order types.

### What it says
At step 0, for higher-order types (first_order_type T = false), if v1 and v2 satisfy val_rel_n 0 (which for HO types means: they are values, closed, and well-typed), then they satisfy val_rel_at_type with step-0 predicates.

### Why it's needed
val_rel_n 0 for HO types only gives: value v1, value v2, closed_expr v1, closed_expr v2, has_type nil Σ Public v1 T EffectPure, has_type nil Σ Public v2 T EffectPure.

val_rel_at_type for different types:
- TFn T1 T2 eff: requires showing that applying v1, v2 to step-0-related args produces step-0-related results
- TProd T1 T2 (HO): structural decomposition with step-0-related components
- TSum T1 T2 (HO): similar
- TChan, TSecureChan: val_rel_at_type is True
- TCapability, TCapabilityFull, TProof, TConstantTime, TZeroizing: val_rel_at_type is True

### The TFn case analysis (the hard one)
For TFn T1 T2 eff, val_rel_at_type at step 0 requires:
Given related args x,y (val_rel_n 0 Σ' T1 x y) and related stores (store_rel_n 0 Σ' st1 st2):
Show exists v1' v2' st1' st2' ctx' Σ'' such that:
- (EApp v1 x, st1, ctx) -->* (v1', st1', ctx')
- (EApp v2 y, st2, ctx) -->* (v2', st2', ctx')
- val_rel_n 0 Σ'' T2 v1' v2'
- store_rel_n 0 Σ'' st1' st2'
- store_wf, stores_agree_low_fo postconditions

The problem: val_rel_n 0 for FO result type T2 requires val_rel_at_type_fo T2 v1' v2' (structural equality). But v1 and v2 are DIFFERENT lambdas applied to merely-typed args. They can produce different FO values (e.g., one returns EInt 5, the other EInt 7).

### Available infrastructure
```coq
well_typed_SN : forall Σ e T ε, has_type nil Σ Public e T ε -> closed_expr e -> SN_expr e
progress : well-typed closed terms are values or can step
preservation : stepping preserves typing
canonical_forms_fn : has_type ... v (TFn T1 T2 ε) ... -> value v -> exists x body, v = ELam x T1 body
```

## QUESTION

Can this axiom be eliminated? Specifically:
1. For which types T (where first_order_type T = false) is val_rel_at_type trivially True?
2. For TFn: can val_rel_at_type be proven from typing alone at step 0?
3. If not fully provable, what is the MINIMAL axiom that captures the irreducible gap?

Provide a complete analysis with:
- Which cases are trivially provable (val_rel_at_type = True)
- Which cases require actual proof work
- Whether the TFn case is provable or fundamentally requires an axiom
- If an axiom is needed, the most minimal formulation
```
