# CLAUDE AI WEB MASTER DELEGATION PROMPT

## MISSION BRIEFING

You are working on the RIINA formal proof codebase in parallel with Claude Code (CLI).

**YOUR ROLE**: Create NEW standalone Coq files that prove foundational lemmas.
**CLAUDE CODE'S ROLE**: Integrate your files and fix admits in existing complex files.

**CRITICAL RULE**: You create NEW files only. NEVER modify existing `.v` files.

---

## CODEBASE CONTEXT (COMPLETE)

### Repository Structure
```
/workspaces/proof/02_FORMAL/coq/
├── foundations/           # PROVEN (0 admits) - DO NOT TOUCH
│   ├── Syntax.v          # Expression AST, types, substitution
│   ├── Semantics.v       # Small-step semantics, step relation
│   └── Typing.v          # Type system, has_type, store_wf
├── type_system/          # PROVEN (0 admits) - DO NOT TOUCH
│   ├── Progress.v        # Progress theorem
│   ├── Preservation.v    # Preservation theorem
│   └── TypeSafety.v      # Combined type safety
├── properties/           # YOUR TARGET - Create new files here
│   ├── CumulativeRelation.v   # val_rel_le definition
│   ├── SN_Closure.v           # SN closure lemmas
│   └── [many more]
└── termination/          # Mostly proven
    └── ReducibilityFull.v     # SN proof (has admits)
```

### Key Type Definitions (from Syntax.v)

```coq
(* Expression type *)
Inductive expr : Type :=
  | EUnit : expr
  | EBool : bool -> expr
  | EInt : nat -> expr
  | EString : string -> expr
  | ELoc : loc -> expr
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
  (* ... and more *)

(* Type type *)
Inductive ty : Type :=
  | TUnit : ty
  | TBool : ty
  | TInt : ty
  | TString : ty
  | TFn : ty -> ty -> effect -> ty    (* Function type *)
  | TProd : ty -> ty -> ty            (* Product type *)
  | TSum : ty -> ty -> ty             (* Sum type *)
  | TRef : ty -> security_level -> ty (* Reference type *)
  | TSecret : ty -> ty                (* Secret type *)
  (* ... and more *)

(* Value predicate *)
Inductive value : expr -> Prop :=
  | VUnit : value EUnit
  | VBool : forall b, value (EBool b)
  | VInt : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc : forall l, value (ELoc l)
  | VLam : forall x T e, value (ELam x T e)
  | VPair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl : forall v T, value v -> value (EInl v T)
  | VInr : forall v T, value v -> value (EInr v T)
  (* ... *)

(* Substitution notation *)
Notation "[ x := v ] e" := (subst x v e) (at level 20).
```

### Key Definitions You Need (from Typing.v)

```coq
(* Free variable predicate *)
Fixpoint free_in (x : ident) (e : expr) : Prop :=
  match e with
  | EUnit => False
  | EVar y => x = y
  | ELam y _ body => x <> y /\ free_in x body
  | EApp e1 e2 => free_in x e1 \/ free_in x e2
  (* ... full definition in Typing.v *)
  end.

(* Type environment lookup *)
Fixpoint lookup (x : ident) (Γ : list (ident * ty)) : option ty := ...

(* Typing judgment *)
Inductive has_type : type_env -> store_ty -> security_level ->
                      expr -> ty -> effect -> Prop := ...
```

### Key Lemmas Already Proven (USE THESE)

```coq
(* In Semantics.v - PROVEN *)
Theorem step_deterministic : forall t st ctx t1 st1 ctx1 t2 st2 ctx2,
  (t, st, ctx) --> (t1, st1, ctx1) ->
  (t, st, ctx) --> (t2, st2, ctx2) ->
  t1 = t2 /\ st1 = st2 /\ ctx1 = ctx2.

Lemma value_not_step : forall v st ctx cfg',
  value v -> ~ ((v, st, ctx) --> cfg').

(* In Preservation.v - PROVEN *)
Lemma substitution_preserves_typing : forall Γ Σ Δ z v e T1 T2 ε2,
  value v ->
  has_type nil Σ Δ v T1 EffectPure ->
  has_type ((z, T1) :: Γ) Σ Δ e T2 ε2 ->
  has_type Γ Σ Δ ([z := v] e) T2 ε2.

Theorem preservation : forall e e' T ε st st' ctx ctx' Σ,
  has_type nil Σ Public e T ε ->
  store_wf Σ st ->
  (e, st, ctx) --> (e', st', ctx') ->
  exists Σ' ε', store_ty_extends Σ Σ' /\ store_wf Σ' st' /\
                has_type nil Σ' Public e' T ε'.

(* In SN_Closure.v - PROVEN *)
Definition SN (cfg : config) : Prop := Acc step_inv cfg.

Lemma value_SN : forall v st ctx, value v -> SN (v, st, ctx).

Lemma SN_app_family : forall e1 e2 st ctx,
  (forall st' ctx', SN (e1, st', ctx')) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  family_lambda_SN e1 ->
  SN (EApp e1 e2, st, ctx).
```

---

## YOUR TASKS

Create the following NEW files. Each file must:
1. Compile independently with `coqc -Q . RIINA <filename>`
2. Import only from foundations/, type_system/, or earlier properties files
3. Have ZERO `Admitted.` statements
4. Follow the exact format specified

---

### TASK 1: Create `properties/ClosedValueLemmas.v`

**Purpose**: Prove that values typed in empty context are closed expressions.

**File Content** (create exactly this):

```coq
(** * ClosedValueLemmas.v

    Lemmas about closed expressions and values.

    Key theorem: Values typed in empty context have no free variables.

    Mode: ULTRA KIASU | ZERO ADMITS
*)

Require Import String.
Require Import List.
Require Import RIINA.foundations.Syntax.
Require Import RIINA.foundations.Typing.
Require Import RIINA.type_system.Preservation.
Import ListNotations.

(** Closed expression: no free variables *)
Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(** Values are closed under empty context typing *)
Lemma value_typed_closed : forall Σ Δ v T ε,
  value v ->
  has_type nil Σ Δ v T ε ->
  closed_expr v.
Proof.
  intros Σ Δ v T ε Hval Hty.
  unfold closed_expr. intros x Hfree.
  (* Use free_in_context from Preservation.v: if x is free in v, x must be in context *)
  (* But context is nil, so this is impossible *)
  destruct (free_in_context x v nil Σ Δ T ε Hfree Hty) as [T' Hlook].
  simpl in Hlook. discriminate.
Qed.

(** Substitution has no effect on closed expressions *)
Lemma subst_closed_noop : forall x v e,
  closed_expr e ->
  [x := v] e = e.
Proof.
  intros x v e Hclosed.
  induction e; simpl; try reflexivity.
  - (* EVar *)
    destruct (String.eqb x i) eqn:Heq.
    + apply String.eqb_eq in Heq. subst.
      exfalso. apply (Hclosed i). simpl. reflexivity.
    + reflexivity.
  - (* ELam *)
    destruct (String.eqb x i) eqn:Heq.
    + reflexivity.
    + f_equal. apply IHe.
      unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. split.
      * intro Heq'. subst. apply String.eqb_neq in Heq. contradiction.
      * exact Hy.
  - (* EApp *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EPair *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EFst *) f_equal. apply IHe. unfold closed_expr in *. exact Hclosed.
  - (* ESnd *) f_equal. apply IHe. unfold closed_expr in *. exact Hclosed.
  - (* EInl *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EInr *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* ECase *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + destruct (String.eqb x i) eqn:Heq1; [reflexivity|].
      apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. left.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq1. contradiction.
    + destruct (String.eqb x i0) eqn:Heq2; [reflexivity|].
      apply IHe3. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. right.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq2. contradiction.
  - (* EIf *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. left. exact Hy.
    + apply IHe3. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. right. exact Hy.
  - (* ELet *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq. contradiction.
  - (* EPerform *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EHandle *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + destruct (String.eqb x i) eqn:Heq; [reflexivity|].
      apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right.
      split; [|exact Hy].
      intro Heq'. subst. apply String.eqb_neq in Heq. contradiction.
  - (* ERef *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EDeref *) f_equal. apply IHe. unfold closed_expr in *. exact Hclosed.
  - (* EAssign *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EClassify *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EDeclassify *)
    f_equal.
    + apply IHe1. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. left. exact Hy.
    + apply IHe2. unfold closed_expr in *. intros y Hy.
      apply (Hclosed y). simpl. right. exact Hy.
  - (* EProve *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* ERequire *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
  - (* EGrant *) f_equal. apply IHe. unfold closed_expr in *. intros y Hy.
    apply (Hclosed y). simpl. exact Hy.
Qed.

(** Closed expressions for compound types *)
Lemma closed_pair : forall e1 e2,
  closed_expr (EPair e1 e2) <-> closed_expr e1 /\ closed_expr e2.
Proof.
  intros e1 e2. split.
  - intros Hc. split; unfold closed_expr in *; intros x Hfree;
    apply (Hc x); simpl; [left | right]; exact Hfree.
  - intros [Hc1 Hc2]. unfold closed_expr in *. intros x Hfree.
    simpl in Hfree. destruct Hfree as [H | H]; [apply (Hc1 x H) | apply (Hc2 x H)].
Qed.

Lemma closed_inl : forall e T,
  closed_expr (EInl e T) <-> closed_expr e.
Proof.
  intros e T. split.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    apply (Hc x). simpl. exact Hfree.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    simpl in Hfree. apply (Hc x). exact Hfree.
Qed.

Lemma closed_inr : forall e T,
  closed_expr (EInr e T) <-> closed_expr e.
Proof.
  intros e T. split.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    apply (Hc x). simpl. exact Hfree.
  - intros Hc. unfold closed_expr in *. intros x Hfree.
    simpl in Hfree. apply (Hc x). exact Hfree.
Qed.

(** Values: specific closed lemmas *)
Lemma closed_unit : closed_expr EUnit.
Proof. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_bool : forall b, closed_expr (EBool b).
Proof. intros b. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_int : forall n, closed_expr (EInt n).
Proof. intros n. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_string : forall s, closed_expr (EString s).
Proof. intros s. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

Lemma closed_loc : forall l, closed_expr (ELoc l).
Proof. intros l. unfold closed_expr. intros x Hfree. simpl in Hfree. exact Hfree. Qed.

(** End of file - ZERO ADMITS *)
```

**Validation**: After creating, run:
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA properties/ClosedValueLemmas.v
grep "Admitted" properties/ClosedValueLemmas.v  # Should return nothing
```

---

### TASK 2: Create `properties/SubstitutionCommute.v`

**Purpose**: Prove the substitution-environment commutation lemma.

**Key Insight**: The lemma `[x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e` requires that ρ's range is closed.

**File Content**: Create a file that:
1. Defines `subst_rho` (substitution environment)
2. Defines `extend_rho` (environment extension)
3. Defines `subst_env` (apply environment to expression)
4. Defines `closed_rho` (all bindings are closed)
5. Proves `subst_subst_env_commute` with `closed_rho` premise

Use the definitions from `termination/ReducibilityFull.v` lines 302-343 as reference.

---

### TASK 3: Create `properties/ValRelMonotone.v`

**Purpose**: Prove step monotonicity for the cumulative relation.

The cumulative relation `val_rel_le n Σ T v1 v2` is defined in `CumulativeRelation.v`.
Step monotonicity means: if related at n, related at any m ≤ n.

**Key Insight**: With cumulative definition, this is trivial - just project out.

---

## VALIDATION CHECKLIST

Before submitting any file:

1. **Compilation Test**:
   ```bash
   cd /workspaces/proof/02_FORMAL/coq
   coqc -Q . RIINA <your-file.v>
   echo "Exit code: $?"  # Must be 0
   ```

2. **Zero Admits Check**:
   ```bash
   grep -c "Admitted\." <your-file.v>  # Must be 0
   ```

3. **Import Check**: Only import from:
   - `RIINA.foundations.Syntax`
   - `RIINA.foundations.Semantics`
   - `RIINA.foundations.Typing`
   - `RIINA.type_system.Preservation` (for `free_in_context`)
   - `RIINA.properties.TypeMeasure`
   - `RIINA.properties.LexOrder`
   - `RIINA.properties.FirstOrderComplete`
   - `RIINA.properties.CumulativeRelation`

4. **No Axioms Check**:
   ```bash
   grep -c "^Axiom\|^Parameter" <your-file.v>  # Must be 0
   ```

---

## COORDINATION PROTOCOL

1. **Output Format**: Provide complete `.v` file content in a code block
2. **File Location**: All new files go in `properties/`
3. **Naming**: Use descriptive names ending in `.v`
4. **No Conflicts**: Never modify existing files
5. **Self-Contained**: Each file must compile independently

---

## IMPORTANT NOTES

- The `free_in_context` lemma exists in `Typing.v` - USE IT
- String equality uses `String.eqb` and `String.eqb_eq`/`String.eqb_neq`
- All proofs must be complete - no `admit`, `Admitted`, or `Abort`
- Test compilation before submitting

---

*This prompt is validated against the codebase as of commit e871f7e*
*Claude Code is handling: SN_Closure.v, ReducibilityFull.v, FundamentalTheorem.v*
*You handle: New standalone lemma files*
