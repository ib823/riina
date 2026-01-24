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

### TASK 1: ClosedValueLemmas.v - ALREADY COMPLETED

**Status**: This file has already been created and is in the codebase.

**Location**: `02_FORMAL/coq/properties/ClosedValueLemmas.v`

**IMPORTANT NOTE**:
- The definition uses `closed_expr_cv` (not `closed_expr`) to avoid conflicts with existing definitions
- The `subst_closed_noop` lemma DOES NOT WORK for lambda binders - do NOT attempt to prove it
- The working approach uses simpler decomposition lemmas

**What's already proven**:
```coq
Definition closed_expr_cv (e : expr) : Prop := forall x, ~ free_in x e.

Lemma value_typed_closed : forall Σ Δ v T ε,
  value v -> has_type nil Σ Δ v T ε -> closed_expr_cv v.

Lemma closed_pair_cv : forall e1 e2,
  closed_expr_cv (EPair e1 e2) <-> closed_expr_cv e1 /\ closed_expr_cv e2.

Lemma closed_inl_cv, closed_inr_cv, closed_app_cv : (* similar *)

Lemma closed_unit_cv, closed_bool_cv, closed_int_cv, closed_string_cv, closed_loc_cv : (* base types *)

Lemma closed_lam_body_cv : forall x T body y,
  closed_expr_cv (ELam x T body) -> free_in y body -> y = x.
```

### TASK 2: Create `properties/SubstitutionCommute.v` - COMPLEX

**Status**: This is a complex lemma that requires careful handling.

**CRITICAL INFO - Read the actual definitions**:

```coq
(* In ReducibilityFull.v - subst_rho is a FUNCTION, not a list! *)
Definition subst_rho := ident -> expr.  (* FUNCTION type *)

Definition id_rho : subst_rho := fun x => EVar x.

Definition extend_rho (ρ : subst_rho) (x : ident) (v : expr) : subst_rho :=
  fun y => if String.eqb y x then v else ρ y.

(* Apply substitution to expression *)
Fixpoint subst_env (ρ : subst_rho) (e : expr) : expr :=
  match e with
  | EVar x => ρ x  (* NOT lookup - just apply the function *)
  | ELam x T body => ELam x T (subst_env (extend_rho ρ x (EVar x)) body)
  (* ... *)
  | ERef e sl => ERef (subst_env ρ e) sl  (* NOTE: ERef takes 2 args! *)
  end.
```

**Known Issue**: The `subst_subst_env_commute` lemma is admitted in ReducibilityFull.v because the binder cases (ELam, ECase, ELet, EHandle) require careful reasoning about capture-avoiding substitution. DO NOT attempt unless you have a complete proof.

---

### TASK 3: ValRelMonotone.v - Use Existing Lemmas

**Status**: The monotonicity properties are already partially proven in:
- `CumulativeRelation.v`: defines `val_rel_le`
- `CumulativeMonotone.v`: has `val_rel_le_mono` (1 admit for TFn case)

**CRITICAL**: The lemma name is `val_rel_le_mono`, NOT `cumulative_val_rel_le`.

**Known Issue**: TFn (function types) have a contravariance problem that makes monotonicity require axioms in step-indexed models. The first-order cases work fine.

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

## CRITICAL CODEBASE DETAILS - READ CAREFULLY

**Expression constructors with multiple arguments**:
```coq
| ERef : expr -> security_level -> expr     (* 2 args: expression AND security level *)
| EInl : expr -> ty -> expr                 (* 2 args: expression AND type annotation *)
| EInr : expr -> ty -> expr                 (* 2 args: expression AND type annotation *)
| EClassify : security_level -> expr -> expr (* DIFFERENT ORDER than you might expect *)
```

**Type aliases that exist**:
- `closed_expr` is ALREADY DEFINED in `CumulativeRelation.v` - use `closed_expr_cv` suffix for new definitions
- `subst_rho` is a FUNCTION `ident -> expr`, NOT a list

**Tactics that work**:
- `discriminate` for empty list lookup impossibility (use after `simpl in Hlook`)
- `String.eqb_eq` and `String.eqb_neq` for string equality reasoning
- `destruct (String.eqb x y) eqn:Heq` for case analysis on string comparison

**Tactics that DON'T work as expected**:
- `contradiction` sometimes fails even with apparent contradictions - use explicit `exfalso; apply Hneq; exact Heq` pattern instead

## IMPORTANT NOTES

- The `free_in_context` lemma exists in `Typing.v` - USE IT
- String equality uses `String.eqb` and `String.eqb_eq`/`String.eqb_neq`
- All proofs must be complete - no `admit`, `Admitted`, or `Abort`
- Test compilation before submitting

---

*This prompt is validated against the codebase as of commit e871f7e*
*Claude Code is handling: SN_Closure.v, ReducibilityFull.v, FundamentalTheorem.v*
*You handle: New standalone lemma files*
