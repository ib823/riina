# PROMPT: Fix 3 Axioms in ReducibilityFull.v

You are working on a Coq 8.18+ (also compiles with Rocq 9.1) formal verification codebase called RIINA. You must fix the 3 `Axiom` statements in `termination/ReducibilityFull.v` by converting them to `Lemma` with complete proofs, OR document why they must remain as justified axioms.

**CRITICAL RULES:**
- Output ONLY the replacement for each axiom
- Convert `Axiom` to `Lemma` + proof + `Qed.` if possible
- If NOT provable without additional infrastructure, keep as `Axiom` but add `(* JUSTIFIED AXIOM: ... *)` documentation
- Do NOT change any existing `Qed.` proofs
- Do NOT add new axioms beyond the 3 being addressed
- Use ONLY the available infrastructure listed below

---

## THE 3 AXIOMS

### Axiom 1 (line 907): env_reducible_closed

```coq
Axiom env_reducible_closed : forall Γ ρ,
  env_reducible Γ ρ -> closed_rho ρ.
```

**What it says**: If ρ maps all variables in Γ to reducible values, then ρ maps ALL variables to closed expressions.

**Problem**: `env_reducible Γ ρ` only constrains `ρ x` for `x ∈ dom(Γ)`. For variables NOT in Γ, `ρ x` is unconstrained. So `closed_rho ρ` (which requires `closed_expr (ρ y)` for ALL y) is NOT provable from `env_reducible` alone.

**Possible fix**: Either:
(a) Strengthen the hypothesis: require `ρ` to be `id_rho` outside `dom(Γ)`, or
(b) Weaken the conclusion: only claim closedness for `x ∈ dom(Γ)`, or
(c) Document as justified axiom: in practice, `ρ` is always constructed from `id_rho` with extensions, so `ρ y = EVar y` for `y ∉ dom(Γ)`, and variables are trivially closed (they have no subterms with free variables... wait, `EVar y` has `y` free, so it's NOT closed).

**CONCLUSION**: This axiom is NOT provable as stated. `closed_rho ρ` requires `forall y, closed_expr (ρ y)`, but for `y ∉ dom(Γ)`, `ρ y` could be `EVar y` which is NOT closed. Keep as justified axiom with documentation.

### Axiom 2 (line 928): lambda_body_SN

```coq
Axiom lambda_body_SN : forall x (T : ty) body v st ctx,
  value v -> SN_expr v ->
  SN (([x := v] body), st, ctx).
```

**What it says**: Substituting any SN value into any lambda body produces SN.

**Problem**: This is TOO STRONG as stated. `body` is completely unconstrained — it could be any expression, not necessarily well-typed. Substituting a value into an arbitrary expression does not guarantee termination.

**The standard version** would require `body` to come from a well-typed lambda, i.e., `has_type ((x,T)::Γ) Σ Δ body T2 ε` for some typing context. Without that, this is unprovable.

**CONCLUSION**: Keep as justified axiom. The callers always use it with well-typed bodies from the fundamental theorem, but the lemma statement is missing the typing premise.

### Axiom 3 (line 942): store_values_are_values

```coq
Axiom store_values_are_values : forall loc val st,
  store_lookup loc st = Some val -> value val.
```

**What it says**: Everything in the store is a value.

**Problem**: This is a global invariant about stores. It's true for stores reachable from well-formed initial states (since `ST_RefValue` and `ST_AssignLoc` only store values), but it's not true for arbitrary `store` values. The type `store = list (nat * expr)` allows non-values.

**Possible fix**:
(a) Add a `store_wf` predicate and require it as a premise
(b) Keep as axiom with justification that all reachable stores satisfy this

**CONCLUSION**: This could be converted to a lemma with a `store_wf` premise, but that would require changing all callers. Keep as justified axiom.

---

## AVAILABLE DEFINITIONS (from ReducibilityFull.v)

```coq
(* Strong normalization *)
Definition config := (expr * store * effect_ctx)%type.
Definition step_inv (cfg1 cfg2 : config) : Prop :=
  let '(e2, st2, ctx2) := cfg2 in
  let '(e1, st1, ctx1) := cfg1 in
  (e2, st2, ctx2) --> (e1, st1, ctx1).
Definition SN (cfg : config) : Prop := Acc step_inv cfg.
Definition SN_expr (e : expr) : Prop := forall st ctx, SN (e, st, ctx).

(* Reducibility — simplified to just SN *)
Definition Reducible (T : ty) (e : expr) : Prop := SN_expr e.

(* Substitution environment *)
Definition subst_rho := ident -> expr.
Definition id_rho : subst_rho := fun x => EVar x.
Definition extend_rho (ρ : subst_rho) (x : ident) (v : expr) : subst_rho :=
  fun y => if String.eqb y x then v else ρ y.

(* Closedness *)
Definition closed_rho (ρ : subst_rho) : Prop := forall y, closed_expr (ρ y).
Definition closed_expr (e : expr) : Prop := forall x, ~ free_in x e.

(* Environment reducibility *)
Definition env_reducible (Γ : list (ident * ty)) (ρ : subst_rho) : Prop :=
  forall x T, lookup x Γ = Some T -> value (ρ x) /\ Reducible T (ρ x).

(* Store *)
Definition store := list (nat * expr).
(* store_lookup and store_update are standard list operations *)
```

### From Semantics.v — Relevant step rules

```coq
| ST_RefValue : forall v sl st ctx l,
    value v ->
    l = fresh_loc st ->
    (ERef v sl, st, ctx) --> (ELoc l, store_update l v st, ctx)
| ST_AssignLoc : forall v1 l st ctx,
    store_lookup l st = Some v1 ->
    forall v2, value v2 ->
    (EAssign (ELoc l) v2, st, ctx) --> (EUnit, store_update l v2 st, ctx)
```

### From Semantics.v — Values

```coq
Inductive value : expr -> Prop :=
  | VUnit   : value EUnit
  | VBool   : forall b, value (EBool b)
  | VInt    : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc    : forall l, value (ELoc l)
  | VLam    : forall x T e, value (ELam x T e)
  | VPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl    : forall v T, value v -> value (EInl v T)
  | VInr    : forall v T, value v -> value (EInr v T)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve  : forall v, value v -> value (EProve v).
```

### From Syntax.v — free_in

```coq
Inductive free_in : ident -> expr -> Prop :=
  | FI_Var : forall x, free_in x (EVar x)
  | FI_Lam : forall x y T e, x <> y -> free_in x e -> free_in x (ELam y T e)
  | FI_App1 : forall x e1 e2, free_in x e1 -> free_in x (EApp e1 e2)
  | FI_App2 : forall x e1 e2, free_in x e2 -> free_in x (EApp e1 e2)
  | FI_Pair1 : forall x e1 e2, free_in x e1 -> free_in x (EPair e1 e2)
  | FI_Pair2 : forall x e1 e2, free_in x e2 -> free_in x (EPair e1 e2)
  (* ... similar constructors for all other expression forms ... *)
  .
```

### From ReducibilityFull.v — Proven lemmas available

```coq
Lemma value_SN : forall v, value v -> SN_expr v.
Lemma SN_step : forall e st ctx e' st' ctx',
  SN (e, st, ctx) -> (e, st, ctx) --> (e', st', ctx') -> SN (e', st', ctx').
Lemma subst_not_free_in : forall x v e, ~ free_in x e -> [x := v] e = e.
```

---

## OUTPUT FORMAT

For each axiom, provide:
1. If provable: `Lemma name : ... Proof. ... Qed.`
2. If not provable: Keep `Axiom name : ...` with `(* JUSTIFIED AXIOM: [detailed explanation of why it cannot be proven and why it is semantically valid] *)`

Provide the replacement for all 3 axiom blocks.
