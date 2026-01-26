# CLAUDE AI WEB: Fix 2 Admits in ReducibilityFull.v

## CRITICAL INSTRUCTIONS

You are fixing 2 `Admitted` statements in a Coq file for the RIINA programming language's formal verification. Your output MUST be **exact Coq code** that I can paste directly into the file.

**DO NOT:**
- Give explanations without code
- Use placeholder comments like `(* TODO *)`
- Use `admit.` or `Admitted.`
- Assume access to any files not provided here

**DO:**
- Provide COMPLETE, COMPILABLE Coq proofs
- End every proof with `Qed.`
- Use only the definitions provided in this prompt

---

## TASK 1: Prove `subst_subst_env_commute`

### Location
File: `termination/ReducibilityFull.v`, Line 463-469

### Current Code (ADMITTED)
```coq
Lemma subst_subst_env_commute : forall ρ x v e,
  [x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e.
Proof.
Admitted.
```

### Required Definitions

```coq
(* Identifiers are strings *)
Definition ident := string.

(* Substitution environment: total function from identifiers to expressions *)
Definition subst_rho := ident -> expr.

(* Identity substitution *)
Definition id_rho : subst_rho := fun x => EVar x.

(* Environment extension *)
Definition extend_rho (ρ : subst_rho) (x : ident) (v : expr) : subst_rho :=
  fun y => if String.eqb y x then v else ρ y.

(* Single-variable substitution [x := v] e *)
(* This is the standard substitution function from Typing.v *)
(* Notation: [x := v] e means "substitute v for x in e" *)

(* Apply substitution environment to expression *)
Fixpoint subst_env (ρ : subst_rho) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar x => ρ x
  | ELam x T body => ELam x T (subst_env (extend_rho ρ x (EVar x)) body)
  | EApp e1 e2 => EApp (subst_env ρ e1) (subst_env ρ e2)
  | EPair e1 e2 => EPair (subst_env ρ e1) (subst_env ρ e2)
  | EFst e => EFst (subst_env ρ e)
  | ESnd e => ESnd (subst_env ρ e)
  | EInl e T => EInl (subst_env ρ e) T
  | EInr e T => EInr (subst_env ρ e) T
  | ECase e x1 e1 x2 e2 =>
      ECase (subst_env ρ e) x1 (subst_env (extend_rho ρ x1 (EVar x1)) e1)
            x2 (subst_env (extend_rho ρ x2 (EVar x2)) e2)
  | EIf e1 e2 e3 => EIf (subst_env ρ e1) (subst_env ρ e2) (subst_env ρ e3)
  | ELet x e1 e2 => ELet x (subst_env ρ e1) (subst_env (extend_rho ρ x (EVar x)) e2)
  | EPerform eff e => EPerform eff (subst_env ρ e)
  | EHandle e x h => EHandle (subst_env ρ e) x (subst_env (extend_rho ρ x (EVar x)) h)
  | ERef e l => ERef (subst_env ρ e) l
  | EDeref e => EDeref (subst_env ρ e)
  | EAssign e1 e2 => EAssign (subst_env ρ e1) (subst_env ρ e2)
  | EClassify e => EClassify (subst_env ρ e)
  | EDeclassify e p => EDeclassify (subst_env ρ e) (subst_env ρ p)
  | EProve e => EProve (subst_env ρ e)
  | ERequire eff e => ERequire eff (subst_env ρ e)
  | EGrant eff e => EGrant eff (subst_env ρ e)
  end.

(* Closed expression: no free variables *)
Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.

(* Closed environment: all values are closed *)
Definition closed_rho (ρ : subst_rho) : Prop :=
  forall y, closed_expr (ρ y).

(* Already proven helper lemma *)
Lemma subst_not_free_in : forall x v e,
  ~ free_in x e ->
  [x := v] e = e.
```

### Proof Strategy

The lemma states:
```
[x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e
```

**Key insight:** The LHS first applies `extend_rho ρ x (EVar x)` which maps `x` to `EVar x`, then substitutes `v` for `x`. The RHS directly maps `x` to `v`.

**For EVar y:**
- If `y = x`: LHS = `[x := v] (EVar x)` = `v`, RHS = `v` ✓
- If `y ≠ x`: LHS = `[x := v] (ρ y)`, RHS = `ρ y`
  - **Problem:** We need `[x := v] (ρ y) = ρ y`, which requires `~ free_in x (ρ y)`
  - **Solution:** Add hypothesis `closed_rho ρ`

**IMPORTANT:** The lemma as stated is UNPROVABLE without a `closed_rho ρ` hypothesis. You must MODIFY the lemma statement to add this premise.

### YOUR TASK

Provide the FIXED lemma with the `closed_rho ρ` hypothesis and its complete proof:

```coq
Lemma subst_subst_env_commute : forall ρ x v e,
  closed_rho ρ ->  (* ADD THIS HYPOTHESIS *)
  [x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e.
Proof.
  (* YOUR PROOF HERE - must end with Qed. *)
Qed.
```

Also provide a helper lemma if needed:
```coq
Lemma closed_rho_subst : forall ρ x v y,
  closed_rho ρ ->
  x <> y ->
  [x := v] (ρ y) = ρ y.
Proof.
  (* YOUR PROOF HERE *)
Qed.
```

---

## TASK 2: Complete `fundamental_reducibility` (T_App case)

### Location
File: `termination/ReducibilityFull.v`, Line 631

### Current Code (ADMITTED)
```coq
  - (* T_App - use SN_app_family with family premise *)
    intros st ctx.
    apply SN_Closure.SN_app_family.
    + intros st' ctx'. apply IHHty1. assumption.
    + intros st' ctx'. apply IHHty2. assumption.
    + (* family_lambda_SN: for all e1' reachable from (subst_env ρ e1),
         if e1' = ELam x T body, then [x:=v]body is SN for values v *)
      admit.  (* <-- THIS NEEDS TO BE FIXED *)
```

### Required Definition: SN_app_family

```coq
(* From SN_Closure.v *)
Lemma SN_app_family : forall e1 e2 st ctx,
  (forall st' ctx', SN (e1, st', ctx')) ->
  (forall st' ctx', SN (e2, st', ctx')) ->
  (forall x T body v st' ctx',
    multi_step_expr e1 (ELam x T body) ->
    value v ->
    SN (([x := v] body), st', ctx')) ->
  SN (EApp e1 e2, st, ctx).
```

### Proof Strategy

The third premise requires showing:
- For any lambda `ELam x T body` reachable from `subst_env ρ e1`
- For any value `v`
- The substitution `[x := v] body` is SN

**Key insight:**
1. If `e1` has type `T1 -> T2` under `Γ`, and reduces to `ELam x T body`, then `body` has type `T2` under `(x, T1) :: Γ`
2. By preservation (typing preserved under reduction)
3. By IH on the body's typing derivation
4. Extending the environment with `(x, v)` where `v : T1` preserves env_reducible
5. Therefore `[x := v] body` is reducible, hence SN

**The proof requires:**
- A lemma about preservation: if `e --> e'` and `has_type Γ Σ pc e T ε`, then `has_type Γ Σ pc e' T ε`
- Inversion on lambda typing to get body type
- Using `env_reducible_cons` to extend environment

### YOUR TASK

Provide a complete proof for the T_App case. You may need helper lemmas.

The approach should be:
1. Intros for the multi_step and value hypotheses
2. Use preservation to get typing for the lambda
3. Invert the lambda typing to get body typing
4. Use `subst_subst_env_commute` (now proven)
5. Apply the IH with extended environment

**Note:** If this requires significant restructuring, you may instead provide an AXIOM with clear justification:

```coq
(* Justified Axiom: Lambda bodies from well-typed terms are SN under value substitution *)
Axiom lambda_body_SN : forall Γ Σ pc e T1 T2 ε ρ x body v,
  has_type Γ Σ pc e (TFn T1 T2 ε) ε ->
  env_reducible Γ ρ ->
  multi_step_expr (subst_env ρ e) (ELam x T1 body) ->
  value v ->
  Reducible T1 v ->
  SN_expr ([x := v] body).
```

---

## TASK 3: Complete `fundamental_reducibility` (T_Deref case)

### Location
File: `termination/ReducibilityFull.v`, Line 712

### Current Code (ADMITTED)
```coq
  - (* T_Deref - use SN_deref *)
    intros st ctx.
    apply SN_Closure.SN_deref.
    + apply IHHty. assumption.
    + (* Store well-formedness: values in store are values *)
      intros loc val st' Hlook.
      (* This requires a global store well-formedness assumption *)
      admit.  (* <-- THIS NEEDS TO BE FIXED *)
```

### Required Definition: SN_deref

```coq
(* From SN_Closure.v *)
Lemma SN_deref : forall e st ctx,
  SN (e, st, ctx) ->
  (forall loc val st', store_lookup loc st' = Some val -> value val) ->
  SN (EDeref e, st, ctx).
```

### Proof Strategy

The second premise requires showing that all values in the store are actually values. This is a **store well-formedness invariant**.

**Options:**

**Option A:** Add a `store_wf` hypothesis to `fundamental_reducibility`:
```coq
Lemma fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  (forall st, store_wf Σ st -> ...) ->  (* Add this *)
  Reducible T (subst_env ρ e).
```

**Option B:** Use an axiom about store well-formedness:
```coq
Axiom store_invariant : forall loc val st,
  store_lookup loc st = Some val -> value val.
```

**Option C:** The store semantics guarantee this (ST_RefValue and ST_AssignLoc require values):
```coq
(* Proof: By induction on evaluation, stores only contain values *)
```

### YOUR TASK

Provide ONE of:
1. A complete proof using store semantics
2. A modified lemma statement with store_wf hypothesis
3. A justified axiom

---

## OUTPUT FORMAT

Your response must be EXACTLY in this format:

```
=== TASK 1: subst_subst_env_commute ===

(* Helper lemma if needed *)
Lemma closed_rho_subst : forall ρ x v y,
  closed_rho ρ ->
  x <> y ->
  [x := v] (ρ y) = ρ y.
Proof.
  [COMPLETE PROOF]
Qed.

(* Main lemma with closed_rho hypothesis *)
Lemma subst_subst_env_commute : forall ρ x v e,
  closed_rho ρ ->
  [x := v] (subst_env (extend_rho ρ x (EVar x)) e) = subst_env (extend_rho ρ x v) e.
Proof.
  [COMPLETE PROOF]
Qed.

=== TASK 2: T_App case in fundamental_reducibility ===

[Either complete proof OR justified axiom with explanation]

=== TASK 3: T_Deref case in fundamental_reducibility ===

[Either complete proof OR justified axiom with explanation]

=== ADDITIONAL NOTES ===

[Any changes needed to other parts of the file, e.g., updating call sites of subst_subst_env_commute to pass the closed_rho hypothesis]
```

---

## CRITICAL REQUIREMENTS

1. All proofs must end with `Qed.` (not `Admitted.`)
2. All code must be valid Coq 8.18.0 syntax
3. Do not use tactics not available in standard Coq (e.g., no `Program`, no `Equations`)
4. Standard tactics available: `intros`, `destruct`, `induction`, `inversion`, `apply`, `exact`, `rewrite`, `simpl`, `unfold`, `split`, `left`, `right`, `exists`, `auto`, `lia`, `f_equal`, `subst`, `assumption`, `reflexivity`, `symmetry`, `transitivity`, `exfalso`, `contradiction`
5. Use `String.eqb_eq` and `String.eqb_neq` for string equality proofs
6. Use `Nat.eqb_eq` and `Nat.eqb_neq` for nat equality proofs

---

**Mode: ULTRA KIASU | ZERO TRUST | ZERO SHORTCUTS**

Every proof must be complete. No placeholders. No admits.
