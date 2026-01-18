# Claude.ai Research Task - Phase 5C: step_preserves_closed Complete Proof

## Context

We need to prove that single-step reduction preserves closed expressions in MasterTheorem.v (line 426-436).

## The Lemma

```coq
Lemma step_preserves_closed : forall e1 st1 ctx e2 st2 ctx',
  closed_expr e1 ->
  (e1, st1, ctx) --> (e2, st2, ctx') ->
  closed_expr e2.
```

## Available Infrastructure (ALREADY PROVEN)

```coq
(* Substitution preserves closed *)
Lemma subst_closed : forall x v e,
  closed_expr v ->
  (forall y, free_in y e -> y = x) ->
  closed_expr ([x := v] e).

(* Free variables in substituted expressions *)
Lemma free_in_subst_closed : forall y x v e,
  closed_expr v ->
  free_in y ([x := v] e) ->
  free_in y e /\ y <> x.

(* Lambda body has at most bound var free *)
Lemma closed_lam_body : forall x T body y,
  closed_expr (ELam x T body) ->
  free_in y body ->
  y = x.

(* Component extraction lemmas *)
Lemma closed_pair_components : forall a b, closed_expr (EPair a b) -> closed_expr a /\ closed_expr b.
Lemma closed_app_left : forall e1 e2, closed_expr (EApp e1 e2) -> closed_expr e1.
Lemma closed_app_right : forall e1 e2, closed_expr (EApp e1 e2) -> closed_expr e2.
Lemma closed_fst : forall e, closed_expr (EFst e) -> closed_expr e.
Lemma closed_snd : forall e, closed_expr (ESnd e) -> closed_expr e.
Lemma closed_inl_component : forall e T, closed_expr (EInl e T) -> closed_expr e.
Lemma closed_inr_component : forall e T, closed_expr (EInr e T) -> closed_expr e.
Lemma closed_deref : forall e, closed_expr (EDeref e) -> closed_expr e.
Lemma closed_if : forall e1 e2 e3, closed_expr (EIf e1 e2 e3) -> closed_expr e1 /\ closed_expr e2 /\ closed_expr e3.
Lemma closed_let : forall x e1 e2, closed_expr (ELet x e1 e2) -> closed_expr e1.
Lemma closed_let_body : forall x e1 e2 y, closed_expr (ELet x e1 e2) -> free_in y e2 -> y = x.
Lemma closed_case : forall e x1 e1 x2 e2, closed_expr (ECase e x1 e1 x2 e2) -> closed_expr e.
Lemma closed_case_left : forall e x1 e1 x2 e2 y, closed_expr (ECase e x1 e1 x2 e2) -> free_in y e1 -> y = x1.
Lemma closed_case_right : forall e x1 e1 x2 e2 y, closed_expr (ECase e x1 e1 x2 e2) -> free_in y e2 -> y = x2.
Lemma closed_handle : forall e x h, closed_expr (EHandle e x h) -> closed_expr e.
Lemma closed_handle_body : forall e x h y, closed_expr (EHandle e x h) -> free_in y h -> y = x.
```

## Step Relation (from Semantics.v)

The step relation `(e1, st1, ctx) --> (e2, st2, ctx')` includes these rules:

### Computation Rules (need substitution lemmas)
```
ST_Beta: (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
ST_LetEval: (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)
ST_CaseInl: (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
ST_CaseInr: (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
ST_HandleReturn: (EHandle v x h, st, ctx) --> (v, st, ctx)
```

### Projection Rules (extract components)
```
ST_FstPair: (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
ST_SndPair: (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
```

### Conditional Rules
```
ST_IfTrue: (EIf (EBool true) e1 e2, st, ctx) --> (e1, st, ctx)
ST_IfFalse: (EIf (EBool false) e1 e2, st, ctx) --> (e2, st, ctx)
```

### Store Rules (need store invariant)
```
ST_RefLoc: (ERef v, st, ctx) --> (ELoc l, st', ctx)  where l is fresh
ST_DerefLoc: (EDeref (ELoc l), st, ctx) --> (v, st, ctx) where v = st[l]
ST_AssignLoc: (EAssign (ELoc l) v, st, ctx) --> (EUnit, st[l:=v], ctx)
```

### Congruence Rules (use IH on subterm)
```
ST_App1: (EApp e1 e2, st, ctx) --> (EApp e1' e2, st', ctx') when (e1, st, ctx) --> (e1', st', ctx')
ST_App2: (EApp v e2, st, ctx) --> (EApp v e2', st', ctx') when (e2, st, ctx) --> (e2', st', ctx')
... (many more)
```

## Your Task

Provide a COMPLETE Coq proof for step_preserves_closed, handling EVERY case of the step relation.

### Structure Requirements

1. **Induction on Hstep**: `induction Hstep; intros.`
2. **Each case**: Use appropriate lemma from infrastructure
3. **Substitution cases**: Use `subst_closed` with `closed_lam_body` etc.
4. **Congruence cases**: Extract closed subterm, apply IH, rebuild
5. **Store cases**: May need assumption about store (see below)

### Store Typing Invariant

For ST_DerefLoc, we need: if `lookup st l = Some v`, then `closed_expr v`.

This requires a **store typing invariant** that well-typed stores contain only closed values. You may:
- Add this as an explicit hypothesis, OR
- Use `admit` for ONLY the ST_DerefLoc case with clear documentation

### Expected Output Format

```coq
Lemma step_preserves_closed : forall e1 st1 ctx e2 st2 ctx',
  closed_expr e1 ->
  (e1, st1, ctx) --> (e2, st2, ctx') ->
  closed_expr e2.
Proof.
  intros e1 st1 ctx e2 st2 ctx' Hc Hstep.
  induction Hstep; intros.
  - (* ST_Beta *)
    apply subst_closed.
    + (* closed_expr v *) apply closed_app_right with (ELam x T body). exact Hc.
    + (* forall y, free_in y body -> y = x *)
      intros y Hy. apply closed_lam_body with T body.
      * apply closed_app_left with v. exact Hc.
      * exact Hy.
  - (* ST_App1 - congruence *)
    ...
  (* ... all other cases ... *)
Qed.
```

## Constraints

1. **COMPLETE**: Every constructor of the step relation must have a case
2. **NO AXIOMS**: Except possibly one `admit` for ST_DerefLoc with documentation
3. **EXPLICIT**: Don't use `auto` without showing it works; prefer explicit tactics
4. **MODULAR**: Use `assert` for sub-goals to keep proof readable

## Rules to Apply

1. **Revolutionary Solution**: The proof must handle all reduction rules systematically and completely.

2. **Zero Vulnerabilities**: Every case must be proven. No missing branches.

3. **Ultra Paranoid Verification**: Each tactic must be justified by an available lemma.

4. **No Shortcuts**: All ~25+ cases must be explicitly written out.

5. **Foundational Correctness**: Based on the actual step relation definition.

## Step Relation Constructors (for Reference)

You'll need to check Semantics.v for the exact constructor names, but typical ones include:
- ST_Beta, ST_App1, ST_App2
- ST_LetEval, ST_Let1
- ST_FstPair, ST_SndPair, ST_Fst, ST_Snd
- ST_CaseInl, ST_CaseInr, ST_Case
- ST_IfTrue, ST_IfFalse, ST_If
- ST_Pair1, ST_Pair2
- ST_Inl, ST_Inr
- ST_RefLoc, ST_Ref, ST_DerefLoc, ST_Deref, ST_AssignLoc, ST_Assign1, ST_Assign2
- ... (security types: ST_Classify, ST_Declassify, etc.)

Deliverable: Complete Coq proof handling all cases.
