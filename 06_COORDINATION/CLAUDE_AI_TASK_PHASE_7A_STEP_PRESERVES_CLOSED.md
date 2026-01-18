# Claude.ai Research Task - Phase 7A: step_preserves_closed Complete Proof

## CRITICAL CONTEXT

This is a BLOCKING infrastructure lemma for the RIINA master_theorem. The proof structure is clear but requires handling ~30 step relation constructors.

## The Problem

```coq
Lemma step_preserves_closed : forall e1 st1 ctx e2 st2 ctx',
  closed_expr e1 ->
  (e1, st1, ctx) --> (e2, st2, ctx') ->
  closed_expr e2.
```

**Definition of closed_expr (CRITICAL - proposition-based, NOT list-based):**
```coq
Definition closed_expr (e : expr) : Prop :=
  forall x, ~ free_in x e.
```

## Step Relation Constructors (ALL 30+)

### Computation Rules (use substitution lemmas)
```
ST_AppAbs:     (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx)
ST_LetValue:   (ELet x v e2, st, ctx) --> ([x := v] e2, st, ctx)
ST_CaseInl:    (ECase (EInl v T) x1 e1 x2 e2, st, ctx) --> ([x1 := v] e1, st, ctx)
ST_CaseInr:    (ECase (EInr v T) x1 e1 x2 e2, st, ctx) --> ([x2 := v] e2, st, ctx)
ST_HandleValue: (EHandle v x h, st, ctx) --> (v, st, ctx)
```

### Extraction Rules (extract closed subterm)
```
ST_Fst:        (EFst (EPair v1 v2), st, ctx) --> (v1, st, ctx)
ST_Snd:        (ESnd (EPair v1 v2), st, ctx) --> (v2, st, ctx)
ST_IfTrue:     (EIf (EBool true) e2 e3, st, ctx) --> (e2, st, ctx)
ST_IfFalse:    (EIf (EBool false) e2 e3, st, ctx) --> (e3, st, ctx)
ST_PerformValue: (EPerform eff v, st, ctx) --> result (effect handling)
ST_DeclassifyValue: (EDeclassify v p, st, ctx) --> (v, st, ctx)
```

### Store Rules (special handling)
```
ST_RefValue:   (ERef v sl, st, ctx) --> (ELoc l, st', ctx)  -- result is ELoc (always closed)
ST_DerefLoc:   (EDeref (ELoc l), st, ctx) --> (v, st, ctx)  -- NEEDS STORE INVARIANT
ST_AssignLoc:  (EAssign (ELoc l) v, st, ctx) --> (EUnit, st', ctx)  -- result is EUnit (closed)
```

### Congruence Rules (use IH + reconstruction)
```
ST_App1, ST_App2:       Application congruence
ST_Pair1, ST_Pair2:     Pair construction
ST_FstStep, ST_SndStep: Projection congruence
ST_CaseStep:            Case scrutinee
ST_InlStep, ST_InrStep: Sum injection
ST_IfStep:              Conditional
ST_LetStep:             Let binding
ST_PerformStep:         Effect perform
ST_HandleStep:          Effect handle
ST_RefStep:             Reference creation
ST_DerefStep:           Dereference
ST_Assign1, ST_Assign2: Assignment
ST_ClassifyStep:        Classification
ST_Declassify1, ST_Declassify2: Declassification
ST_ProveStep:           Proof construction
ST_RequireStep, ST_RequireValue: Capability require
ST_GrantStep, ST_GrantValue: Capability grant
```

## Available Infrastructure (ALREADY PROVEN in MasterTheorem.v)

### Substitution Lemmas
```coq
Lemma subst_closed : forall x v e,
  closed_expr v ->
  (forall y, free_in y e -> y = x) ->
  closed_expr ([x := v] e).

Lemma free_in_subst_closed : forall y x v e,
  closed_expr v ->
  free_in y ([x := v] e) ->
  free_in y e /\ y <> x.
```

### Body Extraction Lemmas
```coq
Lemma closed_lam_body : forall x T body y,
  closed_expr (ELam x T body) -> free_in y body -> y = x.

Lemma closed_let_body : forall x e1 e2 y,
  closed_expr (ELet x e1 e2) -> free_in y e2 -> y = x.

Lemma closed_case_left : forall e x1 e1 x2 e2 y,
  closed_expr (ECase e x1 e1 x2 e2) -> free_in y e1 -> y = x1.

Lemma closed_case_right : forall e x1 e1 x2 e2 y,
  closed_expr (ECase e x1 e1 x2 e2) -> free_in y e2 -> y = x2.

Lemma closed_handle_body : forall e x h y,
  closed_expr (EHandle e x h) -> free_in y h -> y = x.
```

### Component Extraction Lemmas
```coq
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
Lemma closed_case : forall e x1 e1 x2 e2, closed_expr (ECase e x1 e1 x2 e2) -> closed_expr e.
Lemma closed_handle : forall e x h, closed_expr (EHandle e x h) -> closed_expr e.
Lemma closed_perform_inv : forall eff e, closed_expr (EPerform eff e) -> closed_expr e.
Lemma closed_assign_left : forall e1 e2, closed_expr (EAssign e1 e2) -> closed_expr e1.
Lemma closed_assign_right : forall e1 e2, closed_expr (EAssign e1 e2) -> closed_expr e2.
```

### Construction Lemmas
```coq
Lemma closed_app : forall e1 e2, closed_expr e1 -> closed_expr e2 -> closed_expr (EApp e1 e2).
Lemma closed_pair : forall a b, closed_expr a -> closed_expr b -> closed_expr (EPair a b).
Lemma closed_inl : forall e T, closed_expr e -> closed_expr (EInl e T).
Lemma closed_inr : forall e T, closed_expr e -> closed_expr (EInr e T).
Lemma closed_fst_construct : forall e, closed_expr e -> closed_expr (EFst e).
Lemma closed_snd_construct : forall e, closed_expr e -> closed_expr (ESnd e).
Lemma closed_if_construct : forall e1 e2 e3, closed_expr e1 -> closed_expr e2 -> closed_expr e3 -> closed_expr (EIf e1 e2 e3).
Lemma closed_ref : forall e sl, closed_expr e -> closed_expr (ERef e sl).
Lemma closed_deref_construct : forall e, closed_expr e -> closed_expr (EDeref e).
Lemma closed_assign : forall e1 e2, closed_expr e1 -> closed_expr e2 -> closed_expr (EAssign e1 e2).
Lemma closed_perform : forall eff e, closed_expr e -> closed_expr (EPerform eff e).
Lemma closed_loc : forall l, closed_expr (ELoc l).
Lemma closed_unit : closed_expr EUnit.
```

## Your Task

Provide a COMPLETE Coq proof for step_preserves_closed handling ALL ~30 constructors.

### Proof Structure

```coq
Lemma step_preserves_closed : forall e1 st1 ctx e2 st2 ctx',
  closed_expr e1 ->
  (e1, st1, ctx) --> (e2, st2, ctx') ->
  closed_expr e2.
Proof.
  intros e1 st1 ctx e2 st2 ctx' Hc Hstep.
  induction Hstep.

  - (* ST_AppAbs: (EApp (ELam x T body) v, st, ctx) --> ([x := v] body, st, ctx) *)
    apply subst_closed.
    + (* closed_expr v *)
      apply closed_app_right with (ELam x T body). exact Hc.
    + (* forall y, free_in y body -> y = x *)
      intros y Hy. apply closed_lam_body with T body.
      * apply closed_app_left with v. exact Hc.
      * exact Hy.

  - (* ST_App1: congruence *)
    apply closed_app.
    + apply IHHstep. apply closed_app_left with e2. exact Hc.
    + apply closed_app_right with e1. exact Hc.

  - (* ST_App2: congruence *)
    apply closed_app.
    + apply closed_app_left with e2. exact Hc.
    + apply IHHstep. apply closed_app_right with v1. exact Hc.

  (* ... continue for ALL other constructors ... *)
Qed.
```

### ST_DerefLoc Special Case

For ST_DerefLoc, the result `v` comes from the store. We need to assume stores contain only closed values:

```coq
(* Either add as hypothesis or use admit with documentation *)
- (* ST_DerefLoc *)
  (* Store invariant: well-typed stores contain only closed values *)
  (* This is established by the store typing relation *)
  admit. (* Requires: store_contains_closed st l v *)
```

## Constraints

1. **COMPLETE**: Handle ALL step constructors explicitly
2. **USE AVAILABLE LEMMAS**: Don't reprove what's already proven
3. **EXPLICIT TACTICS**: Show each step clearly
4. **ONE ADMIT ALLOWED**: Only for ST_DerefLoc (store invariant)

## Expected Output Format

Provide the complete proof with each case explicitly handled:

```coq
Lemma step_preserves_closed : forall e1 st1 ctx e2 st2 ctx',
  closed_expr e1 ->
  (e1, st1, ctx) --> (e2, st2, ctx') ->
  closed_expr e2.
Proof.
  intros e1 st1 ctx e2 st2 ctx' Hc Hstep.
  induction Hstep.
  - (* ST_AppAbs *) [exact tactics]
  - (* ST_App1 *) [exact tactics]
  - (* ST_App2 *) [exact tactics]
  - (* ST_Pair1 *) [exact tactics]
  - (* ST_Pair2 *) [exact tactics]
  - (* ST_Fst *) [exact tactics]
  - (* ST_Snd *) [exact tactics]
  - (* ST_FstStep *) [exact tactics]
  - (* ST_SndStep *) [exact tactics]
  - (* ST_CaseInl *) [exact tactics]
  - (* ST_CaseInr *) [exact tactics]
  - (* ST_CaseStep *) [exact tactics]
  - (* ST_InlStep *) [exact tactics]
  - (* ST_InrStep *) [exact tactics]
  - (* ST_IfTrue *) [exact tactics]
  - (* ST_IfFalse *) [exact tactics]
  - (* ST_IfStep *) [exact tactics]
  - (* ST_LetValue *) [exact tactics]
  - (* ST_LetStep *) [exact tactics]
  - (* ST_PerformStep *) [exact tactics]
  - (* ST_PerformValue *) [exact tactics]
  - (* ST_HandleStep *) [exact tactics]
  - (* ST_HandleValue *) [exact tactics]
  - (* ST_RefStep *) [exact tactics]
  - (* ST_RefValue *) [exact tactics]
  - (* ST_DerefStep *) [exact tactics]
  - (* ST_DerefLoc *) admit. (* Store invariant *)
  - (* ST_Assign1 *) [exact tactics]
  - (* ST_Assign2 *) [exact tactics]
  - (* ST_AssignLoc *) [exact tactics]
  - (* ... remaining cases ... *)
Qed.
```

## Rules to Apply

1. **Revolutionary Solution**: Every case must be handled with explicit tactics.

2. **Zero Vulnerabilities**: No missing cases. No unexplained `auto`.

3. **Ultra Paranoid Verification**: Each tactic must be justified by an available lemma.

4. **No Shortcuts**: All ~30 cases must be explicitly written.

5. **Foundational Correctness**: Based on exact definitions in codebase.

## Deliverable

Complete Coq proof handling ALL step relation constructors.
