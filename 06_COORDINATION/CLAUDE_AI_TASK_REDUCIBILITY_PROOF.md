# CLAUDE AI DELEGATION TASK: Complete ReducibilityFull.v Proofs

## MISSION CRITICAL - ZERO TOLERANCE FOR FAILURE

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  TASK: Complete ALL admitted proofs in ReducibilityFull.v                        ║
║  MODE: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE ITERATIONS         ║
║  SUCCESS CRITERIA: coqc compiles with ZERO admits                                ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## FILE LOCATION

```
/workspaces/proof/02_FORMAL/coq/termination/ReducibilityFull.v
```

---

## CURRENT STATE

- **Qed proofs:** 12
- **Admitted proofs:** 11
- **Compiles:** Yes (with admits)

---

## EXACT ADMITS TO PROVE (in order of dependency)

### ADMIT 1: CR2_base (Line ~203)
```coq
Lemma CR2_base : forall e e' st ctx st' ctx',
  (e, st, ctx) --> (e', st', ctx') ->
  SN_expr e' ->
  SN_expr e.
```
**What to prove:** If e steps to e' and e' is SN (for all stores), then e is SN (for all stores).

**Proof strategy:**
```coq
Proof.
  intros e e' st ctx st' ctx' Hstep Hsn st0 ctx0.
  constructor.
  intros [[e'' st''] ctx''] Hstep'.
  (* Case 1: e steps to e' in this store - use Hsn *)
  (* Case 2: e steps to something else - use SN property *)
  (* Key insight: SN_expr means SN for ALL stores, so we can use Hsn st0 ctx0 *)
  admit.
Admitted.
```

**ACTUALLY NEEDED:** This lemma may be too strong. Consider proving a weaker version or using the existing SN infrastructure.

---

### ADMIT 2: lam_reducible (Line ~240)
```coq
Lemma lam_reducible : forall x T1 T2 eff body,
  (forall a, Reducible T1 a -> value a -> Reducible T2 ([x := a] body)) ->
  Reducible (TFn T1 T2 eff) (ELam x T1 body).
```

**What to prove:** Lambda is reducible if body is reducible after substitution.

**Proof strategy:**
```coq
Proof.
  intros x T1 T2 eff body Hbody.
  simpl. split.
  - (* SN_expr (ELam x T1 body) - trivial, lambdas are values *)
    apply value_SN. constructor.
  - (* forall reducible a, SN_expr (EApp (ELam x T1 body) a) *)
    intros a Ha.
    (* Need to show EApp (ELam x T1 body) a is SN *)
    (* Key: when a is a value, EApp (ELam x T1 body) a --> [x := a] body *)
    (* When a is not a value, a reduces first *)
    (* Use well-founded induction on SN structure *)

    (* Get that a is SN from Ha *)
    assert (Ha_sn : SN_expr a) by (apply CR1 with T1; exact Ha).

    (* Induction on SN of a *)
    intros st ctx.
    (* ... *)
    admit.
Admitted.
```

**KEY INSIGHT:** Need to handle two cases:
1. `a` is a value → `EApp (ELam x T1 body) a --> [x := a] body` → use Hbody
2. `a` is not a value → `EApp (ELam x T1 body) a --> EApp (ELam x T1 body) a'` → use IH on a'

---

### ADMIT 3: fundamental_reducibility (Line ~280) - THE KEY THEOREM
```coq
Theorem fundamental_reducibility : forall Γ Σ pc e T ε ρ,
  has_type Γ Σ pc e T ε ->
  env_reducible Γ ρ ->
  Reducible T (subst_env ρ e).
```

**What to prove:** Well-typed terms (under reducible substitution) are reducible.

**Proof strategy:** Induction on typing derivation `has_type Γ Σ pc e T ε`.

**CRITICAL:** You must find and read the typing rules in:
```
/workspaces/proof/02_FORMAL/coq/foundations/Typing.v
```

Look for `Inductive has_type` and handle EACH constructor.

**Typical cases:**

```coq
Proof.
  intros Γ Σ pc e T ε ρ Hty Henv.
  induction Hty; simpl.

  - (* T_Unit: has_type Γ Σ pc EUnit TUnit EffectPure *)
    apply unit_reducible.

  - (* T_Bool: has_type Γ Σ pc (EBool b) TBool EffectPure *)
    apply bool_reducible.

  - (* T_Int: has_type Γ Σ pc (EInt n) TInt EffectPure *)
    apply int_reducible.

  - (* T_Var: has_type Γ Σ pc (EVar x) T ε *)
    (* Use env_reducible to get reducibility of ρ x *)
    unfold env_reducible in Henv.
    specialize (Henv x T H). (* H is the lookup hypothesis *)
    destruct Henv as [v [Heq [Hval Hred]]].
    (* subst_env ρ (EVar x) = v *)
    simpl. rewrite Heq.
    exact Hred.

  - (* T_Lam: has_type Γ Σ pc (ELam x T1 body) (TFn T1 T2 eff) ε *)
    apply lam_reducible.
    intros a Ha Hval_a.
    (* Need IH for body under extended env *)
    (* ... *)
    admit.

  - (* T_App: has_type Γ Σ pc (EApp e1 e2) T2 ε *)
    (* IH gives Reducible (TFn T1 T2 eff) (subst_env ρ e1) *)
    (* IH gives Reducible T1 (subst_env ρ e2) *)
    (* Use definition of Reducible at TFn *)
    simpl in IHHty1.
    destruct IHHty1 as [_ Happ].
    apply CR1 with T2.
    (* ... need to show Reducible T2 result ... *)
    admit.

  (* ... many more cases ... *)
Admitted.
```

**IMPORTANT:** The exact constructor names depend on Typing.v. You MUST read it first.

---

### ADMIT 4: well_typed_SN (Line ~310)
```coq
Theorem well_typed_SN : forall Σ pc e T ε,
  has_type nil Σ pc e T ε ->
  SN_expr e.
```

**Proof:** Direct corollary of fundamental_reducibility + CR1.

```coq
Proof.
  intros Σ pc e T ε Hty.
  assert (Hred: Reducible T e).
  { (* Need to show subst_env empty_env e = e *)
    replace e with (subst_env (fun _ => None) e) at 2.
    - apply fundamental_reducibility with (Γ := nil) (Σ := Σ) (pc := pc) (ε := ε).
      + exact Hty.
      + apply env_reducible_nil.
    - (* Prove subst_env (fun _ => None) e = e *)
      (* This requires a lemma about empty substitution *)
      admit. (* or prove inline *)
  }
  apply CR1 with T. exact Hred.
Qed.
```

**NEED:** Lemma that `subst_env (fun _ => None) e = e` for closed terms.

---

### ADMIT 5: SN_app (Line ~325)
```coq
Theorem SN_app : forall f a T1 T2 eff Σ pc,
  has_type nil Σ pc f (TFn T1 T2 eff) EffectPure ->
  has_type nil Σ pc a T1 EffectPure ->
  SN_expr (EApp f a).
```

**Proof:** Similar to well_typed_SN but for applications.

```coq
Proof.
  intros f a T1 T2 eff Σ pc Htyf Htya.
  (* Get reducibility of f and a *)
  assert (Hf: Reducible (TFn T1 T2 eff) f).
  { (* same pattern as well_typed_SN *) admit. }
  assert (Ha: Reducible T1 a).
  { (* same pattern as well_typed_SN *) admit. }
  (* Use definition of Reducible at TFn *)
  simpl in Hf.
  destruct Hf as [_ Happ].
  apply Happ. exact Ha.
Qed.
```

---

## HELPER LEMMAS YOU WILL NEED

### 1. Empty substitution is identity
```coq
Lemma subst_env_nil : forall e,
  subst_env (fun _ => None) e = e.
```

### 2. Substitution distributes over constructs
```coq
Lemma subst_env_app : forall ρ e1 e2,
  subst_env ρ (EApp e1 e2) = EApp (subst_env ρ e1) (subst_env ρ e2).
```

### 3. Extended environment substitution
```coq
Lemma subst_env_extend : forall ρ x v e,
  subst_env (fun y => if String.eqb y x then Some v else ρ y) e =
  [x := v] (subst_env ρ e).
```
(This may need careful handling)

---

## DEFINITIONS YOU NEED TO KNOW

### subst_env (if not defined, add it)
```coq
Fixpoint subst_env (ρ : ident -> option expr) (e : expr) : expr :=
  match e with
  | EVar x => match ρ x with Some v => v | None => EVar x end
  | ELam x T body => ELam x T (subst_env (fun y => if String.eqb y x then None else ρ y) body)
  | EApp e1 e2 => EApp (subst_env ρ e1) (subst_env ρ e2)
  (* ... all other cases recursively ... *)
  end.
```

**CHECK:** Does this already exist in the codebase? Search for it:
```bash
grep -r "subst_env" /workspaces/proof/02_FORMAL/coq/
```

---

## EXECUTION PROTOCOL

### Step 1: Read Required Files
```bash
# Read the file to understand current state
cat /workspaces/proof/02_FORMAL/coq/termination/ReducibilityFull.v

# Read typing rules (CRITICAL)
cat /workspaces/proof/02_FORMAL/coq/foundations/Typing.v | head -500

# Check if subst_env exists
grep -rn "subst_env\|Fixpoint.*subst" /workspaces/proof/02_FORMAL/coq/
```

### Step 2: Add Helper Lemmas First
Add any missing helper lemmas (subst_env_nil, etc.) BEFORE the main proofs.

### Step 3: Prove in Dependency Order
1. First: Helper lemmas
2. Then: CR2_base (or weaken/remove if too hard)
3. Then: lam_reducible
4. Then: fundamental_reducibility
5. Then: well_typed_SN
6. Finally: SN_app

### Step 4: Compile After EACH Change
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -R . RIINA termination/ReducibilityFull.v
```

### Step 5: Iterate Until Zero Admits
```bash
grep -c "Admitted\.\|admit\." termination/ReducibilityFull.v
# Must be 0
```

---

## FALLBACK STRATEGIES

### If fundamental_reducibility is too hard:
1. Prove it for a SUBSET of typing rules (base types only)
2. Add the complex cases as admits with clear documentation
3. The goal is to prove SN_app - if that can be done another way, do it

### If CR2_base is too hard:
1. It may not be needed for the main goal
2. Try removing it and see if other proofs still work
3. Or weaken it to specific cases

### If subst_env is problematic:
1. Check if a similar definition exists elsewhere
2. Use a different formulation (direct substitution instead of environment)

---

## SUCCESS CRITERIA

```bash
$ cd /workspaces/proof/02_FORMAL/coq
$ coqc -R . RIINA termination/ReducibilityFull.v
$ echo $?
0
$ grep -c "Admitted\." termination/ReducibilityFull.v
0
$ grep -c "admit\." termination/ReducibilityFull.v
0
```

**ALL THREE must pass.**

---

## VERIFICATION AFTER COMPLETION

```bash
# 1. Full build still passes
cd /workspaces/proof/02_FORMAL/coq && make

# 2. No axioms introduced
grep -c "^Axiom " termination/ReducibilityFull.v
# Must be 0

# 3. Count Qed proofs (should be ~23+)
grep -c "Qed\." termination/ReducibilityFull.v
```

---

## WHAT NOT TO DO

1. **DO NOT** add axioms
2. **DO NOT** change the Reducible definition unless absolutely necessary
3. **DO NOT** delete lemmas - prove them or document why they're unprovable
4. **DO NOT** assume anything about type constructors - read Typing.v
5. **DO NOT** guess at names - verify with grep/read first

---

## ITERATION PROTOCOL

If you cannot complete all proofs:

1. Document EXACTLY which admits remain
2. Document EXACTLY what you tried
3. Document EXACTLY what blocked you
4. Provide the partial progress
5. Request continuation with specific questions

**There is NO limit on iterations. Keep going until done.**

---

## FINAL REMINDER

```
Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE ITERATIONS

The goal is SN_app with Qed.
Everything else is in service of that goal.
If something is blocking, find a way around it.
```

This task WILL be completed. Failure is not an option.
