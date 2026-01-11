# TERAS-LANG Architecture Decision A-20: Type System Soundness Proofs

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-A20-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | **APPROVED** |

---

## 1. Decision Summary

### 1.1 Decision Statement

**TERAS-LANG SHALL ADOPT** a layered soundness proof strategy:

1. **Syntactic soundness** (Progress + Preservation) for rapid development
2. **Iris-based semantic soundness** for full language coverage
3. **Security-specific theorems** (noninterference, capability safety, etc.)
4. **Full mechanization** in Coq with Iris library
5. **Modular proof architecture** allowing incremental verification

### 1.2 Architecture Decision ID

`TERAS-ARCH-A20-SND-001`

### 1.3 Status

**APPROVED** - Ratified for TERAS-LANG implementation

---

## 2. Context and Requirements

### 2.1 Soundness Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| SND-01 | Type safety (no stuck states) | Critical |
| SND-02 | Memory safety (no invalid access) | Critical |
| SND-03 | Effect safety (only declared effects) | Critical |
| SND-04 | Linear safety (exact resource usage) | Critical |
| SND-05 | Security label safety (IFC) | Critical |
| SND-06 | Capability safety (no amplification) | Critical |
| SND-07 | Session safety (protocol adherence) | High |
| SND-08 | Termination (for total functions) | High |

### 2.2 Verification Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| VER-01 | Machine-checked proofs | Critical |
| VER-02 | Modular proof structure | High |
| VER-03 | Maintainable as language evolves | High |
| VER-04 | Documented assumptions | Critical |
| VER-05 | Coverage of unsafe escape hatches | Critical |

### 2.3 Practical Requirements

| Requirement | Description | Priority |
|-------------|-------------|----------|
| PRA-01 | Proof development < 12 months | High |
| PRA-02 | Incremental proof addition | Medium |
| PRA-03 | Clear correspondence to spec | High |
| PRA-04 | Reusable proof components | Medium |

---

## 3. Decision Details

### 3.1 Layered Proof Architecture

```
TERAS-LANG Soundness Proof Layers:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”

Layer 0: Metatheory Infrastructure
â”œâ”€â”€ Binding representation (locally nameless)
â”œâ”€â”€ Substitution lemmas
â”œâ”€â”€ Context properties
â””â”€â”€ Operational semantics

Layer 1: Syntactic Type Safety
â”œâ”€â”€ Progress theorem
â”œâ”€â”€ Preservation theorem
â”œâ”€â”€ Type safety corollary
â””â”€â”€ Canonical forms

Layer 2: Substructural Safety
â”œâ”€â”€ Linear resource tracking
â”œâ”€â”€ Affine usage verification
â”œâ”€â”€ Context splitting correctness
â””â”€â”€ Resource consumption proof

Layer 3: Effect Safety
â”œâ”€â”€ Effect containment
â”œâ”€â”€ Handler correctness
â”œâ”€â”€ Effect polymorphism
â””â”€â”€ Effect row soundness

Layer 4: Semantic Soundness (Iris)
â”œâ”€â”€ Type interpretation
â”œâ”€â”€ Fundamental theorem
â”œâ”€â”€ Adequacy
â””â”€â”€ State soundness

Layer 5: Security Soundness
â”œâ”€â”€ Noninterference (IFC)
â”œâ”€â”€ Capability safety
â”œâ”€â”€ Session fidelity
â””â”€â”€ State machine correctness

â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

### 3.2 Syntactic Soundness (Layer 1)

**Core Theorems:**

```coq
(* Progress: Well-typed closed terms step or are values *)
Theorem progress : forall e T,
  has_type empty e T ->
  value e \/ exists e', step e e'.

(* Preservation: Typing preserved under reduction *)
Theorem preservation : forall e e' T,
  has_type empty e T ->
  step e e' ->
  has_type empty e' T.

(* Type Safety: Combination *)
Theorem type_safety : forall e T,
  has_type empty e T ->
  safe e.

Definition safe e :=
  forall e', star step e e' ->
    value e' \/ exists e'', step e' e''.
```

**Supporting Lemmas:**

```coq
(* Substitution preserves typing *)
Lemma substitution_preserves_typing : forall Gamma x U e v T,
  has_type (extend Gamma x U) e T ->
  has_type empty v U ->
  has_type Gamma (subst x v e) T.

(* Weakening *)
Lemma weakening : forall Gamma Gamma' e T,
  has_type Gamma e T ->
  includeIn Gamma Gamma' ->
  has_type Gamma' e T.

(* Canonical forms *)
Lemma canonical_forms_arrow : forall v T1 T2,
  has_type empty v (TArrow T1 T2) ->
  value v ->
  exists x e, v = Lam x e.
```

### 3.3 Linear Safety (Layer 2)

**Linear Context:**

```coq
(* Context with usage annotations *)
Inductive lin_ctx : Type :=
  | lin_empty : lin_ctx
  | lin_extend : lin_ctx -> var -> ty -> usage -> lin_ctx.

Inductive usage := Used | Unused.

(* Split context for linear application *)
Inductive ctx_split : lin_ctx -> lin_ctx -> lin_ctx -> Prop :=
  | split_empty : ctx_split lin_empty lin_empty lin_empty
  | split_left : forall G G1 G2 x T,
      ctx_split G G1 G2 ->
      ctx_split (lin_extend G x T Unused)
                (lin_extend G1 x T Used)
                (lin_extend G2 x T Unused)
  | split_right : forall G G1 G2 x T,
      ctx_split G G1 G2 ->
      ctx_split (lin_extend G x T Unused)
                (lin_extend G1 x T Unused)
                (lin_extend G2 x T Used).
```

**Linear Safety Theorem:**

```coq
Theorem linear_safety : forall G e T,
  lin_has_type G e T ->
  all_used G ->
  (* Each linear variable used exactly once *)
  forall x, linear_var G x -> used_count e x = 1.
```

### 3.4 Effect Safety (Layer 3)

**Effect Typing:**

```coq
(* Effects as row types *)
Inductive effect_row : Type :=
  | eff_empty : effect_row
  | eff_cons : effect -> effect_row -> effect_row
  | eff_var : effvar -> effect_row.

(* Effect typing judgment *)
Inductive eff_has_type : ctx -> expr -> ty -> effect_row -> Prop :=
  | T_Pure : forall G e T,
      has_type G e T ->
      eff_has_type G e T eff_empty
  | T_Effect : forall G e T E,
      primitive_effect e E ->
      eff_has_type G e T (eff_cons E eff_empty)
  (* ... more rules ... *)
```

**Effect Containment:**

```coq
Theorem effect_containment : forall G e T E,
  eff_has_type G e T E ->
  forall e' eff,
    star step e e' ->
    performs_effect e' eff ->
    effect_member eff E.
```

### 3.5 Iris Semantic Soundness (Layer 4)

**Type Interpretation:**

```coq
(* Semantic interpretation in Iris *)
Fixpoint interp (T : ty) : val -> iProp :=
  match T with
  | TInt => fun v => âŒœâˆƒ n, v = VInt nâŒ
  | TBool => fun v => âŒœv = VTrue âˆ¨ v = VFalseâŒ
  | TArrow T1 T2 => fun v =>
      â–¡ (âˆ€ w, interp T1 w -âˆ— WP (App v w) {{ interp T2 }})
  | TLinArrow T1 T2 => fun v =>
      âˆ€ w, interp T1 w -âˆ— WP (App v w) {{ interp T2 }}
  | TRef T => fun v =>
      âˆƒ l, âŒœv = VLoc lâŒ âˆ— l â†¦ interp T
  | TForall T => fun v =>
      âˆ€ A : val -> iProp, â–¡ (âˆ€ w, A w -âˆ— WP (TApp v) {{ interp (T A) }})
  end.
```

**Fundamental Theorem:**

```coq
(* Well-typed terms satisfy their semantic type *)
Theorem fundamental : forall G e T,
  has_type G e T ->
  G âŠ¨ e : T.

Definition sem_typed G e T :=
  âˆ€ Î³, interp_ctx G Î³ -âˆ— WP (subst Î³ e) {{ interp T }}.

Notation "G âŠ¨ e : T" := (sem_typed G e T).
```

**Adequacy:**

```coq
(* Semantic typing implies type safety *)
Theorem adequacy : forall e T,
  (âˆ… âŠ¨ e : T) ->
  safe e.
```

### 3.6 Security Soundness (Layer 5)

**Noninterference:**

```coq
(* Binary logical relation for IFC *)
Fixpoint interp_rel (L : label) (T : ty) : val -> val -> iProp :=
  match T with
  | TLabeled L' T' => 
      if flows L' L 
      then fun v1 v2 => interp_rel L T' v1 v2  (* must be equal *)
      else fun v1 v2 => True  (* can differ *)
  | TArrow T1 T2 => fun v1 v2 =>
      â–¡ (âˆ€ w1 w2, interp_rel L T1 w1 w2 -âˆ— 
           WP (App v1 w1) {{ u1, WP (App v2 w2) {{ u2,
             interp_rel L T2 u1 u2 }} }})
  | _ => (* ... *)
  end.

(* Noninterference theorem *)
Theorem noninterference : forall e T L,
  has_type empty e (TLabeled L T) ->
  L = Low ->
  forall H1 H2 v1 v2,
    eval_with_high H1 e v1 ->
    eval_with_high H2 e v2 ->
    v1 = v2.
```

**Capability Safety:**

```coq
(* Capability as Iris resource *)
Definition cap_token (c : cap) : iProp := own Î³ (â—¯ {[ c ]}).

(* Capability-safe operation *)
Definition cap_safe_op (op : operation) (c : cap) : iProp :=
  {{{ cap_token c }}} 
    op 
  {{{ v, RET v; cap_token c }}}.

(* No capability amplification *)
Theorem capability_safety : forall e C,
  has_caps empty e C ->
  forall e' c,
    star step e e' ->
    requires_cap e' c ->
    cap_member c C.
```

**Session Fidelity:**

```coq
(* Session type interpretation *)
Fixpoint interp_session (S : session_ty) (ch : channel) : iProp :=
  match S with
  | SSend T S' => 
      âˆ€ v, interp T v -âˆ— WP (send ch v) {{ _, interp_session S' ch }}
  | SRecv T S' =>
      WP (recv ch) {{ v, interp T v âˆ— interp_session S' ch }}
  | SEnd => ch â†¦ Closed
  | SChoice S1 S2 =>
      (interp_session S1 ch) âˆ¨ (interp_session S2 ch)
  end.

(* Session fidelity *)
Theorem session_fidelity : forall P Q S,
  well_typed_session P Q S ->
  safe_composition P Q.
```

### 3.7 Unsafe Code Verification

```coq
(* Semantic typing for unsafe blocks *)
Definition unsafe_valid (e : expr) (T : ty) : iProp :=
  WP e {{ v, interp T v }}.

(* Proof obligation for unsafe code *)
Theorem unsafe_typing : forall e T,
  unsafe_valid e T ->
  (* Assuming unsafe block satisfies spec *)
  sem_typed empty e T.

(* Example: verifying raw pointer operation *)
Lemma raw_ptr_deref_safe : forall p T,
  p â†¦ ?v -âˆ—
  interp T v -âˆ—
  WP (unsafe { *p }) {{ interp T }}.
```

---

## 4. Integration with Previous Decisions

### 4.1 Type-Level Computation (A-18)

```coq
(* Type family reduction in semantics *)
Lemma type_family_sound : forall F args T,
  type_family_reduces F args T ->
  interp (TFamily F args) â‰¡ interp T.
```

### 4.2 Type Inference (A-19)

```coq
(* Inference produces well-typed terms *)
Theorem inference_sound : forall e T,
  infer empty e = Some T ->
  has_type empty e T.

(* Combined with type safety *)
Corollary inferred_programs_safe : forall e T,
  infer empty e = Some T ->
  safe e.
```

### 4.3 Linear Types (A-04)

```coq
(* Linear semantics via separating conjunction *)
Definition lin_interp (T : ty) : val -> iProp :=
  match T with
  | TLin T' => interp T'  (* no persistence *)
  | TAff T' => interp T'  (* at most once *)
  | _ => â–¡ interp T  (* unrestricted *)
  end.
```

### 4.4 Effect Types (A-05, A-11)

```coq
(* Effect-indexed WP *)
Definition WP_eff (E : effect_row) (e : expr) (Î¦ : val -> iProp) : iProp :=
  WP e {{ v, Î¦ v âˆ— âŒœeffects_in EâŒ }}.

(* Effect typing implies effect-bounded execution *)
Theorem effect_semantic_soundness : forall G e T E,
  eff_has_type G e T E ->
  G âŠ¨eff e : T ! E.
```

### 4.5 Capability Types (A-14)

```coq
(* Capability as owned resource *)
Definition cap_interp (C : capset) : iProp :=
  [âˆ— set] c âˆˆ C, cap_token c.

(* Capability-indexed execution *)
Definition WP_cap (C : capset) (e : expr) (Î¦ : val -> iProp) : iProp :=
  cap_interp C -âˆ— WP e {{ v, Î¦ v âˆ— cap_interp C }}.
```

---

## 5. Mechanization Strategy

### 5.1 Coq Project Structure

```
teras-lang-proofs/
â”œâ”€â”€ theories/
â”‚   â”œâ”€â”€ Prelude/           # Basic definitions
â”‚   â”‚   â”œâ”€â”€ Syntax.v       # AST
â”‚   â”‚   â”œâ”€â”€ Semantics.v    # Operational semantics
â”‚   â”‚   â””â”€â”€ Context.v      # Typing contexts
â”‚   â”œâ”€â”€ Syntactic/         # Syntactic proofs
â”‚   â”‚   â”œâ”€â”€ Progress.v
â”‚   â”‚   â”œâ”€â”€ Preservation.v
â”‚   â”‚   â”œâ”€â”€ TypeSafety.v
â”‚   â”‚   â””â”€â”€ Linear.v
â”‚   â”œâ”€â”€ Iris/              # Semantic proofs
â”‚   â”‚   â”œâ”€â”€ Interp.v       # Type interpretation
â”‚   â”‚   â”œâ”€â”€ Fundamental.v  # Fundamental theorem
â”‚   â”‚   â”œâ”€â”€ Adequacy.v
â”‚   â”‚   â””â”€â”€ State.v
â”‚   â”œâ”€â”€ Security/          # Security proofs
â”‚   â”‚   â”œâ”€â”€ IFC.v          # Noninterference
â”‚   â”‚   â”œâ”€â”€ Capability.v
â”‚   â”‚   â”œâ”€â”€ Session.v
â”‚   â”‚   â””â”€â”€ StateMachine.v
â”‚   â””â”€â”€ Integration/       # Combined results
â”‚       â”œâ”€â”€ FullSoundness.v
â”‚       â””â”€â”€ SecurityGuarantees.v
â”œâ”€â”€ examples/              # Example verifications
â””â”€â”€ extraction/            # Coq extraction setup
```

### 5.2 Proof Conventions

```coq
(* Naming conventions *)
(* Theorems: descriptive_name *)
(* Lemmas: helper_descriptive_name *)
(* Definitions: TypeName or def_name *)

(* Documentation *)
(** * Section Title *)
(** Informal description of this section. *)

(* Proof style *)
(* - Use bullets (-, +, *) for subgoals *)
(* - Name important hypotheses *)
(* - Use automation (auto, eauto) judiciously *)
```

### 5.3 Automation

```coq
(* Hint databases *)
Create HintDb teras_typing.
Create HintDb teras_safety.
Create HintDb teras_security.

(* Custom tactics *)
Ltac solve_typing := 
  repeat match goal with
  | |- has_type _ (Var _) _ => apply T_Var; auto
  | |- has_type _ (App _ _) _ => eapply T_App
  | |- has_type _ (Lam _ _) _ => apply T_Lam
  | _ => auto with teras_typing
  end.
```

---

## 6. TERAS Product Integration

### 6.1 Security Guarantees by Product

| Product | Proved Properties |
|---------|-------------------|
| MENARA | Permission safety, mobile IFC |
| GAPURA | Request type safety, taint tracking |
| ZIRAH | Capability isolation, scan safety |
| BENTENG | Verification workflow correctness |
| SANDI | Key linearity, algorithm safety |

### 6.2 Verification Scope

```
TERAS Product Verification:
â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”

Core Language:
â”œâ”€â”€ Type safety (syntactic + semantic)
â”œâ”€â”€ Memory safety (Iris)
â”œâ”€â”€ Effect safety
â””â”€â”€ Linear safety

Security Properties:
â”œâ”€â”€ Noninterference (per-product labels)
â”œâ”€â”€ Capability safety (permission model)
â”œâ”€â”€ Session types (protocol verification)
â””â”€â”€ State machines (workflow verification)

Unsafe Code:
â”œâ”€â”€ FFI boundaries
â”œâ”€â”€ Low-level crypto operations
â”œâ”€â”€ Performance-critical paths
â””â”€â”€ Hardware interaction

NOT in scope (trusted):
â”œâ”€â”€ Hardware correctness
â”œâ”€â”€ OS kernel
â”œâ”€â”€ Network stack
â””â”€â”€ External dependencies (none by design)

â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”â”
```

---

## 7. Implementation Roadmap

### 7.1 Development Phases

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| 1. Infrastructure | 4 weeks | Syntax, semantics, binding |
| 2. Syntactic Core | 6 weeks | Progress, preservation, type safety |
| 3. Linear Types | 4 weeks | Linear safety proofs |
| 4. Effects | 4 weeks | Effect containment |
| 5. Iris Setup | 4 weeks | Iris integration, basic interp |
| 6. Semantic Types | 6 weeks | Full type interpretation |
| 7. Fundamental | 4 weeks | Fundamental theorem |
| 8. Security | 8 weeks | IFC, capabilities, sessions |
| 9. Integration | 4 weeks | Combined theorems |
| 10. Documentation | 2 weeks | Proof documentation |
| **Total** | **46 weeks** | Complete soundness proofs |

### 7.2 Milestones

| Milestone | Date (relative) | Deliverable |
|-----------|-----------------|-------------|
| M1 | Week 10 | Syntactic type safety |
| M2 | Week 18 | Linear + effect safety |
| M3 | Week 28 | Semantic soundness |
| M4 | Week 40 | Security soundness |
| M5 | Week 46 | Full integration |

### 7.3 Resource Requirements

| Resource | Quantity | Purpose |
|----------|----------|---------|
| Proof engineers | 2 FTE | Coq development |
| Language expert | 0.5 FTE | Spec alignment |
| Security expert | 0.5 FTE | Security proofs |
| Coq expert | 0.25 FTE | Consulting |

---

## 8. Validation Criteria

### 8.1 Proof Completeness

- [ ] All typing rules have corresponding proof cases
- [ ] All operational rules handled in preservation
- [ ] All value forms in canonical forms lemma
- [ ] All security properties theorem statements

### 8.2 Proof Quality

- [ ] No admitted lemmas in final development
- [ ] Axioms documented and justified
- [ ] Proof scripts compile in < 30 minutes
- [ ] CI/CD for proof checking

### 8.3 Documentation

- [ ] Informal theorem statements for each major result
- [ ] Correspondence to language specification
- [ ] Assumptions clearly stated
- [ ] Examples for key properties

---

## 9. Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Iris learning curve | High | Medium | Training, external consulting |
| Proof complexity | High | Medium | Incremental development |
| Spec changes | Medium | High | Modular proof architecture |
| Performance | Low | Medium | Proof engineering techniques |
| Incomplete coverage | Low | High | Systematic case analysis |

---

## 10. References

1. Jung, R., et al. (2018). "RustBelt: Securing the Foundations of the Rust Programming Language"
2. Jung, R., et al. (2018). "Iris from the Ground Up"
3. Wright, A., & Felleisen, M. (1994). "A Syntactic Approach to Type Soundness"
4. Pierce, B. C. (2002). "Types and Programming Languages"
5. Ahmed, A. (2006). "Step-Indexed Syntactic Logical Relations"
6. TERAS Architecture Decisions A-01 through A-19

---

## 11. Approval

| Role | Name | Date | Signature |
|------|------|------|-----------|
| TERAS Architect | [Pending] | | |
| Verification Lead | [Pending] | | |
| Security Lead | [Pending] | | |

---

*Architecture Decision Record for TERAS-LANG type system soundness proofs.*
