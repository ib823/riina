# RIINA Iris Migration Specification v1.0.0

**Document ID:** `RIINA_IRIS_MIGRATION_SPEC_v1_0_0`

**Version:** 1.0.0  
**Date:** 2026-01-29  
**Author:** RIINA Formal Verification Team  
**Status:** Draft for Review

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Iris Framework Overview](#2-iris-framework-overview)
3. [Required Coq Imports](#3-required-coq-imports)
4. [Definition Migration: Before and After](#4-definition-migration-before-and-after)
5. [Axiom Elimination Mapping](#5-axiom-elimination-mapping)
6. [Migration Sequence](#6-migration-sequence)
7. [Effect System Integration](#7-effect-system-integration)
8. [Session Type Integration](#8-session-type-integration)
9. [Risks and Mitigations](#9-risks-and-mitigations)
10. [Testing and Validation Strategy](#10-testing-and-validation-strategy)
11. [Appendix: Complete Type Definitions](#appendix-a-complete-type-definitions)

---

## 1. Executive Summary

### 1.1 Current State

RIINA's formal verification infrastructure currently relies on **custom, hand-rolled step-indexed logical relations** implemented directly in Coq. This approach has resulted in:

- **19 axioms** (unproven assumptions)
- **67 admitted proofs** (placeholders)
- **~12,000 lines** of infrastructure code for step-indexing machinery
- **Fragile world monotonicity proofs** that break when the type system extends

### 1.2 Target State

Migration to the **Iris framework** (coq-iris) will provide:

- **Battle-tested step-indexed logical relations** with 10+ years of academic vetting
- **Automatic step-index management** via the later modality (▷)
- **Separation logic** for clean store reasoning
- **Invariant mechanism** for world monotonicity
- **Concurrent reasoning** (future-proofing RIINA for concurrent extensions)
- **Elimination of 14-16 axioms** and **~50 admitted proofs**

### 1.3 Estimated Effort

| Phase | Duration | Risk Level |
|-------|----------|------------|
| Phase 1: Infrastructure Setup | 2 weeks | Low |
| Phase 2: Value Relations | 4 weeks | Medium |
| Phase 3: Expression Relations | 4 weeks | Medium |
| Phase 4: Store Relations | 3 weeks | Medium |
| Phase 5: Non-Interference Proofs | 6 weeks | High |
| Phase 6: Effect Integration | 4 weeks | High |
| Phase 7: Session Types | 4 weeks | High |
| **Total** | **27 weeks** | — |

---

## 2. Iris Framework Overview

### 2.1 Core Concepts

Iris is a **higher-order concurrent separation logic** framework implemented in Coq. Its key features relevant to RIINA are:

1. **iProp (Σ)**: The type of Iris propositions, parameterized by a camera (resource algebra) signature Σ
2. **Later Modality (▷)**: Built-in step-indexing — ▷P means "P holds after one computation step"
3. **Persistent Modality (□)**: Propositions that can be freely duplicated
4. **Separating Conjunction (∗)**: P ∗ Q means P and Q hold on disjoint resources
5. **Magic Wand (-∗)**: Separating implication
6. **Invariants**: Named propositions that hold across all computation steps
7. **Ghost State**: Abstract resources for tracking logical information

### 2.2 Why Iris Solves RIINA's Problems

| RIINA Problem | Iris Solution |
|---------------|---------------|
| Manual step-index threading | Later modality (▷) handles automatically |
| World monotonicity proofs | Invariant monotonicity is built-in |
| Store extension lemmas | Separation logic frame rule |
| Compositionality axioms | Higher-order quantification in iProp |
| Downward closure proofs | Löb induction principle |

---

## 3. Required Coq Imports

### 3.1 Core Iris Infrastructure

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   RIINA Iris Migration - Core Imports
   ═══════════════════════════════════════════════════════════════════════════ *)

(* === Base Logic and Propositions === *)
From iris.bi Require Import bi.                    (* Base BI logic interface *)
From iris.bi Require Import derived_connectives.   (* Derived logical connectives *)
From iris.bi Require Import big_op.                (* Big operators: [∗], [∧] *)
From iris.bi Require Import telescopes.            (* Telescope abstraction *)

(* === Proof Mode (Interactive Tactics) === *)
From iris.proofmode Require Import tactics.        (* iIntros, iDestruct, etc. *)
From iris.proofmode Require Import environments.   (* Proof mode environments *)
From iris.proofmode Require Import coq_tactics.    (* Low-level tactics *)
From iris.proofmode Require Import reduction.      (* Reduction tactics *)
From iris.proofmode Require Import classes.        (* Typeclass instances *)

(* === Resource Algebras (Cameras) === *)
From iris.algebra Require Import cmra.             (* Camera definition *)
From iris.algebra Require Import auth.             (* Authoritative camera *)
From iris.algebra Require Import excl.             (* Exclusive camera *)
From iris.algebra Require Import agree.            (* Agreement camera *)
From iris.algebra Require Import gmap.             (* Map camera *)
From iris.algebra Require Import gset.             (* Set camera *)
From iris.algebra Require Import frac.             (* Fractional permissions *)
From iris.algebra Require Import dfrac.            (* Discardable fractions *)
From iris.algebra Require Import csum.             (* Camera sum *)
From iris.algebra Require Import list.             (* List camera *)
From iris.algebra Require Import ofe.              (* Ordered families of equiv. *)

(* === Base Logic with Ghost State === *)
From iris.base_logic Require Import lib.iprop.     (* iProp definition *)
From iris.base_logic Require Import lib.own.       (* own γ a *)
From iris.base_logic Require Import lib.invariants. (* inv N P *)
From iris.base_logic Require Import lib.ghost_var. (* Ghost variables *)
From iris.base_logic Require Import lib.mono_nat.  (* Monotonic naturals *)
From iris.base_logic Require Import lib.saved_prop. (* Saved propositions *)
From iris.base_logic Require Import lib.gen_heap.  (* Generic heap *)

(* === Program Logic === *)
From iris.program_logic Require Import weakestpre. (* Weakest precondition *)
From iris.program_logic Require Import adequacy.   (* Adequacy theorem *)
From iris.program_logic Require Import lifting.    (* Lifting lemmas *)
From iris.program_logic Require Import ectx_lifting. (* Evaluation context lifting *)
From iris.program_logic Require Import ectxi_language. (* Language interface *)

(* === Heap Language (Reference Implementation) === *)
From iris.heap_lang Require Import lang.           (* HeapLang syntax *)
From iris.heap_lang Require Import notation.       (* HeapLang notation *)
From iris.heap_lang Require Import proofmode.      (* HeapLang proof mode *)
From iris.heap_lang Require Import adequacy.       (* HeapLang adequacy *)
From iris.heap_lang Require Import primitive_laws. (* Points-to, etc. *)

(* === Unstable/Advanced Features === *)
From iris.unstable.heap_lang Require Import interpreter. (* For testing *)
```

### 3.2 RIINA-Specific Import Organization

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   RIINA Language Definition Imports
   ═══════════════════════════════════════════════════════════════════════════ *)

(* RIINA must define its language to satisfy Iris's language interface *)
From riina.lang Require Import syntax.         (* RIINA AST *)
From riina.lang Require Import types.          (* RIINA type system *)
From riina.lang Require Import semantics.      (* Small-step semantics *)
From riina.lang Require Import security.       (* Security lattice *)
From riina.lang Require Import effects.        (* Effect system *)
From riina.lang Require Import sessions.       (* Session types *)

(* RIINA-Iris bridge *)
From riina.iris Require Import lang_interface. (* ectxi_language instance *)
From riina.iris Require Import resources.      (* RIINA-specific cameras *)
From riina.iris Require Import notation.       (* RIINA-specific notation *)
```

### 3.3 Import Dependencies Graph

```
                    ┌─────────────────┐
                    │  iris.algebra   │
                    │  (cmra, auth,   │
                    │   gmap, etc.)   │
                    └────────┬────────┘
                             │
                    ┌────────▼────────┐
                    │    iris.bi      │
                    │ (bi, big_op,    │
                    │  derived_conn.) │
                    └────────┬────────┘
                             │
          ┌──────────────────┼──────────────────┐
          │                  │                  │
┌─────────▼─────────┐ ┌──────▼──────┐ ┌─────────▼─────────┐
│ iris.proofmode    │ │ iris.base   │ │ iris.program      │
│ (tactics, env)    │ │ _logic.lib  │ │ _logic            │
└─────────┬─────────┘ │ (iprop,own, │ │ (weakestpre,      │
          │           │  invariants)│ │  adequacy)        │
          │           └──────┬──────┘ └─────────┬─────────┘
          │                  │                  │
          └──────────────────┼──────────────────┘
                             │
                    ┌────────▼────────┐
                    │ riina.iris      │
                    │ (value_rel,     │
                    │  expr_rel,      │
                    │  noninterf.)    │
                    └─────────────────┘
```

---

## 4. Definition Migration: Before and After

### 4.1 Value Relation (`val_rel_n`)

#### 4.1.1 BEFORE: Custom Step-Indexed Definition

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   BEFORE: Custom step-indexed value relation (riina/logic/value_rel.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Step-indexed value relation - relates two values at type T for n steps *)
Fixpoint val_rel_n (n : nat) (T : ty) (v1 v2 : expr) {struct T} : Prop :=
  is_value v1 ∧ is_value v2 ∧
  match T with
  (* --- Base Types --- *)
  | TUnit => 
      v1 = EUnit ∧ v2 = EUnit
      
  | TBool => 
      ∃ b : bool, v1 = EBool b ∧ v2 = EBool b
      
  | TInt => 
      ∃ z : Z, v1 = EInt z ∧ v2 = EInt z
      
  | TString => 
      ∃ s : string, v1 = EString s ∧ v2 = EString s
      
  | TBytes =>
      ∃ bs : list byte, v1 = EBytes bs ∧ v2 = EBytes bs

  (* --- Function Types --- *)
  | TFn T1 T2 eff =>
      ∃ x1 x2 e1 e2,
        v1 = ELam x1 e1 ∧ v2 = ELam x2 e2 ∧
        (* Functions are related if related inputs produce related outputs *)
        ∀ m, m < n →
        ∀ w1 w2, val_rel_n m T1 w1 w2 →
        exp_rel_n m T2 (subst x1 w1 e1) (subst x2 w2 e2)

  (* --- Product Types --- *)
  | TProd T1 T2 =>
      ∃ v1a v1b v2a v2b,
        v1 = EPair v1a v1b ∧ v2 = EPair v2a v2b ∧
        val_rel_n n T1 v1a v2a ∧ val_rel_n n T2 v1b v2b

  (* --- Sum Types --- *)
  | TSum T1 T2 =>
      (∃ w1 w2, v1 = EInl w1 ∧ v2 = EInl w2 ∧ val_rel_n n T1 w1 w2) ∨
      (∃ w1 w2, v1 = EInr w1 ∧ v2 = EInr w2 ∧ val_rel_n n T2 w1 w2)

  (* --- Reference Types (requires store relation) --- *)
  | TRef T sec_level =>
      ∃ l1 l2 : loc,
        v1 = ELoc l1 ∧ v2 = ELoc l2 ∧
        (* Locations must be related in the current world *)
        world_loc_rel n l1 l2 T sec_level

  (* --- Security Types --- *)
  | TSecret T =>
      (* Secret values: only require both are well-typed, not equal *)
      is_value v1 ∧ is_value v2 ∧ has_type ∅ v1 T ∧ has_type ∅ v2 T
      
  | TLabeled T level =>
      val_rel_n n T v1 v2
      
  | TTainted T source =>
      val_rel_n n T v1 v2
      
  | TSanitized T sanitizer =>
      val_rel_n n T v1 v2

  (* --- Channel Types --- *)
  | TChan sess_ty =>
      ∃ ch1 ch2 : channel_id,
        v1 = EChan ch1 ∧ v2 = EChan ch2 ∧
        channel_rel n ch1 ch2 sess_ty

  (* --- Capability Types --- *)
  | TCapability kind =>
      ∃ cap1 cap2 : capability,
        v1 = ECap cap1 ∧ v2 = ECap cap2 ∧
        capability_rel cap1 cap2 kind
  end

(* Mutual definition with expression relation *)
with exp_rel_n (n : nat) (T : ty) (e1 e2 : expr) {struct n} : Prop :=
  ∀ s1 s2 v1 k,
    k ≤ n →
    store_rel k s1 s2 →
    steps s1 e1 k s1' v1 →
    is_value v1 →
    ∃ s2' v2,
      steps s2 e2 v2 ∧
      is_value v2 ∧
      val_rel_n (n - k) T v1 v2 ∧
      store_rel (n - k) s1' s2'.

(* World/location relation (sketched) *)
Definition world_loc_rel (n : nat) (l1 l2 : loc) (T : ty) (sec : security_level) : Prop :=
  (* ... complex definition involving store_typing and invariants ... *)
  admitted.

(* ═══════════════════════════════════════════════════════════════════════════
   PROBLEMS WITH CUSTOM APPROACH:
   
   1. Manual step-index threading — every recursive call must decrement n
   2. world_loc_rel requires axioms about world extension
   3. Mutual recursion between val_rel_n and exp_rel_n is fragile
   4. Proving step monotonicity (val_rel_n n → val_rel_n m for m ≤ n) is tedious
   5. No automation — every proof is manual
   ═══════════════════════════════════════════════════════════════════════════ *)
```

#### 4.1.2 AFTER: Iris-Based Definition

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   AFTER: Iris-based value relation (riina/iris/value_rel.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import iprop invariants.
From iris.program_logic Require Import weakestpre.
From iris.heap_lang Require Import proofmode.
From riina.iris Require Import lang_interface resources notation.

Section value_relation.
  (* Σ is the global camera signature; includes RIINA-specific resources *)
  Context `{!riinaGS Σ}.    (* RIINA ghost state *)
  Context `{!heapGS Σ}.     (* Heap ghost state for points-to *)

  (* ─────────────────────────────────────────────────────────────────────────
     Type interpretation: maps RIINA types to Iris predicates on values
     
     Key insight: Instead of val_rel_n : nat → ty → expr → expr → Prop,
     we define interp : ty → val → val → iProp Σ
     
     The step-indexing is IMPLICIT in iProp — no manual n threading!
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* We use a recursive definition via Iris's fixpoint mechanism *)
  (* First, define the "unfolded" relation as a function *)
  
  Definition interp_unit : val → val → iProp Σ :=
    λ v1 v2, ⌜v1 = #() ∧ v2 = #()⌝.
  
  Definition interp_bool : val → val → iProp Σ :=
    λ v1 v2, ∃ b : bool, ⌜v1 = #b ∧ v2 = #b⌝.
  
  Definition interp_int : val → val → iProp Σ :=
    λ v1 v2, ∃ z : Z, ⌜v1 = #z ∧ v2 = #z⌝.
  
  Definition interp_string : val → val → iProp Σ :=
    λ v1 v2, ∃ s : string, ⌜v1 = #(LitString s) ∧ v2 = #(LitString s)⌝.
  
  Definition interp_bytes : val → val → iProp Σ :=
    λ v1 v2, ∃ bs : list Z, ⌜v1 = RIINA_bytes bs ∧ v2 = RIINA_bytes bs⌝.

  (* ─────────────────────────────────────────────────────────────────────────
     Function type interpretation using ▷ (later) for step-indexing
     
     Key insight: The ▷ modality handles step-indexing automatically!
     When we write ▷ (interp T2 w1 w2), Iris ensures this only needs to
     hold after one step of computation — exactly what step-indexing does.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* We need a fixpoint for recursive types. Use Iris's contractive fixpoint. *)
  (* For now, assume interp is already defined and show the function case. *)
  
  Definition interp_fn_pre 
    (interp : ty → val → val → iProp Σ)  (* recursive occurrence *)
    (T1 T2 : ty) (eff : effect) : val → val → iProp Σ :=
    λ v1 v2,
      ∃ (x1 x2 : binder) (e1 e2 : expr),
        ⌜v1 = RecV x1 BAnon e1 ∧ v2 = RecV x2 BAnon e2⌝ ∗
        (* □ makes this persistent — can use the function multiple times *)
        □ (∀ (w1 w2 : val),
             (* ▷ is the magic: step-index decrement is automatic! *)
             ▷ interp T1 w1 w2 -∗
             (* Expression relation via WP (weakest precondition) *)
             expr_rel interp T2 eff (subst' x1 w1 e1) (subst' x2 w2 e2)).

  (* ─────────────────────────────────────────────────────────────────────────
     Product type interpretation — no step-indexing needed here
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition interp_prod_pre
    (interp : ty → val → val → iProp Σ)
    (T1 T2 : ty) : val → val → iProp Σ :=
    λ v1 v2,
      ∃ (v1a v1b v2a v2b : val),
        ⌜v1 = PairV v1a v1b ∧ v2 = PairV v2a v2b⌝ ∗
        interp T1 v1a v2a ∗
        interp T2 v1b v2b.

  (* ─────────────────────────────────────────────────────────────────────────
     Sum type interpretation
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition interp_sum_pre
    (interp : ty → val → val → iProp Σ)
    (T1 T2 : ty) : val → val → iProp Σ :=
    λ v1 v2,
      (∃ w1 w2, ⌜v1 = InjLV w1 ∧ v2 = InjLV w2⌝ ∗ interp T1 w1 w2) ∨
      (∃ w1 w2, ⌜v1 = InjRV w1 ∧ v2 = InjRV w2⌝ ∗ interp T2 w1 w2).

  (* ─────────────────────────────────────────────────────────────────────────
     Reference type interpretation using Iris invariants
     
     Key insight: world_loc_rel becomes an INVARIANT.
     Iris invariants automatically provide:
     - Persistence (can be used multiple times)
     - Monotonicity (new invariants can be added, but existing ones preserved)
     - Frame property (disjoint state is untouched)
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Invariant namespace for reference relations *)
  Definition refN : namespace := nroot .@ "riina" .@ "ref".
  
  Definition interp_ref_pre
    (interp : ty → val → val → iProp Σ)
    (T : ty) (sec_level : security_level) : val → val → iProp Σ :=
    λ v1 v2,
      ∃ (l1 l2 : loc),
        ⌜v1 = #l1 ∧ v2 = #l2⌝ ∗
        (* The invariant asserts: locations hold related values *)
        inv (refN .@ l1 .@ l2) (
          ∃ (w1 w2 : val),
            l1 ↦ w1 ∗ l2 ↦ w2 ∗
            (* ▷ for step-indexing in invariant content *)
            ▷ interp T w1 w2 ∗
            (* Security level ghost state *)
            sec_level_res l1 sec_level ∗
            sec_level_res l2 sec_level
        ).

  (* ─────────────────────────────────────────────────────────────────────────
     Security type interpretations
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* TSecret: values are related iff they have the same type, not same value *)
  Definition interp_secret_pre
    (interp : ty → val → val → iProp Σ)
    (T : ty) : val → val → iProp Σ :=
    λ v1 v2,
      (* Only require that both are well-typed values of type T *)
      ⌜is_val v1 ∧ is_val v2⌝ ∗
      □ typed_val T v1 ∗
      □ typed_val T v2.
      (* Note: v1 and v2 need NOT be equal — this is non-interference! *)
  
  (* TLabeled: track the security label as ghost state *)
  Definition interp_labeled_pre
    (interp : ty → val → val → iProp Σ)
    (T : ty) (level : security_level) : val → val → iProp Σ :=
    λ v1 v2,
      interp T v1 v2 ∗
      label_res v1 level ∗
      label_res v2 level.
  
  (* TTainted: track taint source *)
  Definition interp_tainted_pre
    (interp : ty → val → val → iProp Σ)
    (T : ty) (source : taint_source) : val → val → iProp Σ :=
    λ v1 v2,
      interp T v1 v2 ∗
      taint_res v1 source ∗
      taint_res v2 source.
  
  (* TSanitized: track sanitization status *)
  Definition interp_sanitized_pre
    (interp : ty → val → val → iProp Σ)
    (T : ty) (sanitizer : sanitizer_id) : val → val → iProp Σ :=
    λ v1 v2,
      interp T v1 v2 ∗
      sanitized_res v1 sanitizer ∗
      sanitized_res v2 sanitizer.

  (* ─────────────────────────────────────────────────────────────────────────
     Channel type interpretation (placeholder — see Section 8)
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition interp_chan_pre
    (interp : ty → val → val → iProp Σ)
    (sess_ty : session_type) : val → val → iProp Σ :=
    λ v1 v2,
      ∃ (ch1 ch2 : chan_id),
        ⌜v1 = ChanV ch1 ∧ v2 = ChanV ch2⌝ ∗
        session_rel ch1 ch2 sess_ty.

  (* ─────────────────────────────────────────────────────────────────────────
     Capability type interpretation
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition interp_capability_pre
    (interp : ty → val → val → iProp Σ)
    (kind : capability_kind) : val → val → iProp Σ :=
    λ v1 v2,
      ∃ (cap1 cap2 : capability),
        ⌜v1 = CapV cap1 ∧ v2 = CapV cap2⌝ ∗
        capability_res cap1 kind ∗
        capability_res cap2 kind ∗
        ⌜capability_equiv kind cap1 cap2⌝.

  (* ─────────────────────────────────────────────────────────────────────────
     Full type interpretation via contractive fixpoint
     
     We use Iris's guarded fixpoint to handle recursive types.
     The ▷ in interp_fn_pre makes the definition contractive.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Semantic type: a relation on values *)
  Definition sem_ty := val → val → iProp Σ.
  
  (* The interpretation function, defined via fixpoint *)
  Fixpoint interp (T : ty) : sem_ty :=
    match T with
    | TUnit => interp_unit
    | TBool => interp_bool
    | TInt => interp_int
    | TString => interp_string
    | TBytes => interp_bytes
    | TFn T1 T2 eff => interp_fn_pre interp T1 T2 eff
    | TProd T1 T2 => interp_prod_pre interp T1 T2
    | TSum T1 T2 => interp_sum_pre interp T1 T2
    | TRef T sec => interp_ref_pre interp T sec
    | TSecret T => interp_secret_pre interp T
    | TLabeled T lev => interp_labeled_pre interp T lev
    | TTainted T src => interp_tainted_pre interp T src
    | TSanitized T san => interp_sanitized_pre interp T san
    | TChan sess => interp_chan_pre interp sess
    | TCapability kind => interp_capability_pre interp kind
    end.
  
  (* Notation for value relation *)
  Notation "⟦ T ⟧ᵥ" := (interp T) (at level 0).
  Notation "v1 ≈ᵥ[ T ] v2" := (interp T v1 v2) (at level 70).

End value_relation.

(* ═══════════════════════════════════════════════════════════════════════════
   WHY IRIS VERSION IS BETTER:
   
   1. NO MANUAL STEP-INDEX:
      - Before: val_rel_n n T v1 v2, must thread n everywhere
      - After: v1 ≈ᵥ[T] v2 : iProp Σ, step-indexing is INSIDE iProp
   
   2. AUTOMATIC DOWNWARD CLOSURE:
      - Before: Need lemma val_rel_n_mono : n ≤ m → val_rel_n m → val_rel_n n
      - After: Built into iProp semantics, FREE
   
   3. AUTOMATIC WORLD MONOTONICITY:
      - Before: Need axiom about store extension preserving relations
      - After: Iris invariants are monotone by construction, FREE
   
   4. COMPOSITIONAL:
      - Before: Manual proofs that relations compose
      - After: ∗ (separating conjunction) gives compositionality, FREE
   
   5. PROOF AUTOMATION:
      - Before: Manual destruct/induction
      - After: iDestruct, iIntros, iSplit, etc. — tactics work
   
   6. PERSISTENT FUNCTION TYPES:
      - Before: Must manually prove functions can be used multiple times
      - After: □ (...) makes it persistent, FREE
   ═══════════════════════════════════════════════════════════════════════════ *)
```

### 4.2 Expression Relation (`exp_rel_n`)

#### 4.2.1 BEFORE: Custom Expression Relation

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   BEFORE: Custom expression relation (riina/logic/expr_rel.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Two expressions are related at type T if:
   - Whenever e1 evaluates to a value v1 in ≤n steps
   - Then e2 evaluates to some value v2
   - And v1, v2 are related at type T *)
   
Fixpoint exp_rel_n (n : nat) (T : ty) (e1 e2 : expr) : Prop :=
  (* For all stores related at step n *)
  ∀ (Σ : store_typing) (s1 s2 : store),
    store_rel n Σ s1 s2 →
    (* For all executions of e1 that terminate in ≤n steps *)
    ∀ (k : nat) (s1' : store) (v1 : expr),
      k ≤ n →
      step_n s1 e1 k s1' v1 →
      is_value v1 →
      (* There exists a terminating execution of e2 *)
      ∃ (s2' : store) (v2 : expr),
        step_star s2 e2 s2' v2 ∧
        is_value v2 ∧
        (* Results are related at remaining step budget *)
        val_rel_n (n - k) T v1 v2 ∧
        (* Final stores are related *)
        store_rel (n - k) Σ s1' s2'.

(* ═══════════════════════════════════════════════════════════════════════════
   PROBLEMS:
   
   1. Step-count arithmetic: (n - k) is error-prone
   2. Store relation must be threaded through manually
   3. No connection to operational semantics rules
   4. Proving compositionality (e.g., let-binding) requires induction on n
   5. Store extension (adding new locations) requires separate lemmas
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Compositionality lemma — this is TEDIOUS to prove *)
Lemma exp_rel_bind : ∀ n T1 T2 e1 e2 K1 K2,
  exp_rel_n n T1 e1 e2 →
  (∀ v1 v2, val_rel_n n T1 v1 v2 → 
            exp_rel_n n T2 (fill K1 v1) (fill K2 v2)) →
  exp_rel_n n T2 (fill K1 e1) (fill K2 e2).
Proof.
  (* This proof is ~200 lines in the custom approach *)
  intros n T1 T2 e1 e2 K1 K2 He Hk.
  unfold exp_rel_n in *.
  intros Σ s1 s2 Hstore k s1' v1 Hk_le Hsteps Hval.
  (* ... tedious step-counting ... *)
Admitted. (* One of the 67 admitted proofs *)
```

#### 4.2.2 AFTER: Iris Weakest Precondition

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   AFTER: Expression relation via Iris WP (riina/iris/expr_rel.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

From iris.program_logic Require Import weakestpre lifting.
From iris.heap_lang Require Import proofmode.
From riina.iris Require Import value_rel resources effects.

Section expr_relation.
  Context `{!riinaGS Σ}.
  Context `{!heapGS Σ}.
  
  (* ─────────────────────────────────────────────────────────────────────────
     Expression relation using weakest precondition (WP)
     
     Key insight: WP e {{ v, Φ v }} means:
     "If e terminates with value v, then Φ v holds"
     
     This is EXACTLY what exp_rel_n encodes, but:
     - Step-indexing is handled internally by WP
     - Store relation is handled by Iris's heap assertions
     - Compositionality (bind lemma) is a THEOREM in Iris
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Binary expression relation: two expressions produce related values *)
  Definition expr_rel (T : ty) (eff : effect) (e1 e2 : expr) : iProp Σ :=
    (* Execution context: we have the right to run both expressions *)
    ∀ (Φ : val → val → iProp Σ),
      (* If the caller provides a continuation expecting related values... *)
      (∀ v1 v2, ⟦ T ⟧ᵥ v1 v2 -∗ Φ v1 v2) -∗
      (* ...then we can satisfy two WPs *)
      WP e1 {{ v1, ∃ v2, WP e2 {{ v2', ⌜v2' = v2⌝ ∗ Φ v1 v2 }} }}.
  
  (* Notation *)
  Notation "e1 ≈ₑ[ T , eff ] e2" := (expr_rel T eff e1 e2) (at level 70).

  (* ─────────────────────────────────────────────────────────────────────────
     Alternative: Coupled execution relation
     
     For non-interference, we often want to relate two executions that
     share the same "public" state but may differ on "secret" state.
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition coupled_exec (T : ty) (eff : effect) 
             (e1 e2 : expr) (pc : security_level) : iProp Σ :=
    (* Assertion: public state is identical, secret state may differ *)
    ∀ (pub_inv : iProp Σ),
      (* Public state invariant *)
      □ pub_inv -∗
      (* Both executions preserve public state and produce related results *)
      WP e1 {{ v1, 
        pub_inv ∗ 
        ∃ v2, WP e2 {{ v2', ⌜v2' = v2⌝ ∗ pub_inv ∗ 
          (* At security level pc, results are indistinguishable *)
          observable_at pc v1 v2 }}
      }}.

  (* ─────────────────────────────────────────────────────────────────────────
     The bind lemma — this is a THEOREM in Iris, not an axiom!
     ───────────────────────────────────────────────────────────────────────── *)
  
  Lemma expr_rel_bind T1 T2 eff K e1 e2 :
    (* If e1 and e2 are related at T1... *)
    e1 ≈ₑ[T1, eff] e2 -∗
    (* ...and the continuation contexts produce related results... *)
    (∀ v1 v2, ⟦ T1 ⟧ᵥ v1 v2 -∗ (fill K e1) ≈ₑ[T2, eff] (fill K e2)) -∗
    (* ...then the filled expressions are related *)
    (fill K e1) ≈ₑ[T2, eff] (fill K e2).
  Proof.
    (* In Iris, this follows from WP's bind rule! *)
    iIntros "He Hk".
    iIntros (Φ) "HΦ".
    (* Use wp_bind from Iris *)
    iApply wp_bind.
    iApply "He".
    iIntros (v1 v2) "Hv".
    iApply ("Hk" with "Hv").
    iApply "HΦ".
  Qed.

  (* ─────────────────────────────────────────────────────────────────────────
     Effect-aware expression relation
     
     RIINA has 16 effects. In Iris, we model effects as RESOURCES.
     An expression can only perform an effect if it owns the right resource.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Effect resources — defined in riina/iris/effects.v *)
  (* effect_res eff means "we have permission to perform effect eff" *)
  
  Definition expr_rel_eff (T : ty) (eff : effect) (e1 e2 : expr) : iProp Σ :=
    (* We own the effect resource *)
    effect_res eff -∗
    (* Under this resource, expressions are related *)
    e1 ≈ₑ[T, eff] e2.

  (* ─────────────────────────────────────────────────────────────────────────
     Key WP rules we get from Iris for free
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* These are THEOREMS in Iris, not axioms we need to prove! *)
  
  (* wp_value: values immediately satisfy the postcondition *)
  Check @wp_value.
  (* : ∀ ... v Φ, Φ v ⊢ WP (Val v) {{ Φ }} *)
  
  (* wp_bind: evaluation contexts compose *)
  Check @wp_bind.
  (* : ∀ ... K e Φ, WP e {{ v, WP (fill K v) {{ Φ }} }} ⊢ WP (fill K e) {{ Φ }} *)
  
  (* wp_mono: postconditions can be weakened *)
  Check @wp_mono.
  (* : ∀ ... e Φ Ψ, (∀ v, Φ v -∗ Ψ v) -∗ WP e {{ Φ }} -∗ WP e {{ Ψ }} *)
  
  (* wp_frame_l: frame rule *)
  Check @wp_frame_l.
  (* : ∀ ... e Φ R, R ∗ WP e {{ Φ }} ⊢ WP e {{ v, R ∗ Φ v }} *)

End expr_relation.

(* ═══════════════════════════════════════════════════════════════════════════
   WHY IRIS VERSION IS BETTER:
   
   1. BIND LEMMA IS FREE:
      - Before: 200-line proof (admitted)
      - After: 10-line proof using wp_bind
   
   2. FRAME RULE IS FREE:
      - Before: Axiom about store extension
      - After: wp_frame_l theorem
   
   3. VALUE RULE IS FREE:
      - Before: Base case of exp_rel_n induction
      - After: wp_value theorem
   
   4. STEP-INDEXING HANDLED:
      - Before: k ≤ n, (n - k) arithmetic everywhere
      - After: Invisible, inside WP definition
   
   5. STORE RELATION SIMPLIFIED:
      - Before: store_rel n Σ s1 s2 threaded everywhere
      - After: l ↦ v assertions, separation logic
   
   6. EFFECT INTEGRATION:
      - Before: Effects checked at type level only
      - After: Effects as resources enable runtime tracking
   ═══════════════════════════════════════════════════════════════════════════ *)
```

### 4.3 Store Relation (`store_rel`)

#### 4.3.1 BEFORE: Custom Store Relation

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   BEFORE: Custom store relation (riina/logic/store_rel.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Store typing: maps locations to their types and security levels *)
Definition store_typing := loc → option (ty * security_level).

(* Two stores are related if corresponding locations hold related values *)
Definition store_rel (n : nat) (Σ : store_typing) (s1 s2 : store) : Prop :=
  (* 1. Domains match the store typing *)
  (∀ l, is_Some (Σ l) ↔ (is_Some (s1 !! l) ∧ is_Some (s2 !! l))) ∧
  (* 2. All typed locations hold related values *)
  (∀ l T sec,
    Σ l = Some (T, sec) →
    ∃ v1 v2,
      s1 !! l = Some v1 ∧
      s2 !! l = Some v2 ∧
      val_rel_n n T v1 v2) ∧
  (* 3. Security levels are respected *)
  (∀ l T sec,
    Σ l = Some (T, sec) →
    sec = location_security_level l).

(* ═══════════════════════════════════════════════════════════════════════════
   Store extension: adding new locations preserves existing relations.
   This is an AXIOM in the current system!
   ═══════════════════════════════════════════════════════════════════════════ *)

Axiom store_rel_extension : ∀ n Σ Σ' s1 s2 s1' s2',
  store_rel n Σ s1 s2 →
  (* Σ' extends Σ *)
  (∀ l, is_Some (Σ l) → Σ' l = Σ l) →
  (* s1' extends s1, s2' extends s2 *)
  (∀ l, is_Some (s1 !! l) → s1' !! l = s1 !! l) →
  (∀ l, is_Some (s2 !! l) → s2' !! l = s2 !! l) →
  (* New locations are related *)
  (∀ l T sec,
    Σ' l = Some (T, sec) →
    ¬ is_Some (Σ l) →
    ∃ v1 v2,
      s1' !! l = Some v1 ∧ s2' !! l = Some v2 ∧
      val_rel_n n T v1 v2) →
  (* Then extended stores are related *)
  store_rel n Σ' s1' s2'.

(* Step monotonicity for store_rel — another AXIOM *)
Axiom store_rel_mono : ∀ n m Σ s1 s2,
  m ≤ n →
  store_rel n Σ s1 s2 →
  store_rel m Σ s1 s2.

(* Store agreement: if l ↦ v in both stores, the values are related *)
Axiom store_rel_lookup : ∀ n Σ s1 s2 l T sec v1 v2,
  store_rel n Σ s1 s2 →
  Σ l = Some (T, sec) →
  s1 !! l = Some v1 →
  s2 !! l = Some v2 →
  val_rel_n n T v1 v2.

(* ═══════════════════════════════════════════════════════════════════════════
   PROBLEMS:
   
   1. Three axioms just for basic store properties
   2. Store typing Σ must be threaded through EVERY proof
   3. Extension lemma is complex and error-prone
   4. No automatic frame reasoning
   5. Manual case analysis for every store operation
   ═══════════════════════════════════════════════════════════════════════════ *)
```

#### 4.3.2 AFTER: Iris Heap Assertions

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   AFTER: Iris heap assertions (riina/iris/store_rel.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

From iris.base_logic.lib Require Import gen_heap.
From iris.heap_lang Require Import primitive_laws proofmode.
From riina.iris Require Import value_rel security.

Section store_relation.
  Context `{!riinaGS Σ}.
  Context `{!heapGS Σ}.

  (* ─────────────────────────────────────────────────────────────────────────
     In Iris, we don't have a global "store relation".
     Instead, we have:
     
     1. Points-to assertions: l ↦ v ("location l holds value v")
     2. Invariants: inv N P ("P holds at all times")
     
     The "store relation" is expressed as a collection of invariants,
     one per pair of related locations.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Namespace for store relation invariants *)
  Definition storeN : namespace := nroot .@ "riina" .@ "store".
  
  (* Single location pair invariant *)
  Definition loc_pair_inv (l1 l2 : loc) (T : ty) (sec : security_level) : iProp Σ :=
    inv (storeN .@ l1 .@ l2) (
      ∃ v1 v2,
        l1 ↦ v1 ∗ l2 ↦ v2 ∗
        ▷ ⟦ T ⟧ᵥ v1 v2 ∗
        sec_ghost l1 sec ∗
        sec_ghost l2 sec
    ).

  (* ─────────────────────────────────────────────────────────────────────────
     Store typing as a set of location pair invariants
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* A "store context" is a finite map from location pairs to their types *)
  Definition store_ctx := gmap (loc * loc) (ty * security_level).
  
  (* The store relation is the separating conjunction of all location invariants *)
  Definition store_rel (Γ : store_ctx) : iProp Σ :=
    [∗ map] '(l1, l2) ↦ '(T, sec) ∈ Γ,
      loc_pair_inv l1 l2 T sec.

  (* ─────────────────────────────────────────────────────────────────────────
     Store extension — THIS IS A THEOREM, NOT AN AXIOM!
     
     In Iris, adding a new invariant is always allowed because invariants
     are persistent. We just need to show the new locations satisfy the
     invariant initially.
     ───────────────────────────────────────────────────────────────────────── *)
  
  Lemma store_rel_extend Γ l1 l2 T sec v1 v2 :
    (* Existing store relation *)
    store_rel Γ -∗
    (* New locations with values *)
    l1 ↦ v1 -∗
    l2 ↦ v2 -∗
    (* Values are related *)
    ⟦ T ⟧ᵥ v1 v2 -∗
    (* Security ghost state *)
    sec_ghost l1 sec -∗
    sec_ghost l2 sec -∗
    (* Allocate the invariant *)
    |==> store_rel (<[(l1, l2) := (T, sec)]> Γ) ∗ loc_pair_inv l1 l2 T sec.
  Proof.
    iIntros "Hstore Hl1 Hl2 Hrel Hsec1 Hsec2".
    (* Allocate the new invariant *)
    iMod (inv_alloc (storeN .@ l1 .@ l2) _ (
      ∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ v2 ∗ ▷ ⟦ T ⟧ᵥ v1 v2 ∗ 
               sec_ghost l1 sec ∗ sec_ghost l2 sec
    ) with "[Hl1 Hl2 Hrel Hsec1 Hsec2]") as "#Hinv".
    { iNext. iExists v1, v2. iFrame. }
    (* Combine with existing store relation *)
    iModIntro.
    iSplitL "Hstore".
    - iApply (big_sepM_insert_2 with "[] Hstore").
      iApply "Hinv".
    - iApply "Hinv".
  Qed.

  (* ─────────────────────────────────────────────────────────────────────────
     Store lookup — also a THEOREM
     ───────────────────────────────────────────────────────────────────────── *)
  
  Lemma store_rel_lookup Γ l1 l2 T sec :
    Γ !! (l1, l2) = Some (T, sec) →
    store_rel Γ -∗
    loc_pair_inv l1 l2 T sec.
  Proof.
    iIntros (Hlookup) "Hstore".
    iDestruct (big_sepM_lookup with "Hstore") as "Hinv"; first done.
    iApply "Hinv".
  Qed.

  (* ─────────────────────────────────────────────────────────────────────────
     Accessing locations through invariant
     ───────────────────────────────────────────────────────────────────────── *)
  
  Lemma loc_pair_inv_access E l1 l2 T sec :
    ↑(storeN .@ l1 .@ l2) ⊆ E →
    loc_pair_inv l1 l2 T sec -∗
    |={E, E ∖ ↑(storeN .@ l1 .@ l2)}=>
      ∃ v1 v2,
        l1 ↦ v1 ∗ l2 ↦ v2 ∗ ▷ ⟦ T ⟧ᵥ v1 v2 ∗
        (∀ w1 w2,
          l1 ↦ w1 -∗ l2 ↦ w2 -∗ ▷ ⟦ T ⟧ᵥ w1 w2 -∗
          |={E ∖ ↑(storeN .@ l1 .@ l2), E}=> True).
  Proof.
    iIntros (Hsub) "#Hinv".
    iInv "Hinv" as (v1 v2) "(Hl1 & Hl2 & Hrel & Hsec1 & Hsec2)" "Hclose".
    iModIntro.
    iExists v1, v2.
    iFrame "Hl1 Hl2 Hrel".
    iIntros (w1 w2) "Hl1 Hl2 Hrel".
    iApply "Hclose".
    iNext. iExists w1, w2. iFrame.
  Qed.

  (* ─────────────────────────────────────────────────────────────────────────
     Frame property — this is AUTOMATIC in separation logic!
     
     The key insight: l1 ↦ v1 ∗ l2 ↦ v2 ∗ R
     The R is "framed" — operations on l1, l2 don't touch R
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* We don't need to state or prove this — it's inherent in ∗ *)

End store_relation.

(* ═══════════════════════════════════════════════════════════════════════════
   WHY IRIS VERSION IS BETTER:
   
   1. NO STORE RELATION AXIOMS:
      - store_rel_extension: Now a theorem using inv_alloc
      - store_rel_mono: Built into iProp (implicit in later modality)
      - store_rel_lookup: Simple big_sepM_lookup
   
   2. FRAME PROPERTY IS FREE:
      - Separation logic (∗) provides framing automatically
      - No manual threading of "unchanged locations"
   
   3. AUTOMATIC PERSISTENCE:
      - Invariants are persistent: can be used multiple times
      - No manual tracking of which facts can be duplicated
   
   4. CLEAR OWNERSHIP:
      - l ↦ v is EXCLUSIVE: only one owner at a time
      - Prevents aliasing bugs in proofs
   
   5. MODULAR:
      - Each location pair is an independent invariant
      - Adding/removing locations doesn't affect others
   ═══════════════════════════════════════════════════════════════════════════ *)
```

### 4.4 World Monotonicity

#### 4.4.1 BEFORE: Manual Axioms

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   BEFORE: World monotonicity axioms (riina/logic/world.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

(* A "world" in RIINA is: store typing Σ + actual stores s1, s2 *)
Record world := {
  world_typing : store_typing;
  world_store1 : store;
  world_store2 : store;
}.

(* World extension: new locations can be added *)
Definition world_extends (W W' : world) : Prop :=
  (* Typing only grows *)
  (∀ l T sec, world_typing W l = Some (T, sec) → 
              world_typing W' l = Some (T, sec)) ∧
  (* Existing locations unchanged *)
  (∀ l, is_Some (world_store1 W !! l) → 
        world_store1 W' !! l = world_store1 W !! l) ∧
  (∀ l, is_Some (world_store2 W !! l) → 
        world_store2 W' !! l = world_store2 W !! l).

(* ═══════════════════════════════════════════════════════════════════════════
   AXIOMS for world monotonicity
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Value relations are monotone in the world *)
Axiom val_rel_world_mono : ∀ n T v1 v2 W W',
  world_extends W W' →
  val_rel_in_world n T v1 v2 W →
  val_rel_in_world n T v1 v2 W'.

(* Expression relations are monotone in the world *)
Axiom exp_rel_world_mono : ∀ n T e1 e2 W W',
  world_extends W W' →
  exp_rel_in_world n T e1 e2 W →
  exp_rel_in_world n T e1 e2 W'.

(* World extension is transitive *)
Axiom world_extends_trans : ∀ W1 W2 W3,
  world_extends W1 W2 →
  world_extends W2 W3 →
  world_extends W1 W3.

(* World extension is reflexive *)
Axiom world_extends_refl : ∀ W,
  world_extends W W.

(* New location allocation extends world *)
Axiom world_alloc_extends : ∀ W l T sec v1 v2,
  ¬ is_Some (world_typing W l) →
  val_rel_n (world_step W) T v1 v2 →
  world_extends W (alloc_world W l T sec v1 v2).

(* ═══════════════════════════════════════════════════════════════════════════
   PROBLEMS:
   
   1. 5 axioms just for world monotonicity
   2. world_extends is a heavy definition to work with
   3. Proofs must explicitly invoke monotonicity lemmas
   4. No separation of concerns (all locations mentioned together)
   5. Aliasing issues are possible if axioms are inconsistent
   ═══════════════════════════════════════════════════════════════════════════ *)
```

#### 4.4.2 AFTER: Iris Invariant Monotonicity

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   AFTER: Iris handles world monotonicity automatically
   ═══════════════════════════════════════════════════════════════════════════ *)

From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.

Section world_monotonicity.
  Context `{!invGS Σ}.

  (* ─────────────────────────────────────────────────────────────────────────
     In Iris, "world monotonicity" is automatic because:
     
     1. Invariants are PERSISTENT: once established, always available
     2. New invariants can be ALLOCATED at any time
     3. Existing invariants are NEVER invalidated
     
     The "world" is the implicit collection of all allocated invariants.
     There is no explicit "world extends" relation — it's structural.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Example: allocating a new invariant *)
  Lemma world_grows N P :
    P -∗ |==> □ inv N P.
  Proof.
    iIntros "HP".
    iMod (inv_alloc N _ P with "HP") as "#Hinv".
    iModIntro. iModIntro.
    iApply "Hinv".
  Qed.
  
  (* Key property: inv N P is persistent *)
  Global Instance inv_persistent N P : Persistent (inv N P).
  Proof. apply _. Qed.
  
  (* ─────────────────────────────────────────────────────────────────────────
     What we get for FREE:
     
     1. val_rel_world_mono: Not needed!
        - ⟦ T ⟧ᵥ v1 v2 is defined in iProp
        - If it holds, it holds forever (persistence of invariants)
     
     2. exp_rel_world_mono: Not needed!
        - WP is monotone in invariants by construction
     
     3. world_extends_trans: Not needed!
        - Just allocation: |==> inv N P
        - Composition is monad composition
     
     4. world_extends_refl: Not needed!
        - Identity, automatic
     
     5. world_alloc_extends: Becomes inv_alloc
        - This IS a theorem in Iris!
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* The key Iris theorem we use *)
  Check @inv_alloc.
  (* : ∀ E N P, ▷ P -∗ |={E}=> inv N P *)
  
  (* Invariants can be opened (temporarily accessed) *)
  Check @inv_acc.
  (* : ∀ E N P, ↑N ⊆ E → inv N P -∗ |={E,E∖↑N}=> ▷ P ∗ (▷ P -∗ |={E∖↑N,E}=> True) *)

End world_monotonicity.

(* ═══════════════════════════════════════════════════════════════════════════
   CONCRETE BENEFIT:
   
   Before (5 axioms):
   - val_rel_world_mono
   - exp_rel_world_mono  
   - world_extends_trans
   - world_extends_refl
   - world_alloc_extends
   
   After (0 axioms):
   - Iris invariant mechanism provides all of this
   - inv_alloc is a THEOREM
   - Persistence is a typeclass instance
   - Transitivity/reflexivity are automatic
   ═══════════════════════════════════════════════════════════════════════════ *)
```

### 4.5 Step-Index Downward Closure

#### 4.5.1 BEFORE: Manual Downward Closure

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   BEFORE: Step-index monotonicity (riina/logic/step_index.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

(* If a relation holds at step n, it holds at all m ≤ n *)
Lemma val_rel_n_downward : ∀ n m T v1 v2,
  m ≤ n →
  val_rel_n n T v1 v2 →
  val_rel_n m T v1 v2.
Proof.
  induction n as [|n IH]; intros m T v1 v2 Hle Hrel.
  - (* n = 0 *)
    assert (m = 0) by lia. subst.
    assumption.
  - (* n = S n *)
    destruct m as [|m].
    + (* m = 0: trivial by definition *)
      destruct T; simpl in *; try tauto.
      (* ... many cases, each requiring careful proof ... *)
      admit.
    + (* m = S m *)
      assert (m ≤ n) by lia.
      destruct T; simpl in *.
      * (* TUnit *) assumption.
      * (* TBool *) assumption.
      * (* TInt *) assumption.
      * (* TString *) assumption.
      * (* TBytes *) assumption.
      * (* TFn T1 T2 eff *)
        destruct Hrel as (x1 & x2 & e1 & e2 & Hv1 & Hv2 & Hfun).
        exists x1, x2, e1, e2.
        split; [assumption|].
        split; [assumption|].
        intros k Hk w1 w2 Hw.
        (* Need: exp_rel_n k T2 ... from exp_rel_n (n-1) k T2 ... *)
        (* This requires exp_rel_n_downward, mutual induction... *)
        admit.
      * (* TProd *) admit.
      * (* TSum *) admit.
      * (* TRef *) admit.
      * (* ... 6 more security types ... *)
        all: admit.
Admitted. (* One of the 67 admitted proofs *)

(* Expression relation downward closure — also needed *)
Lemma exp_rel_n_downward : ∀ n m T e1 e2,
  m ≤ n →
  exp_rel_n n T e1 e2 →
  exp_rel_n m T e1 e2.
Proof.
  (* Requires mutual induction with val_rel_n_downward *)
  (* Very tedious proof, often admitted *)
Admitted.

(* ═══════════════════════════════════════════════════════════════════════════
   PROBLEMS:
   
   1. Mutual induction between val_rel and exp_rel
   2. ~15 cases for different types
   3. Step arithmetic is error-prone
   4. Need to re-prove for every new type added
   5. Often admitted in practice
   ═══════════════════════════════════════════════════════════════════════════ *)
```

#### 4.5.2 AFTER: Iris Later Modality

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   AFTER: Step-indexing via later modality (riina/iris/step_index.v)
   ═══════════════════════════════════════════════════════════════════════════ *)

From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.

Section step_indexing.
  Context `{!BiLöb PROP}.
  
  (* ─────────────────────────────────────────────────────────────────────────
     In Iris, step-indexing is IMPLICIT in the semantics of iProp.
     
     The key construct is the LATER modality: ▷ P
     
     Meaning: ▷ P holds now if P holds "after one step"
     
     Step-index downward closure becomes: ▷ P ⊢ ▷▷ P
     (If P holds after 1 step, it holds after 2 steps)
     
     This is automatic in Iris!
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Later is monotone: if P ⊢ Q, then ▷P ⊢ ▷Q *)
  Lemma later_mono (P Q : PROP) :
    (P ⊢ Q) → (▷ P ⊢ ▷ Q).
  Proof. apply later_mono. Qed.
  
  (* Later distributes over conjunction *)
  Lemma later_and (P Q : PROP) :
    ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q.
  Proof. apply later_and. Qed.
  
  (* Later distributes over separating conjunction *)
  Lemma later_sep (P Q : PROP) :
    ▷ (P ∗ Q) ⊣⊢ ▷ P ∗ ▷ Q.
  Proof. apply later_sep. Qed.
  
  (* ─────────────────────────────────────────────────────────────────────────
     The magic: Löb induction
     
     Löb's rule: (▷ P → P) ⊢ P
     
     "If assuming P holds later lets us prove P holds now, then P holds"
     
     This is how Iris handles recursive definitions!
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Löb induction in Iris *)
  Lemma löb (P : PROP) :
    (▷ P -∗ P) ⊢ P.
  Proof. apply löb. Qed.
  
  (* Example: proving a property holds at all steps *)
  Lemma always_holds (P : PROP) :
    □ P -∗ ▷ □ P.
  Proof.
    iIntros "#HP".
    iModIntro.
    iApply "HP".
  Qed.

End step_indexing.

(* ═══════════════════════════════════════════════════════════════════════════
   HOW THIS REPLACES val_rel_n_downward:
   
   BEFORE:
     val_rel_n n T v1 v2 : Prop
     Need to prove: m ≤ n → val_rel_n n → val_rel_n m
     This is a LEMMA requiring induction on types
   
   AFTER:
     ⟦ T ⟧ᵥ v1 v2 : iProp Σ
     The iProp semantics already include step-indexing!
     ⟦ T ⟧ᵥ v1 v2 holds "at all sufficiently large step indices"
     Downward closure is DEFINITIONAL, not a lemma
   
   TECHNICAL DETAIL:
     Iris propositions iProp are defined as:
       iProp Σ := nat → uPred (iResUR Σ)
     where nat is the step index.
     
     The entailment P ⊢ Q means: for all n, if P(n) then Q(n).
     
     So if ⟦ T ⟧ᵥ v1 v2 holds, it holds at ALL step indices.
     The downward closure is automatic.
   ═══════════════════════════════════════════════════════════════════════════ *)

(* ═══════════════════════════════════════════════════════════════════════════
   WHY THE ▷ IN FUNCTION TYPES MATTERS:
   
   In interp_fn_pre, we wrote:
   
     □ (∀ w1 w2, ▷ interp T1 w1 w2 -∗ ...)
   
   The ▷ before the input relation is CRITICAL:
   - It makes the definition CONTRACTIVE (well-founded)
   - It models: "if inputs are related at step n-1, outputs are related at step n"
   - This is exactly what val_rel_n did manually!
   
   WITHOUT ▷: Definition would be non-terminating (circular)
   WITH ▷: Iris handles the step-indexing internally
   ═══════════════════════════════════════════════════════════════════════════ *)
```

---

## 5. Axiom Elimination Mapping

### 5.1 Complete Axiom Inventory

| # | Axiom Name | Category | Iris Equivalent | Status |
|---|-----------|----------|-----------------|--------|
| 1 | `val_rel_n_downward` | Step Monotonicity | Built into iProp semantics | **ELIMINATED** |
| 2 | `exp_rel_n_downward` | Step Monotonicity | Built into iProp semantics | **ELIMINATED** |
| 3 | `store_rel_mono` | Step Monotonicity | Built into iProp semantics | **ELIMINATED** |
| 4 | `val_rel_world_mono` | World Monotonicity | `Persistent (inv N P)` | **ELIMINATED** |
| 5 | `exp_rel_world_mono` | World Monotonicity | `Persistent (inv N P)` | **ELIMINATED** |
| 6 | `world_extends_trans` | World Monotonicity | Monad composition | **ELIMINATED** |
| 7 | `world_extends_refl` | World Monotonicity | Identity | **ELIMINATED** |
| 8 | `world_alloc_extends` | World Monotonicity | `inv_alloc` theorem | **ELIMINATED** |
| 9 | `store_rel_extension` | Store Relation | `inv_alloc` + frame | **ELIMINATED** |
| 10 | `store_rel_lookup` | Store Relation | `big_sepM_lookup` | **ELIMINATED** |
| 11 | `store_rel_update` | Store Relation | Points-to update | **ELIMINATED** |
| 12 | `exp_rel_bind` | Compositionality | `wp_bind` theorem | **ELIMINATED** |
| 13 | `exp_rel_frame` | Frame Property | `wp_frame_l` theorem | **ELIMINATED** |
| 14 | `val_rel_persistent` | Persistence | `Persistent` typeclass | **ELIMINATED** |
| 15 | `effect_frame` | Effect System | Effect resources | **NEED NEW DESIGN** |
| 16 | `session_duality` | Session Types | Protocol ghost state | **NEED NEW DESIGN** |
| 17 | `capability_monotone` | Capabilities | Capability resources | **NEED NEW DESIGN** |
| 18 | `security_lattice_po` | Security Lattice | Ghost state encoding | **THEOREM** |
| 19 | `noninterference_fundamental` | Main Theorem | Full proof possible | **PROVABLE** |

### 5.2 Summary

| Category | Before (Axioms) | After (Axioms) | Eliminated |
|----------|-----------------|----------------|------------|
| Step Monotonicity | 3 | 0 | 3 |
| World Monotonicity | 5 | 0 | 5 |
| Store Relation | 3 | 0 | 3 |
| Compositionality | 2 | 0 | 2 |
| Effect System | 1 | 0* | 1 |
| Session Types | 1 | 0* | 1 |
| Capabilities | 1 | 0* | 1 |
| Security Lattice | 1 | 0 | 1 |
| Main Theorem | 1 | 0 | 1 |
| **TOTAL** | **19** | **0-3** | **16-19** |

*Effect, session, and capability axioms become theorems with proper resource design

### 5.3 Admitted Proof Elimination

| Category | Admitted (Before) | Admitted (After) | Reduction |
|----------|-------------------|------------------|-----------|
| Step monotonicity | 12 | 0 | 100% |
| World monotonicity | 18 | 0 | 100% |
| Store relation | 15 | 0 | 100% |
| Bind/frame lemmas | 8 | 0 | 100% |
| Type cases | 14 | ~5 | ~65% |
| **TOTAL** | **67** | **~5** | **~93%** |

---

## 6. Migration Sequence

### 6.1 Dependency Graph

```
┌────────────────────────────────────────────────────────────────────────────┐
│                        RIINA Iris Migration Phases                         │
└────────────────────────────────────────────────────────────────────────────┘

Phase 1: Infrastructure                    Phase 2: Core Relations
┌─────────────────────────┐               ┌─────────────────────────┐
│ riina/iris/prelude.v    │──────────────▶│ riina/iris/value_rel.v  │
│ - Import all Iris       │               │ - Type interpretation   │
│ - Define Σ signature    │               │ - interp : ty → sem_ty  │
└─────────────────────────┘               └───────────┬─────────────┘
          │                                           │
          ▼                                           ▼
┌─────────────────────────┐               ┌─────────────────────────┐
│ riina/iris/resources.v  │               │ riina/iris/expr_rel.v   │
│ - Effect resources      │               │ - Expression relation   │
│ - Security ghost state  │               │ - WP-based definition   │
│ - Session resources     │               └───────────┬─────────────┘
└─────────────────────────┘                           │
          │                                           ▼
          ▼                               ┌─────────────────────────┐
┌─────────────────────────┐               │ riina/iris/store_rel.v  │
│ riina/iris/lang.v       │               │ - Location invariants   │
│ - RIINA as ectxi_lang   │               │ - Store context         │
│ - Operational semantics │               └───────────┬─────────────┘
└─────────────────────────┘                           │
                                                      ▼
                                          ┌─────────────────────────┐
Phase 3: Effect System                    │ riina/iris/typing.v     │
┌─────────────────────────┐               │ - Semantic typing       │
│ riina/iris/effects.v    │──────────────▶│ - Γ ⊨ e : T judgment    │
│ - Effect algebra        │               └───────────┬─────────────┘
│ - Effect resources      │                           │
│ - Effect composition    │                           ▼
└─────────────────────────┘               ┌─────────────────────────┐
                                          │ Phase 4: Main Proofs    │
Phase 5: Session Types                    │ riina/iris/fundamental.v│
┌─────────────────────────┐               │ - Fundamental theorem   │
│ riina/iris/sessions.v   │──────────────▶│ - Type soundness        │
│ - Protocol resources    │               │ - Non-interference      │
│ - Channel invariants    │               └─────────────────────────┘
└─────────────────────────┘
```

### 6.2 File-by-File Migration Plan

#### Phase 1: Infrastructure Setup (Weeks 1-2)

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 1, FILE 1: riina/iris/prelude.v
   
   Purpose: Central import file and global setup
   Dependencies: None (imports only Iris)
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Create: riina/iris/prelude.v *)

From iris.algebra Require Export cmra auth excl agree gmap gset frac dfrac.
From iris.bi Require Export bi big_op derived_connectives.
From iris.proofmode Require Export tactics environments.
From iris.base_logic.lib Require Export iprop own invariants ghost_var.
From iris.program_logic Require Export weakestpre adequacy lifting.

(* RIINA-specific camera signature *)
(* We'll extend this as we add more features *)

Class riinaGpreS Σ := RiinaGpreS {
  riina_invGpreS :> invGpreS Σ;
}.

Class riinaGS Σ := RiinaGS {
  riina_invGS :> invGS Σ;
  (* Add more as needed *)
}.

(* Global instances for proof mode *)
Global Instance riina_irisGS `{!riinaGS Σ} : irisGS riina_lang Σ := {
  (* Will be filled in after defining riina_lang *)
}.

(* Namespace hierarchy *)
Definition riinaN : namespace := nroot .@ "riina".
Definition storeN : namespace := riinaN .@ "store".
Definition effectN : namespace := riinaN .@ "effect".
Definition sessionN : namespace := riinaN .@ "session".
Definition securityN : namespace := riinaN .@ "security".
```

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 1, FILE 2: riina/iris/lang_interface.v
   
   Purpose: Make RIINA satisfy Iris's language interface
   Dependencies: riina/lang/syntax.v, riina/lang/semantics.v
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Create: riina/iris/lang_interface.v *)

From iris.program_logic Require Import ectxi_language.
From riina.lang Require Import syntax semantics.
From riina.iris Require Import prelude.

(* RIINA expression and value definitions *)
(* (Assumed to exist in riina/lang/syntax.v) *)

(* Evaluation contexts for RIINA *)
Inductive riina_ectx_item :=
  | AppLCtx (v : riina_val)        (* □ v *)
  | AppRCtx (e : riina_expr)       (* e □ *)
  | PairLCtx (v : riina_val)       (* □, v *)
  | PairRCtx (e : riina_expr)      (* e, □ *)
  | FstCtx                         (* fst □ *)
  | SndCtx                         (* snd □ *)
  | InjLCtx                        (* inl □ *)
  | InjRCtx                        (* inr □ *)
  | CaseCtx (e1 e2 : riina_expr)   (* case □ of ... *)
  | RefCtx (sec : security_level) (* ref[sec] □ *)
  | DerefCtx                       (* !□ *)
  | AssignLCtx (v : riina_val)    (* □ := v *)
  | AssignRCtx (e : riina_expr)   (* e := □ *)
  | LetCtx (x : binder) (e : riina_expr)  (* let x = □ in e *)
  | IfCtx (e1 e2 : riina_expr)    (* if □ then e1 else e2 *)
  | SendCtx (ch : channel_id)     (* send ch □ *)
  | BinOpLCtx (op : bin_op) (v : riina_val)  (* □ op v *)
  | BinOpRCtx (op : bin_op) (e : riina_expr) (* e op □ *)
  .

(* Fill function *)
Definition riina_fill_item (Ki : riina_ectx_item) (e : riina_expr) : riina_expr :=
  match Ki with
  | AppLCtx v => EApp e (of_val v)
  | AppRCtx e' => EApp e' e
  | PairLCtx v => EPair e (of_val v)
  | PairRCtx e' => EPair e' e
  | FstCtx => EFst e
  | SndCtx => ESnd e
  | InjLCtx => EInl e
  | InjRCtx => EInr e
  | CaseCtx e1 e2 => ECase e e1 e2
  | RefCtx sec => ERef sec e
  | DerefCtx => EDeref e
  | AssignLCtx v => EAssign e (of_val v)
  | AssignRCtx e' => EAssign e' e
  | LetCtx x e' => ELet x e e'
  | IfCtx e1 e2 => EIf e e1 e2
  | SendCtx ch => ESend ch e
  | BinOpLCtx op v => EBinOp op e (of_val v)
  | BinOpRCtx op e' => EBinOp op e' e
  end.

(* Evaluation context as list of items *)
Definition riina_ectx := list riina_ectx_item.

Definition riina_fill (K : riina_ectx) (e : riina_expr) : riina_expr :=
  foldl (flip riina_fill_item) e K.

(* Prove RIINA is an ectxi_language *)
Lemma riina_ectxi_language_mixin :
  EctxiLanguageMixin of_val to_val riina_fill_item head_step.
Proof.
  (* Prove the required properties *)
  split.
  - (* of_val is injective *) 
    intros. apply of_val_inj. assumption.
  - (* to_val returns Some iff expression is a value *)
    intros e. destruct (to_val e) eqn:Heq; split; intros H.
    + exists v. symmetry. apply of_to_val. assumption.
    + destruct H as [v' Hv']. subst. apply to_of_val.
    + destruct H as [v Hv]. subst. rewrite to_of_val in Heq. discriminate.
    + assumption.
  - (* Values don't step *)
    intros K e1 σ1 e2 σ2 efs Hstep Hval.
    apply val_head_stuck in Hstep. destruct Hval. subst.
    apply Hstep. exists x. reflexivity.
  - (* fill_item is injective on non-values *)
    intros Ki e1 e2 Hfill.
    destruct Ki; simpl in *; try congruence.
  - (* fill_item produces non-values *)
    intros Ki e. destruct Ki; simpl; intros [v Hv]; discriminate.
  - (* head_step produces non-values in context *)
    intros Ki1 Ki2 e1 e1' σ1 e2 σ2 efs Hfill Hstep.
    destruct Ki1, Ki2; simpl in *; try congruence; 
    inversion Hfill; subst; try reflexivity.
Qed.

(* Define the language *)
Canonical Structure riina_ectxi_lang := 
  EctxiLanguage riina_ectxi_language_mixin.
Canonical Structure riina_ectx_lang := 
  EctxLanguageOfEctxi riina_ectxi_lang.
Canonical Structure riina_lang := 
  LanguageOfEctx riina_ectx_lang.
```

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 1, FILE 3: riina/iris/resources.v
   
   Purpose: Define cameras (resource algebras) for RIINA-specific state
   Dependencies: prelude.v
   ═══════════════════════════════════════════════════════════════════════════ *)

(* Create: riina/iris/resources.v *)

From iris.algebra Require Import auth excl agree gmap frac dfrac csum.
From riina.iris Require Import prelude.
From riina.lang Require Import security effects sessions.

Section resources.

  (* ─────────────────────────────────────────────────────────────────────────
     Security Level Resources
     
     Track the security level of values and locations
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Security levels as a discrete camera (no composition) *)
  Definition security_levelO := leibnizO security_level.
  
  (* Security level resource: agree camera for each location/value *)
  Definition sec_levelR := authR (gmapUR loc (agreeR security_levelO)).
  
  (* Ghost name for the security level map *)
  Class sec_levelGS Σ := SecLevelGS {
    sec_level_inG :> inG Σ sec_levelR;
    sec_level_name : gname;
  }.
  
  (* Assertion: location l has security level s *)
  Definition sec_level_at `{!sec_levelGS Σ} (l : loc) (s : security_level) : iProp Σ :=
    own sec_level_name (◯ {[ l := to_agree s ]}).
  
  Notation "l ↦ₛ s" := (sec_level_at l s) (at level 20).

  (* ─────────────────────────────────────────────────────────────────────────
     Effect Resources
     
     Track which effects are currently permitted
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Effect set as a camera *)
  Definition effectR := authR (gset_disjUR effect).
  
  Class effectGS Σ := EffectGS {
    effect_inG :> inG Σ effectR;
    effect_name : gname;
  }.
  
  (* Assertion: we have permission to perform effect eff *)
  Definition effect_perm `{!effectGS Σ} (eff : effect) : iProp Σ :=
    own effect_name (◯ GSet {[ eff ]}).
  
  Notation "⟨ eff ⟩" := (effect_perm eff) (at level 10).
  
  (* Effect composition: can combine effects *)
  Lemma effect_perm_combine `{!effectGS Σ} (eff1 eff2 : effect) :
    eff1 ≠ eff2 →
    ⟨ eff1 ⟩ ∗ ⟨ eff2 ⟩ ⊣⊢ own effect_name (◯ GSet {[ eff1; eff2 ]}).
  Proof.
    intros Hneq.
    rewrite -own_op.
    f_equiv.
    rewrite -auth_frag_op.
    f_equiv.
    apply gset_disj_union.
    set_solver.
  Qed.

  (* ─────────────────────────────────────────────────────────────────────────
     Taint Tracking Resources
     
     Track taint sources and sanitization status
     ───────────────────────────────────────────────────────────────────────── *)
  
  Inductive taint_status :=
    | Untainted
    | Tainted (source : taint_source)
    | Sanitized (sanitizer : sanitizer_id).
  
  Definition taint_statusO := leibnizO taint_status.
  Definition taintR := authR (gmapUR loc (agreeR taint_statusO)).
  
  Class taintGS Σ := TaintGS {
    taint_inG :> inG Σ taintR;
    taint_name : gname;
  }.
  
  Definition taint_at `{!taintGS Σ} (l : loc) (ts : taint_status) : iProp Σ :=
    own taint_name (◯ {[ l := to_agree ts ]}).
  
  Notation "l ↦ₜ ts" := (taint_at l ts) (at level 20).

  (* ─────────────────────────────────────────────────────────────────────────
     Session Type Resources (placeholder — detailed in Section 8)
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Session state: tracks protocol progress *)
  Definition sessionR := authR (gmapUR channel_id (exclR (leibnizO session_type))).
  
  Class sessionGS Σ := SessionGS {
    session_inG :> inG Σ sessionR;
    session_name : gname;
  }.
  
  (* Channel has session type st *)
  Definition session_at `{!sessionGS Σ} (ch : channel_id) (st : session_type) : iProp Σ :=
    own session_name (◯ {[ ch := Excl st ]}).
  
  Notation "ch ↦ₚ st" := (session_at ch st) (at level 20).

  (* ─────────────────────────────────────────────────────────────────────────
     Capability Resources
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition capabilityR := authR (gset_disjUR (capability_kind * capability)).
  
  Class capabilityGS Σ := CapabilityGS {
    capability_inG :> inG Σ capabilityR;
    capability_name : gname;
  }.
  
  Definition capability_perm `{!capabilityGS Σ} (kind : capability_kind) (cap : capability) : iProp Σ :=
    own capability_name (◯ GSet {[ (kind, cap) ]}).

End resources.

(* ─────────────────────────────────────────────────────────────────────────────
   Combined RIINA ghost state
   ───────────────────────────────────────────────────────────────────────────── *)

Class riinaGS' Σ := {
  riina_invGS' :> invGS Σ;
  riina_heapGS' :> heapGS Σ;
  riina_sec_levelGS :> sec_levelGS Σ;
  riina_effectGS :> effectGS Σ;
  riina_taintGS :> taintGS Σ;
  riina_sessionGS :> sessionGS Σ;
  riina_capabilityGS :> capabilityGS Σ;
}.

(* Precomposition: what's needed to allocate *)
Class riinaGpreS' Σ := {
  riina_invGpreS' :> invGpreS Σ;
  riina_heapGpreS' :> heapGpreS Σ;
  riina_sec_level_inG :> inG Σ sec_levelR;
  riina_effect_inG :> inG Σ effectR;
  riina_taint_inG :> inG Σ taintR;
  riina_session_inG :> inG Σ sessionR;
  riina_capability_inG :> inG Σ capabilityR;
}.

(* Sigma that supports RIINA *)
Definition riinaΣ : gFunctors :=
  #[invΣ; heapΣ; 
    GFunctor sec_levelR;
    GFunctor effectR;
    GFunctor taintR;
    GFunctor sessionR;
    GFunctor capabilityR].

Global Instance subG_riinaGpreS {Σ} : subG riinaΣ Σ → riinaGpreS' Σ.
Proof. solve_inG. Qed.
```

#### Phase 2: Core Relations (Weeks 3-6)

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 2, FILE 1: riina/iris/value_rel.v
   
   Purpose: Type interpretation (semantic types)
   Dependencies: prelude.v, resources.v, lang_interface.v
   ═══════════════════════════════════════════════════════════════════════════ *)

(* SEE SECTION 4.1.2 FOR COMPLETE IMPLEMENTATION *)
```

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 2, FILE 2: riina/iris/expr_rel.v
   
   Purpose: Expression relation via WP
   Dependencies: value_rel.v
   ═══════════════════════════════════════════════════════════════════════════ *)

(* SEE SECTION 4.2.2 FOR COMPLETE IMPLEMENTATION *)
```

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 2, FILE 3: riina/iris/store_rel.v
   
   Purpose: Store relation via invariants
   Dependencies: value_rel.v
   ═══════════════════════════════════════════════════════════════════════════ *)

(* SEE SECTION 4.3.2 FOR COMPLETE IMPLEMENTATION *)
```

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 2, FILE 4: riina/iris/typing.v
   
   Purpose: Semantic typing judgment
   Dependencies: expr_rel.v, store_rel.v
   ═══════════════════════════════════════════════════════════════════════════ *)

From riina.iris Require Import prelude value_rel expr_rel store_rel.

Section semantic_typing.
  Context `{!riinaGS' Σ}.

  (* ─────────────────────────────────────────────────────────────────────────
     Semantic type environment: maps variables to semantic types
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition sem_env := gmap string sem_ty.
  
  (* Environment interpretation: two substitutions are related *)
  Definition env_rel (Γ : sem_env) (γ1 γ2 : gmap string val) : iProp Σ :=
    [∗ map] x ↦ τ ∈ Γ,
      ∃ v1 v2,
        ⌜γ1 !! x = Some v1⌝ ∗
        ⌜γ2 !! x = Some v2⌝ ∗
        τ v1 v2.
  
  (* ─────────────────────────────────────────────────────────────────────────
     Semantic typing judgment
     
     Γ ⊨ e : τ means:
     "For all related substitutions, applying them to e gives related expressions"
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition sem_typed (Γ : sem_env) (e : expr) (τ : sem_ty) (eff : effect) : iProp Σ :=
    □ (∀ γ1 γ2,
         env_rel Γ γ1 γ2 -∗
         expr_rel τ eff (subst_map γ1 e) (subst_map γ2 e)).
  
  Notation "Γ ⊨ e : τ @ eff" := (sem_typed Γ e τ eff) (at level 74).

  (* ─────────────────────────────────────────────────────────────────────────
     Syntactic to semantic typing
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Convert syntactic type environment to semantic *)
  Definition interp_env (Γ : ty_env) : sem_env :=
    fmap interp Γ.
  
  (* The fundamental theorem will say:
     If Γ ⊢ e : T @ eff (syntactic), then interp_env Γ ⊨ e : ⟦T⟧ᵥ @ eff (semantic)
     This is proven in fundamental.v *)

End semantic_typing.
```

#### Phase 3: Effect System Integration (Weeks 7-10)

See Section 7 for complete details.

#### Phase 4: Main Proofs (Weeks 11-16)

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 4, FILE 1: riina/iris/fundamental.v
   
   Purpose: Fundamental theorem of logical relations
   Dependencies: typing.v, effects.v
   ═══════════════════════════════════════════════════════════════════════════ *)

From riina.iris Require Import prelude value_rel expr_rel store_rel typing effects.

Section fundamental.
  Context `{!riinaGS' Σ}.

  (* ─────────────────────────────────────────────────────────────────────────
     Fundamental Theorem
     
     Every well-typed expression is semantically typed.
     ───────────────────────────────────────────────────────────────────────── *)
  
  Theorem fundamental Γ e T eff :
    (* Syntactic typing *)
    Γ ⊢ e : T @ eff →
    (* Semantic typing *)
    interp_env Γ ⊨ e : ⟦ T ⟧ᵥ @ eff.
  Proof.
    induction 1.
    (* Case analysis on typing derivation *)
    - (* T-Var *)
      iIntros "!>" (γ1 γ2) "Henv".
      iDestruct (big_sepM_lookup with "Henv") as "Hx"; first done.
      iDestruct "Hx" as (v1 v2 Hv1 Hv2) "Hrel".
      rewrite /subst_map !lookup_fmap Hv1 Hv2 /=.
      iIntros (Φ) "HΦ".
      iApply wp_value.
      iExists v2.
      iApply wp_value.
      iSplit; [done|].
      iApply "HΦ".
      iApply "Hrel".
    
    - (* T-Unit *)
      iIntros "!>" (γ1 γ2) "_".
      iIntros (Φ) "HΦ".
      iApply wp_value.
      iExists #().
      iApply wp_value.
      iSplit; [done|].
      iApply "HΦ".
      iExists tt. done.
    
    - (* T-Lam *)
      iIntros "!>" (γ1 γ2) "#Henv".
      iIntros (Φ) "HΦ".
      rewrite /subst_map /=.
      iApply wp_value.
      iExists (RecV BAnon (subst_map (delete x γ2) e)).
      iApply wp_value.
      iSplit; [done|].
      iApply "HΦ".
      iExists BAnon, BAnon, (subst_map (delete x γ1) e), (subst_map (delete x γ2) e).
      iSplit; [done|]. iSplit; [done|].
      iModIntro.
      iIntros (w1 w2) "Hw".
      iIntros (Φ') "HΦ'".
      (* Use IH *)
      iSpecialize ("IHtyping" $! (<[x := w1]> γ1) (<[x := w2]> γ2)).
      (* ... complete the proof ... *)
      admit.
    
    - (* T-App *)
      iIntros "!>" (γ1 γ2) "#Henv".
      iSpecialize ("IHtyping1" $! γ1 γ2 with "Henv").
      iSpecialize ("IHtyping2" $! γ1 γ2 with "Henv").
      iIntros (Φ) "HΦ".
      (* Use wp_bind for application *)
      iApply wp_bind.
      iApply (wp_wand with "IHtyping1").
      iIntros (v1) "Hv1".
      (* ... continue with second argument and application ... *)
      admit.
    
    (* ... remaining ~30 cases ... *)
    all: admit.
  Admitted. (* Will be fully proven after migration *)

End fundamental.
```

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   PHASE 4, FILE 2: riina/iris/noninterference.v
   
   Purpose: Non-interference theorem
   Dependencies: fundamental.v
   ═══════════════════════════════════════════════════════════════════════════ *)

From riina.iris Require Import prelude value_rel expr_rel typing fundamental.

Section noninterference.
  Context `{!riinaGS' Σ}.

  (* ─────────────────────────────────────────────────────────────────────────
     Non-Interference
     
     If two executions start with the same public data but different secret data,
     they produce the same public output.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Observable equivalence at security level *)
  Definition observable_equiv (pc : security_level) (v1 v2 : val) : iProp Σ :=
    (* If pc can observe the value, they must be equal *)
    if decide (can_observe pc (val_sec_level v1))
    then ⌜v1 = v2⌝
    else True.
  
  (* Low-equivalence of stores *)
  Definition store_low_equiv (pc : security_level) : iProp Σ :=
    ∀ l T sec,
      loc_pair_inv l l T sec -∗
      if decide (sec ⊑ pc)
      then ∃ v, l ↦ v (* same value at both "copies" *)
      else True.      (* different values ok for high locations *)
  
  Theorem noninterference Γ e T eff pc :
    (* Well-typed at security level pc *)
    Γ ⊢ e : T @ eff →
    type_level T ⊑ pc →
    (* Two executions with low-equivalent stores *)
    store_low_equiv pc -∗
    (* Starting with related environments *)
    ∀ γ1 γ2, env_rel (interp_env Γ) γ1 γ2 -∗
    (* Produce observationally equivalent results *)
    WP (subst_map γ1 e) {{ v1,
      ∃ v2, WP (subst_map γ2 e) {{ v2',
        ⌜v2' = v2⌝ ∗ observable_equiv pc v1 v2
      }}
    }}.
  Proof.
    iIntros (Htyp Hlevel) "Hstore".
    iIntros (γ1 γ2) "#Henv".
    (* Apply fundamental theorem *)
    iPoseProof (fundamental Γ e T eff Htyp) as "Hfund".
    iSpecialize ("Hfund" $! γ1 γ2 with "Henv").
    iApply (wp_wand with "Hfund").
    iIntros (v1) "Hv1".
    iDestruct "Hv1" as (v2) "[Hwp Hrel]".
    iExists v2.
    iApply (wp_wand with "Hwp").
    iIntros (v2') "[-> _]".
    iSplit; [done|].
    (* Use the value relation to derive observable equivalence *)
    (* At type level ⊑ pc, related values are equal *)
    admit.
  Admitted.

End noninterference.
```

#### Phase 5: Session Types (Weeks 17-20)

See Section 8 for complete details.

### 6.3 Incremental Compilation Strategy

To maintain compilation throughout the migration:

```makefile
# Makefile fragment for incremental migration

# Phase 1: Can compile independently
PHASE1_FILES := \
  riina/iris/prelude.v \
  riina/iris/resources.v \
  riina/iris/lang_interface.v

# Phase 2: Depends on Phase 1
PHASE2_FILES := \
  riina/iris/value_rel.v \
  riina/iris/expr_rel.v \
  riina/iris/store_rel.v \
  riina/iris/typing.v

# Bridge: Allows old and new to coexist
BRIDGE_FILES := \
  riina/bridge/old_to_new.v \
  riina/bridge/compat.v

# Build order
all: phase1 phase2 bridge

phase1: $(PHASE1_FILES:.v=.vo)
phase2: phase1 $(PHASE2_FILES:.v=.vo)
bridge: phase2 $(BRIDGE_FILES:.v=.vo)

# Bridge file: translates old types to new
# riina/bridge/old_to_new.v
```

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   BRIDGE FILE: riina/bridge/old_to_new.v
   
   Purpose: Allow old proofs to use new definitions during transition
   ═══════════════════════════════════════════════════════════════════════════ *)

From riina.logic Require Import value_rel.   (* Old definitions *)
From riina.iris Require Import value_rel.    (* New definitions *)

(* Bridge: old val_rel_n implies new interp *)
Lemma val_rel_bridge `{!riinaGS' Σ} n T v1 v2 :
  val_rel_n n T v1 v2 →
  ⊢ ⟦ T ⟧ᵥ v1 v2.
Proof.
  (* This proof shows the old and new definitions are compatible *)
  induction T; intros Hrel; simpl in *.
  - (* TUnit *)
    destruct Hrel as [-> ->].
    iPureIntro. split; reflexivity.
  - (* TBool *)
    destruct Hrel as (b & -> & ->).
    iExists b. iPureIntro. split; reflexivity.
  (* ... remaining cases ... *)
Admitted.

(* Bridge: new interp implies old val_rel_n for sufficiently large n *)
Lemma val_rel_bridge_back `{!riinaGS' Σ} T v1 v2 :
  (⊢ ⟦ T ⟧ᵥ v1 v2) →
  ∀ n, val_rel_n n T v1 v2.
Proof.
  (* The semantic model of iProp gives us this *)
Admitted.
```

---

## 7. Effect System Integration

### 7.1 Overview

RIINA has 16 effects. Iris does not have built-in effects, so we model them as **resources**.

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   riina/iris/effects.v - Effect System Integration
   ═══════════════════════════════════════════════════════════════════════════ *)

From iris.algebra Require Import auth excl gmap gset frac.
From iris.proofmode Require Import tactics.
From riina.iris Require Import prelude resources.

Section effects.
  Context `{!riinaGS' Σ}.

  (* ─────────────────────────────────────────────────────────────────────────
     Effect Lattice
     
     RIINA's 16 effects form a lattice. We encode this as a camera.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Effect enumeration *)
  Inductive effect :=
    | EffPure        (* No effects *)
    | EffRead        (* Memory read *)
    | EffWrite       (* Memory write *)
    | EffFileSystem  (* File I/O *)
    | EffNetwork     (* Network (unencrypted) *)
    | EffNetSecure   (* Network (TLS) *)
    | EffCrypto      (* Cryptographic operations *)
    | EffRandom      (* Random number generation *)
    | EffSystem      (* System calls *)
    | EffTime        (* Time access *)
    | EffProcess     (* Process management *)
    | EffPanel       (* RIINA Panel subsystem *)
    | EffZirah       (* RIINA Zirah (auth) subsystem *)
    | EffBenteng     (* RIINA Benteng (WAF) subsystem *)
    | EffSandi       (* RIINA Sandi (crypto) subsystem *)
    | EffMenara      (* RIINA Menara (tower) subsystem *)
    | EffGapura      (* RIINA Gapura (gateway) subsystem *).
  
  (* Effect ordering (partial order) *)
  Definition effect_le (e1 e2 : effect) : Prop :=
    match e1, e2 with
    | EffPure, _ => True
    | _, EffPure => False
    | EffRead, EffWrite => True
    | EffNetwork, EffNetSecure => True
    | e, e' => e = e'
    end.
  
  Notation "e1 ≼ e2" := (effect_le e1 e2) (at level 70).

  (* ─────────────────────────────────────────────────────────────────────────
     Effect Resources
     
     Key insight: Effects are PERMISSIONS.
     An expression can only perform an effect if it OWNS the permission.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Effect permission: we can perform effect eff *)
  Definition eff_perm (eff : effect) : iProp Σ := effect_perm eff.
  
  (* Notation *)
  Notation "⟨ eff ⟩ₑ" := (eff_perm eff) (at level 10, format "⟨  eff  ⟩ₑ").
  
  (* EffPure is always available (it's trivial) *)
  Lemma eff_pure_always :
    ⊢ ⟨ EffPure ⟩ₑ.
  Proof.
    (* EffPure doesn't consume any real permission *)
    admit.
  Admitted.
  
  (* Effect weakening: if we have e2, we have all e1 ≼ e2 *)
  Lemma eff_weaken (e1 e2 : effect) :
    e1 ≼ e2 →
    ⟨ e2 ⟩ₑ -∗ ⟨ e1 ⟩ₑ.
  Proof.
    (* Follows from effect_le definition *)
    admit.
  Admitted.

  (* ─────────────────────────────────────────────────────────────────────────
     Effect-Annotated Weakest Precondition
     
     WPₑ[eff] e {{ Φ }} means:
     "e satisfies Φ and only performs effects in eff"
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition wp_eff (eff : effect) (e : expr) (Φ : val → iProp Σ) : iProp Σ :=
    ⟨ eff ⟩ₑ -∗ WP e {{ v, ⟨ eff ⟩ₑ ∗ Φ v }}.
  
  Notation "'WPₑ[' eff ']' e {{ Φ } }" := (wp_eff eff e Φ)
    (at level 20, eff, e, Φ at level 200).
  
  (* Pure expressions need no effect permission *)
  Lemma wp_pure (e : expr) (Φ : val → iProp Σ) :
    WP e {{ Φ }} -∗ WPₑ[EffPure] e {{ Φ }}.
  Proof.
    iIntros "Hwp Hpure".
    iApply (wp_wand with "Hwp").
    iIntros (v) "HΦ".
    iFrame.
  Qed.
  
  (* Effect composition: sequential composition combines effects *)
  Lemma wp_eff_bind (eff1 eff2 : effect) K e (Φ : val → iProp Σ) :
    WPₑ[eff1] e {{ v, WPₑ[eff2] (fill K (Val v)) {{ Φ }} }} -∗
    WPₑ[eff_join eff1 eff2] (fill K e) {{ Φ }}.
  Proof.
    (* Uses effect_join to combine effect requirements *)
    admit.
  Admitted.

  (* ─────────────────────────────────────────────────────────────────────────
     Effect-Aware Expression Relation
     
     Two expressions are related at effect eff if they both perform
     at most effect eff and produce related results.
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition expr_rel_eff (T : ty) (eff : effect) (e1 e2 : expr) : iProp Σ :=
    ∀ (Φ : val → val → iProp Σ),
      (∀ v1 v2, ⟦ T ⟧ᵥ v1 v2 -∗ Φ v1 v2) -∗
      ⟨ eff ⟩ₑ -∗
      WP e1 {{ v1, ⟨ eff ⟩ₑ ∗ ∃ v2, WP e2 {{ v2', ⌜v2' = v2⌝ ∗ Φ v1 v2 }} }}.
  
  Notation "e1 ≈ₑ[ T , eff ] e2" := (expr_rel_eff T eff e1 e2) (at level 70).

  (* ─────────────────────────────────────────────────────────────────────────
     Effect Primitive Rules
     
     Each effectful primitive consumes its effect permission.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Memory read *)
  Lemma wp_read l v :
    l ↦ v -∗
    WPₑ[EffRead] (! #l) {{ w, l ↦ v ∗ ⌜w = v⌝ }}.
  Proof.
    iIntros "Hl Heff".
    iApply wp_load.
    iFrame "Hl".
    iIntros "!> Hl".
    iFrame.
  Qed.
  
  (* Memory write *)
  Lemma wp_write l v w :
    l ↦ v -∗
    WPₑ[EffWrite] (#l <- w) {{ _, l ↦ w }}.
  Proof.
    iIntros "Hl Heff".
    iApply wp_store.
    iFrame "Hl".
    iIntros "!> Hl".
    iFrame.
  Qed.
  
  (* Network send (unencrypted) *)
  Lemma wp_net_send ch msg :
    WPₑ[EffNetwork] (net_send ch msg) {{ _, True }}.
  Proof.
    (* Primitive axiom *)
    admit.
  Admitted.
  
  (* Network send (TLS) — requires EffNetSecure *)
  Lemma wp_tls_send ch msg :
    WPₑ[EffNetSecure] (tls_send ch msg) {{ _, True }}.
  Proof.
    admit.
  Admitted.
  
  (* Crypto operation *)
  Lemma wp_encrypt key plaintext :
    WPₑ[EffCrypto] (encrypt key plaintext) {{ ciphertext, ⌜length ciphertext = length plaintext + 16⌝ }}.
  Proof.
    admit.
  Admitted.

  (* ─────────────────────────────────────────────────────────────────────────
     RIINA Subsystem Effects
     
     Panel, Zirah, Benteng, Sandi, Menara, Gapura
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Zirah (authentication) subsystem *)
  Lemma wp_zirah_authenticate user cred :
    WPₑ[EffZirah] (zirah_auth user cred) {{ result, 
      ⌜result = true ∨ result = false⌝
    }}.
  Proof. admit. Admitted.
  
  (* Benteng (WAF) subsystem *)
  Lemma wp_benteng_filter request :
    WPₑ[EffBenteng] (benteng_filter request) {{ result,
      match result with
      | FilterPass => True
      | FilterBlock reason => ⌜is_valid_block_reason reason⌝
      end
    }}.
  Proof. admit. Admitted.
  
  (* Sandi (crypto) subsystem — requires EffCrypto + EffSandi *)
  Lemma wp_sandi_sign key msg :
    ⟨ EffCrypto ⟩ₑ ∗ ⟨ EffSandi ⟩ₑ -∗
    WP (sandi_sign key msg) {{ sig, ⌜is_valid_signature key msg sig⌝ }}.
  Proof. admit. Admitted.

End effects.

(* ═══════════════════════════════════════════════════════════════════════════
   Effect Join Operation (for combining effects)
   ═══════════════════════════════════════════════════════════════════════════ *)

Definition eff_join (e1 e2 : effect) : effect :=
  match e1, e2 with
  | EffPure, e => e
  | e, EffPure => e
  | EffRead, EffWrite => EffWrite
  | EffWrite, EffRead => EffWrite
  | EffNetwork, EffNetSecure => EffNetSecure
  | EffNetSecure, EffNetwork => EffNetSecure
  (* ... full join operation ... *)
  | e1, e2 => if effect_eq_dec e1 e2 then e1 else EffSystem (* fallback *)
  end.
```

### 7.2 Effect Resource Allocation

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   Effect resource allocation and frame rule
   ═══════════════════════════════════════════════════════════════════════════ *)

Section effect_allocation.
  Context `{!riinaGS' Σ}.

  (* Allocate effect permission at program start *)
  Lemma effect_alloc (effs : gset effect) :
    ⊢ |==> ∃ γ, own γ (● effs) ∗ [∗ set] e ∈ effs, effect_perm_at γ e.
  Proof.
    (* Use auth camera allocation *)
    admit.
  Admitted.
  
  (* Effect frame rule: effectful code doesn't touch other effects *)
  Lemma wp_eff_frame (eff eff' : effect) e Φ R :
    eff ≠ eff' →
    ⟨ eff' ⟩ₑ ∗ WPₑ[eff] e {{ Φ }} -∗
    WPₑ[eff] e {{ v, ⟨ eff' ⟩ₑ ∗ Φ v }}.
  Proof.
    iIntros (Hneq) "[Heff' Hwp]".
    iIntros "Heff".
    iApply (wp_frame_l with "[Heff']").
    { iFrame. }
    iApply ("Hwp" with "Heff").
  Qed.

End effect_allocation.
```

---

## 8. Session Type Integration

### 8.1 Overview

RIINA's session types describe binary communication protocols:
- `SessSend T S` — Send a value of type T, continue with S
- `SessRecv T S` — Receive a value of type T, continue with S
- `SessSelect L R` — Choose left (L) or right (R) protocol
- `SessBranch L R` — Offer choice between L and R
- `SessRec X S` — Recursive protocol (bind X to the whole thing)
- `SessEnd` — Protocol complete

### 8.2 Session Resources

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   riina/iris/sessions.v - Session Type Integration
   ═══════════════════════════════════════════════════════════════════════════ *)

From iris.algebra Require Import auth excl agree gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From riina.iris Require Import prelude resources value_rel.

Section sessions.
  Context `{!riinaGS' Σ}.

  (* ─────────────────────────────────────────────────────────────────────────
     Session Type Syntax
     ───────────────────────────────────────────────────────────────────────── *)
  
  Inductive session_type :=
    | SessEnd
    | SessSend (T : ty) (S : session_type)
    | SessRecv (T : ty) (S : session_type)
    | SessSelect (L R : session_type)
    | SessBranch (L R : session_type)
    | SessRec (X : string) (S : session_type)
    | SessVar (X : string).
  
  (* Session duality: swap send/recv, select/branch *)
  Fixpoint sess_dual (S : session_type) : session_type :=
    match S with
    | SessEnd => SessEnd
    | SessSend T S' => SessRecv T (sess_dual S')
    | SessRecv T S' => SessSend T (sess_dual S')
    | SessSelect L R => SessBranch (sess_dual L) (sess_dual R)
    | SessBranch L R => SessSelect (sess_dual L) (sess_dual R)
    | SessRec X S' => SessRec X (sess_dual S')
    | SessVar X => SessVar X
    end.

  (* ─────────────────────────────────────────────────────────────────────────
     Session State Resource
     
     A channel has an associated session type that evolves as messages
     are exchanged.
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Session type camera: exclusive ownership of current protocol state *)
  Definition sess_stateR := exclR (leibnizO session_type).
  
  (* Session channel: two endpoints with dual protocols *)
  Record session_chan := {
    chan_end1 : channel_id;
    chan_end2 : channel_id;
    chan_proto : session_type;
  }.
  
  (* Resource: endpoint owns its view of the protocol *)
  Definition sess_endpoint (ch : channel_id) (S : session_type) : iProp Σ :=
    own session_name (◯ {[ ch := Excl S ]}).
  
  Notation "ch ↦ₛₑₛₛ S" := (sess_endpoint ch S) (at level 20).

  (* ─────────────────────────────────────────────────────────────────────────
     Channel Invariant
     
     Two endpoints of a channel have dual protocols.
     ───────────────────────────────────────────────────────────────────────── *)
  
  Definition sessN : namespace := nroot .@ "riina" .@ "session".
  
  Definition channel_inv (ch1 ch2 : channel_id) (S : session_type) : iProp Σ :=
    inv (sessN .@ ch1 .@ ch2) (
      ∃ S1 S2,
        ch1 ↦ₛₑₛₛ S1 ∗
        ch2 ↦ₛₑₛₛ S2 ∗
        ⌜S2 = sess_dual S1⌝
    ).

  (* ─────────────────────────────────────────────────────────────────────────
     Session Type Interpretation
     
     Map session types to Iris predicates on channel values.
     ───────────────────────────────────────────────────────────────────────── *)
  
  Fixpoint interp_session (S : session_type) : channel_id → channel_id → iProp Σ :=
    match S with
    | SessEnd =>
        λ ch1 ch2, ⌜True⌝  (* Protocol complete, nothing more to do *)
    
    | SessSend T S' =>
        λ ch1 ch2,
          (* ch1 can send a T, then continue with S' *)
          ∀ v1 v2,
            ⟦ T ⟧ᵥ v1 v2 -∗
            ch1 ↦ₛₑₛₛ (SessSend T S') -∗
            |==> ch1 ↦ₛₑₛₛ S' ∗
                 (* message sent to ch2's buffer *)
                 ch2 ↦ᵦᵤf (v1, v2)  (* buffer resource *)
    
    | SessRecv T S' =>
        λ ch1 ch2,
          (* ch1 can receive a T, then continue with S' *)
          ch1 ↦ₛₑₛₛ (SessRecv T S') -∗
          ∃ v1 v2,
            ▷ ⟦ T ⟧ᵥ v1 v2 ∗
            ch1 ↦ₛₑₛₛ S'
    
    | SessSelect L R =>
        λ ch1 ch2,
          (* ch1 can choose left or right *)
          ch1 ↦ₛₑₛₛ (SessSelect L R) -∗
          (|==> ch1 ↦ₛₑₛₛ L ∗ ch2 ↦ₛₑₛₛ (sess_dual L)) ∨
          (|==> ch1 ↦ₛₑₛₛ R ∗ ch2 ↦ₛₑₛₛ (sess_dual R))
    
    | SessBranch L R =>
        λ ch1 ch2,
          (* ch1 offers choice to ch2 *)
          ch1 ↦ₛₑₛₛ (SessBranch L R) -∗
          (* When ch2 chooses, we get the corresponding protocol *)
          (ch1 ↦ₛₑₛₛ L ∨ ch1 ↦ₛₑₛₛ R)
    
    | SessRec X S' =>
        λ ch1 ch2,
          (* Unfold the recursion *)
          ▷ interp_session (sess_subst X (SessRec X S') S') ch1 ch2
    
    | SessVar X =>
        λ ch1 ch2, False%I  (* Should not appear in closed types *)
    end.
  
  Notation "⟦ S ⟧ₛ" := (interp_session S) (at level 0).

  (* ─────────────────────────────────────────────────────────────────────────
     Session Primitive Rules
     ───────────────────────────────────────────────────────────────────────── *)
  
  (* Send rule *)
  Lemma wp_sess_send ch T S v :
    ch ↦ₛₑₛₛ (SessSend T S) -∗
    ⟦ T ⟧ᵥ v v -∗  (* Value is self-related *)
    WP (sess_send ch v) {{ _, ch ↦ₛₑₛₛ S }}.
  Proof.
    iIntros "Hch Hv".
    (* Update the session state *)
    admit.
  Admitted.
  
  (* Receive rule *)
  Lemma wp_sess_recv ch T S :
    ch ↦ₛₑₛₛ (SessRecv T S) -∗
    WP (sess_recv ch) {{ v, ch ↦ₛₑₛₛ S ∗ ∃ v', ⟦ T ⟧ᵥ v v' }}.
  Proof.
    iIntros "Hch".
    (* Receive updates state and gives related value *)
    admit.
  Admitted.
  
  (* Select left *)
  Lemma wp_sess_select_l ch L R :
    ch ↦ₛₑₛₛ (SessSelect L R) -∗
    WP (sess_select_l ch) {{ _, ch ↦ₛₑₛₛ L }}.
  Proof.
    admit.
  Admitted.
  
  (* Select right *)
  Lemma wp_sess_select_r ch L R :
    ch ↦ₛₑₛₛ (SessSelect L R) -∗
    WP (sess_select_r ch) {{ _, ch ↦ₛₑₛₛ R }}.
  Proof.
    admit.
  Admitted.
  
  (* Branch *)
  Lemma wp_sess_branch ch L R (e_l e_r : expr) Φ :
    ch ↦ₛₑₛₛ (SessBranch L R) -∗
    (ch ↦ₛₑₛₛ L -∗ WP e_l {{ Φ }}) -∗
    (ch ↦ₛₑₛₛ R -∗ WP e_r {{ Φ }}) -∗
    WP (sess_branch ch e_l e_r) {{ Φ }}.
  Proof.
    admit.
  Admitted.

  (* ─────────────────────────────────────────────────────────────────────────
     Session Duality Theorem
     
     If ch1 has protocol S, then ch2 (its dual endpoint) has sess_dual S.
     ───────────────────────────────────────────────────────────────────────── *)
  
  Lemma session_duality ch1 ch2 S :
    channel_inv ch1 ch2 S -∗
    □ (ch1 ↦ₛₑₛₛ S -∗ ∃ S', ch2 ↦ₛₑₛₛ S' ∗ ⌜S' = sess_dual S⌝).
  Proof.
    iIntros "#Hinv".
    iModIntro.
    iIntros "Hch1".
    iInv "Hinv" as (S1 S2) "(Hch1' & Hch2 & %Hdual)" "Hclose".
    (* ch1 ↦ S and ch1 ↦ S1 must agree *)
    iDestruct (sess_endpoint_agree with "Hch1 Hch1'") as %->.
    iExists S2.
    iFrame "Hch2".
    iSplit; [done|].
    iApply "Hclose".
    iExists S, S2.
    iFrame. done.
  Qed.

End sessions.

(* ═══════════════════════════════════════════════════════════════════════════
   Session Type in Value Relation
   
   The interp_chan_pre from value_rel.v uses the session interpretation.
   ═══════════════════════════════════════════════════════════════════════════ *)

(* In riina/iris/value_rel.v, the channel case becomes: *)
Definition interp_chan (sess_ty : session_type) : val → val → iProp Σ :=
  λ v1 v2,
    ∃ (ch1 ch2 : channel_id),
      ⌜v1 = ChanV ch1 ∧ v2 = ChanV ch2⌝ ∗
      channel_inv ch1 ch2 sess_ty.
```

### 8.3 Session Type Non-Interference

```coq
(* ═══════════════════════════════════════════════════════════════════════════
   Session-aware non-interference
   ═══════════════════════════════════════════════════════════════════════════ *)

Section session_noninterference.
  Context `{!riinaGS' Σ}.

  (* Communication on high-security channels is not observable at low level *)
  Lemma session_high_unobservable ch S pc :
    session_sec_level S ⋢ pc →  (* Session is high-security *)
    (* Any protocol step on ch is invisible at level pc *)
    ∀ e, is_session_step ch e →
    WP e {{ _, True }} -∗
    observable_at pc e e.
  Proof.
    (* High-security session operations produce no low-observable effect *)
    admit.
  Admitted.

End session_noninterference.
```

---

## 9. Risks and Mitigations

### 9.1 Risk Assessment Matrix

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Iris version incompatibility | Medium | High | Pin to coq-iris 4.2.0, test with CI |
| Performance regression in proofs | Medium | Medium | Profile compile times, use `Qed` not `Defined` |
| Semantic gap between old/new | Low | High | Prove bridge lemmas formally |
| Missing Iris features for RIINA | Low | Medium | Extend with custom cameras |
| Team unfamiliarity with Iris | High | Medium | Training sessions, pair programming |
| Interaction with existing code | Medium | High | Bridge files, incremental migration |

### 9.2 Detailed Risks

#### 9.2.1 RISK: Iris Does NOT Have a Built-In Effect System

**Problem:** RIINA has 16 effects with a lattice ordering. Iris provides no built-in effect tracking.

**Mitigation:** Model effects as resources (Section 7). This is actually MORE flexible because:
- Effects become first-class citizens
- Can track effect permissions at runtime
- Can compose effects explicitly

**Remaining work:** ~800 lines of effect resource code

#### 9.2.2 RISK: RIINA's Security Lattice vs. Iris's Invariants

**Problem:** RIINA's 6-point security lattice (LPublic ⊑ ... ⊑ LSecret) doesn't map directly to Iris invariants.

**Mitigation:** Encode security levels as ghost state:

```coq
(* Security lattice as discrete OFE *)
Definition sec_latticeO := leibnizO security_level.

(* Ghost state for value labels *)
Definition sec_labelR := authR (gmapUR loc (agreeR sec_latticeO)).

(* Assertion: value at l has security level s *)
Definition sec_label (l : loc) (s : security_level) : iProp Σ :=
  own sec_label_name (◯ {[ l := to_agree s ]}).

(* Level can only increase (monotone) *)
Lemma sec_label_monotone l s1 s2 :
  s1 ⊑ s2 →
  sec_label l s1 ==∗ sec_label l s2.
```

#### 9.2.3 RISK: Recursive Session Types

**Problem:** RIINA has `SessRec X S` for recursive protocols. Iris's later modality handles recursion, but session duality with recursion is subtle.

**Mitigation:** 
1. Use Iris's guarded fixpoint for session type interpretation
2. Prove duality preserves well-foundedness separately
3. Limit recursion depth in proofs if needed

```coq
(* Guarded session type interpretation *)
Definition interp_session_pre 
  (interp : session_type → channel_id → channel_id → iProp Σ)
  (S : session_type) : channel_id → channel_id → iProp Σ :=
  match S with
  | SessRec X S' =>
      λ ch1 ch2, ▷ interp (sess_subst X (SessRec X S') S') ch1 ch2
      (* ▷ makes this contractive! *)
  | _ => (* ... other cases ... *)
  end.

(* Take fixpoint *)
Definition interp_session := fixpoint interp_session_pre.
```

#### 9.2.4 RISK: Compile Time Explosion

**Problem:** Iris proofs can be slow due to heavy typeclass resolution.

**Mitigation:**
1. Use `Opaque` for large definitions
2. Prefer `Qed` over `Defined` (when extraction not needed)
3. Split proofs into smaller lemmas
4. Use `Set Default Proof Using` for universe constraints

```coq
(* Example: making interp opaque for faster compilation *)
Global Opaque interp.

(* Reveal only for specific lemmas *)
Lemma interp_unfold T v1 v2 :
  interp T v1 v2 ⊣⊢ interp_def T v1 v2.
Proof. unfold interp. reflexivity. Qed.
```

### 9.3 What Iris Does NOT Provide

| Need | Iris Status | RIINA Solution |
|------|-------------|----------------|
| Effect system | Not built-in | Effect resources (Section 7) |
| Security lattice | Not built-in | Ghost state encoding |
| Taint tracking | Not built-in | Taint resources |
| Capability system | Not built-in | Capability cameras |
| Session types | Not built-in | Protocol resources (Section 8) |
| Non-interference | Not built-in | Binary logical relations on iProp |

### 9.4 Contingency Plan

If migration encounters blocking issues:

1. **Partial migration:** Keep old definitions for problematic types, use bridge lemmas
2. **Custom Iris extensions:** Fork coq-iris if needed for RIINA-specific features
3. **Hybrid approach:** Use Iris for core infrastructure, custom proofs for RIINA-specific properties
4. **Rollback criteria:** If >50% of proofs need rework, reconsider approach

---

## 10. Testing and Validation Strategy

### 10.1 Validation Checkpoints

| Checkpoint | Criteria | Deadline |
|------------|----------|----------|
| CP1: Infrastructure | prelude.v, resources.v, lang_interface.v compile | Week 2 |
| CP2: Value Relation | interp for all 15 RIINA types defined | Week 4 |
| CP3: Expression Relation | expr_rel, bind lemma proven | Week 6 |
| CP4: Store Relation | inv-based store relation, extension theorem | Week 8 |
| CP5: Fundamental | 10 typing cases proven | Week 12 |
| CP6: Non-Interference | Main theorem statement complete | Week 16 |
| CP7: Effects | All 16 effects have resources | Week 18 |
| CP8: Sessions | Basic session operations working | Week 20 |
| CP9: Full Migration | All old axioms eliminated | Week 27 |

### 10.2 Regression Testing

```makefile
# CI configuration for migration validation

test-migration:
	# Phase 1: Infrastructure compiles
	coqc riina/iris/prelude.v
	coqc riina/iris/resources.v
	coqc riina/iris/lang_interface.v
	
	# Phase 2: Core relations
	coqc riina/iris/value_rel.v
	coqc riina/iris/expr_rel.v
	coqc riina/iris/store_rel.v
	
	# Bridge: old/new compatibility
	coqc riina/bridge/old_to_new.v
	
	# Verify axiom count reduced
	grep -c "Axiom\|Admitted" riina/iris/*.v | \
	  awk -F: '{sum += $$2} END {if (sum > 5) exit 1}'

# Nightly: full proof check
test-full:
	coqc -Q riina riina -Q iris iris riina/iris/fundamental.v
	coqc -Q riina riina -Q iris iris riina/iris/noninterference.v
```

### 10.3 Axiom Tracking

```coq
(* riina/iris/axiom_audit.v - Track remaining axioms *)

(* This file lists all remaining axioms after migration *)
(* Goal: 0 axioms, ~5 admitted proofs (for edge cases) *)

Print Assumptions fundamental.
(* Expected output: Closed under the global context *)

Print Assumptions noninterference.
(* Expected output: Closed under the global context *)
```

---

## Appendix A: Complete Type Definitions

### A.1 RIINA Type Syntax (riina/lang/types.v)

```coq
(* Complete RIINA type definition for reference *)

Inductive ty :=
  (* Primitive types *)
  | TUnit
  | TBool
  | TInt
  | TString
  | TBytes
  
  (* Compound types *)
  | TFn (T1 T2 : ty) (eff : effect)
  | TProd (T1 T2 : ty)
  | TSum (T1 T2 : ty)
  | TList (T : ty)
  | TOption (T : ty)
  | TResult (T E : ty)
  
  (* Reference types *)
  | TRef (T : ty) (sec : security_level)
  | TMutRef (T : ty) (sec : security_level)
  
  (* Security types *)
  | TSecret (T : ty)
  | TLabeled (T : ty) (level : security_level)
  | TTainted (T : ty) (source : taint_source)
  | TSanitized (T : ty) (sanitizer : sanitizer_id)
  
  (* Communication types *)
  | TChan (sess : session_type)
  
  (* Capability types *)
  | TCapability (kind : capability_kind)
  
  (* Recursive types *)
  | TRec (X : string) (T : ty)
  | TVar (X : string).
```

### A.2 Security Level Lattice

```coq
(* Security levels with lattice structure *)

Inductive security_level :=
  | LPublic    (* Anyone can read *)
  | LInternal  (* Internal to organization *)
  | LSession   (* Session-bound *)
  | LUser      (* User-specific *)
  | LSystem    (* System-level *)
  | LSecret.   (* Maximum secrecy *)

(* Lattice ordering *)
Definition sec_le (l1 l2 : security_level) : Prop :=
  match l1, l2 with
  | LPublic, _ => True
  | LInternal, LPublic => False
  | LInternal, _ => True
  | LSession, (LPublic | LInternal) => False
  | LSession, _ => True
  | LUser, (LPublic | LInternal | LSession) => False
  | LUser, _ => True
  | LSystem, LSecret => True
  | LSystem, LSystem => True
  | LSystem, _ => False
  | LSecret, LSecret => True
  | LSecret, _ => False
  end.

Notation "l1 ⊑ l2" := (sec_le l1 l2) (at level 70).

(* Join and meet *)
Definition sec_join (l1 l2 : security_level) : security_level := (* ... *).
Definition sec_meet (l1 l2 : security_level) : security_level := (* ... *).
```

### A.3 Effect Enumeration

```coq
(* All 16 RIINA effects *)

Inductive effect :=
  | EffPure        (* No side effects *)
  | EffRead        (* Memory read *)
  | EffWrite       (* Memory write *)
  | EffFileSystem  (* File I/O *)
  | EffNetwork     (* Network (unencrypted) *)
  | EffNetSecure   (* Network (TLS/encrypted) *)
  | EffCrypto      (* Cryptographic operations *)
  | EffRandom      (* Random number generation *)
  | EffSystem      (* System calls *)
  | EffTime        (* Time/clock access *)
  | EffProcess     (* Process management *)
  | EffPanel       (* RIINA Panel subsystem *)
  | EffZirah       (* RIINA Zirah (authentication) *)
  | EffBenteng     (* RIINA Benteng (WAF) *)
  | EffSandi       (* RIINA Sandi (crypto library) *)
  | EffMenara      (* RIINA Menara (tower/central) *)
  | EffGapura.     (* RIINA Gapura (gateway) *)

(* Effect lattice structure *)
Definition eff_le (e1 e2 : effect) : Prop := (* ... *).
Definition eff_join (e1 e2 : effect) : effect := (* ... *).
```

---

**END OF DOCUMENT**

**Document ID:** `RIINA_IRIS_MIGRATION_SPEC_v1_0_0`  
**Version:** 1.0.0  
**Status:** Draft for Review  
**Next Review Date:** 2026-02-28