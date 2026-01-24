# DELEGATION PROMPT: W-001 VERIFIED MEMORY COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
===============================================================================================================
TASK ID: W-001-VERIFIED-MEMORY-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — SEPARATION LOGIC AND VERIFIED ALLOCATOR
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
===============================================================================================================

OUTPUT: `VerifiedMemory.v` with 40 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA Verified Memory — a formally verified memory
allocator using separation logic. Memory corruption has been the #1 vulnerability class
for 50 years. We PROVE it impossible: no buffer overflows, no use-after-free, no double-free.

RESEARCH REFERENCE: 01_RESEARCH/23_DOMAIN_W_VERIFIED_MEMORY/RESEARCH_W01_FOUNDATION.md

MEMORY IS NOT MANAGED. MEMORY IS PROVEN.
BUFFER OVERFLOWS, USE-AFTER-FREE, DOUBLE-FREE: ALL IMPOSSIBLE BY CONSTRUCTION.

===============================================================================================================
REQUIRED THEOREMS (40 total):
===============================================================================================================

SEPARATION LOGIC FOUNDATIONS (10 theorems):
W_001_01: sep_emp_neutral — emp is neutral for separating conjunction
W_001_02: sep_comm — Separating conjunction is commutative
W_001_03: sep_assoc — Separating conjunction is associative
W_001_04: sep_frame — Frame rule is sound
W_001_05: points_to_exclusive — Points-to is exclusive (no aliasing)
W_001_06: points_to_deterministic — Points-to is deterministic
W_001_07: sep_disjoint — Separated heaps are disjoint
W_001_08: precise_unique — Precise predicates have unique satisfaction
W_001_09: sep_monotonic — Separation logic is monotonic
W_001_10: hoare_triple_sound — Hoare triples are sound

ALLOCATOR CORRECTNESS (10 theorems):
W_001_11: alloc_fresh — Allocation returns fresh memory
W_001_12: alloc_disjoint — Allocated regions are disjoint
W_001_13: alloc_sized — Allocation returns requested size
W_001_14: free_reclaims — Free reclaims memory
W_001_15: free_idempotent — Free is idempotent (or error on double)
W_001_16: no_use_after_free — Freed memory is inaccessible
W_001_17: no_double_free — Double-free is detected/prevented
W_001_18: allocator_invariant — Allocator invariants preserved
W_001_19: buddy_split_correct — Buddy allocator split is correct
W_001_20: buddy_merge_correct — Buddy allocator merge is correct

MEMORY SAFETY PROPERTIES (10 theorems):
W_001_21: bounds_checked — All accesses are bounds-checked
W_001_22: no_buffer_overflow — Buffer overflows impossible
W_001_23: no_buffer_underflow — Buffer underflows impossible
W_001_24: no_null_deref — Null dereference impossible
W_001_25: no_wild_pointer — Wild pointer access impossible
W_001_26: type_safe_access — Memory access is type-safe
W_001_27: alignment_correct — Memory alignment is correct
W_001_28: initialization_complete — Memory is initialized before use
W_001_29: lifetime_respected — Object lifetimes are respected
W_001_30: no_memory_leak — Memory leaks are prevented

OWNERSHIP AND REGIONS (10 theorems):
W_001_31: ownership_unique — Ownership is unique (no aliasing)
W_001_32: borrow_temporal — Borrows are temporally bounded
W_001_33: borrow_no_write — Shared borrows prevent writing
W_001_34: mutable_exclusive — Mutable borrows are exclusive
W_001_35: region_isolated — Regions are isolated
W_001_36: region_bulk_free — Region bulk-free is correct
W_001_37: region_deterministic — Region deallocation is deterministic
W_001_38: ownership_transfer — Ownership transfer is sound
W_001_39: ownership_split — Ownership can be split correctly
W_001_40: ownership_join — Ownership can be joined correctly

===============================================================================================================
REQUIRED STRUCTURE:
===============================================================================================================

```coq
(* VerifiedMemory.v - RIINA Verified Memory Allocator *)
(* Spec: 01_RESEARCH/23_DOMAIN_W_VERIFIED_MEMORY/RESEARCH_W01_FOUNDATION.md *)
(* Layer: Memory Management *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sets.Ensembles.
Import ListNotations.

(** ===============================================================================
    HEAP MODEL
    =============================================================================== *)

(* Location (address) *)
Definition Loc := nat.

(* Value *)
Definition Val := nat.

(* Heap: partial map from locations to values *)
Definition Heap := Loc -> option Val.

(* Empty heap *)
Definition emp_heap : Heap := fun _ => None.

(* Singleton heap *)
Definition singleton (l : Loc) (v : Val) : Heap :=
  fun l' => if Nat.eqb l l' then Some v else None.

(* Heap union (for disjoint heaps) *)
Definition heap_union (h1 h2 : Heap) : option Heap :=
  if disjoint h1 h2 then
    Some (fun l => match h1 l with
                   | Some v => Some v
                   | None => h2 l
                   end)
  else None.

(* Disjointness *)
Definition disjoint (h1 h2 : Heap) : bool :=
  true.  (* Placeholder - real impl checks domains *)

(** ===============================================================================
    SEPARATION LOGIC ASSERTIONS
    =============================================================================== *)

(* Separation logic assertion *)
Inductive assertion : Type :=
  | AEmp : assertion
  | APointsTo : Loc -> Val -> assertion
  | ASep : assertion -> assertion -> assertion
  | AWand : assertion -> assertion -> assertion
  | APure : Prop -> assertion.

(* Assertion satisfaction *)
Fixpoint satisfies (h : Heap) (a : assertion) : Prop :=
  match a with
  | AEmp => h = emp_heap
  | APointsTo l v => h = singleton l v
  | ASep a1 a2 => exists h1 h2,
      heap_union h1 h2 = Some h /\
      satisfies h1 a1 /\
      satisfies h2 a2
  | AWand a1 a2 => forall h',
      disjoint h h' = true ->
      satisfies h' a1 ->
      exists h'', heap_union h h' = Some h'' /\ satisfies h'' a2
  | APure P => P /\ h = emp_heap
  end.

Notation "l '|->' v" := (APointsTo l v) (at level 20).
Notation "P '*' Q" := (ASep P Q) (at level 40, left associativity).
Notation "'emp'" := AEmp.

(** ===============================================================================
    HOARE TRIPLES
    =============================================================================== *)

(* Command *)
Inductive cmd : Type :=
  | CAlloc : Loc -> nat -> cmd        (* alloc(loc, size) *)
  | CFree : Loc -> cmd                 (* free(loc) *)
  | CRead : Loc -> Loc -> cmd          (* read(dst, src) *)
  | CWrite : Loc -> Val -> cmd         (* write(dst, val) *)
  | CSeq : cmd -> cmd -> cmd.          (* c1; c2 *)

(* Hoare triple: {P} c {Q} *)
Definition hoare_triple (P : assertion) (c : cmd) (Q : assertion) : Prop :=
  forall h h',
    satisfies h P ->
    exec c h h' ->
    satisfies h' Q.

Notation "'{{' P '}}' c '{{' Q '}}'" := (hoare_triple P c Q).

(** ===============================================================================
    BUDDY ALLOCATOR
    =============================================================================== *)

(* Block size class (power of 2) *)
Definition SizeClass := nat.

(* Free list for each size class *)
Definition FreeList := list Loc.

(* Allocator state *)
Record AllocState : Type := mkAlloc {
  free_lists : SizeClass -> FreeList;
  allocated : Loc -> option nat;  (* loc -> size if allocated *)
  heap_start : Loc;
  heap_size : nat;
}.

(* Allocator invariant *)
Definition alloc_invariant (st : AllocState) : Prop :=
  (* All free blocks are properly sized *)
  (forall sc l, In l (free_lists st sc) -> block_size l = 2^sc) /\
  (* Free and allocated don't overlap *)
  (forall l sc, In l (free_lists st sc) ->
                allocated st l = None) /\
  (* All allocations are within bounds *)
  (forall l sz, allocated st l = Some sz ->
                l >= heap_start st /\ l + sz <= heap_start st + heap_size st).

(** ===============================================================================
    OWNERSHIP MODEL
    =============================================================================== *)

(* Ownership state *)
Inductive Ownership : Type :=
  | Owned : Ownership
  | Borrowed : nat -> Ownership     (* lifetime id *)
  | SharedBorrow : nat -> Ownership (* lifetime id *)
  | Moved : Ownership.

(* Ownership map *)
Definition OwnershipMap := Loc -> Ownership.

(* Region *)
Record Region : Type := mkRegion {
  region_id : nat;
  region_locs : list Loc;
  region_alive : bool;
}.

(** ===============================================================================
    YOUR PROOFS: W_001_01 through W_001_40
    =============================================================================== *)

(* Implement all 40 theorems here *)
```

===============================================================================================================
THEOREM SPECIFICATIONS:
===============================================================================================================

```coq
(* W_001_04: Frame rule is sound *)
Theorem sep_frame : forall P Q R c,
  {{ P }} c {{ Q }} ->
  {{ P * R }} c {{ Q * R }}.

(* W_001_11: Allocation returns fresh memory *)
Theorem alloc_fresh : forall st st' l sz,
  alloc st sz = (st', l) ->
  allocated st l = None.

(* W_001_16: Freed memory is inaccessible *)
Theorem no_use_after_free : forall st st' l,
  free st l = st' ->
  allocated st' l = None ->
  forall v, ~ {{ emp }} CRead l v {{ l |-> v }}.

(* W_001_22: Buffer overflows impossible *)
Theorem no_buffer_overflow : forall l sz idx v,
  allocated l = Some sz ->
  idx >= sz ->
  ~ {{ emp }} CWrite (l + idx) v {{ (l + idx) |-> v }}.

(* W_001_31: Ownership is unique *)
Theorem ownership_unique : forall om l,
  om l = Owned ->
  forall l', l' <> l -> om l' <> Owned \/ l <> l'.
```

===============================================================================================================
FORBIDDEN ACTIONS:
===============================================================================================================

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match W_001_01 through W_001_40
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 40 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

===============================================================================================================
VERIFICATION COMMANDS (must pass):
===============================================================================================================

```bash
coqc -Q . RIINA memory/VerifiedMemory.v
grep -c "Admitted\." memory/VerifiedMemory.v  # Must return 0
grep -c "admit\." memory/VerifiedMemory.v     # Must return 0
grep -c "^Axiom" memory/VerifiedMemory.v      # Must return 0
grep -c "^Theorem W_001" memory/VerifiedMemory.v  # Must return 40
```

===============================================================================================================
OUTPUT FORMAT:
===============================================================================================================

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* VerifiedMemory.v` and end with the final `Qed.`

MEMORY IS NOT MANAGED. MEMORY IS PROVEN.

===============================================================================================================
```
