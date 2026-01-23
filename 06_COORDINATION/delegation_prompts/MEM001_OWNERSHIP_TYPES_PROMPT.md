# DELEGATION PROMPT: MEM-001 OWNERSHIP TYPES COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: MEM-001-OWNERSHIP-TYPES-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — MEMORY SAFETY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `OwnershipTypes.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Ownership Types (Rust-style borrow checking) for RIINA.
Ownership types prevent use-after-free, double-free, and dangling pointer bugs by
enforcing exclusive ownership and borrowing rules at compile time.

RESEARCH REFERENCE: 01_RESEARCH/23_DOMAIN_W_VERIFIED_MEMORY/ (~580 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

MEM_001_01: Ownership uniqueness (at most one owner at any time)
MEM_001_02: Ownership transfer (move semantics invalidate source)
MEM_001_03: Shared borrow allows multiple readers
MEM_001_04: Mutable borrow is exclusive (no other borrows)
MEM_001_05: Borrows cannot outlive owner
MEM_001_06: No use after move
MEM_001_07: No mutable borrow while shared borrow exists
MEM_001_08: No shared borrow while mutable borrow exists
MEM_001_09: Reborrow shortens lifetime
MEM_001_10: Drop called exactly once (no double-free)
MEM_001_11: No dangling references (lifetime safety)
MEM_001_12: Interior mutability (RefCell) runtime checked
MEM_001_13: Copy types don't transfer ownership
MEM_001_14: Box heap allocation and deallocation paired
MEM_001_15: Memory safety (no UB from ownership violations)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* OwnershipTypes.v - Ownership Types for RIINA *)
(* Spec: 01_RESEARCH/23_DOMAIN_W_VERIFIED_MEMORY/ *)
(* Model: Rust-style ownership and borrowing *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Lifetime (represented as natural number, larger = longer) *)
Definition Lifetime := nat.

(* Lifetime ordering *)
Definition lifetime_outlives (l1 l2 : Lifetime) : bool :=
  Nat.leb l2 l1.  (* l1 outlives l2 if l1 >= l2 *)

(* Ownership state *)
Inductive OwnState : Type :=
  | Owned : OwnState                          (* Exclusively owned *)
  | Moved : OwnState                          (* Ownership transferred *)
  | Borrowed : Lifetime -> OwnState           (* Immutably borrowed *)
  | MutBorrowed : Lifetime -> OwnState        (* Mutably borrowed *)
  | Dropped : OwnState                        (* Deallocated *)
.

(* Variable with ownership *)
Record OwnedVar : Type := mkOV {
  ov_id : nat;
  ov_state : OwnState;
  ov_lifetime : Lifetime;           (* Scope lifetime *)
  ov_is_copy : bool;                (* Copy type? *)
}.

(* Borrow record *)
Record Borrow : Type := mkBorrow {
  br_source : nat;                  (* Source variable ID *)
  br_target : nat;                  (* Borrow variable ID *)
  br_mutable : bool;                (* Mutable borrow? *)
  br_lifetime : Lifetime;           (* Borrow lifetime *)
}.

(* Ownership context *)
Record OwnCtx : Type := mkOC {
  oc_vars : list OwnedVar;
  oc_borrows : list Borrow;
  oc_current_lifetime : Lifetime;
}.

(* Find variable by ID *)
Fixpoint find_var (vars : list OwnedVar) (id : nat) : option OwnedVar :=
  match vars with
  | [] => None
  | v :: rest => if Nat.eqb (ov_id v) id then Some v else find_var rest id
  end.

(* Check if variable is usable (owned and not moved/dropped) *)
Definition is_usable (v : OwnedVar) : bool :=
  match ov_state v with
  | Owned => true
  | Borrowed _ => true
  | MutBorrowed _ => true
  | Moved => false
  | Dropped => false
  end.

(* Check if variable can be mutably borrowed *)
Definition can_mut_borrow (ctx : OwnCtx) (id : nat) : bool :=
  match find_var (oc_vars ctx) id with
  | None => false
  | Some v =>
    match ov_state v with
    | Owned => negb (existsb (fun b => Nat.eqb (br_source b) id) (oc_borrows ctx))
    | _ => false
    end
  end.

(* Check if variable can be immutably borrowed *)
Definition can_shared_borrow (ctx : OwnCtx) (id : nat) : bool :=
  match find_var (oc_vars ctx) id with
  | None => false
  | Some v =>
    match ov_state v with
    | Owned => negb (existsb (fun b => andb (Nat.eqb (br_source b) id) (br_mutable b))
                             (oc_borrows ctx))
    | Borrowed _ => true  (* Can reborrow *)
    | _ => false
    end
  end.

(* Count active borrows for a variable *)
Definition count_borrows (ctx : OwnCtx) (id : nat) : nat :=
  length (filter (fun b => Nat.eqb (br_source b) id) (oc_borrows ctx)).

(* Count mutable borrows for a variable *)
Definition count_mut_borrows (ctx : OwnCtx) (id : nat) : nat :=
  length (filter (fun b => andb (Nat.eqb (br_source b) id) (br_mutable b))
                 (oc_borrows ctx)).

(* Move ownership *)
Definition move_var (ctx : OwnCtx) (from_id to_id : nat) : option OwnCtx :=
  match find_var (oc_vars ctx) from_id with
  | None => None
  | Some v =>
    if ov_is_copy v then
      (* Copy: don't invalidate source *)
      Some ctx
    else
      match ov_state v with
      | Owned =>
        (* Mark source as moved, create new owned var *)
        let updated := map (fun var =>
          if Nat.eqb (ov_id var) from_id
          then mkOV from_id Moved (ov_lifetime var) (ov_is_copy var)
          else var
        ) (oc_vars ctx) in
        let new_var := mkOV to_id Owned (oc_current_lifetime ctx) (ov_is_copy v) in
        Some (mkOC (new_var :: updated) (oc_borrows ctx) (oc_current_lifetime ctx))
      | _ => None  (* Can't move if not owned *)
      end
  end.

(* Drop variable *)
Definition drop_var (ctx : OwnCtx) (id : nat) : option OwnCtx :=
  match find_var (oc_vars ctx) id with
  | None => None
  | Some v =>
    match ov_state v with
    | Owned =>
      let updated := map (fun var =>
        if Nat.eqb (ov_id var) id
        then mkOV id Dropped (ov_lifetime var) (ov_is_copy var)
        else var
      ) (oc_vars ctx) in
      Some (mkOC updated (oc_borrows ctx) (oc_current_lifetime ctx))
    | _ => None  (* Can only drop owned *)
    end
  end.

(* Check borrow lifetime validity *)
Definition borrow_lifetime_valid (ctx : OwnCtx) (b : Borrow) : bool :=
  match find_var (oc_vars ctx) (br_source b) with
  | None => false
  | Some v => lifetime_outlives (ov_lifetime v) (br_lifetime b)
  end.

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match MEM_001_01 through MEM_001_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA memory/OwnershipTypes.v
grep -c "Admitted\." memory/OwnershipTypes.v  # Must return 0
grep -c "admit\." memory/OwnershipTypes.v     # Must return 0
grep -c "^Axiom" memory/OwnershipTypes.v      # Must return 0
grep -c "^Theorem MEM_001" memory/OwnershipTypes.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* OwnershipTypes.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
