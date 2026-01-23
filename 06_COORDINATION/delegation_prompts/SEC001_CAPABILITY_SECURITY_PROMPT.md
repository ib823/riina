# DELEGATION PROMPT: SEC-001 CAPABILITY SECURITY COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: SEC-001-CAPABILITY-SECURITY-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — SECURITY FOUNDATION
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `CapabilitySecurity.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for Object-Capability (OCAP) Security for the RIINA
programming language. Capability security provides unforgeable tokens of authority,
preventing ambient authority attacks and enabling principle of least privilege.

RESEARCH REFERENCE: 01_RESEARCH/04_DOMAIN_D_CAPABILITIES/ (~3,317 lines)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

SEC_001_01: Capability unforgeability (caps cannot be created from nothing)
SEC_001_02: Capability attenuation (can only weaken, never amplify permissions)
SEC_001_03: Capability composition (combined caps ≤ union of individual caps)
SEC_001_04: Capability revocation (revoked cap cannot be used)
SEC_001_05: No ambient authority (all access requires explicit capability)
SEC_001_06: Principle of least authority (components get minimal caps needed)
SEC_001_07: Capability confinement (cap cannot escape its granted scope)
SEC_001_08: Capability facets (different views of same object)
SEC_001_09: Membrane isolation (caps crossing boundary are attenuated)
SEC_001_10: Capability delegation safety (delegated cap ≤ original cap)
SEC_001_11: Sealer/unsealer pairs (sealed data only opened with paired unsealer)
SEC_001_12: Capability caretaker (intermediary maintains authority)
SEC_001_13: Rights amplification impossible (no cap can grant more than it has)
SEC_001_14: Defensive consistency (objects behave correctly under any input)
SEC_001_15: Capability-safe encapsulation (private state inaccessible without cap)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* CapabilitySecurity.v - Object-Capability Security for RIINA *)
(* Spec: 01_RESEARCH/04_DOMAIN_D_CAPABILITIES/ *)
(* Model: Object-Capability Model (OCAP) *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Sets.Ensembles.
Import ListNotations.

(* Permission types *)
Inductive Permission : Type :=
  | PermRead : Permission
  | PermWrite : Permission
  | PermExecute : Permission
  | PermDelegate : Permission
  | PermRevoke : Permission
.

(* Permission set (as list for decidability) *)
Definition PermSet := list Permission.

(* Check permission membership *)
Definition has_perm (p : Permission) (ps : PermSet) : bool :=
  existsb (fun p' => match p, p' with
    | PermRead, PermRead => true
    | PermWrite, PermWrite => true
    | PermExecute, PermExecute => true
    | PermDelegate, PermDelegate => true
    | PermRevoke, PermRevoke => true
    | _, _ => false
  end) ps.

(* Capability *)
Record Capability : Type := mkCap {
  cap_id : nat;
  cap_object : nat;                (* Target object ID *)
  cap_permissions : PermSet;
  cap_revoked : bool;
  cap_parent : option nat;         (* Parent capability for attenuation tracking *)
}.

(* Permission subset check *)
Definition perm_subset (ps1 ps2 : PermSet) : bool :=
  forallb (fun p => has_perm p ps2) ps1.

(* Capability is valid (not revoked) *)
Definition cap_valid (c : Capability) : bool :=
  negb (cap_revoked c).

(* Capability system state *)
Record CapSystem : Type := mkCapSys {
  sys_capabilities : list Capability;
  sys_objects : list nat;              (* Object IDs *)
  sys_seals : list (nat * nat);        (* sealer_id, unsealer_id pairs *)
}.

(* Lookup capability by ID *)
Fixpoint find_cap (caps : list Capability) (id : nat) : option Capability :=
  match caps with
  | [] => None
  | c :: rest => if Nat.eqb (cap_id c) id then Some c else find_cap rest id
  end.

(* Derive (attenuate) a capability *)
Definition derive_cap (parent : Capability) (new_perms : PermSet) (new_id : nat) : option Capability :=
  if andb (cap_valid parent) (perm_subset new_perms (cap_permissions parent))
  then Some (mkCap new_id (cap_object parent) new_perms false (Some (cap_id parent)))
  else None.

(* Revoke a capability *)
Definition revoke_cap (c : Capability) : Capability :=
  mkCap (cap_id c) (cap_object c) (cap_permissions c) true (cap_parent c).

(* Sealed value *)
Record SealedValue : Type := mkSealed {
  sealed_value : nat;
  sealed_with : nat;    (* Sealer ID *)
}.

(* Unseal requires matching unsealer *)
Definition can_unseal (sv : SealedValue) (unsealer_id : nat) (sys : CapSystem) : bool :=
  existsb (fun pair => andb (Nat.eqb (fst pair) (sealed_with sv))
                            (Nat.eqb (snd pair) unsealer_id))
          (sys_seals sys).

(* Object with encapsulated state *)
Record CapObject : Type := mkObj {
  obj_id : nat;
  obj_public_state : nat;
  obj_private_state : nat;      (* Only accessible via capability *)
}.

(* Access check *)
Definition can_access (c : Capability) (obj : CapObject) (perm : Permission) : bool :=
  andb (andb (cap_valid c) (Nat.eqb (cap_object c) (obj_id obj)))
       (has_perm perm (cap_permissions c)).

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match SEC_001_01 through SEC_001_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA security/CapabilitySecurity.v
grep -c "Admitted\." security/CapabilitySecurity.v  # Must return 0
grep -c "admit\." security/CapabilitySecurity.v     # Must return 0
grep -c "^Axiom" security/CapabilitySecurity.v      # Must return 0
grep -c "^Theorem SEC_001" security/CapabilitySecurity.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* CapabilitySecurity.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
