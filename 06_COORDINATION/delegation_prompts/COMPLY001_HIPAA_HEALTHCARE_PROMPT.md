# DELEGATION PROMPT: COMPLY-001 HIPAA HEALTHCARE COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: COMPLY-001-HIPAA-HEALTHCARE-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — REGULATORY COMPLIANCE
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `HIPAACompliance.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for HIPAA (Health Insurance Portability and Accountability Act)
compliance for the RIINA programming language. HIPAA compliance is LEGALLY REQUIRED for
healthcare software handling PHI (Protected Health Information).

RESEARCH REFERENCE: 04_SPECS/industries/IND_B_HEALTHCARE.md

NOTE: These proofs REPLACE the current axiom-only approach. The existing axioms
(hipaa_phi_encrypted, hipaa_access_logged, etc.) must be PROVEN, not assumed.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

COMPLY_001_01: PHI encryption at rest (all PHI stored encrypted with AES-256)
COMPLY_001_02: PHI encryption in transit (all PHI transmitted via TLS 1.3)
COMPLY_001_03: Access control enforcement (role-based access to PHI)
COMPLY_001_04: Audit logging completeness (all PHI access logged immutably)
COMPLY_001_05: Minimum necessary rule (access limited to needed PHI only)
COMPLY_001_06: Patient consent tracking (disclosure requires documented consent)
COMPLY_001_07: Breach detection (unauthorized access detected within 24 hours)
COMPLY_001_08: Data integrity (PHI cannot be modified without authorization)
COMPLY_001_09: Secure disposal (deleted PHI unrecoverable)
COMPLY_001_10: Authentication strength (MFA required for PHI access)
COMPLY_001_11: Session timeout (inactive sessions terminated)
COMPLY_001_12: Automatic logoff (workstation locks after inactivity)
COMPLY_001_13: Unique user identification (each user uniquely identified)
COMPLY_001_14: Emergency access procedure (break-glass with full audit)
COMPLY_001_15: Transmission security (integrity and confidentiality verified)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* HIPAACompliance.v - HIPAA Compliance Proofs for RIINA *)
(* Spec: 04_SPECS/industries/IND_B_HEALTHCARE.md *)
(* Legal Requirement: 45 CFR Parts 160, 162, 164 *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(* User roles *)
Inductive Role : Type :=
  | Physician : Role
  | Nurse : Role
  | Admin : Role
  | Patient : Role
  | Auditor : Role
  | Emergency : Role
.

(* PHI categories *)
Inductive PHICategory : Type :=
  | Demographics : PHICategory
  | MedicalHistory : PHICategory
  | Diagnosis : PHICategory
  | Treatment : PHICategory
  | Billing : PHICategory
  | Genetic : PHICategory
.

(* Encryption state *)
Inductive EncryptionState : Type :=
  | Plaintext : EncryptionState
  | EncryptedAES128 : EncryptionState
  | EncryptedAES256 : EncryptionState       (* Required for HIPAA *)
.

(* Transport security *)
Inductive TransportSecurity : Type :=
  | NoTLS : TransportSecurity
  | TLS12 : TransportSecurity
  | TLS13 : TransportSecurity               (* Required *)
.

(* PHI record *)
Record PHIRecord : Type := mkPHI {
  phi_category : PHICategory;
  phi_patient_id : nat;
  phi_data : nat;                           (* Abstract data *)
  phi_encryption : EncryptionState;
  phi_consent_documented : bool;
}.

(* Audit log entry *)
Record AuditEntry : Type := mkAudit {
  audit_timestamp : nat;
  audit_user_id : nat;
  audit_action : nat;                       (* 0=read, 1=write, 2=delete *)
  audit_phi_id : nat;
  audit_success : bool;
}.

(* System state *)
Record SystemState : Type := mkState {
  state_phi_records : list PHIRecord;
  state_audit_log : list AuditEntry;
  state_active_sessions : list (nat * nat); (* user_id, last_activity *)
  state_user_roles : list (nat * Role);
}.

(* Role-based access control *)
Definition can_access (role : Role) (cat : PHICategory) : bool :=
  match role, cat with
  | Physician, _ => true
  | Nurse, Demographics => true
  | Nurse, MedicalHistory => true
  | Nurse, Treatment => true
  | Admin, Demographics => true
  | Admin, Billing => true
  | Patient, Demographics => true  (* Own only - simplified *)
  | Auditor, _ => true             (* Read-only audit access *)
  | Emergency, _ => true           (* Break-glass *)
  | _, _ => false
  end.

(* Encryption check *)
Definition is_hipaa_encrypted (enc : EncryptionState) : bool :=
  match enc with
  | EncryptedAES256 => true
  | _ => false
  end.

(* Transport check *)
Definition is_hipaa_transport (ts : TransportSecurity) : bool :=
  match ts with
  | TLS13 => true
  | _ => false
  end.

(* Session timeout (300 seconds = 5 minutes for healthcare) *)
Definition session_timeout : nat := 300.

Definition session_expired (current_time last_activity : nat) : bool :=
  Nat.ltb session_timeout (current_time - last_activity).

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
CRITICAL NOTE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

These proofs must show that the RIINA type system ENFORCES HIPAA requirements by construction.
For example:
- A type `PHI<encrypted=AES256>` cannot be stored without encryption
- A type `AuditedAccess<PHI>` cannot be accessed without creating an audit log entry
- Session types ensure timeout compliance

The proofs demonstrate that HIPAA violations are TYPE ERRORS in RIINA.

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match COMPLY_001_01 through COMPLY_001_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA compliance/HIPAACompliance.v
grep -c "Admitted\." compliance/HIPAACompliance.v  # Must return 0
grep -c "admit\." compliance/HIPAACompliance.v     # Must return 0
grep -c "^Axiom" compliance/HIPAACompliance.v      # Must return 0
grep -c "^Theorem COMPLY_001" compliance/HIPAACompliance.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* HIPAACompliance.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
