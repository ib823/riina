# DELEGATION PROMPT: COMPLY-002 PCI-DSS FINANCIAL COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: COMPLY-002-PCIDSS-FINANCIAL-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — PAYMENT CARD INDUSTRY COMPLIANCE
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `PCIDSSCompliance.v` with 15 theorems
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for PCI-DSS (Payment Card Industry Data Security Standard)
compliance for the RIINA programming language. PCI-DSS compliance is REQUIRED for any
software handling cardholder data (CHD) - credit card numbers, CVV, PIN, etc.

RESEARCH REFERENCE: 04_SPECS/industries/IND_C_FINANCIAL.md

NOTE: These proofs REPLACE the current axiom-only approach. The existing PCI axioms
must be PROVEN, not assumed.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total) - Based on PCI-DSS Requirements:
═══════════════════════════════════════════════════════════════════════════════════════════════════

COMPLY_002_01: PAN masking (display only last 4 digits: ****-****-****-1234)
COMPLY_002_02: PAN encryption (stored PAN encrypted with AES-256 or stronger)
COMPLY_002_03: CVV never stored (CVV2/CVC2 prohibited from storage)
COMPLY_002_04: PIN never stored (PIN/PIN block prohibited from storage)
COMPLY_002_05: Key management (encryption keys protected, rotated)
COMPLY_002_06: Access restricted (CHD access on need-to-know basis)
COMPLY_002_07: Unique IDs (each user with CHD access uniquely identified)
COMPLY_002_08: MFA required (multi-factor for CHD system access)
COMPLY_002_09: Audit trail (all CHD access logged with timestamp, user, action)
COMPLY_002_10: Log integrity (audit logs tamper-evident)
COMPLY_002_11: Encryption in transit (TLS 1.2+ for CHD transmission)
COMPLY_002_12: Tokenization validity (tokens cannot reverse to PAN without key)
COMPLY_002_13: Data retention (CHD deleted when no longer needed)
COMPLY_002_14: Secure deletion (deleted CHD unrecoverable)
COMPLY_002_15: Scope isolation (CHD environment segmented from other systems)

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* PCIDSSCompliance.v - PCI-DSS Compliance Proofs for RIINA *)
(* Spec: 04_SPECS/industries/IND_C_FINANCIAL.md *)
(* Requirement: PCI-DSS v4.0 *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

(* Cardholder data types *)
Inductive CHDType : Type :=
  | PAN : CHDType                 (* Primary Account Number - 16 digits *)
  | CVV : CHDType                 (* Card Verification Value - 3-4 digits *)
  | PIN : CHDType                 (* Personal Identification Number *)
  | Expiry : CHDType              (* Expiration date *)
  | CardholderName : CHDType      (* Cardholder name *)
.

(* Storage permission per PCI-DSS *)
Definition can_store (chd : CHDType) : bool :=
  match chd with
  | PAN => true           (* Yes, but encrypted *)
  | Expiry => true        (* Yes, with protection *)
  | CardholderName => true (* Yes, with protection *)
  | CVV => false          (* NEVER *)
  | PIN => false          (* NEVER *)
  end.

(* Encryption state *)
Inductive EncState : Type :=
  | Plain : EncState
  | AES128 : EncState
  | AES256 : EncState           (* Minimum for PAN *)
  | Tokenized : EncState        (* Tokenization *)
.

(* PAN display format *)
Inductive PANDisplay : Type :=
  | FullPAN : PANDisplay              (* PROHIBITED for display *)
  | MaskedPAN : PANDisplay            (* ****-****-****-1234 *)
  | TokenizedPAN : PANDisplay         (* Token reference *)
.

(* Cardholder data record *)
Record CHDRecord : Type := mkCHD {
  chd_type : CHDType;
  chd_value : nat;                    (* Abstract value *)
  chd_encryption : EncState;
  chd_display_format : PANDisplay;
}.

(* Key management *)
Record KeyState : Type := mkKey {
  key_id : nat;
  key_creation_time : nat;
  key_rotation_period : nat;          (* Typically 1 year *)
  key_protected : bool;               (* Stored in HSM or equivalent *)
}.

(* Audit entry *)
Record PCIAudit : Type := mkPCIAudit {
  pci_timestamp : nat;
  pci_user : nat;
  pci_action : nat;
  pci_chd_accessed : CHDType;
  pci_success : bool;
  pci_hash : nat;                     (* For integrity *)
}.

(* Token vault (for tokenization) *)
Record TokenVault : Type := mkVault {
  vault_tokens : list (nat * nat);    (* token -> PAN mapping *)
  vault_key : KeyState;               (* Key protecting the vault *)
  vault_isolated : bool;              (* Network segmented *)
}.

(* System state *)
Record PCISystem : Type := mkPCI {
  pci_chd_records : list CHDRecord;
  pci_audit_log : list PCIAudit;
  pci_keys : list KeyState;
  pci_vault : TokenVault;
}.

(* PCI-DSS compliant encryption *)
Definition pci_compliant_encryption (enc : EncState) (chd : CHDType) : bool :=
  match chd with
  | PAN => match enc with AES256 | Tokenized => true | _ => false end
  | CVV => false    (* Cannot be stored regardless of encryption *)
  | PIN => false    (* Cannot be stored regardless of encryption *)
  | _ => match enc with AES128 | AES256 | Tokenized => true | _ => false end
  end.

(* Display compliance *)
Definition display_compliant (disp : PANDisplay) : bool :=
  match disp with
  | FullPAN => false      (* Never display full PAN *)
  | MaskedPAN => true     (* Last 4 digits OK *)
  | TokenizedPAN => true  (* Token OK *)
  end.

(* Key rotation check *)
Definition key_needs_rotation (k : KeyState) (current_time : nat) : bool :=
  Nat.ltb (key_creation_time k + key_rotation_period k) current_time.

(* YOUR PROOFS HERE - ALL 15 THEOREMS *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match COMPLY_002_01 through COMPLY_002_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA compliance/PCIDSSCompliance.v
grep -c "Admitted\." compliance/PCIDSSCompliance.v  # Must return 0
grep -c "admit\." compliance/PCIDSSCompliance.v     # Must return 0
grep -c "^Axiom" compliance/PCIDSSCompliance.v      # Must return 0
grep -c "^Theorem COMPLY_002" compliance/PCIDSSCompliance.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* PCIDSSCompliance.v` and end with the final `Qed.`

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
