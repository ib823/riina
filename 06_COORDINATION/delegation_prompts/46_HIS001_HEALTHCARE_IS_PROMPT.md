# DELEGATION PROMPT: HIS-001 HEALTHCARE INFORMATION SYSTEM COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: HIS-001-HEALTHCARE-IS-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — HEALTHCARE INFRASTRUCTURE
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `HealthcareIS.v` with 30 theorems (subset of ~1,150 total HIS theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-HIS, a formally verified healthcare information system.
These proofs establish that clinical operations CANNOT produce incorrect results —
medication errors, patient misidentification, and clinical data corruption are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/37_DOMAIN_RIINA_HIS/RESEARCH_HIS01_FOUNDATION.md

THIS IS THE STANDARD THAT MAKES EPIC, CERNER, MEDITECH LOOK LIKE PROTOTYPES.
THIS IS THE HEALTHCARE SYSTEM THAT ENDS ALL CLINICAL SOFTWARE ERRORS.
PATIENT SAFETY IS NOT A GOAL — IT IS A PROVEN THEOREM.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (30 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

PATIENT IDENTITY (5 theorems):
HIS_001_01: patient_identity_uniqueness — MRNs are unique
HIS_001_02: patient_matching_accuracy — Matching sensitivity >= 99.9%
HIS_001_03: duplicate_detection — Similar patients flagged for review
HIS_001_04: patient_merge_integrity — Merge preserves all records, no data loss
HIS_001_05: amendment_tracking — Amendments linked to original, timestamped

CLINICAL DOCUMENTATION (5 theorems):
HIS_001_06: encounter_completeness — Complete encounters have all SOAP elements
HIS_001_07: documentation_immutability — Signed notes cannot be modified
HIS_001_08: allergy_documentation — Allergies have allergen, reaction, severity
HIS_001_09: drug_allergy_alert — Drug-allergy interaction triggers alert
HIS_001_10: problem_list_coded — All problems have SNOMED codes

MEDICATION SAFETY (5 theorems):
HIS_001_11: five_rights_verification — Right patient/drug/dose/route/time
HIS_001_12: drug_interaction_checking — Interactions trigger severity-based alert
HIS_001_13: dose_range_checking — Dose within safe range for patient
HIS_001_14: high_alert_safeguards — High-alert meds require double-check
HIS_001_15: barcode_verification — Scan verifies match before administration

ORDER MANAGEMENT (5 theorems):
HIS_001_16: order_completeness — Orders have all required fields
HIS_001_17: order_signature — Electronic signature is legally binding
HIS_001_18: verbal_order_auth — Verbal orders authenticated within 24hrs
HIS_001_19: duplicate_order_prevention — Duplicate orders warn and require override
HIS_001_20: contraindication_alert — Contraindications trigger hard stop

LABORATORY (5 theorems):
HIS_001_21: specimen_tracking — Specimens tracked from collection to disposal
HIS_001_22: critical_value_notification — Critical values notified within 30 min
HIS_001_23: result_validation — Results auto-validated or flagged for review
HIS_001_24: delta_check — Large changes from prior flagged
HIS_001_25: reference_range_adjusted — Ranges adjusted for age/sex

COMPLIANCE (5 theorems):
HIS_001_26: phi_access_control — PHI access is role-based, minimum necessary
HIS_001_27: audit_trail_complete — All PHI access logged and reviewable
HIS_001_28: breach_notification — Breaches notified within 60 days
HIS_001_29: consent_required — Data processing requires explicit consent
HIS_001_30: data_portability — Patient data exportable in machine-readable format

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* HealthcareIS.v - RIINA-HIS Healthcare Information System Verification *)
(* Spec: 01_RESEARCH/37_DOMAIN_RIINA_HIS/RESEARCH_HIS01_FOUNDATION.md *)
(* Layer: Healthcare Infrastructure *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(** ═══════════════════════════════════════════════════════════════════════════
    PATIENT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition MRN := nat.  (* Medical Record Number *)

Record Patient : Type := mkPatient {
  mrn : MRN;
  name_hash : nat;
  dob : nat;
  demographics : nat;
}.

Record PatientMatch : Type := mkPatientMatch {
  match_score : nat;  (* 0-1000, 999 = 99.9% *)
  matched_patient : MRN;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    CLINICAL DOCUMENTATION DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record Encounter : Type := mkEncounter {
  enc_id : nat;
  enc_patient : MRN;
  chief_complaint : bool;
  history : bool;
  exam : bool;
  assessment : bool;
  plan : bool;
}.

Definition encounter_complete (e : Encounter) : Prop :=
  chief_complaint e = true /\ history e = true /\
  exam e = true /\ assessment e = true /\ plan e = true.

Record ClinicalNote : Type := mkNote {
  note_id : nat;
  note_encounter : nat;
  is_signed : bool;
  sign_timestamp : nat;
  author : nat;
}.

Record Amendment : Type := mkAmendment {
  amend_id : nat;
  original_note : nat;
  amend_timestamp : nat;
  amend_author : nat;
  marked_as_amendment : bool;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    ALLERGY DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive Severity : Type :=
  | Mild : Severity
  | Moderate : Severity
  | Severe : Severity
  | LifeThreatening : Severity.

Record Allergy : Type := mkAllergy {
  allergy_id : nat;
  allergen : nat;
  reaction_type : nat;
  severity : Severity;
  snomed_code : nat;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    MEDICATION DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record MedicationOrder : Type := mkMedOrder {
  order_id : nat;
  drug : nat;
  dose : nat;
  dose_unit : nat;
  route : nat;
  frequency : nat;
  patient_weight : nat;
  patient_age : nat;
  renal_function : nat;
}.

Record Administration : Type := mkAdmin {
  admin_id : nat;
  admin_order : nat;
  right_patient : bool;
  right_drug : bool;
  right_dose : bool;
  right_route : bool;
  right_time : bool;
  barcode_verified : bool;
}.

Definition five_rights_verified (a : Administration) : Prop :=
  right_patient a = true /\ right_drug a = true /\
  right_dose a = true /\ right_route a = true /\
  right_time a = true.

(** ═══════════════════════════════════════════════════════════════════════════
    LABORATORY DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive SpecimenStatus : Type :=
  | Collected : SpecimenStatus
  | InTransit : SpecimenStatus
  | Processing : SpecimenStatus
  | Analyzed : SpecimenStatus
  | Disposed : SpecimenStatus.

Record Specimen : Type := mkSpecimen {
  specimen_id : nat;
  specimen_patient : MRN;
  status : SpecimenStatus;
}.

Record LabResult : Type := mkLabResult {
  result_id : nat;
  result_value : nat;
  is_critical : bool;
  notification_time : option nat;
  validated : bool;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    COMPLIANCE DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive Role : Type :=
  | Physician : Role
  | Nurse : Role
  | Admin : Role
  | Patient : Role.

Record PHIAccess : Type := mkAccess {
  access_id : nat;
  accessor : nat;
  accessor_role : Role;
  accessed_patient : MRN;
  access_timestamp : nat;
  logged : bool;
}.

(* HIS_001_01 through HIS_001_30 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* HIS_001_01: Patient identity uniqueness *)
Theorem patient_identity_uniqueness : forall patients p1 p2,
  In p1 patients -> In p2 patients ->
  mrn p1 = mrn p2 -> p1 = p2.

(* HIS_001_06: Encounter completeness *)
Theorem encounter_completeness : forall e,
  finalized e -> encounter_complete e.

(* HIS_001_11: Five rights verification *)
Theorem five_rights_verification : forall a,
  administration_allowed a -> five_rights_verified a.

(* HIS_001_22: Critical value notification *)
Theorem critical_value_notification : forall r notification_time,
  is_critical r = true ->
  notification_time r = Some t ->
  t <= result_time r + 30. (* 30 minutes *)

(* HIS_001_27: Audit trail complete *)
Theorem audit_trail_complete : forall access,
  phi_accessed access -> logged access = true.
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match HIS_001_01 through HIS_001_30
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 30 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA healthcare/HealthcareIS.v
grep -c "Admitted\." healthcare/HealthcareIS.v  # Must return 0
grep -c "admit\." healthcare/HealthcareIS.v     # Must return 0
grep -c "^Axiom" healthcare/HealthcareIS.v      # Must return 0
grep -c "^Theorem HIS_001" healthcare/HealthcareIS.v  # Must return 30
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* HealthcareIS.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
