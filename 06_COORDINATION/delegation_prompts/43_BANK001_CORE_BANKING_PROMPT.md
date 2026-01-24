# DELEGATION PROMPT: BANK-001 CORE BANKING COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: BANK-001-CORE-BANKING-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — FINANCIAL INFRASTRUCTURE
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `CoreBanking.v` with 30 theorems (subset of ~760 total banking theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-BANK, a formally verified core banking system.
These proofs establish that banking operations CANNOT produce incorrect results —
balance inconsistencies, double-spending, and transaction integrity violations are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/34_DOMAIN_RIINA_BANK/RESEARCH_BANK01_FOUNDATION.md

THIS IS THE STANDARD THAT MAKES TEMENOS, FINASTRA, TCS BANCS LOOK LIKE PROTOTYPES.
THIS IS THE BANKING SYSTEM THAT ENDS ALL BANKING SYSTEM VULNERABILITIES.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (30 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

CUSTOMER INFORMATION (5 theorems):
BANK_001_01: customer_identity_uniqueness — Customer IDs are unique
BANK_001_02: kyc_completeness — Onboarded customers have complete KYC
BANK_001_03: beneficial_ownership_complete — UBOs sum to 100%
BANK_001_04: sanctions_check_mandatory — All parties screened before transactions
BANK_001_05: pep_enhanced_monitoring — PEP customers have enhanced due diligence

DEPOSITS (5 theorems):
BANK_001_06: balance_non_negative — Savings accounts cannot go negative
BANK_001_07: interest_calculation_precise — Interest calculated with exact precision
BANK_001_08: double_entry_invariant — Debits always equal credits
BANK_001_09: term_deposit_lock — Early withdrawal incurs penalty
BANK_001_10: dormancy_detection — Inactive accounts marked dormant

LOANS (5 theorems):
BANK_001_11: loan_within_eligibility — Approved amount within calculated limit
BANK_001_12: collateral_coverage — Secured loans have sufficient collateral
BANK_001_13: amortization_correctness — EMI schedule sums to principal
BANK_001_14: covenant_monitoring — Covenant breach triggers event of default
BANK_001_15: facility_limit_enforcement — Drawdowns within sanctioned limit

PAYMENTS (5 theorems):
BANK_001_16: instant_payment_completion — Instant payments complete within SLA
BANK_001_17: payment_irrevocability — Credited payments are final
BANK_001_18: idempotency — Duplicate requests execute once
BANK_001_19: nostro_reconciliation — Internal and external balances match
BANK_001_20: swift_message_validation — SWIFT messages are schema-valid

TREASURY (5 theorems):
BANK_001_21: fx_spot_settlement — Spot trades settle T+2
BANK_001_22: repo_collateral_haircut — Repo cash reflects haircut
BANK_001_23: bond_accrued_interest — Accrued interest calculated correctly
BANK_001_24: derivative_valuation — IRS NPV calculated correctly
BANK_001_25: collateral_call_trigger — MTM beyond threshold triggers call

ISLAMIC BANKING (5 theorems):
BANK_001_26: murabaha_cost_plus — Selling price = cost + profit, disclosed
BANK_001_27: ijarah_ownership — Bank retains ownership during tenure
BANK_001_28: musharakah_profit_loss — Profit by ratio, loss by capital
BANK_001_29: sukuk_asset_backing — Sukuk backed by tangible assets
BANK_001_30: shariah_no_riba — No interest-based transactions

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* CoreBanking.v - RIINA-BANK Core Banking Verification *)
(* Spec: 01_RESEARCH/34_DOMAIN_RIINA_BANK/RESEARCH_BANK01_FOUNDATION.md *)
(* Layer: Financial Infrastructure *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope Z_scope.

(** ═══════════════════════════════════════════════════════════════════════════
    CUSTOMER DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition CustomerId := nat.

Record Customer : Type := mkCustomer {
  customer_id : CustomerId;
  kyc_verified : bool;
  address_verified : bool;
  risk_assessed : bool;
  pep_screened : bool;
  sanctions_screened : bool;
  is_pep : bool;
}.

Definition kyc_complete (c : Customer) : Prop :=
  kyc_verified c = true /\ address_verified c = true /\
  risk_assessed c = true /\ pep_screened c = true /\
  sanctions_screened c = true.

(** ═══════════════════════════════════════════════════════════════════════════
    ACCOUNT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive AccountType : Type :=
  | Savings : AccountType
  | Current : AccountType
  | TermDeposit : AccountType.

Record Account : Type := mkAccount {
  account_id : nat;
  account_type : AccountType;
  balance : Z;
  owner : CustomerId;
  is_dormant : bool;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    TRANSACTION DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record JournalEntry : Type := mkJournalEntry {
  debit_account : nat;
  credit_account : nat;
  amount : Z;
  timestamp : nat;
}.

Definition debits (entries : list JournalEntry) : Z :=
  fold_left (fun acc e => acc + amount e) entries 0.

Definition credits (entries : list JournalEntry) : Z :=
  fold_left (fun acc e => acc + amount e) entries 0.

(** ═══════════════════════════════════════════════════════════════════════════
    LOAN DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record Loan : Type := mkLoan {
  loan_id : nat;
  borrower : CustomerId;
  principal : Z;
  collateral_value : Z;
  ltv_ratio : Z;  (* In basis points, e.g., 8000 = 80% *)
}.

Record Installment : Type := mkInstallment {
  inst_principal : Z;
  inst_interest : Z;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    PAYMENT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive PaymentStatus : Type :=
  | Pending : PaymentStatus
  | Completed : PaymentStatus
  | Failed : PaymentStatus.

Record Payment : Type := mkPayment {
  payment_id : nat;
  payment_amount : Z;
  status : PaymentStatus;
  idempotency_key : nat;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    ISLAMIC BANKING DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record Murabaha : Type := mkMurabaha {
  murabaha_cost : Z;
  murabaha_profit : Z;
  profit_disclosed : bool;
}.

Definition murabaha_selling_price (m : Murabaha) : Z :=
  murabaha_cost m + murabaha_profit m.

(* BANK_001_01 through BANK_001_30 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* BANK_001_01: Customer identity uniqueness *)
Theorem customer_identity_uniqueness : forall customers c1 c2,
  In c1 customers -> In c2 customers ->
  customer_id c1 = customer_id c2 -> c1 = c2.

(* BANK_001_06: Balance non-negative for savings *)
Theorem balance_non_negative : forall a,
  account_type a = Savings -> balance a >= 0.

(* BANK_001_08: Double-entry invariant *)
Theorem double_entry_invariant : forall entries,
  valid_entries entries -> debits entries = credits entries.

(* BANK_001_18: Idempotency *)
Theorem idempotency : forall p1 p2 executed,
  idempotency_key p1 = idempotency_key p2 ->
  In p1 executed -> In p2 executed -> p1 = p2.

(* BANK_001_26: Murabaha cost plus profit *)
Theorem murabaha_cost_plus : forall m,
  profit_disclosed m = true ->
  murabaha_selling_price m = murabaha_cost m + murabaha_profit m.
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match BANK_001_01 through BANK_001_30
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 30 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA banking/CoreBanking.v
grep -c "Admitted\." banking/CoreBanking.v  # Must return 0
grep -c "admit\." banking/CoreBanking.v     # Must return 0
grep -c "^Axiom" banking/CoreBanking.v      # Must return 0
grep -c "^Theorem BANK_001" banking/CoreBanking.v  # Must return 30
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* CoreBanking.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
