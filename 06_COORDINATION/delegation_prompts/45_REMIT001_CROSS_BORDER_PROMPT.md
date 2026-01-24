# DELEGATION PROMPT: REMIT-001 CROSS-BORDER REMITTANCE COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: REMIT-001-CROSS-BORDER-REMITTANCE-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — FINANCIAL INFRASTRUCTURE
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `CrossBorderRemittance.v` with 25 theorems (subset of ~465 total remittance theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-REMIT, a formally verified cross-border remittance system.
These proofs establish that remittance operations CANNOT produce incorrect results —
FX manipulation, hidden fees, and settlement failures are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/36_DOMAIN_RIINA_REMIT/RESEARCH_REMIT01_FOUNDATION.md

THIS IS THE STANDARD THAT MAKES WISE, AIRWALLEX, WESTERN UNION LOOK LIKE PROTOTYPES.
THIS IS THE REMITTANCE SYSTEM THAT ENDS ALL CROSS-BORDER PAYMENT INEFFICIENCIES.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (25 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

CORRIDOR MANAGEMENT (5 theorems):
REMIT_001_01: universal_coverage — All UN member states supported
REMIT_001_02: currency_support — All ISO 4217 currencies supported
REMIT_001_03: pricing_transparency — All fees disclosed upfront
REMIT_001_04: corridor_availability — 99.99% uptime per corridor
REMIT_001_05: sanctioned_country_blocking — Sanctioned countries blocked

FX ENGINE (5 theorems):
REMIT_001_06: rate_freshness — Rate staleness <= 1 second
REMIT_001_07: spread_transparency — Customer rate = mid-market + disclosed spread
REMIT_001_08: rate_lock_guarantee — Locked rate valid for guarantee window
REMIT_001_09: no_hidden_margin — Total cost = stated fee + stated spread only
REMIT_001_10: hedge_ratio_maintenance — Hedge ratio in [98%, 102%]

PAYMENT RAILS (5 theorems):
REMIT_001_11: swift_gpi_tracking — End-to-end tracking for SWIFT payments
REMIT_001_12: instant_rail_settlement — Instant rails settle within seconds
REMIT_001_13: blockchain_atomic_execution — Bridge transfers are atomic
REMIT_001_14: mobile_money_instant — Mobile money credits instantly
REMIT_001_15: local_rail_integration — Last-mile via local rails

COMPLIANCE (5 theorems):
REMIT_001_16: realtime_screening — Screening before execution, < 500ms
REMIT_001_17: sanctions_screening_complete — All sanctions lists checked
REMIT_001_18: travel_rule_compliance — Originator/beneficiary info transmitted
REMIT_001_19: str_filing — Suspicious activity reported within deadline
REMIT_001_20: kyc_verification — Identity verified at onboarding

PAYOUT (5 theorems):
REMIT_001_21: instant_bank_credit — Instant rail = credit within seconds
REMIT_001_22: wallet_instant_credit — Wallet credit is instant
REMIT_001_23: cash_pickup_security — Secure random pickup code, 16 digits
REMIT_001_24: iban_validation — IBAN checksum and format validated
REMIT_001_25: recipient_notification — Recipient notified via preferred channel

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* CrossBorderRemittance.v - RIINA-REMIT Cross-Border Verification *)
(* Spec: 01_RESEARCH/36_DOMAIN_RIINA_REMIT/RESEARCH_REMIT01_FOUNDATION.md *)
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
    CORRIDOR DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition CountryCode := nat.  (* ISO 3166-1 numeric *)
Definition CurrencyCode := nat. (* ISO 4217 numeric *)

Record Corridor : Type := mkCorridor {
  send_country : CountryCode;
  receive_country : CountryCode;
  send_currency : CurrencyCode;
  receive_currency : CurrencyCode;
  is_enabled : bool;
  availability_pct : nat;  (* In basis points: 9999 = 99.99% *)
}.

Definition un_member_states : list CountryCode :=
  (* 193 UN member states - placeholder *)
  seq 1 193.

Definition iso_4217_currencies : list CurrencyCode :=
  (* Active ISO 4217 currencies - placeholder *)
  seq 1 180.

(** ═══════════════════════════════════════════════════════════════════════════
    FX DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record FXQuote : Type := mkFXQuote {
  quote_id : nat;
  mid_market_rate : Z;  (* In smallest unit, e.g., pips *)
  spread : Z;
  customer_rate : Z;
  quote_timestamp : nat;
  guarantee_window : nat;  (* Seconds *)
}.

Definition rate_staleness (q : FXQuote) (current_time : nat) : nat :=
  current_time - quote_timestamp q.

(** ═══════════════════════════════════════════════════════════════════════════
    PAYMENT RAIL DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive PaymentRail : Type :=
  | SWIFT : PaymentRail
  | SEPA_Instant : PaymentRail
  | FasterPayments : PaymentRail
  | RTP : PaymentRail
  | Blockchain : PaymentRail
  | MobileMoney : PaymentRail
  | LocalACH : PaymentRail.

Record Transfer : Type := mkTransfer {
  transfer_id : nat;
  rail : PaymentRail;
  send_amount : Z;
  receive_amount : Z;
  stated_fee : Z;
  stated_spread : Z;
  screening_passed : bool;
  tracking_available : bool;
}.

Definition is_instant_rail (r : PaymentRail) : bool :=
  match r with
  | SWIFT => false
  | SEPA_Instant => true
  | FasterPayments => true
  | RTP => true
  | Blockchain => true
  | MobileMoney => true
  | LocalACH => false
  end.

(** ═══════════════════════════════════════════════════════════════════════════
    COMPLIANCE DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record Beneficiary : Type := mkBeneficiary {
  ben_id : nat;
  ben_name : nat;  (* Hash of name *)
  ofac_screened : bool;
  un_screened : bool;
  eu_screened : bool;
  local_screened : bool;
}.

Definition fully_screened (b : Beneficiary) : Prop :=
  ofac_screened b = true /\ un_screened b = true /\
  eu_screened b = true /\ local_screened b = true.

(** ═══════════════════════════════════════════════════════════════════════════
    PAYOUT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record CashPickup : Type := mkCashPickup {
  pickup_code : nat;
  code_length : nat;
  expiry_days : nat;
}.

Definition secure_pickup_code (cp : CashPickup) : Prop :=
  code_length cp = 16 /\ expiry_days cp <= 30.

(* REMIT_001_01 through REMIT_001_25 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* REMIT_001_01: Universal coverage *)
Theorem universal_coverage : forall c,
  In c un_member_states ->
  send_enabled c \/ receive_enabled c.

(* REMIT_001_07: Spread transparency *)
Theorem spread_transparency : forall q,
  valid_quote q ->
  customer_rate q = mid_market_rate q + spread q.

(* REMIT_001_09: No hidden margin *)
Theorem no_hidden_margin : forall t,
  valid_transfer t ->
  total_cost t = stated_fee t + stated_spread t.

(* REMIT_001_17: Sanctions screening complete *)
Theorem sanctions_screening_complete : forall b,
  transfer_allowed b -> fully_screened b.

(* REMIT_001_23: Cash pickup security *)
Theorem cash_pickup_security : forall cp,
  valid_cash_pickup cp -> secure_pickup_code cp.
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match REMIT_001_01 through REMIT_001_25
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 25 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA remittance/CrossBorderRemittance.v
grep -c "Admitted\." remittance/CrossBorderRemittance.v  # Must return 0
grep -c "admit\." remittance/CrossBorderRemittance.v     # Must return 0
grep -c "^Axiom" remittance/CrossBorderRemittance.v      # Must return 0
grep -c "^Theorem REMIT_001" remittance/CrossBorderRemittance.v  # Must return 25
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* CrossBorderRemittance.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
