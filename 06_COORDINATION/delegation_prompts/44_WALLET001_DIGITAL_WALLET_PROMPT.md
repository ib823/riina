# DELEGATION PROMPT: WALLET-001 DIGITAL WALLET COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: WALLET-001-DIGITAL-WALLET-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — FINANCIAL INFRASTRUCTURE
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `DigitalWallet.v` with 25 theorems (subset of ~515 total wallet theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-WALLET, a formally verified digital wallet system.
These proofs establish that wallet operations CANNOT produce incorrect results —
balance inconsistencies, unauthorized transactions, and double-spending are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/35_DOMAIN_RIINA_WALLET/RESEARCH_WALLET01_FOUNDATION.md

THIS IS THE STANDARD THAT MAKES PAYPAL, ALIPAY, GRABPAY LOOK LIKE PROTOTYPES.
THIS IS THE DIGITAL WALLET THAT ENDS ALL WALLET SECURITY VULNERABILITIES.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (25 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

ACCOUNT MANAGEMENT (5 theorems):
WALLET_001_01: account_uniqueness — Wallet IDs are unique
WALLET_001_02: balance_integrity — Balance = sum(credits) - sum(debits)
WALLET_001_03: tier_limit_enforcement — Transaction limits per tier enforced
WALLET_001_04: virtual_account_segregation — Virtual accounts within parent balance
WALLET_001_05: dormancy_detection — Inactive wallets marked dormant

PAYMENTS (5 theorems):
WALLET_001_06: p2p_instant_settlement — P2P transfer completes within 1 second
WALLET_001_07: qr_payment_instant — QR payment completes within 3 seconds
WALLET_001_08: dynamic_qr_single_use — Used dynamic QR is invalidated
WALLET_001_09: merchant_settlement — Merchant receives net after MDR
WALLET_001_10: refund_instant — Merchant refund credits instantly

TOP-UP (5 theorems):
WALLET_001_11: bank_transfer_reconciliation — Credit matches bank debit
WALLET_001_12: card_chargeback_handling — Chargeback debits wallet
WALLET_001_13: agent_float_sufficiency — Agent float covers pending deposits
WALLET_001_14: crypto_rate_lock — Crypto rate locked at confirmation time
WALLET_001_15: stablecoin_instant_credit — Stablecoin confirms instantly

WITHDRAWAL (5 theorems):
WALLET_001_16: withdrawal_limit_enforcement — Daily limit enforced
WALLET_001_17: bank_withdrawal_ownership — Bank account ownership verified first
WALLET_001_18: cardless_atm_otp_validity — OTP valid for 15 minutes
WALLET_001_19: agent_cash_availability — Agent has cash before approval
WALLET_001_20: withdrawal_balance_check — Cannot withdraw more than balance

SECURITY (5 theorems):
WALLET_001_21: multi_factor_required — Sensitive operations require 2FA
WALLET_001_22: session_expiry — Sessions expire after inactivity
WALLET_001_23: velocity_check — High velocity triggers review
WALLET_001_24: fraud_score_blocking — High fraud score blocks transaction
WALLET_001_25: device_binding — Biometrics are device-specific

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* DigitalWallet.v - RIINA-WALLET Digital Wallet Verification *)
(* Spec: 01_RESEARCH/35_DOMAIN_RIINA_WALLET/RESEARCH_WALLET01_FOUNDATION.md *)
(* Layer: Financial Infrastructure *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope Z_scope.

(** ═══════════════════════════════════════════════════════════════════════════
    WALLET DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition WalletId := nat.

Inductive WalletTier : Type :=
  | Basic : WalletTier
  | Standard : WalletTier
  | Premium : WalletTier
  | Unlimited : WalletTier.

Record Wallet : Type := mkWallet {
  wallet_id : WalletId;
  balance : Z;
  tier : WalletTier;
  is_dormant : bool;
  last_activity : nat;
}.

Definition tier_limit (t : WalletTier) : Z :=
  match t with
  | Basic => 200
  | Standard => 5000
  | Premium => 20000
  | Unlimited => 1000000000  (* Effectively unlimited *)
  end.

(** ═══════════════════════════════════════════════════════════════════════════
    TRANSACTION DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive TransactionType : Type :=
  | Credit : TransactionType
  | Debit : TransactionType.

Record Transaction : Type := mkTransaction {
  txn_id : nat;
  txn_type : TransactionType;
  txn_amount : Z;
  txn_wallet : WalletId;
  txn_timestamp : nat;
}.

Definition sum_credits (txns : list Transaction) : Z :=
  fold_left (fun acc t =>
    match txn_type t with
    | Credit => acc + txn_amount t
    | Debit => acc
    end) txns 0.

Definition sum_debits (txns : list Transaction) : Z :=
  fold_left (fun acc t =>
    match txn_type t with
    | Debit => acc + txn_amount t
    | Credit => acc
    end) txns 0.

(** ═══════════════════════════════════════════════════════════════════════════
    QR CODE DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Inductive QRType : Type :=
  | StaticQR : QRType
  | DynamicQR : QRType.

Record QRCode : Type := mkQRCode {
  qr_id : nat;
  qr_type : QRType;
  qr_used : bool;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    SECURITY DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

Record Session : Type := mkSession {
  session_id : nat;
  session_wallet : WalletId;
  session_start : nat;
  last_activity_time : nat;
  inactivity_timeout : nat;
}.

Definition session_expired (s : Session) (current_time : nat) : bool :=
  (inactivity_timeout s + last_activity_time s) <? current_time.

(* WALLET_001_01 through WALLET_001_25 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* WALLET_001_01: Account uniqueness *)
Theorem account_uniqueness : forall wallets w1 w2,
  In w1 wallets -> In w2 wallets ->
  wallet_id w1 = wallet_id w2 -> w1 = w2.

(* WALLET_001_02: Balance integrity *)
Theorem balance_integrity : forall w txns,
  valid_wallet w txns ->
  balance w = sum_credits txns - sum_debits txns.

(* WALLET_001_08: Dynamic QR single use *)
Theorem dynamic_qr_single_use : forall qr,
  qr_type qr = DynamicQR ->
  qr_used qr = true ->
  invalidated qr.

(* WALLET_001_20: Withdrawal balance check *)
Theorem withdrawal_balance_check : forall w amount,
  can_withdraw w amount -> amount <= balance w.

(* WALLET_001_22: Session expiry *)
Theorem session_expiry : forall s current_time,
  session_expired s current_time = true ->
  ~ session_valid s current_time.
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match WALLET_001_01 through WALLET_001_25
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 25 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA wallet/DigitalWallet.v
grep -c "Admitted\." wallet/DigitalWallet.v  # Must return 0
grep -c "admit\." wallet/DigitalWallet.v     # Must return 0
grep -c "^Axiom" wallet/DigitalWallet.v      # Must return 0
grep -c "^Theorem WALLET_001" wallet/DigitalWallet.v  # Must return 25
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* DigitalWallet.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
