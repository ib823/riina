# DELEGATION PROMPT: INFRA-001 VERIFIED CLOUD INFRASTRUCTURE COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: INFRA-001-VERIFIED-CLOUD-INFRASTRUCTURE-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — INFRASTRUCTURE LAYER (CROSS-CUTTING)
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `VerifiedInfra.v` with 25 theorems (subset of ~400 total infrastructure theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-INFRA, formally verified cloud infrastructure.
These proofs establish that infrastructure services CANNOT introduce vulnerabilities —
cache poisoning, injection attacks, and configuration errors are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/33_DOMAIN_RIINA_INFRA/RESEARCH_INFRA01_FOUNDATION.md

THIS IS THE STANDARD THAT MAKES ALL CLOUD PROVIDERS OBSOLETE.
THIS IS INFRASTRUCTURE AS PROVEN CODE.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (25 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

LOAD BALANCER (5 theorems):
INF_001_01: lb_routes_correctly — Load balancer routes to healthy backends
INF_001_02: lb_session_affinity — Session affinity is maintained
INF_001_03: lb_no_request_smuggling — Request smuggling is impossible
INF_001_04: lb_health_check_correct — Health checks are accurate
INF_001_05: lb_fair_distribution — Load is fairly distributed

DATABASE (8 theorems):
INF_001_06: db_atomicity — Transactions are atomic
INF_001_07: db_consistency — Transactions preserve consistency
INF_001_08: db_isolation — Transactions are isolated (serializable)
INF_001_09: db_durability — Committed transactions survive crashes
INF_001_10: db_no_injection — SQL/NoSQL injection is impossible
INF_001_11: db_encryption_at_rest — Data is encrypted at rest
INF_001_12: db_access_controlled — Access is capability-controlled
INF_001_13: db_audit_complete — All access is audited

MESSAGE QUEUE (5 theorems):
INF_001_14: mq_exactly_once — Messages delivered exactly once
INF_001_15: mq_ordering — Message ordering is preserved
INF_001_16: mq_no_deser_attack — Deserialization is type-safe
INF_001_17: mq_dlq_complete — Failed messages go to dead letter queue
INF_001_18: mq_backpressure — Backpressure prevents overflow

LOGGING & SECRETS (7 theorems):
INF_001_19: log_append_only — Logs are append-only
INF_001_20: log_no_injection — Log injection is impossible
INF_001_21: log_tamper_detected — Log tampering is detected
INF_001_22: secret_isolated — Secrets are isolated per service
INF_001_23: secret_rotation_safe — Key rotation maintains availability
INF_001_24: secret_expiry — Secrets expire as configured
INF_001_25: secret_audited — Secret access is audited

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* VerifiedInfra.v - RIINA-INFRA Cloud Infrastructure Verification *)
(* Spec: 01_RESEARCH/33_DOMAIN_RIINA_INFRA/RESEARCH_INFRA01_FOUNDATION.md *)
(* Layer: Cross-cutting Infrastructure *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ═══════════════════════════════════════════════════════════════════════════
    LOAD BALANCER DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Backend server *)
Record Backend : Type := mkBackend {
  backend_id : nat;
  backend_healthy : bool;
  backend_capacity : nat;
  backend_current_load : nat;
}.

(* HTTP Request *)
Record HTTPRequest : Type := mkRequest {
  req_method : string;
  req_path : string;
  req_headers : list (string * string);
  req_body : list nat;
  req_session_id : option nat;
}.

(* Load balancer state *)
Record LBState : Type := mkLB {
  lb_backends : list Backend;
  lb_session_map : nat -> option nat;  (* session -> backend *)
}.

(* Healthy backend *)
Definition healthy (b : Backend) : Prop :=
  backend_healthy b = true.

(* Has capacity *)
Definition has_capacity (b : Backend) : Prop :=
  backend_current_load b < backend_capacity b.

(* Routes to *)
Parameter routes_to : LBState -> HTTPRequest -> Backend -> Prop.

(** ═══════════════════════════════════════════════════════════════════════════
    DATABASE DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Database key-value *)
Definition Key := string.
Definition Value := list nat.

(* Database state *)
Definition DBState := Key -> option Value.

(* Transaction *)
Inductive TxnOp : Type :=
  | TxnRead : Key -> TxnOp
  | TxnWrite : Key -> Value -> TxnOp.

Record Transaction : Type := mkTxn {
  txn_id : nat;
  txn_ops : list TxnOp;
}.

(* Transaction outcome *)
Inductive TxnOutcome : Type :=
  | TxnCommit : TxnOutcome
  | TxnAbort : TxnOutcome.

(* Transaction execution *)
Parameter execute : DBState -> Transaction -> DBState * TxnOutcome.

(* Valid state (invariants hold) *)
Parameter valid_state : DBState -> Prop.

(* Committed predicate *)
Definition commits (db : DBState) (txn : Transaction) : Prop :=
  snd (execute db txn) = TxnCommit.

(* Survives crash *)
Parameter survives : Transaction -> Prop.

(** ═══════════════════════════════════════════════════════════════════════════
    MESSAGE QUEUE DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Message *)
Record Message : Type := mkMsg {
  msg_id : nat;
  msg_payload : list nat;
  msg_type : string;
}.

(* Consumer *)
Definition Consumer := nat.

(* Queue state *)
Record QueueState : Type := mkQueue {
  q_messages : list Message;
  q_delivered : list (Message * Consumer);
  q_dlq : list Message;
}.

(* Message sent *)
Definition sent (q : QueueState) (m : Message) : Prop :=
  In m (q_messages q) \/ exists c, In (m, c) (q_delivered q).

(* Message delivered *)
Definition delivered (q : QueueState) (m : Message) (c : Consumer) : Prop :=
  In (m, c) (q_delivered q).

(* Delivered count *)
Definition delivered_count (q : QueueState) (m : Message) (c : Consumer) : nat :=
  length (filter (fun p => andb (Nat.eqb (msg_id (fst p)) (msg_id m))
                                (Nat.eqb (snd p) c))
                 (q_delivered q)).

(** ═══════════════════════════════════════════════════════════════════════════
    LOGGING DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Log entry *)
Record LogEntry : Type := mkLog {
  log_timestamp : nat;
  log_level : nat;
  log_message : string;
  log_structured : bool;
  log_hash : nat;
}.

(* Log *)
Definition Log := list LogEntry.

(* Entry in log at time *)
Definition in_log (l : Log) (e : LogEntry) (t : nat) : Prop :=
  In e l /\ log_timestamp e <= t.

(* Hash chain valid *)
Fixpoint hash_chain_valid (l : Log) : Prop :=
  match l with
  | [] => True
  | [e] => True
  | e1 :: e2 :: rest =>
      log_hash e2 = log_hash e1 + 1 /\ (* Simplified hash chain *)
      hash_chain_valid (e2 :: rest)
  end.

(** ═══════════════════════════════════════════════════════════════════════════
    SECRETS MANAGEMENT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Secret *)
Record Secret : Type := mkSecret {
  secret_id : nat;
  secret_value : list nat;
  secret_created : nat;
  secret_ttl : nat;
}.

(* Service *)
Definition Service := nat.

(* Secrets store *)
Record SecretsStore : Type := mkSecrets {
  secrets : list Secret;
  access_policy : Service -> Secret -> bool;
  access_log : list (Service * Secret * nat);
}.

(* Has access *)
Definition has_access (ss : SecretsStore) (svc : Service) (sec : Secret) : Prop :=
  access_policy ss svc sec = true.

(* Can read *)
Definition can_read (ss : SecretsStore) (svc : Service) (sec : Secret) : Prop :=
  has_access ss svc sec.

(** ═══════════════════════════════════════════════════════════════════════════
    INFRASTRUCTURE THEOREMS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* INF_001_01 through INF_001_25 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* INF_001_01: Load balancer routes correctly *)
Theorem lb_routes_correctly : forall lb req b,
  routes_to lb req b ->
  healthy b /\ has_capacity b.

(* INF_001_06: ACID Atomicity *)
Theorem db_atomicity : forall db txn,
  commits db txn \/ ~ commits db txn.

(* INF_001_14: Exactly-once delivery *)
Theorem mq_exactly_once : forall q m c,
  sent q m ->
  eventually (delivered q m c) ->
  delivered_count q m c = 1.

(* INF_001_19: Append-only log *)
Theorem log_append_only : forall l e t1 t2,
  t1 < t2 ->
  in_log l e t1 ->
  in_log l e t2.
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match INF_001_01 through INF_001_25
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 25 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA infra/VerifiedInfra.v
grep -c "Admitted\." infra/VerifiedInfra.v  # Must return 0
grep -c "admit\." infra/VerifiedInfra.v     # Must return 0
grep -c "^Axiom" infra/VerifiedInfra.v      # Must return 0
grep -c "^Theorem INF_001" infra/VerifiedInfra.v  # Must return 25
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* VerifiedInfra.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
