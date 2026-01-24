# DELEGATION PROMPT: NET-001 VERIFIED NETWORK STACK COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: NET-001-VERIFIED-NETWORK-STACK-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — NETWORK LAYER (L3)
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `VerifiedNetwork.v` with 25 theorems (subset of ~400 total network theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-NET, a formally verified network stack.
These proofs establish that network protocols CANNOT be exploited — man-in-the-middle,
downgrade attacks, and protocol confusion are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/29_DOMAIN_RIINA_NET/RESEARCH_NET01_FOUNDATION.md

THIS IS THE STANDARD THAT MAKES miTLS LOOK LIKE A STUDENT PROJECT.
THIS IS THE NETWORK STACK THAT ENDS ALL PROTOCOL VULNERABILITIES.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (25 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

TLS 1.3 (10 theorems):
NET_001_01: tls_handshake_auth — TLS handshake authenticates server
NET_001_02: tls_forward_secrecy — Session keys provide forward secrecy
NET_001_03: tls_no_downgrade — Downgrade attacks are impossible
NET_001_04: tls_key_derivation — Key derivation is correct
NET_001_05: tls_transcript_binding — Transcript binds all handshake messages
NET_001_06: tls_0rtt_replay_safe — 0-RTT has replay protection
NET_001_07: tls_certificate_chain_valid — Certificate chain validation is correct
NET_001_08: tls_cipher_strength — Only strong ciphers are negotiated
NET_001_09: tls_no_truncation — Message truncation is detected
NET_001_10: tls_channel_binding — Channel binding prevents MITM

TCP/IP (8 theorems):
NET_001_11: tcp_state_machine_correct — TCP state machine is correct
NET_001_12: tcp_seq_unpredictable — Sequence numbers are unpredictable
NET_001_13: tcp_no_injection — Packet injection is detected
NET_001_14: tcp_flow_control_correct — Flow control is correct
NET_001_15: ip_frag_reassembly_safe — IP fragmentation reassembly is safe
NET_001_16: ip_no_overlapping_fragments — Overlapping fragments rejected
NET_001_17: icmp_rate_limited — ICMP responses are rate limited
NET_001_18: ip_routing_correct — IP routing is correct

DNS/DNSSEC (7 theorems):
NET_001_19: dnssec_chain_valid — DNSSEC chain of trust is valid
NET_001_20: dns_cache_safe — DNS cache is safe from poisoning
NET_001_21: dns_no_rebinding — DNS rebinding is prevented
NET_001_22: dns_query_integrity — DNS queries have integrity
NET_001_23: dns_response_authentic — DNS responses are authentic
NET_001_24: dns_no_amplification — DNS amplification is bounded
NET_001_25: doh_confidential — DNS-over-HTTPS is confidential

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* VerifiedNetwork.v - RIINA-NET Network Stack Verification *)
(* Spec: 01_RESEARCH/29_DOMAIN_RIINA_NET/RESEARCH_NET01_FOUNDATION.md *)
(* Layer: L3 Network *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ═══════════════════════════════════════════════════════════════════════════
    CRYPTOGRAPHIC PRIMITIVES
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Cryptographic types *)
Definition Key := list nat.
Definition Nonce := list nat.
Definition Ciphertext := list nat.
Definition MAC := list nat.
Definition Hash := list nat.
Definition Signature := list nat.

(* X25519 key exchange result *)
Record KEResult : Type := mkKE {
  ke_shared : Key;
  ke_ephemeral_pub : Key;
}.

(* Certificate *)
Record Certificate : Type := mkCert {
  cert_subject : string;
  cert_issuer : string;
  cert_public_key : Key;
  cert_signature : Signature;
  cert_valid_from : nat;
  cert_valid_to : nat;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    TLS 1.3 DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* TLS version *)
Inductive TLSVersion : Type :=
  | TLS_1_2 : TLSVersion
  | TLS_1_3 : TLSVersion.

(* Cipher suite *)
Inductive CipherSuite : Type :=
  | TLS_AES_128_GCM_SHA256 : CipherSuite
  | TLS_AES_256_GCM_SHA384 : CipherSuite
  | TLS_CHACHA20_POLY1305_SHA256 : CipherSuite.

(* TLS connection state *)
Record TLSConnection : Type := mkTLSConn {
  tls_version : TLSVersion;
  tls_cipher : CipherSuite;
  tls_session_key : Key;
  tls_transcript : list nat;
  tls_server_cert : Certificate;
  tls_verified : bool;
}.

(* Predicate: TLS connection established *)
Definition tls_connected (conn : TLSConnection) : Prop :=
  tls_verified conn = true /\ tls_version conn = TLS_1_3.

(** ═══════════════════════════════════════════════════════════════════════════
    TCP/IP DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* TCP state *)
Inductive TCPState : Type :=
  | CLOSED | LISTEN | SYN_SENT | SYN_RECEIVED
  | ESTABLISHED | FIN_WAIT_1 | FIN_WAIT_2
  | CLOSE_WAIT | CLOSING | LAST_ACK | TIME_WAIT.

(* TCP connection *)
Record TCPConnection : Type := mkTCPConn {
  tcp_state : TCPState;
  tcp_seq : nat;
  tcp_ack : nat;
  tcp_window : nat;
}.

(* IP packet *)
Record IPPacket : Type := mkIP {
  ip_src : nat;
  ip_dst : nat;
  ip_frag_offset : nat;
  ip_frag_more : bool;
  ip_payload : list nat;
}.

(** ═══════════════════════════════════════════════════════════════════════════
    DNS DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* DNS record types *)
Inductive DNSRecordType : Type :=
  | A | AAAA | CNAME | MX | TXT | RRSIG | DNSKEY | DS.

(* DNS record *)
Record DNSRecord : Type := mkDNS {
  dns_name : string;
  dns_type : DNSRecordType;
  dns_value : string;
  dns_ttl : nat;
  dns_signature : option Signature;
}.

(* DNSSEC validated *)
Definition dnssec_validated (r : DNSRecord) : Prop :=
  match dns_signature r with
  | Some _ => True
  | None => False
  end.

(** ═══════════════════════════════════════════════════════════════════════════
    NETWORK THEOREMS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* NET_001_01 through NET_001_25 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* NET_001_01: TLS handshake authentication *)
Theorem tls_handshake_auth : forall conn,
  tls_connected conn ->
  valid_cert_chain (tls_server_cert conn).

(* NET_001_03: TLS no downgrade *)
Theorem tls_no_downgrade : forall conn,
  tls_connected conn ->
  tls_version conn = TLS_1_3.

(* NET_001_11: TCP state machine correctness *)
Theorem tcp_state_machine_correct : forall conn event new_state,
  tcp_transition conn event new_state ->
  valid_transition (tcp_state conn) event new_state.

(* NET_001_19: DNSSEC chain validation *)
Theorem dnssec_chain_valid : forall query response,
  dnssec_validated response ->
  authentic response query.
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match NET_001_01 through NET_001_25
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 25 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA network/VerifiedNetwork.v
grep -c "Admitted\." network/VerifiedNetwork.v  # Must return 0
grep -c "admit\." network/VerifiedNetwork.v     # Must return 0
grep -c "^Axiom" network/VerifiedNetwork.v      # Must return 0
grep -c "^Theorem NET_001" network/VerifiedNetwork.v  # Must return 25
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* VerifiedNetwork.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
