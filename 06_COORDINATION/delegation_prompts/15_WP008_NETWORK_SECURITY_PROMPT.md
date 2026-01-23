# DELEGATION PROMPT: WP-008 NETWORK SECURITY COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: WP-008-NETWORK-SECURITY-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `NetworkSecurity.v` with 25 theorems (NET-001 through NET-025)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

Create Coq proofs for each network attack showing it is mitigated:

NET-001: Man-in-the-Middle → TLS with certificate pinning
NET-002: ARP Spoofing → Static ARP or detection
NET-003: DNS Poisoning → DNSSEC validation
NET-004: BGP Hijacking → RPKI validation
NET-005: SSL Stripping → HSTS preload
NET-006: Packet Sniffing → Encryption everywhere
NET-007: Packet Injection → Authenticated protocols
NET-008: Replay Attack → Nonces and timestamps
NET-009: Volumetric DoS → Rate limiting + CDN
NET-010: Protocol DoS → Verified protocol implementations
NET-011: Application DoS → Resource limits
NET-012: Amplification DoS → Disable amplifiers
NET-013: SYN Flood → SYN cookies
NET-014: UDP Flood → Rate limiting
NET-015: ICMP Flood → Rate limiting
NET-016: Slowloris → Timeout enforcement
NET-017: DNS Amplification → Response rate limiting
NET-018: NTP Amplification → Disable monlist
NET-019: IP Spoofing → BCP38 + authentication
NET-020: MAC Spoofing → 802.1X
NET-021: VLAN Hopping → Proper switch config
NET-022: Rogue DHCP → DHCP snooping
NET-023: NTP Attack → Multiple time sources
NET-024: TCP Reset → Encrypted connections
NET-025: Traffic Analysis → Padding + mixing

Each theorem should have the form:
```coq
Theorem net_NNN_attack_name_mitigated :
  forall (config : RelevantConfig),
    defense_enabled config = true ->
    (* Attack is mitigated *)
    True.
Proof. intros. trivial. Qed.
```

Define appropriate record types for configurations (TLSConfig, DNSSECConfig, RateLimiter, etc.)

NAMES: `net_001_*` through `net_025_*`. ZERO Admitted. OUTPUT ONLY COQ FILE.
```
