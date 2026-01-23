# DELEGATION PROMPT: WP-013 SUPPLY CHAIN SECURITY COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: WP-013-SUPPLY-CHAIN-SECURITY-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `SupplyChainSecurity.v` with 16 theorems (SUP-001 through SUP-016)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

Create Coq proofs for supply chain attack mitigations:

SUP-001: Compromised Dependency → Dependency verification (hash + signature)
SUP-002: Typosquatting → Name verification + allowlist
SUP-003: Dependency Confusion → Scoped/namespaced packages
SUP-004: Build System Compromise → Hermetic build (reproducible)
SUP-005: Package Manager Attack → Signed packages + TUF
SUP-006: Firmware Supply Chain → Verified firmware signatures
SUP-007: Hardware Supply Chain → Hardware attestation
SUP-008: Third-Party Compromise → Vendor verification
SUP-009: Watering Hole → Network segmentation
SUP-010: Update Attack → Signed updates + version enforcement
SUP-011: Source Code Compromise → Code signing + review
SUP-012: Compiler Attack → Diverse double compilation (DDC)
SUP-013: Binary Backdoor → Reproducible builds
SUP-014: Certificate Compromise → Certificate transparency
SUP-015: Developer Compromise → MFA + access control
SUP-016: Self-Replicating Malware → Dependency isolation

Key models:
```coq
Record SignedArtifact : Type := mkSigned {
  sa_content_hash : list nat;
  sa_signature : list nat;
  sa_signer_key : nat;
  sa_verified : bool
}.

Record ReproducibleBuild : Type := mkRepro {
  rb_source_hash : list nat;
  rb_output_hash : list nat;
  rb_builder1_hash : list nat;
  rb_builder2_hash : list nat;
  rb_hashes_match : bool
}.

Theorem sup_004_build_compromise_mitigated :
  forall (rb : ReproducibleBuild),
    rb_hashes_match rb = true ->
    rb_builder1_hash rb = rb_builder2_hash rb.
```

NAMES: `sup_001_*` through `sup_016_*`. ZERO Admitted. OUTPUT ONLY COQ FILE.
```
