# DELEGATION PROMPT: WP-011 PHYSICAL SECURITY COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: WP-011-PHYSICAL-SECURITY-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `PhysicalSecurity.v` with 20 theorems (PHYS-001 through PHYS-020)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

Create Coq proofs for physical attack mitigations:

PHYS-001: Device Theft → Full disk encryption + remote wipe capability
PHYS-002: Device Tampering → Tamper detection (seals, sensors)
PHYS-003: TEMPEST → EM shielding
PHYS-004: Van Eck Phreaking → Display shielding
PHYS-005: Acoustic Keystroke → Acoustic masking
PHYS-006: Power Analysis → Hardware countermeasures + masking
PHYS-007: EM Analysis → Shielding
PHYS-008: Thermal Imaging → Thermal masking
PHYS-009: Optical Surveillance → Screen protection
PHYS-010: Key Extraction → HSM + tamper response
PHYS-011: Cold Boot Attack → Memory encryption
PHYS-012: Evil Maid → Measured boot + sealing
PHYS-013: Supply Chain Intercept → Attestation
PHYS-014: Hardware Implant → Inspection + verification
PHYS-015: Fault Injection → Fault detection
PHYS-016: Probing Attack → Active shielding
PHYS-017: Decapping → Tamper evidence
PHYS-018: Bus Probing → Bus encryption
PHYS-019: Debug Port Access → Debug disabled/locked
PHYS-020: Radiation Attack → Radiation hardening

Models:
- Encryption state (encrypted/plaintext)
- Tamper detection state
- Shielding effectiveness

NAMES: `phys_001_*` through `phys_020_*`. ZERO Admitted. OUTPUT ONLY COQ FILE.
```
