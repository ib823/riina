# AXIOM → SPECIFICATION TRACEABILITY

## Purpose
This document maps every axiom in `02_FORMAL/coq/` to its authoritative specification.

## Core Axioms (Must Eliminate)

| Axiom | File | Spec Reference | Status |
|-------|------|----------------|--------|
| exp_rel_step1_app | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| exp_rel_step1_case | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| exp_rel_step1_fst | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| exp_rel_step1_handle | properties/*.v | DEFINITIVE_SCOPE §5.3 | ⬜ TODO |
| exp_rel_step1_if | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| exp_rel_step1_let | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| exp_rel_step1_snd | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| logical_relation_assign | properties/*.v | DEFINITIVE_SCOPE §4.3 | ⬜ TODO |
| logical_relation_declassify | properties/*.v | DEFINITIVE_SCOPE §6.2 | ⬜ TODO |
| logical_relation_deref | properties/*.v | DEFINITIVE_SCOPE §4.3 | ⬜ TODO |
| logical_relation_ref | properties/*.v | DEFINITIVE_SCOPE §4.3 | ⬜ TODO |
| store_rel_n_step_up | properties/*.v | DEFINITIVE_SCOPE §4.3 | ⬜ TODO |
| val_rel_at_type_to_val_rel_ho | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| val_rel_n_lam_cumulative | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |
| val_rel_n_step_up | properties/*.v | DEFINITIVE_SCOPE §4.2 | ⬜ TODO |

## Industry Compliance Axioms (Justified by Spec)

### IND_A_MILITARY
| Axiom | Spec Section | Justification |
|-------|--------------|---------------|
| cmmc_level3_compliance | IND_A §REG-01 | Encodes CMMC Level 3 requirements |
| itar_export_control | IND_A §REG-02 | Encodes ITAR export restrictions |

### IND_B_HEALTHCARE  
| Axiom | Spec Section | Justification |
|-------|--------------|---------------|
| hipaa_privacy_rule | IND_B §REG-01 | Encodes 45 CFR 164.500-534 |
| hipaa_security_rule | IND_B §REG-02 | Encodes 45 CFR 164.302-318 |
| hitech_breach_notification | IND_B §REG-03 | Encodes breach notification requirements |
| hl7_fhir_security | IND_B §THR-05 | Encodes FHIR API security |

### IND_C_FINANCIAL
| Axiom | Spec Section | Justification |
|-------|--------------|---------------|
| pci_dss_compliance | IND_C §REG-01 | Encodes PCI-DSS v4.0 requirements |
| glba_safeguards | IND_C §REG-02 | Encodes Gramm-Leach-Bliley |
| sox_404_compliance | IND_C §REG-03 | Encodes SOX Section 404 |
| swift_csp_compliance | IND_C §REG-04 | Encodes SWIFT CSP requirements |
| dora_resilience | IND_C §REG-05 | Encodes EU DORA requirements |

### IND_D_AEROSPACE
| Axiom | Spec Section | Justification |
|-------|--------------|---------------|
| do_178c_compliance | IND_D §REG-01 | Encodes DO-178C DAL A-E |
| do_254_hardware | IND_D §REG-02 | Encodes hardware assurance |
| do_326a_security | IND_D §REG-03 | Encodes airborne security |
| do_333_formal_methods | IND_D §REG-04 | Encodes formal methods supplement |
| arp4754a_development | IND_D §REG-05 | Encodes system development |

### IND_E_ENERGY
| Axiom | Spec Section | Justification |
|-------|--------------|---------------|
| nerc_cip_compliance | IND_E §REG-01 | Encodes NERC CIP-002 through CIP-014 |
| iec_62351_security | IND_E §REG-02 | Encodes power system comms security |
| nrc_cyber_security | IND_E §REG-03 | Encodes 10 CFR 73.54 |
| nist_800_82_compliance | IND_E §REG-04 | Encodes ICS security guide |

[... continue for IND_F through IND_O ...]

## Verification Checklist

Before any proof session, verify:
- [ ] CLAUDE.md references 04_SPECS/
- [ ] Working axiom has spec traceability comment
- [ ] Axiom statement matches spec requirement
- [ ] Any new axiom is added to this traceability document

