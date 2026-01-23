# DELEGATION PROMPTS INDEX

## RIINA Complete Research Integration — Claude AI Web Delegation Prompts

**Created:** 2026-01-23
**Last Updated:** 2026-01-23
**Total Work Packages:** 44
**Total Theorems Required:** ~600+

---

## QUICK REFERENCE BY CATEGORY

### THREAT COVERAGE (WP001-WP016) — 355 Theorems

| WP | File | Threats | Theorems | Category |
|----|------|---------|----------|----------|
| WP-001 | `WP001_MEMORY_SAFETY_PROMPT.md` | MEM-001 to MEM-020 | 20 | Memory Corruption |
| WP-002 | `WP002_CONTROL_FLOW_PROMPT.md` | CTL-001 to CTL-015 | 15 | Control Flow |
| WP-003 | `WP003_INJECTION_PREVENTION_PROMPT.md` | INJ-001 to INJ-015 | 15 | Injection |
| WP-004 | `WP004_WEB_SECURITY_PROMPT.md` | WEB-001 to WEB-025 | 25 | Web Application |
| WP-005 | `WP005_AUTHENTICATION_PROMPT.md` | AUTH-001 to AUTH-020 | 20 | Authentication |
| WP-006 | `WP006_CRYPTOGRAPHIC_PROMPT.md` | CRY-001 to CRY-031 | 31 | Cryptographic |
| WP-007 | `WP007_HARDWARE_SECURITY_PROMPT.md` | HW-001 to HW-034 | 34 | Hardware/Microarch |
| WP-008 | `WP008_NETWORK_SECURITY_PROMPT.md` | NET-001 to NET-025 | 25 | Network |
| WP-009 | `WP009_TIMING_SECURITY_PROMPT.md` | TIME-001 to TIME-015 | 15 | Timing/Temporal |
| WP-010 | `WP010_COVERT_CHANNEL_PROMPT.md` | COV-001 to COV-015 | 15 | Covert Channels |
| WP-011 | `WP011_PHYSICAL_SECURITY_PROMPT.md` | PHYS-001 to PHYS-020 | 20 | Physical |
| WP-012 | `WP012_HUMAN_FACTOR_PROMPT.md` | HUM-001 to HUM-021 | 21 | Human/Social |
| WP-013 | `WP013_SUPPLY_CHAIN_PROMPT.md` | SUP-001 to SUP-016 | 16 | Supply Chain |
| WP-014 | `WP014_AI_ML_SECURITY_PROMPT.md` | AI-001 to AI-018 | 18 | AI/ML |
| WP-015 | `WP015_DISTRIBUTED_SECURITY_PROMPT.md` | DIST-001 to DIST-015 | 15 | Distributed |
| WP-016 | `WP016_FUTURE_SECURITY_PROMPT.md` | FUT-001 to FUT-010 | 10 | Future/Theoretical |

### TYPE SYSTEM (TYPE001-TYPE005) — 68 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| TYPE-001 | `TYPE001_MLTT_FOUNDATION_PROMPT.md` | 15 | MLTT Foundation |
| TYPE-002 | `TYPE002_LINEAR_TYPES_PROMPT.md` | 12 | Linear Types |
| TYPE-003 | `TYPE003_SESSION_TYPES_PROMPT.md` | 15 | Session Types |
| TYPE-004 | `TYPE004_REFINEMENT_TYPES_PROMPT.md` | 12 | Refinement Types |
| TYPE-005 | `TYPE005_DEPENDENT_TYPES_PROMPT.md` | 14 | Dependent Types |

### EFFECT SYSTEM (EFF001) — 15 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| EFF-001 | `EFF001_ALGEBRAIC_EFFECTS_PROMPT.md` | 15 | Algebraic Effects |

### PERFORMANCE (PERF001-PERF003) — 39 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| PERF-001 | `PERF001_WCET_BOUNDS_PROMPT.md` | 15 | WCET Analysis |
| PERF-002 | `PERF002_BINARY_SIZE_BOUNDS_PROMPT.md` | 12 | Binary Size Bounds |
| PERF-003 | `PERF003_SIMD_VERIFICATION_PROMPT.md` | 12 | SIMD Verification |

### COMPLIANCE (COMPLY001-COMPLY003) — 50 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| COMPLY-001 | `COMPLY001_HIPAA_HEALTHCARE_PROMPT.md` | 15 | HIPAA (Healthcare) |
| COMPLY-002 | `COMPLY002_PCIDSS_FINANCIAL_PROMPT.md` | 15 | PCI-DSS (Financial) |
| COMPLY-003 | `COMPLY003_DO178C_AEROSPACE_PROMPT.md` | 20 | DO-178C (Aerospace) |

### SECURITY (SEC001-SEC002) — 30 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| SEC-001 | `SEC001_CAPABILITY_SECURITY_PROMPT.md` | 15 | Capability Security |
| SEC-002 | `SEC002_COVERT_CHANNELS_PROMPT.md` | 15 | Covert Channels |

### CONCURRENCY (CONC001) — 15 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| CONC-001 | `CONC001_DATA_RACE_FREEDOM_PROMPT.md` | 15 | Data Race Freedom |

### MEMORY (MEM001) — 15 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| MEM-001 | `MEM001_OWNERSHIP_TYPES_PROMPT.md` | 15 | Ownership Types |

### SPECIAL DOMAINS (DOMAIN001-DOMAIN002) — 30 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| DOMAIN-001 | `DOMAIN001_RADIATION_HARDENING_PROMPT.md` | 15 | Radiation Hardening |
| DOMAIN-002 | `DOMAIN002_VERIFIED_AI_ML_PROMPT.md` | 15 | Verified AI/ML |

### COMPILER (COMPILE001) — 15 Theorems

| ID | File | Theorems | Category |
|----|------|----------|----------|
| COMPILE-001 | `COMPILE001_TRANSLATION_VALIDATION_PROMPT.md` | 15 | Translation Validation |

### RUST IMPLEMENTATION (RUST001) — N/A (Code)

| ID | File | Output | Category |
|----|------|--------|----------|
| RUST-001 | `RUST001_BAHASA_MELAYU_LEXER_PROMPT.md` | keywords.rs | Bahasa Melayu Lexer |

---

## USAGE INSTRUCTIONS

### Step 1: Open Prompt File
```bash
cat /workspaces/proof/06_COORDINATION/delegation_prompts/TYPE001_MLTT_FOUNDATION_PROMPT.md
```

### Step 2: Copy Content After "COPY EVERYTHING BELOW THIS LINE"
Copy the entire prompt text starting from the `═══` line.

### Step 3: Paste to Claude AI Web
Open a new chat at claude.ai and paste the prompt.

### Step 4: Save Output
```bash
# Example for TYPE-001
cat > /workspaces/proof/02_FORMAL/coq/foundations/MLTTFoundation.v << 'EOF'
[PASTE COQ OUTPUT HERE]
EOF
```

### Step 5: Verify Output
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA foundations/MLTTFoundation.v

# Check for admits
grep -c "Admitted\." foundations/MLTTFoundation.v  # Must be 0
grep -c "admit\." foundations/MLTTFoundation.v     # Must be 0
grep -c "^Axiom" foundations/MLTTFoundation.v      # Must be 0
```

---

## OUTPUT FILE MAPPING

| Prompt | Output File Path |
|--------|------------------|
| TYPE001 | `02_FORMAL/coq/foundations/MLTTFoundation.v` |
| TYPE002 | `02_FORMAL/coq/foundations/LinearTypes.v` |
| TYPE003 | `02_FORMAL/coq/concurrency/SessionTypes.v` |
| TYPE004 | `02_FORMAL/coq/foundations/RefinementTypes.v` |
| TYPE005 | `02_FORMAL/coq/foundations/DependentTypes.v` |
| EFF001 | `02_FORMAL/coq/effects/AlgebraicEffects.v` |
| PERF001 | `02_FORMAL/coq/performance/WCETBounds.v` |
| PERF002 | `02_FORMAL/coq/performance/BinarySizeBounds.v` |
| PERF003 | `02_FORMAL/coq/performance/SIMDVerification.v` |
| COMPLY001 | `02_FORMAL/coq/compliance/HIPAACompliance.v` |
| COMPLY002 | `02_FORMAL/coq/compliance/PCIDSSCompliance.v` |
| COMPLY003 | `02_FORMAL/coq/compliance/DO178CCompliance.v` |
| SEC001 | `02_FORMAL/coq/security/CapabilitySecurity.v` |
| SEC002 | `02_FORMAL/coq/security/CovertChannels.v` |
| CONC001 | `02_FORMAL/coq/concurrency/DataRaceFreedom.v` |
| MEM001 | `02_FORMAL/coq/memory/OwnershipTypes.v` |
| DOMAIN001 | `02_FORMAL/coq/domains/RadiationHardening.v` |
| DOMAIN002 | `02_FORMAL/coq/domains/VerifiedAIML.v` |
| COMPILE001 | `02_FORMAL/coq/compiler/TranslationValidation.v` |
| RUST001 | `03_PROTO/crates/riina-lexer/src/keywords.rs` |

---

## PROGRESS TRACKING

### Threat Coverage (WP001-WP016)

| WP | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| WP-001 | [ ] | [ ] | [ ] | [ ] |
| WP-002 | [ ] | [ ] | [ ] | [ ] |
| WP-003 | [ ] | [ ] | [ ] | [ ] |
| WP-004 | [ ] | [ ] | [ ] | [ ] |
| WP-005 | [ ] | [ ] | [ ] | [ ] |
| WP-006 | [ ] | [ ] | [ ] | [ ] |
| WP-007 | [ ] | [ ] | [ ] | [ ] |
| WP-008 | [ ] | [ ] | [ ] | [ ] |
| WP-009 | [ ] | [ ] | [ ] | [ ] |
| WP-010 | [ ] | [ ] | [ ] | [ ] |
| WP-011 | [ ] | [ ] | [ ] | [ ] |
| WP-012 | [ ] | [ ] | [ ] | [ ] |
| WP-013 | [ ] | [ ] | [ ] | [ ] |
| WP-014 | [ ] | [ ] | [ ] | [ ] |
| WP-015 | [ ] | [ ] | [ ] | [ ] |
| WP-016 | [ ] | [ ] | [ ] | [ ] |

### Type System (TYPE001-TYPE005)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| TYPE-001 | [ ] | [ ] | [ ] | [ ] |
| TYPE-002 | [ ] | [ ] | [ ] | [ ] |
| TYPE-003 | [ ] | [ ] | [ ] | [ ] |
| TYPE-004 | [ ] | [ ] | [ ] | [ ] |
| TYPE-005 | [ ] | [ ] | [ ] | [ ] |

### Effect System

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| EFF-001 | [ ] | [ ] | [ ] | [ ] |

### Performance (PERF001-PERF003)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| PERF-001 | [ ] | [ ] | [ ] | [ ] |
| PERF-002 | [ ] | [ ] | [ ] | [ ] |
| PERF-003 | [ ] | [ ] | [ ] | [ ] |

### Compliance (COMPLY001-COMPLY003)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| COMPLY-001 | [ ] | [ ] | [ ] | [ ] |
| COMPLY-002 | [ ] | [ ] | [ ] | [ ] |
| COMPLY-003 | [ ] | [ ] | [ ] | [ ] |

### Security (SEC001-SEC002)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| SEC-001 | [ ] | [ ] | [ ] | [ ] |
| SEC-002 | [ ] | [ ] | [ ] | [ ] |

### Concurrency (CONC001)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| CONC-001 | [ ] | [ ] | [ ] | [ ] |

### Memory (MEM001)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| MEM-001 | [ ] | [ ] | [ ] | [ ] |

### Special Domains (DOMAIN001-DOMAIN002)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| DOMAIN-001 | [ ] | [ ] | [ ] | [ ] |
| DOMAIN-002 | [ ] | [ ] | [ ] | [ ] |

### Compiler (COMPILE001)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| COMPILE-001 | [ ] | [ ] | [ ] | [ ] |

### Rust Implementation (RUST001)

| ID | Delegated | Received | Verified | Integrated |
|----|-----------|----------|----------|------------|
| RUST-001 | [ ] | [ ] | [ ] | [ ] |

---

## ADVERSARIAL ASSUMPTIONS

Each prompt is designed assuming Claude AI Web will:
1. Try to use `Admitted.` or `admit.` to skip proofs
2. Try to add `Axiom` declarations instead of proving
3. Try to change theorem names to avoid specifications
4. Try to output non-Coq content (markdown, explanations)
5. Try to produce code that doesn't compile

All prompts include:
- Explicit forbidden actions list
- Exact theorem name requirements
- Verification commands to run
- Output format requirements

---

## RECOMMENDED EXECUTION ORDER

**Priority 1 (Foundation):**
1. TYPE001 - MLTT Foundation
2. TYPE002 - Linear Types
3. EFF001 - Algebraic Effects
4. MEM001 - Ownership Types

**Priority 2 (Security Core):**
5. SEC001 - Capability Security
6. SEC002 - Covert Channels
7. CONC001 - Data Race Freedom

**Priority 3 (Threats):**
8-23. WP001-WP016 (Threat categories)

**Priority 4 (Compliance):**
24. COMPLY001 - HIPAA
25. COMPLY002 - PCI-DSS
26. COMPLY003 - DO-178C

**Priority 5 (Performance):**
27. PERF001 - WCET
28. PERF002 - Binary Size
29. PERF003 - SIMD

**Priority 6 (Advanced):**
30. TYPE003 - Session Types
31. TYPE004 - Refinement Types
32. TYPE005 - Dependent Types
33. DOMAIN001 - Radiation Hardening
34. DOMAIN002 - Verified AI/ML
35. COMPILE001 - Translation Validation

**Priority 7 (Implementation):**
36. RUST001 - Bahasa Melayu Lexer

---

## SUMMARY STATISTICS

| Category | Prompts | Theorems | Status |
|----------|---------|----------|--------|
| Threats | 16 | 355 | Ready |
| Type System | 5 | 68 | Ready |
| Effects | 1 | 15 | Ready |
| Performance | 3 | 39 | Ready |
| Compliance | 3 | 50 | Ready |
| Security | 2 | 30 | Ready |
| Concurrency | 1 | 15 | Ready |
| Memory | 1 | 15 | Ready |
| Domains | 2 | 30 | Ready |
| Compiler | 1 | 15 | Ready |
| Rust | 1 | N/A | Ready |
| **TOTAL** | **36** | **~632** | **Ready** |

---

*"Trust nothing. Verify everything."*

*RIINA: Rigorous Immutable Invariant — Normalized Axiom*
