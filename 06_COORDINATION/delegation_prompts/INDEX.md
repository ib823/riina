# DELEGATION PROMPTS INDEX

## RIINA Complete Research Integration — Claude AI Web Delegation Prompts

**Created:** 2026-01-23
**Last Updated:** 2026-01-24
**Total Work Packages:** 42
**Total Theorems Required:** ~757

---

## EXECUTION ORDER (Use `ls *.md | grep -v INDEX | sort`)

Files are prefixed with execution order (01-36). Execute in numeric order.

```bash
# List all prompts in execution order
ls /workspaces/proof/06_COORDINATION/delegation_prompts/*.md | grep -v INDEX | sort

# View specific prompt
cat /workspaces/proof/06_COORDINATION/delegation_prompts/01_TYPE001_MLTT_FOUNDATION_PROMPT.md
```

---

## COMPLETE EXECUTION ORDER

| # | File | Category | Output Path | Theorems |
|---|------|----------|-------------|----------|
| 01 | `01_TYPE001_MLTT_FOUNDATION_PROMPT.md` | MLTT Foundation | `foundations/MLTTFoundation.v` | 15 |
| 02 | `02_TYPE002_LINEAR_TYPES_PROMPT.md` | Linear Types | `foundations/LinearTypes.v` | 12 |
| 03 | `03_EFF001_ALGEBRAIC_EFFECTS_PROMPT.md` | Algebraic Effects | `effects/AlgebraicEffects.v` | 15 |
| 04 | `04_MEM001_OWNERSHIP_TYPES_PROMPT.md` | Ownership Types | `memory/OwnershipTypes.v` | 15 |
| 05 | `05_SEC001_CAPABILITY_SECURITY_PROMPT.md` | Capability Security | `security/CapabilitySecurity.v` | 15 |
| 06 | `06_SEC002_COVERT_CHANNELS_PROMPT.md` | Covert Channels | `security/CovertChannels.v` | 15 |
| 07 | `07_CONC001_DATA_RACE_FREEDOM_PROMPT.md` | Data Race Freedom | `concurrency/DataRaceFreedom.v` | 15 |
| 08 | `08_WP001_MEMORY_SAFETY_PROMPT.md` | Memory Corruption | `properties/MemorySafety.v` | 20 |
| 09 | `09_WP002_CONTROL_FLOW_PROMPT.md` | Control Flow | `properties/ControlFlow.v` | 15 |
| 10 | `10_WP003_INJECTION_PREVENTION_PROMPT.md` | Injection | `properties/InjectionPrevention.v` | 15 |
| 11 | `11_WP004_WEB_SECURITY_PROMPT.md` | Web Application | `properties/WebSecurity.v` | 25 |
| 12 | `12_WP005_AUTHENTICATION_PROMPT.md` | Authentication | `properties/Authentication.v` | 20 |
| 13 | `13_WP006_CRYPTOGRAPHIC_PROMPT.md` | Cryptographic | `properties/Cryptographic.v` | 31 |
| 14 | `14_WP007_HARDWARE_SECURITY_PROMPT.md` | Hardware/Microarch | `properties/HardwareSecurity.v` | 34 |
| 15 | `15_WP008_NETWORK_SECURITY_PROMPT.md` | Network | `properties/NetworkSecurity.v` | 25 |
| 16 | `16_WP009_TIMING_SECURITY_PROMPT.md` | Timing/Temporal | `properties/TimingSecurity.v` | 15 |
| 17 | `17_WP010_COVERT_CHANNEL_PROMPT.md` | Covert Channels | `properties/CovertChannel.v` | 15 |
| 18 | `18_WP011_PHYSICAL_SECURITY_PROMPT.md` | Physical | `properties/PhysicalSecurity.v` | 20 |
| 19 | `19_WP012_HUMAN_FACTOR_PROMPT.md` | Human/Social | `properties/HumanFactor.v` | 21 |
| 20 | `20_WP013_SUPPLY_CHAIN_PROMPT.md` | Supply Chain | `properties/SupplyChain.v` | 16 |
| 21 | `21_WP014_AI_ML_SECURITY_PROMPT.md` | AI/ML | `properties/AIMLSecurity.v` | 18 |
| 22 | `22_WP015_DISTRIBUTED_SECURITY_PROMPT.md` | Distributed | `properties/DistributedSecurity.v` | 15 |
| 23 | `23_WP016_FUTURE_SECURITY_PROMPT.md` | Future/Theoretical | `properties/FutureSecurity.v` | 10 |
| 24 | `24_COMPLY001_HIPAA_HEALTHCARE_PROMPT.md` | HIPAA (Healthcare) | `compliance/HIPAACompliance.v` | 15 |
| 25 | `25_COMPLY002_PCIDSS_FINANCIAL_PROMPT.md` | PCI-DSS (Financial) | `compliance/PCIDSSCompliance.v` | 15 |
| 26 | `26_COMPLY003_DO178C_AEROSPACE_PROMPT.md` | DO-178C (Aerospace) | `compliance/DO178CCompliance.v` | 20 |
| 27 | `27_PERF001_WCET_BOUNDS_PROMPT.md` | WCET Analysis | `performance/WCETBounds.v` | 15 |
| 28 | `28_PERF002_BINARY_SIZE_BOUNDS_PROMPT.md` | Binary Size Bounds | `performance/BinarySizeBounds.v` | 12 |
| 29 | `29_PERF003_SIMD_VERIFICATION_PROMPT.md` | SIMD Verification | `performance/SIMDVerification.v` | 12 |
| 30 | `30_TYPE003_SESSION_TYPES_PROMPT.md` | Session Types | `concurrency/SessionTypes.v` | 15 |
| 31 | `31_TYPE004_REFINEMENT_TYPES_PROMPT.md` | Refinement Types | `foundations/RefinementTypes.v` | 12 |
| 32 | `32_TYPE005_DEPENDENT_TYPES_PROMPT.md` | Dependent Types | `foundations/DependentTypes.v` | 14 |
| 33 | `33_DOMAIN001_RADIATION_HARDENING_PROMPT.md` | Radiation Hardening | `domains/RadiationHardening.v` | 15 |
| 34 | `34_DOMAIN002_VERIFIED_AI_ML_PROMPT.md` | Verified AI/ML | `domains/VerifiedAIML.v` | 15 |
| 35 | `35_COMPILE001_TRANSLATION_VALIDATION_PROMPT.md` | Translation Validation | `compiler/TranslationValidation.v` | 15 |
| 36 | `36_RUST001_BAHASA_MELAYU_LEXER_PROMPT.md` | Bahasa Melayu Lexer | `riina-lexer/src/keywords.rs` | N/A |
| 37 | `37_OS001_VERIFIED_MICROKERNEL_PROMPT.md` | Verified Microkernel | `os/VerifiedMicrokernel.v` | 25 |
| 38 | `38_NET001_VERIFIED_NETWORK_PROMPT.md` | Verified Network Stack | `network/VerifiedNetwork.v` | 25 |
| 39 | `39_RUNTIME001_VERIFIED_RUNTIME_PROMPT.md` | Verified Runtime | `runtime/VerifiedRuntime.v` | 20 |
| 40 | `40_UX001_VERIFIED_UI_PROMPT.md` | Verified UI | `ui/VerifiedUI.v` | 15 |
| 41 | `41_PHYSICS001_PHYSICAL_SECURITY_PROMPT.md` | Physical Security | `physical/PhysicalSecurity.v` | 15 |
| 42 | `42_INFRA001_VERIFIED_CLOUD_PROMPT.md` | Verified Infrastructure | `infra/VerifiedInfra.v` | 25 |

---

## QUICK CLI COMMANDS

```bash
# Navigate to prompts
cd /workspaces/proof/06_COORDINATION/delegation_prompts

# List all prompts in order
ls -1 [0-9]*.md

# View prompt N (e.g., prompt 01)
cat 01_TYPE001_MLTT_FOUNDATION_PROMPT.md

# Copy prompt content to clipboard (Linux)
cat 01_TYPE001_MLTT_FOUNDATION_PROMPT.md | xclip -selection clipboard

# Save output to correct location
cat > /workspaces/proof/02_FORMAL/coq/foundations/MLTTFoundation.v << 'EOF'
[PASTE COQ OUTPUT HERE]
EOF

# Verify output compiles
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA foundations/MLTTFoundation.v

# Check for forbidden patterns (ALL MUST BE 0)
grep -c "Admitted\.\|admit\.\|^Axiom" foundations/MLTTFoundation.v
```

---

## PRIORITY PHASES

### Phase 1: Foundation (01-04) — Start Here
| # | ID | Category | Critical For |
|---|-----|----------|--------------|
| 01 | TYPE001 | MLTT Foundation | Everything else |
| 02 | TYPE002 | Linear Types | Resource safety |
| 03 | EFF001 | Algebraic Effects | Effect tracking |
| 04 | MEM001 | Ownership Types | Memory safety |

### Phase 2: Security Core (05-07)
| # | ID | Category | Critical For |
|---|-----|----------|--------------|
| 05 | SEC001 | Capability Security | Access control |
| 06 | SEC002 | Covert Channels | Information flow |
| 07 | CONC001 | Data Race Freedom | Concurrency |

### Phase 3: Threat Coverage (08-23)
16 work packages covering 355 threat theorems.

### Phase 4: Compliance (24-26)
HIPAA, PCI-DSS, DO-178C regulatory requirements.

### Phase 5: Performance (27-29)
WCET bounds, binary size, SIMD verification.

### Phase 6: Advanced (30-35)
Session types, refinement types, radiation hardening, etc.

### Phase 7: Implementation (36)
Rust lexer for Bahasa Melayu keywords.

### Phase 8: RIINA Total Stack (37-42)
Full-stack verified infrastructure from silicon to UI.

| # | ID | Category | Critical For |
|---|-----|----------|--------------|
| 37 | OS001 | Verified Microkernel | Capability-based OS |
| 38 | NET001 | Verified Network | TLS 1.3 + TCP/IP + DNS |
| 39 | RUNTIME001 | Verified Runtime | GC + Allocator + Sandbox |
| 40 | UX001 | Verified UI | Anti-clickjacking + Origin |
| 41 | PHYSICS001 | Physical Security | PUF + Tamper Detection |
| 42 | INFRA001 | Verified Infrastructure | LB + DB + MQ + Secrets |

---

## PROGRESS TRACKING

Mark with [x] when complete:

### Phase 1: Foundation
- [ ] 01_TYPE001 — Delegated | Received | Verified | Integrated
- [ ] 02_TYPE002 — Delegated | Received | Verified | Integrated
- [ ] 03_EFF001 — Delegated | Received | Verified | Integrated
- [ ] 04_MEM001 — Delegated | Received | Verified | Integrated

### Phase 2: Security Core
- [ ] 05_SEC001 — Delegated | Received | Verified | Integrated
- [ ] 06_SEC002 — Delegated | Received | Verified | Integrated
- [ ] 07_CONC001 — Delegated | Received | Verified | Integrated

### Phase 3: Threats (08-23)
- [ ] 08_WP001 — Delegated | Received | Verified | Integrated
- [ ] 09_WP002 — Delegated | Received | Verified | Integrated
- [ ] 10_WP003 — Delegated | Received | Verified | Integrated
- [ ] 11_WP004 — Delegated | Received | Verified | Integrated
- [ ] 12_WP005 — Delegated | Received | Verified | Integrated
- [ ] 13_WP006 — Delegated | Received | Verified | Integrated
- [ ] 14_WP007 — Delegated | Received | Verified | Integrated
- [ ] 15_WP008 — Delegated | Received | Verified | Integrated
- [ ] 16_WP009 — Delegated | Received | Verified | Integrated
- [ ] 17_WP010 — Delegated | Received | Verified | Integrated
- [ ] 18_WP011 — Delegated | Received | Verified | Integrated
- [ ] 19_WP012 — Delegated | Received | Verified | Integrated
- [ ] 20_WP013 — Delegated | Received | Verified | Integrated
- [ ] 21_WP014 — Delegated | Received | Verified | Integrated
- [ ] 22_WP015 — Delegated | Received | Verified | Integrated
- [ ] 23_WP016 — Delegated | Received | Verified | Integrated

### Phase 4: Compliance (24-26)
- [ ] 24_COMPLY001 — Delegated | Received | Verified | Integrated
- [ ] 25_COMPLY002 — Delegated | Received | Verified | Integrated
- [ ] 26_COMPLY003 — Delegated | Received | Verified | Integrated

### Phase 5: Performance (27-29)
- [ ] 27_PERF001 — Delegated | Received | Verified | Integrated
- [ ] 28_PERF002 — Delegated | Received | Verified | Integrated
- [ ] 29_PERF003 — Delegated | Received | Verified | Integrated

### Phase 6: Advanced (30-35)
- [ ] 30_TYPE003 — Delegated | Received | Verified | Integrated
- [ ] 31_TYPE004 — Delegated | Received | Verified | Integrated
- [ ] 32_TYPE005 — Delegated | Received | Verified | Integrated
- [ ] 33_DOMAIN001 — Delegated | Received | Verified | Integrated
- [ ] 34_DOMAIN002 — Delegated | Received | Verified | Integrated
- [ ] 35_COMPILE001 — Delegated | Received | Verified | Integrated

### Phase 7: Implementation (36)
- [ ] 36_RUST001 — Delegated | Received | Verified | Integrated

### Phase 8: RIINA Total Stack (37-42)
- [ ] 37_OS001 — Delegated | Received | Verified | Integrated
- [ ] 38_NET001 — Delegated | Received | Verified | Integrated
- [ ] 39_RUNTIME001 — Delegated | Received | Verified | Integrated
- [ ] 40_UX001 — Delegated | Received | Verified | Integrated
- [ ] 41_PHYSICS001 — Delegated | Received | Verified | Integrated
- [ ] 42_INFRA001 — Delegated | Received | Verified | Integrated

---

## VERIFICATION CHECKLIST

For EACH output file:

```bash
# 1. Save to correct path
# 2. Compile test
coqc -Q . RIINA [path/to/file.v]

# 3. Forbidden pattern check (ALL MUST BE 0)
grep -c "Admitted\." [file.v]   # MUST BE 0
grep -c "admit\." [file.v]      # MUST BE 0
grep -c "^Axiom" [file.v]       # MUST BE 0

# 4. If all pass, mark as Verified
# 5. Add to _CoqProject and rebuild
echo "[path/to/file.v]" >> _CoqProject
make
```

---

## SUMMARY

| Phase | Prompts | Theorems | Status |
|-------|---------|----------|--------|
| 1. Foundation | 4 | 57 | Ready |
| 2. Security Core | 3 | 45 | Ready |
| 3. Threats | 16 | 355 | Ready |
| 4. Compliance | 3 | 50 | Ready |
| 5. Performance | 3 | 39 | Ready |
| 6. Advanced | 6 | 86 | Ready |
| 7. Implementation | 1 | N/A | Ready |
| 8. RIINA Total Stack | 6 | 125 | Ready |
| **TOTAL** | **42** | **~757** | **Ready** |

---

*"Trust nothing. Verify everything."*

*RIINA: Rigorous Immutable Invariant — Normalized Axiom*
