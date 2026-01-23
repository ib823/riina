# DELEGATION PROMPTS INDEX

## RIINA 350+ Threat Coverage — Claude AI Web Delegation Prompts

**Created:** 2026-01-23
**Total Work Packages:** 16
**Total Threats Covered:** 355
**Total Theorems Required:** ~400

---

## QUICK REFERENCE

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
| **TOTAL** | | **355** | **~355** | |

---

## USAGE INSTRUCTIONS

### Step 1: Open Prompt File
```bash
cat /workspaces/proof/06_COORDINATION/delegation_prompts/WP001_MEMORY_SAFETY_PROMPT.md
```

### Step 2: Copy Content After "COPY EVERYTHING BELOW THIS LINE"
Copy the entire prompt text starting from the `═══` line.

### Step 3: Paste to Claude AI Web
Open a new chat at claude.ai and paste the prompt.

### Step 4: Save Output
Save the Coq output to the appropriate file:
```bash
# Example for WP-001
cat > /workspaces/proof/02_FORMAL/coq/threats/MemorySafety.v << 'EOF'
[PASTE COQ OUTPUT HERE]
EOF
```

### Step 5: Verify Output
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA threats/MemorySafety.v

# Check for admits
grep -c "Admitted\." threats/MemorySafety.v
# Must be 0 (or 1 for files that note an exception)
```

### Step 6: Track Progress
Update this file or PROGRESS.md with completion status.

---

## VERIFICATION CHECKLIST

For each work package output:

- [ ] File compiles with `coqc` (exit code 0)
- [ ] Zero `Admitted.` (grep returns 0)
- [ ] Zero `admit.` (grep returns 0)
- [ ] Zero new `Axiom` (grep returns 0)
- [ ] Correct number of theorems (grep -c "^Theorem")
- [ ] All theorem names match specification

---

## PROGRESS TRACKING

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

*"Trust nothing. Verify everything."*
