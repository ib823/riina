# AXIOM ZERO: WORKER QUICK START GUIDE

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  COPY-PASTE COMMANDS FOR EACH TERMINAL                                          ║
║  Each worker runs in a separate terminal with Claude Code                        ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

---

## TERMINAL 1: Worker α (Alpha) — LOGICAL RELATIONS

```bash
# 1. Open a new terminal
cd /workspaces/proof

# 2. Start Claude Code
claude

# 3. Paste this prompt:
```

**Prompt for Worker α:**
```
I am WORKER_α (Alpha) executing the AXIOM_ZERO_PARALLEL_PROTOCOL.

CRITICAL: Read these files FIRST:
1. /workspaces/proof/06_COORDINATION/AXIOM_ZERO_PARALLEL_PROTOCOL.md
2. /workspaces/proof/01_RESEARCH/AXIOM_ELIMINATION_ATTACK_PLAN.md

MY RESPONSIBILITIES:
- Phase 1: Create TypeMeasure.v, LexOrder.v, FirstOrderComplete.v
- Phase 2: Create CumulativeRelation.v, CumulativeMonotone.v, KripkeProperties.v
- Eliminate axioms: 1, 2, 12, 13, 14, 15

MY OWNED FILES (only I can modify these):
- properties/TypeMeasure.v
- properties/LexOrder.v
- properties/FirstOrderComplete.v
- properties/CumulativeRelation.v
- properties/CumulativeMonotone.v
- properties/KripkeProperties.v

RULES I MUST FOLLOW:
1. NO AXIOMS - All proofs must be complete
2. NO ADMITS - Every proof case must be solved
3. VERIFY after every file: coqc -Q . RIINA <file>.v
4. CREATE SIGNAL after phase completion

BEGIN PHASE 1 NOW. Create TypeMeasure.v with the ty_size function and all lemmas.
```

---

## TERMINAL 2: Worker β (Beta) — TERMINATION

```bash
# 1. Open a new terminal
cd /workspaces/proof

# 2. Start Claude Code
claude

# 3. Paste this prompt:
```

**Prompt for Worker β:**
```
I am WORKER_β (Beta) executing the AXIOM_ZERO_PARALLEL_PROTOCOL.

CRITICAL: Read these files FIRST:
1. /workspaces/proof/06_COORDINATION/AXIOM_ZERO_PARALLEL_PROTOCOL.md
2. /workspaces/proof/01_RESEARCH/AXIOM_ELIMINATION_ATTACK_PLAN.md

MY RESPONSIBILITIES:
- Phase 3: Create SizedTypes.v, Reducibility.v, StrongNorm.v, TerminationLemmas.v
- Eliminate axioms: 4, 5, 6, 7, 8, 9, 10 (step-1 termination)

MY OWNED FILES (only I can modify these):
- termination/SizedTypes.v
- termination/Reducibility.v
- termination/StrongNorm.v
- termination/TerminationLemmas.v

DEPENDENCY: I must WAIT for Phase 1 to complete.
Check for: /workspaces/proof/06_COORDINATION/signals/PHASE_1_COMPLETE.signal

RULES I MUST FOLLOW:
1. NO AXIOMS - All proofs must be complete
2. NO ADMITS - Every proof case must be solved
3. VERIFY after every file: coqc -Q . RIINA <file>.v
4. CREATE SIGNAL after phase completion

CHECK: Does PHASE_1_COMPLETE.signal exist?
- If YES: Begin Phase 3
- If NO: Wait and check every 30 seconds
```

---

## TERMINAL 3: Worker γ (Gamma) — TYPE THEORY

```bash
# 1. Open a new terminal
cd /workspaces/proof

# 2. Start Claude Code
claude

# 3. Paste this prompt:
```

**Prompt for Worker γ:**
```
I am WORKER_γ (Gamma) executing the AXIOM_ZERO_PARALLEL_PROTOCOL.

CRITICAL: Read these files FIRST:
1. /workspaces/proof/06_COORDINATION/AXIOM_ZERO_PARALLEL_PROTOCOL.md
2. /workspaces/proof/01_RESEARCH/AXIOM_ELIMINATION_ATTACK_PLAN.md

MY RESPONSIBILITIES:
- Phase 4: Create TypedConversion.v, ApplicationComplete.v
- Eliminate axioms: 3, 11 (conversion and application)

MY OWNED FILES (only I can modify these):
- properties/TypedConversion.v
- properties/ApplicationComplete.v

DEPENDENCIES: I must WAIT for BOTH:
1. /workspaces/proof/06_COORDINATION/signals/PHASE_2_COMPLETE.signal
2. /workspaces/proof/06_COORDINATION/signals/PHASE_3_COMPLETE.signal

RULES I MUST FOLLOW:
1. NO AXIOMS - All proofs must be complete
2. NO ADMITS - Every proof case must be solved
3. VERIFY after every file: coqc -Q . RIINA <file>.v
4. CREATE SIGNAL after phase completion

CHECK: Do BOTH PHASE_2_COMPLETE.signal AND PHASE_3_COMPLETE.signal exist?
- If YES: Begin Phase 4
- If NO: Wait and check every 30 seconds
```

---

## TERMINAL 4: Worker ζ (Zeta) — STORE SEMANTICS

```bash
# 1. Open a new terminal
cd /workspaces/proof

# 2. Start Claude Code
claude

# 3. Paste this prompt:
```

**Prompt for Worker ζ:**
```
I am WORKER_ζ (Zeta) executing the AXIOM_ZERO_PARALLEL_PROTOCOL.

CRITICAL: Read these files FIRST:
1. /workspaces/proof/06_COORDINATION/AXIOM_ZERO_PARALLEL_PROTOCOL.md
2. /workspaces/proof/01_RESEARCH/AXIOM_ELIMINATION_ATTACK_PLAN.md

MY RESPONSIBILITIES:
- Phase 5: Create StoreRelation.v, ReferenceOps.v, Declassification.v
- Eliminate axioms: 16, 17, 18, 19 (semantic typing)

MY OWNED FILES (only I can modify these):
- properties/StoreRelation.v
- properties/ReferenceOps.v
- properties/Declassification.v

DEPENDENCY: I must WAIT for Phase 2 to complete.
Check for: /workspaces/proof/06_COORDINATION/signals/PHASE_2_COMPLETE.signal

RULES I MUST FOLLOW:
1. NO AXIOMS - All proofs must be complete
2. NO ADMITS - Every proof case must be solved
3. VERIFY after every file: coqc -Q . RIINA <file>.v
4. CREATE SIGNAL after phase completion

CHECK: Does PHASE_2_COMPLETE.signal exist?
- If YES: Begin Phase 5
- If NO: Wait and check every 30 seconds
```

---

## TERMINAL 5: Worker Ω (Omega) — VERIFICATION & INTEGRATION

```bash
# 1. Open a new terminal
cd /workspaces/proof

# 2. Start Claude Code
claude

# 3. Paste this prompt:
```

**Prompt for Worker Ω:**
```
I am WORKER_Ω (Omega) executing the AXIOM_ZERO_PARALLEL_PROTOCOL.

CRITICAL: Read these files FIRST:
1. /workspaces/proof/06_COORDINATION/AXIOM_ZERO_PARALLEL_PROTOCOL.md
2. /workspaces/proof/01_RESEARCH/AXIOM_ELIMINATION_ATTACK_PLAN.md

MY RESPONSIBILITIES:
- MONITORING: Continuously verify all worker outputs
- Phase 6: Integrate all proven lemmas into NonInterference.v
- FINAL: Create verification file and confirm ZERO AXIOMS

MY OWNED FILES (only I can modify these):
- properties/NonInterference.v (after Phase 6 starts)
- verification/*.v

MONITORING TASKS:
1. Every 5 minutes, run: make clean && make
2. Check for new signal files
3. Cross-verify worker outputs
4. Update GLOBAL_STATE.md

PHASE 6 TRIGGER: I must WAIT for BOTH:
1. /workspaces/proof/06_COORDINATION/signals/PHASE_4_COMPLETE.signal
2. /workspaces/proof/06_COORDINATION/signals/PHASE_5_COMPLETE.signal

BEGIN MONITORING NOW. Report current state of:
- Existing files in properties/ and termination/
- Current axiom count
- Current admitted count
```

---

## VERIFICATION COMMANDS (All Workers)

After creating any file:
```bash
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA <path/to/file>.v
```

After completing a phase:
```bash
cd /workspaces/proof/02_FORMAL/coq
make clean && make
grep -r "^Axiom " *.v | wc -l      # Count axioms
grep -r "Admitted\." *.v | wc -l   # Count admits
```

Create signal file:
```bash
echo "Phase X complete by WORKER_Y at $(date -u +%Y-%m-%dT%H:%M:%SZ)" > /workspaces/proof/06_COORDINATION/signals/PHASE_X_COMPLETE.signal
```

---

## EXPECTED PARALLEL EXECUTION TIMELINE

```
Time    │ α (Alpha)    │ β (Beta)     │ γ (Gamma)    │ ζ (Zeta)     │ Ω (Omega)
────────┼──────────────┼──────────────┼──────────────┼──────────────┼──────────────
Day 1-3 │ Phase 1      │ WAIT         │ WAIT         │ WAIT         │ Monitor
        │ ████████     │              │              │              │ ▓▓▓▓▓▓▓▓
Day 4-10│ Phase 2      │ Phase 3      │ WAIT         │ WAIT         │ Monitor
        │ ████████     │ ████████     │              │              │ ▓▓▓▓▓▓▓▓
Day 11+ │ (continue)   │ Phase 3      │ WAIT         │ Phase 5      │ Monitor
        │ ████████     │ ████████     │              │ ████████     │ ▓▓▓▓▓▓▓▓
Day 21+ │ Review       │ Review       │ Phase 4      │ Phase 5      │ Monitor
        │ ▒▒▒▒▒▒▒▒     │ ▒▒▒▒▒▒▒▒     │ ████████     │ ████████     │ ▓▓▓▓▓▓▓▓
Day 36+ │ ALL          │ ALL          │ ALL          │ ALL          │ Phase 6
        │ ▒▒▒▒▒▒▒▒     │ ▒▒▒▒▒▒▒▒     │ ▒▒▒▒▒▒▒▒     │ ▒▒▒▒▒▒▒▒     │ ████████

Legend: ████ = Active │ ▒▒▒▒ = Review/Support │ ▓▓▓▓ = Monitoring
```

---

## SUCCESS: AXIOM ZERO ACHIEVED

When all phases complete, Worker Ω creates:
```
/workspaces/proof/06_COORDINATION/signals/AXIOM_ZERO_ACHIEVED.signal
```

Final verification:
```bash
cd /workspaces/proof/02_FORMAL/coq
grep -r "^Axiom " *.v | wc -l       # Must be 0
grep -r "Admitted\." *.v | wc -l    # Must be 0
coqc -Q . RIINA verification/AxiomZeroVerify.v
# Output: "Closed under the global context"
```

---

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE*
