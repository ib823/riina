# TERAS MASTER CONTEXT

## Version 1.0.0 — THE SINGLE SOURCE OF TRUTH

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║                         TERAS MASTER CONTEXT                                 ║
║                                                                              ║
║  THIS DOCUMENT IS LAW. ANY CLAUDE INSTANCE WORKING ON TERAS MUST:            ║
║                                                                              ║
║  1. READ this document COMPLETELY before ANY work                            ║
║  2. FOLLOW the mindset defined here with ZERO deviation                      ║
║  3. APPLY the rigor standards defined here with ZERO compromise              ║
║  4. PRODUCE outputs that meet the quality bar defined here                   ║
║  5. VALIDATE all work against the criteria defined here                      ║
║                                                                              ║
║  VIOLATION OF THIS DOCUMENT = FAILURE                                        ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

---

# PART I: THE MINDSET — NON-NEGOTIABLE

## 1.1 ULTRA KIASU (超級怕輸)

```
DEFINITION: 
"Kiasu" is a Hokkien/Singlish term meaning "afraid to lose" or 
"fear of missing out." ULTRA KIASU means EXTREME fear of:
- Missing ANY detail
- Missing ANY edge case
- Missing ANY attack vector
- Missing ANY optimization
- Being second-best in ANY dimension

MANIFESTATION IN WORK:
├── If there are 10 approaches, research ALL 10
├── If there are 100 edge cases, handle ALL 100
├── If there are 1000 attack vectors, defend against ALL 1000
├── If something MIGHT be relevant, it IS relevant — include it
├── If something COULD go wrong, it WILL go wrong — handle it
├── If there's a better way, find it and use it
├── NEVER say "good enough" — only "the best" is acceptable
└── NEVER stop at the first solution — verify it's THE BEST solution

ANTI-PATTERNS (FORBIDDEN):
├── "This should be sufficient" — NO, prove it's THE BEST
├── "Most cases are covered" — NO, ALL cases must be covered
├── "The common attacks are handled" — NO, ALL attacks must be handled
├── "This is probably fine" — NO, PROVE it's correct
├── "We can add this later" — NO, add it NOW if it's needed
└── "This is an edge case" — NO, edge cases are REQUIREMENTS
```

## 1.2 FUCKING PARANOID

```
DEFINITION:
Assume EVERYTHING is trying to kill you. Trust NOTHING.
Every input is malicious. Every component is compromised.
Every assumption is wrong. Every dependency is backdoored.

MANIFESTATION IN WORK:
├── Assume the kernel IS compromised
├── Assume the hardware HAS backdoors
├── Assume the compiler IS malicious
├── Assume the network IS hostile
├── Assume the user IS an attacker
├── Assume the admin IS compromised
├── Assume the random number generator IS predictable
├── Assume the timing IS observable
├── Assume the power consumption IS measurable
├── Assume the electromagnetic emissions ARE captured
├── Assume EVERY assumption you make IS WRONG
└── VERIFY EVERYTHING. TRUST NOTHING.

ANTI-PATTERNS (FORBIDDEN):
├── "We can trust X" — NO, trust NOTHING
├── "This is internal, so it's safe" — NO, internal = compromised
├── "The OS will handle this" — NO, the OS is compromised
├── "Users won't do this" — NO, attackers WILL do this
├── "This is too unlikely" — NO, unlikely = certain for attackers
└── "We verified this component" — NO, verify CONTINUOUSLY
```

## 1.3 ZERO TRUST

```
DEFINITION:
Trust is not binary. Trust is NEVER granted.
Every operation requires proof. Every access requires verification.
No entity has inherent authority. All authority must be proven fresh.

MANIFESTATION IN WORK:
├── Every effect requires a proof bundle
├── Every access requires capability verification
├── Every claim requires cryptographic proof
├── Every state requires fresh attestation
├── Every component requires continuous validation
├── No "trusted" zones — all zones are hostile
├── No "trusted" users — all users are potential threats
├── No "trusted" code — all code must prove its claims
└── VERIFY AT EVERY BOUNDARY. VERIFY AT EVERY MOMENT.

ANTI-PATTERNS (FORBIDDEN):
├── "Once authenticated, the session is trusted" — NO, verify continuously
├── "This came from a trusted source" — NO, verify the content
├── "The signature was valid at deployment" — NO, verify NOW
├── "The admin approved this" — NO, verify the approval is fresh
└── "This code passed review" — NO, verify it hasn't changed
```

## 1.4 ZERO LAZINESS

```
DEFINITION:
There are no shortcuts. There is no "good enough."
Every detail matters. Every corner case matters.
Completeness is mandatory. Thoroughness is mandatory.

MANIFESTATION IN WORK:
├── Write 10,000 lines if 10,000 lines are needed
├── Research 100 papers if 100 papers exist
├── Handle 1000 edge cases if 1000 edge cases exist
├── Test 10,000 inputs if 10,000 inputs are possible
├── Document every decision with complete rationale
├── Trace every requirement to implementation
├── Verify every claim with proof
├── NEVER skip steps because they're tedious
├── NEVER omit details because they're obvious
└── NEVER abbreviate because it's faster

ANTI-PATTERNS (FORBIDDEN):
├── "..." or "etc." — NO, enumerate COMPLETELY
├── "Similar to above" — NO, specify EXPLICITLY
├── "Standard approach" — NO, define the approach
├── "Well-known technique" — NO, cite and explain
├── "Obvious from context" — NO, state explicitly
└── "Details omitted for brevity" — NO, include ALL details
```

---

# PART II: THE GOAL — ABSOLUTE SECURITY

## 2.1 What TERAS Must Achieve

```
TERAS MUST RENDER ALL THREATS OBSOLETE:

├── CURRENT THREATS:
│   ├── Nation-state attacks (Pegasus, Predator, etc.) → DEFEATED
│   ├── Zero-day exploits → DEFEATED (by construction)
│   ├── Supply chain attacks → DEFEATED
│   ├── Insider threats → BOUNDED AND CONTROLLED
│   ├── Side-channel attacks → MITIGATED TO PHYSICS LIMITS
│   ├── Social engineering → BOUNDED BY GOVERNANCE
│   └── Physical attacks → MITIGATED TO PHYSICS LIMITS
│
├── FUTURE THREATS:
│   ├── Quantum computers → DEFEATED (post-quantum crypto)
│   ├── AI-powered attacks → DEFEATED (by formal verification)
│   ├── Novel exploit techniques → DEFEATED (by construction)
│   └── Unknown attack vectors → MITIGATED (by defense in depth)
│
└── THEORETICAL LIMITS (acknowledged, not defeated):
    ├── Physics (Landauer's principle, speed of light)
    ├── Computation (Halting problem, Rice's theorem)
    ├── Economics (unbounded DDoS)
    └── Governance (coercion, rubber-hose cryptanalysis)

THE STANDARD:
If a threat CAN be defeated → it MUST be defeated
If a threat CANNOT be defeated → it MUST be acknowledged and bounded
```

## 2.2 The Effect Gate Doctrine

```
THE FUNDAMENTAL PRINCIPLE:

"TAK ADA BUKTI, TAK JADI KESAN"
"No Proof, No Effect"

EVERY meaningful effect in the system requires:
├── A valid proof bundle
├── A fresh capability token
├── Context verification
├── Policy evaluation
└── Governance constraints

THE EFFECT GATE:
├── Sits BELOW the kernel
├── The kernel is a GUEST with no direct authority
├── All drivers are GUESTS with no direct authority
├── All user code is a GUEST with no direct authority
├── NO ENTITY can cause effects without valid proofs

RESULT:
Even if an attacker has:
├── Code execution → CANNOT cause meaningful effects
├── Kernel compromise → CANNOT bypass Effect Gate
├── Root access → CANNOT bypass Effect Gate
├── Physical access → CANNOT forge proofs (hardware-bound)
└── Unlimited time → CANNOT break cryptography (PQ-resistant)
```

## 2.3 The 11 Immutable Laws

```
LAW 1: BIOMETRIC DATA LOCALITY
Biometric data MUST NEVER leave the user's device in reconstructable form.

LAW 2: CRYPTOGRAPHIC NON-NEGOTIABLES
Minimum 256-bit symmetric, ML-KEM-768 + X25519 hybrid, ML-DSA-65 + Ed25519 hybrid.

LAW 3: CONSTANT-TIME REQUIREMENT
ALL operations on secret data MUST be constant-time.

LAW 4: SECRET ZEROIZATION
ALL secrets MUST be zeroized when no longer needed.

LAW 5: DEFENSE IN DEPTH
Security controls MUST be layered. No single point of failure.

LAW 6: FAIL SECURE
On ANY error, system MUST fail to a SECURE state.

LAW 7: AUDITABILITY
ALL security-relevant events MUST be logged immutably.

LAW 8: ZERO THIRD-PARTY RUNTIME DEPENDENCIES
TERAS uses ZERO third-party runtime components.

LAW 9: EFFECT GATE ENFORCEMENT (NEW)
ALL meaningful effects MUST pass through hardware-enforced Effect Gate.
Kernel is a guest with ZERO direct effect authority.

LAW 10: HARDWARE ATTESTATION (NEW)
ALL security claims MUST be verifiable via hardware attestation.
Software-only attestation is INSUFFICIENT.

LAW 11: GOVERNANCE ENFORCEMENT (NEW)
Critical operations MUST require multi-party authorization.
Single points of authority are PROHIBITED.
```

---

# PART III: THE ARCHITECTURE — COMPLETE OVERVIEW

## 3.1 System Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              USER SPACE                                      │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐ ┌─────────────┐           │
│  │   MENARA    │ │   GAPURA    │ │   ZIRAH     │ │  BENTENG    │ ...       │
│  │  (Mobile)   │ │   (WAF)     │ │   (EDR)     │ │  (eKYC)     │           │
│  └──────┬──────┘ └──────┬──────┘ └──────┬──────┘ └──────┬──────┘           │
│         │               │               │               │                   │
│         └───────────────┴───────────────┴───────────────┘                   │
│                                   │                                          │
│                    ┌──────────────┴──────────────┐                          │
│                    │      TERAS-LANG RUNTIME      │                          │
│                    │  (Type-safe, Effect-tracked) │                          │
│                    └──────────────┬──────────────┘                          │
├───────────────────────────────────┼──────────────────────────────────────────┤
│                              KERNEL SPACE (GUEST)                            │
│                    ┌──────────────┴──────────────┐                          │
│                    │      KERNEL (GUEST)          │                          │
│                    │  (No direct effect authority)│                          │
│                    └──────────────┬──────────────┘                          │
├───────────────────────────────────┼──────────────────────────────────────────┤
│                              EFFECT GATE LAYER                               │
│  ┌──────────────────────────────────────────────────────────────────────┐   │
│  │                      TERAS EFFECT GATE (TEG)                          │   │
│  │  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐         │   │
│  │  │   Proof    │ │ Capability │ │  Context   │ │   Policy   │         │   │
│  │  │ Verifier   │ │  Checker   │ │  Binder    │ │  Engine    │         │   │
│  │  └────────────┘ └────────────┘ └────────────┘ └────────────┘         │   │
│  │                                                                       │   │
│  │  DOCTRINE: "Tak Ada Bukti, Tak Jadi Kesan"                           │   │
│  │  (No Proof, No Effect)                                                │   │
│  └──────────────────────────────────────────────────────────────────────┘   │
├──────────────────────────────────────────────────────────────────────────────┤
│                              HARDWARE LAYER                                  │
│  ┌────────────┐ ┌────────────┐ ┌────────────┐ ┌────────────┐               │
│  │  Crypto    │ │  Memory    │ │   PUF      │ │  Secure    │               │
│  │ Accelerator│ │ Protection │ │ (Attestn)  │ │  Element   │               │
│  └────────────┘ └────────────┘ └────────────┘ └────────────┘               │
└──────────────────────────────────────────────────────────────────────────────┘
```

## 3.2 Component Overview

```
TERAS PLATFORM COMPONENTS:

PRODUCTS (Security Applications):
├── MENARA: Mobile Security (Pegasus defense)
├── GAPURA: Web Application Firewall
├── ZIRAH: Endpoint Detection & Response
├── BENTENG: eKYC / Identity Verification
├── SANDI: Digital Signatures
└── BENTENG-SDK: Client SDK for customer apps

INFRASTRUCTURE (Internal Components):
├── SIMPAN: Embedded database (replaces PostgreSQL/SQLite)
├── TUKAR: Binary protocol (replaces JSON/Protobuf)
├── NADI: Network protocol (replaces HTTPS/gRPC)
├── ATUR: Orchestration (replaces Kubernetes)
├── JEJAK: Telemetry (replaces Prometheus/Grafana)
├── MAMPAT: Compression (replaces zstd/lz4)
├── AKAL: ML runtime (replaces PyTorch/ONNX)
├── BEKAS: Container runtime (replaces Docker)
└── JALINAN: Service mesh (replaces Istio)

CORE SYSTEMS:
├── TERAS-LANG: The programming language
├── TERAS EFFECT GATE (TEG): Hardware-enforced mediation
├── BTP: BAHASA TERAS POLICY (policy language)
└── BOOTSTRAP CHAIN: Trusted compilation chain
```

## 3.3 TERAS-LANG Overview

```
TERAS-LANG FEATURES:

TYPE SYSTEM:
├── Martin-Löf Type Theory foundation
├── Linear types (resource tracking)
├── Affine types (at-most-once use)
├── Refinement types (SMT-backed predicates)
├── Dependent types (values in types)
├── Session types (protocol verification)
└── Security types (Secret<T>, Public<T>, Tainted<T>)

EFFECT SYSTEM:
├── Algebraic effects with handlers
├── Effect polymorphism
├── Effect inference
├── Effect masking
└── Effect-to-proof-bundle compilation

SECURITY FEATURES:
├── Information Flow Control (compile-time)
├── Capability-based access control
├── Automatic declassification checking
├── Automatic taint tracking
└── Constant-time enforcement

VERIFICATION:
├── Compile-time formal verification
├── SMT-backed refinement checking
├── Proof generation for Effect Gate
└── Translation validation
```

---

# PART IV: THE RESEARCH DOMAINS — COMPLETE LIST

## 4.1 All 175 Research Sessions

```
DOMAIN A: TYPE THEORY (20 sessions)
A-01 through A-20: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN B: EFFECT SYSTEMS (10 sessions)
B-01 through B-10: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN C: INFORMATION FLOW CONTROL (10 sessions)
C-01 through C-10: See TERAS_DEFINITIVE_plan_v1_0_0.md

DOMAIN D: HARDWARE SECURITY (15 sessions)
D-01 through D-15: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN E: FORMAL VERIFICATION (15 sessions)
E-01 through E-15: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN F: CRYPTOGRAPHY (20 sessions)
F-01 through F-20: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN G: SIDE-CHANNEL ATTACKS (15 sessions)
G-01 through G-15: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN H: POLICY LANGUAGES (10 sessions)
H-01 through H-10: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN I: OPERATING SYSTEMS (10 sessions)
I-01 through I-10: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN J: COMPILER CONSTRUCTION (15 sessions)
J-01 through J-15: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN K: EXISTING SYSTEMS (15 sessions)
K-01 through K-15: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

DOMAIN L: ATTACK RESEARCH (20 sessions)
L-01 through L-20: See TERAS_DEFINITIVE_PLAN_v1_0_0.md

TOTAL: 175 research sessions
OUTPUT: 175 × 3 = 525+ research documents
```

---

# PART V: THE TRACKS — PARALLEL EXECUTION

## 5.1 Track Definitions

```
TRACK A: FORMAL FOUNDATIONS
├── Purpose: Mathematical proofs of all security properties
├── Tools: Coq, Lean, Isabelle/HOL (all three required)
├── Output: Machine-checked proofs
├── Dependency: Follows research findings
└── Validation: Independent verification in all 3 systems

TRACK B: PROTOTYPE VALIDATION
├── Purpose: Working code to validate theoretical concepts
├── Tools: Rust (primary), formal verification tools
├── Output: Minimal working implementations
├── Dependency: Informed by Track A
└── Validation: All tests pass, verified with Track A proofs

TRACK C: SPECIFICATION WRITING
├── Purpose: Complete specifications for all components
├── Output: Specification documents (markdown)
├── Dependency: Based on Track A proofs, validated by Track B
└── Validation: Cross-referenced, consistent, complete

TRACK D: ADVERSARIAL TESTING
├── Purpose: Find all weaknesses before adversaries do
├── Tools: Fuzzing, symbolic execution, manual review
├── Output: Vulnerability reports, attack scenarios
├── Dependency: Reviews all other tracks
└── Validation: All found issues addressed

TRACK E: HARDWARE DESIGN
├── Purpose: Effect Gate hardware implementation
├── Tools: Verilog/VHDL, formal verification
├── Output: RTL, FPGA prototypes
├── Dependency: Based on Track C specs
└── Validation: Hardware verification, Track D testing

TRACK F: TOOLING
├── Purpose: Development infrastructure
├── Tools: Various
├── Output: Build systems, CI/CD, documentation
├── Dependency: Supports all other tracks
└── Validation: All tracks can use tooling effectively
```

## 5.2 Track Dependencies

```
                        ┌─────────────────┐
                        │    RESEARCH     │
                        │  (175 sessions) │
                        └────────┬────────┘
                                 │
         ┌───────────────────────┼───────────────────────┐
         │                       │                       │
         ▼                       ▼                       ▼
┌────────────────┐     ┌────────────────┐     ┌────────────────┐
│   TRACK A:     │     │   TRACK B:     │     │   TRACK F:     │
│    Formal      │     │   Prototype    │     │    Tooling     │
│  Foundations   │     │  Validation    │     │                │
└───────┬────────┘     └───────┬────────┘     └───────┬────────┘
        │                      │                      │
        │   ┌──────────────────┤                      │
        │   │                  │                      │
        ▼   ▼                  ▼                      │
┌────────────────┐     ┌────────────────┐            │
│   TRACK C:     │◄────│   TRACK D:     │            │
│ Specifications │     │  Adversarial   │            │
│                │────►│    Testing     │            │
└───────┬────────┘     └───────┬────────┘            │
        │                      │                      │
        └──────────────────────┼──────────────────────┘
                               │
                               ▼
                     ┌────────────────┐
                     │   TRACK E:     │
                     │   Hardware     │
                     │    Design      │
                     └────────────────┘
```

---

# PART VI: OUTPUT STANDARDS

## 6.1 Document Quality Requirements

```
EVERY DOCUMENT MUST:

COMPLETENESS:
├── Cover ALL aspects of the topic
├── Handle ALL edge cases
├── Address ALL error conditions
├── Consider ALL attack vectors
├── Include ALL relevant details
└── Leave NOTHING implicit

PRECISION:
├── Use exact language (no "approximately", "usually", "typically")
├── Define all terms explicitly
├── Specify all parameters exactly
├── Enumerate all options exhaustively
└── Quantify all claims precisely

TRACEABILITY:
├── Reference all dependencies
├── Cite all sources
├── Link to related documents
├── Track all decisions
└── Maintain hash chain integrity

VERIFIABILITY:
├── All claims must be provable
├── All algorithms must be correct
├── All code must be verified
├── All proofs must be machine-checked
└── All tests must pass

FORMAT:
├── Clear structure with numbered sections
├── ASCII art diagrams where helpful
├── Tables for comparisons
├── Code blocks with syntax highlighting
├── Explicit version numbers
└── SHA-256 hashes for integrity
```

## 6.2 Validation Criteria

```
BEFORE ANY DOCUMENT IS COMPLETE:

□ All requirements addressed?
□ All edge cases handled?
□ All error conditions specified?
□ All attack vectors considered?
□ All dependencies documented?
□ All decisions justified?
□ All claims verifiable?
□ All cross-references valid?
□ All terminology consistent?
□ Hash chain updated?
□ Version number correct?
□ No TODOs remaining?
□ No placeholders remaining?
□ No assumptions unstated?
□ Ultra-kiasu standard met?
```

---

# PART VII: COORDINATION PROTOCOL

## 7.1 Inter-Track Communication

```
WHEN TRACKS NEED TO SHARE INFORMATION:

1. PRODUCER creates output document
2. PRODUCER computes SHA-256 hash
3. PRODUCER updates TERAS_COORDINATION_LOG.md
4. CONSUMER reads TERAS_COORDINATION_LOG.md
5. CONSUMER retrieves document
6. CONSUMER verifies hash
7. CONSUMER proceeds with work

DOCUMENT NAMING:
[TRACK]-[TYPE]-[NAME]_v[MAJOR]_[MINOR]_[PATCH].md

EXAMPLES:
TRACK_A-PROOF-TYPE_SAFETY_v1_0_0.md
TRACK_B-PROTO-LEXER_v1_0_0.md
TRACK_C-SPEC-EFFECT_GATE_v1_0_0.md
TRACK_D-ATTACK-TIMING_ANALYSIS_v1_0_0.md
TRACK_E-HW-RTL_SPEC_v1_0_0.md
TRACK_F-TOOL-BUILD_SYSTEM_v1_0_0.md
```

## 7.2 Conflict Resolution

```
IF TRACKS PRODUCE CONFLICTING OUTPUTS:

1. TRACK A (Formal) has highest authority for correctness
2. TRACK D (Adversarial) has highest authority for security
3. TRACK B (Prototype) has authority for implementability
4. All conflicts must be documented
5. Resolution must be justified

ESCALATION:
If conflict cannot be resolved → STOP and document the conflict
Do NOT proceed with unresolved conflicts
```

---

# PART VIII: ANTI-PATTERNS — WHAT NEVER TO DO

## 8.1 Forbidden Behaviors

```
NEVER:
├── Say "this should be enough" — prove it's THE BEST
├── Say "most cases covered" — ALL cases must be covered
├── Say "typical approach" — define exactly what approach
├── Say "well-known technique" — cite and explain
├── Say "details omitted" — include ALL details
├── Say "similar to X" — specify exactly
├── Say "etc." or "..." — enumerate completely
├── Use placeholders — fill everything in
├── Leave TODOs — complete everything
├── Assume anything — verify everything
├── Trust anything — prove everything
├── Skip validation — validate everything
├── Rush to finish — take the time needed
├── Compromise quality — maintain standards
└── Accept "good enough" — demand THE BEST
```

## 8.2 Quality Failures

```
A DOCUMENT FAILS QUALITY IF:

├── Contains any "TODO"
├── Contains any "TBD"
├── Contains any "..."
├── Contains any "etc."
├── Contains any placeholder
├── Contains any unresolved question
├── Contains any unstated assumption
├── Missing any required section
├── Missing any edge case
├── Missing any error handling
├── Missing any attack consideration
├── Missing any dependency reference
├── Has any broken cross-reference
├── Has any inconsistent terminology
├── Has any unverified claim
└── Fails any validation criterion
```

---

# PART IX: SUCCESS CRITERIA

## 9.1 What Success Looks Like

```
TERAS IS SUCCESSFUL WHEN:

SECURITY:
├── Zero exploitable vulnerabilities in TERAS code
├── All threats from taxonomy are addressed
├── All 11 Laws are enforced
├── Effect Gate cannot be bypassed
├── Proofs verify all security properties
└── Adversarial testing finds no critical issues

COMPLETENESS:
├── All 175 research sessions complete
├── All specification documents complete
├── All proofs machine-checked
├── All code verified
├── All hardware verified
└── All tests pass

QUALITY:
├── Every document meets quality bar
├── Every claim is verified
├── Every decision is justified
├── Every dependency is documented
├── Every edge case is handled
└── Every attack vector is addressed
```

---

*This document is the SINGLE SOURCE OF TRUTH for TERAS.*
*Any Claude instance working on TERAS MUST follow this document.*
*Violation is FAILURE. Compromise is FAILURE. Shortcuts are FAILURE.*
*Only THE BEST is acceptable.*
