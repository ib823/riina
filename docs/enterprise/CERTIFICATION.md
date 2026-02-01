# RIINA Certification Output

## What RIINA Certifies

When you build a RIINA program, the compiler can produce a **proof certificate** — a machine-readable document that maps your program's security properties to independently verifiable Coq theorems.

This is not a test report. This is a mathematical proof that your program satisfies specific security properties.

## Certificate Format

```
┌──────────────────────────────────────────────────────┐
│ RIINA PROOF CERTIFICATE                              │
├──────────────────────────────────────────────────────┤
│ Program     : myapp.rii                              │
│ Compiled    : 2026-01-31T14:30:00Z                   │
│ Compiler    : riinac 0.1.0                           │
│ Prover      : Rocq 9.1 (Coq 8.21)                   │
│ Certificate : SHA-256 of proof objects                │
├──────────────────────────────────────────────────────┤
│                                                      │
│ PROVEN PROPERTIES                                    │
│                                                      │
│ ✓ Type Safety                                        │
│   Progress + Preservation theorems                   │
│   Coq: type_system/TypeSafety.v                      │
│                                                      │
│ ✓ Non-Interference                                   │
│   Secret data cannot flow to public outputs          │
│   Coq: properties/NonInterference_v2.v               │
│                                                      │
│ ✓ Effect Safety                                      │
│   Functions cannot perform undeclared effects         │
│   Coq: effects/EffectSafety.v                        │
│                                                      │
│ ✓ Declassification Correctness                       │
│   Secrets only released through authorized policy     │
│   Coq: properties/Declassification.v                 │
│                                                      │
│ AXIOMS (5, all justified)                            │
│   See: 02_FORMAL/coq/AXIOM_JUSTIFICATION.md          │
│                                                      │
│ VERIFICATION                                         │
│   To independently verify:                           │
│   $ cd 02_FORMAL/coq && make                         │
│   Expected: 244 files, 0 errors, 0 admits            │
│                                                      │
└──────────────────────────────────────────────────────┘
```

## Generating Certificates

```bash
# Type-check and generate certificate
riinac build --certificate myapp.rii

# Output: myapp.certificate.json
```

## Certificate Verification (Zero-Trust)

Anyone can verify a RIINA certificate independently:

```bash
# 1. Clone the RIINA repository
git clone https://github.com/ib823/proof.git

# 2. Build the Coq proofs from source
cd proof/02_FORMAL/coq && make

# 3. Check that no proofs use admits
grep -r "Admitted\|admit" *.v
# Expected: no output (0 admits)

# 4. Check axiom count
grep -r "^Axiom " *.v | wc -l
# Expected: 5 (all justified)

# 5. Verify specific theorem
coqc -Q . RIINA properties/NonInterference_v2.v
Print Assumptions non_interference.
```

If step 2 succeeds with no errors, every theorem in the certificate is valid.

## Use Cases

### Regulatory Compliance

Attach the certificate to compliance submissions. It demonstrates that security controls are **mathematically proven**, satisfying formal methods requirements in:

- **Common Criteria (EAL5-7)** — Formally verified design
- **DO-178C (DAL-A)** — Formal methods supplement
- **ISO 26262 (ASIL-D)** — Proven absence of interference
- **HIPAA** — Proven access control and encryption
- **PCI-DSS** — Proven cardholder data isolation

### Security Audits

Replace manual code review for covered properties. The certificate proves that:

- No information leaks between security levels (non-interference)
- No unauthorized side effects (effect safety)
- No runtime type errors (type safety)
- No uncontrolled declassification

### Supply Chain Security

The certificate includes:

- SHA-256 hash of the compiled program
- SHA-256 hash of the Coq proof objects
- The exact compiler version used
- Zero external dependencies (auditable from source)

### Insurance / Liability

Proof certificates provide evidence that security was **provably correct** at the time of compilation. This can support:

- Cybersecurity insurance claims
- Due diligence evidence
- Liability defense (demonstrated best-in-class security practice)

## What Certificates Do NOT Cover

Certificates prove properties of the **RIINA program** as compiled. They do not cover:

- The correctness of external C libraries called via FFI
- The security of the deployment environment (OS, hardware)
- Business logic correctness (only security properties)
- Physical security of the running system

For hardware-level guarantees, see Track S (Hardware Contracts) and Track U (Runtime Guardian) in the formal proofs.

---

*RIINA — Security proven. Mathematically verified. Certifiably correct.*
