# Security Policy

## Reporting a Vulnerability

If you discover a security vulnerability in RIINA, please report it responsibly.

**Contact:** Telegram [@AqilAziz823](https://t.me/AqilAziz823)

Please include:
- Description of the vulnerability
- Steps to reproduce
- Potential impact
- Suggested fix (if any)

## Response Timeline

- **Acknowledgment**: Within 48 hours
- **Initial Assessment**: Within 7 days
- **Fix Release**: Depends on severity

## Scope

The following are in scope:
- RIINA compiler (`riinac`)
- Type checker and effect system
- Code generation backends (C, WASM, mobile)
- Formal proof soundness

The following are out of scope:
- Third-party tools or services
- Social engineering

## Security Guarantees

RIINA provides mathematically proven security guarantees:
- **Non-interference**: Proven in Coq (7,929 Qed proofs, 0 Admitted)
- **Type safety**: Progress + Preservation formally verified
- **Effect safety**: Effect system soundness proven
- **Zero dependencies**: No third-party runtime dependencies

---

*RIINA — Rigorous Immutable Invariant, No Assumptions*
