# Security Policy

## Reporting

If you discover a security issue in RIINA, please report it responsibly.

**Telegram:** [@ib823](https://t.me/ib823)

Please do **not** open a public GitHub issue for security reports.

## Response Timeline

- **72 hours** — Acknowledgment of your report
- **7 days** — Initial assessment and severity classification
- **30 days** — Target for fix or mitigation (critical issues prioritized)

## Scope

The following components are in scope:

- **Compiler** (`riinac`) — All compiler passes, code generation, and verification
- **Formal proofs** (`02_FORMAL/`) — Coq, Lean, and Isabelle proof files
- **Tooling** (`05_TOOLING/`) — Cryptographic primitives and build tools
- **Website** (`website/`) — Project website
- **VS Code extension** (`riina-vscode/`) — Language support extension

## Out of Scope

- Example programs in `07_EXAMPLES/` (educational, not production)
- Documentation content (unless it leaks secrets)

## Responsible Disclosure

We follow a coordinated disclosure process:

1. Reporter sends details via the contact above
2. We acknowledge receipt within 72 hours
3. We work with the reporter to understand and reproduce the issue
4. We develop and test a fix
5. We release the fix and credit the reporter (unless anonymity is requested)
6. We publish an advisory after the fix is available

## Recognition

We gratefully acknowledge security researchers who report issues responsibly. With your permission, we will credit you in our CHANGELOG and security advisories.

---

*RIINA takes security seriously. Our formal verification approach means many classes of bugs are mathematically impossible — but we remain vigilant about the components that fall outside our proof coverage.*
