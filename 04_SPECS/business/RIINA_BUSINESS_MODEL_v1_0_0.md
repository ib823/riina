# RIINA Business Model v1.0.0

**CONFIDENTIAL — INTERNAL ONLY — NEVER PUBLISH**

*Last updated: 2026-02-01*

---

## 1. The Moat

RIINA is the only programming language where compliance violations are **type errors**, not linter warnings. Every rule is backed by a Coq formal proof. This is not a feature — it is a category.

No competitor can replicate this without:
1. Building a formally verified type system (years of PhD-level work)
2. Mapping regulatory requirements to type-level constraints (domain expertise)
3. Maintaining proof validity as regulations change (ongoing cost)

**The moat is the proof. The product is the report.**

---

## 2. Revenue Model

### Tier 1: Open Source (Free)

| What's included | Purpose |
|----------------|---------|
| RIINA compiler (`riinac`) | Adoption — get developers using the language |
| Core type safety + noninterference proofs | Trust — the math is public and auditable |
| `--compliance` flag with basic rules | Hook — show what compliance checking looks like |
| 3 profiles with starter rules (PCI-DSS: 3/78, PDPA: 2/14, BNM: 1/26) | Taste — enough to demo, not enough to certify |
| Text report output | Awareness — users see the report format |

**Goal:** Maximize adoption. Every developer using RIINA is a future enterprise lead.

### Tier 2: Professional (Subscription)

| What's included | Pricing basis |
|----------------|--------------|
| Full rule packs per profile (e.g., PCI-DSS: 78/78 rules) | Per profile per year |
| JSON report output with digital signatures | Audit-grade artifact |
| Coverage gap analysis (what's checked vs. what's not) | Transparency builds trust |
| Quarterly rule updates as regulations change | Ongoing value |
| Email support | Standard SLA |

**Suggested pricing:**
- Single profile: USD $2,000–$5,000/year
- Bundle (3 profiles): USD $5,000–$12,000/year
- All 15 profiles: USD $15,000–$25,000/year

**Target:** Small-to-mid fintechs, healthtech startups, SaaS companies needing SOC2/ISO prep.

### Tier 3: Enterprise (Contract)

| What's included | Pricing basis |
|----------------|--------------|
| Everything in Professional | Base |
| Custom rule authoring (client-specific policies) | Per engagement |
| On-premise deployment + air-gapped builds | Per installation |
| Dedicated compliance engineer | Retainer |
| Signed audit certificates (see Section 4) | Per certificate |
| Pre-audit preparation packages | Per regulation |
| Priority SLA (4h response) | Included |
| Regulatory change alerts + impact analysis | Included |

**Suggested pricing:**
- Base enterprise license: USD $50,000–$150,000/year
- Custom rule development: USD $10,000–$30,000 per rule pack
- Audit certificate: USD $5,000–$20,000 per issuance
- Pre-audit package: USD $25,000–$75,000 per regulation

**Target:** Banks, telcos, government agencies, defense contractors, hospitals.

---

## 3. A La Carte Rule Marketplace (Phase 2)

### Design

Third-party auditors and compliance consultants publish rule packs to a RIINA registry. RIINA takes a platform fee.

```
riinac pkg install compliance-pack/pci-dss-full
riinac check --compliance pci-dss file.rii    # now uses full 78-rule pack
```

### Economics

| Party | Cut |
|-------|-----|
| Rule author (auditor/consultant) | 70% |
| RIINA platform | 30% |

### Rule pack requirements
- Each rule must reference the exact regulatory clause it enforces
- Rules must include test cases (positive + negative)
- Rules are reviewed for correctness before listing (quality gate)
- Optional: rule author can submit a Coq proof for the rule → "Formally Verified" badge

### Why auditors will publish
- New revenue stream for compliance firms
- Their clients already need these checks
- "Powered by RIINA" badge on their audit reports
- Access to RIINA's customer base

---

## 4. Certification & Audit Certificates

This is the highest-margin product line.

### What it is

A RIINA Compliance Certificate is a digitally signed document stating:

> "Source file X (SHA-256: Y) was checked by RIINA Compiler vZ against
> profile P at coverage C% with 0 violations on date D."

### Why it has value

1. **Tamper-proof** — Source hash + compiler version + timestamp
2. **Reproducible** — Anyone with the same compiler + rules can re-verify
3. **Proof-backed** — Each rule traces to a Coq theorem
4. **Machine-readable** — JSON report can feed into GRC tools (ServiceNow, Archer, etc.)

### Certificate tiers

| Tier | Coverage required | Validity | Price |
|------|------------------|----------|-------|
| Bronze | ≥25% of profile rules, 0 errors | 90 days | USD $1,000 |
| Silver | ≥50% of profile rules, 0 errors | 180 days | USD $3,000 |
| Gold | ≥75% of profile rules, 0 violations | 1 year | USD $7,500 |
| Platinum | 100% of profile rules, 0 violations | 1 year | USD $15,000 |

### Renewal
Certificates expire. Renewal requires re-running compliance check against the latest rule pack (regulations change). This creates recurring revenue.

### Multi-profile certificates
Organizations needing multiple certifications (e.g., a Malaysian bank needs BNM + PCI-DSS + PDPA) get a bundled rate.

---

## 5. Go-to-Market Strategy

### Phase 1: Malaysia First (Months 1–6)

**Why Malaysia:**
- BNM RMiT is mandatory for all licensed financial institutions
- PDPA enforcement is increasing
- Small market = can dominate quickly
- Bahasa Melayu syntax = cultural differentiation and national pride
- Founder's home market = relationships + regulatory knowledge

**Target accounts:**
- Top 10 Malaysian banks (Maybank, CIMB, RHB, Public Bank, AmBank, etc.)
- E-wallet operators (Touch 'n Go, GrabPay, Boost, BigPay, ShopeePay)
- Payment processors (iPay88, Razer Merchant Services, Revenue Monster)
- Fintech startups (regulated by BNM)

**Entry strategy:**
1. Free workshop: "Compiler-Enforced BNM RMiT Compliance" at bank tech teams
2. Pilot: Offer 3-month free Professional tier to 2-3 banks
3. Case study from pilot → sales material for the rest
4. BNM engagement: Present RIINA to BNM directly as a compliance tool they can recommend

**Revenue target:** 5 paying enterprise clients = ~USD $500K ARR

### Phase 2: ASEAN Expansion (Months 6–18)

**Markets:** Singapore (MAS TRM), Thailand (BOT), Indonesia (OJK), Philippines (BSP)

**Why ASEAN:**
- Similar regulatory landscape (Basel III derivatives)
- Regional banks operate across borders (compliance headache = our opportunity)
- MAS TRM is the gold standard — Singapore credibility opens every door

**Revenue target:** 15–20 enterprise clients = ~USD $2–3M ARR

### Phase 3: Global Verticals (Months 18–36)

**Expand by vertical, not geography:**
- PCI-DSS: Every company globally that processes cards
- HIPAA: US healthcare ($1.3M average breach penalty)
- DO-178C: Aviation (certification costs $10M+ per system — saving 10% = $1M value prop)
- SOX: Every US public company

**Revenue target:** USD $10–20M ARR

### Phase 4: Platform (Year 3+)

- Rule marketplace live
- Third-party auditors publishing rule packs
- GRC integration partnerships (ServiceNow, Archer, OneTrust)
- RIINA becomes the compliance infrastructure layer

**Revenue target:** USD $50M+ ARR → path to $1B valuation

---

## 6. Competitive Landscape

| Competitor | What they do | Why RIINA wins |
|-----------|-------------|----------------|
| SonarQube | Static analysis linting | Heuristic, not proven. False positives. No compliance reports. |
| Snyk | Dependency vulnerability scanning | Checks libraries, not your code's logic. |
| Veracode | Binary/source scanning | Black box. No formal proofs. Expensive and slow. |
| Semgrep | Pattern-based code search | Regex-level, not type-level. No soundness guarantee. |
| Formal methods tools (Frama-C, SPARK) | Formal verification for C/Ada | No compliance profiles. No Bahasa Melayu. No report generator. |

**RIINA's unique position:** Compliance checking at the type system level, backed by mathematical proofs, with machine-generated audit artifacts. Nobody else does this.

---

## 7. Cost Structure

### Engineering (Year 1)

| Role | Purpose | Est. cost/year |
|------|---------|---------------|
| Founder | Architecture, proofs, strategy | Equity only |
| 1 compiler engineer | Rule implementation, parser, codegen | USD $80–120K |
| 1 compliance domain expert | Regulatory mapping, rule authoring | USD $60–100K |
| Infrastructure | Hosting, CI, registry | USD $5–10K |

**Total Year 1 burn:** USD $150–230K (lean)

### Unit economics at scale

| Metric | Value |
|--------|-------|
| CAC (enterprise) | ~$5–10K (workshop + pilot + sales cycle) |
| ACV (enterprise) | $50–150K |
| LTV (5-year, 90% retention) | $225–675K |
| LTV/CAC ratio | 22–67x |
| Gross margin | >90% (software, no COGS) |

---

## 8. Funding Strategy

| Stage | Amount | Purpose | Timing |
|-------|--------|---------|--------|
| Bootstrap | $0 | Build MVP (done), get first 2-3 pilots | Now |
| Pre-seed | $250–500K | First hire, BNM certification push | After 2-3 pilot banks |
| Seed | $2–5M | ASEAN expansion, 5+ profiles at full coverage | After $500K ARR |
| Series A | $15–30M | Global verticals, marketplace, GRC integrations | After $3M ARR |

**Investor pitch in one line:** "We're building the Bloomberg Terminal of compliance — except instead of financial data, we verify that code is legally compliant, with mathematical proof."

---

## 9. Key Risks

| Risk | Mitigation |
|------|-----------|
| Slow enterprise sales cycle (6-12 months) | Start with free workshops + pilots to shorten |
| Regulations change faster than rules | Quarterly update cadence, marketplace for speed |
| Developers resist new language | Bahasa Melayu angle for Malaysian pride; FFI for gradual adoption |
| Competitor builds formal verification | 5+ years of Coq proofs = massive head start |
| Founder dependency (single person) | Document everything (CLAUDE.md, specs); hire early |

---

## 10. Implementation Roadmap (Technical)

### Immediate (Next 2 sessions)

1. Flesh out BNM RMiT profile to full coverage (26/26 rules)
2. Add digital signature to JSON reports (Ed25519, from riina-core)
3. Add `--certificate` flag that generates a signed compliance certificate

### Short-term (Next month)

4. PDPA full coverage (14/14 rules)
5. PCI-DSS full coverage (78/78 rules)
6. GRC export formats (SARIF for IDE integration, CSV for auditors)
7. Rule pack file format (`.riina-rules.toml`) for custom/third-party rules

### Medium-term (3 months)

8. Rule marketplace registry (hosted on riina.dev)
9. Certificate verification endpoint (verify.riina.dev)
10. Integration with ServiceNow / Archer APIs
11. Remaining 12 profiles at starter coverage

### Long-term (6 months)

12. All 15 profiles at ≥50% coverage
13. Third-party auditor onboarding program
14. SOC 2 Type II for RIINA itself (eat your own dog food)
15. ISO 27001 certification for RIINA the company

---

## 11. Success Metrics

| Milestone | Target date | Metric |
|-----------|-----------|--------|
| First PASS report on real bank code | Month 2 | 1 pilot |
| First paying enterprise customer | Month 4 | $50K+ ACV |
| BNM profile at full coverage | Month 3 | 26/26 rules |
| 5 enterprise customers (Malaysia) | Month 8 | $500K ARR |
| First Singapore customer | Month 12 | MAS TRM profile complete |
| Rule marketplace beta | Month 15 | 3+ third-party rule packs |
| $3M ARR | Month 24 | Seed round trigger |

---

*This document is the single source of truth for RIINA's business model.*
*Updated as strategy evolves. Never published externally.*

*"The moat is the proof. The product is the report."*
