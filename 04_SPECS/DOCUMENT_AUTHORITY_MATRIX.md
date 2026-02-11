# RIINA Document Authority Matrix

Date: 2026-02-10
Status: AUTHORITATIVE
Purpose: define which documents are allowed to drive execution decisions.

## Authority Levels

| Level | Meaning | Allowed for execution decisions |
|------|---------|----------------------------------|
| L0 | Live generated truth (machine outputs) | Yes, highest priority |
| L1 | Operational control docs (protocol + execution board) | Yes |
| L2 | Design/architecture references | Yes, when consistent with L0-L1 |
| L3 | Historical/context docs | No (reference only) |

## L0: Live Truth Sources

| File | Role | Refresh Trigger |
|------|------|-----------------|
| `PROOF_STATUS.md` | Active build proof ledger | `bash scripts/update-proof-ledger.sh --check` |
| `website/public/metrics.json` | Public claim levels and lane quality flags | `bash scripts/generate-metrics.sh` |
| `reports/public_quality_status.json` | Public quality gate output | `bash scripts/public-quality-gates.sh` |
| `reports/easier_gap_status.json` | Easier-gap closure status (items 1/2/9/12) | `bash scripts/check-easier-gaps.sh` |
| `reports/medium_gap_status.json` | Medium-gap closure status (items 1/2/3/4/9/12) | `bash scripts/check-medium-gaps.sh` |
| `reports/heavy_gap_status.json` | Heavy-gap foundation status (items 5/6/7/8/10/11/13) | `bash scripts/check-heavy-gaps.sh` |
| `reports/heavy_closure_status.json` | Heavy-gap executable closure tracker (items 5/6/7/8/10/11/13) | `bash scripts/check-heavy-closure.sh` |
| `reports/dim1_dim9_promotion_status.json` | Dim1/Dim9 promotion-readiness status | `bash scripts/check-dim1-dim9-promotion.sh` |

## L1: Operational Sources

| File | Role |
|------|------|
| `COMMIT_PROTOCOL.md` | Commit/deploy runbook and gate order |
| `DEPLOY_PROTOCOL.md` | Deterministic deploy sequence and strict publish gates |
| `04_SPECS/execution/RIINA_A_TO_Z_EXECUTION_BOARD.md` | Canonical execution plan, completion state, pending activities |

## L2: Design References

| File | Role |
|------|------|
| `04_SPECS/language/RIINA_MATERIALIZATION_PLAN_v1_0_0.md` | Program-level roadmap and implementation phases |
| `04_SPECS/RIINA_PRIME_DIRECTIVE_GAP_CLOSURE.md` | Gap taxonomy and bounded guarantees framing |
| `04_SPECS/scope/RIINA_RESEARCH_EXECUTION_MAP.md` | Research-to-execution mapping reference |
| `04_SPECS/scope/RIINA_ARCHITECTURE_CORRECTED.md` | Architecture direction and dependency model |
| `06_COORDINATION/DOMAIN_COVERAGE_MATRIX.md` | Automated coverage mapping reference |

## L3: Historical/Context-Only Docs

| File | Reason |
|------|--------|
| `01_RESEARCH/RIINA_DOMINANCE_STRATEGY_v2.md` | Superseded and stale counts |
| `06_COORDINATION/ATTACK_PROOF_MAP.md` | Contains stale axiom/count statements |
| `06_COORDINATION/AXIOM_ELIMINATION_STRATEGY.md` | Historical elimination inventory |
| `06_COORDINATION/axiom_elimination/EXECUTION_REPORT_v2.md` | Historical intermediate report |

## Conflict Resolution

If two documents conflict:
1. L0 wins over all.
2. L1 wins over L2 and L3.
3. L2 is advisory when consistent with L0-L1.
4. L3 never overrides L0-L2.

## Minimum Evidence Pack Before Claim Updates

1. `03_PROTO/target/release/riinac verify --full` passes.
2. `bash scripts/public-quality-gates.sh` passes.
3. `bash scripts/check-easier-gaps.sh` passes.
4. `bash scripts/check-medium-gaps.sh` passes.
5. `bash scripts/check-heavy-gaps.sh` passes.
6. `bash scripts/check-heavy-closure.sh` runs and report is current (use `--strict` only for promotion to independent-audit-grade claims).
7. `bash scripts/check-dim1-dim9-promotion.sh --strict-tools` passes.
8. `bash scripts/update-proof-ledger.sh --check` passes.
