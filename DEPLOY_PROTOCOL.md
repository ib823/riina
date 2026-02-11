# RIINA Deploy Protocol

Purpose: deterministic deploy runbook for publishing to `/riina` with strict proof-claim gates.

## Canonical command

```bash
bash scripts/godzilla-pipeline.sh deploy --deep-level 4
```

This command enforces:
1. strict Dim1/Dim9 promotion gate (`--strict-tools`, auto-provision formal jars when needed)
2. metrics regeneration from current repository state
3. public quality gates
4. full verifier stack and deep tooling verification
5. sync to public branch + deploy to `riina/gh-pages`
6. post-deploy endpoint verification

## Manual deterministic sequence

```bash
# 1) Ensure clean tree
git status

# 2) Optional explicit formal-tool provisioning (strict gate also auto-provisions)
bash scripts/provision-formal-tools.sh

# 3) Strict Dim1/Dim9 promotion gate (must pass)
bash scripts/check-dim1-dim9-promotion.sh --strict-tools

# 4) Regenerate claims + docs from live outputs
bash scripts/generate-metrics.sh --fast
bash scripts/sync-metrics.sh
bash scripts/audit-docs.sh

# 5) Heavy closure tracking gate (strict only when promoting independent-audit claims)
bash scripts/check-heavy-closure.sh

# 6) Public claim integrity gate
bash scripts/public-quality-gates.sh

# 7) Full verifier
03_PROTO/target/release/riinac verify --full
bash 05_TOOLING/scripts/verify.sh 4

# 8) Sync + deploy
bash scripts/sync-public.sh
bash scripts/deploy-website.sh
bash scripts/verify-riina-deploy.sh
```

## Hard fail conditions

Deploy is blocked when any of these are true:
- strict Dim1/Dim9 promotion gate fails
- quality gates fail
- `metrics.json` claim levels exceed evidence
- verifier stack fails
- endpoint verification fails

## Evidence artifacts to retain

- `reports/dim1_dim9_promotion_status.json`
- `reports/public_quality_status.json`
- `website/public/metrics.json`
- `VERIFICATION_MANIFEST.md`
- `reports/easier_gap_status.json`
- `reports/medium_gap_status.json`
- `reports/heavy_gap_status.json`
