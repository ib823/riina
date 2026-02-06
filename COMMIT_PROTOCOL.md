# RIINA COMMIT PROTOCOL — MANDATORY FOR ALL CONTRIBUTORS

```
╔══════════════════════════════════════════════════════════════════════════════╗
║                                                                              ║
║  ZERO TRUST COMMIT PROTOCOL                                                  ║
║                                                                              ║
║  Trust no one. Trust nothing. Verify everything.                             ║
║  This protocol is MANDATORY. No exceptions. Ever.                            ║
║                                                                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

## 0. BEFORE ANYTHING ELSE

**Every session, before ANY work:**

```bash
# 1. Verify hooks are installed
ls -la .git/hooks/pre-commit .git/hooks/pre-push

# If they don't exist or are wrong:
bash 00_SETUP/scripts/install_hooks.sh

# 2. Verify riinac exists and works
./03_PROTO/target/release/riinac verify --fast

# If riinac doesn't exist:
cd 03_PROTO && cargo build --release -p riinac && cd ..
```

**If hooks are not installed, STOP. Install them first. No exceptions.**

---

## 1. DOCUMENTATION AUDIT (MANDATORY BEFORE COMMIT)

Before ANY commit, you MUST audit ALL documentation files. This is not optional.

### 1.1 Core Documents to Audit

| File | What to Check | Update If |
|------|---------------|-----------|
| `CLAUDE.md` | Session number, Qed counts, Admitted counts, axiom counts, file counts, test counts | Any metric changed |
| `PROGRESS.md` | Current session entry, task status, metrics | Any work completed |
| `SESSION_LOG.md` | Session entry with date, tasks, outcomes | Every session |
| `README.md` | Hero metrics, comparison table | Metrics changed significantly |
| `VERSION` | Semver version | Release milestone |
| `CHANGELOG.md` | Release notes | Any user-facing change |
| `VERIFICATION_MANIFEST.md` | Auto-generated | Run `riinac verify --full` |

### 1.2 Website Documents to Audit

| File | What to Check | Update If |
|------|---------------|-----------|
| `website/src/RiinaWebsite.jsx` | Hero stats, release data | Metrics changed |
| `website/public/metrics.json` | Auto-generated | Run `scripts/generate-metrics.sh` |

### 1.3 Coordination Documents

| File | What to Check |
|------|---------------|
| `06_COORDINATION/COORDINATION_LOG.md` | Version, session, audit date |
| `06_COORDINATION/DECISIONS.md` | Any architectural decisions made |

### 1.4 Audit Script

Run this before EVERY commit:

```bash
bash scripts/audit-docs.sh
```

This script will:
1. Count current Qed proofs, admits, axioms
2. Compare against documented values
3. Flag any discrepancies
4. Generate an audit report

---

## 2. COMMIT CHECKLIST (MANDATORY)

Before running `git commit`, verify ALL of the following:

```
[ ] Hooks installed (ls -la .git/hooks/pre-commit .git/hooks/pre-push)
[ ] riinac verify --fast passes
[ ] Documentation audit complete (bash scripts/audit-docs.sh)
[ ] All flagged documents updated OR explicitly marked "no change needed"
[ ] Commit message follows format: [TRACK_X] TYPE: Description
[ ] No secrets in staged files
[ ] No Admitted in active Coq build (unless justified and documented)
```

---

## 3. PUSH CHECKLIST (MANDATORY)

Before running `git push origin main`:

```
[ ] All commit checklist items verified
[ ] riinac verify --full passes (will run automatically via pre-push hook)
[ ] VERIFICATION_MANIFEST.md updated
[ ] GPG signing enabled (optional but recommended)
```

---

## 4. PUBLIC SYNC CHECKLIST (MANDATORY)

Before running `bash scripts/sync-public.sh`:

```
[ ] main branch is pushed and verified
[ ] No internal files will leak to public (script handles this)
[ ] Website metrics are current
```

---

## 5. WEBSITE DEPLOY CHECKLIST (MANDATORY)

Before running `npm run deploy` in website/:

```
[ ] Public branch is synced
[ ] metrics.json regenerated (scripts/generate-metrics.sh)
[ ] Website builds without errors (npm run build)
[ ] All hero stats match CLAUDE.md
[ ] Release information is current
```

---

## 6. THE CARDINAL RULES

1. **NEVER commit without running the audit**
2. **NEVER push without verification passing**
3. **NEVER deploy without syncing public first**
4. **NEVER trust that hooks are installed — verify**
5. **NEVER trust that documentation is current — audit**
6. **NEVER skip steps because "it's a small change"**
7. **NEVER trust external systems (GitHub, CI, AI) — own verification**

---

## 7. ENFORCEMENT

This protocol is enforced by:

1. **Pre-commit hook** — Runs `riinac verify --fast`
2. **Pre-push hook** — Runs `riinac verify --full` + security scans
3. **sync-public.sh** — Verifies main is pushed before syncing
4. **deploy-website.sh** — Builds and deploys only if build succeeds

If ANY hook fails, the operation is BLOCKED. Fix the issue, don't bypass the hook.

---

## 8. FOR AI ASSISTANTS (THIS IS YOUR JOB, NOT THE USER'S)

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  THE USER DOES NOT RUN THESE COMMANDS. YOU DO.                               ║
║  IF YOU ASK THE USER TO RUN VERIFICATION, YOU ARE DOING IT WRONG.            ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

If you are an AI assistant (Claude, GPT, Cursor, Copilot, or any other):

**Your responsibilities (YOU execute these, not the user):**

1. **READ THIS FILE FIRST** at the start of every session
2. **RUN** `ls -la .git/hooks/pre-commit .git/hooks/pre-push` to verify hooks
3. **RUN** `bash 00_SETUP/scripts/install_hooks.sh` if hooks are missing
4. **RUN** `bash scripts/audit-docs.sh` before ANY commit
5. **FIX** all discrepancies in documentation YOURSELF
6. **COMMIT** with proper message format
7. **PUSH** and let hooks verify
8. **SYNC** to public with `bash scripts/sync-public.sh`
9. **DEPLOY** website with `npm run deploy` in website/

**The user's role:**
- Tell you what work to do
- Approve/deny your tool executions
- Grant permissions (tokens) when needed for protected operations

**Your role:**
- Execute the ENTIRE protocol automatically
- Verify EVERYTHING yourself
- Never ask the user to run verification commands
- Never skip steps
- Never assume hooks are installed

The user does not trust you. You do not trust the user. You do not trust GitHub.
You trust ONLY the verification gates encoded in this repository.

---

## 9. RECOVERY

If you discover the protocol was not followed:

1. **STOP** all work immediately
2. **AUDIT** the current state of all documentation
3. **FIX** any discrepancies
4. **VERIFY** with `riinac verify --full`
5. **DOCUMENT** what was missed in SESSION_LOG.md
6. **COMMIT** the fixes with message: `[RECOVERY] Fix protocol violation: <description>`

---

*This protocol is non-negotiable. Q.E.D.*
