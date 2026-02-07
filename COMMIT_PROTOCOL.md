# RIINA COMMIT & DEPLOY PROTOCOL

**This is law. No exceptions. No shortcuts. No "it's a small change."**

There are exactly TWO instructions a human gives: **"commit"** and **"deploy"**.
Each has a fixed sequence of steps. Every step must pass before the next runs.
If any step fails, STOP. Fix it. Restart from step 1.

---

## INSTRUCTION: "COMMIT"

**What it means:** Save this work to main. Verify it. Nothing goes to production.

```
Step 1.  git status                          — See what changed
Step 2.  bash scripts/audit-docs.sh          — Docs match reality?
Step 3.  git add <specific files>            — Stage only what you changed
Step 4.  git commit -m "[SCOPE] message"     — Pre-commit hook runs automatically:
                                                 - audit-docs.sh
                                                 - riinac verify --fast (856+ tests, clippy)
Step 5.  git push origin main                — Pre-push hook runs automatically:
                                                 - riinac verify --full (10-prover scan)
                                                 - Commit signature verification
                                                 - Secret scan
                                                 - Trojan source scan
```

**That's it. 5 steps. "Commit" does NOT touch public, riina, or gh-pages.**

---

## INSTRUCTION: "DEPLOY"

**What it means:** Put the current main onto the live website. Full pipeline.

**"Deploy" INCLUDES "commit" first if there are uncommitted changes.**

```
Step 1.  git status                          — Clean? If not, run COMMIT first.
Step 2.  bash scripts/audit-docs.sh          — Docs match reality?
Step 3.  bash scripts/sync-public.sh         — Cherry-pick main → public,
                                                strip internal files,
                                                push public to origin AND ib823/riina
Step 4.  bash scripts/deploy-website.sh      — Build website (npm run build),
                                                push dist/ to gh-pages on ib823/riina
Step 5.  Hard refresh https://ib823.github.io/riina/ and VISUALLY VERIFY
```

**That's it. 5 steps. The website is live after step 4. Step 5 confirms it.**

---

## WHAT THE SCRIPTS DO (so you know what's happening)

### `audit-docs.sh`
Reads metrics.json (the single source of truth) and checks that every markdown doc quotes the right numbers. Fails if anything is stale.

### Pre-commit hook (automatic on `git commit`)
1. Runs `audit-docs.sh`
2. Runs `riinac verify --fast` — compiles Rust, runs all tests, runs clippy

### Pre-push hook (automatic on `git push`)
1. Runs `riinac verify --full` — everything from --fast PLUS scans all 10 prover file sets
2. Verifies commit signatures (SSH signing)
3. Scans for accidentally committed secrets
4. Scans for trojan source attacks (Unicode tricks)

### `sync-public.sh`
1. Verifies you're on main and it's pushed
2. Switches to public branch
3. Cherry-picks the latest main commit
4. Deletes internal files (CLAUDE.md, 01_RESEARCH/, 06_COORDINATION/, etc.)
5. Pushes public to both origin and ib823/riina
6. Switches back to main

### `deploy-website.sh`
1. Builds WASM binary
2. Regenerates metrics.json from live codebase
3. Runs `npm run build` (Vite production build)
4. Copies install.sh into dist/
5. Creates temp git repo in dist/, force-pushes to gh-pages on ib823/riina
6. GitHub Pages serves gh-pages → https://ib823.github.io/riina/

---

## THE RULES

1. **"Commit" never touches production.** It only saves to main.
2. **"Deploy" always includes sync + website build.** No partial deploys.
3. **If any step fails, STOP.** Fix it. Restart from step 1.
4. **No skipping steps.** Not even for a typo fix.
5. **No manual pushes to public.** Only sync-public.sh touches public.
6. **No manual pushes to gh-pages.** Only deploy-website.sh touches gh-pages.
7. **Visual verification is mandatory after deploy.** Open the URL. Look at it. Confirm it's right.
8. **The website reads metrics.json at runtime.** Zero hardcoded numbers in JSX. If you see a number that should come from metrics and it's hardcoded, that's a bug.

---

## QUICK REFERENCE

| Human says | You do |
|------------|--------|
| "commit" | Steps 1-5 of COMMIT |
| "deploy" | COMMIT (if needed) + Steps 1-5 of DEPLOY |
| "deploy to prod" | Same as "deploy" |
| "push to public" | Same as "deploy" |
| "push to riina" | Same as "deploy" |

---

*This protocol is non-negotiable. Q.E.D.*
