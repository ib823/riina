# RIINA A-to-Z Execution Board

Date: 2026-02-10
Status: AUTHORITATIVE
Scope: strict execution tracker from current mechanized Coq core to full multi-lane defensible verification and independent audit readiness.

## Live Baseline (must match L0 sources)

- Active Coq build: `7740 Qed`, `0 Admitted`, `0 active axioms`, `0 active assumptions`
- Claim levels: `overall=mechanized`, `coq=mechanized`, `lean/isabelle/tlaplus/alloy=compiled`, `fstar/smt/verus/kani/tv=generated`
- Independent external audit: `false`
- Easier-gap checks (items 1/2/9/12): `PASS`
- Medium-gap checks (items 1/2/3/4/9/12): `PASS`
- Heavy-gap foundation checks (items 5/6/7/8/10/11/13): `PASS`
- Heavy-gap executable closure tracker (items 5/6/7/8/10/11/13): `started` (see `reports/heavy_closure_status.json`)
- Heavy-gap closure-ready snapshot: `D5=ready`, `D6=ready`, `D7=ready`, `D11=ready`, `D8/D10/D13=pending`
- Dim1/Dim9 promotion-readiness check: `dimension_1=PASS`, `dimension_9=PASS`, `promotion_ready=true`
- Public quality gates: `PASS`

Sources:
- `PROOF_STATUS.md`
- `website/public/metrics.json`
- `reports/easier_gap_status.json`
- `reports/medium_gap_status.json`
- `reports/heavy_gap_status.json`
- `reports/heavy_closure_status.json`
- `reports/dim1_dim9_promotion_status.json`
- `reports/public_quality_status.json`

## Claim-Level Rules (non-negotiable)

1. Public messaging cannot exceed `website/public/metrics.json` claim levels.
2. A lane cannot be called compiled/mechanized unless its toolchain check is real and passing.
3. "Independently verified/audited" is forbidden until external signed audit artifacts exist.
4. Deploy claims are blocked if quality gates fail.

## 13-Dimension Board

| Dim | Dimension | Completion | Current Status | Key Pending Activities | Exit Criteria |
|-----|-----------|------------|----------------|------------------------|---------------|
| 1 | Type system soundness | 82% | Coq mechanized, Lean/Isabelle core compilation passing | publish parity check reports; enforce parity drift gate beyond core files; extend cross-lane obligations beyond type-safety core | Coq+Lean+Isabelle core theorems compiled and parity report published |
| 2 | Non-interference | 65% | Active Coq path strong, cross-lane generated | complete NI obligations for effects/linearity/session interactions; compile cross-lane NI core; add compile-path preservation evidence | NI core compiled in at least 2 independent lanes and preservation checks published |
| 3 | Effect soundness | 60% | Coq theorems present, implementation binding partial | close remaining composition obligations; bind proofs to compiler effect checker invariants; add regression obligations for unauthorized effects | proof-to-implementation effect invariants enforced in verification gate |
| 4 | Linear type soundness | 55% | Coq domain proofs present, not implementation-closed | close linearity obligations against implementation semantics; bind to runtime/resource model; add rejection regressions | no linearity gap between spec and compiler/runtime checks |
| 5 | Constant-time enforcement | 35% | Model-level theorems present, backend preservation open | mechanize full theorem chain; add backend timing-preservation checks; publish executable side-channel harness results | constant-time property proved and checked post-compilation on supported targets |
| 6 | Zeroization completeness | 30% | model proofs present, binary preservation open | formalize erase semantics end-to-end; prove no optimizer removal; add binary-level zeroization checks | verified erase behavior survives compilation and runtime execution |
| 7 | Compiler correctness (source->target) | 15% | translation-validation lane generated | define source/IR/target correspondence; implement per-target validation artifacts; publish per-target reports | native/WASM/eBPF/SGX scope has concrete correctness evidence in repository |
| 8 | Crypto primitive correctness | 10% | F* lane generated | replace generated corpus with real F* proofs; extract/integrate verified primitives; publish equivalence/perf/security evidence | cryptographic primitives have real verified corpus and integration proof evidence |
| 9 | Protocol correctness | 58% | foundation and executable TLA+/Alloy checks passing; full closure open | prove session-type linkage in Coq to runtime enforcement; publish full model-check artifact pack; add protocol-runtime conformance gate | protocol properties checked + linked to language/runtime enforcement |
| 10 | Implementation correctness | 10% | Verus/Kani lanes generated | verify critical compiler modules in Verus; add Kani bounded checks for edge paths; bind implementation to formal spec clauses | implementation-correctness obligations executable and passing on production code |
| 11 | Protocol <-> implementation binding | 10% | open | define protocol trace schema; add conformance checker; gate deploy on zero conformance violations | protocol model and runtime traces are checked and policy-enforced |
| 12 | Compilation-chain integrity | 45% | foundation present (easier-gap pass), deploy protocol hardened, operationalization open | implement DDC in deploy protocol (non-CI path); produce reproducible build attestations and signed hashes; maintain transparency log | trusting-trust controls are executable and auditable per release |
| 13 | Hardware model assumptions | 25% | foundation models present, trust-boundary closure open | publish architecture trust boundary model; add litmus tests for memory/timing assumptions; fail-closed policy for unsupported behavior | hardware assumptions are explicit, tested, and release-gated |

## Strict A-to-Z Execution Sequence

| Step | Workstream | Deliverable |
|------|------------|-------------|
| A | Authority lock | `04_SPECS/DOCUMENT_AUTHORITY_MATRIX.md` adopted and linked |
| B | Baseline freeze | L0 metrics snapshot refreshed and checked |
| C | Claim hygiene | website/docs claims reconciled to claim levels |
| D | Deploy gates | deploy protocol blocks over-claim and drift |
| E | Dimension 1 closure set | type-safety cross-lane compile/parity pack |
| F | Dimension 2 closure set | NI cross-lane core + preservation pack |
| G | Dimension 3 closure set | effect soundness spec->compiler binding pack |
| H | Dimension 4 closure set | linearity soundness + runtime binding pack |
| I | Dimension 5 closure set | constant-time theorem+backend evidence pack |
| J | Dimension 6 closure set | zeroization preservation evidence pack |
| K | Dimension 7 closure set | compiler-correctness target reports pack |
| L | Dimension 8 closure set | verified crypto corpus + integration pack |
| M | Dimension 9 closure set | protocol model-check + Coq linkage pack |
| N | Dimension 10 closure set | Verus/Kani implementation proof pack |
| O | Dimension 11 closure set | protocol-runtime conformance pack |
| P | Dimension 12 closure set | DDC + reproducible-build attestation pack |
| Q | Dimension 13 closure set | hardware model + litmus evidence pack |
| R | Cross-lane promotion | lane statuses moved from generated->compiled/mechanized with evidence |
| S | Regression hardening | negative tests and drift detectors integrated |
| T | Traceability sync | threat->proof->impl matrix updated from live artifacts |
| U | User-facing docs sync | README/docs/website aligned to latest verified state |
| V | Version readiness | changelog/version/tag alignment checks pass |
| W | Release candidate build | full verify + quality gates pass on release commit |
| X | External audit prep | reproducibility scripts, hashes, claim matrix packaged |
| Y | Independent audit execution | third-party signed findings captured |
| Z | Public claim elevation | only then allow "independently audited" messaging |

## Operational Cadence

1. Before every claim update: run full verify + public quality gates.
2. Before every deploy: follow `COMMIT_PROTOCOL.md` without skipping steps.
3. Weekly: refresh this board's completion values from L0 outputs only.
4. Monthly: publish a delta report listing completed exits and newly opened risks.
