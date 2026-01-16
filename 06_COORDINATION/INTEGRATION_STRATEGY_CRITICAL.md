# Critical Integration Strategy

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  INTEGRATION STRATEGY: REVOLUTIONARY IMPROVEMENTS + ONGOING PROOF WORK           ║
║  Date: 2026-01-16                                                                ║
║  Status: CRITICAL COORDINATION DOCUMENT                                          ║
║                                                                                  ║
║  Situation: Another Claude instance is working on eliminating 21 admits          ║
║  in NonInterference.v using DIRECT proof approach.                               ║
║                                                                                  ║
║  Our documents propose RESTRUCTURING approach (Kripke worlds).                   ║
║  Both approaches target the same goal. This document coordinates them.           ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

## 1. Current State Analysis

### 1.1 The Other Instance's Approach

The other Claude is attempting to prove:
1. `exp_rel_n_mono` - Step index monotonicity for expressions
2. `step_index_app` - Step index for function application
3. `step_index_fst/snd` - Step index for projections
4. `step_index_case_inl/inr` - Step index for sum elimination
5. `canonical_bool/prod/sum/fn/ref/labeled` - Canonical forms
6. `val_rel_n_zero` - Base case validity

**Their strategy:** Prove helper lemmas, then use them to complete the 21 remaining admits.

### 1.2 Our Proposed Approach

We proposed restructuring to Kripke worlds:

```coq
Record World := mkWorld { w_n : nat; w_Σ : store_ty }.
Definition world_future (w w' : World) : Prop := ...
```

**Our strategy:** Restructure definitions so axioms become trivially provable.

### 1.3 Compatibility Analysis

| Aspect | Direct Proof | Kripke Restructure |
|--------|--------------|-------------------|
| Files Modified | NonInterference.v only | Multiple new files |
| Risk | May hit unprovable cases | Larger refactor |
| Reward | Minimal disruption | Cleaner foundation |
| Time | Unknown (depends on proof difficulty) | ~80-100 units |

---

## 2. Integration Decision Matrix

### 2.1 Scenario A: Direct Proof Succeeds

**If the other instance successfully eliminates all 21 admits:**

| Our Improvement | Action | Rationale |
|-----------------|--------|-----------|
| P0-* (Foundation) | PROCEED | Independent, adds value |
| P1-001 (Kripke) | ARCHIVE | No longer needed |
| P1-002 (Fundamental theorem) | ARCHIVE | Completed by other |
| P1-003-005 | SELECTIVE | Some may still help |
| P2-* (Performance) | PROCEED | Independent |
| P3-* (Crypto) | PROCEED | Independent |

**Integration steps:**
1. Verify their proofs compile: `cd 02_FORMAL/coq && make`
2. Verify zero admits: `grep -r "Admitted" *.v`
3. Archive our P1-001/P1-002 specs to `01_RESEARCH/archive/`
4. Proceed with P0, P2, P3 implementations

### 2.2 Scenario B: Direct Proof Partially Succeeds

**If they reduce admits but cannot eliminate all:**

| Remaining Admits | Our Action |
|------------------|------------|
| 1-5 | Help with remaining cases |
| 6-10 | Evaluate: direct help vs restructure |
| 11+ | Recommend Kripke restructure |

**Integration steps:**
1. Wait for their progress report
2. Analyze which admits remain
3. If < 6 remain: provide targeted help
4. If >= 6 remain: propose hybrid approach

### 2.3 Scenario C: Direct Proof Blocked

**If they hit fundamental unprovability:**

The key issue is likely **contravariance in function types**. The axiom:

```coq
Axiom val_rel_n_weaken : forall n Σ Σ' T v1 v2,
  store_ty_extends Σ Σ' ->
  val_rel_n n Σ' T v1 v2 ->
  val_rel_n n Σ T v1 v2.
```

For `T = TFn T1 T2 eff`, this requires:

```
(∀ arg. val_rel_n n' Σ' T1 arg → result related at Σ'')
→
(∀ arg. val_rel_n n' Σ T1 arg → result related at Σ'')
```

This is **CONTRAVARIANT** in Σ for the argument type! If `Σ ⊆ Σ'`, then
`val_rel_n n' Σ' T1` is MORE restrictive than `val_rel_n n' Σ T1`.
So the implication goes the WRONG way.

**This is why we proposed Kripke worlds:** Universal quantification over
future worlds in the TFn case makes weakening trivial.

**Integration steps:**
1. Implement Kripke restructure (our P1-001)
2. Port any completed lemmas from their work
3. Complete remaining cases in new structure

---

## 3. Immediate Safe Actions

### 3.1 Actions That Cannot Conflict

Regardless of which scenario occurs, these are SAFE to start now:

| Priority | Improvement | Location | Why Safe |
|----------|-------------|----------|----------|
| 1 | P0-002 | `03_PROTO/crates/riina-symbols/` | NEW crate |
| 2 | P0-003 | `03_PROTO/crates/riina-arena/` | NEW crate |
| 3 | P0-005 | `03_PROTO/crates/riina-span/` | NEW crate |
| 4 | P3-001 | `05_TOOLING/.../aes_ni.rs` | NEW file |
| 5 | P3-002 | `05_TOOLING/.../aes_bitsliced.rs` | NEW file |
| 6 | P2-001 | `03_PROTO/.../fast_lexer.rs` | NEW file |

### 3.2 Actions To Wait On

| Improvement | Wait For | Reason |
|-------------|----------|--------|
| P1-001 | Other instance completes | May not be needed |
| P1-002 | Other instance completes | They're doing it |
| P1-003 | Other instance completes | Affects same file |
| P1-004 | Other instance completes | Depends on NonInterference.v |
| P1-005 | Other instance completes | Affects effect proofs |

---

## 4. Timeline Recommendations

### 4.1 Immediate (Now - Wait Period)

1. **DO:** Start P0-002, P0-003, P0-005 (foundation crates)
2. **DO:** Start P3-001, P3-002 (crypto new files)
3. **DO:** Start P2-001 (fast lexer new file)
4. **DO NOT:** Touch any files in `02_FORMAL/coq/`

### 4.2 After Other Instance Completes

**Check their results:**
```bash
cd /workspaces/proof/02_FORMAL/coq
make clean && make
grep -rn "Admitted" *.v */*.v | wc -l
```

**If admits = 0:**
- Celebrate - proofs complete!
- Archive our P1-001/P1-002 specs
- Continue with P0, P2, P3

**If admits > 0:**
- Analyze remaining admits
- Decide: targeted help vs restructure
- Coordinate next steps

### 4.3 Long-term

After proof completion (by either method):
1. Complete P2-* performance improvements
2. Complete P3-* crypto hardening
3. Start P4-* verified compilation
4. Start P5-* zero-trust bootstrap

---

## 5. Document Preservation

### 5.1 Documents Already Created

| Document | Location | Status |
|----------|----------|--------|
| Master Roadmap | `01_RESEARCH/IMPROVEMENT_ROADMAP_REVOLUTIONARY.md` | KEEP |
| Proof Spec | `01_RESEARCH/specs/SPEC_PROOF_COMPLETION_TRACK_A.md` | KEEP (may become archive) |
| Performance Spec | `01_RESEARCH/specs/SPEC_PERFORMANCE_OPTIMIZATION.md` | KEEP |
| Coordination Protocol | `06_COORDINATION/IMPROVEMENT_COORDINATION_PROTOCOL.md` | KEEP |
| Lock File | `06_COORDINATION/.locks` | KEEP |
| Safe Actions | `06_COORDINATION/IMMEDIATE_SAFE_ACTIONS.md` | KEEP |
| This Document | `06_COORDINATION/INTEGRATION_STRATEGY_CRITICAL.md` | KEEP |

### 5.2 Adding to 01_RESEARCH

Our documents are already properly placed:
- `01_RESEARCH/IMPROVEMENT_ROADMAP_REVOLUTIONARY.md` - Main roadmap
- `01_RESEARCH/specs/SPEC_*.md` - Technical specifications

These follow the existing 01_RESEARCH pattern and will be preserved.

---

## 6. Communication Protocol

### 6.1 When Other Instance Completes

1. Read their final commit message
2. Check SESSION_LOG.md for their notes
3. Run verification: `grep -rn "Admitted" 02_FORMAL/coq/*.v`
4. Update this document with outcome

### 6.2 If Help Is Needed

If the other instance gets stuck and needs the Kripke approach:

1. Create branch: `git checkout -b feature/kripke-worlds`
2. Implement P1-001 KripkeWorlds.v
3. Show how axioms become provable
4. Merge after verification

---

## 7. Risk Assessment

### 7.1 Risk: Other Instance Breaks Proofs

**Mitigation:**
- All changes tracked in git
- Can revert to known-good state
- Our specs provide alternative approach

### 7.2 Risk: Conflicting Changes

**Mitigation:**
- Lock file mechanism in place
- Clear safe zones defined
- We only touch NEW files

### 7.3 Risk: Approaches Incompatible

**Mitigation:**
- Both approaches are semantically equivalent
- Kripke restructure is more elegant but not required
- Direct proofs are valid if they work

---

## 8. Decision: When to Materialize

### 8.1 Phase 0 Improvements: MATERIALIZE NOW

These create NEW infrastructure with ZERO risk:

```bash
# Safe to execute immediately
cd /workspaces/proof/03_PROTO
mkdir -p crates/riina-symbols/src
mkdir -p crates/riina-arena/src
mkdir -p crates/riina-span/src
```

### 8.2 Phase 1 Improvements: WAIT

Wait for other instance to complete, then:
- If success: Archive our P1 specs
- If blocked: Implement Kripke restructure

### 8.3 Phase 2 Improvements: START NEW FILES NOW

Create new files alongside existing:
- `fast_lexer.rs` (NEW)
- `simd.rs` (NEW)
- `ast_arena.rs` (NEW)

Do NOT modify `lexer.rs`, `parser.rs` until P0 complete.

### 8.4 Phase 3 Improvements: START NOW

Crypto improvements are completely independent:
- `aes_ni.rs` (NEW)
- `aes_bitsliced.rs` (NEW)

Do NOT modify `ml_kem.rs`, `ml_dsa.rs` until other instance done.

---

## 9. Summary: Action Items

### IMMEDIATE (No Coordination Needed)

1. ✅ Create `riina-symbols` crate
2. ✅ Create `riina-arena` crate
3. ✅ Create `riina-span` crate
4. ✅ Create `aes_ni.rs`
5. ✅ Create `aes_bitsliced.rs`
6. ✅ Create `fast_lexer.rs`

### WAIT (Coordination Required)

1. ⏳ Any modification to `02_FORMAL/coq/*.v`
2. ⏳ Any modification to existing `03_PROTO/crates/*/src/lib.rs`
3. ⏳ Any modification to `05_TOOLING/crates/*/src/crypto/*.rs`

### AFTER OTHER INSTANCE COMPLETES

1. 📋 Evaluate admit count
2. 📋 Decide on P1 approach
3. 📋 Update this document
4. 📋 Proceed with remaining phases

---

*Status: ACTIVE COORDINATION*
*Last Updated: 2026-01-16*
*Next Review: After other instance completes NonInterference work*
