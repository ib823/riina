# RIINA Proof Batch Processing Workflow

## Overview

Parallelize proof development across multiple AI systems.

```
┌─────────────────────────────────────────────────────────────────┐
│                    BATCH PROCESSING PIPELINE                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   ┌──────────┐    ┌──────────┐    ┌──────────┐                  │
│   │ Claude   │    │ DeepSeek │    │   Grok   │                  │
│   │   AI     │    │          │    │          │                  │
│   └────┬─────┘    └────┬─────┘    └────┬─────┘                  │
│        │               │               │                         │
│        ▼               ▼               ▼                         │
│   ┌─────────────────────────────────────────┐                   │
│   │         Proof Collection                 │                   │
│   └─────────────────────────────────────────┘                   │
│                        │                                         │
│                        ▼                                         │
│   ┌─────────────────────────────────────────┐                   │
│   │      Validation (coqc compile)          │                   │
│   └─────────────────────────────────────────┘                   │
│                        │                                         │
│                        ▼                                         │
│   ┌─────────────────────────────────────────┐                   │
│   │         Integration & Commit             │                   │
│   └─────────────────────────────────────────┘                   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## Phase 1: Assignment (5 minutes)

### Distribute Lemmas by AI Strength

| AI | Assigned Lemmas | Rationale |
|----|-----------------|-----------|
| **Claude AI** | P0-1, P0-2, P0-3, P1-8 | Best at complex reasoning |
| **DeepSeek** | P1-1 to P1-7 | Strong mathematical proofs |
| **Grok** | P2-1 to P2-10 | Standard lemmas |

### Copy-Paste Prompts

**For Claude AI (P0-1: val_rel_n_mono):**
```
I need you to prove this Coq lemma for step-indexed logical relations.

CONTEXT:
val_rel_n n Σ T v1 v2 is defined as:
- val_rel_n 0 = base case (True or structural)
- val_rel_n (S n) = val_rel_n n ∧ val_rel_struct

LEMMA:
Lemma val_rel_n_mono : forall m n Σ T v1 v2,
  m <= n ->
  val_rel_n n Σ T v1 v2 ->
  val_rel_n m Σ T v1 v2.

STRATEGY:
- Downward monotonicity: larger n implies smaller m
- Induction on n, generalize m
- val_rel_n (S n) contains val_rel_n n as first conjunct

Provide complete Coq proof ending with Qed.
```

**For DeepSeek (P1-4: exp_rel_le_ref):**
```
Prove this Coq lemma for expression relations with references.

LEMMA:
Lemma exp_rel_le_ref : forall n Σ T sl e1 e2 st1 st2 ctx,
  exp_rel_le n Σ T e1 e2 st1 st2 ctx ->
  store_rel_le n Σ st1 st2 ->
  exp_rel_le n Σ (TRef T sl) (ERef e1 sl) (ERef e2 sl) st1 st2 ctx.

CONTEXT:
- exp_rel_le means expressions evaluate to related values
- ERef e sl allocates a new reference
- TRef T sl is the reference type

Provide complete Coq proof ending with Qed.
```

---

## Phase 2: Collection (Parallel - run simultaneously)

### Send to Each AI

1. Open Claude AI web interface
2. Open DeepSeek web interface
3. Open Grok web interface
4. Paste assigned prompts to each
5. Wait for responses (usually 1-3 minutes each)

### Expected Output Format

Each AI should return:
```coq
Proof.
  intros ...
  [tactics]
Qed.
```

---

## Phase 3: Validation (Sequential)

### For Each Returned Proof

```bash
# 1. Create test file
cat > /tmp/test_proof.v << 'EOF'
Require Import RIINA.properties.NonInterference_v2.
(* Paste the lemma and proof here *)
EOF

# 2. Compile
cd /workspaces/proof/02_FORMAL/coq
coqc -Q . RIINA /tmp/test_proof.v

# 3. Check result
if [ $? -eq 0 ]; then
    echo "✅ PROOF VALID"
else
    echo "❌ PROOF FAILED - request revision"
fi
```

### Validation Checklist

- [ ] Compiles without errors
- [ ] Uses `Qed.` not `Admitted.`
- [ ] No new axioms introduced
- [ ] All cases handled

---

## Phase 4: Integration

### Replace Admitted Proofs

```bash
# 1. Backup original
cp properties/NonInterference_v2.v properties/NonInterference_v2.v.bak

# 2. Edit file - replace Admitted proof with validated proof
# (manual step - use editor)

# 3. Rebuild
make clean && make

# 4. Verify
grep "Admitted" properties/NonInterference_v2.v
# Should show one fewer Admitted
```

### Commit Progress

```bash
git add -A
git commit -m "[PROOF] Prove val_rel_n_mono via AI delegation"
git push origin main
```

---

## Phase 5: Iterate

### Track Progress

| Lemma | Assigned To | Status | Attempts |
|-------|-------------|--------|----------|
| val_rel_n_mono | Claude | ⏳ Pending | 0 |
| val_rel_n_step_up | Claude | ⏳ Pending | 0 |
| store_rel_n_step_up | Claude | ⏳ Pending | 0 |
| exp_rel_le_ref | DeepSeek | ⏳ Pending | 0 |
| ... | ... | ... | ... |

### If Proof Fails

1. Send error message back to AI
2. Request revision with specific error
3. Try different AI if 3 attempts fail
4. Mark as "needs manual attention" if all fail

---

## Quick Reference Commands

```bash
# Count remaining admits
grep -r "^Admitted\." --include="*.v" | wc -l

# List admitted lemmas
grep -B 5 "^Admitted\." properties/*.v | grep "Lemma\|Theorem"

# Full rebuild
cd /workspaces/proof/02_FORMAL/coq && make clean && make

# Check specific file
coqc -Q . RIINA properties/NonInterference_v2.v
```

---

## Success Metrics

| Metric | Start | Target | Current |
|--------|-------|--------|---------|
| Admits | 45 | 0 | 45 |
| P0 Complete | 0/3 | 3/3 | 0/3 |
| P1 Complete | 0/12 | 12/12 | 0/12 |
| P2 Complete | 0/30 | 30/30 | 0/30 |

---

## Estimated Timeline

| Phase | Duration | Parallelism |
|-------|----------|-------------|
| P0 (3 lemmas) | 1-2 hours | 3 AIs |
| P1 (12 lemmas) | 2-4 hours | 3 AIs |
| P2 (30 lemmas) | 4-8 hours | 3 AIs |

**Total with parallelization: 7-14 hours**
**Without parallelization: 20-40 hours**

---

*Workflow designed for maximum parallelization across AI systems*
