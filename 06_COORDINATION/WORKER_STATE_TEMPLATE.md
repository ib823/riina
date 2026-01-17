# Worker State Template

## Worker ID: [α|β|γ|δ|ε|ζ]
## Domain: [Proofs|Compiler|Crypto|TransVal|Completeness|Coordination]

---

## LAST CHECKPOINT

| Field | Value |
|-------|-------|
| Timestamp | YYYY-MM-DDTHH:MM:SSZ |
| Commit Hash | xxxxxxx |
| Status | [ACTIVE|PAUSED|BLOCKED|COMPLETE] |

---

## CURRENT TASK

### Primary Task
- **File:** path/to/file
- **Line:** NNN
- **Function/Lemma:** name_of_item
- **Description:** What you're working on
- **Progress:** XX%

### Context
- Previous completed: item_name
- Currently doing: specific_action
- Next planned: next_item

### Code Snippet (if applicable)
```coq
(* or rust, etc. *)
Current code context here
```

---

## TASK QUEUE

| Priority | Task | Status | Notes |
|----------|------|--------|-------|
| 1 | Primary task | IN_PROGRESS | Current focus |
| 2 | Secondary task | PENDING | After primary |
| 3 | Tertiary task | PENDING | If time permits |

---

## BLOCKERS

| Blocker | Severity | Waiting On | ETA |
|---------|----------|------------|-----|
| (none or describe) | [P0|P1|P2] | Worker X / External | Date |

---

## HEARTBEAT LOG

| Timestamp | Status | File | Line | Progress |
|-----------|--------|------|------|----------|
| HH:MM:SS | ACTIVE | file.v | 123 | 10% |
| HH:MM:SS | ACTIVE | file.v | 145 | 25% |
| ... | ... | ... | ... | ... |

---

## SESSION NOTES

### Key Decisions
1. Decision made and rationale

### Discoveries
1. Important finding

### Technical Notes
1. Implementation detail

---

## RECOVERY INSTRUCTIONS

If resuming this worker's task:

1. `git pull origin main`
2. Navigate to: `path/to/file:line`
3. Read context above
4. Continue from: specific_point
5. Update this file immediately

---

*Last updated: TIMESTAMP*
