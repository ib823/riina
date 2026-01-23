# DELEGATION PROMPT: WP-009 TIMING/TEMPORAL SECURITY COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: WP-009-TIMING-SECURITY-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `TimingSecurity.v` with 15 theorems (TIME-001 through TIME-015)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

Create Coq proofs for each timing/temporal attack:

TIME-001: Race Condition → Session types, verified locking
TIME-002: TOCTOU → Atomic operations
TIME-003: Timing Side Channel → Constant-time operations
TIME-004: Covert Timing Channel → Timing isolation
TIME-005: NTP Attack → Authenticated NTP (NTS)
TIME-006: Replay Attack → Nonces + timestamps + window
TIME-007: Ordering Attack → Sequence numbers
TIME-008: Deadline Attack → Real-time scheduling guarantees
TIME-009: Timestamp Manipulation → Signed timestamps
TIME-010: Timeout Attack → Proper timeout handling
TIME-011: Clock Skew Attack → Clock synchronization
TIME-012: Scheduling Attack → Priority inheritance
TIME-013: Deadlock → Deadlock-free types (ordering)
TIME-014: Livelock → Liveness proofs
TIME-015: Starvation → Fair scheduling

Models needed:
- Lock ordering for deadlock prevention
- Session types for race conditions
- Constant-time operation markers
- Real-time scheduling model

NAMES: `time_001_*` through `time_015_*`. ZERO Admitted. OUTPUT ONLY COQ FILE.
```
