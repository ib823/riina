# TERAS Track Dependency Graph

```
                    ┌─────────────────────────────────────────┐
                    │           RESEARCH TRACK                │
                    │         ✅ COMPLETE (175 sessions)      │
                    └────────────────┬────────────────────────┘
                                     │
                                     │ (Research informs all tracks)
                                     │
           ┌─────────────────────────┼─────────────────────────┐
           │                         │                         │
           ▼                         ▼                         ▼
    ┌─────────────┐          ┌─────────────┐          ┌─────────────┐
    │  TRACK A    │          │  TRACK B    │          │  TRACK F    │
    │   Formal    │◄────────▶│  Prototype  │◄─────────│  Tooling    │
    │  Proofs     │  cross-  │   Impl      │          │  (Crypto)   │
    └──────┬──────┘  verify  └──────┬──────┘          └──────┬──────┘
           │                        │                        │
           │         ┌──────────────┴──────────────┐         │
           │         │                             │         │
           ▼         ▼                             ▼         │
    ┌─────────────────────┐                ┌─────────────────┘
    │      TRACK C        │                │
    │   Specifications    │◄───────────────┤
    │                     │                │
    └──────────┬──────────┘                │
               │                           │
               │       ┌───────────────────┘
               │       │
               ▼       ▼
        ┌─────────────────────┐
        │      TRACK D        │
        │  Adversarial Test   │
        │                     │
        └──────────┬──────────┘
                   │
                   ▼
        ┌─────────────────────┐
        │      TRACK E        │
        │  Hardware Design    │
        │                     │
        └─────────────────────┘
```

## Dependency Matrix

| Track | Depends On | Provides To |
|-------|------------|-------------|
| A | Research | B, C, D |
| B | Research, A, F | A, C, D |
| C | Research, A, B | D, E |
| D | All others | All others (findings) |
| E | C, F | - |
| F | Research | A, B, C, D, E |

## Critical Path

1. Research (DONE)
2. Track A + Track B + Track F (PARALLEL)
3. Track C (after A, B stable)
4. Track D (continuous, reviews all)
5. Track E (after C complete)
