# RIINA Proof Repository

Formal proofs and prototype implementation for RIINA.

```
+=============================================================================================+
|                                                                                             |
|  ██████╗ ██╗██╗███╗   ██╗ █████╗                                                           |
|  ██╔══██╗██║██║████╗  ██║██╔══██╗                                                          |
|  ██████╔╝██║██║██╔██╗ ██║███████║                                                          |
|  ██╔══██╗██║██║██║╚██╗██║██╔══██║                                                          |
|  ██║  ██║██║██║██║ ╚████║██║  ██║                                                          |
|  ╚═╝  ╚═╝╚═╝╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝                                                          |
|                                                                                             |
|  Rigorous Immutable Invariant, No Assumptions                                          |
|                                                                                             |
|  RIINA PROOF REPOSITORY                                                                     |
|                                                                                             |
|  The world's first formally verified programming language with Bahasa Melayu syntax         |
|  where security properties are mathematically guaranteed at compile time.                   |
|                                                                                             |
|  Mode: ULTRA KIASU | PARANOID | ZERO TRUST | INFINITE TIMELINE                              |
|                                                                                             |
|  "Q.E.D. Aeternum"                                                |
|                                                                                             |
+=============================================================================================+
```

## About RIINA

### Name Origin

```
RIINA = Rigorous Immutable Invariant — Normalized Axiom

R  — Rigorous (formal verification)
I  — Immutable (security guarantees)
I  — Integrity (data and code)
NA — No-attack Assured (the guarantee)
```

### What Makes RIINA Unique

- **Mathematical Guarantees** — All security properties proven in Coq
- **Bahasa Melayu Syntax** — Native Malaysian language keywords
- **Zero-Trust Architecture** — Compiler, hardware, and supply chain untrusted
- **Formal Verification** — End-to-end provable security

### File Extension

| Extension | Purpose |
|-----------|---------|
| `.rii` | RIINA source files |
| `.riih` | RIINA header/interface files |

## Repository Structure

```
proof/
├── CLAUDE.md          ← Instructions for Claude Code
├── 01_RESEARCH/       ← Research track archive (A-Z + Σ,Π,Δ,Ω,Ψ)
├── 02_FORMAL/         ← Coq/Lean/Isabelle proofs
├── 03_PROTO/          ← Rust prototype implementation
├── 04_SPECS/          ← Specifications
├── 05_TOOLING/        ← Build tools and cryptography
├── 06_COORDINATION/   ← Cross-track coordination
└── 07_EXAMPLES/       ← Example .rii files
```

## Getting Started

1. Clone the repository
2. Read `CLAUDE.md` for detailed instructions
3. Run setup scripts in `00_SETUP/scripts/`
4. Build Coq proofs: `cd 02_FORMAL/coq && make`
5. Build prototype: `cd 03_PROTO && cargo build`

## Quick Syntax Preview

```riina
// hello_dunia.rii - Hello World in RIINA

modul hello_dunia;

guna std::io;

awam fungsi utama() -> kesan Tulis {
    biar mesej = "Selamat datang ke RIINA!";
    laku Tulis cetak_baris(mesej);
    pulang ();
}

fungsi tambah(x: Nombor, y: Nombor) -> Nombor kesan Bersih {
    pulang x + y;
}
```

See `07_EXAMPLES/` for more comprehensive examples.

## Research Tracks

### Core Tracks (A-F)
- **Track A (Formal):** Coq proofs for type safety and non-interference
- **Track B (Prototype):** Rust implementation of compiler
- **Track C (Specs):** Language specifications
- **Track D (Testing):** Test infrastructure
- **Track E (Hardware):** Hardware verification
- **Track F (Tooling):** Build tools and cryptography

### Extended Tracks (R-Z)
- **Track R:** Translation Validation (Certified Compilation)
- **Track S:** Hardware Contracts (HW/SW Co-Verification)
- **Track T:** Hermetic Build (Binary Bootstrap)
- **Track U:** Runtime Guardian (Verified Micro-Hypervisor)
- **Track V:** Termination Guarantees
- **Track W:** Verified Memory
- **Track X:** Concurrency Model
- **Track Y:** Verified Stdlib
- **Track Z:** Declassification Policy

### Application Tracks (Σ,Π,Δ,Ω,Ψ)
- **Track Σ (Sigma):** Verified Persistent Storage (TigerBeetle-style)
- **Track Π (Pi):** Verified Performance (SIMD, lock-free)
- **Track Δ (Delta):** Verified Distribution (Raft/Paxos, BFT)
- **Track Ω (Omega):** Network Defense (DDoS mitigation)
- **Track Ψ (Psi):** Operational Security (insider threats, duress)

## Status

| Track | Status | Description |
|-------|--------|-------------|
| Research | Complete | 175+ sessions, 31 domains |
| Track A (Formal) | In Progress | Type safety proofs ongoing |
| Track B (Prototype) | In Progress | Lexer/parser/typechecker |
| Track C (Specs) | In Progress | Specs populated, integration pending |
| Track F (Tooling) | Partial | Build system complete |

## Bahasa Melayu Keywords (Sample)

| Bahasa Melayu | English | Usage |
|---------------|---------|-------|
| `fungsi` | fn | Function declaration |
| `biar` | let | Variable binding |
| `kalau` | if | Conditional |
| `pulang` | return | Return value |
| `rahsia` | secret | Secret type |
| `dedah` | declassify | Declassify |
| `kesan` | effect | Effect annotation |
| `masa_tetap` | ct | Constant-time block |

Full specification: `01_RESEARCH/specs/bahasa/RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md`

## License

MIT OR Apache-2.0

---

*RIINA: Rigorous Immutable Invariant — Normalized Axiom*

*"QED Eternum."*
