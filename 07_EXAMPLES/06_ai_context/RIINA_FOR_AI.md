# RIINA for AI Assistants

**Audit Update:** 2026-02-06 (Session 78: Proof Depth 20+ All Files) — 7,929 Coq Qed + 6154 Lean theorems + 6227 Isabelle lemmas = 20,310 total proofs. 0 Admitted/sorry across all provers. 1 axiom (policy). 250 active .v, 178 .lean, 175 .thy. 6149 triple-prover theorems. 845 Rust tests.

## What is RIINA?

RIINA (Rigorous Immutable Invariant — Normalized Axiom) is a formally verified programming language with:

1. **Bahasa Melayu syntax** — Native Malaysian language keywords
2. **Mathematical security guarantees** — All security properties proven in Coq
3. **Effect system** — Track all side effects at the type level
4. **Information flow control** — 6-level security lattice
5. **Capability-based security** — Fine-grained access control
6. **Taint tracking** — Track untrusted data through the system
7. **Zero-trust architecture** — Compiler, hardware, and supply chain untrusted

## File Extension

- `.rii` — RIINA source files
- `.riih` — RIINA header/interface files

## Language Design

RIINA is a typed, expression-oriented language. Every construct is an expression that returns a value. Functions are first-class. Security properties are enforced by the type system.

### Core Syntax

```riina
// Variable binding
biar nama = "Ahmad";
biar umur: Nombor = 25;

// Function declaration
fungsi tambah(x: Nombor, y: Nombor) -> Nombor {
    x + y
}

// Function with effect
fungsi cetak_mesej(mesej: Teks) -> () kesan Tulis {
    laku Tulis cetak(mesej);
}

// If-else
kalau umur >= 18 {
    "dewasa"
} lain {
    "kanak"
}

// Pattern match
padan status {
    0 => "berjaya",
    1 => "gagal",
    _ => "tidak diketahui",
}

// For loop
untuk item dalam senarai {
    proses(item);
}

// Pipe operator
data |> transform |> validate |> process
```

### Security Types

```riina
// Secret data — cannot be leaked to lower security levels
biar kata_laluan: Rahsia<Teks> = sulit "abc123";

// Declassify with proof
biar log_safe = dedah kata_laluan dengan bukti audit_proof;

// Labeled data at specific security level
biar data: Berlabel<Teks, Pengguna> = label("sensitive");

// Tainted data from untrusted source
biar input: Tercemar<Teks, UserInput> = baca_input();

// Sanitized data
biar clean: Disanitasi<Teks, HtmlEscape> = sanitize(input);

// Capability-gated operations
biar fail_cap: Keupayaan<FileRead> = perlukan FileRead;
biar data = baca_fail(fail_cap, "config.txt");
```

### Effect System

Every function declares its effects. Pure functions have no effects. The effect system tracks:

- `Bersih` (Pure) — No side effects
- `Baca` (Read) — Memory/state read
- `Tulis` (Write) — Memory/state write
- `SistemFail` (FileSystem) — File I/O
- `Rangkaian` (Network) — Network I/O
- `Kripto` (Crypto) — Cryptographic operations
- `Rawak` (Random) — Random number generation
- `Masa` (Time) — Clock/time access
- `Proses` (Process) — Process management

Effects compose: if a function calls another function with `Tulis` effect, the caller must also declare `Tulis` (or a superset).

### Security Levels

The security lattice has 6 levels (ascending):
```
Awam (Public) ⊑ Dalaman (Internal) ⊑ Sesi (Session) ⊑ Pengguna (User) ⊑ Sistem (System) ⊑ Rahsia (Secret)
```

Information can flow up (from Public to Secret) but not down. Declassification requires explicit proof.

## Standard Library Modules

| Module | BM Name | Builtins | Description |
|--------|---------|----------|-------------|
| teks | Teks | 18 | String operations |
| senarai | Senarai | 17 | List operations |
| matematik | Matematik | 10 | Math functions |
| penukaran | Penukaran | 5 | Type conversions |
| peta | Peta | 6 | Hash maps |
| set | Set | 5 | Hash sets |
| ujian | Ujian | 5 | Testing assertions |
| masa | Masa | 6 | Time operations |
| fail | Fail | 8 | File I/O |
| json | Json | 5 | JSON parsing |

## Formal Verification

RIINA's security properties are proven in Coq:
- **Type safety** (progress + preservation)
- **Non-interference** (secrets don't leak)
- **Effect soundness** (effects correctly tracked)
- **Capability safety** (capabilities cannot be forged)
- **Taint tracking correctness** (tainted data properly tracked)

The proofs are in `02_FORMAL/coq/` with 4,885 Qed proofs (active build) and 0 admits.

## Compiler

The RIINA compiler (`riinac`) supports:
- `riinac check <file.rii>` — Parse and typecheck
- `riinac run <file.rii>` — Interpret
- `riinac build <file.rii>` — Compile to native (via C)
- `riinac emit-c <file.rii>` — Emit C code
- `riinac fmt <file.rii>` — Format source
- `riinac doc <file.rii>` — Generate HTML docs
- `riinac lsp` — Start LSP server
- `riinac repl` — Interactive REPL

## When Writing RIINA Code

1. Use Bahasa Melayu keywords (fungsi, biar, kalau, etc.)
2. Annotate effects on all impure functions
3. Use `Rahsia<T>` for sensitive data
4. Use capabilities for resource access
5. Sanitize tainted data before use
6. Provide proofs for declassification
7. Keep functions pure when possible
