# RIINA for AI Assistants

**Verification:** 12,678 Coq Qed (compiled, 0 Admitted, 0 active axioms) — Coq is the only mechanized lane | 3365 Rust tests | the other prover trees are machine-generated (claim-level tracked, not independent verification)

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

## Modules — multi-file programs

`guna <name>;` imports the sibling file `<name>.rii`. Multi-file programs
check, run, and compile natively (and to wasm32 if they stay inside the small
WASM builtin surface — see the Backend table below).

```riina
// kira.rii
awam fungsi tambah(x: Nombor, y: Nombor) -> Nombor kesan Bersih { x + y }
fungsi pembantu_persendirian(x: Nombor) -> Nombor kesan Bersih { x * 2 }  // no `awam` = private
```

```riina
// main.rii
guna kira;
fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks(kira::tambah(3, 4)));   // qualified call
    0
}
```

Rules, each enforced with a real error (not a silent fallback):

| Rule | Behaviour |
|---|---|
| Visibility | Only `awam` names cross a module boundary. Referencing a private one errors and tells you to add `awam`. |
| Direct imports | You may only name modules you `guna` yourself; a transitively-loaded module is not silently in scope. |
| Cycles | `a` → `b` → `a` reports the chain, it does not hang or overflow. |
| Collisions | Two modules producing the same linked name is an error, never silent shadowing. |
| Module bodies | Only the root file may have top-level code; an imported module must be declarations only. |

**`guna std::teks;` is different** — a *multi-segment* path names the builtin
namespace, not a file. It is not an import and needs no `std/` directory. Use
single-segment `guna kira;` for your own files.

Not yet available: there is no `.rii` standard library to import, and modules
resolve only within the importing file's directory (no search path or package
dependencies yet — master plan REQ-71 remainder, REQ-72).

## Standard Library Modules

**Counts and the Backend column below are command-derived (2026-08-15) from the
builtin tables in `03_PROTO/crates/riina-codegen/src/builtins/` cross-referenced
against the generated `docs/api/STDLIB.md`, whose Backend column comes from the
compiled-backend boundary `riina_codegen::codegen_supports_builtin` itself.** The
authoritative per-builtin list is that generated file (373 registered builtins,
each with its own Backend marker).

| Module | BM Name | Builtins | Backend | Description |
|--------|---------|----------|---------|-------------|
| teks | Teks | 16 | native-only | String operations |
| senarai | Senarai | 18 | native-only | List operations |
| peta | Peta | 8 | native-only | Hash maps |
| set | Set | 7 | native-only | Hash sets |
| matematik | Matematik | 10 | 7 of 10 native-only | Math functions (`baki`, `log2`, `rawak` are interpreter-only) |
| ujian | Ujian | 6 | 5 of 6 native-only | Test assertions (`jangkakan` is interpreter-only) |
| masa | Masa | 7 | native-only | Time operations |
| simpan | Simpan | 8 | native-only | Durable key-value store (log-structured journal, fsync per record) |
| json | Json | 5 | native-only | JSON parsing |
| net | Jaring | 17 | 9 of 17 native-only | TCP sockets (real I/O, verified RFC 793 state machine). The 8 `jaring_tls_*` builtins are **interpreter-only**: the C backend has no `riina-tls`, and a weaker handshake that still compiled would be worse than a build error |
| http | Http | 6 | native-only | **Real** HTTP/1.1 (`http_hurai_*`, `http_balas`, `http_minta`) over the verified TCP machine |
| fail | Fail | 8 | **none** | File I/O |
| vfs | Vfs | 5 | **none** | Virtual filesystem (verified access-control model) |
| keselamatan | Keselamatan | 42 | **none** | Taint sanitizers + **modelled** sinks (`sanitasi_*`, `sql_*`, `http_dapat`/`http_hantar`, `csrf_*`) — type discipline only, no socket/database/SMTP |

Conversions (`ke_teks`, `ke_nombor`, …), printing (`cetak`, `cetakln`), and the
numeric-tower constructors (`besar`, `perpuluhan`, `wang`, `titik_tetap`, `qmn`)
are registered directly rather than in a module table. Printing, `ke_teks`,
`gabung_teks` and the numeric-tower constructors are the **only** builtins the
WASM backend implements; everything else marked `native-only` compiles to C but
is REFUSED for wasm32 (it used to be silently miscompiled — master plan
REQ-78).

### Real HTTP vs modelled HTTP — do not confuse them

Two different `http_*` families exist, deliberately:

| Family | Behaviour |
|---|---|
| `http_hurai_kaedah/laluan/jasad/kepala`, `http_balas`, `http_minta` | **REAL.** RFC 9112 codec; `http_minta` opens a real socket over the verified TCP machine. Use these to serve or call HTTP. |
| `http_dapat`/`http_get`, `http_hantar`/`http_post`, `sql_laksana`, `emel_hantar`, `shell_laksana` | **MODELLED.** Return canned values, open no socket, contact no database or SMTP. They exist to carry the taint→sink *type* discipline. |

Writing a server: read the request with `jaring_terima`, parse it with
`http_hurai_*`, build the reply with `http_balas` (which computes
`Content-Length` itself, so a response cannot be split). Malformed or smuggled
requests — `Content-Length` plus `Transfer-Encoding`, `Foo : bar`, conflicting
duplicate lengths — are **errors**, not repaired messages.

`https://` is refused, not silently downgraded: there is no TLS record layer yet.

### ⚠ Type-checking does not imply compiling

**Of 373 builtins: 20 compile to C *and* WASM, 198 are native-only (the WASM
backend refuses them), and 155 are interpreter-only.** A
program using any interpreter-only builtin type-checks and runs, but cannot be
built for native or WASM — lowering fails closed rather than miscompiling:

```bash
riinac check baca.rii   # Success!  Effect: FileSystem
riinac run   baca.rii   # works — reads the file
riinac build baca.rii   # Codegen Error: unbound variable: fail_baca
```

A **networked, persistent service now compiles**: `jaring_*` (except the TLS
half), `http_*`, `simpan_*`, `masa_*` and `json_*` are all routed, so
`07_EXAMPLES/11_servis/pelayan.rii` builds natively and keeps its counter across
restarts. The families still interpreter-only are `fail_*`, `vfs_*`,
`keselamatan` and `jaring_tls_*`.

If you are generating RIINA code that must be **compiled for WASM**, restrict
yourself to printing, `gabung_teks`, `ke_teks` and the numeric-tower
constructors — that is the entire WASM surface. For **native**, the `all
compiled` modules above plus conversions and math are available. Anything touching the network (including the real HTTP layer),
filesystem, JSON, time, or the security sinks is `riinac run` only. Closing this gap is master plan **REQ-70** (Gate C).

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
- `riinac check <file.rii>` — Parse and typecheck (accepts all 329 builtins)
- `riinac run <file.rii>` — Interpret (runs all 329 builtins)
- `riinac build <file.rii>` — Compile to native via C (**only the 148 compiled
  builtins**; fails closed on the rest — see the warning above)
- `riinac emit-c <file.rii>` — Emit C code (same 148-builtin limit)
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
