# 12_kelayakan — credential policy audit + constant-time verification

A small three-file program that exercises the parts of RIINA that are actually
load-bearing: real loops, mutable locals that stay pure, module boundaries, and
the classify/declassify boundary. It runs on the interpreter and compiles to a
native binary, and the two produce byte-identical output.

```bash
riinac run   07_EXAMPLES/12_kelayakan/utama.rii    # interpreted
riinac build 07_EXAMPLES/12_kelayakan/utama.rii    # native binary via C
./07_EXAMPLES/12_kelayakan/utama
```

```
Audit dasar kata laluan
----------------------------------------------
kata laluan        skor  gred
----------------------------------------------
admin                0  ditolak  [kelas 1, ulangan 1]
aaaaaaaa             0  ditolak  [kelas 1, ulangan 8]
Ahmad2026           61  sederhana  [kelas 3, ulangan 1]
Sungai#Kelantan7    98  kukuh  [kelas 4, ulangan 1]
x                   12  ditolak  [kelas 1, ulangan 1]
----------------------------------------------
purata skor  : 34 (5 calon)
calon terbaik: Sungai#Kelantan7 (98)

Pengesahan rahsia (masa tetap)
----------------------------------------------
LULUS: banding masa-tetap membezakan akhiran
LULUS: rahsia yang betul disahkan
```

## The files

| File | Effect | What it does |
|---|---|---|
| `peraturan.rii` | `Bersih` | Character classes, longest repeated run, banned-list check, policy score |
| `pengesah.rii` | `Bersih` | Constant-time string comparison, and the one `dedah` in the program |
| `utama.rii` | `Tulis` | The report — the only file that touches a terminal |

Two thirds of the program is `kesan Bersih`, mutable accumulators and all. That
is the point of the `biar ubah` slot: it holds local state without becoming an
observable effect, so a counting loop does not force `Tulis` on its caller. A
`ruj` cell would, because a `ruj` cell can escape.

## Why the comparison is written the way it is

`pengesah::banding_masa_tetap` looks at **every** position of both strings and
accumulates differences instead of returning at the first mismatch. A
comparison that returns early leaks the length of the matching prefix through
its running time, and a few thousand timed guesses recover a secret one
character at a time. There is deliberately no `putus` in that loop.

`peraturan::skor` is the contrast: its length loop *does* `putus` once it has
awarded its cap, because everything it looks at is public. Short-circuiting is
a bug in one and the right thing in the other — the difference is what the data
is, not what the loop looks like.

## What this example would have done before 2026-08

All of it silently wrong, none of it diagnosed:

- `selagi` desugared to `if cond { body; () }`, so every scoring loop inspected
  one character. `Sungai#Kelantan7` would have scored as a one-character
  lowercase password.
- `biar ubah` was decorative — `x = e;` re-parsed as a shadowing `biar` — so
  even with real loops the accumulators would have reset every iteration.
- Together those made `banding_masa_tetap` compare position 0 and stop, so
  `beza` was 0 for **any** two strings sharing a first character and
  `semak_rahsia` accepted them as equal. Not a timing side-channel: an
  authentication bypass, in the function whose entire purpose was to be safe.
  `ujian_banding_menolak_awalan_sepadan` in `utama.rii` is that case, and the
  compiler's own `loops_differential.rs` asserts it.

## Notes on the surface language

- Definitions still precede uses here, but they no longer have to: a forward
  call used to type-check and interpret fine and then fail `riinac build` with
  `unbound variable: <module>_<callee>`, because codegen lowered a top-level
  group as a backward-reference chain. Groups are lowered properly now, so
  declaration order is the author's choice again.
- `dasar`, `lajur`, `sahkan` and `luaran` are keywords, so they cannot be used
  as module, variable or function names — hence `peraturan`, `medan` and
  `semak_rahsia`.
- `riinac build --target wasm32` still refuses this program, but no longer
  because of its loops — those compile now, to a `block`/`loop` pair with
  `br_if`. What it refuses is the `panjang` builtin, which that backend has not
  implemented; it fails closed rather than emit a stub that returns a wrong
  length (REQ-78).
