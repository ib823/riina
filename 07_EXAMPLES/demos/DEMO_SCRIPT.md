# RIINA Demo Script

Terminal commands and expected output for each demo.

## Prerequisites

```bash
cd 03_PROTO
cargo build --release
```

---

## Demo 1: Selamat Datang (Hello Malaysia)

**Audience:** Malaysian tech community, general developers

```bash
$ riinac run 07_EXAMPLES/demos/selamat_datang.rii
Selamat datang ke RIINA, Malaysia!

$ riinac build 07_EXAMPLES/demos/selamat_datang.rii
Built: 07_EXAMPLES/demos/selamat_datang

$ ./07_EXAMPLES/demos/selamat_datang
Selamat datang ke RIINA, Malaysia!
```

**Features shown:** Bahasa Melayu keywords (`biar`, `cetakln`), string builtins (`gabung_teks`), native compilation.

---

## Demo 2: Rahsia Dijaga (Secret Types)

**Audience:** Security engineers, PL researchers

```bash
$ riinac run 07_EXAMPLES/demos/rahsia_dijaga.rii
s3cr3t_p4ss
```

**Features shown:** `sulit` (classify), `bukti` (prove), `dedah` (declassify) — secrets tracked through the type system.

---

## Demo 3: Kalkulator C (C FFI)

**Audience:** Systems programmers

```bash
$ riinac build 07_EXAMPLES/demos/kalkulator_c.rii
Built: 07_EXAMPLES/demos/kalkulator_c

$ ./07_EXAMPLES/demos/kalkulator_c
42
```

**Features shown:** `luaran "C"` extern blocks, calling C `abs()` from RIINA, native binary interop.

---

## Demo 4: Pasangan (Safe Pairs)

**Audience:** FP enthusiasts

```bash
$ riinac run 07_EXAMPLES/demos/pasangan.rii
Titik: (10, 20)

$ riinac build 07_EXAMPLES/demos/pasangan.rii
Built: 07_EXAMPLES/demos/pasangan

$ ./07_EXAMPLES/demos/pasangan
Titik: (10, 20)
```

**Features shown:** Pair construction, `pertama`/`kedua` projections, `ke_teks` conversion.

---

## Demo 5: Faktorial (Recursive Functions)

**Audience:** All developers (flagship demo)

```bash
$ riinac run 07_EXAMPLES/demos/faktorial.rii
faktorial(10) = 3628800

$ riinac build 07_EXAMPLES/demos/faktorial.rii
Built: 07_EXAMPLES/demos/faktorial

$ ./07_EXAMPLES/demos/faktorial
faktorial(10) = 3628800
```

**Features shown:** Recursive functions (`fungsi` + `LetRec`), arithmetic, native compilation, Bahasa Melayu syntax.

---

## Quick Run All

```bash
for demo in selamat_datang rahsia_dijaga pasangan faktorial; do
    echo "=== $demo ==="
    riinac run 07_EXAMPLES/demos/${demo}.rii
    echo
done
```
