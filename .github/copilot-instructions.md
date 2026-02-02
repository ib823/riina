# GitHub Copilot Instructions for RIINA

## Language: RIINA

RIINA is a formally verified programming language with Bahasa Melayu keywords. File extension: `.rii`.

## Rules for Code Generation

1. Use ONLY Bahasa Melayu keywords: `fungsi` (fn), `biar` (let), `kalau` (if), `lain` (else), `pulang` (return), `padan` (match), `untuk` (for), `selagi` (while), `ulang` (loop), `betul` (true), `salah` (false).
2. Every function needs an effect annotation: `kesan Bersih` (pure), `kesan Tulis` (write), `kesan Baca` (read), `kesan Rangkaian` (network), `kesan Kripto` (crypto), `kesan Sistem` (system).
3. Use Bahasa Melayu type names: `Nombor` (Int), `Teks` (String), `Benar` (Bool), `Kosong` (Unit), `Rahsia<T>` (Secret), `Mungkin<T>` (Option), `Hasil<T,E>` (Result), `Senarai<T>` (List).
4. Statements separated by semicolons. Last expression is return value.
5. If-else must have both branches.
6. Entry point: `fungsi utama() -> Nombor kesan Tulis { ... }`

## Pipe Operator

Use `|>` for functional composition: `5 |> darab_dua |> tambah_satu`

## Secret Types

- `Rahsia<T>` cannot be printed or leaked
- Use `dedah(secret, bukti: "reason")` to declassify

## FFI

```riina
luaran "C" {
    fungsi puts(s: *CChar) -> CInt;
}
```

## Builtin Functions (prefer Bahasa Melayu names)

- I/O: `cetak`, `cetakln`
- String: `gabung_teks`, `panjang`, `teks_belah`, `teks_cantum`
- Math: `mutlak`, `minimum`, `maksimum`, `kuasa`, `punca`
- List: `senarai_peta`, `senarai_tapis`, `senarai_lipat`
- Assert: `tegaskan`, `tegaskan_sama`

## Example

```riina
fungsi tambah(x: Nombor, y: Nombor) -> Nombor kesan Bersih {
    x + y
}

fungsi utama() -> Nombor kesan Tulis {
    biar hasil = tambah(3, 4);
    cetak(hasil);
    pulang 0;
}
```
