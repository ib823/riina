# RIINA

**Bahasa pengaturcaraan yang disahkan secara formal.**

Sifat keselamatan bukan diuji, bukan diandaikan — ia *dibuktikan secara matematik* pada masa kompilasi.

---

## Apa itu RIINA?

RIINA ialah bahasa pengaturcaraan di mana **setiap jaminan keselamatan mempunyai bukti matematik yang disemak mesin**. Jika program anda boleh dikompilasi, ia selamat — bukan kerana konvensyen, bukan amalan terbaik, tetapi kerana bukti.

| Apa yang RIINA buktikan pada masa kompilasi | Bagaimana |
|---|---|
| Tiada kebocoran maklumat antara tahap keselamatan | Teorem bukan-gangguan (Coq) |
| Tiada pelaksanaan kesan tanpa kebenaran | Algebra pintu kesan (Coq) |
| Keselamatan jenis (tiada ralat jenis masa larian) | Teorem Kemajuan + Pemeliharaan (Coq) |
| Tiada data rahsia dalam output awam | Bukti dasar deklasifikasi (Coq) |
| Penamatan semua pengiraan tulen | Bukti normalisasi kuat (Coq) |
| Keselamatan memori tanpa pengutip sampah | Bukti logik pemisahan (Coq) |

---

## Mula Pantas

### Pasang

```bash
git clone https://github.com/ib823/riina.git
cd riina/03_PROTO
cargo build --release
```

Binari pengkompil ialah `riinac`. Sifar kebergantungan luaran.

### Hello World

Cipta `hello.rii`:

```riina
fungsi utama() -> Teks kesan IO {
    biar mesej = "Selamat datang ke RIINA!";
    cetakln(mesej);
    pulang mesej;
}
```

```bash
riinac check hello.rii    # Semak jenis dan sahkan
riinac run hello.rii      # Jalankan terus
riinac build hello.rii    # Kompilasi ke binari natif melalui C
```

### Keselamatan dalam Tindakan

```riina
// RIINA menghalang kebocoran maklumat pada masa kompilasi

fungsi proses_pembayaran(kad: Rahsia<Teks>, jumlah: Nombor) -> Teks kesan Kripto {
    // 'kad' ialah Rahsia — pengkompil MEMBUKTIKAN ia tidak sampai ke output awam

    biar hash = sha256(kad);           // OK: kripto pada data rahsia
    biar resit = "Jumlah: " + ke_teks(jumlah);  // OK: jumlah ialah awam

    // cetakln(kad);                   // RALAT KOMPILASI: data rahsia dalam kesan IO
    // pulang kad;                     // RALAT KOMPILASI: rahsia dalam pulangan awam

    pulang resit;                      // OK: hanya data awam dikembalikan
}
```

---

## Kata Kunci Bahasa Melayu

| RIINA | Inggeris | Contoh |
|-------|---------|--------|
| `fungsi` | fn | `fungsi tambah(x: Nombor) -> Nombor` |
| `biar` | let | `biar nama = "Ahmad";` |
| `kalau` | if | `kalau x > 0 { ... }` |
| `lain` | else | `lain { ... }` |
| `untuk` | for | `untuk x dalam senarai { ... }` |
| `selagi` | while | `selagi aktif { ... }` |
| `pulang` | return | `pulang hasil;` |
| `padan` | match | `padan nilai { ... }` |
| `rahsia` | secret | `biar kunci: Rahsia<Teks>` |
| `dedah` | declassify | `dedah(nilai)` |
| `kesan` | effect | `kesan IO` |
| `bersih` | pure | `kesan Bersih` |
| `betul` / `salah` | true / false | Nilai Boolean |
| `ubah` | mut | `biar ubah x = 0;` |

---

## Sumbangan

Lihat [CONTRIBUTING.md](../../CONTRIBUTING.md) untuk panduan sumbangan.

## Lesen

[Mozilla Public License 2.0](../../LICENSE)

---

*RIINA — Rigorous Immutable Invariant, No Assumptions*

*Q.E.D. Aeternum.*
