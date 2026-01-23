# RIINA Bahasa Melayu Syntax Specification

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║                                                                                  ║
║  ██████╗ ██╗██╗███╗   ██╗ █████╗                                                ║
║  ██╔══██╗██║██║████╗  ██║██╔══██╗                                               ║
║  ██████╔╝██║██║██╔██╗ ██║███████║                                               ║
║  ██╔══██╗██║██║██║╚██╗██║██╔══██║                                               ║
║  ██║  ██║██║██║██║ ╚████║██║  ██║                                               ║
║  ╚═╝  ╚═╝╚═╝╚═╝╚═╝  ╚═══╝╚═╝  ╚═╝                                               ║
║                                                                                  ║
║  Rigorous Immutable Invariant — Normalized Axiom                                  ║
║                                                                                  ║
║  BAHASA MELAYU SYNTAX SPECIFICATION                                             ║
║  Version 1.0.0                                                                   ║
║                                                                                  ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RIINA-BAHASA-MELAYU-SYNTAX |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Status | AUTHORITATIVE |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |

---

## 1. INTRODUCTION

### 1.1 Purpose

This document defines the **complete and authoritative** syntax specification for RIINA,
the world's first formally verified programming language with Bahasa Melayu keywords.

RIINA combines:
- **Mathematical rigor** — All security properties proven in Coq
- **Cultural identity** — Bahasa Melayu syntax honoring Malaysian heritage

### 1.2 Name Origin

```
Technical Acronym:
RIINA = Rigorous Immutable Invariant — Normalized Axiom
```

### 1.3 File Extension

| Extension | Purpose |
|-----------|---------|
| `.rii` | RIINA source files |
| `.riih` | RIINA header/interface files |
| `.riim` | RIINA module files |

### 1.4 Language Philosophy

The Bahasa Melayu syntax follows these principles:

1. **Street-practical** — Common words used in everyday Malaysian speech
2. **Respectful** — No crude slang; dignified vocabulary
3. **Accurate** — Proper Malay where applicable
4. **Concise** — Short keywords for efficient coding
5. **Consistent** — Predictable patterns throughout

---

## 2. KEYWORD REFERENCE

### 2.1 Declaration Keywords (Kata Kunci Pengisytiharan)

| Bahasa Melayu | English | Usage | Example |
|---------------|---------|-------|---------|
| `fungsi` | fn/function | Declare function | `fungsi tambah(x: Nombor) -> Nombor` |
| `biar` | let | Variable binding | `biar nama = "Ahmad";` |
| `ubah` | mut | Mutable modifier | `biar ubah kiraan = 0;` |
| `tetap` | const | Constant | `tetap MAX = 100;` |
| `statik` | static | Static variable | `statik CACHE: Senarai = [];` |
| `bentuk` | struct | Structure | `bentuk Pengguna { nama: Teks }` |
| `pilihan` | enum | Enumeration | `pilihan Warna { Merah, Biru }` |
| `jenis` | type | Type alias | `jenis Id = Nombor;` |
| `sifat` | trait | Trait | `sifat Boleh_Cetak { ... }` |
| `laksana` | impl | Implementation | `laksana Pengguna { ... }` |
| `modul` | mod | Module | `modul pengesahan;` |
| `guna` | use | Import | `guna std::io;` |
| `awam` | pub | Public visibility | `awam fungsi api() { }` |
| `luaran` | extern | External | `luaran "C" { ... }` |

### 2.2 Control Flow Keywords (Kata Kunci Kawalan Aliran)

| Bahasa Melayu | English | Usage | Example |
|---------------|---------|-------|---------|
| `kalau` | if | Conditional | `kalau x > 0 { ... }` |
| `lain` | else | Alternative | `lain { ... }` |
| `untuk` | for | For loop | `untuk i dalam 0..10 { }` |
| `selagi` | while | While loop | `selagi aktif { }` |
| `ulang` | loop | Infinite loop | `ulang { ... keluar; }` |
| `keluar` | break | Break loop | `keluar;` |
| `terus` | continue | Continue loop | `terus;` |
| `pulang` | return | Return value | `pulang hasil;` |
| `padan` | match | Pattern match | `padan nilai { ... }` |
| `dengan` | with | With clause | `kendali e dengan { }` |

### 2.3 Boolean and Logic (Boolean dan Logik)

| Bahasa Melayu | English | Usage | Example |
|---------------|---------|-------|---------|
| `betul` | true | True value | `biar aktif = betul;` |
| `salah` | false | False value | `biar tutup = salah;` |
| `dan` | and/&& | Logical AND | `kalau a dan b { }` |
| `atau` | or/\|\| | Logical OR | `kalau a atau b { }` |
| `bukan` | not/! | Logical NOT | `kalau bukan aktif { }` |
| `dalam` | in | Membership | `untuk x dalam senarai` |
| `ialah` | is | Type check | `kalau x ialah Nombor` |
| `sebagai` | as | Type cast | `x sebagai Nombor` |

### 2.4 Type Keywords (Kata Kunci Jenis)

| Bahasa Melayu | English | Description |
|---------------|---------|-------------|
| `Kosong` | Unit/() | Empty type, no value |
| `Benar` | Bool | Boolean type |
| `Nombor` | Int | Integer type |
| `Pecahan` | Float | Floating point |
| `Teks` | String | Text/string |
| `Aksara` | Char | Single character |
| `Bait` | Bytes | Byte array |
| `Senarai` | Vec/List | Dynamic array |
| `Peta` | Map/HashMap | Key-value map |
| `Set` | Set | Unique collection |
| `Mungkin` | Option | Optional value |
| `Hasil` | Result | Result type |
| `Rujukan` | Ref | Reference type |
| `Penunjuk` | Ptr | Pointer type |

### 2.5 Option and Result (Mungkin dan Hasil)

| Bahasa Melayu | English | Usage |
|---------------|---------|-------|
| `Mungkin` | Option | Optional type wrapper |
| `Ada` | Some | Has value |
| `Tiada` | None | No value |
| `Hasil` | Result | Result type wrapper |
| `Jadi` | Ok | Success |
| `Gagal` | Err | Failure |

### 2.6 Security Keywords (Kata Kunci Keselamatan) — RIINA Exclusive

| Bahasa Melayu | English | Description | Example |
|---------------|---------|-------------|---------|
| `rahsia` | secret | Secret type modifier | `biar kunci: Rahsia<Teks>` |
| `terbuka` | public | Public security level | `tahap Terbuka` |
| `sulit` | classify | Make secret | `sulit(data)` |
| `dedah` | declassify | Reveal with proof | `dedah(x, bukti: B)` |
| `bukti` | prove | Proof term | `bukti KeselamatanSah` |
| `dasar` | policy | Security policy | `dasar: "semak_kata"` |
| `tahap` | level | Security level annotation | `tahap Rahsia` |
| `bersih` | pure | No side effects | `kesan Bersih` |
| `selamat` | safe | Safety annotation | `selamat { ... }` |
| `bahaya` | unsafe | Unsafe block | `bahaya { ... }` |

### 2.7 Effect Keywords (Kata Kunci Kesan)

| Bahasa Melayu | English | Description |
|---------------|---------|-------------|
| `kesan` | effect | Effect annotation |
| `Bersih` | Pure | No effects |
| `Baca` | Read | Read effect |
| `Tulis` | Write | Write effect |
| `Rangkaian` | Network | Network I/O |
| `Kripto` | Crypto | Cryptographic operations |
| `Sistem` | System | System calls |
| `laku` | perform | Perform effect |
| `kendali` | handle | Handle effect |
| `sambung` | resume | Resume from handler |
| `batal` | abort | Abort operation |

### 2.8 Constant-Time Keywords (Kata Kunci Masa Tetap)

| Bahasa Melayu | English | Description |
|---------------|---------|-------------|
| `masa_tetap` | ct/constant-time | Constant-time block |
| `selamat_spekulasi` | speculation-safe | Speculation-safe |
| `gabungan` | combined | Combined CT+SS |
| `kosongkan` | zeroize | Secure erasure |

### 2.9 Concurrency Keywords (Kata Kunci Keselarasan)

| Bahasa Melayu | English | Description |
|---------------|---------|-------------|
| `sesi` | session | Session type |
| `saluran` | channel | Communication channel |
| `hantar` | send | Send message |
| `terima` | receive | Receive message |
| `pilih` | select | Select branch |
| `cabang` | branch | Branch point |
| `tamat` | end | End session |
| `atom` | atomic | Atomic operation |
| `pagar` | fence | Memory fence |
| `peroleh` | acquire | Acquire semantics |
| `lepas` | release | Release semantics |

### 2.10 Reference Keywords (Kata Kunci Rujukan)

| Bahasa Melayu | English | Description |
|---------------|---------|-------------|
| `ruj` | ref | Create reference |
| `pinjam` | borrow | Borrow reference |
| `pindah` | move | Move ownership |
| `salin` | copy | Copy value |
| `klon` | clone | Deep clone |
| `jangka` | lifetime | Lifetime annotation |

### 2.11 Self and Type References

| Bahasa Melayu | English | Description |
|---------------|---------|-------------|
| `diri` | self | Instance reference |
| `Diri` | Self | Type reference |
| `super` | super | Parent module |
| `peti` | crate | Current crate |

---

## 3. TYPE SYSTEM

### 3.1 Primitive Types (Jenis Primitif)

```riina
// Boolean
biar aktif: Benar = betul;
biar tutup: Benar = salah;

// Numbers
biar umur: Nombor = 25;
biar harga: Pecahan = 19.99;
biar besar: Nombor64 = 9_999_999_999;

// Text
biar nama: Teks = "Ahmad";
biar huruf: Aksara = 'A';

// Bytes
biar data: Bait = b"\x00\x01\x02\xFF";

// Unit (void equivalent)
biar kosong: Kosong = ();
```

### 3.2 Compound Types (Jenis Gabungan)

```riina
// Tuple (Tupel)
biar pasangan: (Nombor, Teks) = (42, "jawapan");
biar pertama = pasangan.0;
biar kedua = pasangan.1;

// Array (Tatasusunan) - fixed size
biar nombor: [Nombor; 5] = [1, 2, 3, 4, 5];

// Vector/List (Senarai) - dynamic
biar senarai: Senarai<Nombor> = senarai![1, 2, 3];
senarai.tambah(4);

// Map (Peta)
biar ubah peta: Peta<Teks, Nombor> = Peta::baru();
peta.letak("kunci", 42);
```

### 3.3 Function Types (Jenis Fungsi)

```riina
// Function type: Input -[Effect]-> Output
jenis Pengira = fungsi(Nombor) -[Bersih]-> Nombor;
jenis Pembaca = fungsi(Teks) -[Baca]-> Hasil<Bait, Ralat>;

// Function with effect annotation
fungsi kira(x: Nombor) -> Nombor
    kesan Bersih
{
    x * 2
}

// Higher-order function
fungsi peta<T, U>(
    senarai: Senarai<T>,
    f: fungsi(T) -[Bersih]-> U
) -> Senarai<U>
    kesan Bersih
{
    // implementation
}
```

### 3.4 Security Types (Jenis Keselamatan)

```riina
// Secret wrapper - cannot be printed or leaked
biar katalaluan: Rahsia<Teks> = rahsia("hunter2");

// Operations on secrets produce secrets
biar hash: Rahsia<Hash> = sha256(katalaluan);

// Reference with security level
biar ruj_awam: Ruj<Nombor, Terbuka> = ruj(42);
biar ruj_sulit: Ruj<Nombor, Rahsia> = ruj_sulit(kunci);

// Proof type - compile-time evidence
biar bukti_sah: Bukti<AdaKebenaran> = buktikan();

// Capability type
biar kap_rangkaian: Keupayaan<Rangkaian> = minta_keupayaan();
```

### 3.5 Option and Result (Mungkin dan Hasil)

```riina
// Option type
pilihan Mungkin<T> {
    Ada(T),
    Tiada,
}

// Result type
pilihan Hasil<T, E> {
    Jadi(T),
    Gagal(E),
}

// Usage
fungsi cari(id: Nombor) -> Mungkin<Pengguna> {
    kalau id == 0 {
        pulang Tiada;
    }
    pulang Ada(muatkan_pengguna(id));
}

fungsi baca_fail(laluan: Teks) -> Hasil<Bait, RalatIO> {
    kalau bukan wujud(laluan) {
        pulang Gagal(RalatIO::TakWujud);
    }
    pulang Jadi(muatkan(laluan));
}
```

---

## 4. DECLARATIONS

### 4.1 Functions (Fungsi)

```riina
// Basic function
fungsi tambah(x: Nombor, y: Nombor) -> Nombor {
    x + y
}

// Function with full annotations
fungsi sahkan_pengguna(
    nama: Teks,
    katalaluan: Rahsia<Teks>,
    db: &PangkalanData
) -> Hasil<TokenSesi, RalatSah>
    kesan Baca                    // Effect annotation
    tahap Terbuka                 // Security level of output
    masa_tetap                    // Constant-time requirement
{
    // implementation
}

// Generic function
fungsi tukar<T, U>(nilai: T, f: fungsi(T) -> U) -> U
    di mana T: Salin, U: Lalai
{
    f(nilai)
}

// Method (within impl block)
laksana Pengguna {
    fungsi baru(nama: Teks) -> Diri {
        Pengguna { nama: nama, id: jana_id() }
    }

    fungsi nama(&diri) -> &Teks {
        &diri.nama
    }

    fungsi tukar_nama(&ubah diri, nama_baru: Teks) {
        diri.nama = nama_baru;
    }
}
```

### 4.2 Structures (Bentuk)

```riina
// Basic struct
bentuk Titik {
    x: Nombor,
    y: Nombor,
}

// Struct with visibility
awam bentuk Pengguna {
    awam id: Nombor,
    awam nama: Teks,
    rahsia hash_kata: Rahsia<Hash>,  // Private secret field
    garam: Bait,                      // Private field
}

// Tuple struct
bentuk Warna(Nombor, Nombor, Nombor);

// Unit struct
bentuk Penanda;

// Generic struct
bentuk Kotak<T> {
    nilai: T,
}

// Struct with lifetime
bentuk Rujukan<'a, T> {
    data: &'a T,
}
```

### 4.3 Enumerations (Pilihan)

```riina
// Simple enum
pilihan Arah {
    Utara,
    Selatan,
    Timur,
    Barat,
}

// Enum with data
pilihan Mesej {
    Teks(Teks),
    Nombor(Nombor),
    Binari(Bait),
    Sulit(Rahsia<Bait>),
}

// Generic enum
pilihan Mungkin<T> {
    Ada(T),
    Tiada,
}

// Enum with explicit values
pilihan KodRalat {
    Jaya = 0,
    TakJumpa = 404,
    DalamanGagal = 500,
}
```

### 4.4 Traits (Sifat)

```riina
// Basic trait
sifat BolehCetak {
    fungsi cetak(&diri) -> Teks;
}

// Trait with default implementation
sifat Lalai {
    fungsi lalai() -> Diri;

    fungsi kosong() -> Diri {
        Diri::lalai()
    }
}

// Trait with associated types
sifat Pengulang {
    jenis Item;
    fungsi seterusnya(&ubah diri) -> Mungkin<Diri::Item>;
}

// Trait bounds
sifat Boleh_Hash: Sama + Salin {
    fungsi hash(&diri) -> Nombor64;
}

// Implementation
laksana BolehCetak untuk Pengguna {
    fungsi cetak(&diri) -> Teks {
        format!("Pengguna: {}", diri.nama)
    }
}
```

### 4.5 Modules (Modul)

```riina
// Module declaration
modul pengesahan;
modul kripto;
modul rangkaian;

// Inline module
modul dalaman {
    awam fungsi helper() { }
}

// Import
guna std::io::{baca, tulis};
guna peti::modul::Jenis;
guna super::fungsi_induk;

// Re-export
awam guna dalaman::helper;
```

---

## 5. CONTROL FLOW

### 5.1 Conditionals (Bersyarat)

```riina
// If expression
biar max = kalau a > b { a } lain { b };

// If-else chain
kalau suhu > 30 {
    cetak("Panas");
} lain kalau suhu > 20 {
    cetak("Sederhana");
} lain kalau suhu > 10 {
    cetak("Sejuk");
} lain {
    cetak("Sangat sejuk");
}

// Let-if (if-let equivalent)
kalau biar Ada(nilai) = mungkin_nilai {
    proses(nilai);
}

// Guard clause
kalau bukan sah {
    pulang Gagal(RalatSah);
}
```

### 5.2 Pattern Matching (Pemadanan Corak)

```riina
// Basic match
biar hasil = padan nilai {
    0 => "kosong",
    1 => "satu",
    2..=9 => "sedikit",
    _ => "banyak",
};

// Match with destructuring
padan titik {
    Titik { x: 0, y: 0 } => cetak("Asal"),
    Titik { x, y: 0 } => cetak("Pada paksi X: {}", x),
    Titik { x: 0, y } => cetak("Pada paksi Y: {}", y),
    Titik { x, y } => cetak("Titik: ({}, {})", x, y),
}

// Match on enum
padan mesej {
    Mesej::Teks(t) => cetak("Teks: {}", t),
    Mesej::Nombor(n) => cetak("Nombor: {}", n),
    Mesej::Binari(b) => simpan_binari(b),
    Mesej::Sulit(data) => {
        // Cannot print secret data
        simpan_sulit(data)
    }
}

// Match with guards
padan umur {
    n kalau n < 0 => panik!("Umur tak sah"),
    0..=12 => "kanak-kanak",
    13..=19 => "remaja",
    20..=59 => "dewasa",
    _ => "warga emas",
}

// Match with binding
padan nilai {
    n @ 1..=100 => cetak("Dalam julat: {}", n),
    n => cetak("Luar julat: {}", n),
}
```

### 5.3 Loops (Gelung)

```riina
// For loop
untuk i dalam 0..10 {
    cetak("{}", i);
}

// For with iterator
untuk item dalam senarai {
    proses(item);
}

// For with enumerate
untuk (indeks, nilai) dalam senarai.enumerate() {
    cetak("{}: {}", indeks, nilai);
}

// While loop
selagi aktif {
    kemas_kini();
    kalau siap {
        aktif = salah;
    }
}

// While-let
selagi biar Ada(item) = pengulang.seterusnya() {
    proses(item);
}

// Infinite loop with break
biar hasil = ulang {
    biar input = baca_input();
    kalau input.sah() {
        keluar input.nilai();
    }
    cetak("Cuba lagi");
};

// Loop with continue
untuk i dalam 0..100 {
    kalau i % 2 == 0 {
        terus;  // Skip even numbers
    }
    cetak("{}", i);
}

// Labeled loops
'luar: untuk i dalam 0..10 {
    'dalam: untuk j dalam 0..10 {
        kalau i * j > 50 {
            keluar 'luar;
        }
    }
}
```

---

## 6. SECURITY FEATURES

### 6.1 Secret Types (Jenis Rahsia)

```riina
// Creating secrets
biar katalaluan: Rahsia<Teks> = rahsia("kata_rahsia");
biar kunci: Rahsia<Bait> = rahsia(jana_kunci());

// Classifying data
biar data_sulit: Rahsia<Teks> = sulit(data_awam);

// Operations on secrets (output is also secret)
biar hash: Rahsia<Hash> = sha256(katalaluan);
biar disulitkan: Rahsia<Bait> = aes_sulit(kunci, data);

// COMPILE ERRORS - cannot leak secrets:
// cetak(katalaluan);           // ERROR: Cannot output Rahsia<Teks>
// biar x: Teks = katalaluan;   // ERROR: Cannot convert Rahsia<Teks> to Teks
// kalau katalaluan == "abc"    // ERROR: Cannot compare secrets with public
```

### 6.2 Declassification (Pendedahan)

```riina
// Declassify with policy
fungsi semak_kata(
    input: Rahsia<Teks>,
    simpan: Hash
) -> Benar
    kesan Bersih
    tahap Terbuka
{
    biar hash_input = sha256(input);

    // Must provide policy and proof
    dedah(
        sama_masa_tetap(hash_input, simpan),
        dasar: "semak_katalaluan",
        bukti: BuktiPengesahan::baru()
    )
}

// Policy definition (in separate policy file)
dasar semak_katalaluan {
    prinsipal: PerkhidmatanPengesahan,
    apa: Benar,  // Only boolean result
    bila: percubaan_dalam_tetingkap < 5,
    bajet: 1 bit setiap percubaan,
    audit: WAJIB,
}
```

### 6.3 Constant-Time Operations (Operasi Masa Tetap)

```riina
// Constant-time block
fungsi bandingkan_hash(a: Rahsia<Hash>, b: Hash) -> Benar
    kesan Bersih
    masa_tetap  // Enforced by compiler
{
    masa_tetap {
        // All operations inside must be constant-time
        // Variable-time operations are COMPILE ERRORS
        biar ubah hasil = betul;
        untuk i dalam 0..32 {
            hasil = hasil dan (a[i] == b[i]);
        }
        hasil
    }
}

// Speculation-safe block
selamat_spekulasi {
    // Code here cannot leak via speculative execution
}

// Combined constant-time and speculation-safe
gabungan {
    // Both guarantees enforced
}
```

### 6.4 Effect System (Sistem Kesan)

```riina
// Effect annotations
fungsi fungsi_bersih() -> Nombor
    kesan Bersih  // No side effects
{
    42
}

fungsi baca_fail(laluan: Teks) -> Hasil<Bait, Ralat>
    kesan Baca  // Read effect
{
    Fail::baca(laluan)
}

fungsi tulis_log(mesej: Teks) -> Hasil<(), Ralat>
    kesan Tulis  // Write effect
{
    Fail::tambah("/var/log/app.log", mesej)
}

fungsi ambil_data(url: Teks) -> Hasil<Respons, Ralat>
    kesan Rangkaian  // Network effect
{
    Http::ambil(url)
}

// Effect handling
fungsi dengan_log<T>(
    tindakan: fungsi() -[Tulis]-> T
) -> T
    kesan Bersih  // Handler absorbs effect
{
    kendali tindakan() dengan {
        Tulis(data) => {
            // Intercept writes
            penampan.tambah(data);
            sambung(())
        }
    }
}
```

### 6.5 Capabilities (Keupayaan)

```riina
// Require capability
fungsi perlu_rangkaian() -> Respons
    perlukan Keupayaan<Rangkaian>
{
    Http::ambil("https://api.contoh.com")
}

// Grant capability
fungsi utama() {
    beri Keupayaan<Rangkaian> {
        biar respons = perlu_rangkaian();
    }
}

// Revoke capability
batalkan Keupayaan<Rangkaian> untuk_skop {
    // No network access here
}
```

---

## 7. CONCURRENCY

### 7.1 Session Types (Jenis Sesi)

```riina
// Define protocol
sesi PindahFail {
    hantar NamaFail: Teks;
    terima Saiz: Nombor;
    hantar Sahkan: Benar;
    terima Data: Bait;
    tamat;
}

// Client implementation
fungsi pelanggan(ch: Saluran<PindahFail>) -> Hasil<Bait, Ralat>
    kesan Rangkaian
{
    ch.hantar("data.txt")?;        // Must send Teks first
    biar saiz = ch.terima()?;       // Must receive Nombor second
    ch.hantar(betul)?;              // Must send Benar third
    biar data = ch.terima()?;       // Must receive Bait fourth
    ch.tutup();                     // Must close at end
    Jadi(data)
}

// Protocol violations are COMPILE ERRORS:
// ch.terima();  // ERROR: Expected hantar, got terima
```

### 7.2 Channels (Saluran)

```riina
// Create channel
biar (penghantar, penerima) = saluran::<Mesej>();

// Send
penghantar.hantar(Mesej::Teks("Hello"))?;

// Receive
biar mesej = penerima.terima()?;

// Select (multiple channels)
pilih! {
    mesej = penerima1.terima() => proses1(mesej),
    mesej = penerima2.terima() => proses2(mesej),
    lalai => cetak("Tiada mesej"),
}
```

### 7.3 Atomic Operations (Operasi Atom)

```riina
// Atomic types
biar kiraan: Atom<Nombor> = Atom::baru(0);

// Atomic operations
kiraan.tambah(1, Tertib::SeqCst);
biar nilai = kiraan.muat(Tertib::Peroleh);
kiraan.simpan(42, Tertib::Lepas);

// Compare and swap
kiraan.banding_dan_tukar(0, 1, Tertib::SeqCst);

// Memory fence
pagar(Tertib::SeqCst);
```

---

## 8. ERROR HANDLING

### 8.1 Result Type (Jenis Hasil)

```riina
// Return Result
fungsi bahagi(x: Nombor, y: Nombor) -> Hasil<Nombor, RalatMatematik> {
    kalau y == 0 {
        pulang Gagal(RalatMatematik::BahagiBolehKosong);
    }
    Jadi(x / y)
}

// Propagate errors with ?
fungsi kira() -> Hasil<Nombor, Ralat> {
    biar a = bahagi(10, 2)?;  // Returns early if Gagal
    biar b = bahagi(a, 2)?;
    Jadi(b)
}

// Handle Result
padan hasil {
    Jadi(nilai) => cetak("Berjaya: {}", nilai),
    Gagal(ralat) => cetak("Ralat: {}", ralat),
}

// Unwrap (panics on Gagal)
biar nilai = hasil.buka();  // Use with caution

// Unwrap with default
biar nilai = hasil.buka_atau(0);

// Map Result
biar baru = hasil.peta(|x| x * 2);
```

### 8.2 Option Type (Jenis Mungkin)

```riina
// Return Option
fungsi cari(senarai: &Senarai<Nombor>, sasaran: Nombor) -> Mungkin<Nombor> {
    untuk (i, &nilai) dalam senarai.enumerate() {
        kalau nilai == sasaran {
            pulang Ada(i);
        }
    }
    Tiada
}

// Handle Option
padan mungkin_nilai {
    Ada(x) => cetak("Jumpa: {}", x),
    Tiada => cetak("Tak jumpa"),
}

// Chaining
biar hasil = mungkin_a
    .dan_kemudian(|a| mungkin_b(a))
    .peta(|b| b * 2)
    .buka_atau(0);
```

### 8.3 Panic (Panik)

```riina
// Explicit panic
panik!("Sesuatu yang tak dijangka berlaku");

// Assert
tegaskan!(x > 0, "x mesti positif");
tegaskan_sama!(a, b);
tegaskan_tak_sama!(a, b);

// Debug assert (only in debug builds)
nyahpijat_tegaskan!(x > 0);

// Unreachable
padan nilai {
    Ada(x) => x,
    Tiada => tak_tercapai!("Ini tak sepatutnya berlaku"),
}
```

---

## 9. STANDARD LIBRARY OVERVIEW

### 9.1 Core Modules (Modul Teras)

```riina
guna std::io;           // Input/Output
guna std::fail;         // File operations
guna std::rangkaian;    // Networking
guna std::kripto;       // Cryptography
guna std::koleksi;      // Collections
guna std::masa;         // Time
guna std::benang;       // Threading
guna std::sinkron;      // Synchronization
guna std::teks;         // String utilities
guna std::nombor;       // Number utilities
```

### 9.2 Common Functions (Fungsi Lazim)

```riina
// Printing
cetak!("Hello, Dunia!");
cetak_baris!("Dengan baris baru");
eprint!("Ke stderr");

// Formatting
biar s = format!("Nama: {}, Umur: {}", nama, umur);

// Debug printing
nyahpijat!("Nilai: {:?}", x);

// Input
biar input = baca_baris()?;

// File operations
biar kandungan = Fail::baca_ke_teks("fail.txt")?;
Fail::tulis("keluar.txt", data)?;
```

---

## 10. COMPLETE EXAMPLE

```riina
//! Sistem Pengesahan Selamat RIINA
//!
//! Semua sifat keselamatan disahkan pada masa kompil.
//! Tiada kebocoran maklumat. Tiada serangan masa. Tiada kompromi.

guna std::kripto::{sha256, sama_masa_tetap, jana_garam};
guna std::hasil::Hasil;
guna std::io::cetak_baris;

/// Maklumat pengguna dalam pangkalan data
awam bentuk Pengguna {
    awam id: Nombor,
    awam nama: Teks,
    hash_kata: Rahsia<Hash>,
    garam: Bait,
}

/// Hasil pengesahan
awam pilihan HasilSah {
    Berjaya(TokenSesi),
    Gagal(RalatSah),
}

/// Ralat pengesahan
awam pilihan RalatSah {
    TakSah,
    TakWujud,
    TerlaluBanyakPercubaan,
}

/// Dasar pendedahan untuk semakan katalaluan
dasar semak_kata {
    prinsipal: PerkhidmatanSah,
    apa: Benar,
    bila: percubaan < 5,
    bajet: 1 bit,
    audit: WAJIB,
}

/// Sahkan pengguna dengan katalaluan
///
/// # Keselamatan
/// - Output: Terbuka (hanya Berjaya/Gagal, tiada data rahsia)
/// - Kesan: Baca (akses pangkalan data)
/// - Masa: Tetap (tiada kebocoran masa)
///
/// # Contoh
/// ```riina
/// biar hasil = sahkan("ahmad", rahsia("kata123"), &db);
/// padan hasil {
///     HasilSah::Berjaya(token) => guna_token(token),
///     HasilSah::Gagal(ralat) => kendali_ralat(ralat),
/// }
/// ```
awam fungsi sahkan(
    nama: Teks,
    katalaluan: Rahsia<Teks>,
    db: &PangkalanData,
) -> HasilSah
    kesan Baca
    tahap Terbuka
    masa_tetap
{
    // Cari pengguna dalam pangkalan data
    biar pengguna = padan db.cari_pengguna(&nama) {
        Ada(p) => p,
        Tiada => {
            // Masa tetap: kira hash walaupun pengguna tak wujud
            // Ini menghalang serangan penghitungan pengguna
            biar _ = sha256(katalaluan);
            pulang HasilSah::Gagal(RalatSah::TakSah);
        }
    };

    // Hash katalaluan input dengan garam tersimpan
    biar hash_input: Rahsia<Hash> = sha256(
        gabung_bait(katalaluan, pengguna.garam)
    );

    // Bandingkan dalam blok masa tetap
    biar sah: Benar = masa_tetap {
        sama_masa_tetap(hash_input, pengguna.hash_kata)
    };

    // Dedahkan keputusan (boolean sahaja, bukan data rahsia)
    biar keputusan = dedah(
        sah,
        dasar: "semak_kata",
        bukti: BuktiSemakan::jana(nama)
    );

    // Pulangkan hasil
    kalau keputusan {
        HasilSah::Berjaya(jana_token(pengguna.id))
    } lain {
        HasilSah::Gagal(RalatSah::TakSah)
    }
}

/// Daftar pengguna baru
awam fungsi daftar(
    nama: Teks,
    katalaluan: Rahsia<Teks>,
    db: &ubah PangkalanData,
) -> Hasil<Pengguna, RalatDaftar>
    kesan Tulis
    tahap Terbuka
{
    // Semak nama tak wujud
    kalau db.cari_pengguna(&nama).ialah_ada() {
        pulang Gagal(RalatDaftar::NamaWujud);
    }

    // Jana garam rawak
    biar garam = jana_garam(32);

    // Hash katalaluan dengan garam
    biar hash: Rahsia<Hash> = sha256(
        gabung_bait(katalaluan, &garam)
    );

    // Cipta pengguna baru
    biar pengguna = Pengguna {
        id: db.id_seterusnya(),
        nama: nama,
        hash_kata: hash,
        garam: garam,
    };

    // Simpan ke pangkalan data
    db.simpan_pengguna(&pengguna)?;

    Jadi(pengguna)
}

/// Fungsi utama
fungsi utama() {
    cetak_baris!("═══════════════════════════════════════");
    cetak_baris!("  RIINA - Sistem Pengesahan Selamat");
    cetak_baris!("═══════════════════════════════════════");
    cetak_baris!("");
    cetak_baris!("Semua operasi disahkan secara matematik.");
    cetak_baris!("Tiada serangan yang mungkin.");
    cetak_baris!("");

    // Simulasi penggunaan
    biar ubah db = PangkalanData::baru();

    // Daftar pengguna
    biar kata: Rahsia<Teks> = rahsia("KataLaluanKuat123!");
    padan daftar("ahmad", kata, &ubah db) {
        Jadi(p) => cetak_baris!("Pengguna {} berdaftar dengan ID {}", p.nama, p.id),
        Gagal(r) => cetak_baris!("Gagal daftar: {:?}", r),
    }

    // Sahkan pengguna
    biar kata_cuba: Rahsia<Teks> = rahsia("KataLaluanKuat123!");
    padan sahkan("ahmad", kata_cuba, &db) {
        HasilSah::Berjaya(token) => {
            cetak_baris!("Pengesahan berjaya!");
            cetak_baris!("Token sesi dijana.");
        }
        HasilSah::Gagal(ralat) => {
            cetak_baris!("Pengesahan gagal: {:?}", ralat);
        }
    }
}
```

---

## 11. COMPILER MESSAGES

All compiler messages are also in Bahasa Melayu:

```
ralat[R0001]: jenis tidak sepadan
 --> contoh.rii:15:5
  |
15|     biar x: Nombor = "teks";
  |                      ^^^^^^ dijangka `Nombor`, jumpa `Teks`
  |
  = bantuan: tukar kepada nombor dengan `parse()`

ralat[R0002]: pembolehubah tidak dijumpai
 --> contoh.rii:20:10
  |
20|     cetak(nama_pengguna);
  |           ^^^^^^^^^^^^^ tidak dijumpai dalam skop ini
  |
  = bantuan: adakah anda maksudkan `nama_pengguna`?

amaran[A0001]: pembolehubah tidak digunakan
 --> contoh.rii:10:9
  |
10|     biar x = 42;
  |         ^ pertimbangkan untuk menggunakan `_x` jika ini disengajakan

ralat[K0001]: kebocoran rahsia dikesan
 --> contoh.rii:25:5
  |
25|     cetak(katalaluan);
  |           ^^^^^^^^^^ tidak boleh mengeluarkan `Rahsia<Teks>` ke saluran awam
  |
  = nota: gunakan `dedah()` dengan dasar dan bukti untuk mendedahkan data rahsia
```

---

## 12. APPENDICES

### Appendix A: Reserved Words (Kata Simpanan)

All keywords listed in this document are reserved and cannot be used as identifiers.

### Appendix B: Operator Precedence (Keutamaan Operator)

| Precedence | Operator | Description |
|------------|----------|-------------|
| 1 (highest) | `()` `[]` `.` | Grouping, index, field |
| 2 | `bukan` `-` (unary) | Unary not, negation |
| 3 | `*` `/` `%` | Multiply, divide, modulo |
| 4 | `+` `-` | Add, subtract |
| 5 | `<<` `>>` | Bit shift |
| 6 | `&` | Bitwise AND |
| 7 | `^` | Bitwise XOR |
| 8 | `\|` | Bitwise OR |
| 9 | `==` `!=` `<` `>` `<=` `>=` | Comparison |
| 10 | `dan` | Logical AND |
| 11 | `atau` | Logical OR |
| 12 | `..` `..=` | Range |
| 13 (lowest) | `=` `+=` `-=` etc. | Assignment |

### Appendix C: Style Guide (Panduan Gaya)

```riina
// Nama fungsi: huruf_kecil_dengan_garis_bawah
fungsi hitung_jumlah() { }

// Nama jenis: HurufBesarCamelCase
bentuk PenggunaBaru { }

// Nama pemalar: HURUF_BESAR_DENGAN_GARIS_BAWAH
tetap SAIZ_MAKSIMUM: Nombor = 1024;

// Nama modul: huruf_kecil
modul pengesahan;

// Inden: 4 ruang
// Lebar baris maksimum: 100 aksara
```

---

## Document Hash

```
SHA-256: [To be computed after finalization]
```

---

**RIINA: Rigorous Immutable Invariant — Normalized Axiom**
