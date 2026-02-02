# RIINA Language Reference (AI-Optimized)

Version: 0.1.0 | File extension: `.rii` | Prover: Rocq 9.1 (Coq 8.21)

RIINA is a formally verified programming language with Bahasa Melayu (Malaysian Malay) keywords, information flow control, and an effect type system. All security properties are proven in Coq.

---

## 1. Keywords

### 1.1 Declarations

| Bahasa Melayu | English | Usage |
|---|---|---|
| `fungsi` | fn | Function declaration: `fungsi nama(x: Nombor) -> Nombor kesan Bersih { ... }` |
| `biar` | let | Binding: `biar x = 42;` |
| `ubah` | mut | Mutable: `biar ubah x = 0;` |
| `tetap` | const | Constant: `tetap MAX = 100;` |
| `statik` | static | Static variable |
| `bentuk` | struct | Structure: `bentuk Titik { x: Nombor, y: Nombor }` |
| `pilihan` | enum | Enumeration: `pilihan Warna { Merah, Biru }` |
| `jenis` | type | Type alias: `jenis Id = Nombor;` |
| `sifat` | trait | Trait: `sifat BolehCetak { ... }` |
| `laksana` | impl | Implementation: `laksana Pengguna { ... }` |
| `modul` | mod | Module: `modul pengesahan;` |
| `guna` | use | Import: `guna std::io;` |
| `awam` | pub | Public: `awam fungsi api() { }` |
| `luaran` | extern | FFI: `luaran "C" { ... }` |

### 1.2 Control Flow

| Bahasa Melayu | English | Usage |
|---|---|---|
| `kalau` | if | `kalau x > 0 { ... } lain { ... }` |
| `lain` | else | `lain { ... }` |
| `untuk` | for | `untuk i dalam 0..10 { }` |
| `selagi` | while | `selagi aktif { }` |
| `ulang` | loop | `ulang { ... keluar; }` |
| `keluar` | break | `keluar;` |
| `terus` | continue | `terus;` |
| `pulang` | return | `pulang hasil;` |
| `padan` | match | `padan nilai { 0 => "kosong", _ => "lain" }` |
| `pastikan` | guard | `pastikan x > 0 lain { pulang Gagal(...); }` |
| `dengan` | with | Used in handle: `kendali e dengan { ... }` |

### 1.3 Boolean and Logic

| Bahasa Melayu | English |
|---|---|
| `betul` | true |
| `salah` | false |
| `dan` / `&&` | and |
| `atau` / `\|\|` | or |
| `bukan` / `!` | not |
| `dalam` | in |
| `ialah` | is |
| `sebagai` | as |

### 1.4 Security Keywords

| Bahasa Melayu | English | Description |
|---|---|---|
| `rahsia` | secret | Secret type modifier |
| `terbuka` | public | Public security level |
| `sulit` | classify | Make data secret |
| `dedah` | declassify | Declassify with proof |
| `bukti` | prove | Proof term |
| `dasar` | policy | Security policy |
| `tahap` | level | Security level annotation |
| `bersih` | pure | No side effects |
| `selamat` | safe | Safety annotation |
| `bahaya` | unsafe | Unsafe block |

### 1.5 Effect Keywords

| Bahasa Melayu | English | Description |
|---|---|---|
| `kesan` | effect | Effect annotation on function |
| `laku` | perform | Perform effect |
| `kendali` | handle | Handle effect |
| `sambung` | resume | Resume from handler |
| `batal` | abort | Abort operation |

### 1.6 Constant-Time Keywords

| Bahasa Melayu | English |
|---|---|
| `masa_tetap` | constant-time block |
| `selamat_spekulasi` | speculation-safe |
| `gabungan` | combined CT+SS |
| `kosongkan` | zeroize |

### 1.7 Concurrency Keywords

| Bahasa Melayu | English |
|---|---|
| `sesi` | session |
| `saluran` | channel |
| `hantar` | send |
| `terima` | receive |
| `pilih` | select |
| `tamat` | end |
| `atom` | atomic |

### 1.8 Reference Keywords

| Bahasa Melayu | English |
|---|---|
| `ruj` | ref |
| `pinjam` | borrow |
| `pindah` | move |
| `salin` | copy |
| `klon` | clone |
| `diri` | self |
| `Diri` | Self |

---

## 2. Type System

### 2.1 Primitive Types

| Bahasa Melayu | English | Rust Equivalent |
|---|---|---|
| `Kosong` / `Unit` | Unit | `()` |
| `Benar` / `Bool` | Bool | `bool` |
| `Nombor` / `Int` | Int | `u64` |
| `Teks` / `String` | String | `String` |
| `Bait` / `Bytes` | Bytes | `Vec<u8>` |
| `Aksara` | Char | `char` |
| `Pecahan` | Float | `f64` |

### 2.2 Compound Types

| Syntax | Description |
|---|---|
| `(T1, T2)` | Product / tuple |
| `Sum<T1, T2>` | Sum type |
| `Senarai<T>` / `List<T>` | Dynamic list |
| `Mungkin<T>` / `Option<T>` | Optional value |
| `Fn(T1, T2)` / `Fn(T1, T2, Effect)` | Function type |

### 2.3 Security Types

| Syntax | Description |
|---|---|
| `Rahsia<T>` / `Secret<T>` | Classified data (cannot be printed/leaked) |
| `Berlabel<T, Level>` / `Labeled<T, Level>` | Security-labeled data |
| `Tercemar<T, Source>` / `Tainted<T, Source>` | Tainted (untrusted) data |
| `Disanitasi<T, Sanitizer>` / `Sanitized<T, Sanitizer>` | Sanitized data |
| `Bukti<T>` / `Proof<T>` | Declassification proof |
| `Keupayaan<Kind>` / `Capability<Kind>` | Capability token |
| `MasaTetap<T>` / `ConstantTime<T>` | Constant-time computation |
| `Sifar<T>` / `Zeroizing<T>` | Zeroized on drop |

### 2.4 Reference Types

| Syntax | Description |
|---|---|
| `Ruj<T>@Level` / `Ref<T>@Level` | Mutable reference at security level |

Security levels (lattice order): `Awam` (Public) < `Dalaman` (Internal) < `Sesi` (Session) < `Pengguna` (User) < `Sistem` (System) < `Rahsia` (Secret)

### 2.5 FFI Types

| Type | Description |
|---|---|
| `*T` | Raw pointer (FFI) |
| `CInt` | C int |
| `CChar` | C char |
| `CVoid` | C void |

### 2.6 Option and Result Variants

| Bahasa Melayu | English | Meaning |
|---|---|---|
| `Ada(x)` | Some(x) | Has value |
| `Tiada` | None | No value |
| `Jadi(x)` / `Ok(x)` | Ok(x) | Success |
| `Gagal(e)` / `Ralat(e)` | Err(e) | Failure |

---

## 3. Effects

Effects track observable behaviors. Declared with `kesan` after return type.

| Effect (BM) | Effect (EN) | Level | Category |
|---|---|---|---|
| `Bersih` | Pure | 0 | Pure |
| `Baca` | Read | 1 | IO |
| `Tulis` | Write | 2 | IO |
| `SistemFail` | FileSystem | 3 | IO |
| `Rangkaian` | Network | 4 | Network |
| `RangkaianSelamat` | NetworkSecure | 5 | Network |
| `Kripto` | Crypto | 6 | Crypto |
| `Rawak` | Random | 7 | Crypto |
| `Sistem` | System | 8 | System |
| `Masa` | Time | 9 | System |
| `Proses` | Process | 10 | System |
| `Panel` | Panel | 11 | Product |
| `Zirah` | Zirah | 12 | Product |
| `Benteng` | Benteng | 13 | Product |
| `Sandi` | Sandi | 14 | Product |
| `Menara` | Menara | 15 | Product |
| `Gapura` | Gapura | 16 | Product |

Multiple effects: `kesan (Tulis, Baca)`

Effect hierarchy: a function with `kesan Bersih` cannot call a function with `kesan Tulis`.

---

## 4. Expressions

### 4.1 Core Expression Forms

| Form | Syntax | Example |
|---|---|---|
| Unit | `()` | `()` |
| Boolean | `betul`, `salah` | `betul` |
| Integer | `42` | `42` |
| String | `"hello"` | `"Selamat pagi"` |
| Variable | `x` | `nama` |
| Lambda | `fungsi(x: T) -> T { body }` | `fungsi(x: Nombor) -> Nombor { x + 1 }` |
| Application | `f(x)` or `f(x, y)` | `tambah(1, 2)` |
| Pair | `(e1, e2)` | `(42, "jawapan")` |
| First | `fst e` | `fst pasangan` |
| Second | `snd e` | `snd pasangan` |
| If | `kalau c { t } lain { f }` | `kalau x > 0 { x } lain { 0 }` |
| Let | `biar x = e1; e2` | `biar x = 42; x + 1` |
| Let Rec | `fungsi f(...) { ... }` (top-level) | Recursive function binding |
| Match (sum) | `padan e { kiri x => ..., kanan y => ... }` | Sum type case analysis |
| Match (literal) | `padan e { 0 => ..., _ => ... }` | Literal pattern matching |
| Pipe | `e \|> f` | `5 \|> darab_dua \|> tambah_satu` |
| BinOp | `e1 op e2` | `x + y`, `a == b`, `p && q` |
| Assign | `e1 := e2` | `ruj := 42` |

### 4.2 Security Expressions

| Form | Syntax | Description |
|---|---|---|
| Classify | `sulit(e)` | Make value secret |
| Declassify | `dedah e dengan proof` | Declassify with proof |
| Prove | `bukti(e)` | Create proof term |
| Ref | `ruj e @Level` | Create reference at security level |
| Deref | `!e` | Dereference |

### 4.3 Effect Expressions

| Form | Syntax | Description |
|---|---|---|
| Perform | `laku Effect e` | Perform an effect |
| Handle | `kendali e dengan x => h` | Handle effects |
| Require | `perlu Effect e` | Require capability |
| Grant | `beri Effect e` | Grant capability |

### 4.4 Operators (Precedence high to low)

| Precedence | Operators |
|---|---|
| 1 | `()` `[]` `.` |
| 2 | `bukan` / `!` (unary) |
| 3 | `*` `/` `%` |
| 4 | `+` `-` |
| 5 | `==` `!=` `<` `>` `<=` `>=` |
| 6 | `&&` / `dan` |
| 7 | `\|\|` / `atau` |
| 8 | `:=` (assignment) |
| 9 | `\|>` (pipe) |

---

## 5. Declarations

### 5.1 Function Declaration

```
fungsi name(param1: Type1, param2: Type2) -> ReturnType kesan Effect {
    body
}
```

- `kesan` is optional (defaults to `Bersih`/Pure)
- `-> ReturnType` is optional (defaults to `Kosong`/Unit)
- `awam` prefix for public visibility
- Multi-param functions are curried internally

### 5.2 Top-Level Binding

```
biar name = expression;
```

### 5.3 Extern Block (FFI)

```
luaran "C" {
    fungsi puts(s: *CChar) -> CInt;
    fungsi strlen(s: *CChar) -> CInt;
}
```

### 5.4 Struct and Enum (parsed but skipped in current implementation)

```
bentuk Titik { x: Nombor, y: Nombor }
pilihan Arah { Utara, Selatan, Timur, Barat }
```

### 5.5 Module and Import (parsed but skipped)

```
modul pengesahan;
guna std::kripto;
```

---

## 6. Builtin Functions

### 6.1 I/O

| Bahasa Melayu | English | Signature | Effect |
|---|---|---|---|
| `cetak` | `print` | `Any -> ()` | System |
| `cetakln` | `println` | `Any -> ()` | System |

### 6.2 String

| Bahasa Melayu | English | Description |
|---|---|---|
| `gabung_teks` | `concat` | Concatenate two strings |
| `panjang` | `length` | String length |
| `ke_teks` | `to_string` | Convert to string |
| `teks_belah` | `str_split` | Split string |
| `teks_cantum` | `str_join` | Join strings |
| `teks_potong` | `str_trim` | Trim whitespace |
| `teks_mengandungi` | `str_contains` | Check substring |
| `teks_ganti` | `str_replace` | Replace in string |
| `teks_mula_dengan` | `str_starts_with` | Starts with prefix |
| `teks_akhir_dengan` | `str_ends_with` | Ends with suffix |
| `teks_huruf_besar` | `str_to_upper` | To uppercase |
| `teks_huruf_kecil` | `str_to_lower` | To lowercase |
| `teks_aksara_di` | `str_char_at` | Char at index |
| `teks_sub` | `str_substring` | Substring |
| `teks_indeks` | `str_index_of` | Index of substring |
| `teks_ulang` | `str_repeat` | Repeat string |
| `teks_pad_kiri` | `str_pad_left` | Pad left |
| `teks_pad_kanan` | `str_pad_right` | Pad right |
| `teks_baris` | `str_lines` | Split into lines |

### 6.3 Math

| Bahasa Melayu | English | Description |
|---|---|---|
| `mutlak` | `abs` | Absolute value |
| `minimum` | `min` | Minimum of two |
| `maksimum` | `max` | Maximum of two |
| `kuasa` | `pow` | Power |
| `punca` | `sqrt` | Square root |
| `baki` | `rem` | Remainder |
| `log2` | `log2` | Log base 2 |
| `gcd` | `gcd` | Greatest common divisor |
| `lcm` | `lcm` | Least common multiple |

### 6.4 Conversion

| Bahasa Melayu | English | Signature |
|---|---|---|
| `ke_nombor` | `parse_int` | `String -> Int` |
| `ke_teks` | `to_string` | `Any -> String` |
| `ke_bool` | `to_bool` | `Any -> Bool` |
| `nombor_ke_teks` | `int_to_string` | `Int -> String` |
| `bool_ke_nombor` | `bool_to_int` | `Bool -> Int` |

### 6.5 List

| Bahasa Melayu | English | Description |
|---|---|---|
| `senarai_baru` | `list_new` | Create empty list |
| `senarai_tolak` | `list_push` | Push element |
| `senarai_dapat` | `list_get` | Get by index |
| `senarai_panjang` | `list_len` | List length |
| `senarai_peta` | `list_map` | Map function over list |
| `senarai_tapis` | `list_filter` | Filter list |
| `senarai_lipat` | `list_fold` | Fold/reduce |
| `senarai_balik` | `list_reverse` | Reverse list |
| `senarai_susun` | `list_sort` | Sort list |
| `senarai_mengandungi` | `list_contains` | Check membership |
| `senarai_sambung` | `list_concat` | Concatenate lists |
| `senarai_kepala` | `list_head` | First element |
| `senarai_ekor` | `list_tail` | All but first |
| `senarai_zip` | `list_zip` | Zip two lists |
| `senarai_nombor` | `list_enumerate` | Enumerate with index |
| `senarai_rata` | `list_flatten` | Flatten nested |
| `senarai_unik` | `list_unique` | Remove duplicates |
| `senarai_potong` | `list_slice` | Slice |

### 6.6 Map

| Bahasa Melayu | English | Description |
|---|---|---|
| `peta_baru` | `map_new` | Create empty map |
| `peta_letak` | `map_insert` | Insert key-value |
| `peta_dapat` | `map_get` | Get by key |
| `peta_buang` | `map_remove` | Remove key |
| `peta_kunci` | `map_keys` | Get all keys |
| `peta_nilai` | `map_values` | Get all values |
| `peta_mengandungi` | `map_contains` | Check key exists |
| `peta_panjang` | `map_len` | Map size |

### 6.7 Set

| Bahasa Melayu | English | Description |
|---|---|---|
| `set_baru` | `set_new` | Create empty set |
| `set_letak` | `set_insert` | Insert element |
| `set_buang` | `set_remove` | Remove element |
| `set_mengandungi` | `set_contains` | Check membership |
| `set_kesatuan` | `set_union` | Union |
| `set_persilangan` | `set_intersect` | Intersection |
| `set_panjang` | `set_len` | Set size |

### 6.8 File I/O (Effect: FileSystem)

| Bahasa Melayu | English | Description |
|---|---|---|
| `fail_baca` | `file_read` | Read file |
| `fail_tulis` | `file_write` | Write file |
| `fail_tambah` | `file_append` | Append to file |
| `fail_ada` | `file_exists` | Check file exists |
| `fail_buang` | `file_delete` | Delete file |
| `fail_panjang` | `file_size` | File size |
| `fail_senarai` | `file_list_dir` | List directory |
| `fail_baca_baris` | `file_read_lines` | Read lines |

### 6.9 Time (Effect: Time)

| Bahasa Melayu | English | Description |
|---|---|---|
| `masa_sekarang` | `time_now` | Current time |
| `masa_sekarang_ms` | `time_now_ms` | Current time (ms) |
| `masa_format` | `time_format` | Format time |
| `masa_urai` | `time_parse` | Parse time string |
| `masa_tidur` | `time_sleep` | Sleep |
| `masa_jam` | `time_clock` | Clock value |

### 6.10 JSON

| Bahasa Melayu | English | Description |
|---|---|---|
| `json_urai` | `json_parse` | Parse JSON |
| `json_ke_teks` | `json_stringify` | JSON to string |
| `json_dapat` | `json_get` | Get JSON field |
| `json_letak` | `json_set` | Set JSON field |
| `json_ada` | `json_has` | Check field exists |

### 6.11 Assert

| Bahasa Melayu | English | Description |
|---|---|---|
| `tegaskan` | `assert` | Assert boolean |
| `tegaskan_betul` | `assert_true` | Assert true |
| `tegaskan_salah` | `assert_false` | Assert false |
| `tegaskan_sama` | `assert_eq` | Assert equal |
| `tegaskan_beza` | `assert_ne` | Assert not equal |

### 6.12 Random (Effect: Random)

| Bahasa Melayu | English |
|---|---|
| `rawak` | `random` |

---

## 7. Taint Sources and Sanitizers

### 7.1 Taint Sources

`NetworkExternal`, `NetworkInternal`, `UserInput`, `FileSystem`, `Database`, `Environment`, `GapuraRequest`, `ZirahEvent`, `ZirahEndpoint`, `BentengBiometric`, `SandiSignature`, `MenaraDevice`

### 7.2 Sanitizers

**Web:** `HtmlEscape`, `UrlEncode`, `JsEscape`, `CssEscape`
**SQL:** `SqlEscape`, `SqlParam`
**Injection:** `XssFilter`, `PathTraversal`, `CommandEscape`, `LdapEscape`, `XmlEscape`
**Validation:** `JsonValidation`, `XmlValidation`, `EmailValidation`, `PhoneValidation`
**Crypto:** `HashVerify`, `SignatureVerify`, `MacVerify`
**Product:** `GapuraAuth`, `ZirahSession`, `BentengBiometric`, `SandiDecrypt`, `MenaraAttestation`

---

## 8. Capability Kinds

`FileRead`, `FileWrite`, `FileExecute`, `FileDelete`, `NetConnect`, `NetListen`, `NetBind`, `ProcSpawn`, `ProcSignal`, `SysTime`, `SysRandom`, `SysEnv`, `RootProduct`, `ProductAccess`

---

## 9. Session Types

```
sesi Protocol {
    hantar T1;    // Send
    terima T2;    // Receive
    tamat;        // End
}
```

Session type constructors: `End`, `Send(T, S)`, `Recv(T, S)`, `Select(S1, S2)`, `Branch(S1, S2)`, `Rec(x, S)`, `Var(x)`

---

## 10. Code Examples

### 10.1 Hello World

```riina
fungsi utama() -> Nombor kesan Tulis {
    cetak("Selamat pagi, dunia!");
    pulang 0;
}
```

### 10.2 Functions and Arithmetic

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

### 10.3 Variables and Let Bindings

```riina
fungsi utama() -> Nombor kesan Tulis {
    biar nama = "Ahmad";
    biar umur = 25;
    biar aktif = betul;
    cetak(nama);
    pulang 0;
}
```

### 10.4 Conditionals

```riina
fungsi max(a: Nombor, b: Nombor) -> Nombor kesan Bersih {
    kalau a > b { a } lain { b }
}
```

### 10.5 Pattern Matching (Literals)

```riina
fungsi periksa(x: Nombor) -> Teks kesan Bersih {
    padan x {
        0 => "kosong",
        1 => "satu",
        _ => "lain",
    }
}
```

### 10.6 Recursion

```riina
fungsi faktorial(n: Nombor) -> Nombor kesan Bersih {
    kalau n == 0 {
        1
    } lain {
        n * faktorial(n - 1)
    }
}
```

### 10.7 Higher-Order Functions and Pipe

```riina
fungsi darab_dua(x: Nombor) -> Nombor kesan Bersih {
    x * 2
}

fungsi tambah_satu(x: Nombor) -> Nombor kesan Bersih {
    x + 1
}

fungsi utama() -> Nombor kesan Tulis {
    biar hasil = 5 |> darab_dua |> tambah_satu;
    cetak(hasil);
    pulang 0;
}
```

### 10.8 Closures

```riina
fungsi buat_pengganda(faktor: Nombor) -> Fn(Nombor) -> Nombor kesan Bersih {
    fungsi darab(x: Nombor) -> Nombor {
        x * faktor
    }
    pulang darab;
}
```

### 10.9 Secret Types

```riina
fungsi proses_kata_laluan(kata: Rahsia<Teks>) -> Benar kesan Kripto {
    biar hash = sha256(kata);
    // cetak(kata);  // COMPILE ERROR: cannot output Rahsia<Teks>
    betul
}
```

### 10.10 Declassification with Proof

```riina
fungsi semak_kata(
    input: Rahsia<Teks>,
    hash_simpan: Teks
) -> Benar kesan Bersih {
    biar hash_input = sha256(input);
    dedah(
        sama_masa_tetap(hash_input, hash_simpan),
        dasar: "semak_katalaluan",
        bukti: BuktiPengesahan::baru()
    )
}
```

### 10.11 Effects

```riina
fungsi tulen(x: Nombor) -> Nombor kesan Bersih {
    x * 2
}

fungsi baca_fail(laluan: Teks) -> Teks kesan Baca {
    fail_baca(laluan)
}

fungsi tulis_log(mesej: Teks) -> () kesan Tulis {
    cetak(mesej);
}
```

### 10.12 FFI (C Interop)

```riina
luaran "C" {
    fungsi puts(s: *CChar) -> CInt;
}

fungsi utama() -> CInt kesan Sistem {
    puts("Selamat datang ke RIINA FFI!")
}
```

### 10.13 For Loop

```riina
fungsi utama() -> Nombor kesan Tulis {
    untuk i dalam [1, 2, 3, 4, 5] {
        cetak(i);
    }
    pulang 0;
}
```

### 10.14 Guard Clause

```riina
fungsi bahagi(x: Nombor, y: Nombor) -> Nombor kesan Bersih {
    pastikan y != 0 lain { pulang 0; };
    x / y
}
```

### 10.15 Pairs and Tuples

```riina
fungsi utama() -> Nombor kesan Tulis {
    biar pasangan = (42, "jawapan");
    biar pertama = fst pasangan;
    biar kedua = snd pasangan;
    cetak(pertama);
    pulang 0;
}
```

---

## 11. Common Patterns

### 11.1 Entry Point

Every program has `fungsi utama()` as entry point.

### 11.2 Effect Annotation

Always declare effects: `kesan Bersih` for pure, `kesan Tulis` for output, etc. Multiple: `kesan (Tulis, Baca)`.

### 11.3 Secret Data Flow

1. Classify: `biar kunci = Rahsia("data");` or `sulit(data)`
2. Operate: operations on secrets produce secrets
3. Declassify: `dedah(secret, bukti: "justification")` only when needed

### 11.4 Error Handling

Use `Hasil<T, E>` (Result) with `Ok(v)` / `Ralat(e)` and pattern match.

### 11.5 Functional Composition

Use `|>` pipe operator for left-to-right data flow.

---

## 12. Error Patterns and Fixes

### 12.1 Leaking Secrets

```riina
// ERROR: Cannot output Rahsia<Teks> to public channel
cetak(katalaluan);  // COMPILE ERROR

// FIX: Use dedah with proof
biar nilai = dedah(katalaluan, bukti: "audit_sah");
cetak(nilai);
```

### 12.2 Effect Mismatch

```riina
// ERROR: Function declared Bersih but calls Tulis function
fungsi tulen() -> Nombor kesan Bersih {
    cetak("hello");  // COMPILE ERROR: effect Tulis not allowed
}

// FIX: Declare correct effect
fungsi tulen() -> Nombor kesan Tulis {
    cetak("hello");
    42
}
```

### 12.3 Missing Semicolons

```riina
// ERROR: Statements in sequence need semicolons
biar x = 1
biar y = 2  // Parse error

// FIX: Add semicolons
biar x = 1;
biar y = 2;
```

### 12.4 Missing Else Branch

```riina
// ERROR: if-else must have both branches
kalau x > 0 { x }  // Parse error

// FIX: Add else branch
kalau x > 0 { x } lain { 0 }
```

### 12.5 Wrong Match Arrow

```riina
// In parser: use => (fat arrow) for match arms
padan x {
    0 => "kosong",
    _ => "lain",
}
```

---

## 13. Style Guide

- Function names: `huruf_kecil_dengan_garis_bawah` (snake_case)
- Type names: `HurufBesarCamelCase` (PascalCase)
- Constants: `HURUF_BESAR` (SCREAMING_SNAKE)
- Indent: 4 spaces
- Max line width: 100 characters
- Always use Bahasa Melayu keywords
- File extension: `.rii`

---

## 14. Compiler Usage

```bash
# Compile
riinac compile program.rii

# Run
riinac run program.rii

# Type check only
riinac check program.rii

# REPL
riinac repl

# Target WASM
riinac compile --target=wasm32 program.rii

# Verify (formal verification gate)
riinac verify --full
```

---

## 15. Formal Verification

All security properties proven in Coq (Rocq 9.1):
- **Type safety**: Progress + Preservation
- **Non-interference**: Secret data cannot influence public output
- **Effect safety**: Effects tracked and enforced
- **Information flow control**: Multi-level security lattice

Proofs: 4,885 Qed (active build), 0 admits, 4 justified axioms.
