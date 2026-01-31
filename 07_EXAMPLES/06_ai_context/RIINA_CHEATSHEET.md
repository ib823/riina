# RIINA Cheatsheet

## Keywords (Bahasa Melayu → English)

| BM | EN | Usage |
|---|---|---|
| `fungsi` | fn | `fungsi tambah(x: Nombor) -> Nombor { x + 1 }` |
| `biar` | let | `biar nama = "Ahmad";` |
| `ubah` | mut | `biar ubah kiraan = 0;` |
| `tetap` | const | `tetap MAX = 100;` |
| `kalau` | if | `kalau x > 0 { ... } lain { ... }` |
| `lain` | else | see above |
| `untuk` | for | `untuk item dalam senarai { ... }` |
| `dalam` | in | see above |
| `selagi` | while | `selagi x > 0 { ... }` |
| `ulang` | loop | `ulang { ... }` |
| `pulang` | return | `pulang hasil;` |
| `padan` | match | `padan x { 0 => "kosong", _ => "lain" }` |
| `betul` | true | boolean true |
| `salah` | false | boolean false |

## Security Keywords

| BM | EN | Usage |
|---|---|---|
| `rahsia` | secret | `biar k: Rahsia<Teks>` |
| `sulit` | classify | `sulit nilai` |
| `dedah` | declassify | `dedah nilai dengan bukti_val` |
| `bukti` | prove | `bukti syarat` |
| `terbuka` | public | public visibility |

## Effect Keywords

| BM | EN | Usage |
|---|---|---|
| `kesan` | effect | `fungsi f() -> Teks kesan Tulis { ... }` |
| `laku` | perform | `laku Tulis cetak("hello")` |
| `kendali` | handle | `kendali expr dengan x => handler` |
| `bersih` | pure | no effects |

## Types

| BM | EN | Description |
|---|---|---|
| `Nombor` | Int | Integer |
| `Benar` | Bool | Boolean |
| `Teks` | String | Text |
| `Bait` | Bytes | Byte array |
| `Senarai<T>` | List | List |
| `Mungkin<T>` | Option | Optional value |
| `Rahsia<T>` | Secret | Classified data |
| `Ruj<T>@L` | Ref | Reference at security level |
| `Berlabel<T,L>` | Labeled | Security-labeled value |
| `Tercemar<T,S>` | Tainted | Tainted data |
| `Bukti<T>` | Proof | Proof value |
| `Keupayaan<K>` | Capability | Access capability |
| `MasaTetap<T>` | ConstantTime | Constant-time type |

## Effects

| BM | EN | Domain |
|---|---|---|
| `Bersih` | Pure | No side effects |
| `Baca` | Read | Memory read |
| `Tulis` | Write | Memory write |
| `SistemFail` | FileSystem | File I/O |
| `Rangkaian` | Network | Network I/O |
| `Kripto` | Crypto | Cryptographic ops |
| `Rawak` | Random | RNG |
| `Masa` | Time | Clock access |
| `Proses` | Process | Process management |

## Security Levels (ascending)

`Awam` < `Dalaman` < `Sesi` < `Pengguna` < `Sistem` < `Rahsia`

## Operators

| Operator | Description |
|---|---|
| `\|>` | Pipe |
| `+` `-` `*` `/` `%` | Arithmetic |
| `==` `!=` `<` `>` `<=` `>=` | Comparison |
| `&&` `\|\|` | Logical |
| `:=` | Assign to ref |
| `->` | Return type |
| `=>` | Match arm |

## Example

```riina
/// Kira jumlah senarai nombor
fungsi jumlah(senarai: Senarai<Nombor>) -> Nombor {
    biar ubah hasil = 0;
    untuk n dalam senarai {
        hasil = hasil + n;
    };
    pulang hasil;
}

/// Fungsi utama
fungsi utama() -> () kesan Tulis {
    biar nombor = [1, 2, 3, 4, 5];
    biar total = jumlah(nombor);
    laku Tulis cetak(ke_teks(total));
}
```
