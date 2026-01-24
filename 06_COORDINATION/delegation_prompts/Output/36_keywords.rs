// keywords.rs - Bahasa Melayu Keywords for RIINA
// Spec: 01_RESEARCH/specs/bahasa/RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md

use std::collections::HashMap;

/// RIINA keywords in Bahasa Melayu
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Keyword {
    // Function and binding
    Fungsi,     // fn
    Biar,       // let
    Ubah,       // mut
    Tetap,      // const

    // Control flow
    Kalau,      // if
    Lain,       // else
    Untuk,      // for
    Selagi,     // while
    Ulang,      // loop
    Pulang,     // return
    Padan,      // match
    Henti,      // break
    Terus,      // continue

    // Literals
    Betul,      // true
    Salah,      // false
    Tiada,      // none
    Ada,        // some

    // OOP/Type system
    Diri,       // self
    Struktur,   // struct
    Enum,       // enum
    Ciri,       // trait
    Laksana,    // impl
    Jenis,      // type
    DiMana,     // where
    Sebagai,    // as

    // Modules
    Modul,      // mod
    Guna,       // use
    Awam,       // pub
    Luaran,     // extern

    // Memory & Safety
    Rujuk,      // ref
    Pinjam,     // borrow
    Milik,      // own
    Statik,     // static
    TidakSelamat, // unsafe

    // IFC (Information Flow Control)
    Rahsia,     // secret
    Dedah,      // declassify

    // Effects
    Kesan,      // effect
    Bersih,     // pure

    // Async
    Async,      // async
    Tunggu,     // await

    // Other
    Dalam,      // in
}

impl Keyword {
    /// Returns all keyword variants
    pub const fn all() -> &'static [Keyword] {
        &[
            Keyword::Fungsi,
            Keyword::Biar,
            Keyword::Ubah,
            Keyword::Tetap,
            Keyword::Kalau,
            Keyword::Lain,
            Keyword::Untuk,
            Keyword::Selagi,
            Keyword::Ulang,
            Keyword::Pulang,
            Keyword::Padan,
            Keyword::Henti,
            Keyword::Terus,
            Keyword::Betul,
            Keyword::Salah,
            Keyword::Tiada,
            Keyword::Ada,
            Keyword::Diri,
            Keyword::Struktur,
            Keyword::Enum,
            Keyword::Ciri,
            Keyword::Laksana,
            Keyword::Jenis,
            Keyword::DiMana,
            Keyword::Sebagai,
            Keyword::Modul,
            Keyword::Guna,
            Keyword::Awam,
            Keyword::Luaran,
            Keyword::Rujuk,
            Keyword::Pinjam,
            Keyword::Milik,
            Keyword::Statik,
            Keyword::TidakSelamat,
            Keyword::Rahsia,
            Keyword::Dedah,
            Keyword::Kesan,
            Keyword::Bersih,
            Keyword::Async,
            Keyword::Tunggu,
            Keyword::Dalam,
        ]
    }

    /// Returns the Bahasa Melayu string representation
    pub fn as_str(&self) -> &'static str {
        match self {
            Keyword::Fungsi => "fungsi",
            Keyword::Biar => "biar",
            Keyword::Ubah => "ubah",
            Keyword::Tetap => "tetap",
            Keyword::Kalau => "kalau",
            Keyword::Lain => "lain",
            Keyword::Untuk => "untuk",
            Keyword::Selagi => "selagi",
            Keyword::Ulang => "ulang",
            Keyword::Pulang => "pulang",
            Keyword::Padan => "padan",
            Keyword::Henti => "henti",
            Keyword::Terus => "terus",
            Keyword::Betul => "betul",
            Keyword::Salah => "salah",
            Keyword::Tiada => "tiada",
            Keyword::Ada => "ada",
            Keyword::Diri => "diri",
            Keyword::Struktur => "struktur",
            Keyword::Enum => "enum",
            Keyword::Ciri => "ciri",
            Keyword::Laksana => "laksana",
            Keyword::Jenis => "jenis",
            Keyword::DiMana => "di_mana",
            Keyword::Sebagai => "sebagai",
            Keyword::Modul => "modul",
            Keyword::Guna => "guna",
            Keyword::Awam => "awam",
            Keyword::Luaran => "luaran",
            Keyword::Rujuk => "rujuk",
            Keyword::Pinjam => "pinjam",
            Keyword::Milik => "milik",
            Keyword::Statik => "statik",
            Keyword::TidakSelamat => "tidak_selamat",
            Keyword::Rahsia => "rahsia",
            Keyword::Dedah => "dedah",
            Keyword::Kesan => "kesan",
            Keyword::Bersih => "bersih",
            Keyword::Async => "async",
            Keyword::Tunggu => "tunggu",
            Keyword::Dalam => "dalam",
        }
    }

    /// Returns the English equivalent
    pub fn english_equivalent(&self) -> &'static str {
        match self {
            Keyword::Fungsi => "fn",
            Keyword::Biar => "let",
            Keyword::Ubah => "mut",
            Keyword::Tetap => "const",
            Keyword::Kalau => "if",
            Keyword::Lain => "else",
            Keyword::Untuk => "for",
            Keyword::Selagi => "while",
            Keyword::Ulang => "loop",
            Keyword::Pulang => "return",
            Keyword::Padan => "match",
            Keyword::Henti => "break",
            Keyword::Terus => "continue",
            Keyword::Betul => "true",
            Keyword::Salah => "false",
            Keyword::Tiada => "none",
            Keyword::Ada => "some",
            Keyword::Diri => "self",
            Keyword::Struktur => "struct",
            Keyword::Enum => "enum",
            Keyword::Ciri => "trait",
            Keyword::Laksana => "impl",
            Keyword::Jenis => "type",
            Keyword::DiMana => "where",
            Keyword::Sebagai => "as",
            Keyword::Modul => "mod",
            Keyword::Guna => "use",
            Keyword::Awam => "pub",
            Keyword::Luaran => "extern",
            Keyword::Rujuk => "ref",
            Keyword::Pinjam => "borrow",
            Keyword::Milik => "own",
            Keyword::Statik => "static",
            Keyword::TidakSelamat => "unsafe",
            Keyword::Rahsia => "secret",
            Keyword::Dedah => "declassify",
            Keyword::Kesan => "effect",
            Keyword::Bersih => "pure",
            Keyword::Async => "async",
            Keyword::Tunggu => "await",
            Keyword::Dalam => "in",
        }
    }

    /// Parse a string to a keyword (case-sensitive)
    /// Wrapper around FromStr implementation for convenience
    pub fn parse(s: &str) -> Option<Keyword> {
        s.parse().ok()
    }
}

/// Error type for keyword parsing
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseKeywordError;

impl std::fmt::Display for ParseKeywordError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid keyword")
    }
}

impl std::error::Error for ParseKeywordError {}

impl std::str::FromStr for Keyword {
    type Err = ParseKeywordError;

    fn from_str(s: &str) -> Result<Keyword, Self::Err> {
        match s {
            "fungsi" => Ok(Keyword::Fungsi),
            "biar" => Ok(Keyword::Biar),
            "ubah" => Ok(Keyword::Ubah),
            "tetap" => Ok(Keyword::Tetap),
            "kalau" => Ok(Keyword::Kalau),
            "lain" => Ok(Keyword::Lain),
            "untuk" => Ok(Keyword::Untuk),
            "selagi" => Ok(Keyword::Selagi),
            "ulang" => Ok(Keyword::Ulang),
            "pulang" => Ok(Keyword::Pulang),
            "padan" => Ok(Keyword::Padan),
            "henti" => Ok(Keyword::Henti),
            "terus" => Ok(Keyword::Terus),
            "betul" => Ok(Keyword::Betul),
            "salah" => Ok(Keyword::Salah),
            "tiada" => Ok(Keyword::Tiada),
            "ada" => Ok(Keyword::Ada),
            "diri" => Ok(Keyword::Diri),
            "struktur" => Ok(Keyword::Struktur),
            "enum" => Ok(Keyword::Enum),
            "ciri" => Ok(Keyword::Ciri),
            "laksana" => Ok(Keyword::Laksana),
            "jenis" => Ok(Keyword::Jenis),
            "di_mana" => Ok(Keyword::DiMana),
            "sebagai" => Ok(Keyword::Sebagai),
            "modul" => Ok(Keyword::Modul),
            "guna" => Ok(Keyword::Guna),
            "awam" => Ok(Keyword::Awam),
            "luaran" => Ok(Keyword::Luaran),
            "rujuk" => Ok(Keyword::Rujuk),
            "pinjam" => Ok(Keyword::Pinjam),
            "milik" => Ok(Keyword::Milik),
            "statik" => Ok(Keyword::Statik),
            "tidak_selamat" => Ok(Keyword::TidakSelamat),
            "rahsia" => Ok(Keyword::Rahsia),
            "dedah" => Ok(Keyword::Dedah),
            "kesan" => Ok(Keyword::Kesan),
            "bersih" => Ok(Keyword::Bersih),
            "async" => Ok(Keyword::Async),
            "tunggu" => Ok(Keyword::Tunggu),
            "dalam" => Ok(Keyword::Dalam),
            _ => Err(ParseKeywordError),
        }
    }
}

/// Build keyword lookup table
pub fn keyword_map() -> HashMap<&'static str, Keyword> {
    let mut map = HashMap::with_capacity(41);
    for &kw in Keyword::all() {
        map.insert(kw.as_str(), kw);
    }
    map
}

/// Check if a string is a reserved keyword
pub fn is_keyword(s: &str) -> bool {
    s.parse::<Keyword>().is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fungsi_keyword() {
        assert_eq!(Keyword::parse("fungsi"), Some(Keyword::Fungsi));
        assert_eq!(Keyword::Fungsi.as_str(), "fungsi");
        assert_eq!(Keyword::Fungsi.english_equivalent(), "fn");
    }

    #[test]
    fn test_all_keywords_roundtrip() {
        for &kw in Keyword::all() {
            let s = kw.as_str();
            let parsed = Keyword::parse(s);
            assert_eq!(parsed, Some(kw), "Roundtrip failed for {:?}", kw);
        }
    }

    #[test]
    fn test_is_keyword() {
        assert!(is_keyword("fungsi"));
        assert!(is_keyword("biar"));
        assert!(is_keyword("kalau"));
        assert!(!is_keyword("foobar"));
        assert!(!is_keyword("fn"));  // English NOT a keyword
    }

    #[test]
    fn test_case_sensitivity() {
        assert!(is_keyword("fungsi"));
        assert!(!is_keyword("Fungsi"));  // Case sensitive
        assert!(!is_keyword("FUNGSI"));
    }

    #[test]
    fn test_keyword_map_contains_all() {
        let map = keyword_map();
        assert_eq!(map.len(), 41);
        for &kw in Keyword::all() {
            assert!(map.contains_key(kw.as_str()));
            assert_eq!(map.get(kw.as_str()), Some(&kw));
        }
    }

    #[test]
    fn test_english_not_recognized() {
        assert!(!is_keyword("fn"));
        assert!(!is_keyword("let"));
        assert!(!is_keyword("if"));
        assert!(!is_keyword("else"));
        assert!(!is_keyword("while"));
        assert!(!is_keyword("for"));
        assert!(!is_keyword("return"));
        assert!(!is_keyword("match"));
        assert!(!is_keyword("true"));
        assert!(!is_keyword("false"));
        assert!(!is_keyword("struct"));
        assert!(!is_keyword("trait"));
        assert!(!is_keyword("impl"));
        assert!(!is_keyword("mod"));
        assert!(!is_keyword("use"));
        assert!(!is_keyword("pub"));
        assert!(!is_keyword("const"));
        assert!(!is_keyword("mut"));
        assert!(!is_keyword("ref"));
        assert!(!is_keyword("unsafe"));
        assert!(!is_keyword("await"));
        assert!(!is_keyword("break"));
        assert!(!is_keyword("continue"));
    }

    #[test]
    fn test_all_control_flow_keywords() {
        assert_eq!(Keyword::parse("kalau"), Some(Keyword::Kalau));
        assert_eq!(Keyword::Kalau.english_equivalent(), "if");

        assert_eq!(Keyword::parse("lain"), Some(Keyword::Lain));
        assert_eq!(Keyword::Lain.english_equivalent(), "else");

        assert_eq!(Keyword::parse("untuk"), Some(Keyword::Untuk));
        assert_eq!(Keyword::Untuk.english_equivalent(), "for");

        assert_eq!(Keyword::parse("selagi"), Some(Keyword::Selagi));
        assert_eq!(Keyword::Selagi.english_equivalent(), "while");

        assert_eq!(Keyword::parse("ulang"), Some(Keyword::Ulang));
        assert_eq!(Keyword::Ulang.english_equivalent(), "loop");

        assert_eq!(Keyword::parse("pulang"), Some(Keyword::Pulang));
        assert_eq!(Keyword::Pulang.english_equivalent(), "return");

        assert_eq!(Keyword::parse("padan"), Some(Keyword::Padan));
        assert_eq!(Keyword::Padan.english_equivalent(), "match");

        assert_eq!(Keyword::parse("henti"), Some(Keyword::Henti));
        assert_eq!(Keyword::Henti.english_equivalent(), "break");

        assert_eq!(Keyword::parse("terus"), Some(Keyword::Terus));
        assert_eq!(Keyword::Terus.english_equivalent(), "continue");
    }

    #[test]
    fn test_all_binding_keywords() {
        assert_eq!(Keyword::parse("biar"), Some(Keyword::Biar));
        assert_eq!(Keyword::Biar.english_equivalent(), "let");

        assert_eq!(Keyword::parse("ubah"), Some(Keyword::Ubah));
        assert_eq!(Keyword::Ubah.english_equivalent(), "mut");

        assert_eq!(Keyword::parse("tetap"), Some(Keyword::Tetap));
        assert_eq!(Keyword::Tetap.english_equivalent(), "const");
    }

    #[test]
    fn test_all_literal_keywords() {
        assert_eq!(Keyword::parse("betul"), Some(Keyword::Betul));
        assert_eq!(Keyword::Betul.english_equivalent(), "true");

        assert_eq!(Keyword::parse("salah"), Some(Keyword::Salah));
        assert_eq!(Keyword::Salah.english_equivalent(), "false");

        assert_eq!(Keyword::parse("tiada"), Some(Keyword::Tiada));
        assert_eq!(Keyword::Tiada.english_equivalent(), "none");

        assert_eq!(Keyword::parse("ada"), Some(Keyword::Ada));
        assert_eq!(Keyword::Ada.english_equivalent(), "some");
    }

    #[test]
    fn test_all_type_system_keywords() {
        assert_eq!(Keyword::parse("diri"), Some(Keyword::Diri));
        assert_eq!(Keyword::Diri.english_equivalent(), "self");

        assert_eq!(Keyword::parse("struktur"), Some(Keyword::Struktur));
        assert_eq!(Keyword::Struktur.english_equivalent(), "struct");

        assert_eq!(Keyword::parse("enum"), Some(Keyword::Enum));
        assert_eq!(Keyword::Enum.english_equivalent(), "enum");

        assert_eq!(Keyword::parse("ciri"), Some(Keyword::Ciri));
        assert_eq!(Keyword::Ciri.english_equivalent(), "trait");

        assert_eq!(Keyword::parse("laksana"), Some(Keyword::Laksana));
        assert_eq!(Keyword::Laksana.english_equivalent(), "impl");

        assert_eq!(Keyword::parse("jenis"), Some(Keyword::Jenis));
        assert_eq!(Keyword::Jenis.english_equivalent(), "type");

        assert_eq!(Keyword::parse("di_mana"), Some(Keyword::DiMana));
        assert_eq!(Keyword::DiMana.english_equivalent(), "where");

        assert_eq!(Keyword::parse("sebagai"), Some(Keyword::Sebagai));
        assert_eq!(Keyword::Sebagai.english_equivalent(), "as");
    }

    #[test]
    fn test_all_module_keywords() {
        assert_eq!(Keyword::parse("modul"), Some(Keyword::Modul));
        assert_eq!(Keyword::Modul.english_equivalent(), "mod");

        assert_eq!(Keyword::parse("guna"), Some(Keyword::Guna));
        assert_eq!(Keyword::Guna.english_equivalent(), "use");

        assert_eq!(Keyword::parse("awam"), Some(Keyword::Awam));
        assert_eq!(Keyword::Awam.english_equivalent(), "pub");

        assert_eq!(Keyword::parse("luaran"), Some(Keyword::Luaran));
        assert_eq!(Keyword::Luaran.english_equivalent(), "extern");
    }

    #[test]
    fn test_all_memory_keywords() {
        assert_eq!(Keyword::parse("rujuk"), Some(Keyword::Rujuk));
        assert_eq!(Keyword::Rujuk.english_equivalent(), "ref");

        assert_eq!(Keyword::parse("pinjam"), Some(Keyword::Pinjam));
        assert_eq!(Keyword::Pinjam.english_equivalent(), "borrow");

        assert_eq!(Keyword::parse("milik"), Some(Keyword::Milik));
        assert_eq!(Keyword::Milik.english_equivalent(), "own");

        assert_eq!(Keyword::parse("statik"), Some(Keyword::Statik));
        assert_eq!(Keyword::Statik.english_equivalent(), "static");

        assert_eq!(Keyword::parse("tidak_selamat"), Some(Keyword::TidakSelamat));
        assert_eq!(Keyword::TidakSelamat.english_equivalent(), "unsafe");
    }

    #[test]
    fn test_all_ifc_keywords() {
        assert_eq!(Keyword::parse("rahsia"), Some(Keyword::Rahsia));
        assert_eq!(Keyword::Rahsia.english_equivalent(), "secret");

        assert_eq!(Keyword::parse("dedah"), Some(Keyword::Dedah));
        assert_eq!(Keyword::Dedah.english_equivalent(), "declassify");
    }

    #[test]
    fn test_all_effect_keywords() {
        assert_eq!(Keyword::parse("kesan"), Some(Keyword::Kesan));
        assert_eq!(Keyword::Kesan.english_equivalent(), "effect");

        assert_eq!(Keyword::parse("bersih"), Some(Keyword::Bersih));
        assert_eq!(Keyword::Bersih.english_equivalent(), "pure");
    }

    #[test]
    fn test_all_async_keywords() {
        assert_eq!(Keyword::parse("async"), Some(Keyword::Async));
        assert_eq!(Keyword::Async.english_equivalent(), "async");

        assert_eq!(Keyword::parse("tunggu"), Some(Keyword::Tunggu));
        assert_eq!(Keyword::Tunggu.english_equivalent(), "await");
    }

    #[test]
    fn test_dalam_keyword() {
        assert_eq!(Keyword::parse("dalam"), Some(Keyword::Dalam));
        assert_eq!(Keyword::Dalam.english_equivalent(), "in");
    }

    #[test]
    fn test_keyword_count() {
        assert_eq!(Keyword::all().len(), 41);
    }

    #[test]
    fn test_underscore_keywords() {
        // Keywords with underscores
        assert!(is_keyword("di_mana"));
        assert!(is_keyword("tidak_selamat"));

        // Without underscore should NOT match
        assert!(!is_keyword("dimana"));
        assert!(!is_keyword("tidakselamat"));
    }
}
