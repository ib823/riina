# DELEGATION PROMPT: RUST-001 BAHASA MELAYU LEXER IMPLEMENTATION

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: RUST-001-BAHASA-MELAYU-LEXER
CLASSIFICATION: RUST IMPLEMENTATION — LEXER MODULE
SECURITY LEVEL: CRITICAL — LANGUAGE CORE
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: Complete Rust module `keywords.rs` for Bahasa Melayu keyword support
REQUIREMENTS: Compiles with `cargo build`, passes `cargo clippy -- -D warnings`

You are implementing Bahasa Melayu (Malay language) keyword support for the RIINA
programming language lexer. RIINA uses Malaysian language keywords as its PRIMARY syntax.

RESEARCH REFERENCE: 01_RESEARCH/specs/bahasa/RIINA-BAHASA-MELAYU-SYNTAX_v1_0_0.md

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED BAHASA MELAYU KEYWORDS (Full List):
═══════════════════════════════════════════════════════════════════════════════════════════════════

| Bahasa Melayu | English Equivalent | Usage |
|---------------|-------------------|-------|
| fungsi | fn | Function declaration |
| biar | let | Variable binding |
| ubah | mut | Mutable modifier |
| tetap | const | Constant declaration |
| kalau | if | Conditional |
| lain | else | Alternative branch |
| untuk | for | For loop |
| selagi | while | While loop |
| ulang | loop | Infinite loop |
| pulang | return | Return statement |
| padan | match | Pattern matching |
| betul | true | Boolean true |
| salah | false | Boolean false |
| tiada | none | Option none |
| ada | some | Option some |
| diri | self | Self reference |
| struktur | struct | Structure definition |
| enum | enum | Enumeration (same) |
| ciri | trait | Trait definition |
| laksana | impl | Implementation block |
| modul | mod | Module declaration |
| guna | use | Use/import |
| awam | pub | Public visibility |
| rahsia | secret | Secret/private type (IFC) |
| dedah | declassify | Declassification |
| kesan | effect | Effect annotation |
| bersih | pure | Pure effect |
| jenis | type | Type alias |
| di_mana | where | Where clause |
| sebagai | as | Type casting |
| dalam | in | In keyword |
| rujuk | ref | Reference |
| pinjam | borrow | Borrow (explicit) |
| milik | own | Ownership |
| statik | static | Static lifetime |
| luaran | extern | External linkage |
| tidak_selamat | unsafe | Unsafe block |
| async | async | Async (same) |
| tunggu | await | Await |
| henti | break | Break loop |
| terus | continue | Continue loop |

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```rust
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
    /// Returns the Bahasa Melayu string representation
    pub fn as_str(&self) -> &'static str {
        // YOUR IMPLEMENTATION HERE
    }

    /// Returns the English equivalent
    pub fn english_equivalent(&self) -> &'static str {
        // YOUR IMPLEMENTATION HERE
    }

    /// Parse a string to a keyword (case-sensitive)
    pub fn from_str(s: &str) -> Option<Keyword> {
        // YOUR IMPLEMENTATION HERE
    }
}

/// Build keyword lookup table
pub fn keyword_map() -> HashMap<&'static str, Keyword> {
    // YOUR IMPLEMENTATION HERE
}

/// Check if a string is a reserved keyword
pub fn is_keyword(s: &str) -> bool {
    // YOUR IMPLEMENTATION HERE
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fungsi_keyword() {
        assert_eq!(Keyword::from_str("fungsi"), Some(Keyword::Fungsi));
        assert_eq!(Keyword::Fungsi.as_str(), "fungsi");
        assert_eq!(Keyword::Fungsi.english_equivalent(), "fn");
    }

    #[test]
    fn test_all_keywords_roundtrip() {
        // Every keyword should roundtrip through as_str/from_str
        // YOUR TEST HERE
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
}
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
CRITICAL REQUIREMENTS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. ALL 42 keywords must be implemented
2. Keywords are CASE-SENSITIVE (lowercase only)
3. English keywords (fn, let, if) are NOT recognized - only Bahasa Melayu
4. The `keyword_map()` function must be O(1) lookup using HashMap
5. All tests must pass

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use English keywords instead of Bahasa Melayu
2. DO NOT make keywords case-insensitive
3. DO NOT add keywords not in the specification
4. DO NOT use unsafe code
5. DO NOT use external dependencies beyond std
6. DO NOT output anything except the Rust file
7. DO NOT skip any keywords

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
# Place file at: riina-lexer/src/keywords.rs
cd /workspaces/proof/03_PROTO/crates/riina-lexer
cargo build
cargo test keywords
cargo clippy -- -D warnings
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Rust file. No markdown, no explanations, no commentary.
Start with `// keywords.rs` and end with the closing brace of the last test.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
