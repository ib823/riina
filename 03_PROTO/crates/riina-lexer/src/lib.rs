//! RIINA Lexer
//!
//! Tokenizes RIINA source code.
//! RIINA = Rigorous Immutable Integrity No-attack Assured
//!
//! Reference: RIINA-LANG-LEXER-SPEC_v1_0_0.md
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

#![forbid(unsafe_code)]
#![deny(clippy::unwrap_used, clippy::expect_used)]
#![warn(clippy::pedantic)]

mod token;
mod lexer;
mod error;

pub use token::{Token, TokenKind, Span};
pub use lexer::Lexer;
pub use error::LexError;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_keywords() {
        let input = "fn let mut effect secret";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFn);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwLet);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMut);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwEffect);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSecret);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_keywords() {
        let input = "fungsi biar ubah kesan rahsia";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFn);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwLet);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMut);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwEffect);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSecret);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_control_flow() {
        let input = "kalau lain untuk selagi ulang pulang";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwIf);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwElse);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFor);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwWhile);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwLoop);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwReturn);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_boolean_literals() {
        let input = "betul salah";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LiteralBool(true));
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LiteralBool(false));
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_effect_keywords() {
        let input = "laku kendali sambung batal";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwPerform);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwHandle);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwResume);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAbort);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_security_keywords() {
        let input = "dedah bukti sulit terbuka";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwDeclassify);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwProve);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwClassify);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwPublic);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_type_keywords() {
        let input = "bentuk pilihan jenis sifat laksana";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwStruct);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwEnum);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwType);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwTrait);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwImpl);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_concurrency_keywords() {
        let input = "sesi hantar terima atom pagar";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSession);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSend);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRecv);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAtomic);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFence);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_literals() {
        let input = "123 42.5 true 'a' \"hello\"";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "123"),
            _ => panic!("Expected Int"),
        }
        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralFloat(s, _) => assert_eq!(s, "42.5"),
            _ => panic!("Expected Float"),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LiteralBool(true));
        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralChar(c) => assert_eq!(c, 'a'),
            _ => panic!("Expected Char"),
        }
        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralString(s) => assert_eq!(s, "hello"),
            _ => panic!("Expected String"),
        }
    }

    #[test]
    fn test_operators() {
        let input = "+ - * / == != < > <= >=";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Plus);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Minus);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Star);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Slash);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::EqEq);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Ne);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Lt);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Gt);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Le);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Ge);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_delimiters() {
        let input = "( ) [ ] { } , ; :";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LParen);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RParen);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LBracket);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RBracket);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LBrace);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RBrace);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Comma);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Semi);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Colon);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_comments() {
        let input = "// line comment\nfn /* block */ let";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFn);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwLet);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    // =========================================================================
    // COMPREHENSIVE OPERATOR TESTS
    // Rationale: Every operator must be verified individually to ensure correct
    // tokenization. Operators form the backbone of expression parsing.
    // =========================================================================

    #[test]
    fn test_bitwise_operators() {
        // Input: bitwise AND, OR, XOR, NOT
        // Expected: Each produces its respective token
        // Rationale: Bitwise ops critical for low-level security operations
        let input = "& | ^ !";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::And,
            "Bitwise AND '&' must tokenize to TokenKind::And");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Or,
            "Bitwise OR '|' must tokenize to TokenKind::Or");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Caret,
            "Bitwise XOR '^' must tokenize to TokenKind::Caret");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Not,
            "Logical NOT '!' must tokenize to TokenKind::Not");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_percent_operator() {
        // Input: modulo operator
        // Expected: TokenKind::Percent
        // Rationale: Modulo essential for cryptographic operations
        let input = "%";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Percent,
            "Modulo '%' must tokenize to TokenKind::Percent");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_shift_operators() {
        // Input: left shift, right shift
        // Expected: TokenKind::Shl, TokenKind::Shr
        // Rationale: Shift operations critical for bit manipulation in crypto
        let input = "<< >>";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Shl,
            "Left shift '<<' must tokenize to TokenKind::Shl");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Shr,
            "Right shift '>>' must tokenize to TokenKind::Shr");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_logical_operators() {
        // Input: logical AND, logical OR
        // Expected: TokenKind::AndAnd, TokenKind::OrOr
        // Rationale: Logical operators for control flow
        let input = "&& ||";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::AndAnd,
            "Logical AND '&&' must tokenize to TokenKind::AndAnd");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::OrOr,
            "Logical OR '||' must tokenize to TokenKind::OrOr");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_assignment_operators_arithmetic() {
        // Input: +=, -=, *=, /=, %=
        // Expected: Compound assignment tokens
        // Rationale: Compound assignment must be distinguished from simple operators
        let input = "+= -= *= /= %=";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::PlusEq,
            "'+=' must tokenize to TokenKind::PlusEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::MinusEq,
            "'-=' must tokenize to TokenKind::MinusEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::StarEq,
            "'*=' must tokenize to TokenKind::StarEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::SlashEq,
            "'/=' must tokenize to TokenKind::SlashEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::PercentEq,
            "'%=' must tokenize to TokenKind::PercentEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_assignment_operators_bitwise() {
        // Input: &=, |=, ^=, <<=, >>=
        // Expected: Bitwise compound assignment tokens
        // Rationale: Bitwise assignments used in low-level bit manipulation
        let input = "&= |= ^= <<= >>=";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::AndEq,
            "'&=' must tokenize to TokenKind::AndEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::OrEq,
            "'|=' must tokenize to TokenKind::OrEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::CaretEq,
            "'^=' must tokenize to TokenKind::CaretEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::ShlEq,
            "'<<=' must tokenize to TokenKind::ShlEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::ShrEq,
            "'>>=' must tokenize to TokenKind::ShrEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_arrow_operators() {
        // Input: ->, =>
        // Expected: Arrow and fat arrow tokens
        // Rationale: Arrows used for return types and pattern matching
        let input = "-> =>";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Arrow,
            "'->' must tokenize to TokenKind::Arrow");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::FatArrow,
            "'=>' must tokenize to TokenKind::FatArrow");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_simple_equals() {
        // Input: single equals (assignment)
        // Expected: TokenKind::Eq
        // Rationale: Must distinguish from == (equality)
        let input = "=";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eq,
            "'=' must tokenize to TokenKind::Eq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    // =========================================================================
    // COMPREHENSIVE DELIMITER TESTS
    // Rationale: Delimiters define structure; must be tokenized precisely
    // =========================================================================

    #[test]
    fn test_dot_operators() {
        // Input: ., .., ..=
        // Expected: Dot, DotDot, DotDotEq
        // Rationale: Range operators critical for iteration bounds
        let input = ". .. ..=";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Dot,
            "'.' must tokenize to TokenKind::Dot");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::DotDot,
            "'..' must tokenize to TokenKind::DotDot");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::DotDotEq,
            "'..=' must tokenize to TokenKind::DotDotEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_colon_variants() {
        // Input: :, ::, :=
        // Expected: Colon, ColonColon, ColonEq
        // Rationale: Colons used for type annotations and paths
        let input = ": :: :=";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Colon,
            "':' must tokenize to TokenKind::Colon");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::ColonColon,
            "'::' must tokenize to TokenKind::ColonColon");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::ColonEq,
            "':=' must tokenize to TokenKind::ColonEq");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_special_punctuation() {
        // Input: ?, @, #, $
        // Expected: Question, At, Hash, Dollar
        // Rationale: Special chars for error handling, attributes, macros
        let input = "? @ # $";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Question,
            "'?' must tokenize to TokenKind::Question");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::At,
            "'@' must tokenize to TokenKind::At");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Hash,
            "'#' must tokenize to TokenKind::Hash");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Dollar,
            "'$' must tokenize to TokenKind::Dollar");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    // =========================================================================
    // COMPREHENSIVE ENGLISH KEYWORD TESTS
    // Rationale: All 70+ keywords must be verified for correctness
    // =========================================================================

    #[test]
    fn test_english_declaration_keywords() {
        // Input: Declaration keywords in English
        // Expected: Respective keyword tokens
        // Rationale: Core of variable/type declarations
        let input = "const static type struct enum union trait impl where";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwConst,
            "'const' must tokenize to TokenKind::KwConst");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwStatic,
            "'static' must tokenize to TokenKind::KwStatic");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwType,
            "'type' must tokenize to TokenKind::KwType");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwStruct,
            "'struct' must tokenize to TokenKind::KwStruct");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwEnum,
            "'enum' must tokenize to TokenKind::KwEnum");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwUnion,
            "'union' must tokenize to TokenKind::KwUnion");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwTrait,
            "'trait' must tokenize to TokenKind::KwTrait");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwImpl,
            "'impl' must tokenize to TokenKind::KwImpl");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwWhere,
            "'where' must tokenize to TokenKind::KwWhere");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_module_keywords() {
        // Input: Module system keywords
        // Expected: Mod, Pub, Use, Extern
        // Rationale: Module system fundamental to code organization
        let input = "mod pub use extern";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMod,
            "'mod' must tokenize to TokenKind::KwMod");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwPub,
            "'pub' must tokenize to TokenKind::KwPub");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwUse,
            "'use' must tokenize to TokenKind::KwUse");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwExtern,
            "'extern' must tokenize to TokenKind::KwExtern");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_control_flow_keywords() {
        // Input: Control flow keywords
        // Expected: Respective control tokens
        // Rationale: Control flow determines program execution path
        let input = "if else for match loop while with break continue return";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwIf);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwElse);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFor);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMatch);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwLoop);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwWhile);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwWith);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwBreak);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwContinue);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwReturn);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_reference_keywords() {
        // Input: Reference and casting keywords
        // Expected: As, Ref, Move
        // Rationale: Memory safety through explicit references
        let input = "as ref move";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAs,
            "'as' must tokenize to TokenKind::KwAs");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRef,
            "'ref' must tokenize to TokenKind::KwRef");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMove,
            "'move' must tokenize to TokenKind::KwMove");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_self_keywords() {
        // Input: Self reference keywords
        // Expected: SelfValue, SelfType, Super, Crate
        // Rationale: Self-referential types and module paths
        let input = "self Self super crate";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSelfValue,
            "'self' must tokenize to TokenKind::KwSelfValue");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSelfType,
            "'Self' must tokenize to TokenKind::KwSelfType");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSuper,
            "'super' must tokenize to TokenKind::KwSuper");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwCrate,
            "'crate' must tokenize to TokenKind::KwCrate");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_async_keywords() {
        // Input: Async/await keywords
        // Expected: KwAsync, KwAwait
        // Rationale: Async programming support
        let input = "async await";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAsync,
            "'async' must tokenize to TokenKind::KwAsync");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAwait,
            "'await' must tokenize to TokenKind::KwAwait");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_unsafe_keyword() {
        // Input: unsafe keyword
        // Expected: KwUnsafe
        // Rationale: Explicit marking of unsafe operations
        let input = "unsafe";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwUnsafe,
            "'unsafe' must tokenize to TokenKind::KwUnsafe");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_effect_keywords() {
        // Input: Effect system keywords
        // Expected: Effect, Perform, Handle, Resume, Abort
        // Rationale: Algebraic effects core to RIINA
        let input = "effect perform handle resume abort";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwEffect);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwPerform);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwHandle);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwResume);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAbort);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_security_keywords() {
        // Input: Security type keywords
        // Expected: Secret, Classify, Public, Tainted, Declassify, Prove, Sanitize
        // Rationale: Information flow security is core to RIINA
        let input = "secret classify public tainted declassify prove sanitize";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSecret);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwClassify);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwPublic);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwTainted);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwDeclassify);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwProve);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSanitize);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_sum_type_keywords() {
        // Input: Sum type constructors
        // Expected: KwInl, KwInr
        // Rationale: Sum types for type-safe unions
        let input = "inl inr";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwInl,
            "'inl' must tokenize to TokenKind::KwInl");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwInr,
            "'inr' must tokenize to TokenKind::KwInr");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_session_keywords() {
        // Input: Session type keywords
        // Expected: Session, Send, Recv, Select, Branch, End
        // Rationale: Session types for protocol verification
        let input = "session send recv select branch end";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSession);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSend);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRecv);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSelect);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwBranch);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwEnd);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_capability_keywords() {
        // Input: Capability keywords
        // Expected: KwCapability, KwRevoke
        // Rationale: Capability-based security
        let input = "capability revoke";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwCapability,
            "'capability' must tokenize to TokenKind::KwCapability");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRevoke,
            "'revoke' must tokenize to TokenKind::KwRevoke");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_memory_ordering_keywords() {
        // Input: Memory ordering keywords
        // Expected: Atomic, Fence, Acquire, Release, SeqCst, Relaxed, AcqRel
        // Rationale: Memory ordering critical for concurrent safety
        let input = "atomic fence acquire release seqcst relaxed acqrel";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAtomic);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFence);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAcquire);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRelease);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSeqCst);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRelaxed);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAcqRel);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_product_keyword() {
        // Input: product keyword
        // Expected: KwProduct
        // Rationale: Product types
        let input = "product";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwProduct,
            "'product' must tokenize to TokenKind::KwProduct");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_english_constant_time_keywords() {
        // Input: Constant-time security keywords
        // Expected: Ct, SpeculationSafe, Combined, Zeroize
        // Rationale: Constant-time critical for crypto security
        let input = "ct speculation_safe combined zeroize";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwCt,
            "'ct' must tokenize to TokenKind::KwCt");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSpeculationSafe,
            "'speculation_safe' must tokenize to TokenKind::KwSpeculationSafe");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwCombined,
            "'combined' must tokenize to TokenKind::KwCombined");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwZeroize,
            "'zeroize' must tokenize to TokenKind::KwZeroize");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    // =========================================================================
    // COMPREHENSIVE BAHASA MELAYU KEYWORD TESTS (REMAINING)
    // Rationale: Full bilingual support is core RIINA requirement
    // =========================================================================

    #[test]
    fn test_bahasa_melayu_declaration_keywords() {
        // Input: Declaration keywords in Bahasa Melayu
        // Expected: Same tokens as English equivalents
        // Rationale: Bahasa Melayu syntax must be fully supported
        let input = "tetap statik modul awam guna luaran";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwConst,
            "'tetap' (const) must tokenize to TokenKind::KwConst");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwStatic,
            "'statik' (static) must tokenize to TokenKind::KwStatic");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMod,
            "'modul' (mod) must tokenize to TokenKind::KwMod");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwPub,
            "'awam' (pub) must tokenize to TokenKind::KwPub");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwUse,
            "'guna' (use) must tokenize to TokenKind::KwUse");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwExtern,
            "'luaran' (extern) must tokenize to TokenKind::KwExtern");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_control_flow_extended() {
        // Input: Additional control flow in Bahasa Melayu
        // Expected: Match, With, Break, Continue tokens
        // Rationale: Complete control flow in native language
        let input = "padan dengan keluar terus";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMatch,
            "'padan' (match) must tokenize to TokenKind::KwMatch");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwWith,
            "'dengan' (with) must tokenize to TokenKind::KwWith");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwBreak,
            "'keluar' (break) must tokenize to TokenKind::KwBreak");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwContinue,
            "'terus' (continue) must tokenize to TokenKind::KwContinue");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_reference_keywords() {
        // Input: Reference keywords in Bahasa Melayu
        // Expected: As, Ref, Move tokens
        // Rationale: Memory management in native language
        let input = "sebagai ruj pindah";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAs,
            "'sebagai' (as) must tokenize to TokenKind::KwAs");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRef,
            "'ruj' (ref) must tokenize to TokenKind::KwRef");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwMove,
            "'pindah' (move) must tokenize to TokenKind::KwMove");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_self_keywords() {
        // Input: Self references in Bahasa Melayu
        // Expected: SelfValue, SelfType, Crate tokens
        // Rationale: Self-referential types in native language
        let input = "diri Diri peti";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSelfValue,
            "'diri' (self) must tokenize to TokenKind::KwSelfValue");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSelfType,
            "'Diri' (Self) must tokenize to TokenKind::KwSelfType");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwCrate,
            "'peti' (crate) must tokenize to TokenKind::KwCrate");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_unsafe_keyword() {
        // Input: unsafe in Bahasa Melayu
        // Expected: KwUnsafe
        // Rationale: Safety marking in native language
        let input = "bahaya";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwUnsafe,
            "'bahaya' (unsafe) must tokenize to TokenKind::KwUnsafe");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_session_keywords() {
        // Input: Session keywords in Bahasa Melayu
        // Expected: Select, Branch, End tokens
        // Rationale: Protocol types in native language
        let input = "pilih cabang tamat";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSelect,
            "'pilih' (select) must tokenize to TokenKind::KwSelect");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwBranch,
            "'cabang' (branch) must tokenize to TokenKind::KwBranch");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwEnd,
            "'tamat' (end) must tokenize to TokenKind::KwEnd");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_memory_ordering_keywords() {
        // Input: Memory ordering in Bahasa Melayu
        // Expected: Acquire, Release tokens
        // Rationale: Concurrent safety in native language
        let input = "peroleh lepas";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwAcquire,
            "'peroleh' (acquire) must tokenize to TokenKind::KwAcquire");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwRelease,
            "'lepas' (release) must tokenize to TokenKind::KwRelease");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_bahasa_melayu_constant_time_keywords() {
        // Input: Constant-time keywords in Bahasa Melayu
        // Expected: Ct, SpeculationSafe, Combined, Zeroize tokens
        // Rationale: Crypto security in native language
        let input = "masa_tetap selamat_spekulasi gabungan kosongkan";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwCt,
            "'masa_tetap' (ct) must tokenize to TokenKind::KwCt");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwSpeculationSafe,
            "'selamat_spekulasi' (speculation_safe) must tokenize to TokenKind::KwSpeculationSafe");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwCombined,
            "'gabungan' (combined) must tokenize to TokenKind::KwCombined");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwZeroize,
            "'kosongkan' (zeroize) must tokenize to TokenKind::KwZeroize");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    // =========================================================================
    // LITERAL EDGE CASE TESTS
    // Rationale: Literals must handle all valid forms without error
    // =========================================================================

    #[test]
    fn test_hex_literal() {
        // Input: Hexadecimal integer literal
        // Expected: LiteralInt with "0xABCDEF" value
        // Rationale: Hex literals common in low-level/crypto code
        let input = "0xABCDEF";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "0xABCDEF",
                "Hex literal must preserve original representation"),
            other => panic!("Expected LiteralInt, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_octal_literal() {
        // Input: Octal integer literal
        // Expected: LiteralInt with "0o755" value
        // Rationale: Octal literals for permissions, etc.
        let input = "0o755";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "0o755",
                "Octal literal must preserve original representation"),
            other => panic!("Expected LiteralInt, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_binary_literal() {
        // Input: Binary integer literal
        // Expected: LiteralInt with "0b1010" value
        // Rationale: Binary literals for bit manipulation
        let input = "0b1010";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "0b1010",
                "Binary literal must preserve original representation"),
            other => panic!("Expected LiteralInt, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_integer_with_underscores() {
        // Input: Integer with visual separators
        // Expected: LiteralInt with underscores preserved
        // Rationale: Readability for large numbers
        let input = "1_000_000";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "1_000_000",
                "Underscores in integers must be preserved"),
            other => panic!("Expected LiteralInt, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_float_with_underscores() {
        // Input: Float with visual separators
        // Expected: LiteralFloat with underscores preserved
        // Rationale: Readability for precise floats
        let input = "3.141_592";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralFloat(s, _) => assert_eq!(s, "3.141_592",
                "Underscores in floats must be preserved"),
            other => panic!("Expected LiteralFloat, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_zero_literal() {
        // Input: Zero
        // Expected: LiteralInt("0")
        // Rationale: Zero is a valid literal
        let input = "0";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "0",
                "Zero must be a valid integer literal"),
            other => panic!("Expected LiteralInt, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_empty_string_literal() {
        // Input: Empty string
        // Expected: LiteralString("")
        // Rationale: Empty strings are valid
        let input = "\"\"";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralString(s) => assert_eq!(s, "",
                "Empty string must be valid"),
            other => panic!("Expected LiteralString, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_string_with_escapes() {
        // Input: String with various escape sequences
        // Expected: LiteralString with escape sequences interpreted
        // Rationale: Escape sequences must be processed
        let input = r#""hello\nworld\t!""#;
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralString(s) => assert_eq!(s, "hello\nworld\t!",
                "Escape sequences must be interpreted"),
            other => panic!("Expected LiteralString, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_string_with_escaped_quote() {
        // Input: String with escaped quote
        // Expected: LiteralString with quote preserved
        // Rationale: Escaped quotes must not terminate string
        let input = r#""say \"hello\"""#;
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralString(s) => assert_eq!(s, "say \"hello\"",
                "Escaped quotes must be preserved in string"),
            other => panic!("Expected LiteralString, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_string_with_escaped_backslash() {
        // Input: String with escaped backslash
        // Expected: LiteralString with single backslash
        // Rationale: Backslash escaping must work
        let input = r#""path\\to\\file""#;
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralString(s) => assert_eq!(s, "path\\to\\file",
                "Escaped backslashes must produce single backslash"),
            other => panic!("Expected LiteralString, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_char_escape_sequences() {
        // Input: Character literals with various escapes
        // Expected: LiteralChar with interpreted values
        // Rationale: All escape sequences must work in chars
        let inputs = [
            (r"'\n'", '\n', "newline"),
            (r"'\r'", '\r', "carriage return"),
            (r"'\t'", '\t', "tab"),
            (r"'\0'", '\0', "null"),
            (r"'\\'", '\\', "backslash"),
            (r"'\''", '\'', "single quote"),
        ];

        for (input, expected, name) in inputs {
            let mut lexer = Lexer::new(input);
            match lexer.next_token().unwrap().kind {
                TokenKind::LiteralChar(c) => assert_eq!(c, expected,
                    "Char escape for {} must produce {:?}", name, expected),
                other => panic!("Expected LiteralChar for {}, got {:?}", name, other),
            }
        }
    }

    #[test]
    fn test_lifetime_simple() {
        // Input: Simple lifetime
        // Expected: Lifetime("a")
        // Rationale: Lifetimes critical for memory safety
        let input = "'a";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Lifetime(s) => assert_eq!(s, "a",
                "Simple lifetime must be recognized"),
            other => panic!("Expected Lifetime, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_lifetime_static() {
        // Input: 'static lifetime
        // Expected: Lifetime("static")
        // Rationale: 'static is special but still a lifetime
        let input = "'static";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Lifetime(s) => assert_eq!(s, "static",
                "'static must be recognized as lifetime"),
            other => panic!("Expected Lifetime, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_lifetime_with_underscore() {
        // Input: Lifetime with underscore
        // Expected: Lifetime("_anon")
        // Rationale: Anonymous lifetimes use underscore
        let input = "'_anon";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Lifetime(s) => assert_eq!(s, "_anon",
                "Lifetime with underscore must be recognized"),
            other => panic!("Expected Lifetime, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    // =========================================================================
    // ERROR CASE TESTS
    // Rationale: Lexer must produce meaningful errors for invalid input
    // =========================================================================

    #[test]
    fn test_unterminated_string_error() {
        // Input: String without closing quote
        // Expected: LexError::UnterminatedString
        // Rationale: Must detect and report unterminated strings
        let input = "\"hello";
        let mut lexer = Lexer::new(input);

        let result = lexer.next_token();
        assert!(result.is_err(), "Unterminated string must produce error");
        match result {
            Err(LexError::UnterminatedString(_)) => {}
            other => panic!("Expected UnterminatedString, got {:?}", other),
        }
    }

    #[test]
    fn test_unterminated_char_error() {
        // Input: Char without closing quote
        // Expected: LexError::UnterminatedChar
        // Rationale: Must detect and report unterminated chars
        // Note: 'a is interpreted as lifetime, so we test with space char
        let input = "' ";
        let mut lexer = Lexer::new(input);

        let result = lexer.next_token();
        // Space char followed by no closing quote should be error
        assert!(result.is_err(), "Unterminated char must produce error");
    }

    #[test]
    fn test_invalid_escape_sequence_error() {
        // Input: Invalid escape sequence in char
        // Expected: LexError::InvalidEscapeSequence
        // Rationale: Must detect invalid escapes
        let input = r"'\z'";
        let mut lexer = Lexer::new(input);

        let result = lexer.next_token();
        assert!(result.is_err(), "Invalid escape must produce error");
        match result {
            Err(LexError::InvalidEscapeSequence(_)) => {}
            other => panic!("Expected InvalidEscapeSequence, got {:?}", other),
        }
    }

    #[test]
    fn test_unexpected_char_error() {
        // Input: Character not valid in RIINA
        // Expected: LexError::UnexpectedChar
        // Rationale: Must reject invalid characters
        let input = "~";
        let mut lexer = Lexer::new(input);

        let result = lexer.next_token();
        assert!(result.is_err(), "Unexpected char must produce error");
        match result {
            Err(LexError::UnexpectedChar(c, _)) => assert_eq!(c, '~'),
            other => panic!("Expected UnexpectedChar, got {:?}", other),
        }
    }

    #[test]
    fn test_unexpected_backtick_error() {
        // Input: Backtick (not valid in RIINA)
        // Expected: LexError::UnexpectedChar
        // Rationale: Backticks not part of RIINA syntax
        let input = "`";
        let mut lexer = Lexer::new(input);

        let result = lexer.next_token();
        assert!(result.is_err(), "Backtick must produce error");
        match result {
            Err(LexError::UnexpectedChar(c, _)) => assert_eq!(c, '`'),
            other => panic!("Expected UnexpectedChar, got {:?}", other),
        }
    }

    // =========================================================================
    // EDGE CASE TESTS
    // Rationale: Boundary conditions must be handled correctly
    // =========================================================================

    #[test]
    fn test_empty_input() {
        // Input: Empty string
        // Expected: Immediate Eof
        // Rationale: Empty input is valid, produces Eof
        let input = "";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof,
            "Empty input must produce Eof immediately");
    }

    #[test]
    fn test_whitespace_only() {
        // Input: Only whitespace
        // Expected: Eof
        // Rationale: Whitespace-only input produces Eof
        let input = "   \t\n\r  ";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof,
            "Whitespace-only input must produce Eof");
    }

    #[test]
    fn test_consecutive_operators() {
        // Input: Operators without whitespace
        // Expected: Each tokenized separately where possible
        // Rationale: Maximal munch should apply
        let input = "+-*/";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Plus);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Minus);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Star);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Slash);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_identifier_followed_by_operator() {
        // Input: Identifier immediately followed by operator
        // Expected: Identifier then operator
        // Rationale: Boundary between identifier and operator
        let input = "foo+bar";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "foo"),
            other => panic!("Expected Identifier 'foo', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Plus);
        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "bar"),
            other => panic!("Expected Identifier 'bar', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_number_followed_by_dot() {
        // Input: Number followed by single dot (field access, not float)
        // Expected: Int, Dot
        // Rationale: Distinguish float from int.field
        let input = "42.foo";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "42"),
            other => panic!("Expected LiteralInt '42', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Dot);
        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "foo"),
            other => panic!("Expected Identifier 'foo', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_number_followed_by_range() {
        // Input: Number followed by range operator
        // Expected: Int, DotDot
        // Rationale: Range syntax: 1..10
        let input = "1..10";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "1"),
            other => panic!("Expected LiteralInt '1', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::DotDot);
        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "10"),
            other => panic!("Expected LiteralInt '10', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_nested_block_comments() {
        // Input: Nested block comments
        // Expected: Comments skipped, tokens extracted
        // Rationale: Nested comments must balance
        let input = "fn /* outer /* inner */ still outer */ let";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFn,
            "Token before nested comment must be parsed");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwLet,
            "Token after nested comment must be parsed");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_comment_at_end_of_file() {
        // Input: Token followed by line comment at EOF
        // Expected: Token, Eof
        // Rationale: Comment at EOF must be handled
        let input = "fn // this is a comment";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFn);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_unicode_identifier() {
        // Input: Identifier with unicode characters (Chinese)
        // Expected: Identifier with unicode preserved
        // Rationale: Unicode identifiers for internationalization
        // Note: Using Chinese characters which don't have combining marks
        let input = "变量";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "变量",
                "Unicode identifier must be preserved"),
            other => panic!("Expected Identifier, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_unicode_identifier_malay() {
        // Input: Malay identifier
        // Expected: Identifier preserved
        // Rationale: Native Malaysian names must work
        let input = "pendapatan";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "pendapatan",
                "Malay identifier must be preserved"),
            other => panic!("Expected Identifier, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_unicode_string() {
        // Input: String with unicode content
        // Expected: LiteralString with unicode
        // Rationale: Unicode in strings must be preserved
        let input = "\"مرحبا بالعالم\"";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralString(s) => assert_eq!(s, "مرحبا بالعالم",
                "Unicode in string must be preserved"),
            other => panic!("Expected LiteralString, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_span_tracking_simple() {
        // Input: Simple token
        // Expected: Correct span
        // Rationale: Spans critical for error reporting
        let input = "fn";
        let mut lexer = Lexer::new(input);

        let token = lexer.next_token().unwrap();
        assert_eq!(token.kind, TokenKind::KwFn);
        assert_eq!(token.span.start, 0, "Span start must be 0");
        assert_eq!(token.span.end, 2, "Span end must be 2 for 'fn'");
    }

    #[test]
    fn test_span_tracking_with_whitespace() {
        // Input: Token preceded by whitespace
        // Expected: Span starts after whitespace
        // Rationale: Whitespace not included in token span
        let input = "  fn";
        let mut lexer = Lexer::new(input);

        let token = lexer.next_token().unwrap();
        assert_eq!(token.kind, TokenKind::KwFn);
        assert_eq!(token.span.start, 2, "Span must start after whitespace");
        assert_eq!(token.span.end, 4, "Span end must account for whitespace offset");
    }

    #[test]
    fn test_span_tracking_unicode() {
        // Input: Unicode identifier
        // Expected: Span accounts for UTF-8 byte length
        // Rationale: Spans are byte offsets, not char offsets
        let input = "日本語";
        let mut lexer = Lexer::new(input);

        let token = lexer.next_token().unwrap();
        match token.kind {
            TokenKind::Identifier(s) => assert_eq!(s, "日本語"),
            other => panic!("Expected Identifier, got {:?}", other),
        }
        assert_eq!(token.span.start, 0);
        // 日本語 is 9 bytes in UTF-8 (3 chars × 3 bytes each)
        assert_eq!(token.span.end, 9, "Span must account for UTF-8 byte length");
    }

    #[test]
    fn test_very_long_identifier() {
        // Input: Very long identifier
        // Expected: Identifier preserved
        // Rationale: No arbitrary length limits
        let long_name = "a".repeat(1000);
        let mut lexer = Lexer::new(&long_name);

        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, long_name,
                "Long identifier must be preserved"),
            other => panic!("Expected Identifier, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_very_long_string() {
        // Input: Very long string
        // Expected: LiteralString preserved
        // Rationale: No arbitrary length limits on strings
        let long_content = "x".repeat(10000);
        let input = format!("\"{}\"", long_content);
        let mut lexer = Lexer::new(&input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralString(s) => assert_eq!(s, long_content,
                "Long string must be preserved"),
            other => panic!("Expected LiteralString, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_identifier_starting_with_underscore() {
        // Input: Identifier starting with underscore
        // Expected: Valid identifier
        // Rationale: Underscore-prefixed identifiers for unused vars
        let input = "_unused";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "_unused",
                "Underscore-prefixed identifier must be valid"),
            other => panic!("Expected Identifier, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_identifier_with_numbers() {
        // Input: Identifier with numbers
        // Expected: Valid identifier
        // Rationale: Numbers allowed after first char
        let input = "var123";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "var123",
                "Identifier with numbers must be valid"),
            other => panic!("Expected Identifier, got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_multiple_tokens_per_line() {
        // Input: Multiple tokens on one line
        // Expected: All tokens extracted correctly
        // Rationale: Basic multi-token parsing
        let input = "fn main() { return 42; }";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwFn);
        match lexer.next_token().unwrap().kind {
            TokenKind::Identifier(s) => assert_eq!(s, "main"),
            other => panic!("Expected Identifier 'main', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LParen);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RParen);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LBrace);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::KwReturn);
        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralInt(s, _) => assert_eq!(s, "42"),
            other => panic!("Expected LiteralInt '42', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Semi);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RBrace);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_boolean_english() {
        // Input: English boolean literals
        // Expected: LiteralBool
        // Rationale: English booleans must work
        let input = "true false";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LiteralBool(true),
            "'true' must be boolean true");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LiteralBool(false),
            "'false' must be boolean false");
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_char_literal_space() {
        // Input: Space character literal
        // Expected: LiteralChar(' ')
        // Rationale: Space is valid char
        let input = "' '";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralChar(c) => assert_eq!(c, ' ',
                "Space char literal must be valid"),
            other => panic!("Expected LiteralChar ' ', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_char_literal_unicode() {
        // Input: Unicode character literal
        // Expected: LiteralChar with unicode
        // Rationale: Unicode chars must be supported
        let input = "'λ'";
        let mut lexer = Lexer::new(input);

        match lexer.next_token().unwrap().kind {
            TokenKind::LiteralChar(c) => assert_eq!(c, 'λ',
                "Unicode char literal must be valid"),
            other => panic!("Expected LiteralChar 'λ', got {:?}", other),
        }
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }

    #[test]
    fn test_all_brackets() {
        // Input: All bracket types
        // Expected: Correct bracket tokens
        // Rationale: Bracket matching is critical
        let input = "()[]{}";
        let mut lexer = Lexer::new(input);

        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LParen);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RParen);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LBracket);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RBracket);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::LBrace);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::RBrace);
        assert_eq!(lexer.next_token().unwrap().kind, TokenKind::Eof);
    }
}
