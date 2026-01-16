//! RIINA Lexer
//!
//! Tokenizes RIINA source code.
//! RIINA = Rigorous Immutable Integrity No-attack Assured
//! Named for: Reena + Isaac + Imaan
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
}
