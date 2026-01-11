//! TERAS-LANG Lexer
//!
//! Tokenizes TERAS-LANG source code.
//!
//! Reference: TERAS-LANG-LEXER-SPEC_v1_0_0.md
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
}
