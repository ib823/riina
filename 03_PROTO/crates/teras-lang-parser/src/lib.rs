//! TERAS-LANG Parser
//!
//! Parses token streams into ASTs defined in `teras-lang-types`.
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

use teras_lang_lexer::{Token, TokenKind, Lexer, Span};
use teras_lang_types::{Expr, Ty, Ident, SecurityLevel, Effect};
use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrorKind {
    UnexpectedToken(TokenKind),
    UnexpectedEof,
    ExpectedIdentifier,
    ExpectedType,
    ExpectedExpression,
    InvalidSecurityLevel,
    InvalidEffect,
}

struct LexerIter<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Iterator for LexerIter<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next_token().ok()
    }
}

pub struct Parser<'a> {
    lexer: Peekable<LexerIter<'a>>,
    current_span: Span,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            lexer: LexerIter { lexer: Lexer::new(source) }.peekable(),
            current_span: Span { start: 0, end: 0 },
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_control_flow()
    }

    fn peek(&mut self) -> Option<&Token> {
        self.lexer.peek()
    }

    fn next(&mut self) -> Option<Token> {
        let token = self.lexer.next();
        if let Some(t) = &token {
            self.current_span = t.span;
        }
        token
    }

    fn consume(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        let matches = if let Some(token) = self.peek() {
            token.kind == kind
        } else {
            false
        };

        if matches {
            Ok(self.next().unwrap())
        } else if let Some(token) = self.peek() {
             Err(ParseError {
                kind: ParseErrorKind::UnexpectedToken(token.kind.clone()),
                span: token.span,
            })
        } else {
             Err(ParseError {
                kind: ParseErrorKind::UnexpectedEof,
                span: self.current_span,
            })
        }
    }

    fn parse_control_flow(&mut self) -> Result<Expr, ParseError> {
        match self.peek().map(|t| &t.kind) {
            Some(TokenKind::KwLet) => self.parse_let(),
            Some(TokenKind::KwIf) => self.parse_if(),
            Some(TokenKind::KwFn) => self.parse_lam(),
            Some(TokenKind::KwMatch) => self.parse_match(),
            Some(TokenKind::KwHandle) => self.parse_handle(),
            _ => self.parse_assignment(),
        }
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParseError> {
        let lhs = self.parse_app()?;
        if let Some(TokenKind::ColonEq) = self.peek().map(|t| &t.kind) {
            self.consume(TokenKind::ColonEq)?;
            let rhs = self.parse_expr()?; 
            Ok(Expr::Assign(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_app(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_unary()?;
        loop {
            if self.is_expr_start() {
                let arg = self.parse_unary()?;
                expr = Expr::App(Box::new(expr), Box::new(arg));
            } else {
                break;
            }
        }
        Ok(expr)
    }

    fn is_expr_start(&mut self) -> bool {
        let kind = self.peek().map(|t| &t.kind);
        matches!(kind,
             Some(TokenKind::LiteralInt(_, _)) |
             Some(TokenKind::LiteralBool(_)) |
             Some(TokenKind::LiteralString(_)) |
             Some(TokenKind::Identifier(_)) |
             Some(TokenKind::LParen) |
             Some(TokenKind::Not) |
             Some(TokenKind::KwRef) |
             Some(TokenKind::KwPerform) |
             Some(TokenKind::KwClassify) |
             Some(TokenKind::KwDeclassify) |
             Some(TokenKind::KwProve) |
             Some(TokenKind::KwInl) |
             Some(TokenKind::KwInr)
        )
    }

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        let kind = self.peek().map(|t| t.kind.clone());
        match kind {
            Some(TokenKind::Not) => {
                self.consume(TokenKind::Not)?;
                let e = self.parse_unary()?;
                Ok(Expr::Deref(Box::new(e)))
            },
            Some(TokenKind::KwRef) => {
                self.consume(TokenKind::KwRef)?;
                let e = self.parse_unary()?;
                self.consume(TokenKind::At)?;
                let level = self.parse_security_level()?;
                Ok(Expr::Ref(Box::new(e), level))
            },
            Some(TokenKind::KwPerform) => {
                self.consume(TokenKind::KwPerform)?;
                let eff = self.parse_effect()?;
                let e = self.parse_unary()?;
                Ok(Expr::Perform(eff, Box::new(e)))
            },
            Some(TokenKind::KwClassify) => {
                self.consume(TokenKind::KwClassify)?;
                let e = self.parse_unary()?;
                Ok(Expr::Classify(Box::new(e)))
            },
            Some(TokenKind::KwDeclassify) => {
                self.consume(TokenKind::KwDeclassify)?;
                let e1 = self.parse_unary()?;
                self.consume(TokenKind::KwWith)?;
                let e2 = self.parse_unary()?;
                Ok(Expr::Declassify(Box::new(e1), Box::new(e2)))
            },
             Some(TokenKind::KwProve) => {
                self.consume(TokenKind::KwProve)?;
                let e = self.parse_unary()?;
                Ok(Expr::Prove(Box::new(e)))
            },
            Some(TokenKind::KwInl) => {
                self.consume(TokenKind::KwInl)?;
                let e = self.parse_unary()?;
                self.consume(TokenKind::Colon)?;
                let ty = self.parse_ty()?;
                Ok(Expr::Inl(Box::new(e), ty))
            },
             Some(TokenKind::KwInr) => {
                self.consume(TokenKind::KwInr)?;
                let e = self.parse_unary()?;
                self.consume(TokenKind::Colon)?;
                let ty = self.parse_ty()?;
                Ok(Expr::Inr(Box::new(e), ty))
            },
            _ => self.parse_atom(),
        }
    }

    fn parse_atom(&mut self) -> Result<Expr, ParseError> {
        let kind = self.peek().map(|t| t.kind.clone());
        match kind {
            Some(TokenKind::LiteralInt(s, _)) => {
                self.next();
                Ok(Expr::Int(s.parse().unwrap_or(0)))
            },
            Some(TokenKind::LiteralBool(b)) => {
                self.next();
                Ok(Expr::Bool(b))
            },
            Some(TokenKind::LiteralString(s)) => {
                self.next();
                Ok(Expr::String(s))
            },
            Some(TokenKind::Identifier(s)) => {
                self.next();
                Ok(Expr::Var(s))
            },
            Some(TokenKind::LParen) => {
                self.next(); 
                let is_unit = if let Some(token) = self.peek() {
                    token.kind == TokenKind::RParen
                } else {
                    false
                };

                if is_unit {
                     self.next();
                     Ok(Expr::Unit)
                } else {
                    let e = self.parse_expr()?;
                    
                    let is_comma = if let Some(token) = self.peek() {
                        token.kind == TokenKind::Comma
                    } else {
                        false
                    };

                    if is_comma {
                        self.next();
                        let e2 = self.parse_expr()?;
                        self.consume(TokenKind::RParen)?;
                        Ok(Expr::Pair(Box::new(e), Box::new(e2)))
                    } else {
                        self.consume(TokenKind::RParen)?;
                        Ok(e)
                    }
                }
            },
            Some(kind) => Err(ParseError {
                kind: ParseErrorKind::UnexpectedToken(kind),
                span: self.current_span,
            }),
            None => Err(ParseError {
                kind: ParseErrorKind::UnexpectedEof,
                span: self.current_span,
            }),
        }
    }

    fn parse_let(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwLet)?;
        let name = self.parse_ident()?;
        self.consume(TokenKind::Eq)?;
        let e1 = self.parse_expr()?;
        self.consume(TokenKind::Semi)?;
        let e2 = self.parse_expr()?;
        Ok(Expr::Let(name, Box::new(e1), Box::new(e2)))
    }

    fn parse_if(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwIf)?;
        let cond = self.parse_expr()?;
        self.consume(TokenKind::LBrace)?;
        let e2 = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;
        self.consume(TokenKind::KwElse)?;
        self.consume(TokenKind::LBrace)?;
        let e3 = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;
        Ok(Expr::If(Box::new(cond), Box::new(e2), Box::new(e3)))
    }

    fn parse_lam(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwFn)?;
        self.consume(TokenKind::LParen)?;
        let name = self.parse_ident()?;
        self.consume(TokenKind::Colon)?;
        let ty = self.parse_ty()?;
        self.consume(TokenKind::RParen)?;
        let body = self.parse_expr()?;
        Ok(Expr::Lam(name, ty, Box::new(body)))
    }

    fn parse_match(&mut self) -> Result<Expr, ParseError> {
         self.consume(TokenKind::KwMatch)?;
         let e = self.parse_expr()?;
         self.consume(TokenKind::LBrace)?;
         
         self.consume(TokenKind::KwInl)?;
         let x = self.parse_ident()?;
         self.consume(TokenKind::FatArrow)?;
         let e1 = self.parse_expr()?;
         
         if let Some(TokenKind::Comma) = self.peek().map(|t| &t.kind) {
             self.consume(TokenKind::Comma)?;
         }
         
         self.consume(TokenKind::KwInr)?;
         let y = self.parse_ident()?;
         self.consume(TokenKind::FatArrow)?;
         let e2 = self.parse_expr()?;
         
         if let Some(TokenKind::Comma) = self.peek().map(|t| &t.kind) {
             self.consume(TokenKind::Comma)?;
         }
         
         self.consume(TokenKind::RBrace)?;
         
         Ok(Expr::Case(Box::new(e), x, Box::new(e1), y, Box::new(e2)))
    }

    fn parse_handle(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwHandle)?;
        let e = self.parse_expr()?;
        self.consume(TokenKind::KwWith)?;
        let x = self.parse_ident()?;
        self.consume(TokenKind::FatArrow)?;
        let h = self.parse_expr()?;
        Ok(Expr::Handle(Box::new(e), x, Box::new(h)))
    }

    fn parse_ident(&mut self) -> Result<Ident, ParseError> {
        let kind = self.peek().map(|t| t.kind.clone());
        match kind {
            Some(TokenKind::Identifier(s)) => {
                self.next();
                Ok(s)
            },
            Some(_) => Err(ParseError {
                kind: ParseErrorKind::ExpectedIdentifier,
                span: self.current_span,
            }),
            None => Err(ParseError {
                kind: ParseErrorKind::UnexpectedEof,
                span: self.current_span,
            }),
        }
    }

    fn parse_ty(&mut self) -> Result<Ty, ParseError> {
        let kind = self.peek().map(|t| t.kind.clone());
        match kind {
            Some(TokenKind::Identifier(s)) => {
                self.next();
                match s.as_str() {
                    "Int" => Ok(Ty::Int),
                    "Bool" => Ok(Ty::Bool),
                    "Unit" => Ok(Ty::Unit),
                    "String" => Ok(Ty::String),
                    "Bytes" => Ok(Ty::Bytes),
                    _ => Ok(Ty::Unit), // Fallback/Placeholder
                }
            },
            _ => Err(ParseError {
                kind: ParseErrorKind::ExpectedType,
                span: self.current_span,
            }),
        }
    }

    fn parse_security_level(&mut self) -> Result<SecurityLevel, ParseError> {
        let ident = self.parse_ident()?;
        match ident.as_str() {
            "Public" => Ok(SecurityLevel::Public),
            "Secret" => Ok(SecurityLevel::Secret),
             _ => Err(ParseError { kind: ParseErrorKind::InvalidSecurityLevel, span: self.current_span })
        }
    }

    fn parse_effect(&mut self) -> Result<Effect, ParseError> {
         let ident = self.parse_ident()?;
         match ident.as_str() {
             "Pure" => Ok(Effect::Pure),
             "Read" => Ok(Effect::Read),
             "Write" => Ok(Effect::Write),
             "Network" => Ok(Effect::Network),
             "Crypto" => Ok(Effect::Crypto),
             "System" => Ok(Effect::System),
             _ => Err(ParseError { kind: ParseErrorKind::InvalidEffect, span: self.current_span })
         }
    }
}

#[cfg(test)]
mod tests;
