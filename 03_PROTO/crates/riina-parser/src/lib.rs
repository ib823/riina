//! RIINA Parser
//!
//! Parses token streams into ASTs defined in `riina-types`.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

use riina_lexer::{Token, TokenKind, Lexer, Span};
use riina_types::{BinOp, Expr, Ty, Ident, SecurityLevel, Effect, TopLevelDecl, Program, TaintSource, Sanitizer, CapabilityKind};
use std::fmt;
use std::iter::Peekable;

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.kind, self.span.start, self.span.end)
    }
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

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorKind::UnexpectedToken(tok) => write!(f, "Unexpected token: {:?}", tok),
            ParseErrorKind::UnexpectedEof => write!(f, "Unexpected end of input"),
            ParseErrorKind::ExpectedIdentifier => write!(f, "Expected identifier"),
            ParseErrorKind::ExpectedType => write!(f, "Expected type"),
            ParseErrorKind::ExpectedExpression => write!(f, "Expected expression"),
            ParseErrorKind::InvalidSecurityLevel => write!(f, "Invalid security level"),
            ParseErrorKind::InvalidEffect => write!(f, "Invalid effect"),
        }
    }
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
        self.parse_stmt_sequence()
    }

    /// Parse a complete .rii file as a sequence of top-level declarations.
    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut decls = Vec::new();
        while self.peek().map(|t| &t.kind) != Some(&TokenKind::Eof) && self.peek().is_some() {
            decls.push(self.parse_top_level_decl()?);
        }
        Ok(Program { decls })
    }

    fn parse_top_level_decl(&mut self) -> Result<TopLevelDecl, ParseError> {
        match self.peek().map(|t| &t.kind) {
            Some(TokenKind::KwMod) => {
                // modul name; — skip (no module system yet)
                self.consume(TokenKind::KwMod)?;
                let _name = self.parse_ident()?;
                self.consume(TokenKind::Semi)?;
                self.parse_top_level_decl()
            }
            Some(TokenKind::KwUse) => {
                // guna path::to::module; — skip (no module system yet)
                self.consume(TokenKind::KwUse)?;
                while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Semi) | None) {
                    self.next();
                }
                self.consume(TokenKind::Semi)?;
                self.parse_top_level_decl()
            }
            Some(TokenKind::KwStruct) | Some(TokenKind::KwEnum) => {
                // bentuk/pilihan — skip declaration (no struct/enum semantics yet)
                self.next(); // consume KwStruct or KwEnum
                let _name = self.parse_ident()?;
                self.consume(TokenKind::LBrace)?;
                // Skip until matching RBrace
                let mut depth = 1u32;
                while depth > 0 {
                    match self.peek().map(|t| &t.kind) {
                        Some(TokenKind::LBrace) => { self.next(); depth += 1; }
                        Some(TokenKind::RBrace) => { self.next(); depth -= 1; }
                        None => break,
                        _ => { self.next(); }
                    }
                }
                self.parse_top_level_decl()
            }
            Some(TokenKind::KwPub) => {
                // awam fungsi ... — consume visibility, delegate
                self.consume(TokenKind::KwPub)?;
                self.parse_top_level_decl()
            }
            Some(TokenKind::KwFn) => self.parse_function_decl(),
            Some(TokenKind::KwLet) => {
                self.consume(TokenKind::KwLet)?;
                let name = self.parse_ident()?;
                self.consume(TokenKind::Eq)?;
                let value = self.parse_control_flow()?;
                self.consume(TokenKind::Semi)?;
                Ok(TopLevelDecl::Binding { name, value: Box::new(value) })
            }
            _ => {
                let expr = self.parse_expr()?;
                Ok(TopLevelDecl::Expr(Box::new(expr)))
            }
        }
    }

    fn parse_function_decl(&mut self) -> Result<TopLevelDecl, ParseError> {
        self.consume(TokenKind::KwFn)?;
        let name = self.parse_ident()?;
        self.consume(TokenKind::LParen)?;
        let params = self.parse_param_list()?;
        self.consume(TokenKind::RParen)?;

        // Optional return type
        let return_ty = if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Arrow)) {
            self.consume(TokenKind::Arrow)?;
            self.parse_ty()?
        } else {
            Ty::Unit
        };

        // Optional effect annotation
        let effect = if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwEffect)) {
            self.consume(TokenKind::KwEffect)?;
            self.parse_effect()?
        } else {
            Effect::Pure
        };

        // Body in braces
        self.consume(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;

        Ok(TopLevelDecl::Function {
            name, params, return_ty, effect, body: Box::new(body),
        })
    }

    fn parse_param_list(&mut self) -> Result<Vec<(Ident, Ty)>, ParseError> {
        let mut params = Vec::new();
        if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
            // Optional mut/ubah modifier (ignored for now)
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwMut)) {
                self.consume(TokenKind::KwMut)?;
            }
            let name = self.parse_ident()?;
            self.consume(TokenKind::Colon)?;
            let ty = self.parse_ty()?;
            params.push((name, ty));

            while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                self.consume(TokenKind::Comma)?;
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwMut)) {
                    self.consume(TokenKind::KwMut)?;
                }
                let name = self.parse_ident()?;
                self.consume(TokenKind::Colon)?;
                let ty = self.parse_ty()?;
                params.push((name, ty));
            }
        }
        Ok(params)
    }

    /// Parse a sequence of statements separated by semicolons.
    /// stmt_seq ::= (stmt ';')* expr
    /// A `biar` binding: `biar x = e1; rest` desugars to Let(x, e1, rest).
    /// A non-binding expression followed by `;`: `e1; rest` desugars to Let("_", e1, rest).
    fn parse_stmt_sequence(&mut self) -> Result<Expr, ParseError> {
        // Check if this is a let-binding
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwLet)) {
            self.consume(TokenKind::KwLet)?;
            let name = self.parse_ident()?;
            self.consume(TokenKind::Eq)?;
            let e1 = self.parse_control_flow()?;
            self.consume(TokenKind::Semi)?;
            let e2 = self.parse_stmt_sequence()?;
            return Ok(Expr::Let(name, Box::new(e1), Box::new(e2)));
        }

        let first = self.parse_control_flow()?;

        // If next token is ';', this is a statement sequence
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Semi)) {
            self.consume(TokenKind::Semi)?;
            let rest = self.parse_stmt_sequence()?;
            Ok(Expr::Let("_".to_string(), Box::new(first), Box::new(rest)))
        } else {
            Ok(first)
        }
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
            Some(TokenKind::KwIf) => self.parse_if(),
            Some(TokenKind::KwFn) => self.parse_lam(),
            Some(TokenKind::KwMatch) => self.parse_match(),
            Some(TokenKind::KwHandle) => self.parse_handle(),
            Some(TokenKind::KwGuard) => self.parse_guard(),
            Some(TokenKind::KwReturn) => {
                self.consume(TokenKind::KwReturn)?;
                // pulang expr — return is identity (desugars to just the expression)
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
                    self.parse_pipe()
                } else {
                    self.parse_pipe()
                }
            }
            Some(TokenKind::KwFor) => self.parse_for_in(),
            Some(TokenKind::KwWhile) => self.parse_while(),
            Some(TokenKind::KwLoop) => self.parse_loop(),
            _ => self.parse_pipe(),
        }
    }

    /// Parse for-in loop:
    ///   untuk x dalam iter { body }
    /// Desugars to: map (fn(x: Any) body) iter
    fn parse_for_in(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwFor)?;
        let var = self.parse_ident()?;
        self.consume(TokenKind::KwIn)?;
        let iter = self.parse_pipe()?;
        self.consume(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;
        // Desugar: untuk x dalam list { body } → map(fn(x: Any) body, list)
        let lam = Expr::Lam(var, Ty::Any, Box::new(body));
        Ok(Expr::App(
            Box::new(Expr::App(Box::new(Expr::Var("map".into())), Box::new(lam))),
            Box::new(iter),
        ))
    }

    /// Parse while loop:
    ///   selagi cond { body }
    /// Desugars to: If(cond, Let("_", body, while_again), Unit)
    /// Since we don't have Fix/recursion, we desugar to a bounded
    /// representation the interpreter can handle via recursive eval.
    fn parse_while(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwWhile)?;
        let cond = self.parse_pipe()?;
        self.consume(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;
        // Desugar: selagi cond { body } → if cond { body; () } else { () }
        // Full looping requires runtime support; for now emit single-iteration conditional
        Ok(Expr::If(
            Box::new(cond),
            Box::new(Expr::Let("_".to_string(), Box::new(body), Box::new(Expr::Unit))),
            Box::new(Expr::Unit),
        ))
    }

    /// Parse infinite loop:
    ///   ulang { body }
    /// Desugars to: selagi betul { body }
    fn parse_loop(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwLoop)?;
        self.consume(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;
        // Desugar: ulang { body } → body; () (single iteration for now)
        Ok(Expr::Let("_".to_string(), Box::new(body), Box::new(Expr::Unit)))
    }

    /// Parse guard clause:
    ///   'pastikan'|'guard' expr 'lain'|'else' '{' expr '}' ';' expr
    /// Desugars to If(cond, continuation, else_body)
    fn parse_guard(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwGuard)?;
        let cond = self.parse_pipe()?;
        self.consume(TokenKind::KwElse)?;
        self.consume(TokenKind::LBrace)?;
        let else_body = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;
        self.consume(TokenKind::Semi)?;
        let continuation = self.parse_expr()?;
        Ok(Expr::If(Box::new(cond), Box::new(continuation), Box::new(else_body)))
    }

    /// Parse pipe expressions: expr (|> expr)*
    /// a |> f |> g  desugars to  App(g, App(f, a))
    fn parse_pipe(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_assignment()?;
        while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Pipe)) {
            self.consume(TokenKind::Pipe)?;
            let func = self.parse_assignment()?;
            expr = Expr::App(Box::new(func), Box::new(expr));
        }
        Ok(expr)
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParseError> {
        let lhs = self.parse_or()?;
        if let Some(TokenKind::ColonEq) = self.peek().map(|t| &t.kind) {
            self.consume(TokenKind::ColonEq)?;
            let rhs = self.parse_expr()?;
            Ok(Expr::Assign(Box::new(lhs), Box::new(rhs)))
        } else {
            Ok(lhs)
        }
    }

    fn parse_or(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_and()?;
        while let Some(TokenKind::OrOr) = self.peek().map(|t| &t.kind) {
            self.next();
            let right = self.parse_and()?;
            left = Expr::BinOp(BinOp::Or, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_equality()?;
        while let Some(TokenKind::AndAnd) = self.peek().map(|t| &t.kind) {
            self.next();
            let right = self.parse_equality()?;
            left = Expr::BinOp(BinOp::And, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_equality(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_comparison()?;
        loop {
            let op = match self.peek().map(|t| &t.kind) {
                Some(TokenKind::EqEq) => BinOp::Eq,
                Some(TokenKind::Ne) => BinOp::Ne,
                _ => break,
            };
            self.next();
            let right = self.parse_comparison()?;
            left = Expr::BinOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_comparison(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_additive()?;
        loop {
            let op = match self.peek().map(|t| &t.kind) {
                Some(TokenKind::Lt) => BinOp::Lt,
                Some(TokenKind::Gt) => BinOp::Gt,
                Some(TokenKind::Le) => BinOp::Le,
                Some(TokenKind::Ge) => BinOp::Ge,
                _ => break,
            };
            self.next();
            let right = self.parse_additive()?;
            left = Expr::BinOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_additive(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_multiplicative()?;
        loop {
            let op = match self.peek().map(|t| &t.kind) {
                Some(TokenKind::Plus) => BinOp::Add,
                Some(TokenKind::Minus) => BinOp::Sub,
                _ => break,
            };
            self.next();
            let right = self.parse_multiplicative()?;
            left = Expr::BinOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_multiplicative(&mut self) -> Result<Expr, ParseError> {
        let mut left = self.parse_app()?;
        loop {
            let op = match self.peek().map(|t| &t.kind) {
                Some(TokenKind::Star) => BinOp::Mul,
                Some(TokenKind::Slash) => BinOp::Div,
                Some(TokenKind::Percent) => BinOp::Mod,
                _ => break,
            };
            self.next();
            let right = self.parse_app()?;
            left = Expr::BinOp(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_app(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_unary()?;
        // Check for parenthesized call syntax: f(a, b, c) → App(App(App(f, a), b), c)
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
            // Only treat as call if current expr could be a callee (Var or prior App)
            if matches!(&expr, Expr::Var(_) | Expr::App(_, _)) {
                self.consume(TokenKind::LParen)?;
                if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                    let arg = self.parse_control_flow()?;
                    expr = Expr::App(Box::new(expr), Box::new(arg));
                    while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                        self.consume(TokenKind::Comma)?;
                        let arg = self.parse_control_flow()?;
                        expr = Expr::App(Box::new(expr), Box::new(arg));
                    }
                }
                self.consume(TokenKind::RParen)?;
                return Ok(expr);
            }
        }
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
            Some(TokenKind::KwFst) => {
                self.consume(TokenKind::KwFst)?;
                let e = self.parse_unary()?;
                Ok(Expr::Fst(Box::new(e)))
            },
            Some(TokenKind::KwSnd) => {
                self.consume(TokenKind::KwSnd)?;
                let e = self.parse_unary()?;
                Ok(Expr::Snd(Box::new(e)))
            },
            Some(TokenKind::KwRequire) => {
                self.consume(TokenKind::KwRequire)?;
                let eff = self.parse_effect()?;
                let e = self.parse_unary()?;
                Ok(Expr::Require(eff, Box::new(e)))
            },
            Some(TokenKind::KwGrant) => {
                self.consume(TokenKind::KwGrant)?;
                let eff = self.parse_effect()?;
                let e = self.parse_unary()?;
                Ok(Expr::Grant(eff, Box::new(e)))
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

    // parse_let logic is now inlined in parse_stmt_sequence

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
        let body = self.parse_control_flow()?;
        Ok(Expr::Lam(name, ty, Box::new(body)))
    }

    fn parse_match(&mut self) -> Result<Expr, ParseError> {
         self.consume(TokenKind::KwMatch)?;
         let scrutinee = self.parse_pipe()?;
         self.consume(TokenKind::LBrace)?;

         // Dispatch: inl/inr → sum match, otherwise → literal match
         match self.peek().map(|t| &t.kind) {
             Some(TokenKind::KwInl) => {
                 self.consume(TokenKind::KwInl)?;
                 let x = self.parse_ident()?;
                 self.consume(TokenKind::FatArrow)?;
                 let e1 = self.parse_expr()?;
                 if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                     self.next();
                 }
                 self.consume(TokenKind::KwInr)?;
                 let y = self.parse_ident()?;
                 self.consume(TokenKind::FatArrow)?;
                 let e2 = self.parse_expr()?;
                 if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                     self.next();
                 }
                 self.consume(TokenKind::RBrace)?;
                 Ok(Expr::Case(Box::new(scrutinee), x, Box::new(e1), y, Box::new(e2)))
             }
             _ => {
                 // Literal match: desugar to nested if-else
                 let mut arms = Vec::new();
                 let mut default = None;
                 loop {
                     if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBrace) | None) {
                         break;
                     }
                     // Wildcard _
                     if matches!(self.peek().map(|t| t.kind.clone()), Some(TokenKind::Identifier(ref s)) if s == "_") {
                         self.next();
                         self.consume(TokenKind::FatArrow)?;
                         default = Some(self.parse_pipe()?);
                         if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                             self.next();
                         }
                         break;
                     }
                     let pattern = self.parse_atom()?;
                     self.consume(TokenKind::FatArrow)?;
                     let body = self.parse_pipe()?;
                     arms.push((pattern, body));
                     if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                         self.next();
                     }
                 }
                 self.consume(TokenKind::RBrace)?;
                 let fallback = default.unwrap_or(Expr::Unit);
                 let result = arms.into_iter().rev().fold(fallback, |else_branch, (pat, body)| {
                     Expr::If(
                         Box::new(Expr::BinOp(BinOp::Eq, Box::new(scrutinee.clone()), Box::new(pat))),
                         Box::new(body),
                         Box::new(else_branch),
                     )
                 });
                 Ok(result)
             }
         }
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
            Some(TokenKind::LParen) => {
                self.next();
                // () = Unit, or (T1, T2) = Prod
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                    self.next();
                    return Ok(Ty::Unit);
                }
                let t1 = self.parse_ty()?;
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                    self.consume(TokenKind::Comma)?;
                    let t2 = self.parse_ty()?;
                    self.consume(TokenKind::RParen)?;
                    Ok(Ty::Prod(Box::new(t1), Box::new(t2)))
                } else {
                    self.consume(TokenKind::RParen)?;
                    Ok(t1)
                }
            },
            Some(TokenKind::Identifier(s)) => {
                self.next();
                match s.as_str() {
                    // Primitives
                    "Int" | "Nombor" => Ok(Ty::Int),
                    "Bool" | "Benar" => Ok(Ty::Bool),
                    "Unit" => Ok(Ty::Unit),
                    "String" | "Teks" => Ok(Ty::String),
                    "Bytes" | "Bait" => Ok(Ty::Bytes),

                    // Parameterized types: Name<T>
                    "List" | "Senarai" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::List(Box::new(inner)))
                    },
                    "Option" | "Mungkin" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Option(Box::new(inner)))
                    },
                    "Secret" | "Rahsia" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Secret(Box::new(inner)))
                    },
                    "Proof" | "Bukti" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Proof(Box::new(inner)))
                    },
                    "ConstantTime" | "MasaTetap" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::ConstantTime(Box::new(inner)))
                    },
                    "Zeroizing" | "Sifar" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Zeroizing(Box::new(inner)))
                    },
                    // Ref<T>@level
                    "Ref" | "Ruj" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        self.consume(TokenKind::At)?;
                        let level = self.parse_security_level()?;
                        Ok(Ty::Ref(Box::new(inner), level))
                    },
                    // Sum type: Sum<T1, T2>
                    "Sum" => {
                        self.consume(TokenKind::Lt)?;
                        let t1 = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let t2 = self.parse_ty()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Sum(Box::new(t1), Box::new(t2)))
                    },
                    // Function type: Fn(T1, T2) or Fn(T1, T2, Effect)
                    "Fn" => {
                        self.consume(TokenKind::LParen)?;
                        let param_ty = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let ret_ty = self.parse_ty()?;
                        // Optional effect as third argument
                        let eff = if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                            self.consume(TokenKind::Comma)?;
                            self.parse_effect()?
                        } else {
                            Effect::Pure
                        };
                        self.consume(TokenKind::RParen)?;
                        Ok(Ty::Fn(Box::new(param_ty), Box::new(ret_ty), eff))
                    },
                    // Labeled<T, Level> / Berlabel<T, Level>
                    "Labeled" | "Berlabel" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let level = self.parse_security_level()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Labeled(Box::new(inner), level))
                    },
                    // Tainted<T, Source> / Tercemar<T, Source>
                    "Tainted" | "Tercemar" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let source = self.parse_taint_source()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Tainted(Box::new(inner), source))
                    },
                    // Sanitized<T, Sanitizer> / Disanitasi<T, Sanitizer>
                    "Sanitized" | "Disanitasi" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let san = self.parse_sanitizer()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Sanitized(Box::new(inner), san))
                    },
                    // Capability<Kind> / Keupayaan<Kind>
                    "Capability" | "Keupayaan" => {
                        self.consume(TokenKind::Lt)?;
                        let kind = self.parse_capability_kind()?;
                        self.consume(TokenKind::Gt)?;
                        Ok(Ty::Capability(kind))
                    },
                    _ => Err(ParseError {
                        kind: ParseErrorKind::ExpectedType,
                        span: self.current_span,
                    }),
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
            "Public" | "Awam" => Ok(SecurityLevel::Public),
            "Internal" | "Dalaman" => Ok(SecurityLevel::Internal),
            "Session" | "Sesi" => Ok(SecurityLevel::Session),
            "User" | "Pengguna" => Ok(SecurityLevel::User),
            "System" | "Sistem" => Ok(SecurityLevel::System),
            "Secret" | "Rahsia" => Ok(SecurityLevel::Secret),
             _ => Err(ParseError { kind: ParseErrorKind::InvalidSecurityLevel, span: self.current_span })
        }
    }

    fn parse_effect(&mut self) -> Result<Effect, ParseError> {
         let ident = self.parse_ident()?;
         match ident.as_str() {
             "Pure" | "Bersih" => Ok(Effect::Pure),
             "Read" | "Baca" => Ok(Effect::Read),
             "Write" | "Tulis" => Ok(Effect::Write),
             "FileSystem" | "SistemFail" => Ok(Effect::FileSystem),
             "Network" | "Rangkaian" => Ok(Effect::Network),
             "NetworkSecure" | "RangkaianSelamat" => Ok(Effect::NetworkSecure),
             "Crypto" | "Kripto" => Ok(Effect::Crypto),
             "Random" | "Rawak" => Ok(Effect::Random),
             "System" | "Sistem" => Ok(Effect::System),
             "Time" | "Masa" => Ok(Effect::Time),
             "Process" | "Proses" => Ok(Effect::Process),
             "Panel" => Ok(Effect::Panel),
             "Zirah" => Ok(Effect::Zirah),
             "Benteng" => Ok(Effect::Benteng),
             "Sandi" => Ok(Effect::Sandi),
             "Menara" => Ok(Effect::Menara),
             "Gapura" => Ok(Effect::Gapura),
             _ => Err(ParseError { kind: ParseErrorKind::InvalidEffect, span: self.current_span })
         }
    }

    fn parse_taint_source(&mut self) -> Result<TaintSource, ParseError> {
        let ident = self.parse_ident()?;
        match ident.as_str() {
            "NetworkExternal" => Ok(TaintSource::NetworkExternal),
            "NetworkInternal" => Ok(TaintSource::NetworkInternal),
            "UserInput" => Ok(TaintSource::UserInput),
            "FileSystem" => Ok(TaintSource::FileSystem),
            "Database" => Ok(TaintSource::Database),
            "Environment" => Ok(TaintSource::Environment),
            "GapuraRequest" => Ok(TaintSource::GapuraRequest),
            "ZirahEvent" => Ok(TaintSource::ZirahEvent),
            "ZirahEndpoint" => Ok(TaintSource::ZirahEndpoint),
            "BentengBiometric" => Ok(TaintSource::BentengBiometric),
            "SandiSignature" => Ok(TaintSource::SandiSignature),
            "MenaraDevice" => Ok(TaintSource::MenaraDevice),
            _ => Err(ParseError { kind: ParseErrorKind::ExpectedType, span: self.current_span }),
        }
    }

    fn parse_sanitizer(&mut self) -> Result<Sanitizer, ParseError> {
        let ident = self.parse_ident()?;
        match ident.as_str() {
            "HtmlEscape" => Ok(Sanitizer::HtmlEscape),
            "UrlEncode" => Ok(Sanitizer::UrlEncode),
            "JsEscape" => Ok(Sanitizer::JsEscape),
            "CssEscape" => Ok(Sanitizer::CssEscape),
            "SqlEscape" => Ok(Sanitizer::SqlEscape),
            "SqlParam" => Ok(Sanitizer::SqlParam),
            "XssFilter" => Ok(Sanitizer::XssFilter),
            "PathTraversal" => Ok(Sanitizer::PathTraversal),
            "CommandEscape" => Ok(Sanitizer::CommandEscape),
            "LdapEscape" => Ok(Sanitizer::LdapEscape),
            "XmlEscape" => Ok(Sanitizer::XmlEscape),
            "JsonValidation" => Ok(Sanitizer::JsonValidation),
            "XmlValidation" => Ok(Sanitizer::XmlValidation),
            "EmailValidation" => Ok(Sanitizer::EmailValidation),
            "PhoneValidation" => Ok(Sanitizer::PhoneValidation),
            "HashVerify" => Ok(Sanitizer::HashVerify),
            "SignatureVerify" => Ok(Sanitizer::SignatureVerify),
            "MacVerify" => Ok(Sanitizer::MacVerify),
            "GapuraAuth" => Ok(Sanitizer::GapuraAuth),
            "ZirahSession" => Ok(Sanitizer::ZirahSession),
            "BentengBiometric" => Ok(Sanitizer::BentengBiometric),
            "SandiDecrypt" => Ok(Sanitizer::SandiDecrypt),
            "MenaraAttestation" => Ok(Sanitizer::MenaraAttestation),
            _ => Err(ParseError { kind: ParseErrorKind::ExpectedType, span: self.current_span }),
        }
    }

    fn parse_capability_kind(&mut self) -> Result<CapabilityKind, ParseError> {
        let ident = self.parse_ident()?;
        match ident.as_str() {
            "FileRead" => Ok(CapabilityKind::FileRead),
            "FileWrite" => Ok(CapabilityKind::FileWrite),
            "FileExecute" => Ok(CapabilityKind::FileExecute),
            "FileDelete" => Ok(CapabilityKind::FileDelete),
            "NetConnect" => Ok(CapabilityKind::NetConnect),
            "NetListen" => Ok(CapabilityKind::NetListen),
            "NetBind" => Ok(CapabilityKind::NetBind),
            "ProcSpawn" => Ok(CapabilityKind::ProcSpawn),
            "ProcSignal" => Ok(CapabilityKind::ProcSignal),
            "SysTime" => Ok(CapabilityKind::SysTime),
            "SysRandom" => Ok(CapabilityKind::SysRandom),
            "SysEnv" => Ok(CapabilityKind::SysEnv),
            "RootProduct" => Ok(CapabilityKind::RootProduct),
            "ProductAccess" => Ok(CapabilityKind::ProductAccess),
            _ => Err(ParseError { kind: ParseErrorKind::ExpectedType, span: self.current_span }),
        }
    }
}

#[cfg(test)]
mod tests;
