//! Lexer Implementation

use crate::token::{Token, TokenKind, Span};
use crate::error::LexError;
use std::iter::Peekable;
use std::str::Chars;

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    source: &'a str,
    pos: usize,
}

impl<'a> Lexer<'a> {
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        Self {
            input: input.chars().peekable(),
            source: input,
            pos: 0,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.input.peek().copied()
    }

    fn advance(&mut self) -> Option<char> {
        match self.input.next() {
            Some(c) => {
                self.pos += c.len_utf8();
                Some(c)
            }
            None => None,
        }
    }

    fn advance_n(&mut self, n: usize) {
        for _ in 0..n {
            self.advance();
        }
    }

    fn consume_while<F>(&mut self, predicate: F) -> String
    where
        F: Fn(char) -> bool,
    {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if predicate(c) {
                self.advance();
                s.push(c);
            } else {
                break;
            }
        }
        s
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                self.advance();
            } else if c == '/' {
                // Check for comments
                // Need to peek next
                // Cannot peek next easily with simple Peekable<Chars>.
                // But we can check current position in source.
                // Or verify next char.
                // Hack: consume / then peek. If not /, put back? No.

                // Let's look at source slice if possible, or just standard lookahead.
                // peek() gives current char.
                // clone iter?
                let mut lookahead = self.input.clone();
                lookahead.next(); // consume current '/'
                match lookahead.next() {
                    Some('/') => {
                        // Line comment
                        self.advance(); // /
                        self.advance(); // /
                        while let Some(c) = self.peek() {
                            if c == '\n' {
                                break;
                            }
                            self.advance();
                        }
                    }
                    Some('*') => {
                        // Block comment
                        self.advance(); // /
                        self.advance(); // *
                        let mut depth = 1;
                        while depth > 0 {
                            match self.advance() {
                                Some('/') => {
                                    if let Some('*') = self.peek() {
                                        self.advance();
                                        depth += 1;
                                    }
                                }
                                Some('*') => {
                                    if let Some('/') = self.peek() {
                                        self.advance();
                                        depth -= 1;
                                    }
                                }
                                Some(_) => {} // Ignore other characters
                                None => break, // Unterminated, handled by next_token logic?
                            }
                        }
                    }
                    _ => break, // Not a comment
                }
            } else {
                break;
            }
        }
    }

    pub fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_whitespace();

        let start = self.pos;
        let c = match self.advance() {
            Some(c) => c,
            None => return Ok(Token::new(TokenKind::Eof, Span::new(start, start))),
        };

        let kind = match c {
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semi,
            '?' => TokenKind::Question,
            '@' => TokenKind::At,
            '#' => TokenKind::Hash,
            '$' => TokenKind::Dollar,
            
            '.' => {
                if let Some('.') = self.peek() {
                    self.advance();
                    if let Some('=') = self.peek() {
                        self.advance();
                        TokenKind::DotDotEq
                    } else {
                        TokenKind::DotDot
                    }
                } else {
                    TokenKind::Dot
                }
            }
            
            ':' => {
                if let Some(':') = self.peek() {
                    self.advance();
                    TokenKind::ColonColon
                } else {
                    TokenKind::Colon
                }
            }

            '+' => if let Some('=') = self.peek() { self.advance(); TokenKind::PlusEq } else { TokenKind::Plus },
            '-' => if let Some('=') = self.peek() { self.advance(); TokenKind::MinusEq }
                   else if let Some('>') = self.peek() { self.advance(); TokenKind::Arrow }
                   else { TokenKind::Minus },
            '*' => if let Some('=') = self.peek() { self.advance(); TokenKind::StarEq } else { TokenKind::Star },
            '/' => if let Some('=') = self.peek() { self.advance(); TokenKind::SlashEq } else { TokenKind::Slash },
            '%' => if let Some('=') = self.peek() { self.advance(); TokenKind::PercentEq } else { TokenKind::Percent },
            '^' => if let Some('=') = self.peek() { self.advance(); TokenKind::CaretEq } else { TokenKind::Caret },
            
            '&' => if let Some('=') = self.peek() { self.advance(); TokenKind::AndEq }
                   else if let Some('&') = self.peek() { self.advance(); TokenKind::AndAnd }
                   else { TokenKind::And },
            
            '|' => if let Some('=') = self.peek() { self.advance(); TokenKind::OrEq }
                   else if let Some('|') = self.peek() { self.advance(); TokenKind::OrOr }
                   else { TokenKind::Or },

            '!' => if let Some('=') = self.peek() { self.advance(); TokenKind::Ne } else { TokenKind::Not },
            '=' => if let Some('=') = self.peek() { self.advance(); TokenKind::EqEq }
                   else if let Some('>') = self.peek() { self.advance(); TokenKind::FatArrow }
                   else { TokenKind::Eq },
            
            '<' => if let Some('=') = self.peek() { self.advance(); TokenKind::Le }
                   else if let Some('<') = self.peek() { 
                       self.advance(); 
                       if let Some('=') = self.peek() { self.advance(); TokenKind::ShlEq } else { TokenKind::Shl }
                   } else { TokenKind::Lt },
            
            '>' => if let Some('=') = self.peek() { self.advance(); TokenKind::Ge }
                   else if let Some('>') = self.peek() { 
                       self.advance(); 
                       if let Some('=') = self.peek() { self.advance(); TokenKind::ShrEq } else { TokenKind::Shr }
                   } else { TokenKind::Gt },

            '"' => self.read_string(start)?,
            '\'' => self.read_char_or_lifetime(start)?,
            
            _ if c.is_ascii_digit() => self.read_number(c, start)?,
            _ if is_ident_start(c) => self.read_identifier(c, start),
            
            _ => return Err(LexError::UnexpectedChar(c, start)),
        };

        Ok(Token::new(kind, Span::new(start, self.pos)))
    }

    fn read_string(&mut self, start: usize) -> Result<TokenKind, LexError> {
        let mut value = String::new();
        loop {
            match self.advance() {
                Some('"') => break,
                Some('\\') => {
                    match self.advance() {
                        Some('n') => value.push('\n'),
                        Some('r') => value.push('\r'),
                        Some('t') => value.push('\t'),
                        Some('0') => value.push('\0'),
                        Some('\\') => value.push('\\'),
                        Some('"') => value.push('"'),
                        Some('\'') => value.push('\''),
                        Some(c) => value.push(c), // Should handle unicode/hex
                        None => return Err(LexError::UnterminatedString(start)),
                    }
                }
                Some(c) => value.push(c),
                None => return Err(LexError::UnterminatedString(start)),
            }
        }
        Ok(TokenKind::LiteralString(value))
    }

    fn read_char_or_lifetime(&mut self, start: usize) -> Result<TokenKind, LexError> {
        // If it's a lifetime: 'ident
        // If it's a char: 'c' or '\n'
        
        // Peek next
        let c1 = self.peek();
        match c1 {
            Some(c) if is_ident_start(c) => {
                // Could be lifetime OR char 'a'
                // Consume char
                self.advance();
                let c2 = self.peek();
                if c2 == Some('\'') {
                    self.advance();
                    Ok(TokenKind::LiteralChar(c))
                } else {
                    // It is a lifetime
                    let rest = self.consume_while(is_ident_continue);
                    let mut name = String::new();
                    name.push(c);
                    name.push_str(&rest);
                    Ok(TokenKind::Lifetime(name))
                }
            }
            Some('\\') => {
                // Escape char
                self.advance();
                let esc = self.advance().ok_or(LexError::UnterminatedChar(start))?;
                let c_val = match esc {
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    '0' => '\0',
                    '\\' => '\\',
                    '\'' => '\'',
                    '"' => '"',
                    _ => return Err(LexError::InvalidEscapeSequence(start)),
                };
                if self.advance() != Some('\'') {
                    return Err(LexError::UnterminatedChar(start));
                }
                Ok(TokenKind::LiteralChar(c_val))
            }
            Some(c) => {
                self.advance();
                if self.advance() != Some('\'') {
                    return Err(LexError::UnterminatedChar(start));
                }
                Ok(TokenKind::LiteralChar(c))
            }
            None => Err(LexError::UnterminatedChar(start)),
        }
    }

    fn read_number(&mut self, first: char, _start: usize) -> Result<TokenKind, LexError> {
        let mut s = String::new();
        s.push(first);
        
        // Hex/Oct/Bin
        if first == '0' {
            if let Some(c) = self.peek() {
                if c == 'x' || c == 'o' || c == 'b' {
                    self.advance();
                    s.push(c);
                    s.push_str(&self.consume_while(|c| c.is_ascii_hexdigit() || c == '_'));
                    // Check suffix
                    // ...
                    return Ok(TokenKind::LiteralInt(s, None)); // TODO: Suffix
                }
            }
        }

        s.push_str(&self.consume_while(|c| c.is_ascii_digit() || c == '_'));

        // Float?
        if let Some('.') = self.peek() {
            // Need to distinguish range ..
            // Peek next next?
            let mut lookahead = self.input.clone();
            lookahead.next(); // consume .
            if let Some(c) = lookahead.next() {
                if c != '.' && !is_ident_start(c) { // 1.e5, 1.2
                    self.advance();
                    s.push('.');
                    s.push_str(&self.consume_while(|c| c.is_ascii_digit() || c == '_'));
                    // Exponent
                    // ...
                    return Ok(TokenKind::LiteralFloat(s, None));
                }
            }
        }
        
        Ok(TokenKind::LiteralInt(s, None)) // Default
    }

    fn read_identifier(&mut self, first: char, _start: usize) -> TokenKind {
        let mut s = String::new();
        s.push(first);
        s.push_str(&self.consume_while(is_ident_continue));

        match s.as_str() {
            "true" => TokenKind::LiteralBool(true),
            "false" => TokenKind::LiteralBool(false),
            "fn" => TokenKind::KwFn,
            "let" => TokenKind::KwLet,
            "mut" => TokenKind::KwMut,
            "const" => TokenKind::KwConst,
            "static" => TokenKind::KwStatic,
            "type" => TokenKind::KwType,
            "struct" => TokenKind::KwStruct,
            "enum" => TokenKind::KwEnum,
            "union" => TokenKind::KwUnion,
            "trait" => TokenKind::KwTrait,
            "impl" => TokenKind::KwImpl,
            "where" => TokenKind::KwWhere,
            "for" => TokenKind::KwFor,
            "if" => TokenKind::KwIf,
            "else" => TokenKind::KwElse,
            "match" => TokenKind::KwMatch,
            "loop" => TokenKind::KwLoop,
            "while" => TokenKind::KwWhile,
            "break" => TokenKind::KwBreak,
            "continue" => TokenKind::KwContinue,
            "return" => TokenKind::KwReturn,
            "mod" => TokenKind::KwMod,
            "pub" => TokenKind::KwPub,
            "use" => TokenKind::KwUse,
            "as" => TokenKind::KwAs,
            "self" => TokenKind::KwSelfValue,
            "Self" => TokenKind::KwSelfType,
            "super" => TokenKind::KwSuper,
            "crate" => TokenKind::KwCrate,
            "extern" => TokenKind::KwExtern,
            "async" => TokenKind::KwAsync,
            "await" => TokenKind::KwAwait,
            "move" => TokenKind::KwMove,
            "ref" => TokenKind::KwRef,
            "unsafe" => TokenKind::KwUnsafe,
            "effect" => TokenKind::KwEffect,
            "handle" => TokenKind::KwHandle,
            "resume" => TokenKind::KwResume,
            "abort" => TokenKind::KwAbort,
            "secret" => TokenKind::KwSecret,
            "public" => TokenKind::KwPublic,
            "tainted" => TokenKind::KwTainted,
            "declassify" => TokenKind::KwDeclassify,
            "sanitize" => TokenKind::KwSanitize,
            "session" => TokenKind::KwSession,
            "send" => TokenKind::KwSend,
            "recv" => TokenKind::KwRecv,
            "select" => TokenKind::KwSelect,
            "branch" => TokenKind::KwBranch,
            "end" => TokenKind::KwEnd,
            "capability" => TokenKind::KwCapability,
            "revoke" => TokenKind::KwRevoke,
            "atomic" => TokenKind::KwAtomic,
            "fence" => TokenKind::KwFence,
            "acquire" => TokenKind::KwAcquire,
            "release" => TokenKind::KwRelease,
            "seqcst" => TokenKind::KwSeqCst,
            "relaxed" => TokenKind::KwRelaxed,
            "acqrel" => TokenKind::KwAcqRel,
            "product" => TokenKind::KwProduct,
            "ct" => TokenKind::KwCt,
            "speculation_safe" => TokenKind::KwSpeculationSafe,
            "combined" => TokenKind::KwCombined,
            "zeroize" => TokenKind::KwZeroize,
            _ => TokenKind::Identifier(s),
        }
    }
}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}