//! Lexer Implementation

use crate::token::{Token, TokenKind, Span};
use crate::error::LexError;
use std::iter::Peekable;
use std::str::Chars;

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    #[allow(dead_code)] // Reserved for future error recovery and span validation
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

    #[allow(dead_code)] // Reserved for future optimizations
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

    /// Returns the next token from the input.
    ///
    /// # Errors
    ///
    /// Returns a [`LexError`] if:
    /// - An unexpected character is encountered
    /// - A string literal is not properly terminated
    /// - A character literal is not properly terminated
    /// - An invalid escape sequence is encountered
    pub fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_whitespace();

        let start = self.pos;
        let Some(c) = self.advance() else {
            return Ok(Token::new(TokenKind::Eof, Span::new(start, start)));
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
                } else if let Some('=') = self.peek() {
                    self.advance();
                    TokenKind::ColonEq
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
            
            '|' => if let Some('|') = self.peek() { self.advance(); TokenKind::OrOr }
                   else if let Some('>') = self.peek() { self.advance(); TokenKind::Pipe }
                   else if let Some('=') = self.peek() { self.advance(); TokenKind::OrEq }
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
            
            _ if c.is_ascii_digit() => self.read_number(c),
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

    fn read_number(&mut self, first: char) -> TokenKind {
        let mut s = String::new();
        s.push(first);

        // Hex/Oct/Bin
        if first == '0' {
            if let Some(c) = self.peek() {
                if c == 'x' || c == 'o' || c == 'b' {
                    self.advance();
                    s.push(c);
                    s.push_str(&self.consume_while(|ch| ch.is_ascii_hexdigit() || ch == '_'));
                    // Check suffix
                    // ...
                    return TokenKind::LiteralInt(s, None); // TODO: Suffix
                }
            }
        }

        s.push_str(&self.consume_while(|ch| ch.is_ascii_digit() || ch == '_'));

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
                    s.push_str(&self.consume_while(|ch| ch.is_ascii_digit() || ch == '_'));
                    // Exponent
                    // ...
                    return TokenKind::LiteralFloat(s, None);
                }
            }
        }

        TokenKind::LiteralInt(s, None) // Default
    }

    fn read_identifier(&mut self, first: char, _start: usize) -> TokenKind {
        let mut s = String::new();
        s.push(first);
        s.push_str(&self.consume_while(is_ident_continue));

        match s.as_str() {
            // Boolean literals (English + Bahasa Melayu)
            "true" | "betul" => TokenKind::LiteralBool(true),
            "false" | "salah" => TokenKind::LiteralBool(false),

            // Declaration keywords (English | Bahasa Melayu)
            "fn" | "fungsi" => TokenKind::KwFn,
            "let" | "biar" => TokenKind::KwLet,
            "mut" | "ubah" => TokenKind::KwMut,
            "const" | "tetap" => TokenKind::KwConst,
            "static" | "statik" => TokenKind::KwStatic,
            "type" | "jenis" => TokenKind::KwType,
            "struct" | "bentuk" => TokenKind::KwStruct,
            "enum" | "pilihan" => TokenKind::KwEnum,
            "union" | "kesatuan" => TokenKind::KwUnion,
            "trait" | "sifat" => TokenKind::KwTrait,
            "impl" | "laksana" => TokenKind::KwImpl,
            "where" | "dimana" => TokenKind::KwWhere,
            "mod" | "modul" => TokenKind::KwMod,
            "pub" | "awam" => TokenKind::KwPub,
            "use" | "guna" => TokenKind::KwUse,
            "extern" | "luaran" => TokenKind::KwExtern,

            // Control flow keywords (English | Bahasa Melayu)
            "for" | "untuk" => TokenKind::KwFor,
            "if" | "kalau" => TokenKind::KwIf,
            "else" | "lain" => TokenKind::KwElse,
            "match" | "padan" => TokenKind::KwMatch,
            "loop" | "ulang" => TokenKind::KwLoop,
            "while" | "selagi" => TokenKind::KwWhile,
            "with" | "dengan" => TokenKind::KwWith,
            "break" | "keluar" => TokenKind::KwBreak,
            "continue" | "terus" => TokenKind::KwContinue,
            "return" | "pulang" => TokenKind::KwReturn,

            // Type cast and reference (English | Bahasa Melayu)
            "as" | "sebagai" => TokenKind::KwAs,
            "ref" | "ruj" => TokenKind::KwRef,
            "move" | "pindah" => TokenKind::KwMove,

            // Self references (English | Bahasa Melayu)
            "self" | "diri" => TokenKind::KwSelfValue,
            "Self" | "Diri" => TokenKind::KwSelfType,
            "super" | "induk" => TokenKind::KwSuper,
            "crate" | "peti" => TokenKind::KwCrate,

            // Async/await (English | Bahasa Melayu)
            "async" | "tak_segerak" => TokenKind::KwAsync,
            "await" | "tunggu" => TokenKind::KwAwait,

            // Safety keywords (English | Bahasa Melayu)
            "unsafe" | "bahaya" => TokenKind::KwUnsafe,

            // Effect system (English | Bahasa Melayu)
            "effect" | "kesan" => TokenKind::KwEffect,
            "perform" | "laku" => TokenKind::KwPerform,
            "handle" | "kendali" => TokenKind::KwHandle,
            "resume" | "sambung" => TokenKind::KwResume,
            "abort" | "batal" => TokenKind::KwAbort,

            // Security keywords (English | Bahasa Melayu)
            "secret" | "rahsia" => TokenKind::KwSecret,
            "classify" | "sulit" => TokenKind::KwClassify,
            "public" | "terbuka" => TokenKind::KwPublic,
            "tainted" | "tercemar" => TokenKind::KwTainted,
            "declassify" | "dedah" => TokenKind::KwDeclassify,
            "prove" | "bukti" => TokenKind::KwProve,
            "sanitize" | "bersihkan" => TokenKind::KwSanitize,

            // Logic keywords (Bahasa Melayu contextual)
            "in" | "dalam" => TokenKind::KwIn,
            "is" | "ialah" => TokenKind::KwIs,

            // Security extended (English | Bahasa Melayu)
            "pure" | "bersih" => TokenKind::KwPure,
            "safe" | "selamat" => TokenKind::KwSafe,
            "policy" | "dasar" => TokenKind::KwPolicy,
            "level" | "tahap" => TokenKind::KwLevel,

            // Concurrency extended (English | Bahasa Melayu)
            "channel" | "saluran" => TokenKind::KwChannel,

            // Reference extended (English | Bahasa Melayu)
            "borrow" | "pinjam" => TokenKind::KwBorrow,
            "copy" | "salin" => TokenKind::KwCopy,
            "clone" | "klon" => TokenKind::KwClone,
            "lifetime" | "jangka" => TokenKind::KwLifetime,

            // Logic keywords (English | Bahasa Melayu)
            "and" | "dan" => TokenKind::KwAnd,
            "or" | "atau" => TokenKind::KwOr,
            "not" | "bukan" => TokenKind::KwNot,

            // Guard clause (English | Bahasa Melayu)
            "guard" | "pastikan" => TokenKind::KwGuard,

            // Sum type constructors
            "inl" => TokenKind::KwInl,
            "inr" => TokenKind::KwInr,

            // Session types (English | Bahasa Melayu)
            "session" | "sesi" => TokenKind::KwSession,
            "send" | "hantar" => TokenKind::KwSend,
            "recv" | "terima" => TokenKind::KwRecv,
            "select" | "pilih" => TokenKind::KwSelect,
            "branch" | "cabang" => TokenKind::KwBranch,
            "end" | "tamat" => TokenKind::KwEnd,

            // Capabilities (English | Bahasa Melayu)
            "capability" | "keupayaan" => TokenKind::KwCapability,
            "revoke" | "tarik_balik" => TokenKind::KwRevoke,

            // Concurrency/Memory ordering (English | Bahasa Melayu)
            "atomic" | "atom" => TokenKind::KwAtomic,
            "fence" | "pagar" => TokenKind::KwFence,
            "acquire" | "peroleh" => TokenKind::KwAcquire,
            "release" | "lepas" => TokenKind::KwRelease,
            "seqcst" | "turutan_ketat" => TokenKind::KwSeqCst,
            "relaxed" | "santai" => TokenKind::KwRelaxed,
            "acqrel" | "peroleh_lepas" => TokenKind::KwAcqRel,

            // Product types (English | Bahasa Melayu)
            "product" | "hasil_darab" => TokenKind::KwProduct,

            // Constant-time (English | Bahasa Melayu)
            "ct" | "masa_tetap" => TokenKind::KwCt,
            "speculation_safe" | "selamat_spekulasi" => TokenKind::KwSpeculationSafe,
            "combined" | "gabungan" => TokenKind::KwCombined,
            "zeroize" | "kosongkan" => TokenKind::KwZeroize,

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