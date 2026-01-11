//! Lexer implementation for TERAS-LANG

use crate::token::{Token, TokenKind, Span};
use crate::error::LexError;

/// TERAS-LANG Lexer
pub struct Lexer<'src> {
    source: &'src str,
    chars: std::iter::Peekable<std::str::CharIndices<'src>>,
    position: usize,
    line: usize,
    column: usize,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer for the given source
    pub fn new(source: &'src str) -> Self {
        Self {
            source,
            chars: source.char_indices().peekable(),
            position: 0,
            line: 1,
            column: 1,
        }
    }

    /// Tokenize the entire source
    pub fn tokenize(&mut self) -> Result<Vec<Token>, LexError> {
        let mut tokens = Vec::new();
        
        loop {
            let token = self.next_token()?;
            let is_eof = matches!(token.kind, TokenKind::Eof);
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        
        Ok(tokens)
    }

    /// Get the next token
    pub fn next_token(&mut self) -> Result<Token, LexError> {
        self.skip_whitespace_and_comments();
        
        let start = self.position;
        let start_line = self.line;
        let start_column = self.column;
        
        let kind = match self.advance() {
            None => TokenKind::Eof,
            Some((_, c)) => self.lex_char(c)?,
        };
        
        let span = Span {
            start,
            end: self.position,
            line: start_line,
            column: start_column,
        };
        
        Ok(Token::new(kind, span))
    }

    fn advance(&mut self) -> Option<(usize, char)> {
        let next = self.chars.next();
        if let Some((pos, c)) = next {
            self.position = pos + c.len_utf8();
            if c == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
        next
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().map(|(_, c)| *c)
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            match self.peek() {
                Some(c) if c.is_whitespace() => {
                    self.advance();
                }
                Some('/') => {
                    // TODO: Handle comments
                    break;
                }
                _ => break,
            }
        }
    }

    fn lex_char(&mut self, c: char) -> Result<TokenKind, LexError> {
        match c {
            // Single-character tokens
            '(' => Ok(TokenKind::LParen),
            ')' => Ok(TokenKind::RParen),
            '[' => Ok(TokenKind::LBracket),
            ']' => Ok(TokenKind::RBracket),
            '{' => Ok(TokenKind::LBrace),
            '}' => Ok(TokenKind::RBrace),
            ',' => Ok(TokenKind::Comma),
            '.' => Ok(TokenKind::Dot),
            ';' => Ok(TokenKind::Semicolon),
            '@' => Ok(TokenKind::At),
            '#' => Ok(TokenKind::Hash),
            '+' => Ok(TokenKind::Plus),
            '*' => Ok(TokenKind::Star),
            '/' => Ok(TokenKind::Slash),
            '%' => Ok(TokenKind::Percent),
            '&' => Ok(TokenKind::Ampersand),
            '|' => Ok(TokenKind::Pipe),
            '^' => Ok(TokenKind::Caret),
            '~' => Ok(TokenKind::Tilde),
            '?' => Ok(TokenKind::Question),
            
            // Multi-character tokens
            '-' => self.lex_minus(),
            '=' => self.lex_equals(),
            ':' => self.lex_colon(),
            '<' => self.lex_less(),
            '>' => self.lex_greater(),
            '!' => self.lex_bang(),
            
            // Literals
            '"' => self.lex_string(),
            '\'' => self.lex_char_or_byte(),
            
            // Numbers
            c if c.is_ascii_digit() => self.lex_number(c),
            
            // Identifiers and keywords
            c if c.is_alphabetic() || c == '_' => self.lex_identifier(c),
            
            _ => Err(LexError::UnexpectedCharacter(c, self.line, self.column)),
        }
    }

    fn lex_minus(&mut self) -> Result<TokenKind, LexError> {
        match self.peek() {
            Some('>') => {
                self.advance();
                Ok(TokenKind::Arrow)
            }
            _ => Ok(TokenKind::Minus),
        }
    }

    fn lex_equals(&mut self) -> Result<TokenKind, LexError> {
        match self.peek() {
            Some('=') => {
                self.advance();
                Ok(TokenKind::Eq)
            }
            Some('>') => {
                self.advance();
                Ok(TokenKind::FatArrow)
            }
            _ => Ok(TokenKind::Assign),
        }
    }

    fn lex_colon(&mut self) -> Result<TokenKind, LexError> {
        match self.peek() {
            Some('=') => {
                self.advance();
                Ok(TokenKind::ColonEq)
            }
            _ => Ok(TokenKind::Colon),
        }
    }

    fn lex_less(&mut self) -> Result<TokenKind, LexError> {
        match self.peek() {
            Some('=') => {
                self.advance();
                Ok(TokenKind::Le)
            }
            _ => Ok(TokenKind::Lt),
        }
    }

    fn lex_greater(&mut self) -> Result<TokenKind, LexError> {
        match self.peek() {
            Some('=') => {
                self.advance();
                Ok(TokenKind::Ge)
            }
            _ => Ok(TokenKind::Gt),
        }
    }

    fn lex_bang(&mut self) -> Result<TokenKind, LexError> {
        match self.peek() {
            Some('=') => {
                self.advance();
                Ok(TokenKind::Ne)
            }
            _ => Ok(TokenKind::Bang),
        }
    }

    fn lex_string(&mut self) -> Result<TokenKind, LexError> {
        let mut value = String::new();
        
        loop {
            match self.advance() {
                None => return Err(LexError::UnterminatedString(self.line)),
                Some((_, '"')) => break,
                Some((_, '\\')) => {
                    // Handle escape sequences
                    match self.advance() {
                        Some((_, 'n')) => value.push('\n'),
                        Some((_, 't')) => value.push('\t'),
                        Some((_, 'r')) => value.push('\r'),
                        Some((_, '\\')) => value.push('\\'),
                        Some((_, '"')) => value.push('"'),
                        Some((_, c)) => {
                            return Err(LexError::InvalidEscape(c, self.line));
                        }
                        None => return Err(LexError::UnterminatedString(self.line)),
                    }
                }
                Some((_, c)) => value.push(c),
            }
        }
        
        Ok(TokenKind::StringLiteral(value))
    }

    fn lex_char_or_byte(&mut self) -> Result<TokenKind, LexError> {
        // TODO: Implement char/byte literals
        Err(LexError::NotImplemented("char/byte literals"))
    }

    fn lex_number(&mut self, first: char) -> Result<TokenKind, LexError> {
        let mut value = String::from(first);
        
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                self.advance();
                value.push(c);
            } else if c == '.' {
                // Float literal
                self.advance();
                value.push('.');
                while let Some(c) = self.peek() {
                    if c.is_ascii_digit() {
                        self.advance();
                        value.push(c);
                    } else {
                        break;
                    }
                }
                let f: f64 = value.parse().map_err(|_| {
                    LexError::InvalidNumber(value.clone(), self.line)
                })?;
                return Ok(TokenKind::FloatLiteral(f));
            } else {
                break;
            }
        }
        
        let n: i64 = value.parse().map_err(|_| {
            LexError::InvalidNumber(value.clone(), self.line)
        })?;
        Ok(TokenKind::IntLiteral(n))
    }

    fn lex_identifier(&mut self, first: char) -> Result<TokenKind, LexError> {
        let mut value = String::from(first);
        
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
                value.push(c);
            } else {
                break;
            }
        }
        
        // Check for keywords
        let kind = match value.as_str() {
            // Types
            "unit" => TokenKind::KwUnit,
            "bool" => TokenKind::KwBool,
            "int" => TokenKind::KwInt,
            "float" => TokenKind::KwFloat,
            "string" => TokenKind::KwString,
            "bytes" => TokenKind::KwBytes,
            
            // Control
            "if" => TokenKind::KwIf,
            "then" => TokenKind::KwThen,
            "else" => TokenKind::KwElse,
            "match" => TokenKind::KwMatch,
            "with" => TokenKind::KwWith,
            "let" => TokenKind::KwLet,
            "in" => TokenKind::KwIn,
            "fn" => TokenKind::KwFn,
            "return" => TokenKind::KwReturn,
            
            // Effects
            "effect" => TokenKind::KwEffect,
            "perform" => TokenKind::KwPerform,
            "handle" => TokenKind::KwHandle,
            "resume" => TokenKind::KwResume,
            
            // Security
            "public" => TokenKind::KwPublic,
            "secret" => TokenKind::KwSecret,
            "classify" => TokenKind::KwClassify,
            "declassify" => TokenKind::KwDeclassify,
            "prove" => TokenKind::KwProve,
            
            // Capabilities
            "require" => TokenKind::KwRequire,
            "grant" => TokenKind::KwGrant,
            "cap" => TokenKind::KwCap,
            
            // Booleans
            "true" => TokenKind::BoolLiteral(true),
            "false" => TokenKind::BoolLiteral(false),
            
            // Type identifier (starts with uppercase)
            _ if value.chars().next().unwrap().is_uppercase() => {
                TokenKind::TypeIdentifier(value)
            }
            
            // Regular identifier
            _ => TokenKind::Identifier(value),
        };
        
        Ok(kind)
    }
}
