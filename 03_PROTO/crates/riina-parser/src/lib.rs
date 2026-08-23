// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA Parser
//!
//! Parses token streams into ASTs defined in `riina-types`.
//! RIINA = Rigorous Immutable Invariant, No Assumptions
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

pub mod modules;

use riina_lexer::{Lexer, Span, Token, TokenKind};
use riina_types::Span as AstSpan;
use riina_types::{
    BinOp, CapabilityKind, Effect, Expr, ExternDecl, Ident, Import, Linearity, Program, Sanitizer,
    SecurityLevel, SessionType, SpannedDecl, TaintSource, TopLevelDecl, Ty,
};
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
    InvalidSessionType,
    /// Expression/grouping nesting exceeded the parser's depth limit. Returned
    /// instead of letting deeply nested input (e.g. `((((…`) overflow the stack
    /// — a denial-of-service guard on untrusted input (REQ-30).
    NestingTooDeep,
    /// `putus`/`lanjut` used outside any `selagi`/`ulang` body. Reported rather
    /// than ignored: until 2026-08 both desugared to `()` anywhere they appeared,
    /// so a misplaced loop-control statement silently did nothing.
    LoopControlOutsideLoop(&'static str),
    /// `biar ubah sekali/paling/mesti x` — a mutable slot with a linearity
    /// qualifier. The two do not combine ("use exactly once" vs "assign
    /// repeatedly"), and a slot carries no linearity, so this is reported
    /// rather than silently dropping the qualifier.
    MutWithLinearity,
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
            ParseErrorKind::InvalidSessionType => write!(f, "Invalid session type"),
            ParseErrorKind::NestingTooDeep => write!(f, "Expression nesting too deep"),
            ParseErrorKind::LoopControlOutsideLoop(kw) => write!(
                f,
                "`{kw}` is only valid inside a `selagi` or `ulang` loop body"
            ),
            ParseErrorKind::MutWithLinearity => write!(
                f,
                "`ubah` cannot be combined with a linearity qualifier"
            ),
        }
    }
}

impl ParseErrorKind {
    /// Return an error code for this parse error.
    #[must_use]
    pub fn error_code(&self) -> &'static str {
        match self {
            ParseErrorKind::UnexpectedToken(_) => "P0001",
            ParseErrorKind::UnexpectedEof => "P0002",
            ParseErrorKind::ExpectedIdentifier => "P0003",
            ParseErrorKind::ExpectedType => "P0004",
            ParseErrorKind::ExpectedExpression => "P0005",
            ParseErrorKind::InvalidSecurityLevel => "P0006",
            ParseErrorKind::InvalidEffect => "P0007",
            ParseErrorKind::InvalidSessionType => "P0008",
            ParseErrorKind::NestingTooDeep => "P0009",
            ParseErrorKind::LoopControlOutsideLoop(_) => "P0010",
            ParseErrorKind::MutWithLinearity => "P0011",
        }
    }

    /// Return a fix hint for this parse error.
    #[must_use]
    pub fn fix_hint(&self) -> Option<String> {
        Some(match self {
            ParseErrorKind::UnexpectedToken(tok) => {
                format!("Unexpected {:?}. Check for missing semicolons, braces, or parentheses", tok)
            }
            ParseErrorKind::UnexpectedEof => {
                "Unexpected end of file. Check for unclosed braces {{ }}, parentheses (), or missing semicolons".to_string()
            }
            ParseErrorKind::ExpectedIdentifier => {
                "Expected a name (identifier). Variable and function names must start with a letter or underscore".to_string()
            }
            ParseErrorKind::ExpectedType => {
                "Expected a type. Valid types: Nombor, Teks, Benar, Kosong, Rahsia<T>, Senarai<T>, (T1, T2)".to_string()
            }
            ParseErrorKind::ExpectedExpression => {
                "Expected an expression. This can be a value (42, \"hello\", betul), variable, function call, or operator expression".to_string()
            }
            ParseErrorKind::LoopControlOutsideLoop(kw) => {
                format!("`{kw}` needs an enclosing loop. Wrap the code in `selagi <syarat> {{ ... }}` or `ulang {{ ... }}`, or delete the `{kw}`")
            }
            ParseErrorKind::MutWithLinearity => {
                "Drop either `ubah` (for a mutable slot) or the linearity qualifier `sekali`/`paling`/`mesti` (for a use-counted binding)".to_string()
            }
            ParseErrorKind::InvalidSecurityLevel => {
                "Invalid security level. Valid levels: Awam, Dalaman, Sesi, Pengguna, Sistem, Rahsia".to_string()
            }
            ParseErrorKind::InvalidEffect => {
                "Invalid effect. Valid effects: Bersih, Ubah, Baca, Tulis, SistemFail, Rangkaian, Kripto, Rawak, Sistem, Masa, Proses".to_string()
            }
            ParseErrorKind::InvalidSessionType => {
                "Invalid session type. Valid: Send<T, S>, Recv<T, S>, Select<S1, S2>, Branch<S1, S2>, End, Rec<X, S>, Var<X>".to_string()
            }
            ParseErrorKind::NestingTooDeep => {
                "Expression/grouping nesting is too deep. Deeply nested input like ((((… can exhaust the stack; reduce the nesting depth".to_string()
            }
        })
    }
}

#[derive(Clone)]
struct LexerIter<'a> {
    lexer: Lexer<'a>,
}

impl Iterator for LexerIter<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next_token().ok()
    }
}

/// Maximum expression/grouping nesting depth before the parser fails with
/// [`ParseErrorKind::NestingTooDeep`]. The recursive-descent parser would
/// otherwise overflow the stack on adversarial input (`((((…`) — a SIGABRT/SIGSEGV
/// rather than a catchable error.
///
/// The value is chosen to be safe on a **default 2 MiB thread stack** (Rust's
/// `std::thread` default — smaller than the 8 MiB main thread), since the parser
/// is a library others may call off-thread: the per-level frames are large
/// (~8 KiB), so 256 levels overflow a 2 MiB stack while 100 leaves comfortable
/// margin (~1 MiB). No hand-written or generated RIINA nests expressions
/// anywhere near this deep. REQ-30 (found by the fuzz-robustness harness).
const MAX_EXPR_DEPTH: usize = 100;

pub struct Parser<'a> {
    lexer: Peekable<LexerIter<'a>>,
    current_span: Span,
    /// Current expression-nesting depth (incremented per `parse_expr`); bounded
    /// by [`MAX_EXPR_DEPTH`] to keep untrusted input from overflowing the stack.
    depth: usize,
    /// Counter for generating fresh, capture-free variable names during
    /// desugaring (e.g. `padan` compilation). See [`Parser::fresh_var`].
    gensym: usize,
    /// A "virtual" closing `>` left over after splitting a `>>` (Shr) token while
    /// closing nested generic type arguments (e.g. `Mungkin<Senarai<Nombor>>`).
    /// When set, the next [`Parser::consume_type_close`] consumes it without
    /// advancing the real token stream.
    pending_gt: bool,
    /// Top-level decls flattened out of `modul Name { ... }` blocks, queued to
    /// be returned by `parse_top_level_decl` before resuming the token stream.
    /// A module function `fungsi f` becomes a top-level `Name_f` so the existing
    /// `Name::f` -> `Name_f` qualified-call resolution finds it.
    pending_decls: Vec<TopLevelDecl>,
    /// Sibling modules named by a single-segment `guna <name>;` (REQ-71).
    /// A multi-segment path (`guna std::teks;`) names the builtin namespace,
    /// has no file behind it, and is deliberately NOT recorded here.
    imports: Vec<Import>,
    /// Top-level names introduced with the `awam` (pub) visibility keyword.
    /// Everything else is module-private to the file that declares it.
    public_names: Vec<Ident>,
    /// Set while parsing the declaration that directly follows an `awam`, so
    /// the name is captured wherever the decl parser finally produces it.
    pending_pub: bool,
    /// Lexical binding stack, innermost last, recording whether each name was
    /// introduced with `ubah`. Consulted to decide whether a name read is a
    /// plain [`Expr::Var`] or a mutable-slot read, and whether `x = e;` is a
    /// slot write or the legacy shadowing rebind. A shadowing immutable binding
    /// pushes `(name, false)`, so an inner `biar x` correctly hides an outer
    /// `biar ubah x`.
    binding_scope: Vec<(Ident, bool)>,
    /// Number of `selagi`/`ulang` bodies currently open. `putus`/`lanjut` are
    /// only meaningful inside one, so a zero depth turns them into a parse error
    /// instead of a silently-ignored statement (which is what they were until
    /// 2026-08 — both desugared to `()`).
    ///
    /// A `untuk` body deliberately does NOT raise this. `untuk` desugars to
    /// `senarai_peta` over a closure, and neither the interpreter's builtin nor
    /// the C runtime's can honour a break or a continue raised inside it — so
    /// `putus` there is rejected rather than accepted and ignored.
    loop_depth: usize,
}

/// A surface match pattern, used only during `padan` compilation. The AST has
/// no pattern node; [`Parser::compile_match`] lowers these to core `Expr`.
#[derive(Debug, Clone)]
enum Pattern {
    /// `_` — matches anything, binds nothing.
    Wildcard,
    /// A variable binding — matches anything, binds the name.
    Var(Ident),
    /// Integer literal pattern.
    Int(u64),
    /// Boolean literal pattern.
    Bool(bool),
    /// String literal pattern.
    Str(String),
    /// Tuple pattern `(p1, p2, ...)`.
    Tuple(Vec<Pattern>),
    /// List pattern `[p0, p1, ...]` with an optional rest binding `..name`
    /// (`tail` is `Some(name)` for `[a, b, ..rest]`, `None` for a fixed-length
    /// `[a, b]`). An empty fixed list `[]` is `elems = [], tail = None`.
    List {
        elems: Vec<Pattern>,
        tail: Option<Ident>,
    },
    /// Left-injection constructor (`Some`/`Ada`/`Ok`/`Jadi`/`inl`) with payload.
    CtorLeft(Box<Pattern>),
    /// Right-injection constructor (`None`/`Tiada`/`Err`/`Gagal`/`Ralat`/`inr`)
    /// with payload.
    CtorRight(Box<Pattern>),
    /// Reference pattern `ruj(p)`: matches a reference, testing/binding the inner
    /// pattern `p` against the dereferenced value.
    Ref(Box<Pattern>),
    /// Named (nominal-enum) constructor pattern `C(p0, p1, ...)` or nullary `C`.
    /// Matches a structurally-tagged value `("C", payload)`: tests the tag string
    /// and binds the argument pattern(s) against the payload.
    NamedCtor { name: String, args: Vec<Pattern> },
}

/// One arm of a `padan` expression: a pattern, an optional `kalau` guard, and a
/// body expression.
#[derive(Debug, Clone)]
struct MatchArm {
    pattern: Pattern,
    guard: Option<Expr>,
    body: Expr,
}

/// Map a lexed integer width suffix (`u8`..`u64`, `i8`..`i64`) to its
/// `(bits, signed)`. The lexer (`peek_int_suffix`) only ever attaches one of
/// these eight suffixes and already range-checked the magnitude, so this is the
/// total inverse used when building a sized-integer literal (`Expr::IntN`).
fn int_suffix_to_width(suffix: &str) -> Option<(u8, bool)> {
    match suffix {
        "u8" => Some((8, false)),
        "u16" => Some((16, false)),
        "u32" => Some((32, false)),
        "u64" => Some((64, false)),
        "i8" => Some((8, true)),
        "i16" => Some((16, true)),
        "i32" => Some((32, true)),
        "i64" => Some((64, true)),
        _ => None,
    }
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            lexer: LexerIter {
                lexer: Lexer::new(source),
            }
            .peekable(),
            current_span: Span { start: 0, end: 0 },
            depth: 0,
            gensym: 0,
            pending_gt: false,
            pending_decls: Vec::new(),
            imports: Vec::new(),
            public_names: Vec::new(),
            pending_pub: false,
            binding_scope: Vec::new(),
            loop_depth: 0,
        }
    }

    /// Consume a closing `>` of a generic type-argument list, transparently
    /// handling a `>>` (Shr) token that closes two nesting levels at once
    /// (e.g. `Mungkin<Senarai<Nombor>>`). The lexer emits a single `Shr` for two
    /// adjacent `>`; the first call splits it (consuming the `Shr` and leaving a
    /// pending `>`), and the next call consumes the pending half.
    fn consume_type_close(&mut self) -> Result<(), ParseError> {
        if self.pending_gt {
            self.pending_gt = false;
            return Ok(());
        }
        match self.peek().map(|t| &t.kind) {
            Some(TokenKind::Shr) => {
                // `>>` closes two angle-bracket levels: consume the token, mark
                // the second `>` pending for the enclosing generic's close.
                self.next();
                self.pending_gt = true;
                Ok(())
            }
            _ => self.consume(TokenKind::Gt).map(|_| ()),
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        // Depth guard (REQ-30): every nested grouping `(e)`, block, argument,
        // etc. re-enters here, so bounding `parse_expr` bounds the recursion and
        // turns a stack-overflow on adversarial input into a clean error.
        self.depth += 1;
        if self.depth > MAX_EXPR_DEPTH {
            self.depth -= 1;
            return Err(ParseError {
                kind: ParseErrorKind::NestingTooDeep,
                span: self.current_span,
            });
        }
        let result = self.parse_stmt_sequence();
        self.depth -= 1;
        result
    }

    /// Parse a complete .rii file as a sequence of top-level declarations.
    pub fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut decls = Vec::new();
        let mut spans = Vec::new();
        while self.peek().map(|t| &t.kind) != Some(&TokenKind::Eof) && self.peek().is_some() {
            let start = self.peek().map(|t| t.span.start).unwrap_or(0);
            let decl = self.parse_top_level_decl()?;
            let end = self.current_span.end;
            let name_span = match &decl {
                TopLevelDecl::Function { .. } | TopLevelDecl::Binding { .. } => {
                    // Name span recorded during parsing via current_span after ident
                    None // Will be filled in by enhanced parse methods below
                }
                TopLevelDecl::Expr(_)
                | TopLevelDecl::ExternBlock { .. }
                | TopLevelDecl::Test { .. } => None,
            };
            spans.push(SpannedDecl {
                decl: decl.clone(),
                span: AstSpan::new(start, end),
                name_span,
            });
            decls.push(decl);
        }
        Ok(Program::with_modules(
            decls,
            spans,
            std::mem::take(&mut self.imports),
            std::mem::take(&mut self.public_names),
        ))
    }

    /// Continue parsing the next top-level declaration after a skipped one
    /// (module/use/etc.). If the input is exhausted, yield a Unit expression
    /// declaration instead of recursing into `parse_top_level_decl` (which would
    /// try to parse an expression from EOF and fail).
    fn parse_next_decl_or_unit(&mut self) -> Result<TopLevelDecl, ParseError> {
        if matches!(
            self.peek().map(|t| &t.kind),
            Some(TokenKind::Eof) | None
        ) {
            return Ok(TopLevelDecl::Expr(Box::new(Expr::Unit)));
        }
        self.parse_top_level_decl()
    }

    fn parse_top_level_decl(&mut self) -> Result<TopLevelDecl, ParseError> {
        // Drain any decls flattened out of a `modul { ... }` block first.
        if !self.pending_decls.is_empty() {
            return Ok(self.pending_decls.remove(0));
        }
        match self.peek().map(|t| &t.kind) {
            Some(TokenKind::KwMod) => {
                // Module declaration. `modul name;` (forward decl) is skipped.
                // `modul name { ...decls }` is FLATTENED: each inner `fungsi f`
                // becomes a top-level `name_f` so the existing `name::f` ->
                // `name_f` qualified-call resolution (parse_module_path) finds
                // the user definition. Non-function inner items are skipped
                // (struct/enum/let have no top-level semantics yet).
                self.consume(TokenKind::KwMod)?;
                let modname = self.parse_ident()?;
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LBrace)) {
                    self.consume(TokenKind::LBrace)?;
                    while !matches!(
                        self.peek().map(|t| &t.kind),
                        Some(TokenKind::RBrace) | None
                    ) {
                        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwFn)) {
                            let decl = self.parse_function_decl()?;
                            if let TopLevelDecl::Function {
                                name,
                                params,
                                return_ty,
                                effect,
                                effect_set,
                                body,
                            } = decl
                            {
                                self.pending_decls.push(TopLevelDecl::Function {
                                    name: format!("{modname}_{name}"),
                                    params,
                                    return_ty,
                                    effect,
                                    effect_set,
                                    body,
                                });
                            }
                        } else {
                            // Skip a non-function inner item up to the next
                            // top-level boundary within the module.
                            self.next();
                        }
                    }
                    self.consume(TokenKind::RBrace)?;
                } else {
                    self.consume(TokenKind::Semi)?;
                }
                self.parse_next_decl_or_unit()
            }
            Some(TokenKind::KwUse) => {
                // `guna <name>;`            — import the sibling file <name>.rii (REQ-71).
                // `guna a::b;` / `guna std::teks;` — the BUILTIN namespace: no file
                //   behind it, so it is consumed and not recorded. This is what
                //   keeps every pre-module-system example (`guna std::senarai;`)
                //   compiling unchanged.
                self.consume(TokenKind::KwUse)?;
                let first = self.peek().and_then(|t| match &t.kind {
                    TokenKind::Identifier(n) => Some(n.clone()),
                    _ => None,
                });
                let name_span = self.peek().map(|t| t.span).unwrap_or(self.current_span);
                let mut segments = 0usize;
                while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Semi) | None) {
                    if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::ColonColon)) {
                        segments += 1;
                    }
                    self.next();
                }
                self.consume(TokenKind::Semi)?;
                if segments == 0 {
                    if let Some(module) = first {
                        // Deduplicate: importing the same module twice is
                        // harmless, and the resolver loads each file once.
                        if !self.imports.iter().any(|i| i.module == module) {
                            self.imports.push(Import {
                                module,
                                span: AstSpan::new(name_span.start, name_span.end),
                            });
                        }
                    }
                }
                self.parse_next_decl_or_unit()
            }
            Some(TokenKind::KwStruct) | Some(TokenKind::KwEnum) => {
                // bentuk/pilihan — skip declaration (no struct/enum semantics yet)
                self.next(); // consume KwStruct or KwEnum
                let _name = self.parse_ident()?;
                self.consume(TokenKind::LBrace)?;
                self.skip_balanced_braces();
                self.parse_next_decl_or_unit()
            }
            Some(TokenKind::KwType) => {
                // jenis — skip type/record declaration (no nominal type semantics
                // yet; the typechecker infers structurally). Forms handled:
                //   jenis Name { ... }
                //   jenis Name<T, ...> { ... }
                //   jenis Name            (marker type, no body)
                self.next(); // consume KwType
                let _name = self.parse_ident()?;
                // Optional generic parameter list `<...>` — skip balanced angles.
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Lt)) {
                    self.next();
                    let mut depth = 1u32;
                    while depth > 0 {
                        match self.peek().map(|t| &t.kind) {
                            Some(TokenKind::Lt) => {
                                self.next();
                                depth += 1;
                            }
                            Some(TokenKind::Gt) => {
                                self.next();
                                depth -= 1;
                            }
                            // Terminate at Eof (lexer repeats Eof, never None) so
                            // unclosed `<` doesn't loop forever (REQ-30).
                            Some(TokenKind::Eof) | None => break,
                            _ => {
                                self.next();
                            }
                        }
                    }
                }
                match self.peek().map(|t| &t.kind) {
                    // Record body: `jenis Name { ... }`
                    Some(TokenKind::LBrace) => {
                        self.next();
                        self.skip_balanced_braces();
                    }
                    // Type alias: `jenis Name = SomeType;` — skip to the `;`.
                    Some(TokenKind::Eq) => {
                        self.next();
                        while !matches!(
                            self.peek().map(|t| &t.kind),
                            Some(TokenKind::Semi) | None
                        ) {
                            self.next();
                        }
                        let _ = self.consume(TokenKind::Semi);
                    }
                    // Marker type with no body: `jenis Name`
                    _ => {}
                }
                self.parse_next_decl_or_unit()
            }
            Some(TokenKind::KwChoreography) => self.parse_choreography(),
            Some(TokenKind::KwActor) => self.parse_actor_decl(),
            Some(TokenKind::KwTest) => self.parse_test_block(),
            Some(TokenKind::KwExtern) => self.parse_extern_block(),
            Some(TokenKind::KwPub) => {
                // `awam fungsi ...` — consume the visibility keyword, then let
                // the normal decl parser run with `pending_pub` set so whatever
                // name it produces is recorded as public (REQ-71). Delegating
                // (rather than special-casing `fungsi` here) keeps `awam` working
                // for every decl form the parser already supports.
                self.consume(TokenKind::KwPub)?;
                self.pending_pub = true;
                let decl = self.parse_next_decl_or_unit();
                self.pending_pub = false;
                if let Ok(d) = &decl {
                    match d {
                        TopLevelDecl::Function { name, .. }
                        | TopLevelDecl::Binding { name, .. } => {
                            if !self.public_names.contains(name) {
                                self.public_names.push(name.clone());
                            }
                        }
                        TopLevelDecl::Expr(_)
                        | TopLevelDecl::ExternBlock { .. }
                        | TopLevelDecl::Test { .. } => {}
                    }
                }
                decl
            }
            Some(TokenKind::KwFn) => self.parse_function_decl(),
            Some(TokenKind::KwLet) => {
                self.consume(TokenKind::KwLet)?;
                // Optional `ubah` (mut) modifier: a top-level mutable slot,
                // exactly as inside a function.
                let is_mut = matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwMut));
                if is_mut {
                    self.consume(TokenKind::KwMut)?;
                }
                let name = self.parse_binding_name()?;
                // Optional type annotation `biar x: T = e` (parsed and discarded;
                // type is inferred). Mirrors the in-function binding form.
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Colon)) {
                    self.consume(TokenKind::Colon)?;
                    let _annotated_ty = self.parse_ty()?;
                }
                self.consume(TokenKind::Eq)?;
                let value = self.parse_control_flow()?;
                self.consume(TokenKind::Semi)?;
                // A top-level binding scopes over every declaration that
                // follows, so it stays on the scope stack (nothing pops it).
                self.binding_scope.push((name.clone(), is_mut));
                Ok(TopLevelDecl::Binding {
                    name,
                    value: Box::new(value),
                    is_mut,
                })
            }
            _ => {
                let expr = self.parse_expr()?;
                Ok(TopLevelDecl::Expr(Box::new(expr)))
            }
        }
    }

    fn parse_function_decl(&mut self) -> Result<TopLevelDecl, ParseError> {
        self.consume(TokenKind::KwFn)?;
        let mut name = self.parse_ident()?;
        // A qualified method-style definition name `Type::method` resolves to the
        // flat builtin name `Type_method` for a lowercase module, or to the final
        // segment for a capitalized namespace — matching how `::` call sites
        // resolve (see `parse_module_path`), so definitions and calls line up.
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::ColonColon)) {
            name = self.parse_module_path(name)?;
        }
        // Optional generic parameter list `<T>`, `<E, T>`, `<T1, T2>`, etc.
        // RIINA's type system is monomorphic at this layer; generic parameters
        // carry no semantics yet, so the list is skipped (balanced-angle aware,
        // so bounds like `<T: Sifat>` and nested `<Map<K, V>>` are consumed).
        self.skip_type_argument_list();
        self.consume(TokenKind::LParen)?;
        let params = self.parse_param_list()?;
        self.consume(TokenKind::RParen)?;

        // Optional return type. `-> kesan <eff>` (an arrow immediately followed
        // by the effect keyword) denotes a Unit return with only an effect
        // annotation, so the arrow consumes no type in that case.
        let return_ty = if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Arrow)) {
            self.consume(TokenKind::Arrow)?;
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwEffect)) {
                Ty::Unit
            } else {
                self.parse_ty()?
            }
        } else {
            Ty::Unit
        };

        // Optional effect annotation
        let (effect, effect_set) =
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwEffect)) {
                self.consume(TokenKind::KwEffect)?;
                self.parse_effect_annotation()?
            } else {
                (Effect::Pure, vec![Effect::Pure])
            };

        // Body in braces. Parameters shadow any outer `biar ubah` of the same
        // name, so a parameter read stays a plain `Var`.
        self.consume(TokenKind::LBrace)?;
        let scope: Vec<(Ident, bool)> = params.iter().map(|(n, _)| (n.clone(), false)).collect();
        let body = self.with_bindings(&scope, Self::parse_expr)?;
        self.consume(TokenKind::RBrace)?;

        Ok(TopLevelDecl::Function {
            name,
            params,
            return_ty,
            effect,
            effect_set,
            body: Box::new(body),
        })
    }

    /// Parse: luaran "C" { fungsi name(params) -> ret_ty; ... }
    /// Parse: ujian "name" { body }
    fn parse_test_block(&mut self) -> Result<TopLevelDecl, ParseError> {
        self.consume(TokenKind::KwTest)?;
        // Expect test name as string literal
        let name = match self.peek().map(|t| t.kind.clone()) {
            Some(TokenKind::LiteralString(s)) => {
                self.next();
                s
            }
            _ => {
                return Err(ParseError {
                    kind: ParseErrorKind::ExpectedExpression,
                    span: self.current_span,
                });
            }
        };
        self.consume(TokenKind::LBrace)?;
        let body = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;
        Ok(TopLevelDecl::Test {
            name,
            body: Box::new(body),
        })
    }

    fn parse_extern_block(&mut self) -> Result<TopLevelDecl, ParseError> {
        self.consume(TokenKind::KwExtern)?;
        // Expect ABI string literal "C"
        let abi = match self.peek().map(|t| t.kind.clone()) {
            Some(TokenKind::LiteralString(s)) => {
                self.next();
                s
            }
            _ => {
                return Err(ParseError {
                    kind: ParseErrorKind::ExpectedExpression,
                    span: self.current_span,
                });
            }
        };
        self.consume(TokenKind::LBrace)?;
        let mut decls = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBrace) | None) {
            self.consume(TokenKind::KwFn)?;
            let name = self.parse_ident()?;
            self.consume(TokenKind::LParen)?;
            let params = self.parse_param_list()?;
            self.consume(TokenKind::RParen)?;
            let ret_ty = if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Arrow)) {
                self.consume(TokenKind::Arrow)?;
                self.parse_ty()?
            } else {
                Ty::Unit
            };
            self.consume(TokenKind::Semi)?;
            decls.push(ExternDecl {
                name,
                params,
                ret_ty,
                effect: Effect::System,
            });
        }
        self.consume(TokenKind::RBrace)?;
        Ok(TopLevelDecl::ExternBlock { abi, decls })
    }

    fn parse_param_list(&mut self) -> Result<Vec<(Ident, Ty)>, ParseError> {
        let mut params = Vec::new();
        if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
            // Optional mut/ubah modifier (ignored for now)
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwMut)) {
                self.consume(TokenKind::KwMut)?;
            }
            let name = self.parse_binding_name()?;
            self.consume(TokenKind::Colon)?;
            let ty = self.parse_ty()?;
            params.push((name, ty));

            while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                self.consume(TokenKind::Comma)?;
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwMut)) {
                    self.consume(TokenKind::KwMut)?;
                }
                let name = self.parse_binding_name()?;
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
        // Local (nested) function declaration: `fungsi f(..) -> T { .. }` in
        // statement position. Desugars to a recursive `LetRec` binding whose
        // continuation is the rest of the sequence, mirroring how top-level
        // functions desugar. Distinguished from a lambda (`fn(x: T) body`) by a
        // *named* head: `fn`/`fungsi` immediately followed by an identifier.
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwFn))
            && self.next_is_named_fn()
        {
            let decl = self.parse_function_decl()?;
            let (name, params, return_ty, effect, body) = match decl {
                TopLevelDecl::Function {
                    name,
                    params,
                    return_ty,
                    effect,
                    body,
                    ..
                } => (name, params, return_ty, effect, body),
                _ => unreachable!("parse_function_decl returns Function"),
            };
            let continuation = if self.at_sequence_end() {
                Expr::Var(name.clone())
            } else {
                self.parse_stmt_sequence()?
            };
            // Build the curried lambda and its function type through the SAME
            // helper top-level declarations use. This was a third hand-rolled
            // copy of the fold, and it diverged: when zero-parameter functions
            // gained a synthesised `()` parameter (REQ-68) a NESTED zero-arg
            // `fungsi` kept the old thunk shape here, so calling it applied a
            // non-function.
            let (lam, fn_ty) = riina_types::desugar_function(params, return_ty, effect, body);
            return Ok(Expr::LetRec(
                name,
                fn_ty,
                Box::new(lam),
                Box::new(continuation),
            ));
        }

        // Check if this is a let-binding
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwLet)) {
            self.consume(TokenKind::KwLet)?;
            // Optional `ubah` (mut) modifier: `biar ubah x = e` binds a real
            // mutable slot (see `Expr::LetMut`). Without it the binding is
            // immutable, as before.
            let is_mut = matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwMut));
            if is_mut {
                self.consume(TokenKind::KwMut)?;
            }
            let linearity = match self.peek().map(|t| &t.kind) {
                Some(TokenKind::KwSekali) => {
                    self.next();
                    Some(Linearity::Linear)
                }
                Some(TokenKind::KwPaling) => {
                    self.next();
                    Some(Linearity::Affine)
                }
                Some(TokenKind::KwMesti) => {
                    self.next();
                    Some(Linearity::Relevant)
                }
                _ => None,
            };
            // Tuple-destructuring binding: `biar (a, b, ...) = e; rest`. Binds a
            // fresh temp to `e`, then projects each name via Fst/Snd (left-nested
            // pairs, matching how tuples are constructed). Nested patterns are not
            // supported here — only a flat list of identifiers.
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
                self.consume(TokenKind::LParen)?;
                let mut names = vec![self.parse_ident()?];
                while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                    self.consume(TokenKind::Comma)?;
                    names.push(self.parse_ident()?);
                }
                self.consume(TokenKind::RParen)?;
                self.consume(TokenKind::Eq)?;
                let e1 = self.parse_control_flow()?;
                self.consume(TokenKind::Semi)?;
                let scope: Vec<(Ident, bool)> =
                    names.iter().map(|n| (n.clone(), false)).collect();
                let body = self.with_bindings(&scope, |p| {
                    if p.at_sequence_end() {
                        Ok(Expr::Unit)
                    } else {
                        p.parse_stmt_sequence()
                    }
                })?;
                let tmp = self.fresh_var("padTup");
                // Bind the names from the temp via Fst/Snd projection; the last
                // element is the final `Snd` of the left-nested pair chain.
                let mut bound = body;
                let n = names.len();
                for (i, nm) in names.iter().enumerate().rev() {
                    let proj = self.tuple_proj(&tmp, i, n);
                    bound = Expr::Let(nm.clone(), None, Box::new(proj), Box::new(bound));
                }
                return Ok(Expr::Let(tmp, linearity, Box::new(e1), Box::new(bound)));
            }
            let name = self.parse_binding_name()?;
            // Optional type annotation: `biar x: T = e`. Accepted for ergonomics
            // and documentation; the binding's type is inferred by the
            // typechecker, so the parsed `Ty` is intentionally discarded (the
            // Let AST node carries no annotation slot).
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Colon)) {
                self.consume(TokenKind::Colon)?;
                let _annotated_ty = self.parse_ty()?;
            }
            self.consume(TokenKind::Eq)?;
            let e1 = self.parse_control_flow()?;
            self.consume(TokenKind::Semi)?;
            // A trailing binding with nothing after it (`biar x = e;` then `}`/EOF)
            // yields Unit as the block's value. The name is in scope for the rest
            // of the sequence, shadowing any outer binding of the same name.
            let e2 = self.with_bindings(&[(name.clone(), is_mut)], |p| {
                if p.at_sequence_end() {
                    Ok(Expr::Unit)
                } else {
                    p.parse_stmt_sequence()
                }
            })?;
            if is_mut {
                // A slot has no linearity slot to carry, and "use exactly once"
                // does not combine with "assign repeatedly" anyway. Reject the
                // pair rather than silently dropping the qualifier.
                if linearity.is_some() {
                    return Err(ParseError {
                        kind: ParseErrorKind::MutWithLinearity,
                        span: self.current_span,
                    });
                }
                return Ok(Expr::LetMut(name, Box::new(e1), Box::new(e2)));
            }
            return Ok(Expr::Let(name, linearity, Box::new(e1), Box::new(e2)));
        }

        // Statement-position assignment: `x = e;`.
        //
        // For a `biar ubah` name this is a real slot write, visible to every
        // later read of `x` — including reads OUTSIDE the enclosing block, which
        // is the whole point: `kalau c { jumlah = jumlah + 1; }` inside a loop
        // has to accumulate.
        //
        // For any other name it keeps the historical meaning — rebinding `x`
        // (shadowing) for the rest of this sequence. That is observationally
        // equivalent for straight-line code and keeps programs that never say
        // `ubah` working exactly as before, but it does NOT escape the block, so
        // `biar ubah` is the form to reach for.
        //
        // Detected as `ident =` where the next token is a single `=` (not `==`).
        // Field/element assignments (`obj.f = e`) fall through to normal parsing.
        if let Some(name) = self.peek_simple_reassignment() {
            self.parse_ident()?; // consume the name
            self.consume(TokenKind::Eq)?;
            let value = self.parse_control_flow()?;
            self.consume(TokenKind::Semi)?;
            if self.is_slot(&name) {
                let rest = if self.at_sequence_end() {
                    Expr::Unit
                } else {
                    self.parse_stmt_sequence()?
                };
                return Ok(Expr::Let(
                    "_".to_string(),
                    None,
                    Box::new(Expr::SlotSet(name, Box::new(value))),
                    Box::new(rest),
                ));
            }
            let rest = self.with_bindings(&[(name.clone(), false)], |p| {
                if p.at_sequence_end() {
                    Ok(Expr::Var(name.clone()))
                } else {
                    p.parse_stmt_sequence()
                }
            })?;
            return Ok(Expr::Let(name, None, Box::new(value), Box::new(rest)));
        }

        // A block-form statement (`kalau`/`padan`/`selagi`/`untuk`/`ulang`) may
        // be used in statement position without a trailing `;`, e.g. an
        // early-return guard `kalau c { pulang x; }` followed by more statements.
        // Other expressions still require a `;` to start a sequence.
        let first_is_block_form = matches!(
            self.peek().map(|t| &t.kind),
            Some(TokenKind::KwIf)
                | Some(TokenKind::KwMatch)
                | Some(TokenKind::KwWhile)
                | Some(TokenKind::KwFor)
                | Some(TokenKind::KwLoop)
        );

        let first = self.parse_control_flow()?;

        // If next token is ';', this is a statement sequence
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Semi)) {
            self.consume(TokenKind::Semi)?;
            // A trailing `;` before the block end (`expr;` then `}`/EOF) — e.g. a
            // final `pulang x;` — yields `expr` as the block's value. RIINA marks
            // returns explicitly with `pulang`, so `pulang x;}` is intended to
            // return `x`, not discard it.
            if self.at_sequence_end() {
                return Ok(first);
            }
            let rest = self.parse_stmt_sequence()?;
            Ok(Expr::Let(
                "_".to_string(),
                None,
                Box::new(first),
                Box::new(rest),
            ))
        } else if first_is_block_form && !self.at_sequence_end() {
            // No `;`, but a block-form statement is followed by more statements
            // — e.g. `kalau c { pulang x; }` (a guard) then further statements.
            // Sequence `first` (its value discarded) before the rest.
            let rest = self.parse_stmt_sequence()?;
            Ok(Expr::Let(
                "_".to_string(),
                None,
                Box::new(first),
                Box::new(rest),
            ))
        } else {
            Ok(first)
        }
    }

    /// True when the next token ends a statement sequence — a block close `}`
    /// or end of input. Used to allow a trailing `;` after the final statement.
    fn at_sequence_end(&mut self) -> bool {
        matches!(
            self.peek().map(|t| &t.kind),
            Some(TokenKind::RBrace) | Some(TokenKind::Eof) | None
        )
    }

    /// Skip a `<...>` generic argument list (the leading `<` is still on the
    /// input). Tracks `<`/`>` nesting so e.g. `Map<K, List<V>>` is consumed
    /// fully. Used for unknown nominal types where generics carry no semantics
    /// yet. `Shr` (`>>`) closes two levels at once.
    fn skip_type_argument_list(&mut self) {
        // A pending `>` (left over from a `>>` split by an enclosing generic's
        // close) accounts for this list's opening `<` having no real `<` token —
        // but here we always require a real `<`, so just clear any stale pending
        // first via the normal close path rather than special-casing it.
        if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Lt)) {
            return;
        }
        self.next(); // consume opening `<`
        let mut depth = 1u32;
        while depth > 0 {
            match self.peek().map(|t| &t.kind) {
                Some(TokenKind::Lt) => {
                    self.next();
                    depth += 1;
                }
                Some(TokenKind::Gt) => {
                    self.next();
                    depth -= 1;
                }
                Some(TokenKind::Shr) => {
                    self.next();
                    if depth >= 2 {
                        // `>>` closes two levels that both belong to this list.
                        depth -= 2;
                    } else {
                        // Only one level remains here; the second `>` belongs to
                        // an enclosing generic — leave it pending so nested types
                        // like `Peta<.., ..>>>` don't over-consume the outer `>`s.
                        depth -= 1;
                        self.pending_gt = true;
                    }
                }
                // The lexer yields `Eof` repeatedly (never `None`) at end of
                // input, so an Eof here must terminate the skip — otherwise the
                // `_` arm consumes it without progress and loops forever on
                // unclosed input like `fungsi x<` (REQ-30, fuzz-found).
                Some(TokenKind::Eof) | None => break,
                _ => {
                    self.next();
                }
            }
        }
    }

    /// Skip tokens up to and including the `}` that closes an already-consumed
    /// opening `{`. Tracks nesting so inner braces don't end the skip early.
    fn skip_balanced_braces(&mut self) {
        let mut depth = 1u32;
        while depth > 0 {
            match self.peek().map(|t| &t.kind) {
                Some(TokenKind::LBrace) => {
                    self.next();
                    depth += 1;
                }
                Some(TokenKind::RBrace) => {
                    self.next();
                    depth -= 1;
                }
                // The lexer yields `Eof` repeatedly (never `None`) at end of
                // input, so an Eof here must terminate the skip — otherwise the
                // `_` arm consumes it without progress and loops forever on
                // unclosed input like `fungsi x<` (REQ-30, fuzz-found).
                Some(TokenKind::Eof) | None => break,
                _ => {
                    self.next();
                }
            }
        }
    }

    fn peek(&mut self) -> Option<&Token> {
        self.lexer.peek()
    }

    /// True when the current position begins a record-literal body: the next
    /// token is `{` and the one after is an identifier followed by `:`. Uses a
    /// cheap clone of the token stream for two-token lookahead; this avoids
    /// misreading a control-flow block as a record. A bare `{ }` (empty record)
    /// also qualifies.
    /// If the upcoming tokens are `<identifier> =` (a simple variable
    /// reassignment, with a single `=` — not `==`, and not `ident.field =`),
    /// return the identifier name. Uses a two-token clone-based lookahead so the
    /// real stream is untouched.
    /// True when `name` currently resolves to a `biar ubah` slot.
    fn is_slot(&self, name: &str) -> bool {
        self.binding_scope
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .is_some_and(|(_, is_mut)| *is_mut)
    }

    /// Read a name: a mutable slot reads through [`Expr::SlotGet`], everything
    /// else stays an ordinary [`Expr::Var`].
    fn name_ref(&self, name: Ident) -> Expr {
        if self.is_slot(&name) {
            Expr::SlotGet(name)
        } else {
            Expr::Var(name)
        }
    }

    /// Parse `body_fn` with `names` in scope, then restore the previous scope.
    fn with_bindings<T>(
        &mut self,
        names: &[(Ident, bool)],
        body_fn: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Result<T, ParseError> {
        let mark = self.binding_scope.len();
        self.binding_scope.extend(names.iter().cloned());
        let out = body_fn(self);
        self.binding_scope.truncate(mark);
        out
    }

    fn peek_simple_reassignment(&mut self) -> Option<Ident> {
        let mut ahead = self.lexer.clone();
        let name = match ahead.next().map(|t| t.kind) {
            Some(TokenKind::Identifier(s)) => s,
            _ => return None,
        };
        match ahead.next().map(|t| t.kind) {
            Some(TokenKind::Eq) => Some(name),
            _ => None,
        }
    }

    /// True when the upcoming tokens are `fn`/`fungsi` followed by an identifier
    /// — i.e. a *named* function declaration, as opposed to a lambda
    /// (`fn(x: T) body`). Uses a cheap clone of the token stream for two-token
    /// lookahead.
    fn next_is_named_fn(&mut self) -> bool {
        let mut ahead = self.lexer.clone();
        ahead.next(); // skip `fn`/`fungsi`
        matches!(ahead.next().map(|t| t.kind), Some(TokenKind::Identifier(_)))
    }

    fn looks_like_record_literal(&mut self) -> bool {
        if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LBrace)) {
            return false;
        }
        let mut ahead = self.lexer.clone();
        ahead.next(); // skip `{`
        match ahead.next().map(|t| t.kind) {
            Some(TokenKind::RBrace) => true, // empty record `{}`
            // A field name is an identifier or a soft keyword (e.g. `tahap:`).
            Some(TokenKind::Identifier(_)) => {
                matches!(ahead.next().map(|t| t.kind), Some(TokenKind::Colon))
            }
            Some(ref k) if Self::soft_keyword_spelling(k).is_some() => {
                matches!(ahead.next().map(|t| t.kind), Some(TokenKind::Colon))
            }
            _ => false,
        }
    }

    /// Parse a record-literal body starting at the `{` (the type name has been
    /// consumed): `{ field1: e1, field2: e2, ... }`. Trailing comma allowed.
    fn parse_record_literal_body(&mut self, type_name: Ident) -> Result<Expr, ParseError> {
        self.consume(TokenKind::LBrace)?;
        let mut fields = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBrace) | None) {
            let field = self.parse_binding_name()?;
            self.consume(TokenKind::Colon)?;
            let value = self.parse_control_flow()?;
            fields.push((field, value));
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                self.consume(TokenKind::Comma)?;
            } else {
                break;
            }
        }
        self.consume(TokenKind::RBrace)?;
        Ok(Expr::RecordLit(type_name, fields))
    }

    /// Parse a qualified module path `Module::function` (the first segment is
    /// already consumed and passed as `first`). Resolves to a flat builtin name.
    ///
    /// A leading `std` segment is dropped (`std::teks::mengandungi`). A lowercase
    /// module (a type's own methods) maps to `module_function`
    /// (`teks::mengandungi` -> `teks_mengandungi`). A capitalized module (a
    /// namespace) drops the module and uses the final segment, which already
    /// carries its full builtin name (`Masa::masa_unix` -> `masa_unix`).
    ///
    /// Names that resolve to a non-existent builtin fail later at type-check with
    /// "Variable not found", which is the correct behavior.
    /// Parse a `format!("template", args...)` macro (the `format` identifier is
    /// already consumed). Desugars to string concatenation: the template is split
    /// on `{}` placeholders, and each placeholder is replaced by `ke_teks(arg)`
    /// of the corresponding positional argument. Literal `{{`/`}}` are unescaped
    /// to `{`/`}`. The result type is `Teks` (String).
    ///
    /// Example: `format!("a={} b={}", x, y)` becomes
    /// `"a=" + ke_teks(x) + " b=" + ke_teks(y) + ""`.
    fn parse_format_macro(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::Not)?;
        self.consume(TokenKind::LParen)?;
        let template = match self.peek().map(|t| t.kind.clone()) {
            Some(TokenKind::LiteralString(s)) => {
                self.next();
                s
            }
            _ => {
                return Err(ParseError {
                    kind: ParseErrorKind::UnexpectedToken(
                        self.peek().map(|t| t.kind.clone()).unwrap_or(TokenKind::Eof),
                    ),
                    span: self.current_span,
                });
            }
        };
        // Parse the (optional) positional arguments.
        let mut args = Vec::new();
        while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
            self.consume(TokenKind::Comma)?;
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                break; // trailing comma
            }
            args.push(self.parse_control_flow()?);
        }
        self.consume(TokenKind::RParen)?;

        // Split the template into literal segments around `{}` placeholders,
        // honoring `{{`/`}}` escapes.
        let mut segments: Vec<String> = Vec::new();
        let mut cur = String::new();
        let mut chars = template.chars().peekable();
        let mut placeholders = 0usize;
        while let Some(c) = chars.next() {
            match c {
                '{' if chars.peek() == Some(&'{') => {
                    chars.next();
                    cur.push('{');
                }
                '}' if chars.peek() == Some(&'}') => {
                    chars.next();
                    cur.push('}');
                }
                '{' => {
                    // Placeholder `{}` or `{name}`/`{:spec}` — skip to the `}`.
                    while let Some(&n) = chars.peek() {
                        chars.next();
                        if n == '}' {
                            break;
                        }
                    }
                    segments.push(std::mem::take(&mut cur));
                    placeholders += 1;
                }
                _ => cur.push(c),
            }
        }
        segments.push(cur);

        // Build: seg0 + ke_teks(arg0) + seg1 + ke_teks(arg1) + ... + segN.
        // `segments` has exactly `placeholders + 1` entries. Missing args (fewer
        // than placeholders) stringify the empty string; extra args are ignored.
        let mut result = Expr::String(segments[0].clone());
        for (i, seg) in segments.iter().enumerate().skip(1) {
            // Insert the stringified argument for the placeholder before this seg.
            let arg_expr = match args.get(i - 1) {
                Some(a) => Expr::App(
                    Box::new(Expr::Var("ke_teks".to_string())),
                    Box::new(a.clone()),
                ),
                None => Expr::String(String::new()),
            };
            result = Expr::BinOp(BinOp::Add, Box::new(result), Box::new(arg_expr));
            result = Expr::BinOp(
                BinOp::Add,
                Box::new(result),
                Box::new(Expr::String(seg.clone())),
            );
        }
        let _ = placeholders;
        Ok(result)
    }

    fn parse_module_path(&mut self, first: Ident) -> Result<Ident, ParseError> {
        let mut segments = vec![first];
        while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::ColonColon)) {
            self.consume(TokenKind::ColonColon)?;
            segments.push(self.parse_ident()?);
        }
        // Drop a leading `std` namespace.
        if segments.len() > 1 && segments[0] == "std" {
            segments.remove(0);
        }
        if segments.len() == 1 {
            return Ok(segments.pop().unwrap());
        }
        let module = &segments[0];
        let func = segments.last().unwrap();
        let starts_upper = module
            .chars()
            .next()
            .map(|c| c.is_uppercase())
            .unwrap_or(false);
        if starts_upper {
            Ok(func.clone())
        } else {
            Ok(format!("{module}_{func}"))
        }
    }

    /// Parse the argument of an Option/Result constructor: either parenthesized
    /// `(e)` (the common `Some(x)` form) or a bare unary expression (`Some x`).
    fn parse_constructor_arg(&mut self) -> Result<Expr, ParseError> {
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
            self.consume(TokenKind::LParen)?;
            let e = self.parse_control_flow()?;
            self.consume(TokenKind::RParen)?;
            Ok(e)
        } else {
            self.parse_unary()
        }
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
                // `pulang e` — early return; unwinds to the nearest enclosing
                // function-application boundary (see Expr::Return). A bare
                // `pulang;` (no operand) returns Unit.
                let e = if matches!(
                    self.peek().map(|t| &t.kind),
                    Some(TokenKind::Semi) | Some(TokenKind::RBrace) | Some(TokenKind::Eof) | None
                ) {
                    Expr::Unit
                } else {
                    self.parse_pipe()?
                };
                Ok(Expr::Return(Box::new(e)))
            }
            Some(TokenKind::KwFor) => self.parse_for_in(),
            Some(TokenKind::KwWhile) => self.parse_while(),
            Some(TokenKind::KwLoop) => self.parse_loop(),
            // `putus` (break) / `lanjut` (continue) — real loop control over the
            // innermost enclosing `selagi`/`ulang`/`untuk` body. Until 2026-08
            // both desugared to a no-op `()`, so a `putus` in a loop silently did
            // nothing. An optional `'label` is still accepted and ignored (only
            // the innermost loop is targeted); using either outside a loop is a
            // parse error rather than a statement that quietly disappears.
            Some(TokenKind::KwBreak) | Some(TokenKind::KwContinue) => {
                let is_break = matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwBreak));
                let span = self.peek().map(|t| t.span).unwrap_or(self.current_span);
                self.next();
                if matches!(
                    self.peek().map(|t| &t.kind),
                    Some(TokenKind::Lifetime(_)) | Some(TokenKind::Label(_))
                ) {
                    self.next();
                }
                if self.loop_depth == 0 {
                    return Err(ParseError {
                        kind: ParseErrorKind::LoopControlOutsideLoop(if is_break {
                            "putus"
                        } else {
                            "lanjut"
                        }),
                        span,
                    });
                }
                Ok(if is_break { Expr::Break } else { Expr::Continue })
            }
            // CAHAYA Phase J5 block forms
            Some(TokenKind::KwDisplay) => self.parse_display(),
            Some(TokenKind::KwRow) => self.parse_row(),
            Some(TokenKind::KwColumn) => self.parse_column(),
            Some(TokenKind::KwStyle) => self.parse_style_decl(),
            _ => self.parse_pipe(),
        }
    }

    /// Parse for-in loop:
    ///   untuk x dalam iter { body }
    /// Desugars to: map (fn(x: Any) body) iter
    fn parse_for_in(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwFor)?;
        // Loop variable: a single name, or a tuple pattern `(a, b, ...)` for
        // destructuring each element.
        let pattern_names: Vec<Ident> =
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
                self.consume(TokenKind::LParen)?;
                let mut names = vec![self.parse_binding_name()?];
                while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                    self.consume(TokenKind::Comma)?;
                    names.push(self.parse_binding_name()?);
                }
                self.consume(TokenKind::RParen)?;
                names
            } else {
                vec![self.parse_binding_name()?]
            };
        self.consume(TokenKind::KwIn)?;
        let iter = self.parse_pipe()?;
        self.consume(TokenKind::LBrace)?;
        // The loop variable shadows any outer `biar ubah` of the same name.
        let scope: Vec<(Ident, bool)> =
            pattern_names.iter().map(|n| (n.clone(), false)).collect();
        let body = self.with_bindings(&scope, Self::parse_expr)?;
        self.consume(TokenKind::RBrace)?;
        // Desugar `untuk x dalam iter { body }` to a list map over the iterable,
        // applying the body as a per-element closure:
        //   senarai_peta((iter, fungsi(x) body))
        // `senarai_peta` (list_map) is the higher-order builtin that iterates a
        // list and evaluates the closure for each element (running its effects).
        // For a tuple pattern `(a, b, ...)` the closure binds a fresh element and
        // projects each name from it via Fst/Snd.
        let lam = if pattern_names.len() == 1 {
            Expr::Lam(pattern_names.into_iter().next().unwrap(), Ty::Any, Box::new(body))
        } else {
            let elem = self.fresh_var("forElem");
            let n = pattern_names.len();
            let mut bound = body;
            for (i, nm) in pattern_names.iter().enumerate().rev() {
                let proj = self.tuple_proj(&elem, i, n);
                bound = Expr::Let(nm.clone(), None, Box::new(proj), Box::new(bound));
            }
            Expr::Lam(elem, Ty::Any, Box::new(bound))
        };
        Ok(Expr::App(
            Box::new(Expr::Var("senarai_peta".into())),
            Box::new(Expr::Pair(Box::new(iter), Box::new(lam))),
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
        let body = self.parse_loop_body()?;
        self.consume(TokenKind::RBrace)?;
        Ok(Expr::While(Box::new(cond), Box::new(body)))
    }

    /// Parse a loop body, with `putus`/`lanjut` enabled for its extent.
    fn parse_loop_body(&mut self) -> Result<Expr, ParseError> {
        self.loop_depth += 1;
        let body = self.parse_expr();
        self.loop_depth -= 1;
        body
    }

    /// Parse infinite loop:
    ///   ulang { body }
    /// Desugars to: selagi betul { body }
    fn parse_loop(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwLoop)?;
        self.consume(TokenKind::LBrace)?;
        let body = self.parse_loop_body()?;
        self.consume(TokenKind::RBrace)?;
        // `ulang { body }` is `selagi betul { body }` — an unbounded loop that
        // only `putus` or `pulang` leaves.
        Ok(Expr::While(
            Box::new(Expr::Bool(true)),
            Box::new(body),
        ))
    }

    /// Parse guard clause:
    ///   'pastikan'|'guard' expr 'lain'|'else' '{' expr '}' ';' expr
    /// Desugars to If(cond, continuation, else_body)
    fn parse_guard(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwGuard)?;
        let cond = self.parse_pipe()?;

        // Two surface forms:
        //   1. `pastikan cond lain { else_body }; rest`  (Swift-style guard)
        //   2. `pastikan cond ["message"]; rest`         (assertion guard)
        // Both desugar to `kalau cond { rest } lain { else }`: execution proceeds
        // to `rest` when the condition holds. Form 2 has no false-branch action
        // (RIINA has no panic yet), so its else-branch is Unit — making the guard
        // a proceed-iff-precondition-holds check.
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwElse)) {
            self.consume(TokenKind::KwElse)?;
            self.consume(TokenKind::LBrace)?;
            let else_body = self.parse_expr()?;
            self.consume(TokenKind::RBrace)?;
            self.consume(TokenKind::Semi)?;
            let continuation = self.parse_stmt_sequence()?;
            return Ok(Expr::If(
                Box::new(cond),
                Box::new(continuation),
                Box::new(else_body),
            ));
        }

        // Assertion form: optional trailing message expression, then `;`.
        if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Semi)) {
            let _msg = self.parse_pipe()?; // message (informational; discarded)
        }
        self.consume(TokenKind::Semi)?;
        let continuation = if self.at_sequence_end() {
            Expr::Unit
        } else {
            self.parse_stmt_sequence()?
        };
        // On guard failure, abort by returning (RIINA has no panic). Modeling the
        // else-branch as an early `pulang` gives it type `Any`, so the whole `If`
        // takes the continuation's (true-branch) type rather than collapsing to
        // Unit — important when the enclosing function returns a non-Unit value.
        Ok(Expr::If(
            Box::new(cond),
            Box::new(continuation),
            Box::new(Expr::Return(Box::new(Expr::Unit))),
        ))
    }

    /// Parse pipe expressions: expr (|> expr)*
    /// a |> f |> g  desugars to  App(g, App(f, a))
    fn parse_pipe(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_assignment()?;
        // Range expression `a..b` (exclusive) / `a..=b` (inclusive), desugared to
        // the `julat`/`julat_inklusif` builtin producing the list [a, a+1, ...].
        // Used mainly as the iterable in `untuk i dalam 0..n { ... }`.
        if matches!(
            self.peek().map(|t| &t.kind),
            Some(TokenKind::DotDot) | Some(TokenKind::DotDotEq)
        ) {
            let inclusive = matches!(self.peek().map(|t| &t.kind), Some(TokenKind::DotDotEq));
            self.next();
            let end = self.parse_assignment()?;
            let builtin = if inclusive { "julat_inklusif" } else { "julat" };
            return Ok(Expr::App(
                Box::new(Expr::Var(builtin.to_string())),
                Box::new(Expr::Pair(Box::new(expr), Box::new(end))),
            ));
        }
        while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Pipe)) {
            self.consume(TokenKind::Pipe)?;
            // The pipe target is a single expression. A lambda (`x |> fungsi(y)
            // { .. }`) is parsed directly so it works as a target, but the target
            // must NOT consume further `|>` operators — pipe is left-associative
            // (`x |> f |> g` is `g(f(x))`) — so we use `parse_assignment` for the
            // general case (not `parse_control_flow`, which would recurse here).
            let func = if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwFn)) {
                self.parse_lam()?
            } else {
                self.parse_assignment()?
            };
            expr = Expr::App(Box::new(func), Box::new(expr));
        }
        Ok(expr)
    }

    fn parse_assignment(&mut self) -> Result<Expr, ParseError> {
        let lhs = self.parse_or()?;
        if let Some(TokenKind::ColonEq) = self.peek().map(|t| &t.kind) {
            self.consume(TokenKind::ColonEq)?;
            // The right-hand side is ONE expression, not the rest of the block.
            //
            // This used to call `parse_expr`, which parses a whole statement
            // sequence — so `r := 100; cetakln(!r);` was read as
            // `r := (100; cetakln(!r))`, quietly swallowing every following
            // statement into the assigned value. It surfaced only as a type
            // error on the assignment (`expected Int, found Unit`), or not at
            // all when the sequence happened to end in the right type, and it
            // made `:=` unusable in statement position — the corpus's own
            // `all_examples.rii` `contoh_ruj` did not type-check because of it.
            //
            // `parse_control_flow` is the same level `biar x = <here>;` uses:
            // it takes a full expression including `kalau`/`padan` forms, and
            // stops at the `;`, leaving `parse_stmt_sequence` to sequence what
            // follows.
            let rhs = self.parse_control_flow()?;
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
        // Postfix accessors, chained left-to-right:
        //   `e.field`      -> structural FieldAccess
        //   `e.0` / `e.1`  -> Fst / Snd (pairs)
        //   `e[i]`         -> list indexing, desugared to `senarai_dapat((e, i))`
        loop {
            match self.peek().map(|t| &t.kind) {
                Some(TokenKind::Dot) => {
                    self.consume(TokenKind::Dot)?;
                    match self.peek().map(|t| t.kind.clone()) {
                        Some(TokenKind::LiteralInt(ref n, _)) if n == "0" => {
                            self.next();
                            expr = Expr::Fst(Box::new(expr));
                        }
                        Some(TokenKind::LiteralInt(ref n, _)) if n == "1" => {
                            self.next();
                            expr = Expr::Snd(Box::new(expr));
                        }
                        Some(TokenKind::Identifier(name)) => {
                            self.next();
                            // Enum-variant access `Type.Variant`: when the base is
                            // a bare uppercase type name and the field is also
                            // uppercase, this is a nullary enum constructor rather
                            // than a struct field access. There is no nominal enum
                            // system yet, so it desugars to a unique string tag
                            // `"Type.Variant"` — equality comparison then makes it
                            // usable as both a value and a `padan` literal pattern.
                            if let Expr::Var(type_name) = &expr {
                                let base_upper = type_name
                                    .chars()
                                    .next()
                                    .map(|c| c.is_uppercase())
                                    .unwrap_or(false);
                                let variant_upper =
                                    name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false);
                                if base_upper && variant_upper {
                                    expr = Expr::String(format!("{type_name}.{name}"));
                                    continue;
                                }
                            }
                            expr = Expr::FieldAccess(Box::new(expr), name);
                        }
                        // Soft-keyword field name, e.g. `rec.tahap`.
                        Some(ref k) if Self::soft_keyword_spelling(k).is_some() => {
                            let name = Self::soft_keyword_spelling(k).unwrap().to_string();
                            self.next();
                            expr = Expr::FieldAccess(Box::new(expr), name);
                        }
                        _ => {
                            return Err(ParseError {
                                kind: ParseErrorKind::ExpectedIdentifier,
                                span: self.current_span,
                            });
                        }
                    }
                }
                Some(TokenKind::LBracket) => {
                    // Index access `e[i]` -> `senarai_dapat((e, i))`, reusing the
                    // existing list-get builtin (which takes a (list, index) pair).
                    self.consume(TokenKind::LBracket)?;
                    let index = self.parse_pipe()?;
                    self.consume(TokenKind::RBracket)?;
                    expr = Expr::App(
                        Box::new(Expr::Var("senarai_dapat".to_string())),
                        Box::new(Expr::Pair(Box::new(expr), Box::new(index))),
                    );
                }
                // Parenthesized call `e(a, b, ...)` -> App(App(e, a), b)... Treated
                // as a call when the head could be a callee (a name, prior call,
                // field access — i.e. a method `obj.m(..)` — or projection). Kept
                // in this postfix loop so calls and field accesses chain freely,
                // e.g. `m.peta(..).peta(..)` (multi-step method chains).
                Some(TokenKind::LParen)
                    if matches!(
                        &expr,
                        Expr::Var(_)
                            | Expr::App(_, _)
                            | Expr::FieldAccess(_, _)
                            | Expr::Fst(_)
                            | Expr::Snd(_)
                    ) =>
                {
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
                    else {
                        // Empty parens `f()` are a real application to `()`.
                        // A zero-parameter function now has a synthesised `()`
                        // parameter (`build_lambda`), so calling it is an
                        // application like any other. Treating `()` as a no-op
                        // suffix is what made a zero-arg function a global
                        // thunk that ran once, eagerly, whether called or not
                        // (master plan REQ-68).
                        expr = Expr::App(Box::new(expr), Box::new(Expr::Unit));
                    }
                    self.consume(TokenKind::RParen)?;
                }
                _ => break,
            }
        }
        // Juxtaposition application (`f x`). Only a callable head juxtaposes an
        // argument — a Var, a prior application, a field access (method-like), or
        // a projection. This prevents a literal followed by another atom (e.g. the
        // `0 "msg"` in `pastikan x >= 0 "msg"`) from being misread as the literal
        // applied to the next token.
        let head_is_callable = matches!(
            &expr,
            Expr::Var(_) | Expr::App(_, _) | Expr::FieldAccess(_, _) | Expr::Fst(_) | Expr::Snd(_)
        );
        if head_is_callable {
            loop {
                if self.is_expr_start() {
                    let arg = self.parse_unary()?;
                    expr = Expr::App(Box::new(expr), Box::new(arg));
                } else {
                    break;
                }
            }
        }
        Ok(expr)
    }

    fn is_expr_start(&mut self) -> bool {
        let kind = self.peek().map(|t| &t.kind);
        matches!(
            kind,
            Some(TokenKind::LiteralInt(_, _))
                | Some(TokenKind::LiteralBool(_))
                | Some(TokenKind::LiteralString(_))
                | Some(TokenKind::Identifier(_))
                | Some(TokenKind::LParen)
                | Some(TokenKind::Not)
                | Some(TokenKind::KwRef)
                | Some(TokenKind::KwPerform)
                | Some(TokenKind::KwClassify)
                | Some(TokenKind::KwDeclassify)
                | Some(TokenKind::KwProve)
                | Some(TokenKind::KwInl)
                | Some(TokenKind::KwInr)
                | Some(TokenKind::KwSome)
                | Some(TokenKind::KwNone)
                | Some(TokenKind::KwOk)
                | Some(TokenKind::KwErr)
                | Some(TokenKind::KwSpawn)
                | Some(TokenKind::KwSend)
                | Some(TokenKind::KwRecv)
                | Some(TokenKind::KwMerge)
                | Some(TokenKind::KwContentHash)
                | Some(TokenKind::KwVerify)
                | Some(TokenKind::KwSmartContract)
                | Some(TokenKind::KwToken)
                | Some(TokenKind::KwZakat)
        )
    }

    fn parse_unary(&mut self) -> Result<Expr, ParseError> {
        let kind = self.peek().map(|t| t.kind.clone());
        match kind {
            Some(TokenKind::Not) => {
                // `!e` is dereference (ML-style), not logical negation. The
                // operand is parsed at the postfix (`parse_app`) level so a
                // following call/index binds INSIDE the operator â `!f(x)` is
                // `Deref(f(x))`, not `(Deref f)(x)` (which left the `(x)` dangling
                // -> "Unexpected token: LParen").
                self.consume(TokenKind::Not)?;
                let e = self.parse_app()?;
                Ok(Expr::Deref(Box::new(e)))
            }
            Some(TokenKind::KwNot) => {
                // `bukan e` / `not e` is logical negation, desugared to
                // `kalau e { salah } lain { betul }` (reuses If â no new AST node).
                // Operand at `parse_app` level so `bukan f(x)` negates the call
                // result (same prefix-then-call gap as `!` above).
                self.consume(TokenKind::KwNot)?;
                let e = self.parse_app()?;
                Ok(Expr::If(
                    Box::new(e),
                    Box::new(Expr::Bool(false)),
                    Box::new(Expr::Bool(true)),
                ))
            }
            Some(TokenKind::KwRef) => {
                self.consume(TokenKind::KwRef)?;
                let e = self.parse_unary()?;
                self.consume(TokenKind::At)?;
                let level = self.parse_security_level()?;
                Ok(Expr::Ref(Box::new(e), level))
            }
            Some(TokenKind::KwPerform) => {
                self.consume(TokenKind::KwPerform)?;
                let eff = self.parse_effect()?;
                let e = self.parse_control_flow()?;
                Ok(Expr::Perform(eff, Box::new(e)))
            }
            Some(TokenKind::KwClassify) => {
                self.consume(TokenKind::KwClassify)?;
                let e = self.parse_control_flow()?;
                Ok(Expr::Classify(Box::new(e)))
            }
            Some(TokenKind::KwDeclassify) => {
                self.consume(TokenKind::KwDeclassify)?;
                // Two surface forms, ONE AST node (identical `Expr::Declassify`,
                // so the mechanized `T_Declassify`/`declass_ok` rule covers both
                // and no new semantics exists):
                //   canonical:  `dedah e dengan bukti p`
                //   call-form:  `dedah(e, p)` — used across the example corpus
                //               (REQ-55; 15 files were unparseable without it).
                // The streaming lexer has no backtracking, so the forms are
                // disambiguated AFTER parsing the operand: `(e, p)` parses as a
                // Pair, and a Pair operand with no following `dengan` IS the
                // call-form. A parenthesized canonical operand —
                // `dedah (sulit x) dengan p` — is unaffected because `dengan`
                // follows (this exact shape regressed under a lookahead-only
                // first attempt; see the corpus test on 00_basics/sulit_dedah).
                let e1 = self.parse_control_flow()?;
                if matches!(self.peek().map(|t| t.kind.clone()), Some(TokenKind::KwWith)) {
                    self.consume(TokenKind::KwWith)?;
                    let e2 = self.parse_control_flow()?;
                    return Ok(Expr::Declassify(Box::new(e1), Box::new(e2)));
                }
                if let Expr::Pair(a, b) = e1 {
                    return Ok(Expr::Declassify(a, b));
                }
                // Neither form: produce the canonical missing-`dengan` error.
                self.consume(TokenKind::KwWith)?;
                unreachable!("consume(KwWith) above always errors here")
            }
            Some(TokenKind::KwProve) => {
                self.consume(TokenKind::KwProve)?;
                let e = self.parse_control_flow()?;
                Ok(Expr::Prove(Box::new(e)))
            }
            Some(TokenKind::KwFst) => {
                self.consume(TokenKind::KwFst)?;
                let e = self.parse_unary()?;
                Ok(Expr::Fst(Box::new(e)))
            }
            Some(TokenKind::KwSnd) => {
                self.consume(TokenKind::KwSnd)?;
                let e = self.parse_unary()?;
                Ok(Expr::Snd(Box::new(e)))
            }
            Some(TokenKind::KwRequire) => {
                self.consume(TokenKind::KwRequire)?;
                let eff = self.parse_effect()?;
                let e = self.parse_control_flow()?;
                Ok(Expr::Require(eff, Box::new(e)))
            }
            Some(TokenKind::KwGrant) => {
                self.consume(TokenKind::KwGrant)?;
                let eff = self.parse_effect()?;
                let e = self.parse_control_flow()?;
                Ok(Expr::Grant(eff, Box::new(e)))
            }
            Some(TokenKind::KwInl) => {
                self.consume(TokenKind::KwInl)?;
                let e = self.parse_unary()?;
                self.consume(TokenKind::Colon)?;
                let ty = self.parse_ty()?;
                Ok(Expr::Inl(Box::new(e), ty))
            }
            Some(TokenKind::KwInr) => {
                self.consume(TokenKind::KwInr)?;
                let e = self.parse_unary()?;
                self.consume(TokenKind::Colon)?;
                let ty = self.parse_ty()?;
                Ok(Expr::Inr(Box::new(e), ty))
            }
            // Option/Result constructors desugar onto the existing sum type:
            //   Some(x)/Ada(x)  -> Inl x      None/Tiada      -> Inr unit
            //   Ok(x)/Jadi(x)   -> Inl x      Err(x)/Gagal(x) -> Inr x
            // The carried type is `Any` (structural; Option and Result are not
            // yet distinguished nominally by the typechecker).
            Some(TokenKind::KwSome) | Some(TokenKind::KwOk) => {
                self.next();
                let inner = self.parse_constructor_arg()?;
                Ok(Expr::Inl(Box::new(inner), Ty::Any))
            }
            Some(TokenKind::KwErr) => {
                self.next();
                let inner = self.parse_constructor_arg()?;
                Ok(Expr::Inr(Box::new(inner), Ty::Any))
            }
            Some(TokenKind::KwNone) => {
                self.next();
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
                    self.consume(TokenKind::LParen)?;
                    self.consume(TokenKind::RParen)?;
                }
                Ok(Expr::Inr(Box::new(Expr::Unit), Ty::Any))
            }
            Some(TokenKind::KwSpawn) => self.parse_spawn(),
            Some(TokenKind::KwSend) => self.parse_actor_send(),
            Some(TokenKind::KwRecv) => self.parse_actor_recv(),
            Some(TokenKind::KwMerge) => self.parse_crdt_merge(),
            Some(TokenKind::KwContentHash) => self.parse_content_hash(),
            Some(TokenKind::KwVerify) => self.parse_content_verify(),
            Some(TokenKind::KwSmartContract) => self.parse_contract_deploy(),
            Some(TokenKind::KwToken) => self.parse_token_transfer(),
            Some(TokenKind::KwZakat) => self.parse_zakat_calculate(),
            // CAHAYA Phase J5 prefix forms
            Some(TokenKind::KwText_) => self.parse_ui_text(),
            Some(TokenKind::KwButton) => self.parse_ui_button(),
            Some(TokenKind::KwColor) => self.parse_ui_color(),
            Some(TokenKind::KwContrast) => self.parse_ui_contrast(),
            _ => self.parse_atom(),
        }
    }

    fn parse_atom(&mut self) -> Result<Expr, ParseError> {
        let kind = self.peek().map(|t| t.kind.clone());
        match kind {
            // Anonymous (braced) record literal: `{ field: e, ... }` with no
            // type name (e.g. `pulang { hos: "localhost", port: 8080 }`). Records
            // are structural, so the type name is empty. Disambiguated from a
            // block via `looks_like_record_literal` (next-next token is `ident :`,
            // or `}` for the empty record).
            Some(TokenKind::LBrace) if self.looks_like_record_literal() => {
                self.parse_record_literal_body(String::new())
            }
            Some(TokenKind::LiteralInt(s, suffix)) => {
                self.next();
                // Strip digit separators (`1_000`). When a width suffix is present
                // the lexer guarantees a decimal magnitude and has already
                // range-checked it, so a sized literal becomes `Expr::IntN`;
                // otherwise it stays the default `Expr::Int` (`Ty::Int`).
                let value: u64 = s
                    .chars()
                    .filter(|c| *c != '_')
                    .collect::<String>()
                    .parse()
                    .unwrap_or(0);
                match suffix.as_deref().and_then(int_suffix_to_width) {
                    Some((bits, signed)) => Ok(Expr::IntN {
                        value,
                        bits,
                        signed,
                    }),
                    None => Ok(Expr::Int(value)),
                }
            }
            Some(TokenKind::LiteralBool(b)) => {
                self.next();
                Ok(Expr::Bool(b))
            }
            Some(TokenKind::LiteralString(s)) => {
                self.next();
                Ok(Expr::String(s))
            }
            Some(TokenKind::Identifier(s)) => {
                self.next();
                // `format!("tmpl", args...)` macro — Rust-style string formatting
                // used across the example corpus. Desugar to string concatenation
                // of the template's literal segments interleaved with the
                // stringified arguments (`ke_teks`).
                if s == "format" && matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Not)) {
                    return self.parse_format_macro();
                }
                // Qualified module path `Module::function` (e.g. `teks::mengandungi`,
                // `Masa::masa_unix`). Resolve to the flat builtin name so the
                // existing Var/builtin machinery handles it.
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::ColonColon)) {
                    let resolved = self.parse_module_path(s)?;
                    return Ok(Expr::Var(resolved));
                }
                // Record literal `Name { field: e, ... }`. Only treated as a
                // record when the brace is immediately followed by `ident :`,
                // so it cannot be confused with a control-flow block (those are
                // parsed by their own keywords, never reaching here).
                if self.looks_like_record_literal() {
                    return self.parse_record_literal_body(s);
                }
                // Named (nominal-enum) constructor. An uppercase identifier is a
                // data constructor: `C(args)` builds the structural tagged value
                // `Pair("C", payload)` (payload = the single arg, a tuple of args,
                // or Unit), and a bare uppercase `C` builds the tag string "C".
                // Lowercase identifiers remain variables/functions. `Titik {..}`
                // record literals are handled above; `T::m` paths and `T.V`
                // variants are handled elsewhere.
                let is_ctor = s.chars().next().map(|c| c.is_uppercase()).unwrap_or(false);
                if is_ctor && matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
                    self.consume(TokenKind::LParen)?;
                    let mut args = Vec::new();
                    if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                        args.push(self.parse_control_flow()?);
                        while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                            self.consume(TokenKind::Comma)?;
                            args.push(self.parse_control_flow()?);
                        }
                    }
                    self.consume(TokenKind::RParen)?;
                    // payload: Unit for nullary, the arg for one, a right-nested
                    // tuple for many (matching tuple construction / projection).
                    let payload = match args.len() {
                        0 => Expr::Unit,
                        1 => args.pop().unwrap(),
                        _ => {
                            let mut it = args.into_iter().rev();
                            let mut acc = it.next().unwrap();
                            for x in it {
                                acc = Expr::Pair(Box::new(x), Box::new(acc));
                            }
                            acc
                        }
                    };
                    return Ok(Expr::Pair(
                        Box::new(Expr::String(s)),
                        Box::new(payload),
                    ));
                }
                // Bare uppercase identifier = nullary nominal-enum constructor,
                // built as the tag string "C" (matches the nullary `NamedCtor`
                // pattern). Excludes a following `.` — that is a `Type.Variant`
                // access handled in parse_app. Lowercase identifiers stay
                // variables.
                if is_ctor && !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Dot)) {
                    return Ok(Expr::String(s));
                }
                Ok(self.name_ref(s))
            }
            // List literal `[e1, e2, ...]`. A trailing comma is allowed; `[]` is
            // the empty list.
            Some(TokenKind::LBracket) => {
                self.next();
                let mut elems = Vec::new();
                while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBracket) | None) {
                    elems.push(self.parse_control_flow()?);
                    if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                        self.consume(TokenKind::Comma)?;
                    } else {
                        break;
                    }
                }
                self.consume(TokenKind::RBracket)?;
                Ok(Expr::ListLit(elems))
            }
            // KwExpect (jangkakan/expect) is both a keyword and a builtin function.
            // When used as an expression, treat it as Var("jangkakan").
            Some(TokenKind::KwExpect) => {
                self.next();
                Ok(Expr::Var("jangkakan".to_string()))
            }
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

                    if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                        // Tuple. Collect all elements, then build a right-nested
                        // pair chain `(a, (b, (c, ...)))` so n-tuples (n >= 2) are
                        // supported uniformly (matching `tuple_proj`/Fst-Snd access
                        // and destructuring).
                        let mut elems = vec![e];
                        while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                            self.consume(TokenKind::Comma)?;
                            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                                break; // trailing comma
                            }
                            elems.push(self.parse_expr()?);
                        }
                        self.consume(TokenKind::RParen)?;
                        let mut iter = elems.into_iter().rev();
                        let mut acc = iter.next().unwrap();
                        for x in iter {
                            acc = Expr::Pair(Box::new(x), Box::new(acc));
                        }
                        Ok(acc)
                    } else {
                        self.consume(TokenKind::RParen)?;
                        Ok(e)
                    }
                }
            }
            // A "soft" keyword in value position (where an atom is expected) is a
            // variable reference — the corpus uses words like `tahap`, `keadaan`,
            // `jenis` as ordinary names. Treat it as `Var(canonical spelling)`.
            Some(ref k) if Self::soft_keyword_spelling(k).is_some() => {
                let name = Self::soft_keyword_spelling(k).unwrap().to_string();
                self.next();
                Ok(self.name_ref(name))
            }
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
        let then_branch = self.parse_expr()?;
        self.consume(TokenKind::RBrace)?;

        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwElse)) {
            self.consume(TokenKind::KwElse)?;
            // `lain kalau ...` (else-if): the else branch is itself an `if`,
            // parsed recursively to chain conditions.
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwIf)) {
                let else_branch = self.parse_if()?;
                return Ok(Expr::If(
                    Box::new(cond),
                    Box::new(then_branch),
                    Box::new(else_branch),
                ));
            }
            self.consume(TokenKind::LBrace)?;
            let else_branch = self.parse_expr()?;
            self.consume(TokenKind::RBrace)?;
            Ok(Expr::If(
                Box::new(cond),
                Box::new(then_branch),
                Box::new(else_branch),
            ))
        } else {
            // `kalau cond { ... }` with no `lain`: used as a statement (e.g. an
            // early-return guard `kalau c { pulang x; }`). Both branches must
            // agree in type, so the then-branch's value is discarded (sequenced
            // to Unit) and the implicit else is Unit. The construct yields Unit.
            let then_unit = Expr::Let(
                "_".to_string(),
                None,
                Box::new(then_branch),
                Box::new(Expr::Unit),
            );
            Ok(Expr::If(
                Box::new(cond),
                Box::new(then_unit),
                Box::new(Expr::Unit),
            ))
        }
    }

    fn parse_lam(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwFn)?;
        self.consume(TokenKind::LParen)?;
        // Parameter list: zero or more `name: Type`, comma-separated. Multiple
        // params curry into nested `Lam`s.
        let params = self.parse_param_list()?;
        self.consume(TokenKind::RParen)?;
        // Optional return-type annotation `-> T` (accepted; inferred, so ignored).
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Arrow)) {
            self.consume(TokenKind::Arrow)?;
            let _ret = self.parse_ty()?;
        }
        // Body: a `{ ... }` block or a bare control-flow expression. As for a
        // named function, parameters shadow an outer `biar ubah` of the same name.
        let scope: Vec<(Ident, bool)> = params.iter().map(|(n, _)| (n.clone(), false)).collect();
        let body = self.with_bindings(&scope, |p| {
            if matches!(p.peek().map(|t| &t.kind), Some(TokenKind::LBrace)) {
                p.consume(TokenKind::LBrace)?;
                let b = p.parse_stmt_sequence()?;
                p.consume(TokenKind::RBrace)?;
                Ok(b)
            } else {
                p.parse_control_flow()
            }
        })?;
        // Curry parameters into nested lambdas (right-fold). A no-parameter
        // `fungsi()` becomes a single Unit-typed parameter (a thunk).
        if params.is_empty() {
            Ok(Expr::Lam("_".to_string(), Ty::Unit, Box::new(body)))
        } else {
            Ok(params
                .into_iter()
                .rev()
                .fold(body, |acc, (p, ty)| Expr::Lam(p, ty, Box::new(acc))))
        }
    }

    /// Parse a `padan` (match) expression and compile it to the core calculus.
    ///
    /// RIINA's AST has no dedicated match/pattern node; `padan` is sugar that
    /// this function compiles down to the verified core constructs:
    ///   - `Case` (sum elimination) for Option/Result-style constructor patterns
    ///     (`Ada(x)`/`Tidak`, `Ok(x)`/`Ralat(e)`, `inl x`/`inr y`);
    ///   - nested `If` + structural `==` for literal / bool / string patterns;
    ///   - `Fst`/`Snd` projection for tuple patterns;
    ///   - variable / `_` patterns as binding catch-alls;
    ///   - `kalau <cond>` guards on any arm.
    ///
    /// Arm syntax accepts both `->` (Arrow, the surface syntax used across the
    /// example corpus) and `=>` (FatArrow, legacy). Arm bodies may be a bare
    /// expression or a `{ ... }` block.
    fn parse_match(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwMatch)?;
        let scrutinee = self.parse_pipe()?;
        self.consume(TokenKind::LBrace)?;

        let mut arms: Vec<MatchArm> = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBrace) | None) {
            let pattern = self.parse_pattern()?;
            // Optional guard: `kalau <cond>`.
            let guard = if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwIf)) {
                self.consume(TokenKind::KwIf)?;
                Some(self.parse_pipe()?)
            } else {
                None
            };
            self.consume_arm_arrow()?;
            let body = self.parse_arm_body()?;
            arms.push(MatchArm { pattern, guard, body });
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                self.next();
            }
        }
        self.consume(TokenKind::RBrace)?;

        self.compile_match(scrutinee, arms)
    }

    /// Consume the arrow separating a match pattern from its body. Accepts both
    /// `->` (surface syntax) and `=>` (legacy) for compatibility.
    fn consume_arm_arrow(&mut self) -> Result<(), ParseError> {
        match self.peek().map(|t| &t.kind) {
            Some(TokenKind::Arrow) => {
                self.consume(TokenKind::Arrow)?;
                Ok(())
            }
            Some(TokenKind::FatArrow) => {
                self.consume(TokenKind::FatArrow)?;
                Ok(())
            }
            _ => self.consume(TokenKind::Arrow).map(|_| ()),
        }
    }

    /// Parse a match arm body: either a `{ ... }` block (statement sequence) or
    /// a bare expression.
    fn parse_arm_body(&mut self) -> Result<Expr, ParseError> {
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LBrace)) {
            self.consume(TokenKind::LBrace)?;
            let body = self.parse_stmt_sequence()?;
            self.consume(TokenKind::RBrace)?;
            Ok(body)
        } else {
            // Use parse_control_flow (not parse_pipe) so a bare arm body may be a
            // control-flow expression — e.g. `0 -> pulang 99` or `_ -> kalau ...`.
            // The `pulang`/`kalau` operand parsers stop at the arm-separating `,`.
            self.parse_control_flow()
        }
    }

    /// Parse a single match pattern.
    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        match self.peek().map(|t| t.kind.clone()) {
            // Tuple pattern `(p1, p2, ...)` (or `()` for unit).
            Some(TokenKind::LParen) => {
                self.consume(TokenKind::LParen)?;
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                    self.consume(TokenKind::RParen)?;
                    return Ok(Pattern::Tuple(Vec::new()));
                }
                let mut elems = vec![self.parse_pattern()?];
                while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                    self.consume(TokenKind::Comma)?;
                    elems.push(self.parse_pattern()?);
                }
                self.consume(TokenKind::RParen)?;
                if elems.len() == 1 {
                    Ok(elems.pop().unwrap())
                } else {
                    Ok(Pattern::Tuple(elems))
                }
            }
            // List pattern: `[]`, `[p0, p1, ...]`, or `[p0, ..rest]` (the rest
            // binding `..name` captures the remaining elements as a list and must
            // be last).
            Some(TokenKind::LBracket) => {
                self.consume(TokenKind::LBracket)?;
                let mut elems = Vec::new();
                let mut tail = None;
                while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBracket) | None) {
                    if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::DotDot)) {
                        // `..rest` rest-binding (or bare `..` to ignore the rest).
                        self.consume(TokenKind::DotDot)?;
                        if let Some(TokenKind::Identifier(_)) = self.peek().map(|t| &t.kind) {
                            tail = Some(self.parse_ident()?);
                        } else {
                            tail = Some("_".to_string());
                        }
                        break;
                    }
                    elems.push(self.parse_pattern()?);
                    if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                        self.consume(TokenKind::Comma)?;
                    } else {
                        break;
                    }
                }
                self.consume(TokenKind::RBracket)?;
                Ok(Pattern::List { elems, tail })
            }
            // Sum constructors that are keywords: Some/Ada, Ok/Jadi -> left;
            // None/Tiada, Err/Gagal -> right.
            Some(TokenKind::KwSome) | Some(TokenKind::KwOk) => {
                self.next();
                let inner = self.parse_ctor_payload()?;
                Ok(Pattern::CtorLeft(inner))
            }
            Some(TokenKind::KwErr) => {
                self.next();
                let inner = self.parse_ctor_payload()?;
                Ok(Pattern::CtorRight(inner))
            }
            Some(TokenKind::KwNone) => {
                self.next();
                // `Tiada`/`None` may appear bare or as `Tiada()`.
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
                    self.consume(TokenKind::LParen)?;
                    self.consume(TokenKind::RParen)?;
                }
                Ok(Pattern::CtorRight(Box::new(Pattern::Wildcard)))
            }
            Some(TokenKind::KwInl) => {
                self.next();
                let name = self.parse_ident()?;
                Ok(Pattern::CtorLeft(Box::new(Pattern::Var(name))))
            }
            Some(TokenKind::KwInr) => {
                self.next();
                let name = self.parse_ident()?;
                Ok(Pattern::CtorRight(Box::new(Pattern::Var(name))))
            }
            // Reference pattern `ruj(p)`: matches a reference, binding/testing the
            // inner pattern against the dereferenced value.
            Some(TokenKind::KwRef) => {
                self.next();
                let inner = self.parse_ctor_payload()?;
                Ok(Pattern::Ref(inner))
            }
            // Literal patterns.
            Some(TokenKind::LiteralInt(s, _)) => {
                self.next();
                Ok(Pattern::Int(s.parse().unwrap_or(0)))
            }
            Some(TokenKind::LiteralBool(b)) => {
                self.next();
                Ok(Pattern::Bool(b))
            }
            Some(TokenKind::LiteralString(s)) => {
                self.next();
                Ok(Pattern::Str(s))
            }
            // Identifier: `_` is wildcard; an uppercase identifier followed by
            // `(...)` is an enum constructor (treated as a right-injection payload
            // binding so `Ralat(e)`/`Berjaya(v)` bind their argument); otherwise a
            // variable binding.
            Some(TokenKind::Identifier(s)) => {
                self.next();
                if s == "_" {
                    return Ok(Pattern::Wildcard);
                }
                let is_ctor = s.chars().next().map(|c| c.is_uppercase()).unwrap_or(false);
                // Enum-variant pattern `Type.Variant` — matches the string tag
                // that value-position `Type.Variant` desugars to (see parse_app).
                if is_ctor && matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Dot)) {
                    let mut ahead = self.lexer.clone();
                    ahead.next(); // `.`
                    if let Some(TokenKind::Identifier(v)) = ahead.next().map(|t| t.kind) {
                        if v.chars().next().map(|c| c.is_uppercase()).unwrap_or(false) {
                            self.consume(TokenKind::Dot)?;
                            self.parse_ident()?; // consume variant
                            return Ok(Pattern::Str(format!("{s}.{v}")));
                        }
                    }
                }
                if is_ctor && matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
                    // Named (nominal-enum) constructor with arguments, e.g.
                    // `Bulatan(r)` or `Segi(p, l)`. Matches the structural tag
                    // `("Bulatan", payload)` (see parse_atom construction).
                    self.consume(TokenKind::LParen)?;
                    let mut args = vec![self.parse_pattern()?];
                    while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                        self.consume(TokenKind::Comma)?;
                        args.push(self.parse_pattern()?);
                    }
                    self.consume(TokenKind::RParen)?;
                    Ok(Pattern::NamedCtor { name: s, args })
                } else if is_ctor {
                    // Nullary constructor used as a tag (e.g. `Tertutup`): matches
                    // the bare tag string "Tertutup".
                    Ok(Pattern::NamedCtor {
                        name: s,
                        args: Vec::new(),
                    })
                } else {
                    Ok(Pattern::Var(s))
                }
            }
            _ => Err(ParseError {
                kind: ParseErrorKind::ExpectedIdentifier,
                span: self.current_span,
            }),
        }
    }

    /// Parse a constructor's parenthesized payload pattern: `(p)`. A bare
    /// constructor with no parentheses binds nothing (wildcard payload).
    fn parse_ctor_payload(&mut self) -> Result<Box<Pattern>, ParseError> {
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
            self.consume(TokenKind::LParen)?;
            // Multi-arg constructors `C(a, b, ...)`: bind as a tuple pattern.
            let mut elems = vec![self.parse_pattern()?];
            while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                self.consume(TokenKind::Comma)?;
                elems.push(self.parse_pattern()?);
            }
            self.consume(TokenKind::RParen)?;
            if elems.len() == 1 {
                Ok(Box::new(elems.pop().unwrap()))
            } else {
                Ok(Box::new(Pattern::Tuple(elems)))
            }
        } else {
            Ok(Box::new(Pattern::Wildcard))
        }
    }

    /// Compile parsed match arms to core `Expr`. Constructor patterns
    /// (`CtorLeft`/`CtorRight`) compile to a `Case` over the sum; all other
    /// patterns compile to a nested `If` chain over structural tests. A `padan`
    /// that mixes both forms falls back to the `If`-chain compiler using the
    /// scrutinee directly.
    fn compile_match(
        &mut self,
        scrutinee: Expr,
        arms: Vec<MatchArm>,
    ) -> Result<Expr, ParseError> {
        let has_ctor = arms
            .iter()
            .any(|a| matches!(a.pattern, Pattern::CtorLeft(_) | Pattern::CtorRight(_)));
        let all_ctor_or_default = arms.iter().all(|a| {
            matches!(
                a.pattern,
                Pattern::CtorLeft(_) | Pattern::CtorRight(_) | Pattern::Wildcard | Pattern::Var(_)
            ) && a.guard.is_none()
        });

        if has_ctor && all_ctor_or_default {
            return self.compile_sum_match(scrutinee, arms);
        }
        self.compile_if_chain(scrutinee, arms)
    }

    /// Compile a constructor-style `padan` to a `Case` (sum elimination).
    /// Collects the first left arm and first right arm; a trailing
    /// wildcard/variable arm fills whichever side is absent.
    fn compile_sum_match(
        &mut self,
        scrutinee: Expr,
        arms: Vec<MatchArm>,
    ) -> Result<Expr, ParseError> {
        let mut left: Option<(Box<Pattern>, Expr)> = None;
        let mut right: Option<(Box<Pattern>, Expr)> = None;
        let mut default: Option<Expr> = None;

        for arm in arms {
            match arm.pattern {
                Pattern::CtorLeft(p) if left.is_none() => left = Some((p, arm.body)),
                Pattern::CtorRight(p) if right.is_none() => right = Some((p, arm.body)),
                Pattern::Wildcard | Pattern::Var(_) if default.is_none() => {
                    default = Some(arm.body)
                }
                _ => {} // redundant arm; first match wins
            }
        }

        // Choose the `Case` binder for each side. When the payload pattern is a
        // simple variable (the common `inl x =>` / `Ada(n) ->` form), use that
        // name directly as the binder — no wrapping `let`, giving a clean `Case`.
        // Otherwise introduce a fresh binder and destructure the payload.
        let (left_binder, left_branch) = match left {
            Some((pat, body)) => match *pat {
                Pattern::Var(name) => (name, body),
                Pattern::Wildcard => (self.fresh_var("padL"), body),
                other => {
                    let fresh = self.fresh_var("padL");
                    let b = self.bind_pattern(Expr::Var(fresh.clone()), &other, body)?;
                    (fresh, b)
                }
            },
            None => (self.fresh_var("padL"), default.clone().unwrap_or(Expr::Unit)),
        };
        let (right_binder, right_branch) = match right {
            Some((pat, body)) => match *pat {
                Pattern::Var(name) => (name, body),
                Pattern::Wildcard => (self.fresh_var("padR"), body),
                other => {
                    let fresh = self.fresh_var("padR");
                    let b = self.bind_pattern(Expr::Var(fresh.clone()), &other, body)?;
                    (fresh, b)
                }
            },
            None => (self.fresh_var("padR"), default.unwrap_or(Expr::Unit)),
        };

        Ok(Expr::Case(
            Box::new(scrutinee),
            left_binder,
            Box::new(left_branch),
            right_binder,
            Box::new(right_branch),
        ))
    }

    /// Bind a (payload) pattern against a scrutinee expression, then evaluate
    /// `body` in the resulting scope. Used for constructor payloads in `Case`
    /// branches. Variable patterns introduce a `let`; tuples project with
    /// `Fst`/`Snd`; wildcards/literals bind nothing.
    fn bind_pattern(
        &mut self,
        scrut: Expr,
        pat: &Pattern,
        body: Expr,
    ) -> Result<Expr, ParseError> {
        match pat {
            Pattern::Wildcard | Pattern::Int(_) | Pattern::Bool(_) | Pattern::Str(_) => Ok(body),
            Pattern::Var(name) => Ok(Expr::Let(
                name.clone(),
                None,
                Box::new(scrut),
                Box::new(body),
            )),
            Pattern::Tuple(elems) => {
                // Bind left-nested pairs: (a, b) -> let a = fst s; let b = snd s.
                // For arity > 2, the tail is itself treated as the snd component.
                self.bind_tuple(scrut, elems, body)
            }
            Pattern::CtorLeft(inner) | Pattern::CtorRight(inner) => {
                // Nested constructor in a payload: rare in the corpus; bind its
                // inner pattern directly against the (already-projected) value.
                self.bind_pattern(scrut, inner, body)
            }
            Pattern::List { .. } => {
                // List pattern as a constructor payload (e.g. `Ada([x, ..r])`):
                // bind a fresh temp to the value, then apply the list pattern's
                // element/rest bindings (the length test is irrefutable here since
                // the surrounding Case already selected this branch).
                let tmp = self.fresh_var("padLst");
                let (_test, binds) = self.pattern_test(&Expr::Var(tmp.clone()), pat);
                let bound = self.wrap_lets(binds, body);
                Ok(Expr::Let(tmp, None, Box::new(scrut), Box::new(bound)))
            }
            Pattern::Ref(inner) => {
                // Reference payload: bind the inner pattern against the deref.
                let deref = Expr::Deref(Box::new(scrut));
                self.bind_pattern(deref, inner, body)
            }
            Pattern::NamedCtor { .. } => {
                // Named-constructor pattern as a payload: bind a fresh temp and
                // apply its (irrefutable-here) variable bindings.
                let tmp = self.fresh_var("padCtor");
                let (_t, binds) = self.pattern_test(&Expr::Var(tmp.clone()), pat);
                let bound = self.wrap_lets(binds, body);
                Ok(Expr::Let(tmp, None, Box::new(scrut), Box::new(bound)))
            }
        }
    }

    /// Bind a tuple pattern by `Fst`/`Snd` projection. A 2-tuple binds
    /// `Fst`/`Snd`; an n-tuple binds the first element to `Fst` and recurses on
    /// `Snd` for the remainder.
    fn bind_tuple(
        &mut self,
        scrut: Expr,
        elems: &[Pattern],
        body: Expr,
    ) -> Result<Expr, ParseError> {
        if elems.is_empty() {
            return Ok(body);
        }
        if elems.len() == 1 {
            return self.bind_pattern(scrut, &elems[0], body);
        }
        let fst = Expr::Fst(Box::new(scrut.clone()));
        let snd = Expr::Snd(Box::new(scrut));
        let rest = self.bind_tuple(snd, &elems[1..], body)?;
        self.bind_pattern(fst, &elems[0], rest)
    }

    /// Compile a `padan` to a nested `If` chain over structural equality and
    /// tuple-component tests. Handles literal/bool/string/variable/wildcard/
    /// tuple patterns plus `kalau` guards.
    fn compile_if_chain(
        &mut self,
        scrutinee: Expr,
        mut arms: Vec<MatchArm>,
    ) -> Result<Expr, ParseError> {
        // Bind the scrutinee once to avoid re-evaluating it per arm.
        let s = self.fresh_var("padS");
        let s_expr = Expr::Var(s.clone());

        // RIINA has no exhaustiveness checker yet, and a desugared `If`-chain
        // needs a well-typed fallback. If no arm is irrefutable (no bare
        // wildcard/variable arm without a guard), the final arm is promoted to
        // the catch-all default: its test is dropped so its body becomes the
        // base case. This keeps exhaustive matches (e.g. `betul`/`salah`) sound
        // without a Unit-typed fallback. (Documented simplification.)
        let has_irrefutable = arms.iter().any(|a| {
            a.guard.is_none() && matches!(a.pattern, Pattern::Wildcard | Pattern::Var(_))
        });

        let mut result = if has_irrefutable {
            Expr::Unit
        } else if let Some(last) = arms.pop() {
            let (_test, bindings) = self.pattern_test(&s_expr, &last.pattern);
            self.wrap_lets(bindings, last.body)
        } else {
            Expr::Unit
        };

        for arm in arms.into_iter().rev() {
            let (test, bindings) = self.pattern_test(&s_expr, &arm.pattern);
            // Fold the guard (if any) into the arm test.
            let full_test = match arm.guard {
                Some(g) => match test {
                    Some(t) => Some(Expr::BinOp(BinOp::And, Box::new(t), Box::new(g))),
                    None => Some(g),
                },
                None => test,
            };
            // Bind the pattern variables around BOTH the test and body so guards
            // can reference them. Bindings are pure projections of the scrutinee.
            result = match full_test {
                Some(t) => self.wrap_lets(
                    bindings,
                    Expr::If(Box::new(t), Box::new(arm.body), Box::new(result)),
                ),
                None => self.wrap_lets(bindings, arm.body),
            };
        }
        Ok(Expr::Let(
            s,
            None,
            Box::new(scrutinee),
            Box::new(result),
        ))
    }

    /// Wrap `body` in a chain of `let` bindings, bringing pattern variables into
    /// scope. Bindings apply outermost-first (first binding is outermost).
    fn wrap_lets(&self, bindings: Vec<(Ident, Expr)>, body: Expr) -> Expr {
        bindings.into_iter().rev().fold(body, |acc, (name, value)| {
            Expr::Let(name, None, Box::new(value), Box::new(acc))
        })
    }

    /// Build the boolean test and variable bindings for one pattern against a
    /// scrutinee expression. Returns `(None, _)` for an irrefutable pattern
    /// (wildcard / variable) that always matches.
    fn pattern_test(&mut self, scrut: &Expr, pat: &Pattern) -> (Option<Expr>, Vec<(Ident, Expr)>) {
        match pat {
            Pattern::Wildcard => (None, Vec::new()),
            Pattern::Var(name) => (None, vec![(name.clone(), scrut.clone())]),
            Pattern::Int(n) => (
                Some(Expr::BinOp(
                    BinOp::Eq,
                    Box::new(scrut.clone()),
                    Box::new(Expr::Int(*n)),
                )),
                Vec::new(),
            ),
            Pattern::Bool(b) => (
                Some(Expr::BinOp(
                    BinOp::Eq,
                    Box::new(scrut.clone()),
                    Box::new(Expr::Bool(*b)),
                )),
                Vec::new(),
            ),
            Pattern::Str(s) => (
                Some(Expr::BinOp(
                    BinOp::Eq,
                    Box::new(scrut.clone()),
                    Box::new(Expr::String(s.clone())),
                )),
                Vec::new(),
            ),
            Pattern::Tuple(elems) => {
                // Conjoin component tests over Fst/Snd projections.
                let mut tests: Vec<Expr> = Vec::new();
                let mut binds: Vec<(Ident, Expr)> = Vec::new();
                let mut acc = scrut.clone();
                for (i, elem) in elems.iter().enumerate() {
                    let proj = if i + 1 == elems.len() {
                        // last component: the remaining accumulator
                        acc.clone()
                    } else {
                        Expr::Fst(Box::new(acc.clone()))
                    };
                    let (t, b) = self.pattern_test(&proj, elem);
                    if let Some(t) = t {
                        tests.push(t);
                    }
                    binds.extend(b);
                    acc = Expr::Snd(Box::new(acc));
                }
                let test = tests.into_iter().reduce(|a, b| {
                    Expr::BinOp(BinOp::And, Box::new(a), Box::new(b))
                });
                (test, binds)
            }
            Pattern::List { elems, tail } => {
                // Length test: exact `== n` for a fixed list, `>= n` when a rest
                // binding is present. Element `i` is `senarai_dapat((s, i))`; the
                // rest is `senarai_potong((s, (n, senarai_panjang(s))))`.
                let n = elems.len() as u64;
                let len_expr = Expr::App(
                    Box::new(Expr::Var("senarai_panjang".to_string())),
                    Box::new(scrut.clone()),
                );
                let len_op = if tail.is_some() { BinOp::Ge } else { BinOp::Eq };
                let mut tests = vec![Expr::BinOp(
                    len_op,
                    Box::new(len_expr.clone()),
                    Box::new(Expr::Int(n)),
                )];
                let mut binds: Vec<(Ident, Expr)> = Vec::new();
                for (i, elem) in elems.iter().enumerate() {
                    let item = Expr::App(
                        Box::new(Expr::Var("senarai_dapat".to_string())),
                        Box::new(Expr::Pair(
                            Box::new(scrut.clone()),
                            Box::new(Expr::Int(i as u64)),
                        )),
                    );
                    let (t, b) = self.pattern_test(&item, elem);
                    if let Some(t) = t {
                        tests.push(t);
                    }
                    binds.extend(b);
                }
                if let Some(rest_name) = tail {
                    if rest_name != "_" {
                        // rest = senarai_potong((s, (n, senarai_panjang(s))))
                        let slice = Expr::App(
                            Box::new(Expr::Var("senarai_potong".to_string())),
                            Box::new(Expr::Pair(
                                Box::new(scrut.clone()),
                                Box::new(Expr::Pair(
                                    Box::new(Expr::Int(n)),
                                    Box::new(len_expr),
                                )),
                            )),
                        );
                        binds.push((rest_name.clone(), slice));
                    }
                }
                let test = tests
                    .into_iter()
                    .reduce(|a, b| Expr::BinOp(BinOp::And, Box::new(a), Box::new(b)));
                (test, binds)
            }
            // Constructor patterns in the If-chain compiler (e.g. nested inside a
            // tuple pattern like `(Ada(a), Ada(b))`, where a top-level `Case`
            // can't be used). Test the sum tag with `adalah_kiri`/`adalah_kanan`
            // and project the payload with `nilai_kiri`/`nilai_kanan`, recursing
            // into the inner pattern.
            Pattern::CtorLeft(inner) | Pattern::CtorRight(inner) => {
                let is_left = matches!(pat, Pattern::CtorLeft(_));
                let (tag_fn, val_fn) = if is_left {
                    ("adalah_kiri", "nilai_kiri")
                } else {
                    ("adalah_kanan", "nilai_kanan")
                };
                let tag_test = Expr::App(
                    Box::new(Expr::Var(tag_fn.to_string())),
                    Box::new(scrut.clone()),
                );
                let payload = Expr::App(
                    Box::new(Expr::Var(val_fn.to_string())),
                    Box::new(scrut.clone()),
                );
                let (inner_test, binds) = self.pattern_test(&payload, inner);
                let test = match inner_test {
                    Some(t) => Expr::BinOp(BinOp::And, Box::new(tag_test), Box::new(t)),
                    None => tag_test,
                };
                (Some(test), binds)
            }
            // Reference pattern `ruj(p)`: dereference the scrutinee and match the
            // inner pattern against the pointed-to value. The reference itself is
            // irrefutable (any ref matches `ruj(_)`); refutability comes from `p`.
            Pattern::Ref(inner) => {
                let deref = Expr::Deref(Box::new(scrut.clone()));
                self.pattern_test(&deref, inner)
            }
            // Named (nominal-enum) constructor `C(p0, ...)` matches the structural
            // tagged value `("C", payload)`: test `fst(scrut) == "C"`, then match
            // the argument pattern(s) against `snd(scrut)` (the payload). A nullary
            // `C` matches the bare tag string "C".
            Pattern::NamedCtor { name, args } => {
                if args.is_empty() {
                    // Bare tag: the value is the string "C" itself.
                    let test = Expr::BinOp(
                        BinOp::Eq,
                        Box::new(scrut.clone()),
                        Box::new(Expr::String(name.clone())),
                    );
                    return (Some(test), Vec::new());
                }
                let tag = Expr::Fst(Box::new(scrut.clone()));
                let payload = Expr::Snd(Box::new(scrut.clone()));
                let mut tests = vec![Expr::BinOp(
                    BinOp::Eq,
                    Box::new(tag),
                    Box::new(Expr::String(name.clone())),
                )];
                let mut binds = Vec::new();
                // Match the argument pattern(s) against the payload. One arg
                // matches the payload directly; many match a right-nested tuple.
                let arg_pat = if args.len() == 1 {
                    args[0].clone()
                } else {
                    Pattern::Tuple(args.clone())
                };
                let (t, b) = self.pattern_test(&payload, &arg_pat);
                if let Some(t) = t {
                    tests.push(t);
                }
                binds.extend(b);
                let test = tests
                    .into_iter()
                    .reduce(|a, b| Expr::BinOp(BinOp::And, Box::new(a), Box::new(b)));
                (test, binds)
            }
        }
    }

    /// Generate a fresh, source-illegal variable name (contains `$`) to avoid
    /// capturing user identifiers in desugared bindings.
    fn fresh_var(&mut self, hint: &str) -> Ident {
        let id = self.gensym;
        self.gensym += 1;
        format!("${hint}{id}")
    }

    /// Build a projection of element `i` (0-based) from an `n`-element tuple held
    /// in variable `tmp`, where tuples are right-nested pairs
    /// `(e0, (e1, (e2, ...)))`. Element `i` is `Snd` applied `i` times, then
    /// `Fst` unless it is the last element (which is the final `Snd`).
    fn tuple_proj(&self, tmp: &str, i: usize, n: usize) -> Expr {
        let mut acc = Expr::Var(tmp.to_string());
        for _ in 0..i {
            acc = Expr::Snd(Box::new(acc));
        }
        if i + 1 < n {
            Expr::Fst(Box::new(acc))
        } else {
            acc
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
            }
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

    /// The canonical Bahasa Melayu spelling for "soft" keyword tokens — domain
    /// keywords that the example corpus also uses as ordinary variable, parameter,
    /// and field names (e.g. `tahap`, `keadaan`, `jenis`, `input`). Returns `None`
    /// for tokens that are *not* allowed as names (structural keywords like `fn`,
    /// `let`, `if`, etc., whose use as a name would be genuinely ambiguous).
    fn soft_keyword_spelling(kind: &TokenKind) -> Option<&'static str> {
        Some(match kind {
            TokenKind::KwLevel => "tahap",
            TokenKind::KwState => "keadaan",
            TokenKind::KwType => "jenis",
            TokenKind::KwInput => "input",
            TokenKind::KwToken => "token",
            TokenKind::KwRole => "peranan",
            TokenKind::KwChannel => "saluran",
            TokenKind::KwPolicy => "dasar",
            TokenKind::KwText_ => "tulisan",
            TokenKind::KwDisplay => "paparan",
            TokenKind::KwSafe => "selamat",
            TokenKind::KwCapability => "keupayaan",
            TokenKind::KwSecret => "rahsia",
            TokenKind::KwRow => "baris",
            TokenKind::KwColumn => "lajur",
            TokenKind::KwMod => "mod",
            TokenKind::KwMerge => "gabung",
            TokenKind::KwCombined => "gabungan",
            TokenKind::KwColor => "warna",
            TokenKind::KwStyle => "gaya",
            // NOTE: `pertama`/`kedua` (KwFst/KwSnd) and `terus` (KwContinue) are
            // intentionally NOT soft keywords — they are projection operators /
            // control-flow in value position, so allowing them as names would be
            // genuinely ambiguous.
            _ => return None,
        })
    }

    /// Parse a binding/parameter/field name. Accepts a normal identifier or a
    /// "soft" keyword (see [`Parser::soft_keyword_spelling`]) used as a name,
    /// which the example corpus does pervasively (`tahap: Teks`, `keadaan: ...`).
    fn parse_binding_name(&mut self) -> Result<Ident, ParseError> {
        match self.peek().map(|t| t.kind.clone()) {
            Some(TokenKind::Identifier(s)) => {
                self.next();
                Ok(s)
            }
            Some(ref k) if Self::soft_keyword_spelling(k).is_some() => {
                let name = Self::soft_keyword_spelling(k).unwrap().to_string();
                self.next();
                Ok(name)
            }
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

    /// Parse an optional trailing `kesan <eff>` effect annotation on a function
    /// type (e.g. `Fn(A) -> B kesan Tulis`). Defaults to `Effect::Pure`.
    fn parse_optional_fn_effect(&mut self) -> Result<Effect, ParseError> {
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::KwEffect)) {
            self.consume(TokenKind::KwEffect)?;
            // Function-type effects only need the joined lattice value.
            self.parse_effect_annotation().map(|(eff, _)| eff)
        } else {
            Ok(Effect::Pure)
        }
    }

    fn parse_ty(&mut self) -> Result<Ty, ParseError> {
        let kind = self.peek().map(|t| t.kind.clone());
        match kind {
            Some(TokenKind::Star) => {
                // *T = RawPtr(T) for FFI
                self.next();
                let inner = self.parse_ty()?;
                Ok(Ty::RawPtr(Box::new(inner)))
            }
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
            }
            Some(TokenKind::Identifier(s)) => {
                self.next();
                match s.as_str() {
                    // Primitives
                    "Int" | "Nombor" => Ok(Ty::Int),
                    // Sized integer types (numeric-tower slice).
                    "u8" => Ok(Ty::IntN { bits: 8, signed: false }),
                    "u16" => Ok(Ty::IntN { bits: 16, signed: false }),
                    "u32" => Ok(Ty::IntN { bits: 32, signed: false }),
                    "u64" => Ok(Ty::IntN { bits: 64, signed: false }),
                    "i8" => Ok(Ty::IntN { bits: 8, signed: true }),
                    "i16" => Ok(Ty::IntN { bits: 16, signed: true }),
                    "i32" => Ok(Ty::IntN { bits: 32, signed: true }),
                    "i64" => Ok(Ty::IntN { bits: 64, signed: true }),
                    // Arbitrary-precision integer (numeric-tower BigInt slice).
                    "Besar" | "BigInt" => Ok(Ty::BigInt),
                    // Arbitrary-precision decimal (numeric-tower decimal slice).
                    "Perpuluhan" | "Decimal" => Ok(Ty::Decimal),
                    // Fixed-scale decimal / money (numeric-tower fixed-point slice).
                    "Wang" | "Money" | "TitikTetap" => Ok(Ty::Fixed),
                    // Binary fixed-point / Q-format (numeric-tower fixed-point slice).
                    "Qmn" | "BinaryFixed" => Ok(Ty::FixedBin),
                    "Bool" | "Benar" => Ok(Ty::Bool),
                    "Unit" => Ok(Ty::Unit),
                    "String" | "Teks" => Ok(Ty::String),
                    "Bytes" | "Bait" => Ok(Ty::Bytes),

                    // Parameterized types: Name<T>
                    "List" | "Senarai" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::List(Box::new(inner)))
                    }
                    "Option" | "Mungkin" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::Option(Box::new(inner)))
                    }
                    "Secret" | "Rahsia" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::Secret(Box::new(inner)))
                    }
                    "Proof" | "Bukti" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::Proof(Box::new(inner)))
                    }
                    "ConstantTime" | "MasaTetap" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::ConstantTime(Box::new(inner)))
                    }
                    "Zeroizing" | "Sifar" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::Zeroizing(Box::new(inner)))
                    }
                    // Ref<T>@level
                    "Ref" | "Ruj" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        self.consume(TokenKind::At)?;
                        let level = self.parse_security_level()?;
                        Ok(Ty::Ref(Box::new(inner), level))
                    }
                    // Sum type: Sum<T1, T2>
                    "Sum" => {
                        self.consume(TokenKind::Lt)?;
                        let t1 = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let t2 = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::Sum(Box::new(t1), Box::new(t2)))
                    }
                    // Function type. Two surface forms are accepted:
                    //   Fn(Param) -> Ret            (Rust-style arrow; 0+ params)
                    //   Fn(ParamTy, RetTy [, Eff])  (legacy comma form)
                    // The AST `Ty::Fn` is single-argument; for multiple params the
                    // first is kept as the representative argument type (the type
                    // layer is not yet fully curried), and an empty `Fn()` uses
                    // Unit as the argument type.
                    "Fn" | "fungsi" => {
                        self.consume(TokenKind::LParen)?;
                        // Collect comma-separated types inside the parens. A
                        // trailing element that is an effect keyword (legacy
                        // 3-arg form `Fn(P, R, Eff)`) is captured separately.
                        let mut tys = Vec::new();
                        let mut legacy_eff: Option<Effect> = None;
                        if !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                            tys.push(self.parse_ty()?);
                            while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                                self.consume(TokenKind::Comma)?;
                                // In the legacy form, the third element is an
                                // effect, not a type. Detect an effect-starting
                                // token and parse it as such.
                                if tys.len() >= 2 && self.peek_starts_effect() {
                                    legacy_eff = Some(self.parse_effect()?);
                                    break;
                                }
                                tys.push(self.parse_ty()?);
                            }
                        }
                        self.consume(TokenKind::RParen)?;

                        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Arrow)) {
                            // Arrow form `Fn(P0, P1, ...) -> Ret [kesan Eff]`. The
                            // AST `Ty::Fn` is single-argument, so the first param
                            // type is the representative (the type layer is not yet
                            // fully curried); `Fn()` uses Unit.
                            self.consume(TokenKind::Arrow)?;
                            let ret_ty = self.parse_ty()?;
                            let eff = self.parse_optional_fn_effect()?;
                            let param_ty = tys.into_iter().next().unwrap_or(Ty::Unit);
                            Ok(Ty::Fn(Box::new(param_ty), Box::new(ret_ty), eff))
                        } else {
                            // Legacy comma form `Fn(ParamTy, RetTy [, Effect])`.
                            let mut it = tys.into_iter();
                            let param_ty = it.next().unwrap_or(Ty::Unit);
                            let ret_ty = it.next().unwrap_or(Ty::Unit);
                            Ok(Ty::Fn(
                                Box::new(param_ty),
                                Box::new(ret_ty),
                                legacy_eff.unwrap_or(Effect::Pure),
                            ))
                        }
                    }
                    // Labeled<T, Level> / Berlabel<T, Level>
                    "Labeled" | "Berlabel" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let level = self.parse_security_level()?;
                        self.consume_type_close()?;
                        Ok(Ty::Labeled(Box::new(inner), level))
                    }
                    // Tainted<T, Source> / Tercemar<T, Source>
                    "Tainted" | "Tercemar" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let source = self.parse_taint_source()?;
                        self.consume_type_close()?;
                        Ok(Ty::Tainted(Box::new(inner), source))
                    }
                    // Sanitized<T, Sanitizer> / Disanitasi<T, Sanitizer>
                    "Sanitized" | "Disanitasi" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume(TokenKind::Comma)?;
                        let san = self.parse_sanitizer()?;
                        self.consume_type_close()?;
                        Ok(Ty::Sanitized(Box::new(inner), san))
                    }
                    // FFI C types
                    "CInt" => Ok(Ty::CInt),
                    "CChar" => Ok(Ty::CChar),
                    "CVoid" => Ok(Ty::CVoid),
                    // Capability<Kind> / Keupayaan<Kind>
                    "Capability" | "Keupayaan" => {
                        self.consume(TokenKind::Lt)?;
                        let kind = self.parse_capability_kind()?;
                        self.consume_type_close()?;
                        Ok(Ty::Capability(kind))
                    }
                    // Chan<SessionType> / Saluran<SessionType>
                    "Chan" | "Saluran" => {
                        self.consume(TokenKind::Lt)?;
                        let st = self.parse_session_type()?;
                        self.consume_type_close()?;
                        Ok(Ty::Chan(st))
                    }
                    // SecureChan<SessionType, Level> / SaluranSelamat<SessionType, Level>
                    "SecureChan" | "SaluranSelamat" => {
                        self.consume(TokenKind::Lt)?;
                        let st = self.parse_session_type()?;
                        self.consume(TokenKind::Comma)?;
                        let level = self.parse_security_level()?;
                        self.consume_type_close()?;
                        Ok(Ty::SecureChan(st, level))
                    }
                    "SmartContract" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::SmartContract(Box::new(inner)))
                    }
                    "Token" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::Token(Box::new(inner)))
                    }
                    "SyariahCompliant" => {
                        self.consume(TokenKind::Lt)?;
                        let inner = self.parse_ty()?;
                        self.consume_type_close()?;
                        Ok(Ty::SyariahCompliant(Box::new(inner)))
                    }
                    // User-defined nominal type (e.g. a `jenis`-declared record
                    // like `JejakAudit`, `Taint`, or a generic `Keupayaan<HakBaca>`).
                    // RIINA has no nominal-type semantics yet (matching the `jenis`
                    // skip in top-level parsing), so an unknown type name is treated
                    // structurally as `Any`. Any `<...>` generic argument list is
                    // consumed (and discarded) so it parses.
                    _ => {
                        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Lt)) {
                            self.skip_type_argument_list();
                        }
                        Ok(Ty::Any)
                    }
                }
            }
            Some(TokenKind::KwSmartContract) => {
                self.next();
                self.consume(TokenKind::Lt)?;
                let inner = self.parse_ty()?;
                self.consume_type_close()?;
                Ok(Ty::SmartContract(Box::new(inner)))
            }
            Some(TokenKind::KwToken) => {
                self.next();
                self.consume(TokenKind::Lt)?;
                let inner = self.parse_ty()?;
                self.consume_type_close()?;
                Ok(Ty::Token(Box::new(inner)))
            }
            Some(TokenKind::KwShariahCompliant) => {
                self.next();
                self.consume(TokenKind::Lt)?;
                let inner = self.parse_ty()?;
                self.consume_type_close()?;
                Ok(Ty::SyariahCompliant(Box::new(inner)))
            }
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
            _ => Err(ParseError {
                kind: ParseErrorKind::InvalidSecurityLevel,
                span: self.current_span,
            }),
        }
    }

    /// Parse an effect annotation that is either a single effect (`kesan Kripto`)
    /// or a parenthesized list (`kesan (Kripto, MasaTetap)`). A list is combined
    /// with `Effect::join` into the dominant effect, since the effect model has
    /// no effect-rows yet. An empty `()` is `Pure`.
    /// Parse an effect annotation, returning both the joined lattice `Effect`
    /// (for propagation/codegen) and the *components* of a compound annotation
    /// (for capability granting — the join is lossy). A single effect yields a
    /// one-element component vector.
    fn parse_effect_annotation(&mut self) -> Result<(Effect, Vec<Effect>), ParseError> {
        if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::LParen)) {
            self.consume(TokenKind::LParen)?;
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RParen)) {
                self.consume(TokenKind::RParen)?;
                return Ok((Effect::Pure, vec![Effect::Pure]));
            }
            // A parenthesized effect set may be separated by `,` or `|`
            // (`kesan (Bersih | SistemFail)`); the components are preserved.
            let first = self.parse_effect()?;
            let mut eff = first;
            let mut set = vec![first];
            while matches!(
                self.peek().map(|t| &t.kind),
                Some(TokenKind::Comma) | Some(TokenKind::Or)
            ) {
                self.next();
                let e = self.parse_effect()?;
                eff = eff.join(e);
                set.push(e);
            }
            self.consume(TokenKind::RParen)?;
            Ok((eff, set))
        } else {
            let e = self.parse_effect()?;
            Ok((e, vec![e]))
        }
    }

    /// True when the next token is an identifier naming an effect (used to
    /// distinguish the legacy `Fn(P, R, Eff)` third element from a type).
    fn peek_starts_effect(&mut self) -> bool {
        matches!(
            self.peek().map(|t| &t.kind),
            Some(TokenKind::Identifier(s)) if matches!(
                s.as_str(),
                "Pure" | "Bersih" | "Mut" | "Ubah" | "Alloc" | "Peruntuk"
                | "Read" | "Baca" | "Write" | "Tulis" | "FileSystem" | "SistemFail"
                | "Network" | "Rangkaian" | "NetworkSecure" | "RangkaianSelamat"
                | "Crypto" | "Kripto" | "ConstantTime" | "MasaTetap" | "Random"
                | "Rawak" | "System" | "Sistem" | "Time" | "Masa" | "Process"
                | "Proses" | "Panel" | "Zirah" | "Benteng" | "Sandi" | "Menara"
                | "Gapura"
            )
        )
    }

    fn parse_effect(&mut self) -> Result<Effect, ParseError> {
        let ident = self.parse_ident()?;
        match ident.as_str() {
            "Pure" | "Bersih" => Ok(Effect::Pure),
            "Mut" | "Ubah" => Ok(Effect::Mut),
            "Alloc" | "Peruntuk" => Ok(Effect::Alloc),
            "Read" | "Baca" => Ok(Effect::Read),
            "Write" | "Tulis" => Ok(Effect::Write),
            "FileSystem" | "SistemFail" => Ok(Effect::FileSystem),
            "Network" | "Rangkaian" => Ok(Effect::Network),
            "NetworkSecure" | "RangkaianSelamat" => Ok(Effect::NetworkSecure),
            "Crypto" | "Kripto" => Ok(Effect::Crypto),
            // `MasaTetap` (constant-time) appears in effect position in many
            // examples. It is a crypto-security guarantee, so it maps to the
            // Crypto effect (there is no distinct constant-time effect variant).
            "ConstantTime" | "MasaTetap" => Ok(Effect::Crypto),
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
            _ => Err(ParseError {
                kind: ParseErrorKind::InvalidEffect,
                span: self.current_span,
            }),
        }
    }

    /// Parse a session type: Send<T, S> | Recv<T, S> | Select<S1, S2> |
    /// Branch<S1, S2> | End | Rec<X, S> | Var<X>
    /// Matches Coq SessionTypes.v session type constructors.
    fn parse_session_type(&mut self) -> Result<SessionType, ParseError> {
        let ident = self.parse_ident()?;
        match ident.as_str() {
            // Send<PayloadType, Continuation>
            "Send" | "Hantar" => {
                self.consume(TokenKind::Lt)?;
                let payload = self.parse_ty()?;
                self.consume(TokenKind::Comma)?;
                let cont = self.parse_session_type()?;
                self.consume_type_close()?;
                Ok(SessionType::Send(Box::new(payload), Box::new(cont)))
            }
            // Recv<PayloadType, Continuation>
            "Recv" | "Terima" => {
                self.consume(TokenKind::Lt)?;
                let payload = self.parse_ty()?;
                self.consume(TokenKind::Comma)?;
                let cont = self.parse_session_type()?;
                self.consume_type_close()?;
                Ok(SessionType::Recv(Box::new(payload), Box::new(cont)))
            }
            // Select<S1, S2> — internal choice
            "Select" | "Pilih" => {
                self.consume(TokenKind::Lt)?;
                let s1 = self.parse_session_type()?;
                self.consume(TokenKind::Comma)?;
                let s2 = self.parse_session_type()?;
                self.consume_type_close()?;
                Ok(SessionType::Select(Box::new(s1), Box::new(s2)))
            }
            // Branch<S1, S2> — external choice
            "Branch" | "Cabang" => {
                self.consume(TokenKind::Lt)?;
                let s1 = self.parse_session_type()?;
                self.consume(TokenKind::Comma)?;
                let s2 = self.parse_session_type()?;
                self.consume_type_close()?;
                Ok(SessionType::Branch(Box::new(s1), Box::new(s2)))
            }
            // End — session termination
            "End" | "Tamat" => Ok(SessionType::End),
            // Rec<X, S> — recursive session type
            "Rec" | "Ulang" => {
                self.consume(TokenKind::Lt)?;
                let var = self.parse_ident()?;
                self.consume(TokenKind::Comma)?;
                let body = self.parse_session_type()?;
                self.consume_type_close()?;
                Ok(SessionType::Rec(var, Box::new(body)))
            }
            // Var<X> — session type variable (for recursion)
            "SVar" | "PembolehubahSesi" => {
                self.consume(TokenKind::Lt)?;
                let var = self.parse_ident()?;
                self.consume_type_close()?;
                Ok(SessionType::Var(var))
            }
            _ => Err(ParseError {
                kind: ParseErrorKind::InvalidSessionType,
                span: self.current_span,
            }),
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
            _ => Err(ParseError {
                kind: ParseErrorKind::ExpectedType,
                span: self.current_span,
            }),
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
            "UrlAllowlist" => Ok(Sanitizer::UrlAllowlist),
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
            _ => Err(ParseError {
                kind: ParseErrorKind::ExpectedType,
                span: self.current_span,
            }),
        }
    }

    // ── JALINAN Phase 6: Choreography & Actor parsing ──────────────────

    /// Parse: koreografi Name { peranan R1, R2; interactions... }
    fn parse_choreography(&mut self) -> Result<TopLevelDecl, ParseError> {
        self.consume(TokenKind::KwChoreography)?;
        let name = self.parse_ident()?;
        self.consume(TokenKind::LBrace)?;
        self.consume(TokenKind::KwRole)?;
        let mut roles = vec![self.parse_ident()?];
        while matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
            self.consume(TokenKind::Comma)?;
            roles.push(self.parse_ident()?);
        }
        self.consume(TokenKind::Semi)?;
        // Parse the protocol relative to the first role, so the stored
        // `SessionType` is that role's local view: `A -> B : T` becomes `Send T`
        // when A is roles[0] and `Recv T` when B is roles[0]. The other role's
        // view is the dual (see `project_choreography` in the typechecker).
        let viewpoint = roles.first().cloned().unwrap_or_default();
        let protocol = self.parse_choreography_protocol(&viewpoint)?;
        self.consume(TokenKind::RBrace)?;
        Ok(TopLevelDecl::Expr(Box::new(Expr::ChoreographyBlock {
            name,
            roles,
            protocol,
        })))
    }

    /// Parse a choreography interaction sequence into the `viewpoint` role's
    /// local `SessionType` (a message *from* the viewpoint is a `Send`, *to* it
    /// a `Recv`; a message between two other roles is skipped from this view).
    fn parse_choreography_protocol(
        &mut self,
        viewpoint: &str,
    ) -> Result<SessionType, ParseError> {
        match self.peek().map(|t| &t.kind) {
            // tamat; → End
            Some(TokenKind::KwEnd) => {
                self.consume(TokenKind::KwEnd)?;
                self.consume(TokenKind::Semi)?;
                Ok(SessionType::End)
            }
            // pilih { Label -> { ... }, Label -> { ... } } — the viewpoint role
            // selects (internal choice).
            Some(TokenKind::KwSelect) => {
                self.consume(TokenKind::KwSelect)?;
                self.consume(TokenKind::LBrace)?;
                let _label1 = self.parse_ident()?;
                self.consume(TokenKind::Arrow)?;
                self.consume(TokenKind::LBrace)?;
                let s1 = self.parse_choreography_protocol(viewpoint)?;
                self.consume(TokenKind::RBrace)?;
                self.consume(TokenKind::Comma)?;
                let _label2 = self.parse_ident()?;
                self.consume(TokenKind::Arrow)?;
                self.consume(TokenKind::LBrace)?;
                let s2 = self.parse_choreography_protocol(viewpoint)?;
                self.consume(TokenKind::RBrace)?;
                self.consume(TokenKind::RBrace)?;
                // Check for continuation after choice block
                if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBrace)) {
                    // End of enclosing block, no continuation
                    Ok(SessionType::Select(Box::new(s1), Box::new(s2)))
                } else {
                    // There is a continuation (e.g. tamat;)
                    let _cont = self.parse_choreography_protocol(viewpoint)?;
                    Ok(SessionType::Select(Box::new(s1), Box::new(s2)))
                }
            }
            // RBrace → implicit end (closing an enclosing block)
            Some(TokenKind::RBrace) => Ok(SessionType::End),
            // Identifier: sender -> receiver: hantar Type; continuation
            Some(TokenKind::Identifier(_)) => {
                let sender = self.parse_ident()?;
                self.consume(TokenKind::Arrow)?;
                let receiver = self.parse_ident()?;
                self.consume(TokenKind::Colon)?;
                self.consume(TokenKind::KwSend)?;
                let msg_ident = self.parse_ident()?;
                self.consume(TokenKind::Semi)?;
                let msg_ty = self.ident_to_ty(&msg_ident);
                let continuation = self.parse_choreography_protocol(viewpoint)?;
                // Role-relative projection of a single message onto `viewpoint`.
                if sender == viewpoint {
                    Ok(SessionType::Send(Box::new(msg_ty), Box::new(continuation)))
                } else if receiver == viewpoint {
                    Ok(SessionType::Recv(Box::new(msg_ty), Box::new(continuation)))
                } else {
                    // Message between two other roles: invisible to this view.
                    Ok(continuation)
                }
            }
            _ => Err(ParseError {
                kind: ParseErrorKind::ExpectedExpression,
                span: self.current_span,
            }),
        }
    }

    /// Map an identifier to a Ty for choreography message types.
    fn ident_to_ty(&self, ident: &str) -> Ty {
        match ident {
            "Nombor" | "Int" => Ty::Int,
            "Benar" | "Bool" => Ty::Bool,
            "Teks" | "String" => Ty::String,
            "Unit" => Ty::Unit,
            _ => Ty::Any,
        }
    }

    /// Parse: pelaku Name { keadaan: Type kendalikan Msg(param) { body } ... }
    fn parse_actor_decl(&mut self) -> Result<TopLevelDecl, ParseError> {
        self.consume(TokenKind::KwActor)?;
        let name = self.parse_ident()?;
        self.consume(TokenKind::LBrace)?;

        // State type: keadaan: Type
        self.consume(TokenKind::KwState)?;
        self.consume(TokenKind::Colon)?;
        let state_ty = self.parse_ty()?;

        // Message handlers: kendalikan Msg(param) { body }
        let mut handlers: Vec<(Ident, Ident, Expr)> = Vec::new();
        while matches!(
            self.peek().map(|t| &t.kind),
            Some(TokenKind::Identifier(s)) if s == "kendalikan"
        ) {
            self.next(); // consume "kendalikan" identifier
            let msg_name = self.parse_ident()?;
            self.consume(TokenKind::LParen)?;
            let param = self.parse_ident()?;
            self.consume(TokenKind::RParen)?;
            self.consume(TokenKind::LBrace)?;
            let body = self.parse_expr()?;
            self.consume(TokenKind::RBrace)?;
            handlers.push((msg_name, param, body));
        }

        self.consume(TokenKind::RBrace)?;

        // Build handler expression
        let handler = if handlers.is_empty() {
            Expr::Unit
        } else if handlers.len() == 1 {
            let (_msg, param, body) = handlers.into_iter().next().unwrap();
            Expr::Lam(param, Ty::Any, Box::new(body))
        } else {
            // Multiple handlers: chain as nested Let bindings of lambdas
            let mut result = Expr::Unit;
            for (_msg, param, body) in handlers.into_iter().rev() {
                let lam = Expr::Lam(param, Ty::Any, Box::new(body));
                result = Expr::Let(
                    "_handler".to_string(),
                    None,
                    Box::new(lam),
                    Box::new(result),
                );
            }
            result
        };

        // Default init state based on state type
        let default_init = match &state_ty {
            Ty::Int => Expr::Int(0),
            Ty::Bool => Expr::Bool(false),
            Ty::String => Expr::String(String::new()),
            _ => Expr::Unit,
        };
        Ok(TopLevelDecl::Expr(Box::new(Expr::ActorDecl {
            name,
            state_ty,
            message_ty: Ty::Any,
            init_state: Box::new(default_init),
            handler: Box::new(handler),
        })))
    }

    /// Parse: lahir ActorType(init_state)
    fn parse_spawn(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwSpawn)?;
        let actor_name = self.parse_ident()?;
        self.consume(TokenKind::LParen)?;
        let init = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::Spawn(Box::new(Expr::Var(actor_name)), Box::new(init)))
    }

    /// Parse: hantar(actor, message)
    fn parse_actor_send(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwSend)?;
        self.consume(TokenKind::LParen)?;
        let actor = self.parse_control_flow()?;
        self.consume(TokenKind::Comma)?;
        let msg = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::ActorSend(Box::new(actor), Box::new(msg)))
    }

    /// Parse: terima(actor)
    fn parse_actor_recv(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwRecv)?;
        self.consume(TokenKind::LParen)?;
        let actor = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::ActorRecv(Box::new(actor)))
    }

    /// Parse: gabung(a, b)
    fn parse_crdt_merge(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwMerge)?;
        self.consume(TokenKind::LParen)?;
        let a = self.parse_control_flow()?;
        self.consume(TokenKind::Comma)?;
        let b = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::CRDTMerge(Box::new(a), Box::new(b)))
    }

    /// Parse: cincang(expr)
    fn parse_content_hash(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwContentHash)?;
        self.consume(TokenKind::LParen)?;
        let e = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::ContentHash(Box::new(e)))
    }

    /// Parse: sahkan(expected_hash, value)
    fn parse_content_verify(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwVerify)?;
        self.consume(TokenKind::LParen)?;
        let expected_hash = self.parse_control_flow()?;
        self.consume(TokenKind::Comma)?;
        let value = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::ContentVerify(
            Box::new(expected_hash),
            Box::new(value),
        ))
    }

    /// Parse: kontrak_pintar(expr) or kontrak_pintar { expr }
    fn parse_contract_deploy(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwSmartContract)?;
        let contract = match self.peek().map(|t| t.kind.clone()) {
            Some(TokenKind::LParen) => {
                self.consume(TokenKind::LParen)?;
                let contract = self.parse_control_flow()?;
                self.consume(TokenKind::RParen)?;
                contract
            }
            Some(TokenKind::LBrace) => {
                self.consume(TokenKind::LBrace)?;
                let contract = self.parse_control_flow()?;
                self.consume(TokenKind::RBrace)?;
                contract
            }
            Some(tok) => {
                return Err(ParseError {
                    kind: ParseErrorKind::UnexpectedToken(tok),
                    span: self.current_span,
                });
            }
            None => {
                return Err(ParseError {
                    kind: ParseErrorKind::UnexpectedEof,
                    span: self.current_span,
                });
            }
        };
        Ok(Expr::ContractDeploy(Box::new(contract)))
    }

    /// Parse: token(from, to, amount) or token::pindah(from, to, amount)
    fn parse_token_transfer(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwToken)?;
        if matches!(
            self.peek().map(|t| t.kind.clone()),
            Some(TokenKind::ColonColon)
        ) {
            self.consume(TokenKind::ColonColon)?;
            match self.peek().map(|t| t.kind.clone()) {
                Some(TokenKind::KwMove) => {
                    self.next();
                }
                Some(TokenKind::Identifier(method))
                    if method == "pindah" || method == "transfer" =>
                {
                    self.next();
                }
                Some(tok) => {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedToken(tok),
                        span: self.current_span,
                    });
                }
                None => {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedEof,
                        span: self.current_span,
                    });
                }
            }
        }
        self.consume(TokenKind::LParen)?;
        let from = self.parse_control_flow()?;
        self.consume(TokenKind::Comma)?;
        let to = self.parse_control_flow()?;
        self.consume(TokenKind::Comma)?;
        let amount = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::TokenTransfer {
            from: Box::new(from),
            to: Box::new(to),
            amount: Box::new(amount),
        })
    }

    /// Parse: zakat(expr)
    fn parse_zakat_calculate(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwZakat)?;
        self.consume(TokenKind::LParen)?;
        let value = self.parse_control_flow()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::ZakatCalculate(Box::new(value)))
    }

    // ════════════════════════════════════════════════════════════════════
    // CAHAYA Phase J5: UI Primitives
    // ════════════════════════════════════════════════════════════════════

    /// Parse a brace-delimited list of UI elements separated by `;`
    fn parse_ui_block_elements(&mut self) -> Result<Vec<Expr>, ParseError> {
        self.consume(TokenKind::LBrace)?;
        let mut elements = Vec::new();
        while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBrace)) {
            elements.push(self.parse_control_flow()?);
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Semi)) {
                self.next();
            }
        }
        self.consume(TokenKind::RBrace)?;
        Ok(elements)
    }

    /// Parse `paparan { elements... }` / `display { elements... }`
    fn parse_display(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwDisplay)?;
        let elements = self.parse_ui_block_elements()?;
        Ok(Expr::UIDisplay(elements))
    }

    /// Parse `baris { elements... }` / `row { elements... }`
    fn parse_row(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwRow)?;
        let elements = self.parse_ui_block_elements()?;
        Ok(Expr::UIRow(elements))
    }

    /// Parse `lajur { elements... }` / `column { elements... }`
    fn parse_column(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwColumn)?;
        let elements = self.parse_ui_block_elements()?;
        Ok(Expr::UIColumn(elements))
    }

    /// Parse `warna(r, g, b)` / `color(r, g, b)`
    fn parse_ui_color(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwColor)?;
        self.consume(TokenKind::LParen)?;
        let r = self.parse_u8_literal()?;
        self.consume(TokenKind::Comma)?;
        let g = self.parse_u8_literal()?;
        self.consume(TokenKind::Comma)?;
        let b = self.parse_u8_literal()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::UIColor(r, g, b))
    }

    /// Parse a u8 integer literal (0-255)
    fn parse_u8_literal(&mut self) -> Result<u8, ParseError> {
        let tok = self.next().ok_or(ParseError {
            kind: ParseErrorKind::UnexpectedEof,
            span: self.current_span,
        })?;
        match &tok.kind {
            TokenKind::LiteralInt(s, _) => {
                let val: u64 = s.parse().map_err(|_| ParseError {
                    kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                    span: tok.span,
                })?;
                if val > 255 {
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                        span: tok.span,
                    });
                }
                Ok(val as u8)
            }
            _ => Err(ParseError {
                kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                span: tok.span,
            }),
        }
    }

    /// Parse `tulisan("text", color)` / `text("text", color)`
    fn parse_ui_text(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwText_)?;
        self.consume(TokenKind::LParen)?;
        let content = self.parse_expr()?;
        self.consume(TokenKind::Comma)?;
        let color = self.parse_expr()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::UIText(Box::new(content), Box::new(color)))
    }

    /// Parse `butang("label", handler)` / `button("label", handler)`
    fn parse_ui_button(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwButton)?;
        self.consume(TokenKind::LParen)?;
        let label = self.parse_expr()?;
        self.consume(TokenKind::Comma)?;
        let handler = self.parse_expr()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::UIButton(Box::new(label), Box::new(handler)))
    }

    /// Parse `kontras(fg, bg)` / `contrast(fg, bg)`
    fn parse_ui_contrast(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwContrast)?;
        self.consume(TokenKind::LParen)?;
        let fg = self.parse_expr()?;
        self.consume(TokenKind::Comma)?;
        let bg = self.parse_expr()?;
        self.consume(TokenKind::RParen)?;
        Ok(Expr::UIContrastCheck(Box::new(fg), Box::new(bg)))
    }

    /// Parse `gaya { pelapik: 16, saiz_fon: 14 }` / `style { padding: 16, font_size: 14 }`
    fn parse_style_decl(&mut self) -> Result<Expr, ParseError> {
        self.consume(TokenKind::KwStyle)?;
        self.consume(TokenKind::LBrace)?;
        let mut padding = None;
        let mut font_size = None;
        while !matches!(self.peek().map(|t| &t.kind), Some(TokenKind::RBrace)) {
            let prop = self.peek().map(|t| t.kind.clone());
            match prop {
                Some(TokenKind::KwPadding) => {
                    self.consume(TokenKind::KwPadding)?;
                    self.consume(TokenKind::Colon)?;
                    let tok = self.next().ok_or(ParseError {
                        kind: ParseErrorKind::UnexpectedEof,
                        span: self.current_span,
                    })?;
                    match &tok.kind {
                        TokenKind::LiteralInt(s, _) => {
                            padding = Some(s.parse::<u32>().map_err(|_| ParseError {
                                kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                                span: tok.span,
                            })?);
                        }
                        _ => {
                            return Err(ParseError {
                                kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                                span: tok.span,
                            })
                        }
                    }
                }
                Some(TokenKind::KwFontSize) => {
                    self.consume(TokenKind::KwFontSize)?;
                    self.consume(TokenKind::Colon)?;
                    let tok = self.next().ok_or(ParseError {
                        kind: ParseErrorKind::UnexpectedEof,
                        span: self.current_span,
                    })?;
                    match &tok.kind {
                        TokenKind::LiteralInt(s, _) => {
                            font_size = Some(s.parse::<u32>().map_err(|_| ParseError {
                                kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                                span: tok.span,
                            })?);
                        }
                        _ => {
                            return Err(ParseError {
                                kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                                span: tok.span,
                            })
                        }
                    }
                }
                _ => {
                    let tok = self.next().ok_or(ParseError {
                        kind: ParseErrorKind::UnexpectedEof,
                        span: self.current_span,
                    })?;
                    return Err(ParseError {
                        kind: ParseErrorKind::UnexpectedToken(tok.kind.clone()),
                        span: tok.span,
                    });
                }
            }
            // consume optional comma separator
            if matches!(self.peek().map(|t| &t.kind), Some(TokenKind::Comma)) {
                self.next();
            }
        }
        self.consume(TokenKind::RBrace)?;
        Ok(Expr::UIStyleDecl { padding, font_size })
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
            _ => Err(ParseError {
                kind: ParseErrorKind::ExpectedType,
                span: self.current_span,
            }),
        }
    }
}

#[cfg(test)]
mod tests;
