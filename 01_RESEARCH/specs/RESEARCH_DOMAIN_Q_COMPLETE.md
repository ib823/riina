# TERAS-LANG Research Domain Q: Compiler Architecture and Implementation

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-Q-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | Q-01 through Q-10 |
| Domain | Q: Compiler Architecture and Implementation |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# Q-01: Compiler Architecture Foundations

## Executive Summary

The TERAS compiler (terasc) must translate security-annotated source code into verified, efficient machine code while preserving security properties throughout compilation. The architecture must support incremental compilation, separate compilation, and integration with verification tools.

## Compiler Pipeline

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    TERAS Compiler Pipeline                          â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Source â†’ Lexer â†’ Parser â†’ AST â†’ Type Checker â†’ MIR â†’ Optimizer    â”‚
â”‚                                        â†“                            â”‚
â”‚                              Security Checker                       â”‚
â”‚                                        â†“                            â”‚
â”‚                               Code Generator â†’ Binary               â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Phases:
1. Frontend: Source â†’ AST (parsing, desugaring)
2. Middle: AST â†’ MIR (type checking, security analysis)
3. Backend: MIR â†’ Binary (optimization, code generation)
```

## Compiler Components

```rust
// Main compiler structure
struct Compiler {
    session: Session,
    source_map: SourceMap,
    diagnostics: DiagnosticsEngine,
}

impl Compiler {
    fn compile(&mut self, input: &Path) -> Result<CompileOutput, CompileError> {
        // 1. Parse
        let ast = self.parse(input)?;
        
        // 2. Resolve names
        let resolved = self.resolve(&ast)?;
        
        // 3. Type check
        let typed = self.type_check(&resolved)?;
        
        // 4. Security analysis
        let verified = self.security_check(&typed)?;
        
        // 5. Lower to MIR
        let mir = self.lower_to_mir(&verified)?;
        
        // 6. Optimize
        let optimized = self.optimize(&mir)?;
        
        // 7. Code generation
        let output = self.codegen(&optimized)?;
        
        Ok(output)
    }
}

// Compilation session
struct Session {
    opts: CompilerOptions,
    target: Target,
    crate_types: Vec<CrateType>,
    security_level: SecurityLevel,
}

// Compiler options
struct CompilerOptions {
    optimization_level: OptLevel,
    debug_info: DebugInfo,
    security_checks: SecurityChecks,
    incremental: bool,
    parallel: bool,
}
```

## TERAS Decision Q-01

**IMPLEMENT** compiler architecture:
1. Multi-phase pipeline
2. Security-integrated passes
3. Incremental compilation
4. Parallel processing

### Architecture Decision ID: `TERAS-ARCH-Q01-COMP-001`

---

# Q-02: Lexical Analysis

## Lexer Design

```rust
// Token types
#[derive(Clone, Debug)]
enum TokenKind {
    // Keywords
    Fn, Let, Mut, If, Else, Match, While, For, Loop,
    Return, Break, Continue, Struct, Enum, Trait, Impl,
    Pub, Mod, Use, As, Where, Async, Await, Effect, Handler,
    
    // Security keywords
    Capability, Clearance, Label, Audit, Unsafe,
    
    // Literals
    IntLit(u128),
    FloatLit(f64),
    StringLit(String),
    CharLit(char),
    BoolLit(bool),
    
    // Identifiers
    Ident(Symbol),
    Lifetime(Symbol),
    
    // Operators
    Plus, Minus, Star, Slash, Percent,
    Eq, EqEq, Ne, Lt, Le, Gt, Ge,
    And, AndAnd, Or, OrOr, Not,
    BitAnd, BitOr, BitXor, Shl, Shr,
    
    // Delimiters
    LParen, RParen, LBrace, RBrace, LBracket, RBracket,
    Comma, Colon, ColonColon, Semi, Dot, DotDot, DotDotEq,
    Arrow, FatArrow, Question, At, Hash, Dollar,
    
    // Special
    Eof,
    Error(LexError),
}

struct Token {
    kind: TokenKind,
    span: Span,
}

struct Span {
    lo: BytePos,
    hi: BytePos,
}

// Lexer
struct Lexer<'src> {
    source: &'src str,
    pos: usize,
    start: usize,
    tokens: Vec<Token>,
}

impl<'src> Lexer<'src> {
    fn lex(&mut self) -> Vec<Token> {
        while !self.is_at_end() {
            self.start = self.pos;
            self.scan_token();
        }
        
        self.tokens.push(Token {
            kind: TokenKind::Eof,
            span: Span { lo: self.pos, hi: self.pos },
        });
        
        std::mem::take(&mut self.tokens)
    }
    
    fn scan_token(&mut self) {
        let c = self.advance();
        
        let kind = match c {
            // Single character tokens
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semi,
            '@' => TokenKind::At,
            '#' => TokenKind::Hash,
            
            // Multi-character tokens
            ':' => if self.match_char(':') { TokenKind::ColonColon } else { TokenKind::Colon },
            '.' => self.scan_dot(),
            '-' => if self.match_char('>') { TokenKind::Arrow } else { TokenKind::Minus },
            '=' => self.scan_eq(),
            '<' => self.scan_lt(),
            '>' => self.scan_gt(),
            '&' => self.scan_and(),
            '|' => self.scan_or(),
            '!' => if self.match_char('=') { TokenKind::Ne } else { TokenKind::Not },
            
            // Literals
            '"' => self.scan_string(),
            '\'' => self.scan_char_or_lifetime(),
            '0'..='9' => self.scan_number(),
            
            // Identifiers and keywords
            'a'..='z' | 'A'..='Z' | '_' => self.scan_identifier(),
            
            // Whitespace
            ' ' | '\t' | '\n' | '\r' => return,
            
            // Comments
            '/' => {
                if self.match_char('/') {
                    self.skip_line_comment();
                    return;
                } else if self.match_char('*') {
                    self.skip_block_comment();
                    return;
                } else {
                    TokenKind::Slash
                }
            }
            
            _ => TokenKind::Error(LexError::UnexpectedChar(c)),
        };
        
        self.add_token(kind);
    }
    
    fn scan_identifier(&mut self) -> TokenKind {
        while self.peek().map_or(false, |c| c.is_alphanumeric() || c == '_') {
            self.advance();
        }
        
        let text = &self.source[self.start..self.pos];
        self.keyword_or_ident(text)
    }
    
    fn keyword_or_ident(&self, text: &str) -> TokenKind {
        match text {
            "fn" => TokenKind::Fn,
            "let" => TokenKind::Let,
            "mut" => TokenKind::Mut,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "match" => TokenKind::Match,
            "while" => TokenKind::While,
            "for" => TokenKind::For,
            "loop" => TokenKind::Loop,
            "return" => TokenKind::Return,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "struct" => TokenKind::Struct,
            "enum" => TokenKind::Enum,
            "trait" => TokenKind::Trait,
            "impl" => TokenKind::Impl,
            "pub" => TokenKind::Pub,
            "mod" => TokenKind::Mod,
            "use" => TokenKind::Use,
            "as" => TokenKind::As,
            "where" => TokenKind::Where,
            "async" => TokenKind::Async,
            "await" => TokenKind::Await,
            "effect" => TokenKind::Effect,
            "handler" => TokenKind::Handler,
            "capability" => TokenKind::Capability,
            "clearance" => TokenKind::Clearance,
            "label" => TokenKind::Label,
            "audit" => TokenKind::Audit,
            "unsafe" => TokenKind::Unsafe,
            "true" => TokenKind::BoolLit(true),
            "false" => TokenKind::BoolLit(false),
            _ => TokenKind::Ident(Symbol::intern(text)),
        }
    }
}
```

## TERAS Decision Q-02

**IMPLEMENT** lexer:
1. Security keyword support
2. Span tracking
3. Error recovery
4. Unicode identifiers

### Architecture Decision ID: `TERAS-ARCH-Q02-LEX-001`

---

# Q-03: Parsing

## Parser Design

```rust
// Parser
struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    diagnostics: &'a mut DiagnosticsEngine,
}

impl<'a> Parser<'a> {
    fn parse_crate(&mut self) -> Result<Crate, ParseError> {
        let mut items = vec![];
        
        while !self.is_at_end() {
            items.push(self.parse_item()?);
        }
        
        Ok(Crate { items })
    }
    
    fn parse_item(&mut self) -> Result<Item, ParseError> {
        let attrs = self.parse_attributes()?;
        let vis = self.parse_visibility()?;
        
        match self.peek_kind() {
            TokenKind::Fn => self.parse_function(attrs, vis),
            TokenKind::Struct => self.parse_struct(attrs, vis),
            TokenKind::Enum => self.parse_enum(attrs, vis),
            TokenKind::Trait => self.parse_trait(attrs, vis),
            TokenKind::Impl => self.parse_impl(attrs),
            TokenKind::Mod => self.parse_module(attrs, vis),
            TokenKind::Use => self.parse_use(attrs, vis),
            TokenKind::Effect => self.parse_effect(attrs, vis),
            TokenKind::Handler => self.parse_handler(attrs, vis),
            _ => Err(self.unexpected_token()),
        }
    }
    
    fn parse_function(&mut self, attrs: Vec<Attribute>, vis: Visibility) -> Result<Item, ParseError> {
        self.expect(TokenKind::Fn)?;
        let name = self.parse_ident()?;
        
        // Generics
        let generics = if self.check(TokenKind::Lt) {
            self.parse_generics()?
        } else {
            Generics::default()
        };
        
        // Parameters
        self.expect(TokenKind::LParen)?;
        let params = self.parse_params()?;
        self.expect(TokenKind::RParen)?;
        
        // Return type
        let return_type = if self.match_token(TokenKind::Arrow) {
            Some(self.parse_type()?)
        } else {
            None
        };
        
        // Effects
        let effects = if self.match_token(TokenKind::Not) {
            self.parse_effect_list()?
        } else {
            vec![]
        };
        
        // Security annotations
        let security = self.parse_security_annotations()?;
        
        // Where clause
        let where_clause = if self.check_keyword("where") {
            self.parse_where_clause()?
        } else {
            WhereClause::default()
        };
        
        // Body
        let body = self.parse_block()?;
        
        Ok(Item::Function(Function {
            attrs,
            vis,
            name,
            generics,
            params,
            return_type,
            effects,
            security,
            where_clause,
            body,
        }))
    }
    
    fn parse_expression(&mut self) -> Result<Expr, ParseError> {
        self.parse_expr_with_precedence(0)
    }
    
    fn parse_expr_with_precedence(&mut self, min_prec: u8) -> Result<Expr, ParseError> {
        let mut lhs = self.parse_unary()?;
        
        while let Some((op, prec, assoc)) = self.peek_binary_op() {
            if prec < min_prec {
                break;
            }
            
            self.advance();
            
            let next_min_prec = match assoc {
                Associativity::Left => prec + 1,
                Associativity::Right => prec,
            };
            
            let rhs = self.parse_expr_with_precedence(next_min_prec)?;
            
            lhs = Expr::Binary(Box::new(BinaryExpr {
                op,
                lhs,
                rhs,
                span: lhs.span().merge(rhs.span()),
            }));
        }
        
        Ok(lhs)
    }
}
```

## AST Definition

```rust
// Abstract Syntax Tree
struct Crate {
    items: Vec<Item>,
}

enum Item {
    Function(Function),
    Struct(Struct),
    Enum(Enum),
    Trait(Trait),
    Impl(Impl),
    Module(Module),
    Use(UseDecl),
    Effect(EffectDecl),
    Handler(HandlerDecl),
}

struct Function {
    attrs: Vec<Attribute>,
    vis: Visibility,
    name: Ident,
    generics: Generics,
    params: Vec<Param>,
    return_type: Option<Type>,
    effects: Vec<EffectRef>,
    security: SecurityAnnotations,
    where_clause: WhereClause,
    body: Block,
}

struct SecurityAnnotations {
    capabilities: Vec<Capability>,
    clearance: Option<Clearance>,
    labels: Vec<LabelAnnotation>,
    audit: Option<AuditLevel>,
}

enum Expr {
    Literal(Literal),
    Path(Path),
    Binary(Box<BinaryExpr>),
    Unary(Box<UnaryExpr>),
    Call(Box<CallExpr>),
    MethodCall(Box<MethodCallExpr>),
    Field(Box<FieldExpr>),
    Index(Box<IndexExpr>),
    If(Box<IfExpr>),
    Match(Box<MatchExpr>),
    Block(Box<Block>),
    Loop(Box<LoopExpr>),
    While(Box<WhileExpr>),
    For(Box<ForExpr>),
    Return(Box<ReturnExpr>),
    Break(Box<BreakExpr>),
    Continue(Box<ContinueExpr>),
    Closure(Box<Closure>),
    Await(Box<AwaitExpr>),
    Perform(Box<PerformExpr>),  // Effect operation
    Handle(Box<HandleExpr>),    // Effect handler
}
```

## TERAS Decision Q-03

**IMPLEMENT** parser:
1. Pratt parsing for expressions
2. Error recovery
3. Security annotations
4. Effect syntax

### Architecture Decision ID: `TERAS-ARCH-Q03-PARSE-001`

---

# Q-04: Name Resolution

## Resolver Design

```rust
// Name resolver
struct Resolver<'a> {
    session: &'a Session,
    crate_graph: &'a CrateGraph,
    def_map: DefMap,
    scope_stack: Vec<Scope>,
}

struct DefMap {
    modules: HashMap<ModuleId, ModuleData>,
    items: HashMap<DefId, DefKind>,
    impls: Vec<ImplData>,
}

struct ModuleData {
    parent: Option<ModuleId>,
    children: HashMap<Symbol, ModuleId>,
    items: HashMap<Symbol, DefId>,
    imports: Vec<Import>,
}

impl<'a> Resolver<'a> {
    fn resolve(&mut self, crate_: &Crate) -> Result<ResolvedCrate, ResolveError> {
        // Phase 1: Build module tree
        self.build_module_tree(crate_)?;
        
        // Phase 2: Resolve imports
        self.resolve_imports()?;
        
        // Phase 3: Resolve names in items
        for item in &crate_.items {
            self.resolve_item(item)?;
        }
        
        Ok(ResolvedCrate {
            def_map: self.def_map.clone(),
        })
    }
    
    fn resolve_path(&mut self, path: &Path) -> Result<Res, ResolveError> {
        let mut current_ns = self.current_module();
        
        for (i, segment) in path.segments.iter().enumerate() {
            if i == 0 {
                // First segment: look up in scope
                match self.lookup_in_scope(&segment.ident) {
                    Some(res) => {
                        if path.segments.len() == 1 {
                            return Ok(res);
                        }
                        current_ns = self.res_to_module(res)?;
                    }
                    None => return Err(ResolveError::NotFound(segment.ident.clone())),
                }
            } else {
                // Subsequent segments: look up in namespace
                match self.lookup_in_module(current_ns, &segment.ident) {
                    Some(res) => {
                        if i == path.segments.len() - 1 {
                            return Ok(res);
                        }
                        current_ns = self.res_to_module(res)?;
                    }
                    None => return Err(ResolveError::NotFound(segment.ident.clone())),
                }
            }
        }
        
        unreachable!()
    }
    
    fn lookup_in_scope(&self, name: &Ident) -> Option<Res> {
        // Search from innermost to outermost scope
        for scope in self.scope_stack.iter().rev() {
            if let Some(res) = scope.lookup(name) {
                return Some(res);
            }
        }
        
        // Search in current module
        self.lookup_in_module(self.current_module(), name)
    }
}
```

## TERAS Decision Q-04

**IMPLEMENT** name resolution:
1. Module tree construction
2. Import resolution
3. Scope chain lookup
4. Security annotation resolution

### Architecture Decision ID: `TERAS-ARCH-Q04-RES-001`

---

# Q-05: Type Checking

## Type Checker Design

```rust
// Bidirectional type checker
struct TypeChecker<'a> {
    session: &'a Session,
    def_map: &'a DefMap,
    type_context: TypeContext,
    constraints: Vec<Constraint>,
}

impl<'a> TypeChecker<'a> {
    // Check mode: verify expression has expected type
    fn check(&mut self, expr: &Expr, expected: &Type) -> Result<TypedExpr, TypeError> {
        match (expr, expected) {
            // Lambda check
            (Expr::Closure(closure), Type::Function(fn_ty)) => {
                self.check_closure(closure, fn_ty)
            }
            
            // If-then-else check
            (Expr::If(if_expr), expected) => {
                let cond = self.check(&if_expr.cond, &Type::Bool)?;
                let then_branch = self.check(&if_expr.then_branch, expected)?;
                let else_branch = if_expr.else_branch.as_ref()
                    .map(|e| self.check(e, expected))
                    .transpose()?;
                
                Ok(TypedExpr::If(TypedIfExpr {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_branch),
                    else_branch: else_branch.map(Box::new),
                    ty: expected.clone(),
                }))
            }
            
            // Fall through to infer and unify
            _ => {
                let inferred = self.infer(expr)?;
                self.unify(&inferred.ty(), expected)?;
                Ok(inferred)
            }
        }
    }
    
    // Infer mode: synthesize type from expression
    fn infer(&mut self, expr: &Expr) -> Result<TypedExpr, TypeError> {
        match expr {
            Expr::Literal(lit) => Ok(self.infer_literal(lit)),
            
            Expr::Path(path) => self.infer_path(path),
            
            Expr::Binary(binary) => self.infer_binary(binary),
            
            Expr::Call(call) => self.infer_call(call),
            
            Expr::Field(field) => self.infer_field(field),
            
            Expr::If(if_expr) => {
                let cond = self.check(&if_expr.cond, &Type::Bool)?;
                let then_branch = self.infer(&if_expr.then_branch)?;
                let else_branch = if_expr.else_branch.as_ref()
                    .map(|e| self.check(e, &then_branch.ty()))
                    .transpose()?;
                
                Ok(TypedExpr::If(TypedIfExpr {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_branch.clone()),
                    else_branch: else_branch.map(Box::new),
                    ty: then_branch.ty(),
                }))
            }
            
            Expr::Perform(perform) => self.infer_perform(perform),
            
            _ => todo!("infer {:?}", expr),
        }
    }
    
    fn infer_call(&mut self, call: &CallExpr) -> Result<TypedExpr, TypeError> {
        let callee = self.infer(&call.callee)?;
        
        let fn_ty = match callee.ty() {
            Type::Function(fn_ty) => fn_ty,
            ty => return Err(TypeError::NotCallable(ty)),
        };
        
        // Check argument count
        if call.args.len() != fn_ty.params.len() {
            return Err(TypeError::ArgCountMismatch {
                expected: fn_ty.params.len(),
                found: call.args.len(),
            });
        }
        
        // Check arguments
        let args = call.args.iter().zip(&fn_ty.params)
            .map(|(arg, param_ty)| self.check(arg, param_ty))
            .collect::<Result<Vec<_>, _>>()?;
        
        // Collect effects
        let effects = fn_ty.effects.clone();
        
        Ok(TypedExpr::Call(TypedCallExpr {
            callee: Box::new(callee),
            args,
            ty: *fn_ty.return_type.clone(),
            effects,
        }))
    }
    
    fn unify(&mut self, a: &Type, b: &Type) -> Result<(), TypeError> {
        match (a, b) {
            (Type::Var(v), ty) | (ty, Type::Var(v)) => {
                self.bind_var(*v, ty.clone())
            }
            
            (Type::Primitive(p1), Type::Primitive(p2)) if p1 == p2 => Ok(()),
            
            (Type::Function(f1), Type::Function(f2)) => {
                if f1.params.len() != f2.params.len() {
                    return Err(TypeError::Mismatch(a.clone(), b.clone()));
                }
                
                for (p1, p2) in f1.params.iter().zip(&f2.params) {
                    self.unify(p1, p2)?;
                }
                
                self.unify(&f1.return_type, &f2.return_type)?;
                self.unify_effects(&f1.effects, &f2.effects)?;
                
                Ok(())
            }
            
            (Type::Struct(s1), Type::Struct(s2)) if s1.def_id == s2.def_id => {
                for (a1, a2) in s1.type_args.iter().zip(&s2.type_args) {
                    self.unify(a1, a2)?;
                }
                Ok(())
            }
            
            _ => Err(TypeError::Mismatch(a.clone(), b.clone())),
        }
    }
}
```

## TERAS Decision Q-05

**IMPLEMENT** type checking:
1. Bidirectional type checking
2. Effect type checking
3. Constraint solving
4. Security type verification

### Architecture Decision ID: `TERAS-ARCH-Q05-TYPE-001`

---

# Q-06: Security Analysis

## Security Checker

```rust
// Security analysis pass
struct SecurityChecker<'a> {
    session: &'a Session,
    typed_crate: &'a TypedCrate,
    security_context: SecurityContext,
    violations: Vec<SecurityViolation>,
}

impl<'a> SecurityChecker<'a> {
    fn check(&mut self) -> Result<VerifiedCrate, SecurityError> {
        for item in &self.typed_crate.items {
            self.check_item(item)?;
        }
        
        if !self.violations.is_empty() {
            return Err(SecurityError::Violations(self.violations.clone()));
        }
        
        Ok(VerifiedCrate {
            typed_crate: self.typed_crate.clone(),
        })
    }
    
    fn check_item(&mut self, item: &TypedItem) -> Result<(), SecurityError> {
        match item {
            TypedItem::Function(func) => self.check_function(func),
            TypedItem::Impl(impl_) => self.check_impl(impl_),
            _ => Ok(()),
        }
    }
    
    fn check_function(&mut self, func: &TypedFunction) -> Result<(), SecurityError> {
        // Verify capability requirements
        self.verify_capabilities(func)?;
        
        // Check IFC compliance
        self.check_ifc(func)?;
        
        // Check audit requirements
        self.check_audit(func)?;
        
        // Check body
        self.with_security_context(&func.security, |checker| {
            checker.check_block(&func.body)
        })
    }
    
    fn verify_capabilities(&mut self, func: &TypedFunction) -> Result<(), SecurityError> {
        // Collect required capabilities from body
        let required = self.collect_required_capabilities(&func.body);
        
        // Check all are declared
        for cap in &required {
            if !func.security.capabilities.contains(cap) {
                self.violations.push(SecurityViolation::MissingCapability {
                    function: func.name.clone(),
                    capability: cap.clone(),
                });
            }
        }
        
        Ok(())
    }
    
    fn check_ifc(&mut self, func: &TypedFunction) -> Result<(), SecurityError> {
        // Check information flow within function
        let mut ifc_checker = IFCChecker::new();
        
        // Initialize parameter labels
        for param in &func.params {
            if let Some(label) = &param.label {
                ifc_checker.set_label(&param.name, label.clone());
            }
        }
        
        // Check body
        ifc_checker.check_block(&func.body)?;
        
        // Verify return label
        if let Some(return_label) = &func.return_label {
            let inferred = ifc_checker.infer_label(&func.body)?;
            if !inferred.flows_to(return_label) {
                self.violations.push(SecurityViolation::IFCViolation {
                    source_label: inferred,
                    target_label: return_label.clone(),
                    location: func.span,
                });
            }
        }
        
        Ok(())
    }
    
    fn check_audit(&mut self, func: &TypedFunction) -> Result<(), SecurityError> {
        if let Some(audit_level) = &func.security.audit {
            // Verify audit calls are present for required operations
            let audit_calls = self.collect_audit_calls(&func.body);
            let required_audits = self.required_audits(func, audit_level);
            
            for required in required_audits {
                if !audit_calls.contains(&required) {
                    self.violations.push(SecurityViolation::MissingAudit {
                        function: func.name.clone(),
                        operation: required,
                    });
                }
            }
        }
        
        Ok(())
    }
}
```

## IFC Checker

```rust
// Information flow control checker
struct IFCChecker {
    label_env: HashMap<Ident, Label>,
    pc_label: Label,
}

impl IFCChecker {
    fn check_expr(&mut self, expr: &TypedExpr) -> Result<Label, IFCError> {
        match expr {
            TypedExpr::Literal(_) => Ok(Label::public()),
            
            TypedExpr::Path(path) => {
                self.label_env.get(&path.ident)
                    .cloned()
                    .ok_or(IFCError::UnlabeledVariable(path.ident.clone()))
            }
            
            TypedExpr::Binary(binary) => {
                let lhs_label = self.check_expr(&binary.lhs)?;
                let rhs_label = self.check_expr(&binary.rhs)?;
                Ok(lhs_label.join(&rhs_label))
            }
            
            TypedExpr::If(if_expr) => {
                let cond_label = self.check_expr(&if_expr.cond)?;
                
                // Raise PC for branches
                let old_pc = self.pc_label.clone();
                self.pc_label = self.pc_label.join(&cond_label);
                
                let then_label = self.check_expr(&if_expr.then_branch)?;
                let else_label = if_expr.else_branch.as_ref()
                    .map(|e| self.check_expr(e))
                    .transpose()?
                    .unwrap_or(Label::public());
                
                self.pc_label = old_pc;
                
                Ok(then_label.join(&else_label).join(&cond_label))
            }
            
            TypedExpr::Call(call) => {
                // Function's return label joined with argument labels
                let arg_labels: Result<Vec<_>, _> = call.args.iter()
                    .map(|a| self.check_expr(a))
                    .collect();
                
                let combined = arg_labels?.into_iter()
                    .fold(Label::public(), |acc, l| acc.join(&l));
                
                Ok(combined.join(&call.ty.label().unwrap_or(Label::public())))
            }
            
            _ => Ok(Label::public()),
        }
    }
    
    fn check_assignment(&mut self, target: &Ident, source: &TypedExpr) -> Result<(), IFCError> {
        let source_label = self.check_expr(source)?;
        let target_label = self.label_env.get(target)
            .ok_or(IFCError::UnlabeledVariable(target.clone()))?;
        
        // Check: source_label âŠ” pc_label âŠ‘ target_label
        let effective_label = source_label.join(&self.pc_label);
        if !effective_label.flows_to(target_label) {
            return Err(IFCError::IllegalFlow {
                source: effective_label,
                target: target_label.clone(),
            });
        }
        
        Ok(())
    }
}
```

## TERAS Decision Q-06

**IMPLEMENT** security analysis:
1. Capability verification
2. IFC checking
3. Audit verification
4. Violation reporting

### Architecture Decision ID: `TERAS-ARCH-Q06-SEC-001`

---

# Q-07: Middle Intermediate Representation

## MIR Design

```rust
// MIR - Middle Intermediate Representation
struct Mir {
    functions: HashMap<DefId, MirFunction>,
}

struct MirFunction {
    def_id: DefId,
    params: Vec<Local>,
    return_local: Local,
    locals: Vec<LocalDecl>,
    basic_blocks: Vec<BasicBlock>,
    security: MirSecurity,
}

struct LocalDecl {
    ty: Type,
    mutability: Mutability,
    security_label: Option<Label>,
}

struct BasicBlock {
    statements: Vec<Statement>,
    terminator: Terminator,
}

enum Statement {
    Assign(Place, Rvalue),
    StorageLive(Local),
    StorageDead(Local),
    Audit(AuditStatement),
    CapabilityCheck(Capability),
    Nop,
}

enum Rvalue {
    Use(Operand),
    BinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Ref(BorrowKind, Place),
    AddressOf(Mutability, Place),
    Aggregate(AggregateKind, Vec<Operand>),
    Discriminant(Place),
    Cast(CastKind, Operand, Type),
}

enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

struct Place {
    local: Local,
    projection: Vec<PlaceElem>,
}

enum PlaceElem {
    Deref,
    Field(FieldIdx),
    Index(Local),
    ConstantIndex { offset: u64, from_end: bool },
    Subslice { from: u64, to: u64 },
    Downcast(VariantIdx),
}

enum Terminator {
    Goto { target: BasicBlockId },
    SwitchInt { discr: Operand, targets: SwitchTargets },
    Return,
    Unreachable,
    Call { func: Operand, args: Vec<Operand>, destination: Place, target: BasicBlockId },
    Assert { cond: Operand, expected: bool, target: BasicBlockId },
    Drop { place: Place, target: BasicBlockId },
    PerformEffect { effect: EffectId, op: EffectOp, args: Vec<Operand>, destination: Place, target: BasicBlockId },
}
```

## MIR Lowering

```rust
// Lower typed AST to MIR
struct MirBuilder<'a> {
    session: &'a Session,
    typed_crate: &'a TypedCrate,
    mir: Mir,
    current_function: Option<MirFunction>,
    local_counter: u32,
    block_counter: u32,
}

impl<'a> MirBuilder<'a> {
    fn lower(&mut self) -> Mir {
        for item in &self.typed_crate.items {
            if let TypedItem::Function(func) = item {
                let mir_func = self.lower_function(func);
                self.mir.functions.insert(func.def_id, mir_func);
            }
        }
        
        std::mem::take(&mut self.mir)
    }
    
    fn lower_function(&mut self, func: &TypedFunction) -> MirFunction {
        let mut mir_func = MirFunction {
            def_id: func.def_id,
            params: vec![],
            return_local: Local(0),
            locals: vec![],
            basic_blocks: vec![],
            security: MirSecurity::from(&func.security),
        };
        
        self.current_function = Some(mir_func);
        
        // Create return local
        let return_local = self.new_local(func.return_type.clone());
        self.current_function.as_mut().unwrap().return_local = return_local;
        
        // Create parameter locals
        for param in &func.params {
            let local = self.new_local(param.ty.clone());
            self.current_function.as_mut().unwrap().params.push(local);
        }
        
        // Lower body
        let entry_block = self.new_block();
        self.lower_block(&func.body, entry_block);
        
        self.current_function.take().unwrap()
    }
    
    fn lower_expr(&mut self, expr: &TypedExpr, block: BasicBlockId) -> (Operand, BasicBlockId) {
        match expr {
            TypedExpr::Literal(lit) => {
                let constant = self.lower_literal(lit);
                (Operand::Constant(constant), block)
            }
            
            TypedExpr::Binary(binary) => {
                let (lhs, block) = self.lower_expr(&binary.lhs, block);
                let (rhs, block) = self.lower_expr(&binary.rhs, block);
                
                let result = self.new_temp(binary.ty.clone());
                self.push_statement(block, Statement::Assign(
                    Place::local(result),
                    Rvalue::BinaryOp(binary.op, lhs, rhs),
                ));
                
                (Operand::Copy(Place::local(result)), block)
            }
            
            TypedExpr::Call(call) => {
                let (callee, mut block) = self.lower_expr(&call.callee, block);
                
                let mut args = vec![];
                for arg in &call.args {
                    let (arg_op, new_block) = self.lower_expr(arg, block);
                    args.push(arg_op);
                    block = new_block;
                }
                
                let result = self.new_temp(call.ty.clone());
                let next_block = self.new_block();
                
                self.set_terminator(block, Terminator::Call {
                    func: callee,
                    args,
                    destination: Place::local(result),
                    target: next_block,
                });
                
                (Operand::Copy(Place::local(result)), next_block)
            }
            
            _ => todo!(),
        }
    }
}
```

## TERAS Decision Q-07

**IMPLEMENT** MIR:
1. Control flow graph
2. Explicit drops
3. Security annotations
4. Effect operations

### Architecture Decision ID: `TERAS-ARCH-Q07-MIR-001`

---

# Q-08: Optimization Passes

## Optimization Pipeline

```rust
// Optimization manager
struct OptimizationPipeline {
    passes: Vec<Box<dyn OptPass>>,
}

impl OptimizationPipeline {
    fn new(opt_level: OptLevel) -> Self {
        let mut passes: Vec<Box<dyn OptPass>> = vec![];
        
        // Always run these
        passes.push(Box::new(SimplifyCfg));
        passes.push(Box::new(ConstantPropagation));
        passes.push(Box::new(DeadCodeElimination));
        
        if opt_level >= OptLevel::O1 {
            passes.push(Box::new(Inlining { threshold: 50 }));
            passes.push(Box::new(CopyPropagation));
            passes.push(Box::new(CommonSubexprElimination));
        }
        
        if opt_level >= OptLevel::O2 {
            passes.push(Box::new(Inlining { threshold: 200 }));
            passes.push(Box::new(LoopInvariantCodeMotion));
            passes.push(Box::new(ScalarReplacement));
        }
        
        if opt_level >= OptLevel::O3 {
            passes.push(Box::new(AggressiveInlining));
            passes.push(Box::new(LoopUnrolling));
            passes.push(Box::new(Vectorization));
        }
        
        // Security-preserving optimization verification
        passes.push(Box::new(SecurityPreservation));
        
        OptimizationPipeline { passes }
    }
    
    fn run(&self, mir: &mut Mir) {
        for pass in &self.passes {
            pass.run(mir);
        }
    }
}

trait OptPass {
    fn name(&self) -> &'static str;
    fn run(&self, mir: &mut Mir);
}
```

## Security-Preserving Optimizations

```rust
// Constant-time preservation
struct ConstantTimePreservation;

impl OptPass for ConstantTimePreservation {
    fn name(&self) -> &'static str { "constant-time-preservation" }
    
    fn run(&self, mir: &mut Mir) {
        for func in mir.functions.values_mut() {
            if func.security.constant_time {
                // Verify no timing-dependent optimizations
                self.verify_constant_time(func);
            }
        }
    }
}

impl ConstantTimePreservation {
    fn verify_constant_time(&self, func: &MirFunction) {
        for block in &func.basic_blocks {
            // Check no secret-dependent branches
            if let Terminator::SwitchInt { discr, .. } = &block.terminator {
                if self.is_secret(discr, func) {
                    panic!("Secret-dependent branch in constant-time function");
                }
            }
            
            // Check no secret-dependent memory access patterns
            for stmt in &block.statements {
                if let Statement::Assign(place, rvalue) = stmt {
                    if self.is_secret_indexed(place, func) {
                        panic!("Secret-dependent memory access in constant-time function");
                    }
                }
            }
        }
    }
    
    fn is_secret(&self, operand: &Operand, func: &MirFunction) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                func.locals[place.local.0 as usize].security_label
                    .as_ref()
                    .map(|l| l.is_secret())
                    .unwrap_or(false)
            }
            Operand::Constant(_) => false,
        }
    }
}

// Security check preservation
struct SecurityCheckPreservation;

impl OptPass for SecurityCheckPreservation {
    fn name(&self) -> &'static str { "security-check-preservation" }
    
    fn run(&self, mir: &mut Mir) {
        for func in mir.functions.values() {
            // Verify capability checks not removed
            for cap in &func.security.required_capabilities {
                if !self.has_capability_check(func, cap) {
                    panic!("Capability check removed by optimization");
                }
            }
            
            // Verify audit calls not removed
            if func.security.audit_required {
                if !self.has_audit_call(func) {
                    panic!("Audit call removed by optimization");
                }
            }
        }
    }
}
```

## TERAS Decision Q-08

**IMPLEMENT** optimizations:
1. Standard optimizations
2. Security preservation
3. Constant-time verification
4. Audit preservation

### Architecture Decision ID: `TERAS-ARCH-Q08-OPT-001`

---

# Q-09: Code Generation

## Code Generator

```rust
// Code generator
struct CodeGenerator<'a> {
    session: &'a Session,
    mir: &'a Mir,
    target: &'a Target,
    output: ObjectFile,
}

impl<'a> CodeGenerator<'a> {
    fn generate(&mut self) -> ObjectFile {
        for (def_id, func) in &self.mir.functions {
            let machine_func = self.generate_function(func);
            self.output.add_function(*def_id, machine_func);
        }
        
        std::mem::take(&mut self.output)
    }
    
    fn generate_function(&mut self, func: &MirFunction) -> MachineFunction {
        let mut mfunc = MachineFunction::new();
        
        // Allocate stack frame
        let frame = self.allocate_frame(func);
        
        // Register allocation
        let reg_alloc = self.allocate_registers(func);
        
        // Generate prologue
        self.emit_prologue(&mut mfunc, &frame);
        
        // Generate basic blocks
        for (i, block) in func.basic_blocks.iter().enumerate() {
            mfunc.add_label(format!(".LBB{}_{}", func.def_id.0, i));
            
            for stmt in &block.statements {
                self.generate_statement(&mut mfunc, stmt, &frame, &reg_alloc);
            }
            
            self.generate_terminator(&mut mfunc, &block.terminator, &frame, &reg_alloc);
        }
        
        // Generate epilogue
        self.emit_epilogue(&mut mfunc, &frame);
        
        mfunc
    }
    
    fn generate_statement(
        &mut self,
        mfunc: &mut MachineFunction,
        stmt: &Statement,
        frame: &StackFrame,
        reg_alloc: &RegAlloc,
    ) {
        match stmt {
            Statement::Assign(place, rvalue) => {
                let dest = self.place_to_location(place, frame, reg_alloc);
                self.generate_rvalue(mfunc, rvalue, dest, frame, reg_alloc);
            }
            
            Statement::CapabilityCheck(cap) => {
                // Generate runtime capability check
                self.emit_capability_check(mfunc, cap);
            }
            
            Statement::Audit(audit) => {
                // Generate audit call
                self.emit_audit_call(mfunc, audit);
            }
            
            _ => {}
        }
    }
    
    fn emit_capability_check(&mut self, mfunc: &mut MachineFunction, cap: &Capability) {
        // Load capability from context
        // Compare against required
        // Branch to error handler if missing
        
        // x86_64 example:
        // mov rax, [rdi + SECURITY_CONTEXT_OFFSET]
        // mov rbx, [rax + CAPABILITIES_OFFSET]
        // test rbx, CAPABILITY_MASK
        // jz .capability_error
    }
}
```

## Target-Specific Backends

```rust
// x86_64 backend
struct X86_64Backend;

impl Backend for X86_64Backend {
    fn emit_prologue(&self, mfunc: &mut MachineFunction, frame: &StackFrame) {
        mfunc.emit(Instruction::Push(Reg::RBP));
        mfunc.emit(Instruction::Mov(Reg::RBP, Reg::RSP));
        
        if frame.size > 0 {
            mfunc.emit(Instruction::Sub(Reg::RSP, Immediate::I32(frame.size as i32)));
        }
        
        // Save callee-saved registers
        for reg in frame.callee_saved.iter() {
            mfunc.emit(Instruction::Push(*reg));
        }
    }
    
    fn emit_epilogue(&self, mfunc: &mut MachineFunction, frame: &StackFrame) {
        // Restore callee-saved registers
        for reg in frame.callee_saved.iter().rev() {
            mfunc.emit(Instruction::Pop(*reg));
        }
        
        mfunc.emit(Instruction::Mov(Reg::RSP, Reg::RBP));
        mfunc.emit(Instruction::Pop(Reg::RBP));
        mfunc.emit(Instruction::Ret);
    }
    
    fn emit_call(&self, mfunc: &mut MachineFunction, target: &str, args: &[Location]) {
        // System V AMD64 ABI: RDI, RSI, RDX, RCX, R8, R9, then stack
        let arg_regs = [Reg::RDI, Reg::RSI, Reg::RDX, Reg::RCX, Reg::R8, Reg::R9];
        
        for (i, arg) in args.iter().enumerate() {
            if i < arg_regs.len() {
                mfunc.emit(Instruction::Mov(arg_regs[i], arg.clone()));
            } else {
                mfunc.emit(Instruction::Push(arg.clone()));
            }
        }
        
        mfunc.emit(Instruction::Call(target.to_string()));
    }
}

// AArch64 backend
struct AArch64Backend;

impl Backend for AArch64Backend {
    fn emit_prologue(&self, mfunc: &mut MachineFunction, frame: &StackFrame) {
        // Save frame pointer and link register
        mfunc.emit(Instruction::Stp(Reg::X29, Reg::X30, StackOp::PreDecrement(16)));
        mfunc.emit(Instruction::Mov(Reg::X29, Reg::SP));
        
        if frame.size > 0 {
            mfunc.emit(Instruction::Sub(Reg::SP, Reg::SP, Immediate::I32(frame.size as i32)));
        }
    }
    
    fn emit_epilogue(&self, mfunc: &mut MachineFunction, frame: &StackFrame) {
        mfunc.emit(Instruction::Mov(Reg::SP, Reg::X29));
        mfunc.emit(Instruction::Ldp(Reg::X29, Reg::X30, StackOp::PostIncrement(16)));
        mfunc.emit(Instruction::Ret);
    }
}
```

## TERAS Decision Q-09

**IMPLEMENT** code generation:
1. Multi-target support
2. Security check emission
3. Audit call generation
4. ABI compliance

### Architecture Decision ID: `TERAS-ARCH-Q09-CODEGEN-001`

---

# Q-10: Compiler Integration

## Driver

```rust
// Compiler driver
fn main() {
    let args = parse_args();
    
    let session = Session::new(&args);
    let mut compiler = Compiler::new(session);
    
    // Set up diagnostics
    let diagnostics = DiagnosticsEngine::new();
    
    // Compile
    let result = match args.command {
        Command::Build => compiler.build(&args.input),
        Command::Check => compiler.check(&args.input),
        Command::Run => {
            let output = compiler.build(&args.input)?;
            run_binary(&output)
        }
        Command::Test => {
            let output = compiler.build_tests(&args.input)?;
            run_tests(&output)
        }
    };
    
    // Report diagnostics
    diagnostics.emit_all();
    
    // Exit with appropriate code
    std::process::exit(match result {
        Ok(_) => 0,
        Err(_) => 1,
    });
}

// Incremental compilation
struct IncrementalCompiler {
    cache: CompilationCache,
    file_hashes: HashMap<PathBuf, Hash>,
}

impl IncrementalCompiler {
    fn compile(&mut self, input: &Path) -> Result<CompileOutput, CompileError> {
        let current_hash = hash_file(input);
        
        if let Some(cached_hash) = self.file_hashes.get(input) {
            if *cached_hash == current_hash {
                // Check if dependencies changed
                if !self.dependencies_changed(input) {
                    return Ok(self.cache.get(input).unwrap().clone());
                }
            }
        }
        
        // Recompile
        let output = self.full_compile(input)?;
        
        // Update cache
        self.cache.insert(input.to_path_buf(), output.clone());
        self.file_hashes.insert(input.to_path_buf(), current_hash);
        
        Ok(output)
    }
}
```

## LSP Integration

```rust
// Language server integration
impl TerasLanguageServer {
    fn on_change(&mut self, uri: &Url, text: String) {
        // Parse
        let tokens = Lexer::new(&text).lex();
        let ast = Parser::new(&tokens).parse();
        
        // Type check
        let typed = match self.type_check(&ast) {
            Ok(typed) => typed,
            Err(errors) => {
                self.publish_diagnostics(uri, errors);
                return;
            }
        };
        
        // Security check
        let security_errors = self.security_check(&typed);
        
        // Publish diagnostics
        self.publish_diagnostics(uri, security_errors);
        
        // Update index
        self.index.update(uri, &typed);
    }
    
    fn completion(&self, uri: &Url, position: Position) -> Vec<CompletionItem> {
        let context = self.index.context_at(uri, position);
        
        let mut completions = vec![];
        
        // Add local variables
        for var in context.local_variables() {
            completions.push(CompletionItem {
                label: var.name.to_string(),
                kind: Some(CompletionItemKind::Variable),
                detail: Some(var.ty.to_string()),
                ..Default::default()
            });
        }
        
        // Add capabilities if in security context
        if context.in_security_annotation() {
            for cap in Capability::all() {
                completions.push(CompletionItem {
                    label: cap.name().to_string(),
                    kind: Some(CompletionItemKind::EnumMember),
                    detail: Some("Capability".to_string()),
                    ..Default::default()
                });
            }
        }
        
        completions
    }
}
```

## TERAS Decision Q-10

**IMPLEMENT** integration:
1. Command-line driver
2. Incremental compilation
3. LSP server
4. Build system integration

### Architecture Decision ID: `TERAS-ARCH-Q10-INT-001`

---

# Domain Q Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| Q-01 | Architecture | TERAS-ARCH-Q01-COMP-001 |
| Q-02 | Lexing | TERAS-ARCH-Q02-LEX-001 |
| Q-03 | Parsing | TERAS-ARCH-Q03-PARSE-001 |
| Q-04 | Resolution | TERAS-ARCH-Q04-RES-001 |
| Q-05 | Type Checking | TERAS-ARCH-Q05-TYPE-001 |
| Q-06 | Security | TERAS-ARCH-Q06-SEC-001 |
| Q-07 | MIR | TERAS-ARCH-Q07-MIR-001 |
| Q-08 | Optimization | TERAS-ARCH-Q08-OPT-001 |
| Q-09 | Code Gen | TERAS-ARCH-Q09-CODEGEN-001 |
| Q-10 | Integration | TERAS-ARCH-Q10-INT-001 |

## Domain Q: COMPLETE

---

*Research Track Output â€” Domain Q: Compiler Architecture and Implementation*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
