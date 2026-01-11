# TERAS-LANG Research Domain N: Tooling and IDE Support

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-N-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | N-01 through N-10 |
| Domain | N: Tooling and IDE Support |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# N-01: Developer Tooling Foundations

## Executive Summary

Developer tooling directly impacts productivity, code quality, and security. TERAS-LANG requires comprehensive tooling that surfaces security information, aids verification, and prevents common mistakes through IDE integration.

## Tooling Categories

```
1. Compilation Tools
   - Compiler (terasc)
   - Build system (teras-build)
   - Package manager (teras-pkg)

2. Development Tools
   - Language Server (teras-lsp)
   - Formatter (teras-fmt)
   - Linter (teras-lint)

3. Analysis Tools
   - Type checker
   - Security analyzer
   - Complexity analyzer

4. Documentation
   - Doc generator (teras-doc)
   - Example runner

5. Debugging
   - Debugger integration
   - Profiler
   - Tracing
```

## Security Tooling Requirements

```
Security-Specific Tools:

1. Security Linter
   - Detect unsafe patterns
   - Check capability usage
   - Verify IFC compliance

2. Dependency Auditor
   - Vulnerability database
   - License compliance
   - Supply chain verification

3. Secret Scanner
   - Detect hardcoded secrets
   - Check entropy

4. Audit Log Analyzer
   - Verify audit completeness
   - Check audit integrity
```

## TERAS Decision N-01

**IMPLEMENT** tooling:
1. Comprehensive tool suite
2. Security-focused tools
3. IDE integration
4. CI/CD support

### Architecture Decision ID: `TERAS-ARCH-N01-TOOL-001`

---

# N-02: Language Server Protocol

## LSP Overview

```
Language Server Protocol:

Client (IDE) <--JSON-RPC--> Server (teras-lsp)

Messages:
- textDocument/didOpen
- textDocument/didChange
- textDocument/completion
- textDocument/hover
- textDocument/definition
- textDocument/references
- textDocument/diagnostics
```

## Core LSP Features

```rust
// Language Server implementation
struct TerasLanguageServer {
    workspace: Workspace,
    analyzer: Analyzer,
    index: Index,
}

impl LanguageServer for TerasLanguageServer {
    async fn initialize(&self, params: InitializeParams) -> InitializeResult {
        InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::INCREMENTAL),
                        save: Some(SaveOptions { include_text: Some(true) }),
                        ..Default::default()
                    }
                )),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string(), ":".to_string()]),
                    ..Default::default()
                }),
                hover_provider: Some(true),
                definition_provider: Some(true),
                references_provider: Some(true),
                document_formatting_provider: Some(true),
                code_action_provider: Some(true),
                ..Default::default()
            },
            ..Default::default()
        }
    }
    
    async fn completion(&self, params: CompletionParams) -> Option<CompletionResponse> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        
        let completions = self.analyzer.complete(&uri, position);
        Some(CompletionResponse::List(CompletionList {
            is_incomplete: false,
            items: completions,
        }))
    }
    
    async fn hover(&self, params: HoverParams) -> Option<Hover> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        
        let info = self.analyzer.hover(&uri, position)?;
        Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: info,
            }),
            range: None,
        })
    }
}
```

## Security-Aware LSP Features

```rust
// Security diagnostics
impl TerasLanguageServer {
    fn compute_diagnostics(&self, uri: &Url) -> Vec<Diagnostic> {
        let mut diagnostics = vec![];
        
        // Type errors
        diagnostics.extend(self.type_check_diagnostics(uri));
        
        // Security warnings
        diagnostics.extend(self.security_diagnostics(uri));
        
        // Capability issues
        diagnostics.extend(self.capability_diagnostics(uri));
        
        // IFC violations
        diagnostics.extend(self.ifc_diagnostics(uri));
        
        diagnostics
    }
    
    fn security_diagnostics(&self, uri: &Url) -> Vec<Diagnostic> {
        let mut diagnostics = vec![];
        let ast = self.analyzer.parse(uri);
        
        // Check for hardcoded secrets
        for string_lit in ast.string_literals() {
            if looks_like_secret(&string_lit.value) {
                diagnostics.push(Diagnostic {
                    range: string_lit.range,
                    severity: Some(DiagnosticSeverity::WARNING),
                    code: Some(NumberOrString::String("SEC001".to_string())),
                    message: "Possible hardcoded secret detected".to_string(),
                    tags: Some(vec![DiagnosticTag::UNNECESSARY]),
                    ..Default::default()
                });
            }
        }
        
        // Check for unsafe patterns
        for call in ast.function_calls() {
            if is_unsafe_pattern(&call) {
                diagnostics.push(Diagnostic {
                    range: call.range,
                    severity: Some(DiagnosticSeverity::WARNING),
                    code: Some(NumberOrString::String("SEC002".to_string())),
                    message: "Potentially unsafe operation".to_string(),
                    ..Default::default()
                });
            }
        }
        
        diagnostics
    }
}

// Security-aware hover info
fn security_hover_info(symbol: &Symbol) -> String {
    let mut info = format!("```teras\n{}\n```\n", symbol.signature);
    
    if let Some(caps) = symbol.required_capabilities() {
        info.push_str(&format!("\n**Required Capabilities:** {}\n", 
            caps.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", ")));
    }
    
    if let Some(clearance) = symbol.required_clearance() {
        info.push_str(&format!("\n**Required Clearance:** {}\n", clearance));
    }
    
    if let Some(effects) = symbol.effects() {
        info.push_str(&format!("\n**Effects:** {}\n", effects));
    }
    
    info
}
```

## TERAS Decision N-02

**IMPLEMENT** LSP:
1. Full LSP compliance
2. Security diagnostics
3. Capability information
4. Effect tracking

### Architecture Decision ID: `TERAS-ARCH-N02-LSP-001`

---

# N-03: Code Formatting

## Formatter Design

```rust
// Formatter configuration
#[derive(Deserialize)]
struct FormatConfig {
    indent_style: IndentStyle,      // Spaces or Tabs
    indent_width: usize,            // 2 or 4
    max_line_width: usize,          // 80 or 100
    trailing_comma: TrailingComma,  // Always, Never, Consistent
    brace_style: BraceStyle,        // SameLine, NextLine
    blank_lines_upper_bound: usize, // Max consecutive blank lines
}

// Formatter
struct TerasFormatter {
    config: FormatConfig,
}

impl TerasFormatter {
    fn format(&self, source: &str) -> Result<String, FormatError> {
        let ast = parse(source)?;
        let formatted = self.format_ast(&ast);
        Ok(formatted)
    }
    
    fn format_function(&self, func: &Function) -> String {
        let mut out = String::new();
        
        // Attributes
        for attr in &func.attributes {
            out.push_str(&self.format_attribute(attr));
            out.push('\n');
        }
        
        // Signature
        out.push_str(&func.visibility.to_string());
        out.push_str(" fn ");
        out.push_str(&func.name);
        
        // Generics
        if !func.generics.is_empty() {
            out.push('<');
            out.push_str(&func.generics.iter()
                .map(|g| self.format_generic(g))
                .collect::<Vec<_>>()
                .join(", "));
            out.push('>');
        }
        
        // Parameters
        out.push('(');
        if func.params.len() <= 3 {
            // Single line
            out.push_str(&func.params.iter()
                .map(|p| self.format_param(p))
                .collect::<Vec<_>>()
                .join(", "));
        } else {
            // Multi-line
            out.push('\n');
            for param in &func.params {
                out.push_str(&self.indent(1));
                out.push_str(&self.format_param(param));
                out.push_str(",\n");
            }
        }
        out.push(')');
        
        // Return type and effects
        if let Some(ret) = &func.return_type {
            out.push_str(" -> ");
            out.push_str(&self.format_type(ret));
        }
        
        if !func.effects.is_empty() {
            out.push_str(" ! ");
            out.push_str(&func.effects.iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join(" + "));
        }
        
        // Body
        out.push_str(" {\n");
        out.push_str(&self.format_block(&func.body, 1));
        out.push_str("}\n");
        
        out
    }
}
```

## Security Formatting Rules

```rust
// Security-specific formatting
impl TerasFormatter {
    fn format_with_security(&self, source: &str) -> Result<String, FormatError> {
        let mut formatted = self.format(source)?;
        
        // Add security annotations visibility
        formatted = self.ensure_security_annotations_visible(&formatted);
        
        // Align capability requirements
        formatted = self.align_capabilities(&formatted);
        
        Ok(formatted)
    }
    
    fn ensure_security_annotations_visible(&self, source: &str) -> String {
        // Ensure security attributes are on their own lines
        // #[requires_capability(X)] fn foo() -> ...
        // becomes:
        // #[requires_capability(X)]
        // fn foo() -> ...
        
        let re = Regex::new(r"(#\[requires_\w+\([^)]+\)\])\s*(fn|pub|async)").unwrap();
        re.replace_all(source, "$1\n$2").to_string()
    }
    
    fn align_capabilities(&self, source: &str) -> String {
        // Align capability declarations for readability
        source.to_string()
    }
}

// Format check in CI
fn check_format(path: &Path) -> Result<(), FormatError> {
    let source = std::fs::read_to_string(path)?;
    let formatted = TerasFormatter::default().format(&source)?;
    
    if source != formatted {
        Err(FormatError::NotFormatted {
            path: path.to_path_buf(),
            diff: compute_diff(&source, &formatted),
        })
    } else {
        Ok(())
    }
}
```

## TERAS Decision N-03

**IMPLEMENT** formatter:
1. Configurable formatting
2. Security annotation handling
3. CI integration
4. IDE auto-format

### Architecture Decision ID: `TERAS-ARCH-N03-FMT-001`

---

# N-04: Linting and Static Analysis

## Linter Architecture

```rust
// Lint rule definition
trait LintRule {
    fn name(&self) -> &'static str;
    fn description(&self) -> &'static str;
    fn category(&self) -> LintCategory;
    fn default_severity(&self) -> Severity;
    
    fn check(&self, ctx: &LintContext) -> Vec<LintDiagnostic>;
}

enum LintCategory {
    Correctness,
    Security,
    Performance,
    Style,
    Complexity,
}

// Example lint rules
struct UnusedVariable;
impl LintRule for UnusedVariable {
    fn name(&self) -> &'static str { "unused_variable" }
    fn category(&self) -> LintCategory { LintCategory::Correctness }
    
    fn check(&self, ctx: &LintContext) -> Vec<LintDiagnostic> {
        let mut diagnostics = vec![];
        
        for variable in ctx.declared_variables() {
            if !ctx.is_used(&variable) && !variable.name.starts_with('_') {
                diagnostics.push(LintDiagnostic {
                    rule: self.name(),
                    severity: self.default_severity(),
                    range: variable.range,
                    message: format!("Unused variable: {}", variable.name),
                    suggestions: vec![
                        Suggestion::RenameToUnderscore,
                        Suggestion::Remove,
                    ],
                });
            }
        }
        
        diagnostics
    }
}
```

## Security Lint Rules

```rust
// Hardcoded secrets
struct HardcodedSecret;
impl LintRule for HardcodedSecret {
    fn name(&self) -> &'static str { "hardcoded_secret" }
    fn category(&self) -> LintCategory { LintCategory::Security }
    
    fn check(&self, ctx: &LintContext) -> Vec<LintDiagnostic> {
        let patterns = [
            r"(?i)(password|secret|api_key|token)\s*=\s*['\"][^'\"]+['\"]",
            r"-----BEGIN (RSA |EC |)PRIVATE KEY-----",
            r"[a-zA-Z0-9]{40}",  // API tokens
        ];
        
        let mut diagnostics = vec![];
        for string in ctx.string_literals() {
            if patterns.iter().any(|p| Regex::new(p).unwrap().is_match(&string.value)) {
                diagnostics.push(LintDiagnostic {
                    rule: self.name(),
                    severity: Severity::Error,
                    range: string.range,
                    message: "Possible hardcoded secret detected".to_string(),
                    suggestions: vec![Suggestion::UseEnvironmentVariable],
                });
            }
        }
        diagnostics
    }
}

// Unsafe block audit
struct UnsafeAudit;
impl LintRule for UnsafeAudit {
    fn name(&self) -> &'static str { "unsafe_audit" }
    fn category(&self) -> LintCategory { LintCategory::Security }
    
    fn check(&self, ctx: &LintContext) -> Vec<LintDiagnostic> {
        let mut diagnostics = vec![];
        
        for unsafe_block in ctx.unsafe_blocks() {
            if !unsafe_block.has_safety_comment() {
                diagnostics.push(LintDiagnostic {
                    rule: self.name(),
                    severity: Severity::Warning,
                    range: unsafe_block.range,
                    message: "Unsafe block missing safety documentation".to_string(),
                    suggestions: vec![Suggestion::AddSafetyComment],
                });
            }
        }
        
        diagnostics
    }
}

// Missing capability check
struct MissingCapabilityCheck;
impl LintRule for MissingCapabilityCheck {
    fn name(&self) -> &'static str { "missing_capability_check" }
    fn category(&self) -> LintCategory { LintCategory::Security }
    
    fn check(&self, ctx: &LintContext) -> Vec<LintDiagnostic> {
        let mut diagnostics = vec![];
        
        for call in ctx.capability_requiring_calls() {
            if !ctx.has_capability_check_before(&call) {
                diagnostics.push(LintDiagnostic {
                    rule: self.name(),
                    severity: Severity::Error,
                    range: call.range,
                    message: format!(
                        "Call to {} requires capability {} but no check found",
                        call.name,
                        call.required_capability
                    ),
                    suggestions: vec![Suggestion::AddCapabilityAttribute],
                });
            }
        }
        
        diagnostics
    }
}

// SQL injection potential
struct SqlInjection;
impl LintRule for SqlInjection {
    fn name(&self) -> &'static str { "sql_injection" }
    fn category(&self) -> LintCategory { LintCategory::Security }
    
    fn check(&self, ctx: &LintContext) -> Vec<LintDiagnostic> {
        let mut diagnostics = vec![];
        
        for call in ctx.calls_to(&["query", "execute", "raw_sql"]) {
            if let Some(arg) = call.arguments.first() {
                if arg.contains_string_interpolation() || arg.is_format_string() {
                    diagnostics.push(LintDiagnostic {
                        rule: self.name(),
                        severity: Severity::Error,
                        range: call.range,
                        message: "Potential SQL injection: use parameterized queries".to_string(),
                        suggestions: vec![Suggestion::UseParameterizedQuery],
                    });
                }
            }
        }
        
        diagnostics
    }
}
```

## TERAS Decision N-04

**IMPLEMENT** linting:
1. Extensible lint framework
2. Security-focused rules
3. Auto-fix suggestions
4. Configurable severity

### Architecture Decision ID: `TERAS-ARCH-N04-LINT-001`

---

# N-05: Documentation Generation

## Doc Comments

```rust
/// A cryptographic key for AES-256-GCM encryption.
///
/// # Security
///
/// This key type implements secure memory handling:
/// - Memory is locked to prevent swapping
/// - Key material is zeroized on drop
/// - Constant-time comparison is used
///
/// # Required Capabilities
///
/// Creating keys requires `CryptoKeyGen` capability.
///
/// # Examples
///
/// ```
/// let key = AesKey::generate()?;
/// let ciphertext = key.encrypt(&nonce, plaintext)?;
/// ```
///
/// # Errors
///
/// Returns `CryptoError::KeyGeneration` if the RNG fails.
pub struct AesKey {
    material: SecureBox<[u8; 32]>,
}

impl AesKey {
    /// Generates a new random AES-256 key.
    ///
    /// # Security Considerations
    ///
    /// Uses the system CSPRNG for key generation.
    /// The generated key is stored in secure memory.
    ///
    /// # Panics
    ///
    /// Panics if memory locking fails (requires appropriate privileges).
    #[requires_capability(CryptoKeyGen)]
    pub fn generate() -> Result<Self, CryptoError> {
        // ...
    }
}
```

## Doc Generator

```rust
// Documentation generator
struct TerasDoc {
    config: DocConfig,
}

impl TerasDoc {
    fn generate(&self, crate_path: &Path) -> Result<Documentation, DocError> {
        let krate = parse_crate(crate_path)?;
        
        let mut docs = Documentation::new(&krate.name);
        
        // Generate module docs
        for module in &krate.modules {
            docs.add_module(self.generate_module(module)?);
        }
        
        // Generate index
        docs.generate_index();
        
        // Generate search data
        docs.generate_search_index();
        
        Ok(docs)
    }
    
    fn generate_module(&self, module: &Module) -> Result<ModuleDoc, DocError> {
        let mut doc = ModuleDoc::new(&module.name);
        
        // Add module-level docs
        doc.set_description(&module.doc_comment);
        
        // Document items
        for item in &module.items {
            match item {
                Item::Struct(s) => doc.add_struct(self.document_struct(s)?),
                Item::Enum(e) => doc.add_enum(self.document_enum(e)?),
                Item::Function(f) => doc.add_function(self.document_function(f)?),
                Item::Trait(t) => doc.add_trait(self.document_trait(t)?),
                _ => {}
            }
        }
        
        Ok(doc)
    }
    
    fn document_function(&self, func: &Function) -> Result<FunctionDoc, DocError> {
        let mut doc = FunctionDoc::new(&func.name);
        
        // Basic info
        doc.set_signature(&func.signature());
        doc.set_description(&func.doc_comment);
        
        // Security info
        if let Some(caps) = func.required_capabilities() {
            doc.add_section("Required Capabilities", &format_capabilities(caps));
        }
        
        if let Some(clearance) = func.required_clearance() {
            doc.add_section("Required Clearance", &clearance.to_string());
        }
        
        if !func.effects.is_empty() {
            doc.add_section("Effects", &format_effects(&func.effects));
        }
        
        // Examples
        for example in &func.doc_examples() {
            doc.add_example(example);
        }
        
        Ok(doc)
    }
}
```

## Security Documentation

```rust
// Generate security documentation
impl TerasDoc {
    fn generate_security_docs(&self, krate: &Crate) -> SecurityDocs {
        let mut docs = SecurityDocs::new();
        
        // Capability map
        docs.capability_map = self.generate_capability_map(krate);
        
        // Security boundaries
        docs.boundaries = self.generate_boundary_docs(krate);
        
        // Threat model
        docs.threat_model = self.generate_threat_model(krate);
        
        // Audit points
        docs.audit_points = self.generate_audit_docs(krate);
        
        docs
    }
    
    fn generate_capability_map(&self, krate: &Crate) -> CapabilityMap {
        let mut map = CapabilityMap::new();
        
        for func in krate.all_functions() {
            if let Some(caps) = func.required_capabilities() {
                for cap in caps {
                    map.add_function(&cap, &func.path());
                }
            }
        }
        
        map
    }
}
```

## TERAS Decision N-05

**IMPLEMENT** documentation:
1. Doc comments standard
2. Security sections
3. Capability documentation
4. Searchable output

### Architecture Decision ID: `TERAS-ARCH-N05-DOC-001`

---

# N-06: Build System

## Build Configuration

```toml
# teras.toml
[package]
name = "teras-crypto"
version = "1.0.0"
edition = "2026"

[dependencies]
teras-core = "1.0"

[build]
target = "aarch64-unknown-linux-gnu"
opt-level = 3
lto = true
codegen-units = 1

[security]
stack-protector = "strong"
relro = "full"
fortify-source = 2
cfi = true

[profile.release]
debug = false
strip = true

[profile.dev]
debug = true
opt-level = 0
```

## Build Process

```rust
// Build system
struct TerasBuild {
    config: BuildConfig,
    resolver: DependencyResolver,
    compiler: Compiler,
}

impl TerasBuild {
    fn build(&self, target: &Target) -> Result<BuildOutput, BuildError> {
        // 1. Resolve dependencies
        let deps = self.resolver.resolve(&self.config)?;
        
        // 2. Build dependency graph
        let graph = BuildGraph::from_dependencies(&deps);
        
        // 3. Compile in topological order
        let mut outputs = vec![];
        for node in graph.topological_order() {
            let output = self.compile_node(&node)?;
            outputs.push(output);
        }
        
        // 4. Link
        let binary = self.link(&outputs, target)?;
        
        // 5. Apply security hardening
        self.apply_security_hardening(&binary)?;
        
        Ok(BuildOutput { binary, deps })
    }
    
    fn apply_security_hardening(&self, binary: &mut Binary) -> Result<(), BuildError> {
        // Stack canaries
        if self.config.security.stack_protector.is_some() {
            binary.enable_stack_protector();
        }
        
        // RELRO
        if self.config.security.relro == "full" {
            binary.enable_full_relro();
        }
        
        // CFI
        if self.config.security.cfi {
            binary.enable_cfi();
        }
        
        // PIE
        binary.enable_pie();
        
        Ok(())
    }
}
```

## Incremental Compilation

```rust
// Incremental build
struct IncrementalBuilder {
    cache: BuildCache,
}

impl IncrementalBuilder {
    fn build(&mut self, changed_files: &[PathBuf]) -> Result<BuildOutput, BuildError> {
        // Identify affected modules
        let affected = self.compute_affected_modules(changed_files);
        
        // Recompile only affected
        for module in &affected {
            let hash = self.compute_hash(module);
            
            if self.cache.is_stale(module, hash) {
                let output = self.compile_module(module)?;
                self.cache.store(module, hash, &output);
            }
        }
        
        // Incremental linking
        self.incremental_link(&affected)
    }
    
    fn compute_affected_modules(&self, changed: &[PathBuf]) -> Vec<Module> {
        let mut affected = HashSet::new();
        
        // Direct changes
        for path in changed {
            if let Some(module) = self.path_to_module(path) {
                affected.insert(module.clone());
            }
        }
        
        // Transitive dependents
        let mut worklist: Vec<_> = affected.iter().cloned().collect();
        while let Some(module) = worklist.pop() {
            for dependent in self.dependents_of(&module) {
                if affected.insert(dependent.clone()) {
                    worklist.push(dependent);
                }
            }
        }
        
        affected.into_iter().collect()
    }
}
```

## TERAS Decision N-06

**IMPLEMENT** build system:
1. Security hardening
2. Incremental compilation
3. Reproducible builds
4. Cross-compilation

### Architecture Decision ID: `TERAS-ARCH-N06-BUILD-001`

---

# N-07: Package Manager

## Package Registry

```rust
// Package registry
struct TerasRegistry {
    url: Url,
    cache: PackageCache,
}

impl TerasRegistry {
    async fn fetch(&self, name: &str, version: &VersionReq) -> Result<Package, RegistryError> {
        // Check cache
        if let Some(pkg) = self.cache.get(name, version) {
            return Ok(pkg);
        }
        
        // Fetch from registry
        let pkg = self.download(name, version).await?;
        
        // Verify signature
        self.verify_signature(&pkg)?;
        
        // Verify checksum
        self.verify_checksum(&pkg)?;
        
        // Security audit
        self.check_vulnerabilities(&pkg)?;
        
        // Cache
        self.cache.store(&pkg);
        
        Ok(pkg)
    }
    
    fn verify_signature(&self, pkg: &Package) -> Result<(), RegistryError> {
        let sig = &pkg.signature;
        let data = &pkg.tarball;
        
        // Verify against known publisher keys
        let publisher_key = self.get_publisher_key(&pkg.publisher)?;
        if !verify_signature(&publisher_key, data, sig) {
            return Err(RegistryError::InvalidSignature);
        }
        
        Ok(())
    }
    
    fn check_vulnerabilities(&self, pkg: &Package) -> Result<(), RegistryError> {
        let vulns = self.vuln_db.check(&pkg.name, &pkg.version);
        
        if !vulns.is_empty() {
            let critical = vulns.iter().any(|v| v.severity == Severity::Critical);
            if critical {
                return Err(RegistryError::CriticalVulnerability(vulns));
            }
            
            // Warn about non-critical
            for vuln in &vulns {
                eprintln!("Warning: {} has known vulnerability: {}", pkg.name, vuln.id);
            }
        }
        
        Ok(())
    }
}
```

## Dependency Resolution

```rust
// SAT-based dependency resolution
struct DependencyResolver {
    registry: TerasRegistry,
}

impl DependencyResolver {
    fn resolve(&self, manifest: &Manifest) -> Result<LockFile, ResolveError> {
        let mut solver = SatSolver::new();
        
        // Add direct dependencies
        for (name, req) in &manifest.dependencies {
            let versions = self.registry.available_versions(name)?;
            self.add_version_constraints(&mut solver, name, req, &versions);
        }
        
        // Solve
        let solution = solver.solve()?;
        
        // Verify security constraints
        self.verify_security_constraints(&solution)?;
        
        // Generate lock file
        Ok(self.generate_lockfile(&solution))
    }
    
    fn verify_security_constraints(&self, solution: &Solution) -> Result<(), ResolveError> {
        for pkg in solution.packages() {
            // Check minimum version requirements
            if let Some(min_version) = self.security_min_version(&pkg.name) {
                if pkg.version < min_version {
                    return Err(ResolveError::SecurityVersionRequired {
                        package: pkg.name.clone(),
                        required: min_version,
                        found: pkg.version.clone(),
                    });
                }
            }
            
            // Check for banned packages
            if self.is_banned(&pkg.name) {
                return Err(ResolveError::BannedPackage(pkg.name.clone()));
            }
        }
        
        Ok(())
    }
}
```

## Supply Chain Security

```rust
// Supply chain verification
struct SupplyChainVerifier {
    trusted_publishers: HashSet<PublisherId>,
    signature_keys: HashMap<PublisherId, PublicKey>,
}

impl SupplyChainVerifier {
    fn verify(&self, pkg: &Package) -> Result<(), SupplyChainError> {
        // Verify publisher is trusted
        if !self.trusted_publishers.contains(&pkg.publisher) {
            return Err(SupplyChainError::UntrustedPublisher(pkg.publisher.clone()));
        }
        
        // Verify signature chain
        self.verify_signature_chain(pkg)?;
        
        // Verify reproducible build
        if pkg.metadata.reproducible {
            self.verify_reproducible_build(pkg)?;
        }
        
        // Verify SBOM
        self.verify_sbom(pkg)?;
        
        Ok(())
    }
    
    fn verify_sbom(&self, pkg: &Package) -> Result<(), SupplyChainError> {
        let sbom = &pkg.sbom;
        
        // Verify all dependencies are listed
        for dep in &pkg.dependencies {
            if !sbom.contains(&dep.name) {
                return Err(SupplyChainError::IncompleteSbom);
            }
        }
        
        // Verify no known vulnerable components
        for component in &sbom.components {
            if let Some(vuln) = self.vuln_db.check_component(component) {
                if vuln.severity >= Severity::High {
                    return Err(SupplyChainError::VulnerableComponent {
                        component: component.clone(),
                        vulnerability: vuln,
                    });
                }
            }
        }
        
        Ok(())
    }
}
```

## TERAS Decision N-07

**IMPLEMENT** package manager:
1. Signed packages
2. Vulnerability checking
3. Supply chain verification
4. Reproducible builds

### Architecture Decision ID: `TERAS-ARCH-N07-PKG-001`

---

# N-08: Debugging Support

## Debug Information

```rust
// DWARF debug info generation
struct DebugInfoGenerator {
    builder: DwarfBuilder,
}

impl DebugInfoGenerator {
    fn generate(&mut self, module: &Module) -> DebugInfo {
        // Compile unit
        self.builder.start_compile_unit(&module.name);
        
        // Types
        for ty in &module.types {
            self.emit_type(ty);
        }
        
        // Functions
        for func in &module.functions {
            self.emit_function(func);
        }
        
        // Variables
        for var in &module.variables {
            self.emit_variable(var);
        }
        
        self.builder.finish()
    }
    
    fn emit_function(&mut self, func: &Function) {
        self.builder.start_function(&func.name, func.location());
        
        // Parameters
        for param in &func.params {
            self.builder.add_parameter(&param.name, &param.ty, param.location());
        }
        
        // Local variables
        for local in &func.locals {
            self.builder.add_local(&local.name, &local.ty, local.location());
        }
        
        // Security annotations (custom DWARF extension)
        if let Some(caps) = func.required_capabilities() {
            self.builder.add_custom_attribute("TERAS_capabilities", &caps.to_string());
        }
        
        self.builder.end_function();
    }
}
```

## Debugger Integration

```rust
// GDB/LLDB integration
struct TerasDebugger {
    target: Target,
    breakpoints: Vec<Breakpoint>,
}

impl TerasDebugger {
    // Pretty printing for TERAS types
    fn pretty_print(&self, value: &Value) -> String {
        match value.type_info() {
            TypeInfo::SecureBox => {
                // Don't print contents of secure boxes
                format!("SecureBox<{}> {{ [REDACTED] }}", value.inner_type())
            }
            TypeInfo::Capability => {
                format!("Capability::{}", value.variant_name())
            }
            TypeInfo::Result => {
                if value.is_ok() {
                    format!("Ok({})", self.pretty_print(&value.inner()))
                } else {
                    format!("Err({})", self.pretty_print(&value.error()))
                }
            }
            _ => value.default_format(),
        }
    }
    
    // Security-aware breakpoints
    fn set_security_breakpoint(&mut self, condition: SecurityCondition) {
        match condition {
            SecurityCondition::CapabilityUse(cap) => {
                // Break when capability is used
                for func in self.functions_requiring(&cap) {
                    self.breakpoints.push(Breakpoint::at_function(&func));
                }
            }
            SecurityCondition::ClearanceCheck(level) => {
                // Break on clearance checks
                self.breakpoints.push(Breakpoint::on_clearance_check(level));
            }
            SecurityCondition::AuditEvent => {
                // Break on audit events
                self.breakpoints.push(Breakpoint::at_function("audit::log"));
            }
        }
    }
}
```

## TERAS Decision N-08

**IMPLEMENT** debugging:
1. Full DWARF support
2. Security-aware pretty printing
3. Custom breakpoint types
4. Secure value handling

### Architecture Decision ID: `TERAS-ARCH-N08-DEBUG-001`

---

# N-09: Profiling and Tracing

## Performance Profiling

```rust
// Profiler integration
struct TerasProfiler {
    samples: Vec<Sample>,
    call_graph: CallGraph,
}

impl TerasProfiler {
    fn profile<T, F: FnOnce() -> T>(&mut self, f: F) -> T {
        let _guard = ProfileGuard::start();
        f()
    }
    
    fn report(&self) -> ProfileReport {
        ProfileReport {
            hotspots: self.identify_hotspots(),
            call_graph: self.call_graph.clone(),
            allocations: self.allocation_profile(),
            crypto_operations: self.crypto_profile(),
        }
    }
    
    fn crypto_profile(&self) -> CryptoProfile {
        // Profile cryptographic operations specifically
        CryptoProfile {
            encryption_time: self.time_for_category("encrypt"),
            decryption_time: self.time_for_category("decrypt"),
            hashing_time: self.time_for_category("hash"),
            signing_time: self.time_for_category("sign"),
            verification_time: self.time_for_category("verify"),
        }
    }
}
```

## Tracing

```rust
// Distributed tracing
struct TerasTracer {
    spans: Vec<Span>,
    context: TraceContext,
}

impl TerasTracer {
    fn span(&self, name: &str) -> SpanGuard {
        let span = Span {
            name: name.to_string(),
            trace_id: self.context.trace_id,
            span_id: generate_span_id(),
            parent_id: self.context.current_span_id,
            start: Instant::now(),
            attributes: HashMap::new(),
        };
        
        SpanGuard { tracer: self, span }
    }
}

// Tracing macros
macro_rules! trace_span {
    ($name:expr) => {
        let _span = TRACER.span($name);
    };
    ($name:expr, $($key:ident = $value:expr),*) => {
        let _span = TRACER.span($name)
            $(.attribute(stringify!($key), $value))*;
    };
}

// Security tracing
macro_rules! security_trace {
    ($event:expr) => {
        trace_span!("security_event", 
            event_type = stringify!($event),
            timestamp = now(),
            correlation_id = correlation_id()
        );
    };
}

// Usage
fn authenticate(username: &str, password: &str) -> Result<Session, AuthError> {
    trace_span!("authenticate", username = username);
    security_trace!(AuthenticationAttempt);
    
    // ... authentication logic
}
```

## TERAS Decision N-09

**IMPLEMENT** profiling:
1. CPU profiling
2. Memory profiling
3. Distributed tracing
4. Security event tracing

### Architecture Decision ID: `TERAS-ARCH-N09-PROF-001`

---

# N-10: IDE Integration

## VS Code Extension

```typescript
// VS Code extension
import * as vscode from 'vscode';
import { LanguageClient } from 'vscode-languageclient/node';

export function activate(context: vscode.ExtensionContext) {
    // Start language server
    const serverOptions = {
        command: 'teras-lsp',
        args: ['--stdio'],
    };
    
    const clientOptions = {
        documentSelector: [{ scheme: 'file', language: 'teras' }],
    };
    
    const client = new LanguageClient(
        'terasLanguageServer',
        'TERAS Language Server',
        serverOptions,
        clientOptions
    );
    
    // Security panel
    const securityPanel = new SecurityPanel(context);
    
    // Capability tree view
    const capabilityView = vscode.window.createTreeView('terasCapabilities', {
        treeDataProvider: new CapabilityTreeProvider(client),
    });
    
    // Commands
    context.subscriptions.push(
        vscode.commands.registerCommand('teras.runSecurityCheck', () => {
            runSecurityCheck(client);
        }),
        vscode.commands.registerCommand('teras.showCapabilities', () => {
            showCapabilityGraph(context);
        }),
        vscode.commands.registerCommand('teras.auditCode', () => {
            auditCurrentFile(client);
        }),
    );
    
    client.start();
}

// Security panel
class SecurityPanel {
    private panel: vscode.WebviewPanel | undefined;
    
    show(diagnostics: SecurityDiagnostic[]) {
        if (!this.panel) {
            this.panel = vscode.window.createWebviewPanel(
                'terasSecurity',
                'TERAS Security',
                vscode.ViewColumn.Two,
                { enableScripts: true }
            );
        }
        
        this.panel.webview.html = this.renderDiagnostics(diagnostics);
    }
    
    private renderDiagnostics(diagnostics: SecurityDiagnostic[]): string {
        return `
            <!DOCTYPE html>
            <html>
            <head>
                <style>
                    .critical { color: red; }
                    .warning { color: orange; }
                    .info { color: blue; }
                </style>
            </head>
            <body>
                <h1>Security Analysis</h1>
                <ul>
                    ${diagnostics.map(d => `
                        <li class="${d.severity}">
                            <strong>${d.rule}</strong>: ${d.message}
                            <br>
                            <small>${d.location}</small>
                        </li>
                    `).join('')}
                </ul>
            </body>
            </html>
        `;
    }
}
```

## IntelliJ Plugin

```kotlin
// IntelliJ plugin
class TerasLanguagePlugin : LanguagePlugin {
    override fun createLanguage(): Language = TerasLanguage.INSTANCE
    
    override fun createFileType(): FileType = TerasFileType.INSTANCE
    
    override fun createHighlighter(): SyntaxHighlighter = TerasSyntaxHighlighter()
    
    override fun createAnnotator(): Annotator = TerasSecurityAnnotator()
}

class TerasSecurityAnnotator : Annotator {
    override fun annotate(element: PsiElement, holder: AnnotationHolder) {
        when (element) {
            is TerasFunctionCall -> {
                val capabilities = element.requiredCapabilities()
                if (capabilities.isNotEmpty()) {
                    holder.newAnnotation(
                        HighlightSeverity.INFORMATION,
                        "Requires: ${capabilities.joinToString()}"
                    ).range(element.textRange)
                     .textAttributes(TerasHighlighter.CAPABILITY_HINT)
                     .create()
                }
            }
            is TerasUnsafeBlock -> {
                if (!element.hasSafetyComment()) {
                    holder.newAnnotation(
                        HighlightSeverity.WARNING,
                        "Unsafe block without safety documentation"
                    ).range(element.textRange)
                     .withFix(AddSafetyCommentFix(element))
                     .create()
                }
            }
        }
    }
}
```

## TERAS Decision N-10

**IMPLEMENT** IDE integration:
1. VS Code extension
2. IntelliJ plugin
3. Security panels
4. Capability visualization

### Architecture Decision ID: `TERAS-ARCH-N10-IDE-001`

---

# Domain N Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| N-01 | Foundations | TERAS-ARCH-N01-TOOL-001 |
| N-02 | LSP | TERAS-ARCH-N02-LSP-001 |
| N-03 | Formatting | TERAS-ARCH-N03-FMT-001 |
| N-04 | Linting | TERAS-ARCH-N04-LINT-001 |
| N-05 | Documentation | TERAS-ARCH-N05-DOC-001 |
| N-06 | Build System | TERAS-ARCH-N06-BUILD-001 |
| N-07 | Package Manager | TERAS-ARCH-N07-PKG-001 |
| N-08 | Debugging | TERAS-ARCH-N08-DEBUG-001 |
| N-09 | Profiling | TERAS-ARCH-N09-PROF-001 |
| N-10 | IDE | TERAS-ARCH-N10-IDE-001 |

## Domain N: COMPLETE

---

*Research Track Output â€” Domain N: Tooling and IDE Support*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
