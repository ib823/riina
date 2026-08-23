// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Module resolution — multi-file RIINA programs (master plan REQ-71).
//!
//! Before this, `guna <name>;` parsed and was discarded, so every RIINA program
//! had to be a single file: a two-file program failed with `Variable not found`.
//! This module turns `guna` into a real import.
//!
//! # What a module is
//!
//! A module is one `.rii` file. `guna kira;` in `main.rii` loads `kira.rii` from
//! the SAME directory. Module names are single-segment: a multi-segment path
//! (`guna std::teks;`) names the builtin namespace, has no file behind it, and
//! is ignored by the parser — which is what keeps every pre-REQ-71 example
//! compiling unchanged.
//!
//! # How linking works
//!
//! The surface already resolved `kira::tambah` to the flat name `kira_tambah`
//! at parse time (`parse_module_path`), and `modul kira { fungsi tambah }`
//! already flattened to `kira_tambah`. Linking reuses exactly that convention
//! rather than inventing a second one:
//!
//!   * every top-level name `f` of an imported module `kira` is renamed to
//!     `kira_f`;
//!   * every FREE reference to `f` inside that module is renamed with it, so
//!     the module's internal calls keep working (a local `biar f = …` that
//!     shadows the top-level `f` is correctly left alone);
//!   * the root module is NOT renamed, so `utama` stays `utama`.
//!
//! # What is enforced
//!
//! * **Cycles** — `a` importing `b` importing `a` is a hard error naming the
//!   full chain, not a stack overflow.
//! * **Visibility** — only `awam` names may be referenced across a module
//!   boundary. A private helper is module-local even though every name shares
//!   one flat namespace after linking.
//! * **Direct imports** — a module may only name modules it imports itself.
//!   Transitively-loaded modules are present in the linked program (they must
//!   be, for their importer) but are not silently in scope.
//! * **Collisions** — two modules producing the same final name is an error,
//!   never silent shadowing.
//!
//! # The traversal
//!
//! [`walk_free_idents`] is a single binder-aware walk used for BOTH renaming
//! and reference collection. Its `match` is exhaustive with **no wildcard arm**
//! on purpose: a new `Expr` variant must fail to compile here rather than
//! silently escape renaming and produce a mis-linked program.

use crate::Parser;
use riina_types::{Expr, Ident, Program, SpannedDecl, TopLevelDecl};
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

/// Why module resolution failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolveErrorKind {
    /// `guna x;` named a file that does not exist.
    ModuleNotFound { module: Ident, tried: PathBuf },
    /// The file exists but could not be read.
    Io { path: PathBuf, detail: String },
    /// A module imports itself, directly or through a chain.
    CircularImport { chain: Vec<Ident> },
    /// Two modules produce the same top-level name after linking.
    NameCollision {
        name: Ident,
        first: Ident,
        second: Ident,
    },
    /// A module referenced a name that its owner did not declare `awam`.
    PrivateAccess {
        module: Ident,
        name: Ident,
        from: Ident,
    },
    /// A module referenced `other::name` without `guna other;`.
    MissingImport {
        module: Ident,
        name: Ident,
        from: Ident,
    },
    /// An imported module had top-level code (only the root may have a body).
    TopLevelCodeInModule { module: Ident },
    /// A module file failed to parse. The message carries the inner diagnostic.
    Parse { module: Ident, detail: String },
}

/// A module-resolution failure, with the file it came from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolveError {
    pub kind: ResolveErrorKind,
    /// The file being processed when the error was raised.
    pub path: PathBuf,
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            ResolveErrorKind::ModuleNotFound { module, tried } => write!(
                f,
                "module `{module}` not found (expected `{}`)\n  \
                 note: `guna {module};` imports the sibling file `{module}.rii`; \
                 for builtins use a qualified path such as `guna std::teks;`",
                tried.display()
            ),
            ResolveErrorKind::Io { path, detail } => {
                write!(f, "cannot read `{}`: {detail}", path.display())
            }
            ResolveErrorKind::CircularImport { chain } => write!(
                f,
                "circular import: {}",
                chain
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>()
                    .join(" -> ")
            ),
            ResolveErrorKind::NameCollision {
                name,
                first,
                second,
            } => write!(
                f,
                "name collision: `{name}` is defined by both module `{first}` and \
                 module `{second}`\n  note: rename one of them; linking never \
                 silently shadows a definition"
            ),
            ResolveErrorKind::PrivateAccess { module, name, from } => write!(
                f,
                "`{module}::{name}` is private to module `{module}` (referenced from `{from}`)\n  \
                 note: mark it `awam fungsi {name}` to export it"
            ),
            ResolveErrorKind::MissingImport { module, name, from } => write!(
                f,
                "module `{from}` names `{module}::{name}` without importing it\n  \
                 note: add `guna {module};` to `{from}.rii`"
            ),
            ResolveErrorKind::TopLevelCodeInModule { module } => write!(
                f,
                "imported module `{module}` has top-level code; only the root file \
                 may have a program body\n  note: move it into a function"
            ),
            ResolveErrorKind::Parse { module, detail } => {
                write!(f, "in module `{module}`: {detail}")
            }
        }
    }
}

/// One parsed module before linking.
struct LoadedModule {
    /// Module name — the file stem. The root module keeps its own stem but is
    /// never renamed.
    name: Ident,
    path: PathBuf,
    program: Program,
}

/// Resolve `root` and everything it imports into ONE linked [`Program`].
///
/// The returned program is exactly what the single-file pipeline already
/// consumes, so `check_program` / `desugar` / lowering need no changes.
///
/// # Errors
/// Returns [`ResolveError`] for a missing/unreadable module, an import cycle, a
/// cross-module name collision, a private or un-imported cross-module
/// reference, or a parse failure in an imported file.
pub fn resolve_program(root: &Path, root_source: &str) -> Result<Program, ResolveError> {
    let mut loaded: Vec<LoadedModule> = Vec::new();
    let mut seen: HashSet<PathBuf> = HashSet::new();
    let mut stack: Vec<Ident> = Vec::new();

    let root_name = module_stem(root);
    let root_program = parse_source(root_source, &root_name, root)?;
    // Load dependencies first (post-order), so a module is always linked after
    // everything it needs.
    load_imports(&root_program, root, &mut loaded, &mut seen, &mut stack)?;
    loaded.push(LoadedModule {
        name: root_name.clone(),
        path: root.to_path_buf(),
        program: root_program,
    });

    link(loaded, &root_name)
}

/// Convenience wrapper that reads `root` from disk itself.
///
/// # Errors
/// As [`resolve_program`], plus an IO error if `root` cannot be read.
pub fn resolve_file(root: &Path) -> Result<Program, ResolveError> {
    let src = std::fs::read_to_string(root).map_err(|e| ResolveError {
        kind: ResolveErrorKind::Io {
            path: root.to_path_buf(),
            detail: e.to_string(),
        },
        path: root.to_path_buf(),
    })?;
    resolve_program(root, &src)
}

fn module_stem(path: &Path) -> Ident {
    path.file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "utama".to_string())
}

fn parse_source(src: &str, module: &str, path: &Path) -> Result<Program, ResolveError> {
    let mut parser = Parser::new(src);
    parser.parse_program().map_err(|e| ResolveError {
        kind: ResolveErrorKind::Parse {
            module: module.to_string(),
            detail: e.to_string(),
        },
        path: path.to_path_buf(),
    })
}

/// Depth-first load of every `guna` target, dependencies first.
fn load_imports(
    program: &Program,
    importer_path: &Path,
    loaded: &mut Vec<LoadedModule>,
    seen: &mut HashSet<PathBuf>,
    stack: &mut Vec<Ident>,
) -> Result<(), ResolveError> {
    let dir = importer_path.parent().unwrap_or_else(|| Path::new("."));
    let importer = module_stem(importer_path);

    for import in &program.imports {
        let child_path = dir.join(format!("{}.rii", import.module));

        // Cycle check BEFORE touching the filesystem, so a cycle reports the
        // chain rather than recursing until the stack dies.
        if stack.contains(&import.module) || importer == import.module {
            let mut chain = stack.clone();
            chain.push(importer.clone());
            chain.push(import.module.clone());
            return Err(ResolveError {
                kind: ResolveErrorKind::CircularImport { chain },
                path: importer_path.to_path_buf(),
            });
        }

        // Canonicalize so `./kira.rii` and `kira.rii` are one module.
        let key = std::fs::canonicalize(&child_path).unwrap_or_else(|_| child_path.clone());
        if seen.contains(&key) {
            continue; // diamond import — already linked
        }

        if !child_path.is_file() {
            return Err(ResolveError {
                kind: ResolveErrorKind::ModuleNotFound {
                    module: import.module.clone(),
                    tried: child_path,
                },
                path: importer_path.to_path_buf(),
            });
        }

        let src = std::fs::read_to_string(&child_path).map_err(|e| ResolveError {
            kind: ResolveErrorKind::Io {
                path: child_path.clone(),
                detail: e.to_string(),
            },
            path: importer_path.to_path_buf(),
        })?;
        let child = parse_source(&src, &import.module, &child_path)?;

        seen.insert(key);
        stack.push(importer.clone());
        load_imports(&child, &child_path, loaded, seen, stack)?;
        stack.pop();

        loaded.push(LoadedModule {
            name: import.module.clone(),
            path: child_path,
            program: child,
        });
    }
    Ok(())
}

/// Top-level names a module introduces (functions and bindings).
fn top_level_names(program: &Program) -> Vec<Ident> {
    let mut names = Vec::new();
    for decl in &program.decls {
        match decl {
            TopLevelDecl::Function { name, .. } | TopLevelDecl::Binding { name, .. } => {
                names.push(name.clone());
            }
            TopLevelDecl::ExternBlock { decls, .. } => {
                for d in decls {
                    names.push(d.name.clone());
                }
            }
            TopLevelDecl::Expr(_) | TopLevelDecl::Test { .. } => {}
        }
    }
    names
}

/// Rename every module's names, check the rules, and concatenate.
fn link(mut loaded: Vec<LoadedModule>, root_name: &str) -> Result<Program, ResolveError> {
    // 1. Per-module rename maps. The root is never renamed.
    let mut owner: HashMap<Ident, Ident> = HashMap::new(); // final name -> module
    let mut public_final: HashSet<Ident> = HashSet::new();
    let mut private_final: HashMap<Ident, Ident> = HashMap::new(); // final name -> module

    let mut maps: Vec<HashMap<Ident, Ident>> = Vec::with_capacity(loaded.len());
    for m in &loaded {
        let is_root = m.name == root_name;
        let mut map = HashMap::new();
        for n in top_level_names(&m.program) {
            let final_name = if is_root {
                n.clone()
            } else {
                format!("{}_{}", m.name, n)
            };
            if let Some(prev) = owner.get(&final_name) {
                return Err(ResolveError {
                    kind: ResolveErrorKind::NameCollision {
                        name: final_name,
                        first: prev.clone(),
                        second: m.name.clone(),
                    },
                    path: m.path.clone(),
                });
            }
            owner.insert(final_name.clone(), m.name.clone());
            if is_root || m.program.public_names.contains(&n) {
                public_final.insert(final_name.clone());
            } else {
                private_final.insert(final_name.clone(), m.name.clone());
            }
            map.insert(n, final_name);
        }
        maps.push(map);
    }

    // 2. Rewrite each module in place: declaration names and free references.
    for (m, map) in loaded.iter_mut().zip(maps.iter()) {
        let is_root = m.name == root_name;
        if !is_root {
            // An imported module must not carry a program body. A trailing
            // `Expr(Unit)` is what the parser appends at EOF — harmless, drop
            // it. Anything else is real top-level code and is rejected.
            for decl in &m.program.decls {
                if let TopLevelDecl::Expr(e) = decl {
                    if **e != Expr::Unit {
                        return Err(ResolveError {
                            kind: ResolveErrorKind::TopLevelCodeInModule {
                                module: m.name.clone(),
                            },
                            path: m.path.clone(),
                        });
                    }
                }
            }
            m.program
                .decls
                .retain(|d| !matches!(d, TopLevelDecl::Expr(_)));
        }
        for decl in &mut m.program.decls {
            rename_decl(decl, map);
        }
    }

    // 3. Visibility + direct-import checks, on the renamed forms.
    for (i, m) in loaded.iter().enumerate() {
        let imported: HashSet<&str> = m
            .program
            .imports
            .iter()
            .map(|im| im.module.as_str())
            .collect();
        let own: HashSet<&Ident> = maps[i].values().collect();

        let mut refs: Vec<Ident> = Vec::new();
        for decl in &m.program.decls {
            collect_decl_refs(decl, &mut refs);
        }
        for r in refs {
            if own.contains(&r) {
                continue; // own definition
            }
            if let Some(target_mod) = private_final.get(&r) {
                if *target_mod != m.name {
                    let short = r
                        .strip_prefix(&format!("{target_mod}_"))
                        .unwrap_or(&r)
                        .to_string();
                    return Err(ResolveError {
                        kind: ResolveErrorKind::PrivateAccess {
                            module: target_mod.clone(),
                            name: short,
                            from: m.name.clone(),
                        },
                        path: m.path.clone(),
                    });
                }
            } else if public_final.contains(&r) {
                if let Some(target_mod) = owner.get(&r) {
                    if *target_mod != m.name
                        && *target_mod != root_name
                        && !imported.contains(target_mod.as_str())
                    {
                        let short = r
                            .strip_prefix(&format!("{target_mod}_"))
                            .unwrap_or(&r)
                            .to_string();
                        return Err(ResolveError {
                            kind: ResolveErrorKind::MissingImport {
                                module: target_mod.clone(),
                                name: short,
                                from: m.name.clone(),
                            },
                            path: m.path.clone(),
                        });
                    }
                }
            }
            // Anything else is a builtin or a genuine unbound name; the
            // typechecker reports it with a proper span.
        }
    }

    // 4. Concatenate — dependencies first, root last (its trailing expression
    //    stays the program body).
    let mut decls: Vec<TopLevelDecl> = Vec::new();
    let mut spans: Vec<SpannedDecl> = Vec::new();
    let mut imports = Vec::new();
    let mut public_names = Vec::new();
    for m in loaded {
        if m.name == root_name {
            imports = m.program.imports.clone();
            public_names = m.program.public_names.clone();
        }
        decls.extend(m.program.decls);
        // Spans belong to their own file; a linked program spans several files,
        // so per-decl spans are dropped for imported modules and kept only for
        // the root, whose source is what a diagnostic renders against.
        if m.name == root_name {
            spans = m.program.spans;
        }
    }
    Ok(Program::with_modules(decls, spans, imports, public_names))
}

/// Apply a rename map to a declaration: its own name and its free references.
fn rename_decl(decl: &mut TopLevelDecl, map: &HashMap<Ident, Ident>) {
    match decl {
        TopLevelDecl::Function {
            name, params, body, ..
        } => {
            if let Some(new) = map.get(name) {
                name.clone_from(new);
            }
            // Parameters shadow top-level names inside the body.
            let mut bound: Vec<Ident> = params.iter().map(|(p, _)| p.clone()).collect();
            walk_free_idents(body, &mut bound, &mut |id| {
                if let Some(new) = map.get(id) {
                    id.clone_from(new);
                }
            });
        }
        TopLevelDecl::Binding { name, value, .. } => {
            if let Some(new) = map.get(name) {
                name.clone_from(new);
            }
            let mut bound = Vec::new();
            walk_free_idents(value, &mut bound, &mut |id| {
                if let Some(new) = map.get(id) {
                    id.clone_from(new);
                }
            });
        }
        TopLevelDecl::Expr(e) => {
            let mut bound = Vec::new();
            walk_free_idents(e, &mut bound, &mut |id| {
                if let Some(new) = map.get(id) {
                    id.clone_from(new);
                }
            });
        }
        TopLevelDecl::Test { body, .. } => {
            let mut bound = Vec::new();
            walk_free_idents(body, &mut bound, &mut |id| {
                if let Some(new) = map.get(id) {
                    id.clone_from(new);
                }
            });
        }
        TopLevelDecl::ExternBlock { decls, .. } => {
            for d in decls {
                if let Some(new) = map.get(&d.name) {
                    d.name.clone_from(new);
                }
            }
        }
    }
}

/// Collect every free identifier a declaration references.
fn collect_decl_refs(decl: &TopLevelDecl, out: &mut Vec<Ident>) {
    // The walk needs `&mut Expr`; cloning the body is acceptable here because
    // this runs once per declaration during linking, not in a hot path.
    let mut scratch;
    let (body, mut bound): (&mut Expr, Vec<Ident>) = match decl {
        TopLevelDecl::Function { params, body, .. } => {
            scratch = (**body).clone();
            (&mut scratch, params.iter().map(|(p, _)| p.clone()).collect())
        }
        TopLevelDecl::Binding { value, .. } => {
            scratch = (**value).clone();
            (&mut scratch, Vec::new())
        }
        TopLevelDecl::Expr(e) => {
            scratch = (**e).clone();
            (&mut scratch, Vec::new())
        }
        TopLevelDecl::Test { body, .. } => {
            scratch = (**body).clone();
            (&mut scratch, Vec::new())
        }
        TopLevelDecl::ExternBlock { .. } => return,
    };
    walk_free_idents(body, &mut bound, &mut |id| out.push(id.clone()));
}

/// Visit every FREE identifier reference in `e`, honouring binders.
///
/// `bound` is the binder stack; `f` is applied to each free `Var` name (and may
/// rewrite it in place).
///
/// The `match` below is deliberately exhaustive with **no wildcard arm**: a new
/// `Expr` variant must break this build rather than silently skip renaming and
/// yield a mis-linked program.
fn walk_free_idents<F: FnMut(&mut Ident)>(e: &mut Expr, bound: &mut Vec<Ident>, f: &mut F) {
    match e {
        // ── the only reference site ──────────────────────────────────────
        Expr::Var(name) => {
            if !bound.contains(name) {
                f(name);
            }
        }

        // A mutable-slot read/write names its slot, so both are reference sites.
        Expr::SlotGet(name) => {
            if !bound.contains(name) {
                f(name);
            }
        }
        Expr::SlotSet(name, value) => {
            if !bound.contains(name) {
                f(name);
            }
            walk_free_idents(value, bound, f);
        }

        // ── binders ──────────────────────────────────────────────────────
        Expr::LetMut(name, value, body) => {
            walk_free_idents(value, bound, f); // value is OUTSIDE the binding
            bound.push(name.clone());
            walk_free_idents(body, bound, f);
            bound.pop();
        }
        Expr::Lam(param, _, body) => {
            bound.push(param.clone());
            walk_free_idents(body, bound, f);
            bound.pop();
        }
        Expr::Let(name, _, value, body) => {
            walk_free_idents(value, bound, f); // value is OUTSIDE the binding
            bound.push(name.clone());
            walk_free_idents(body, bound, f);
            bound.pop();
        }
        Expr::LetRec(name, _, value, body) => {
            bound.push(name.clone()); // recursive: in scope in its own value
            walk_free_idents(value, bound, f);
            walk_free_idents(body, bound, f);
            bound.pop();
        }
        Expr::LetRecGroup(entries, cont) => {
            // Every group name is in scope in every value AND the continuation.
            let n = entries.len();
            for (name, _, _) in entries.iter() {
                bound.push(name.clone());
            }
            for (_, _, value) in entries.iter_mut() {
                walk_free_idents(value, bound, f);
            }
            walk_free_idents(cont, bound, f);
            bound.truncate(bound.len() - n);
        }
        Expr::Case(scrutinee, left, left_body, right, right_body) => {
            walk_free_idents(scrutinee, bound, f);
            bound.push(left.clone());
            walk_free_idents(left_body, bound, f);
            bound.pop();
            bound.push(right.clone());
            walk_free_idents(right_body, bound, f);
            bound.pop();
        }
        Expr::Handle(body, name, handler) => {
            walk_free_idents(body, bound, f);
            bound.push(name.clone());
            walk_free_idents(handler, bound, f);
            bound.pop();
        }

        // ── leaves with no identifier references ─────────────────────────
        Expr::Unit
        | Expr::Bool(_)
        | Expr::Int(_)
        | Expr::IntN { .. }
        | Expr::String(_)
        | Expr::Loc(_)
        | Expr::Break
        | Expr::Continue
        | Expr::UIColor(..)
        | Expr::UIStyleDecl { .. }
        | Expr::ChoreographyBlock { .. } => {}

        // ── one child ────────────────────────────────────────────────────
        Expr::Fst(a)
        | Expr::Snd(a)
        | Expr::Inl(a, _)
        | Expr::Inr(a, _)
        | Expr::Return(a)
        | Expr::Perform(_, a)
        | Expr::Ref(a, _)
        | Expr::Deref(a)
        | Expr::Classify(a)
        | Expr::Prove(a)
        | Expr::Require(_, a)
        | Expr::Grant(_, a)
        | Expr::FieldAccess(a, _)
        | Expr::ActorRecv(a)
        | Expr::ContentHash(a)
        | Expr::ContractDeploy(a)
        | Expr::ZakatCalculate(a) => walk_free_idents(a, bound, f),

        // ── two children ─────────────────────────────────────────────────
        Expr::App(a, b)
        | Expr::Pair(a, b)
        | Expr::Assign(a, b)
        | Expr::Declassify(a, b)
        | Expr::BinOp(_, a, b)
        | Expr::Spawn(a, b)
        | Expr::ActorSend(a, b)
        | Expr::CRDTMerge(a, b)
        | Expr::ContentVerify(a, b)
        | Expr::UIText(a, b)
        | Expr::UIButton(a, b)
        | Expr::While(a, b)
        | Expr::UIContrastCheck(a, b) => {
            walk_free_idents(a, bound, f);
            walk_free_idents(b, bound, f);
        }

        // ── three children ───────────────────────────────────────────────
        Expr::If(a, b, c)
        | Expr::TokenTransfer {
            from: a,
            to: b,
            amount: c,
        } => {
            walk_free_idents(a, bound, f);
            walk_free_idents(b, bound, f);
            walk_free_idents(c, bound, f);
        }

        // ── sequences ────────────────────────────────────────────────────
        Expr::ListLit(items)
        | Expr::UIDisplay(items)
        | Expr::UIRow(items)
        | Expr::UIColumn(items) => {
            for item in items {
                walk_free_idents(item, bound, f);
            }
        }
        Expr::RecordLit(_, fields) => {
            // The record name is a type name and the keys are labels; only the
            // field VALUES are expressions.
            for (_, value) in fields {
                walk_free_idents(value, bound, f);
            }
        }
        Expr::FFICall { args, .. } => {
            // `name` is a foreign symbol, not a RIINA binding.
            for arg in args {
                walk_free_idents(arg, bound, f);
            }
        }
        Expr::ActorDecl {
            init_state,
            handler,
            ..
        } => {
            // `name` declares an actor type, a separate namespace from values.
            walk_free_idents(init_state, bound, f);
            walk_free_idents(handler, bound, f);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A throwaway directory that cleans itself up.
    ///
    /// The resolver's whole job is reading sibling files off disk, so the
    /// interesting half of it cannot be tested without a filesystem. No
    /// external temp-dir crate (Law 8: zero external dependencies).
    struct Sandbox(PathBuf);

    impl Sandbox {
        fn new(tag: &str) -> Self {
            let dir = std::env::temp_dir().join(format!(
                "riina_modres_{tag}_{}",
                std::process::id()
            ));
            let _ = std::fs::remove_dir_all(&dir);
            std::fs::create_dir_all(&dir).expect("create sandbox");
            Self(dir)
        }

        fn write(&self, name: &str, contents: &str) -> PathBuf {
            let p = self.0.join(name);
            std::fs::write(&p, contents).expect("write module");
            p
        }
    }

    impl Drop for Sandbox {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    const KIRA: &str = "\
awam fungsi tambah(x: Nombor, y: Nombor) -> Nombor kesan Bersih { x + y }
awam fungsi dua_kali(x: Nombor) -> Nombor kesan Bersih { tambah(x, x) }
fungsi rahsia_dalaman(x: Nombor) -> Nombor kesan Bersih { x * 99 }
";

    /// Resolve `main.rii` in `sb` and return the error kind, failing the test
    /// if resolution unexpectedly SUCCEEDED.
    fn resolve_err(sb: &Sandbox, main: &Path) -> ResolveErrorKind {
        match resolve_file(main) {
            Ok(_) => panic!("expected resolution to fail in {}", sb.0.display()),
            Err(e) => e.kind,
        }
    }

    /// The linked program is one flat namespace: imported names are prefixed
    /// with their module, the ROOT's names are left alone.
    #[test]
    fn links_imported_names_and_leaves_the_root_alone() {
        let sb = Sandbox::new("link");
        sb.write("kira.rii", KIRA);
        let main = sb.write(
            "main.rii",
            "guna kira;\nfungsi utama() -> Nombor kesan Bersih { kira::tambah(3, 4) }\n",
        );
        let linked = resolve_file(&main).expect("resolves");
        let names = top_level_names(&linked);
        assert!(names.contains(&"kira_tambah".to_string()), "{names:?}");
        assert!(names.contains(&"kira_dua_kali".to_string()), "{names:?}");
        // The root keeps its own names — `utama` must stay `utama` or nothing
        // downstream can find the entry point.
        assert!(names.contains(&"utama".to_string()), "{names:?}");
        assert!(!names.contains(&"main_utama".to_string()), "{names:?}");
        // A private helper is still LINKED (its module needs it) — visibility
        // is enforced by reference checking, not by dropping the definition.
        assert!(
            names.contains(&"kira_rahsia_dalaman".to_string()),
            "{names:?}"
        );
    }

    /// A module imported through two paths is loaded and linked ONCE.
    #[test]
    fn diamond_import_links_the_shared_module_once() {
        let sb = Sandbox::new("diamond");
        sb.write("asas.rii", "awam fungsi nilai() -> Nombor kesan Bersih { 1 }\n");
        sb.write(
            "kiri.rii",
            "guna asas;\nawam fungsi l() -> Nombor kesan Bersih { asas::nilai() }\n",
        );
        sb.write(
            "kanan.rii",
            "guna asas;\nawam fungsi r() -> Nombor kesan Bersih { asas::nilai() }\n",
        );
        let main = sb.write(
            "main.rii",
            "guna kiri;\nguna kanan;\n\
             fungsi utama() -> Nombor kesan Bersih { kiri::l() + kanan::r() }\n",
        );
        let linked = resolve_file(&main).expect("resolves");
        let names = top_level_names(&linked);
        let n = names.iter().filter(|s| *s == "asas_nilai").count();
        assert_eq!(n, 1, "shared module linked {n} times: {names:?}");
    }

    /// A multi-segment path names the BUILTIN namespace and has no file behind
    /// it, so it must not be looked up on disk. This is what keeps every
    /// pre-REQ-71 example resolving unchanged.
    #[test]
    fn qualified_path_is_not_a_file_import() {
        let sb = Sandbox::new("builtin_ns");
        let main = sb.write(
            "main.rii",
            "guna std::teks;\nfungsi utama() -> Nombor kesan Bersih { 0 }\n",
        );
        resolve_file(&main).expect("a qualified path must not be resolved as a file");
    }

    #[test]
    fn missing_module_reports_the_file_it_looked_for() {
        let sb = Sandbox::new("missing");
        let main = sb.write(
            "main.rii",
            "guna tiada_ini;\nfungsi utama() -> Nombor kesan Bersih { 0 }\n",
        );
        match resolve_err(&sb, &main) {
            ResolveErrorKind::ModuleNotFound { module, tried } => {
                assert_eq!(module, "tiada_ini");
                assert!(tried.ends_with("tiada_ini.rii"), "{}", tried.display());
            }
            other => panic!("wrong kind: {other:?}"),
        }
    }

    /// A cycle must terminate with the CHAIN, not recurse to death.
    #[test]
    fn circular_import_reports_the_chain() {
        let sb = Sandbox::new("cycle");
        sb.write(
            "a.rii",
            "guna b;\nawam fungsi fa() -> Nombor kesan Bersih { b::fb() }\n",
        );
        sb.write(
            "b.rii",
            "guna a;\nawam fungsi fb() -> Nombor kesan Bersih { a::fa() }\n",
        );
        let main = sb.write(
            "main.rii",
            "guna a;\nfungsi utama() -> Nombor kesan Bersih { a::fa() }\n",
        );
        match resolve_err(&sb, &main) {
            ResolveErrorKind::CircularImport { chain } => {
                assert!(chain.contains(&"a".to_string()), "{chain:?}");
                assert!(chain.contains(&"b".to_string()), "{chain:?}");
            }
            other => panic!("wrong kind: {other:?}"),
        }
    }

    /// Two modules producing the same linked name is an ERROR. Silent
    /// shadowing would mean the program that runs is not the one written.
    #[test]
    fn colliding_linked_names_are_rejected() {
        let sb = Sandbox::new("collide");
        sb.write("kira.rii", KIRA);
        let main = sb.write(
            "main.rii",
            "guna kira;\n\
             fungsi kira_tambah(x: Nombor) -> Nombor kesan Bersih { x }\n\
             fungsi utama() -> Nombor kesan Bersih { kira::tambah(1, 2) }\n",
        );
        match resolve_err(&sb, &main) {
            ResolveErrorKind::NameCollision { name, .. } => assert_eq!(name, "kira_tambah"),
            other => panic!("wrong kind: {other:?}"),
        }
    }

    /// A non-`awam` name is module-private even though linking puts every name
    /// into one flat namespace.
    #[test]
    fn private_name_is_not_reachable_across_a_module_boundary() {
        let sb = Sandbox::new("private");
        sb.write("kira.rii", KIRA);
        let main = sb.write(
            "main.rii",
            "guna kira;\nfungsi utama() -> Nombor kesan Bersih { kira::rahsia_dalaman(2) }\n",
        );
        match resolve_err(&sb, &main) {
            ResolveErrorKind::PrivateAccess { module, name, from } => {
                assert_eq!(module, "kira");
                assert_eq!(name, "rahsia_dalaman");
                assert_eq!(from, "main");
            }
            other => panic!("wrong kind: {other:?}"),
        }
    }

    /// A transitively-loaded module IS in the linked program — it has to be,
    /// for its importer — but it is not silently in scope.
    #[test]
    fn transitive_module_requires_a_direct_import() {
        let sb = Sandbox::new("transitive");
        sb.write("deep.rii", "awam fungsi jauh() -> Nombor kesan Bersih { 7 }\n");
        sb.write(
            "mid.rii",
            "guna deep;\nawam fungsi pertengahan() -> Nombor kesan Bersih { deep::jauh() }\n",
        );
        let main = sb.write(
            "main.rii",
            "guna mid;\nfungsi utama() -> Nombor kesan Bersih { deep::jauh() }\n",
        );
        match resolve_err(&sb, &main) {
            ResolveErrorKind::MissingImport { module, name, from } => {
                assert_eq!(module, "deep");
                assert_eq!(name, "jauh");
                assert_eq!(from, "main");
            }
            other => panic!("wrong kind: {other:?}"),
        }
    }

    /// Only the ROOT file may have a program body. Top-level code in an
    /// imported module would run at an unspecified point during linking.
    #[test]
    fn top_level_code_in_an_imported_module_is_rejected() {
        let sb = Sandbox::new("toplevel");
        sb.write(
            "kesan_sampingan.rii",
            "awam fungsi f() -> Nombor kesan Bersih { 1 }\ncetakln(\"hai\");\n",
        );
        let main = sb.write(
            "main.rii",
            "guna kesan_sampingan;\n\
             fungsi utama() -> Nombor kesan Bersih { kesan_sampingan::f() }\n",
        );
        match resolve_err(&sb, &main) {
            ResolveErrorKind::TopLevelCodeInModule { module } => {
                assert_eq!(module, "kesan_sampingan");
            }
            other => panic!("wrong kind: {other:?}"),
        }
    }

    /// A parse failure in an IMPORTED file names that module, not the root —
    /// otherwise the diagnostic points at the wrong file.
    #[test]
    fn parse_error_in_an_imported_module_names_that_module() {
        let sb = Sandbox::new("parse");
        sb.write("rosak.rii", "fungsi ( ) ) tidak sah\n");
        let main = sb.write(
            "main.rii",
            "guna rosak;\nfungsi utama() -> Nombor kesan Bersih { 0 }\n",
        );
        match resolve_err(&sb, &main) {
            ResolveErrorKind::Parse { module, detail } => {
                assert_eq!(module, "rosak");
                assert!(!detail.is_empty(), "inner diagnostic was dropped");
            }
            other => panic!("wrong kind: {other:?}"),
        }
    }

    /// `resolve_file` on a path that does not exist is an IO error naming the
    /// path, not a panic.
    #[test]
    fn unreadable_root_is_an_io_error() {
        let sb = Sandbox::new("io");
        let missing = sb.0.join("tiada.rii");
        match resolve_file(&missing) {
            Err(ResolveError {
                kind: ResolveErrorKind::Io { path, .. },
                ..
            }) => assert_eq!(path, missing),
            other => panic!("wrong result: {other:?}"),
        }
    }

    /// Every error kind renders a message that names the thing at fault and
    /// says what to do. These strings are the user-facing half of the feature,
    /// so they are asserted rather than left to drift.
    #[test]
    fn every_error_kind_renders_an_actionable_message() {
        let at = |kind| ResolveError {
            kind,
            path: PathBuf::from("/x/main.rii"),
        };
        let cases: Vec<(ResolveError, Vec<&str>)> = vec![
            (
                at(ResolveErrorKind::ModuleNotFound {
                    module: "kira".into(),
                    tried: PathBuf::from("/x/kira.rii"),
                }),
                vec!["kira", "/x/kira.rii", "guna std::teks"],
            ),
            (
                at(ResolveErrorKind::Io {
                    path: PathBuf::from("/x/kira.rii"),
                    detail: "permission denied".into(),
                }),
                vec!["/x/kira.rii", "permission denied"],
            ),
            (
                at(ResolveErrorKind::CircularImport {
                    chain: vec!["a".into(), "b".into(), "a".into()],
                }),
                vec!["circular import", "a -> b -> a"],
            ),
            (
                at(ResolveErrorKind::NameCollision {
                    name: "f".into(),
                    first: "a".into(),
                    second: "b".into(),
                }),
                vec!["collision", "never \n  silently shadows", "`a`", "`b`"],
            ),
            (
                at(ResolveErrorKind::PrivateAccess {
                    module: "kira".into(),
                    name: "rahsia".into(),
                    from: "main".into(),
                }),
                vec!["private", "awam fungsi rahsia"],
            ),
            (
                at(ResolveErrorKind::MissingImport {
                    module: "deep".into(),
                    name: "jauh".into(),
                    from: "main".into(),
                }),
                vec!["without importing", "guna deep;"],
            ),
            (
                at(ResolveErrorKind::TopLevelCodeInModule {
                    module: "m".into(),
                }),
                vec!["top-level code", "move it into a function"],
            ),
            (
                at(ResolveErrorKind::Parse {
                    module: "m".into(),
                    detail: "unexpected token".into(),
                }),
                vec!["in module `m`", "unexpected token"],
            ),
        ];
        for (err, expected) in cases {
            let rendered = err.to_string();
            for needle in expected {
                // The collision note wraps across a line; compare on collapsed
                // whitespace so the assertion pins the WORDS, not the layout.
                let flat: String = rendered.split_whitespace().collect::<Vec<_>>().join(" ");
                let flat_needle: String =
                    needle.split_whitespace().collect::<Vec<_>>().join(" ");
                assert!(
                    flat.contains(&flat_needle),
                    "{:?} missing {flat_needle:?} in {flat:?}",
                    err.kind
                );
            }
        }
    }

    fn parse(src: &str) -> Expr {
        let mut p = Parser::new(src);
        let prog = p.parse_program().expect("parses");
        prog.desugar()
    }

    /// Rename `f` -> `m_f` in an expression with no shadowing.
    #[test]
    fn renames_free_reference() {
        let mut e = Expr::Var("f".into());
        let map: HashMap<Ident, Ident> = [("f".to_string(), "m_f".to_string())].into();
        let mut bound = Vec::new();
        walk_free_idents(&mut e, &mut bound, &mut |id| {
            if let Some(n) = map.get(id) {
                id.clone_from(n);
            }
        });
        assert_eq!(e, Expr::Var("m_f".into()));
    }

    /// A `let`-bound name shadows a top-level one and must NOT be renamed.
    #[test]
    fn shadowed_name_is_not_renamed() {
        // let f = 1 in f
        let mut e = Expr::Let(
            "f".into(),
            None,
            Box::new(Expr::Int(1)),
            Box::new(Expr::Var("f".into())),
        );
        let map: HashMap<Ident, Ident> = [("f".to_string(), "m_f".to_string())].into();
        let mut bound = Vec::new();
        walk_free_idents(&mut e, &mut bound, &mut |id| {
            if let Some(n) = map.get(id) {
                id.clone_from(n);
            }
        });
        match e {
            Expr::Let(_, _, _, body) => assert_eq!(*body, Expr::Var("f".into())),
            other => panic!("shape changed: {other:?}"),
        }
    }

    /// A lambda parameter shadows a top-level name.
    #[test]
    fn lambda_param_shadows() {
        let mut e = Expr::Lam(
            "x".into(),
            riina_types::Ty::Int,
            Box::new(Expr::Var("x".into())),
        );
        let map: HashMap<Ident, Ident> = [("x".to_string(), "m_x".to_string())].into();
        let mut bound = Vec::new();
        walk_free_idents(&mut e, &mut bound, &mut |id| {
            if let Some(n) = map.get(id) {
                id.clone_from(n);
            }
        });
        match e {
            Expr::Lam(_, _, body) => assert_eq!(*body, Expr::Var("x".into())),
            other => panic!("shape changed: {other:?}"),
        }
    }

    /// The value of a non-recursive `let` is OUTSIDE the binding, so a
    /// reference there still renames.
    #[test]
    fn let_value_is_outside_its_own_binding() {
        let mut e = Expr::Let(
            "f".into(),
            None,
            Box::new(Expr::Var("f".into())),
            Box::new(Expr::Unit),
        );
        let map: HashMap<Ident, Ident> = [("f".to_string(), "m_f".to_string())].into();
        let mut bound = Vec::new();
        walk_free_idents(&mut e, &mut bound, &mut |id| {
            if let Some(n) = map.get(id) {
                id.clone_from(n);
            }
        });
        match e {
            Expr::Let(_, _, value, _) => assert_eq!(*value, Expr::Var("m_f".into())),
            other => panic!("shape changed: {other:?}"),
        }
    }

    /// The binder stack must be restored exactly (a truncate bug here would
    /// leak binders into sibling expressions and silently skip renames).
    #[test]
    fn letrecgroup_restores_binder_stack() {
        let mut e = Expr::Pair(
            Box::new(Expr::LetRecGroup(
                vec![("g".into(), riina_types::Ty::Int, Expr::Var("g".into()))],
                Box::new(Expr::Unit),
            )),
            Box::new(Expr::Var("g".into())),
        );
        let map: HashMap<Ident, Ident> = [("g".to_string(), "m_g".to_string())].into();
        let mut bound = Vec::new();
        walk_free_idents(&mut e, &mut bound, &mut |id| {
            if let Some(n) = map.get(id) {
                id.clone_from(n);
            }
        });
        assert!(bound.is_empty(), "binder stack leaked: {bound:?}");
        match e {
            // Inside the group `g` is bound (not renamed); outside it is free.
            Expr::Pair(_, rhs) => assert_eq!(*rhs, Expr::Var("m_g".into())),
            other => panic!("shape changed: {other:?}"),
        }
    }

    /// A real program body walks without panicking and renames the call site.
    #[test]
    fn renames_call_site_in_parsed_program() {
        let mut e = parse("fungsi utama() -> Nombor kesan Bersih { tambah(1) }");
        let map: HashMap<Ident, Ident> = [("tambah".to_string(), "kira_tambah".to_string())].into();
        let mut bound = Vec::new();
        let mut seen = Vec::new();
        walk_free_idents(&mut e, &mut bound, &mut |id| {
            if let Some(n) = map.get(id) {
                id.clone_from(n);
            }
            seen.push(id.clone());
        });
        assert!(
            seen.contains(&"kira_tambah".to_string()),
            "call site not renamed; saw {seen:?}"
        );
    }
}
