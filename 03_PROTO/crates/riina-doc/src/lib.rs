// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! RIINA Documentation Generator
//!
//! Parses .rii files and generates HTML documentation.
//! Extracts `///` doc comments and attaches them to declarations.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

#![forbid(unsafe_code)]

use riina_types::{Effect, Program, TopLevelDecl, Ty};

/// A documented declaration.
#[derive(Debug, Clone)]
pub struct DocItem {
    pub name: String,
    pub kind: DocKind,
    pub doc: String,
    pub signature: String,
}

#[derive(Debug, Clone)]
pub enum DocKind {
    Function,
    Binding,
}

/// Extract doc comments from source (lines starting with `///`).
/// Returns vec of (line_number, doc_text) pairs.
fn extract_doc_comments(source: &str) -> Vec<(usize, String)> {
    source
        .lines()
        .enumerate()
        .filter_map(|(i, line)| {
            let trimmed = line.trim();
            if let Some(rest) = trimmed.strip_prefix("///") {
                Some((i, rest.trim_start().to_string()))
            } else {
                None
            }
        })
        .collect()
}

/// Collect doc comments preceding a given line.
fn collect_preceding_docs(doc_comments: &[(usize, String)], decl_line: usize) -> String {
    let mut docs = Vec::new();
    for (line, text) in doc_comments.iter().rev() {
        if *line < decl_line && decl_line - line <= docs.len() + 1 {
            docs.push(text.clone());
        } else if !docs.is_empty() {
            break;
        }
    }
    docs.reverse();
    docs.join("\n")
}

fn format_ty(ty: &Ty) -> String {
    match ty {
        Ty::Unit => "()".into(),
        Ty::Bool => "Benar".into(),
        Ty::Int => "Nombor".into(),
        Ty::String => "Teks".into(),
        Ty::Bytes => "Bait".into(),
        Ty::List(inner) => format!("Senarai<{}>", format_ty(inner)),
        Ty::Option(inner) => format!("Mungkin<{}>", format_ty(inner)),
        Ty::Secret(inner) => format!("Rahsia<{}>", format_ty(inner)),
        Ty::Fn(a, b, eff) => {
            if *eff == Effect::Pure {
                format!("Fn({}, {})", format_ty(a), format_ty(b))
            } else {
                format!("Fn({}, {}, {:?})", format_ty(a), format_ty(b), eff)
            }
        }
        Ty::Any => "Any".into(),
        _ => format!("{ty:?}"),
    }
}

fn format_effect(eff: &Effect) -> &'static str {
    match eff {
        Effect::Pure => "Bersih",
        Effect::Read => "Baca",
        Effect::Write => "Tulis",
        Effect::FileSystem => "SistemFail",
        Effect::Network => "Rangkaian",
        Effect::Crypto => "Kripto",
        Effect::Time => "Masa",
        _ => "Lain",
    }
}

/// Generate doc items from a parsed program and source text.
pub fn extract_docs(source: &str, program: &Program) -> Vec<DocItem> {
    let doc_comments = extract_doc_comments(source);
    let mut items = Vec::new();

    // Find which line each decl starts on (approximate via span info or source scan)
    for (i, decl) in program.decls.iter().enumerate() {
        let decl_line = if i < program.spans.len() {
            // Use span to find line
            let offset = program.spans[i].span.start;
            source[..offset].chars().filter(|c| *c == '\n').count()
        } else {
            0
        };

        let doc = collect_preceding_docs(&doc_comments, decl_line);

        match decl {
            TopLevelDecl::Function {
                name,
                params,
                return_ty,
                effect,
                ..
            } => {
                let params_str: Vec<String> = params
                    .iter()
                    .map(|(n, t)| format!("{n}: {}", format_ty(t)))
                    .collect();
                let mut sig = format!("fungsi {}({})", name, params_str.join(", "));
                if *return_ty != Ty::Unit {
                    sig.push_str(&format!(" -> {}", format_ty(return_ty)));
                }
                if *effect != Effect::Pure {
                    sig.push_str(&format!(" kesan {}", format_effect(effect)));
                }
                items.push(DocItem {
                    name: name.clone(),
                    kind: DocKind::Function,
                    doc,
                    signature: sig,
                });
            }
            TopLevelDecl::Binding { name, .. } => {
                items.push(DocItem {
                    name: name.clone(),
                    kind: DocKind::Binding,
                    doc,
                    signature: format!("biar {name}"),
                });
            }
            TopLevelDecl::Expr(_) => {}
            TopLevelDecl::ExternBlock { abi, decls } => {
                for decl in decls {
                    let params_str: Vec<String> = decl.params
                        .iter()
                        .map(|(n, t)| format!("{n}: {}", format_ty(t)))
                        .collect();
                    let mut sig = format!("luaran \"{abi}\" fungsi {}({})", decl.name, params_str.join(", "));
                    if decl.ret_ty != Ty::Unit {
                        sig.push_str(&format!(" -> {}", format_ty(&decl.ret_ty)));
                    }
                    if decl.effect != Effect::Pure {
                        sig.push_str(&format!(" kesan {}", format_effect(&decl.effect)));
                    }
                    items.push(DocItem {
                        name: decl.name.clone(),
                        kind: DocKind::Function,
                        doc: doc.clone(),
                        signature: sig,
                    });
                }
            }
        }
    }

    items
}

/// Generate HTML documentation from doc items.
pub fn generate_html(title: &str, items: &[DocItem]) -> String {
    let mut html = String::new();
    html.push_str("<!DOCTYPE html>\n<html lang=\"ms\">\n<head>\n");
    html.push_str("<meta charset=\"utf-8\">\n");
    html.push_str(&format!("<title>{title} — RIINA Dokumentasi</title>\n"));
    html.push_str("<style>\n");
    html.push_str("body { font-family: -apple-system, BlinkMacSystemFont, sans-serif; max-width: 900px; margin: 0 auto; padding: 2em; background: #fafafa; }\n");
    html.push_str("h1 { color: #1a1a2e; border-bottom: 2px solid #16213e; padding-bottom: 0.3em; }\n");
    html.push_str("h2 { color: #16213e; margin-top: 2em; }\n");
    html.push_str(".sig { background: #0f3460; color: #e0e0e0; padding: 0.8em 1em; border-radius: 6px; font-family: 'JetBrains Mono', monospace; font-size: 0.9em; }\n");
    html.push_str(".doc { padding: 0.5em 0; color: #333; line-height: 1.6; }\n");
    html.push_str(".kind { display: inline-block; padding: 2px 8px; border-radius: 3px; font-size: 0.75em; font-weight: bold; margin-right: 8px; }\n");
    html.push_str(".kind-fn { background: #533483; color: white; }\n");
    html.push_str(".kind-let { background: #0f3460; color: white; }\n");
    html.push_str("</style>\n</head>\n<body>\n");
    html.push_str(&format!("<h1>{title}</h1>\n"));
    html.push_str("<p>Dijana oleh <code>riina-doc</code> — RIINA Documentation Generator</p>\n");

    // Table of contents
    html.push_str("<h2>Kandungan</h2>\n<ul>\n");
    for item in items {
        html.push_str(&format!(
            "<li><a href=\"#{}\">{}</a></li>\n",
            item.name, item.name
        ));
    }
    html.push_str("</ul>\n");

    // Items
    for item in items {
        let kind_class = match item.kind {
            DocKind::Function => "kind-fn",
            DocKind::Binding => "kind-let",
        };
        let kind_label = match item.kind {
            DocKind::Function => "fungsi",
            DocKind::Binding => "biar",
        };

        html.push_str(&format!("<h2 id=\"{}\">{}</h2>\n", item.name, item.name));
        html.push_str(&format!(
            "<span class=\"kind {kind_class}\">{kind_label}</span>\n"
        ));
        html.push_str(&format!("<pre class=\"sig\">{}</pre>\n", item.signature));
        if !item.doc.is_empty() {
            html.push_str(&format!(
                "<div class=\"doc\">{}</div>\n",
                item.doc.replace('\n', "<br>")
            ));
        }
    }

    html.push_str("</body>\n</html>\n");
    html
}

/// Generate HTML documentation from source text.
pub fn generate_from_source(title: &str, source: &str) -> Result<String, String> {
    let mut parser = riina_parser::Parser::new(source);
    let program = parser
        .parse_program()
        .map_err(|e| format!("Parse error: {e}"))?;
    let items = extract_docs(source, &program);
    Ok(generate_html(title, &items))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_doc_comments() {
        let source = "/// This is a doc\n/// Second line\nfungsi foo() { () }";
        let comments = extract_doc_comments(source);
        assert_eq!(comments.len(), 2);
        assert_eq!(comments[0].1, "This is a doc");
    }

    #[test]
    fn test_generate_html_basic() {
        let items = vec![DocItem {
            name: "tambah".into(),
            kind: DocKind::Function,
            doc: "Adds two numbers".into(),
            signature: "fungsi tambah(x: Nombor, y: Nombor) -> Nombor".into(),
        }];
        let html = generate_html("Test", &items);
        assert!(html.contains("tambah"));
        assert!(html.contains("Adds two numbers"));
    }

    #[test]
    fn test_generate_from_source() {
        let source = "fungsi tambah(x: Nombor, y: Nombor) -> Nombor { x + y }";
        let html = generate_from_source("test", source).unwrap();
        assert!(html.contains("tambah"));
    }
}
