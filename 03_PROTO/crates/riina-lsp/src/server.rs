// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! LSP Server main loop.

use std::collections::HashMap;
use std::io::{self, Write};

use crate::analysis;
use crate::json::{self, JsonValue};
use crate::jsonrpc;

/// Run the LSP server over stdio.
pub fn run() -> io::Result<()> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut reader = io::BufReader::new(stdin.lock());
    let mut writer = stdout.lock();
    let mut documents: HashMap<String, String> = HashMap::new();

    loop {
        let msg = match jsonrpc::read_message(&mut reader) {
            Ok(m) => m,
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => break,
            Err(e) => return Err(e),
        };

        let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");
        let id = msg.get("id").cloned();
        let params = msg.get("params").cloned().unwrap_or(JsonValue::Null);

        match method {
            "initialize" => {
                let result = json::obj(vec![
                    ("capabilities", json::obj(vec![
                        ("textDocumentSync", JsonValue::Number(1.0)), // Full sync
                        ("hoverProvider", JsonValue::Bool(true)),
                        ("completionProvider", json::obj(vec![
                            ("triggerCharacters", JsonValue::Array(vec![
                                JsonValue::String(".".into()),
                            ])),
                        ])),
                    ])),
                    ("serverInfo", json::obj(vec![
                        ("name", JsonValue::String("riina-lsp".into())),
                        ("version", JsonValue::String("0.1.0".into())),
                    ])),
                ]);
                if let Some(id) = id {
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, result))?;
                }
            }
            "initialized" => {
                // No response needed
            }
            "shutdown" => {
                if let Some(id) = id {
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, JsonValue::Null))?;
                }
            }
            "exit" => {
                break;
            }
            "textDocument/didOpen" => {
                if let Some(td) = params.get("textDocument") {
                    let uri = td.get("uri").and_then(|v| v.as_str()).unwrap_or("").to_string();
                    let text = td.get("text").and_then(|v| v.as_str()).unwrap_or("").to_string();
                    documents.insert(uri.clone(), text.clone());
                    publish_diagnostics(&mut writer, &uri, &text)?;
                }
            }
            "textDocument/didChange" => {
                if let Some(td) = params.get("textDocument") {
                    let uri = td.get("uri").and_then(|v| v.as_str()).unwrap_or("").to_string();
                    if let Some(JsonValue::Array(arr)) = params.get("contentChanges") {
                        if let Some(change) = arr.first() {
                            let text = change.get("text").and_then(|v| v.as_str()).unwrap_or("").to_string();
                            documents.insert(uri.clone(), text.clone());
                            publish_diagnostics(&mut writer, &uri, &text)?;
                        }
                    }
                }
            }
            "textDocument/hover" => {
                if let Some(id) = id {
                    let result = handle_hover(&params, &documents);
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, result))?;
                }
            }
            "textDocument/completion" => {
                if let Some(id) = id {
                    let result = handle_completion();
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, result))?;
                }
            }
            _ => {
                // Unknown method — ignore notifications, respond null to requests
                if let Some(id) = id {
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, JsonValue::Null))?;
                }
            }
        }
    }

    Ok(())
}

fn publish_diagnostics(writer: &mut impl Write, uri: &str, source: &str) -> io::Result<()> {
    let diags = analysis::analyze(source);
    let items: Vec<JsonValue> = diags
        .iter()
        .map(|d| {
            json::obj(vec![
                ("range", json::obj(vec![
                    ("start", json::obj(vec![
                        ("line", JsonValue::Number(d.start_line as f64)),
                        ("character", JsonValue::Number(d.start_col as f64)),
                    ])),
                    ("end", json::obj(vec![
                        ("line", JsonValue::Number(d.end_line as f64)),
                        ("character", JsonValue::Number(d.end_col as f64)),
                    ])),
                ])),
                ("severity", JsonValue::Number(d.severity as u8 as f64)),
                ("source", JsonValue::String("riina".into())),
                ("message", JsonValue::String(d.message.clone())),
            ])
        })
        .collect();

    let notif = jsonrpc::notification(
        "textDocument/publishDiagnostics",
        json::obj(vec![
            ("uri", JsonValue::String(uri.into())),
            ("diagnostics", JsonValue::Array(items)),
        ]),
    );
    jsonrpc::write_message(writer, &notif)
}

fn handle_hover(params: &JsonValue, documents: &HashMap<String, String>) -> JsonValue {
    let uri = params
        .get("textDocument")
        .and_then(|td| td.get("uri"))
        .and_then(|v| v.as_str())
        .unwrap_or("");

    let _line = params
        .get("position")
        .and_then(|p| p.get("line"))
        .and_then(|v| v.as_i64())
        .unwrap_or(0) as usize;

    let _col = params
        .get("position")
        .and_then(|p| p.get("character"))
        .and_then(|v| v.as_i64())
        .unwrap_or(0) as usize;

    let _source = documents.get(uri);

    // Basic hover: show file URI and type info
    // Full implementation needs span map from M1
    json::obj(vec![
        ("contents", json::obj(vec![
            ("kind", JsonValue::String("markdown".into())),
            ("value", JsonValue::String("RIINA — hover info coming soon".into())),
        ])),
    ])
}

fn handle_completion() -> JsonValue {
    // Return keyword completions
    let keywords = [
        ("fungsi", "Function declaration"),
        ("biar", "Variable binding"),
        ("kalau", "If conditional"),
        ("lain", "Else branch"),
        ("untuk", "For loop"),
        ("selagi", "While loop"),
        ("ulang", "Loop"),
        ("pulang", "Return"),
        ("padan", "Pattern match"),
        ("betul", "True"),
        ("salah", "False"),
        ("rahsia", "Secret type"),
        ("dedah", "Declassify"),
        ("kesan", "Effect annotation"),
        ("bersih", "Pure effect"),
        ("laku", "Perform effect"),
        ("kendali", "Handle effect"),
        ("sulit", "Classify"),
        ("bukti", "Prove"),
        ("ruj", "Reference"),
        ("perlukan", "Require capability"),
        ("beri", "Grant capability"),
        ("pastikan", "Guard clause"),
        ("modul", "Module declaration"),
        ("guna", "Use/import"),
        ("awam", "Public visibility"),
    ];

    let items: Vec<JsonValue> = keywords
        .iter()
        .map(|(label, detail)| {
            json::obj(vec![
                ("label", JsonValue::String((*label).into())),
                ("kind", JsonValue::Number(14.0)), // Keyword
                ("detail", JsonValue::String((*detail).into())),
            ])
        })
        .collect();

    json::obj(vec![("items", JsonValue::Array(items))])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_completion_returns_keywords() {
        let result = handle_completion();
        if let Some(items) = result.get("items") {
            if let JsonValue::Array(arr) = items {
                assert!(!arr.is_empty());
                let first = &arr[0];
                assert!(first.get("label").is_some());
            } else {
                panic!("Expected array");
            }
        } else {
            panic!("Expected items key");
        }
    }
}
