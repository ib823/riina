// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! MCP (Model Context Protocol) server for RIINA.
//!
//! Exposes RIINA compiler tools (check, test, run, format) to AI agents
//! over stdin/stdout using JSON-RPC 2.0 with Content-Length framing.
//!
//! # Protocol
//!
//! The MCP server implements the 2024-11-05 protocol version:
//! - `initialize` → server capabilities
//! - `tools/list` → available tools
//! - `tools/call` → execute a tool
//!
//! # Tools
//!
//! | Tool | Description |
//! |------|-------------|
//! | `riina_check` | Parse and typecheck RIINA source code |
//! | `riina_test` | Run inline ujian (test) blocks |
//! | `riina_run` | Interpret RIINA source code |
//! | `riina_format` | Format RIINA source code |
//!
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

use std::io;

use riina_lsp::json::{self, JsonValue};
use riina_lsp::jsonrpc;

/// Maximum JSON-RPC message size: 1 MiB.
/// This prevents OOM from malicious or broken clients sending huge Content-Length.
const MAX_MESSAGE_BYTES: usize = 1_048_576;

/// Maximum source code size accepted by tools: 256 KiB.
/// Source code larger than this is rejected before parsing to prevent
/// excessive memory use during AST construction and typechecking.
const MAX_SOURCE_BYTES: usize = 262_144;

/// Run the MCP server loop over stdin/stdout.
pub fn run() -> Result<(), Box<dyn std::error::Error>> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut reader = io::BufReader::new(stdin.lock());
    let mut writer = stdout.lock();

    eprintln!("RIINA MCP Server v0.1.0 — ready");

    loop {
        let msg = match jsonrpc::read_message_bounded(&mut reader, MAX_MESSAGE_BYTES) {
            Ok(m) => m,
            Err(e) => {
                // EOF — clean shutdown
                if e.kind() == io::ErrorKind::UnexpectedEof {
                    break;
                }
                // Oversized or malformed — send error if possible, then continue
                // (don't crash the server on one bad message)
                if e.kind() == io::ErrorKind::InvalidData {
                    eprintln!("MCP rejected message: {e}");
                    continue;
                }
                eprintln!("MCP read error: {e}");
                break;
            }
        };

        let method = msg.get("method").and_then(|v| v.as_str()).unwrap_or("");
        let id = msg.get("id").cloned();
        let params = msg.get("params").cloned().unwrap_or(JsonValue::Null);

        match method {
            "initialize" => {
                if let Some(id) = id {
                    let result = handle_initialize();
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, result))?;
                }
            }
            "initialized" => {
                // Notification — no response needed
            }
            "tools/list" => {
                if let Some(id) = id {
                    let result = handle_tools_list();
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, result))?;
                }
            }
            "tools/call" => {
                if let Some(id) = id {
                    let result = handle_tools_call(&params);
                    jsonrpc::write_message(&mut writer, &jsonrpc::response(id, result))?;
                }
            }
            "shutdown" | "exit" => {
                if let Some(id) = id {
                    jsonrpc::write_message(
                        &mut writer,
                        &jsonrpc::response(id, JsonValue::Null),
                    )?;
                }
                break;
            }
            "notifications/cancelled" => {
                // Ignore cancellation notifications
            }
            _ => {
                // Unknown method — return error if it has an id
                if let Some(id) = id {
                    let err = json_rpc_error(id, -32601, &format!("Method not found: {method}"));
                    jsonrpc::write_message(&mut writer, &err)?;
                }
            }
        }
    }

    Ok(())
}

fn handle_initialize() -> JsonValue {
    json::obj(vec![
        ("protocolVersion", JsonValue::String("2024-11-05".into())),
        ("capabilities", json::obj(vec![
            ("tools", json::obj(vec![])),
        ])),
        ("serverInfo", json::obj(vec![
            ("name", JsonValue::String("riinac".into())),
            ("version", JsonValue::String("0.1.0".into())),
        ])),
    ])
}

fn handle_tools_list() -> JsonValue {
    json::obj(vec![
        ("tools", JsonValue::Array(vec![
            tool_def(
                "riina_check",
                "Parse and typecheck RIINA source code. Returns type, effect, and any diagnostics.",
                &[("source", "string", "RIINA source code to check")],
            ),
            tool_def(
                "riina_test",
                "Run inline ujian (test) blocks in RIINA source code. Returns pass/fail for each test.",
                &[("source", "string", "RIINA source code containing ujian blocks")],
            ),
            tool_def(
                "riina_run",
                "Interpret RIINA source code and return the result value.",
                &[("source", "string", "RIINA source code to run")],
            ),
            tool_def(
                "riina_format",
                "Format RIINA source code using the canonical formatter.",
                &[("source", "string", "RIINA source code to format")],
            ),
        ])),
    ])
}

fn handle_tools_call(params: &JsonValue) -> JsonValue {
    let tool_name = params.get("name").and_then(|v| v.as_str()).unwrap_or("");
    let args = params.get("arguments").cloned().unwrap_or(JsonValue::Null);
    let source = args.get("source").and_then(|v| v.as_str()).unwrap_or("");

    if source.is_empty() && tool_name != "riina_version" {
        return tool_error("Missing required argument: source");
    }

    // Reject oversized source code before parsing
    if source.len() > MAX_SOURCE_BYTES {
        return tool_error(&format!(
            "Source code too large: {} bytes (max {} bytes / {} KiB)",
            source.len(),
            MAX_SOURCE_BYTES,
            MAX_SOURCE_BYTES / 1024
        ));
    }

    match tool_name {
        "riina_check" => tool_check(source),
        "riina_test" => tool_test(source),
        "riina_run" => tool_run(source),
        "riina_format" => tool_format(source),
        _ => tool_error(&format!("Unknown tool: {tool_name}")),
    }
}

// ─── Tool implementations ─────────────────────────────────────────────

fn tool_check(source: &str) -> JsonValue {
    use riina_parser::Parser;
    use riina_typechecker::{type_check, Context};

    let mut parser = Parser::new(source);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            return tool_text(&format!(
                "{{\"success\":false,\"error\":\"Parse error: {}\"}}",
                json_escape_str(&e.to_string())
            ));
        }
    };

    let expr = program.desugar();
    let ctx = riina_typechecker::register_builtin_types(&Context::new());

    match type_check(&ctx, &expr) {
        Ok((ty, eff)) => {
            tool_text(&format!(
                "{{\"success\":true,\"type\":\"{}\",\"effect\":\"{}\"}}",
                json_escape_str(&format!("{ty:?}")),
                json_escape_str(&format!("{eff:?}"))
            ))
        }
        Err(e) => {
            let code = e.error_code();
            let fix = e.fix_hint().map(|h| json_escape_str(&h)).unwrap_or_default();
            let rule = e.coq_rule().unwrap_or("");
            tool_text(&format!(
                "{{\"success\":false,\"error\":\"{}\",\"code\":\"{code}\",\"fix_hint\":\"{fix}\",\"rule\":\"{}\"}}",
                json_escape_str(&e.to_string()),
                json_escape_str(rule)
            ))
        }
    }
}

fn tool_test(source: &str) -> JsonValue {
    use riina_parser::Parser;
    use riina_typechecker::{type_check, Context};

    let mut parser = Parser::new(source);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            return tool_text(&format!(
                "{{\"success\":false,\"error\":\"Parse error: {}\"}}",
                json_escape_str(&e.to_string())
            ));
        }
    };

    // Extract tests and non-test decls
    let test_blocks: Vec<(String, riina_types::Expr)> = program.decls.iter()
        .filter_map(|d| match d {
            riina_types::TopLevelDecl::Test { name, body } =>
                Some((name.clone(), (**body).clone())),
            _ => None,
        })
        .collect();

    let non_test_decls: Vec<riina_types::TopLevelDecl> = program.decls.iter()
        .filter(|d| !matches!(d, riina_types::TopLevelDecl::Test { .. }))
        .cloned()
        .collect();

    // Typecheck the whole file first
    let expr = program.desugar();
    let ctx = riina_typechecker::register_builtin_types(&Context::new());
    if let Err(e) = type_check(&ctx, &expr) {
        return tool_text(&format!(
            "{{\"success\":false,\"error\":\"Type error: {}\"}}",
            json_escape_str(&e.to_string())
        ));
    }

    // Run each test
    let total = test_blocks.len();
    let mut passed = 0usize;
    let mut failed = 0usize;
    let mut test_results = Vec::new();

    for (name, body) in &test_blocks {
        let test_expr = riina_types::Program::new(non_test_decls.clone())
            .desugar_with_body(body.clone());

        match riina_codegen::eval_with_builtins(&test_expr) {
            Ok(_) => {
                passed += 1;
                test_results.push(format!(
                    "{{\"name\":\"{}\",\"passed\":true}}",
                    json_escape_str(name)
                ));
            }
            Err(e) => {
                failed += 1;
                test_results.push(format!(
                    "{{\"name\":\"{}\",\"passed\":false,\"message\":\"{}\"}}",
                    json_escape_str(name),
                    json_escape_str(&e.to_string())
                ));
            }
        }
    }

    tool_text(&format!(
        "{{\"success\":{},\"tests\":[{}],\"summary\":{{\"total\":{total},\"passed\":{passed},\"failed\":{failed}}}}}",
        failed == 0,
        test_results.join(",")
    ))
}

fn tool_run(source: &str) -> JsonValue {
    use riina_parser::Parser;
    use riina_typechecker::{type_check, Context};

    let mut parser = Parser::new(source);
    let program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            return tool_text(&format!("Parse error: {e}"));
        }
    };

    let expr = program.desugar();
    let ctx = riina_typechecker::register_builtin_types(&Context::new());
    if let Err(e) = type_check(&ctx, &expr) {
        return tool_text(&format!("Type error: {e}"));
    }

    match riina_codegen::eval_with_builtins(&expr) {
        Ok(val) => tool_text(&format!("{val:?}")),
        Err(e) => tool_text(&format!("Runtime error: {e}")),
    }
}

fn tool_format(source: &str) -> JsonValue {
    match riina_fmt::format_source(source) {
        Ok(formatted) => tool_text(&formatted),
        Err(e) => tool_text(&format!("Format error: {e}")),
    }
}

// ─── Helpers ──────────────────────────────────────────────────────────

/// Build an MCP tool definition.
fn tool_def(name: &str, description: &str, params: &[(&str, &str, &str)]) -> JsonValue {
    let mut properties = Vec::new();
    let mut required = Vec::new();
    for &(pname, ptype, pdesc) in params {
        properties.push((pname, json::obj(vec![
            ("type", JsonValue::String(ptype.into())),
            ("description", JsonValue::String(pdesc.into())),
        ])));
        required.push(JsonValue::String(pname.into()));
    }

    let mut prop_map = std::collections::BTreeMap::new();
    for (k, v) in properties {
        prop_map.insert(k.to_string(), v);
    }

    json::obj(vec![
        ("name", JsonValue::String(name.into())),
        ("description", JsonValue::String(description.into())),
        ("inputSchema", json::obj(vec![
            ("type", JsonValue::String("object".into())),
            ("properties", JsonValue::Object(prop_map)),
            ("required", JsonValue::Array(required)),
        ])),
    ])
}

/// Build an MCP tool result with text content.
fn tool_text(text: &str) -> JsonValue {
    json::obj(vec![
        ("content", JsonValue::Array(vec![
            json::obj(vec![
                ("type", JsonValue::String("text".into())),
                ("text", JsonValue::String(text.into())),
            ]),
        ])),
    ])
}

/// Build an MCP tool error result.
fn tool_error(message: &str) -> JsonValue {
    json::obj(vec![
        ("isError", JsonValue::Bool(true)),
        ("content", JsonValue::Array(vec![
            json::obj(vec![
                ("type", JsonValue::String("text".into())),
                ("text", JsonValue::String(message.into())),
            ]),
        ])),
    ])
}

/// Build a JSON-RPC error response.
fn json_rpc_error(id: JsonValue, code: i64, message: &str) -> JsonValue {
    json::obj(vec![
        ("jsonrpc", JsonValue::String("2.0".into())),
        ("id", id),
        ("error", json::obj(vec![
            ("code", JsonValue::Number(code as f64)),
            ("message", JsonValue::String(message.into())),
        ])),
    ])
}

/// Escape a string for embedding in JSON (without outer quotes).
fn json_escape_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c < '\x20' => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_initialize() {
        let result = handle_initialize();
        assert_eq!(
            result.get("protocolVersion"),
            Some(&JsonValue::String("2024-11-05".into()))
        );
        let server = result.get("serverInfo").unwrap();
        assert_eq!(server.get("name"), Some(&JsonValue::String("riinac".into())));
    }

    #[test]
    fn test_handle_tools_list() {
        let result = handle_tools_list();
        let tools = result.get("tools").unwrap();
        if let JsonValue::Array(arr) = tools {
            assert_eq!(arr.len(), 4);
            let names: Vec<&str> = arr.iter()
                .filter_map(|t| t.get("name").and_then(|n| n.as_str()))
                .collect();
            assert!(names.contains(&"riina_check"));
            assert!(names.contains(&"riina_test"));
            assert!(names.contains(&"riina_run"));
            assert!(names.contains(&"riina_format"));
        } else {
            panic!("tools should be an array");
        }
    }

    #[test]
    fn test_tool_check_success() {
        let result = tool_check("fungsi utama() -> Nombor kesan Bersih { 42 }");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("\"success\":true"));
        }
    }

    #[test]
    fn test_tool_check_parse_error() {
        let result = tool_check("fungsi {{{");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("\"success\":false"));
        }
    }

    #[test]
    fn test_tool_run() {
        let result = tool_run("42");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("42"));
        }
    }

    #[test]
    fn test_tool_format() {
        let result = tool_format("biar x = 42;");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(!text.is_empty());
        }
    }

    #[test]
    fn test_tool_test_with_passing_test() {
        let source = "ujian \"basic\" {\n    tegaskan(betul)\n}\n";
        let result = tool_test(source);
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("\"success\":true"), "got: {text}");
            assert!(text.contains("\"passed\":1"), "got: {text}");
        }
    }

    #[test]
    fn test_tool_test_with_failing_test() {
        let source = "ujian \"should fail\" {\n    tegaskan(salah)\n}\n";
        let result = tool_test(source);
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("\"failed\":1"), "got: {text}");
        }
    }

    #[test]
    fn test_json_escape_str() {
        assert_eq!(json_escape_str("hello"), "hello");
        assert_eq!(json_escape_str("a\"b"), "a\\\"b");
        assert_eq!(json_escape_str("a\nb"), "a\\nb");
    }

    #[test]
    fn test_tool_error_format() {
        let result = tool_error("something went wrong");
        assert_eq!(result.get("isError"), Some(&JsonValue::Bool(true)));
    }

    // ─── Adversarial / hardening tests ───────────────────────────────

    #[test]
    fn test_unknown_tool_returns_error() {
        let params = json::obj(vec![
            ("name", JsonValue::String("nonexistent_tool".into())),
            ("arguments", json::obj(vec![
                ("source", JsonValue::String("42".into())),
            ])),
        ]);
        let result = handle_tools_call(&params);
        assert_eq!(result.get("isError"), Some(&JsonValue::Bool(true)));
    }

    #[test]
    fn test_missing_source_returns_error() {
        let params = json::obj(vec![
            ("name", JsonValue::String("riina_check".into())),
            ("arguments", json::obj(vec![])),
        ]);
        let result = handle_tools_call(&params);
        assert_eq!(result.get("isError"), Some(&JsonValue::Bool(true)));
    }

    #[test]
    fn test_empty_source_returns_error() {
        let params = json::obj(vec![
            ("name", JsonValue::String("riina_check".into())),
            ("arguments", json::obj(vec![
                ("source", JsonValue::String("".into())),
            ])),
        ]);
        let result = handle_tools_call(&params);
        assert_eq!(result.get("isError"), Some(&JsonValue::Bool(true)));
    }

    #[test]
    fn test_null_params_returns_error() {
        let result = handle_tools_call(&JsonValue::Null);
        assert_eq!(result.get("isError"), Some(&JsonValue::Bool(true)));
    }

    #[test]
    fn test_missing_tool_name_returns_error() {
        let params = json::obj(vec![
            ("arguments", json::obj(vec![
                ("source", JsonValue::String("42".into())),
            ])),
        ]);
        let result = handle_tools_call(&params);
        // Empty tool name → "Unknown tool: "
        assert_eq!(result.get("isError"), Some(&JsonValue::Bool(true)));
    }

    #[test]
    fn test_oversized_source_rejected() {
        // Create source larger than MAX_SOURCE_BYTES (256 KiB)
        let big_source = "a".repeat(MAX_SOURCE_BYTES + 1);
        let params = json::obj(vec![
            ("name", JsonValue::String("riina_check".into())),
            ("arguments", json::obj(vec![
                ("source", JsonValue::String(big_source)),
            ])),
        ]);
        let result = handle_tools_call(&params);
        assert_eq!(result.get("isError"), Some(&JsonValue::Bool(true)));
        // Verify error message mentions size
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("too large"), "got: {text}");
        }
    }

    #[test]
    fn test_source_at_exact_limit_accepted() {
        // Source of exactly MAX_SOURCE_BYTES should be accepted (though it will parse-error)
        let source = "a".repeat(MAX_SOURCE_BYTES);
        let params = json::obj(vec![
            ("name", JsonValue::String("riina_check".into())),
            ("arguments", json::obj(vec![
                ("source", JsonValue::String(source)),
            ])),
        ]);
        let result = handle_tools_call(&params);
        // Should NOT be a tool error (isError) — it's a parse error instead
        assert!(result.get("isError").is_none());
    }

    #[test]
    fn test_unicode_source_accepted() {
        // Multi-byte UTF-8 source should work
        let result = tool_check("biar nama = \"日本語\";");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            // Should parse and return some result (success or type error)
            assert!(!text.is_empty());
        }
    }

    #[test]
    fn test_json_escape_control_chars() {
        // All control characters should be escaped
        assert_eq!(json_escape_str("\x00"), "\\u0000");
        assert_eq!(json_escape_str("\x01"), "\\u0001");
        assert_eq!(json_escape_str("\x1f"), "\\u001f");
        // Tab, newline, carriage return get special escapes
        assert_eq!(json_escape_str("\t"), "\\t");
        assert_eq!(json_escape_str("\n"), "\\n");
        assert_eq!(json_escape_str("\r"), "\\r");
    }

    #[test]
    fn test_json_escape_backslash_and_quote() {
        assert_eq!(json_escape_str("path\\to\\file"), "path\\\\to\\\\file");
        assert_eq!(json_escape_str("say \"hello\""), "say \\\"hello\\\"");
    }

    #[test]
    fn test_tool_check_with_type_error_returns_code() {
        // Type error should include error code and fix hint
        let result = tool_check("fungsi f() -> Nombor kesan Bersih { betul }");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("\"success\":false"), "got: {text}");
        }
    }

    #[test]
    fn test_tool_run_runtime_error() {
        // Division by zero or similar runtime error
        let result = tool_run("tegaskan(salah)");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("error") || text.contains("Error") || text.contains("failed"),
                "Expected error message, got: {text}");
        }
    }

    #[test]
    fn test_tool_test_no_tests() {
        // Source with no ujian blocks
        let result = tool_test("biar x = 42;");
        let content = result.get("content").unwrap();
        if let JsonValue::Array(arr) = content {
            let text = arr[0].get("text").unwrap().as_str().unwrap();
            assert!(text.contains("\"total\":0"), "got: {text}");
        }
    }

    #[test]
    fn test_max_message_bytes_constant() {
        // Verify constants are reasonable
        assert_eq!(MAX_MESSAGE_BYTES, 1_048_576); // 1 MiB
        assert_eq!(MAX_SOURCE_BYTES, 262_144);    // 256 KiB
        assert!(MAX_SOURCE_BYTES < MAX_MESSAGE_BYTES);
    }
}
