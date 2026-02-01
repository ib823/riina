// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! RIINA WASM Playground Library
//!
//! Thin WASM-only crate that wraps the compiler pipeline (lexer, parser,
//! typechecker, codegen) for in-browser use. Exports raw `extern "C"` functions
//! consumed by a JS Web Worker.
//!
//! # Exports
//!
//! - `riina_alloc(size) -> *mut u8` — allocate WASM linear memory
//! - `riina_free(ptr, size)` — free allocated memory
//! - `riina_check(ptr, len) -> *mut u8` — parse + typecheck → JSON result
//! - `riina_emit_c(ptr, len) -> *mut u8` — full pipeline → C source
//! - `riina_emit_ir(ptr, len) -> *mut u8` — full pipeline → IR dump
//!
//! # Memory Protocol
//!
//! Returned pointers point to `[u32_len_le][utf8_bytes]` — the first 4 bytes
//! are the length (little-endian u32), followed by the UTF-8 payload.
//! The caller must free the returned pointer with `riina_free(ptr, len + 4)`.
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use std::alloc::{alloc, dealloc, Layout};
use std::slice;
use std::str;

// ---------------------------------------------------------------------------
// Memory management exports
// ---------------------------------------------------------------------------

/// Allocate `size` bytes of WASM linear memory.
#[no_mangle]
pub extern "C" fn riina_alloc(size: usize) -> *mut u8 {
    if size == 0 {
        return std::ptr::null_mut();
    }
    let layout = Layout::from_size_align(size, 1).unwrap();
    unsafe { alloc(layout) }
}

/// Free `size` bytes at `ptr`.
///
/// # Safety
///
/// `ptr` must have been allocated by `riina_alloc` with the same `size`.
#[no_mangle]
pub unsafe extern "C" fn riina_free(ptr: *mut u8, size: usize) {
    if ptr.is_null() || size == 0 {
        return;
    }
    let layout = Layout::from_size_align(size, 1).unwrap();
    dealloc(ptr, layout);
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Read a UTF-8 string from WASM memory at (ptr, len).
fn read_input(ptr: *const u8, len: usize) -> Result<String, String> {
    if ptr.is_null() {
        return Err("null input pointer".into());
    }
    let bytes = unsafe { slice::from_raw_parts(ptr, len) };
    str::from_utf8(bytes)
        .map(|s| s.to_string())
        .map_err(|e| format!("invalid UTF-8: {e}"))
}

/// Write a string result into WASM memory with the length-prefix protocol.
/// Returns a pointer to `[u32_len_le][utf8_bytes]`.
fn write_output(s: &str) -> *mut u8 {
    let bytes = s.as_bytes();
    let total = 4 + bytes.len();
    let ptr = riina_alloc(total);
    if ptr.is_null() {
        return ptr;
    }
    let len_bytes = (bytes.len() as u32).to_le_bytes();
    unsafe {
        std::ptr::copy_nonoverlapping(len_bytes.as_ptr(), ptr, 4);
        std::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr.add(4), bytes.len());
    }
    ptr
}

/// Format a JSON success result.
fn json_ok(field: &str, value: &str) -> String {
    let escaped = value
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t");
    format!("{{\"ok\":true,\"{field}\":\"{escaped}\"}}")
}

/// Format a JSON error result.
fn json_err(msg: &str) -> String {
    let escaped = msg
        .replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
        .replace('\t', "\\t");
    format!("{{\"ok\":false,\"error\":\"{escaped}\"}}")
}

// ---------------------------------------------------------------------------
// Pipeline helpers
// ---------------------------------------------------------------------------

fn do_parse(source: &str) -> Result<riina_types::Expr, String> {
    let mut parser = riina_parser::Parser::new(source);
    parser.parse_expr().map_err(|e| format!("Parse error: {e:?}"))
}

fn do_typecheck(expr: &riina_types::Expr) -> Result<String, String> {
    let ctx = riina_typechecker::Context::new();
    match riina_typechecker::type_check(&ctx, expr) {
        Ok((ty, eff)) => Ok(format!("Type: {ty:?}, Effect: {eff:?}")),
        Err(e) => Err(format!("Type error: {e:?}")),
    }
}

fn do_compile_ir(expr: &riina_types::Expr) -> Result<String, String> {
    let program = riina_codegen::compile(expr).map_err(|e| format!("Codegen error: {e:?}"))?;
    Ok(format!("{program:#?}"))
}

fn do_compile_c(expr: &riina_types::Expr) -> Result<String, String> {
    riina_codegen::compile_to_c(expr).map_err(|e| format!("Codegen error: {e:?}"))
}

// ---------------------------------------------------------------------------
// WASM exports
// ---------------------------------------------------------------------------

/// Parse + typecheck the RIINA source at (ptr, len).
/// Returns a length-prefixed JSON string.
#[no_mangle]
pub extern "C" fn riina_check(ptr: *const u8, len: usize) -> *mut u8 {
    let result = (|| -> Result<String, String> {
        let source = read_input(ptr, len)?;
        let expr = do_parse(&source)?;
        let ty_info = do_typecheck(&expr)?;
        Ok(ty_info)
    })();

    let json = match result {
        Ok(info) => json_ok("diagnostics", &info),
        Err(e) => json_err(&e),
    };
    write_output(&json)
}

/// Parse + typecheck + emit C code.
/// Returns a length-prefixed JSON string with the C output.
#[no_mangle]
pub extern "C" fn riina_emit_c(ptr: *const u8, len: usize) -> *mut u8 {
    let result = (|| -> Result<String, String> {
        let source = read_input(ptr, len)?;
        let expr = do_parse(&source)?;
        let _ = do_typecheck(&expr)?;
        do_compile_c(&expr)
    })();

    let json = match result {
        Ok(c_code) => json_ok("output", &c_code),
        Err(e) => json_err(&e),
    };
    write_output(&json)
}

/// Parse + typecheck + emit IR dump.
/// Returns a length-prefixed JSON string with the IR.
#[no_mangle]
pub extern "C" fn riina_emit_ir(ptr: *const u8, len: usize) -> *mut u8 {
    let result = (|| -> Result<String, String> {
        let source = read_input(ptr, len)?;
        let expr = do_parse(&source)?;
        let _ = do_typecheck(&expr)?;
        do_compile_ir(&expr)
    })();

    let json = match result {
        Ok(ir) => json_ok("output", &ir),
        Err(e) => json_err(&e),
    };
    write_output(&json)
}
