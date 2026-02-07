// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! JSON-RPC message reader/writer over stdio.

use std::io::{self, BufRead, Write};
use crate::json::{self, JsonValue};

/// Read a JSON-RPC message from stdin (Content-Length framed).
pub fn read_message(reader: &mut impl BufRead) -> io::Result<JsonValue> {
    // Read headers
    let mut content_length: usize = 0;
    loop {
        let mut line = String::new();
        reader.read_line(&mut line)?;
        let line = line.trim();
        if line.is_empty() {
            break;
        }
        if let Some(len_str) = line.strip_prefix("Content-Length: ") {
            content_length = len_str.parse().map_err(|e| {
                io::Error::new(io::ErrorKind::InvalidData, format!("Bad Content-Length: {e}"))
            })?;
        }
    }

    if content_length == 0 {
        return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "No Content-Length"));
    }

    // Read body
    let mut buf = vec![0u8; content_length];
    reader.read_exact(&mut buf)?;
    let body = String::from_utf8(buf)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("Bad UTF-8: {e}")))?;

    json::parse(&body)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, format!("Bad JSON: {e}")))
}

/// Write a JSON-RPC message to stdout (Content-Length framed).
pub fn write_message(writer: &mut impl Write, msg: &JsonValue) -> io::Result<()> {
    let body = msg.to_string();
    write!(writer, "Content-Length: {}\r\n\r\n{}", body.len(), body)?;
    writer.flush()
}

/// Build a JSON-RPC response.
pub fn response(id: JsonValue, result: JsonValue) -> JsonValue {
    json::obj(vec![
        ("jsonrpc", JsonValue::String("2.0".into())),
        ("id", id),
        ("result", result),
    ])
}

/// Build a JSON-RPC notification.
pub fn notification(method: &str, params: JsonValue) -> JsonValue {
    json::obj(vec![
        ("jsonrpc", JsonValue::String("2.0".into())),
        ("method", JsonValue::String(method.into())),
        ("params", params),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_message() {
        let body = r#"{"a":2,"id":1}"#;
        let input = format!("Content-Length: {}\r\n\r\n{}", body.len(), body);
        let mut reader = io::BufReader::new(input.as_bytes());
        let msg = read_message(&mut reader).unwrap();
        assert_eq!(msg.get("id"), Some(&JsonValue::Number(1.0)));
    }

    #[test]
    fn test_write_message() {
        let msg = json::obj(vec![("id", JsonValue::Number(1.0))]);
        let mut buf = Vec::new();
        write_message(&mut buf, &msg).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.starts_with("Content-Length: "));
        assert!(s.contains("\"id\":1"));
    }
}
