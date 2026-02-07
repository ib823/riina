// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! File I/O builtins (fail)

use crate::value::Value;
use crate::{Error, Result};

/// (BM name, EN alias, canonical name)
pub static BUILTINS: &[(&str, &str, &str)] = &[
    ("fail_baca", "file_read", "fail_baca"),
    ("fail_tulis", "file_write", "fail_tulis"),
    ("fail_tambah", "file_append", "fail_tambah"),
    ("fail_ada", "file_exists", "fail_ada"),
    ("fail_buang", "file_delete", "fail_buang"),
    ("fail_panjang", "file_size", "fail_panjang"),
    ("fail_senarai", "file_list_dir", "fail_senarai"),
    ("fail_baca_baris", "file_read_lines", "fail_baca_baris"),
];

pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "fail_baca" => {
            // Teks -> Teks
            let path = extract_string(arg, "fail_baca")?;
            let content = std::fs::read_to_string(&path).map_err(|e| {
                Error::InvalidOperation(format!("fail_baca: cannot read '{}': {}", path, e))
            })?;
            Ok(Some(Value::String(content)))
        }
        "fail_tulis" => {
            // (Teks, Teks) -> ()
            let (path, content) = extract_pair_strings(arg, "fail_tulis")?;
            std::fs::write(&path, &content).map_err(|e| {
                Error::InvalidOperation(format!("fail_tulis: cannot write '{}': {}", path, e))
            })?;
            Ok(Some(Value::Unit))
        }
        "fail_tambah" => {
            // (Teks, Teks) -> ()
            let (path, content) = extract_pair_strings(arg, "fail_tambah")?;
            use std::io::Write;
            let mut f = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&path)
                .map_err(|e| {
                    Error::InvalidOperation(format!("fail_tambah: cannot open '{}': {}", path, e))
                })?;
            f.write_all(content.as_bytes()).map_err(|e| {
                Error::InvalidOperation(format!("fail_tambah: write error: {}", e))
            })?;
            Ok(Some(Value::Unit))
        }
        "fail_ada" => {
            // Teks -> Bool
            let path = extract_string(arg, "fail_ada")?;
            Ok(Some(Value::Bool(std::path::Path::new(&path).exists())))
        }
        "fail_buang" => {
            // Teks -> Bool
            let path = extract_string(arg, "fail_buang")?;
            let ok = std::fs::remove_file(&path).is_ok();
            Ok(Some(Value::Bool(ok)))
        }
        "fail_panjang" => {
            // Teks -> Int
            let path = extract_string(arg, "fail_panjang")?;
            let meta = std::fs::metadata(&path).map_err(|e| {
                Error::InvalidOperation(format!("fail_panjang: cannot stat '{}': {}", path, e))
            })?;
            Ok(Some(Value::Int(meta.len())))
        }
        "fail_senarai" => {
            // Teks -> List<Teks>
            let path = extract_string(arg, "fail_senarai")?;
            let entries = std::fs::read_dir(&path).map_err(|e| {
                Error::InvalidOperation(format!("fail_senarai: cannot read dir '{}': {}", path, e))
            })?;
            let mut items = Vec::new();
            for e in entries.flatten() {
                if let Some(name) = e.file_name().to_str() {
                    items.push(Value::String(name.to_string()));
                }
            }
            Ok(Some(Value::List(items)))
        }
        "fail_baca_baris" => {
            // Teks -> List<Teks>
            let path = extract_string(arg, "fail_baca_baris")?;
            let content = std::fs::read_to_string(&path).map_err(|e| {
                Error::InvalidOperation(format!("fail_baca_baris: cannot read '{}': {}", path, e))
            })?;
            let lines: Vec<Value> = content.lines().map(|l| Value::String(l.to_string())).collect();
            Ok(Some(Value::List(lines)))
        }
        _ => Ok(None),
    }
}

fn extract_string(v: &Value, ctx: &str) -> Result<String> {
    match v {
        Value::String(s) => Ok(s.clone()),
        _ => Err(type_err("string", v, ctx)),
    }
}

fn extract_pair_strings(v: &Value, ctx: &str) -> Result<(String, String)> {
    match v {
        Value::Pair(a, b) => {
            let sa = extract_string(a, ctx)?;
            let sb = extract_string(b, ctx)?;
            Ok((sa, sb))
        }
        _ => Err(type_err("(string, string)", v, ctx)),
    }
}

fn type_err(expected: &str, found: &Value, ctx: &str) -> Error {
    Error::TypeMismatch {
        expected: expected.to_string(),
        found: format!("{:?}", found),
        context: ctx.to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_fail_tulis_baca() {
        let tmp = std::env::temp_dir().join("riina_test_fail.txt");
        let path = tmp.to_str().unwrap().to_string();

        // Write
        let arg = Value::Pair(
            Box::new(Value::String(path.clone())),
            Box::new(Value::String("hello riina".to_string())),
        );
        assert_eq!(apply("fail_tulis", &arg).unwrap(), Some(Value::Unit));

        // Read
        let result = apply("fail_baca", &Value::String(path.clone())).unwrap().unwrap();
        assert_eq!(result, Value::String("hello riina".to_string()));

        // Exists
        assert_eq!(
            apply("fail_ada", &Value::String(path.clone())).unwrap(),
            Some(Value::Bool(true))
        );

        // Size
        let size = apply("fail_panjang", &Value::String(path.clone())).unwrap().unwrap();
        assert_eq!(size, Value::Int(11));

        // Delete
        assert_eq!(
            apply("fail_buang", &Value::String(path.clone())).unwrap(),
            Some(Value::Bool(true))
        );

        // No longer exists
        assert_eq!(
            apply("fail_ada", &Value::String(path)).unwrap(),
            Some(Value::Bool(false))
        );
    }

    #[test]
    fn test_fail_tambah() {
        let tmp = std::env::temp_dir().join("riina_test_append.txt");
        let path = tmp.to_str().unwrap().to_string();

        // Write initial
        let _ = std::fs::write(&path, "line1\n");
        let arg = Value::Pair(
            Box::new(Value::String(path.clone())),
            Box::new(Value::String("line2\n".to_string())),
        );
        apply("fail_tambah", &arg).unwrap();

        let content = std::fs::read_to_string(&path).unwrap();
        assert_eq!(content, "line1\nline2\n");
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_fail_baca_baris() {
        let tmp = std::env::temp_dir().join("riina_test_lines.txt");
        let path = tmp.to_str().unwrap().to_string();
        std::fs::write(&path, "a\nb\nc").unwrap();

        let result = apply("fail_baca_baris", &Value::String(path.clone())).unwrap().unwrap();
        assert_eq!(result, Value::List(vec![
            Value::String("a".to_string()),
            Value::String("b".to_string()),
            Value::String("c".to_string()),
        ]));
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn test_fail_senarai() {
        let tmp = std::env::temp_dir().join("riina_test_dir");
        let _ = std::fs::create_dir_all(&tmp);
        std::fs::write(tmp.join("a.txt"), "").unwrap();
        std::fs::write(tmp.join("b.txt"), "").unwrap();

        let result = apply("fail_senarai", &Value::String(tmp.to_str().unwrap().to_string()))
            .unwrap()
            .unwrap();
        match result {
            Value::List(items) => assert!(items.len() >= 2),
            _ => panic!("expected list"),
        }
        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[test]
    fn test_unknown_returns_none() {
        assert_eq!(apply("unknown", &Value::Unit).unwrap(), None);
    }
}
