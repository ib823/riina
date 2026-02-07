// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Time builtins (masa)

use crate::value::Value;
use crate::{Error, Result};

/// (BM name, EN alias, canonical name)
pub static BUILTINS: &[(&str, &str, &str)] = &[
    ("masa_sekarang", "time_now", "masa_sekarang"),
    ("masa_sekarang_ms", "time_now_ms", "masa_sekarang_ms"),
    ("masa_format", "time_format", "masa_format"),
    ("masa_urai", "time_parse", "masa_urai"),
    ("masa_tidur", "time_sleep", "masa_tidur"),
    ("masa_jam", "time_clock", "masa_jam"),
];

pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "masa_sekarang" => {
            // () -> Int (unix timestamp seconds)
            use std::time::{SystemTime, UNIX_EPOCH};
            let secs = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs();
            Ok(Some(Value::Int(secs)))
        }
        "masa_sekarang_ms" => {
            // () -> Int (unix timestamp milliseconds)
            use std::time::{SystemTime, UNIX_EPOCH};
            let ms = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as u64;
            Ok(Some(Value::Int(ms)))
        }
        "masa_format" => {
            // (Int, String) -> String
            // Simple format: just return the timestamp as string for now
            // (full strftime would require libc or chrono, both prohibited)
            match arg {
                Value::Pair(ts, _fmt) => {
                    let t = extract_int(ts, "masa_format")?;
                    Ok(Some(Value::String(t.to_string())))
                }
                _ => Err(type_err("(int, string)", arg, "masa_format")),
            }
        }
        "masa_urai" => {
            // (String, String) -> Int
            // Simple: parse string as integer timestamp
            match arg {
                Value::Pair(s, _fmt) => {
                    let text = extract_string(s, "masa_urai")?;
                    let t = text.parse::<u64>().map_err(|_| {
                        Error::InvalidOperation(format!("cannot parse '{}' as timestamp", text))
                    })?;
                    Ok(Some(Value::Int(t)))
                }
                _ => Err(type_err("(string, string)", arg, "masa_urai")),
            }
        }
        "masa_tidur" => {
            // Int -> ()  (sleep milliseconds)
            let ms = extract_int(arg, "masa_tidur")?;
            std::thread::sleep(std::time::Duration::from_millis(ms));
            Ok(Some(Value::Unit))
        }
        "masa_jam" => {
            // () -> Int (monotonic clock in nanoseconds)
            use std::time::{SystemTime, UNIX_EPOCH};
            let ns = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos() as u64;
            Ok(Some(Value::Int(ns)))
        }
        _ => Ok(None),
    }
}

fn extract_int(v: &Value, ctx: &str) -> Result<u64> {
    match v {
        Value::Int(n) => Ok(*n),
        _ => Err(type_err("int", v, ctx)),
    }
}

fn extract_string(v: &Value, ctx: &str) -> Result<String> {
    match v {
        Value::String(s) => Ok(s.clone()),
        _ => Err(type_err("string", v, ctx)),
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

    #[test]
    fn test_masa_sekarang() {
        let result = apply("masa_sekarang", &Value::Unit).unwrap().unwrap();
        match result {
            Value::Int(t) => assert!(t > 1_700_000_000), // after 2023
            _ => panic!("expected int"),
        }
    }

    #[test]
    fn test_masa_sekarang_ms() {
        let result = apply("masa_sekarang_ms", &Value::Unit).unwrap().unwrap();
        match result {
            Value::Int(t) => assert!(t > 1_700_000_000_000),
            _ => panic!("expected int"),
        }
    }

    #[test]
    fn test_masa_format() {
        let arg = Value::Pair(
            Box::new(Value::Int(1700000000)),
            Box::new(Value::String("%Y-%m-%d".to_string())),
        );
        let result = apply("masa_format", &arg).unwrap().unwrap();
        assert_eq!(result, Value::String("1700000000".to_string()));
    }

    #[test]
    fn test_masa_urai() {
        let arg = Value::Pair(
            Box::new(Value::String("1700000000".to_string())),
            Box::new(Value::String("%Y-%m-%d".to_string())),
        );
        let result = apply("masa_urai", &arg).unwrap().unwrap();
        assert_eq!(result, Value::Int(1_700_000_000));
    }

    #[test]
    fn test_masa_jam() {
        let result = apply("masa_jam", &Value::Unit).unwrap().unwrap();
        match result {
            Value::Int(t) => assert!(t > 0),
            _ => panic!("expected int"),
        }
    }

    #[test]
    fn test_unknown_returns_none() {
        assert_eq!(apply("unknown", &Value::Unit).unwrap(), None);
    }
}
