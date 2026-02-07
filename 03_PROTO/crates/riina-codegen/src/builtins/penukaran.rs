// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Conversion builtins (penukaran)

use crate::value::Value;
use crate::{Error, Result};
use super::format_value;

/// Apply a conversion builtin. Returns Ok(None) if name doesn't match.
pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "ke_teks" => Ok(Some(Value::String(format_value(arg)))),
        "ke_nombor" => match arg {
            Value::String(s) => s
                .parse::<u64>()
                .map(|n| Some(Value::Int(n)))
                .map_err(|_| Error::InvalidOperation(format!("cannot parse '{}' as integer", s))),
            _ => Err(Error::TypeMismatch {
                expected: "string".to_string(),
                found: format!("{:?}", arg),
                context: "ke_nombor/parse_int".to_string(),
            }),
        },
        "ke_bool" => {
            let b = match arg {
                Value::Bool(b) => *b,
                Value::Int(n) => *n != 0,
                Value::String(s) => !s.is_empty(),
                Value::Unit => false,
                Value::List(items) => !items.is_empty(),
                Value::Map(entries) => !entries.is_empty(),
                _ => true,
            };
            Ok(Some(Value::Bool(b)))
        }
        "bool_ke_nombor" => match arg {
            Value::Bool(b) => Ok(Some(Value::Int(if *b { 1 } else { 0 }))),
            _ => Err(Error::TypeMismatch {
                expected: "bool".to_string(),
                found: format!("{:?}", arg),
                context: "bool_ke_nombor/bool_to_int".to_string(),
            }),
        },
        "nombor_ke_teks" => match arg {
            Value::Int(n) => Ok(Some(Value::String(n.to_string()))),
            _ => Err(Error::TypeMismatch {
                expected: "int".to_string(),
                found: format!("{:?}", arg),
                context: "nombor_ke_teks/int_to_string".to_string(),
            }),
        },
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ke_teks() {
        assert_eq!(apply("ke_teks", &Value::Int(42)).unwrap(), Some(Value::String("42".to_string())));
    }

    #[test]
    fn test_ke_nombor() {
        assert_eq!(apply("ke_nombor", &Value::String("99".to_string())).unwrap(), Some(Value::Int(99)));
    }

    #[test]
    fn test_ke_bool_truthy() {
        assert_eq!(apply("ke_bool", &Value::Int(1)).unwrap(), Some(Value::Bool(true)));
        assert_eq!(apply("ke_bool", &Value::Int(0)).unwrap(), Some(Value::Bool(false)));
        assert_eq!(apply("ke_bool", &Value::String("x".to_string())).unwrap(), Some(Value::Bool(true)));
        assert_eq!(apply("ke_bool", &Value::String(String::new())).unwrap(), Some(Value::Bool(false)));
        assert_eq!(apply("ke_bool", &Value::Unit).unwrap(), Some(Value::Bool(false)));
    }

    #[test]
    fn test_bool_ke_nombor() {
        assert_eq!(apply("bool_ke_nombor", &Value::Bool(true)).unwrap(), Some(Value::Int(1)));
        assert_eq!(apply("bool_ke_nombor", &Value::Bool(false)).unwrap(), Some(Value::Int(0)));
    }

    #[test]
    fn test_nombor_ke_teks() {
        assert_eq!(apply("nombor_ke_teks", &Value::Int(123)).unwrap(), Some(Value::String("123".to_string())));
    }
}
