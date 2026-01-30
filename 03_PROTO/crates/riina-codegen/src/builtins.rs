//! Built-in Functions
//!
//! Provides standard built-in functions for RIINA programs.
//! These are Rust-only extensions (not in Coq).
//!
//! Bilingual names: Bahasa Melayu and English.

use crate::value::{Env, Value};
use crate::{Error, Result};

/// Register all built-in functions into the given environment.
#[must_use]
pub fn register_builtins(env: &Env) -> Env {
    let mut e = env.clone();
    // I/O
    e = e.extend("cetak".to_string(), Value::Builtin("cetak".to_string()));
    e = e.extend("print".to_string(), Value::Builtin("cetak".to_string()));
    e = e.extend("cetakln".to_string(), Value::Builtin("cetakln".to_string()));
    e = e.extend("println".to_string(), Value::Builtin("cetakln".to_string()));

    // String operations
    e = e.extend("gabung_teks".to_string(), Value::Builtin("gabung_teks".to_string()));
    e = e.extend("concat".to_string(), Value::Builtin("gabung_teks".to_string()));
    e = e.extend("panjang".to_string(), Value::Builtin("panjang".to_string()));
    e = e.extend("length".to_string(), Value::Builtin("panjang".to_string()));

    // Conversion
    e = e.extend("ke_teks".to_string(), Value::Builtin("ke_teks".to_string()));
    e = e.extend("to_string".to_string(), Value::Builtin("ke_teks".to_string()));
    e = e.extend("ke_nombor".to_string(), Value::Builtin("ke_nombor".to_string()));
    e = e.extend("parse_int".to_string(), Value::Builtin("ke_nombor".to_string()));

    e
}

/// Apply a built-in function to an argument.
pub fn apply_builtin(name: &str, arg: Value) -> Result<Value> {
    match name {
        "cetak" => {
            print!("{}", format_value(&arg));
            Ok(Value::Unit)
        }
        "cetakln" => {
            println!("{}", format_value(&arg));
            Ok(Value::Unit)
        }
        "gabung_teks" => {
            // gabung_teks takes a pair of strings
            match arg {
                Value::Pair(a, b) => {
                    let sa = value_to_string(&a)?;
                    let sb = value_to_string(&b)?;
                    Ok(Value::String(format!("{sa}{sb}")))
                }
                _ => Err(Error::TypeMismatch {
                    expected: "pair of strings".to_string(),
                    found: format!("{:?}", arg),
                    context: "gabung_teks/concat".to_string(),
                }),
            }
        }
        "panjang" => match &arg {
            Value::String(s) => Ok(Value::Int(s.len() as u64)),
            _ => Err(Error::TypeMismatch {
                expected: "string".to_string(),
                found: format!("{:?}", arg),
                context: "panjang/length".to_string(),
            }),
        },
        "ke_teks" => Ok(Value::String(format_value(&arg))),
        "ke_nombor" => match &arg {
            Value::String(s) => s
                .parse::<u64>()
                .map(Value::Int)
                .map_err(|_| Error::InvalidOperation(format!("cannot parse '{}' as integer", s))),
            _ => Err(Error::TypeMismatch {
                expected: "string".to_string(),
                found: format!("{:?}", arg),
                context: "ke_nombor/parse_int".to_string(),
            }),
        },
        _ => Err(Error::InvalidOperation(format!("unknown builtin: {name}"))),
    }
}

/// Format a value for display (user-facing, no debug wrapping).
fn format_value(v: &Value) -> String {
    match v {
        Value::Unit => "()".to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Int(n) => n.to_string(),
        Value::String(s) => s.clone(),
        Value::Pair(a, b) => format!("({}, {})", format_value(a), format_value(b)),
        other => format!("{other}"),
    }
}

/// Extract string from value.
fn value_to_string(v: &Value) -> Result<String> {
    match v {
        Value::String(s) => Ok(s.clone()),
        _ => Err(Error::TypeMismatch {
            expected: "string".to_string(),
            found: format!("{:?}", v),
            context: "string conversion".to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_builtins() {
        let env = register_builtins(&Env::new());
        assert!(env.lookup("cetak").is_some());
        assert!(env.lookup("print").is_some());
        assert!(env.lookup("cetakln").is_some());
        assert!(env.lookup("println").is_some());
        assert!(env.lookup("panjang").is_some());
        assert!(env.lookup("length").is_some());
        assert!(env.lookup("ke_teks").is_some());
        assert!(env.lookup("ke_nombor").is_some());
    }

    #[test]
    fn test_builtin_ke_teks() {
        let result = apply_builtin("ke_teks", Value::Int(42)).unwrap();
        assert_eq!(result, Value::String("42".to_string()));
    }

    #[test]
    fn test_builtin_ke_nombor() {
        let result = apply_builtin("ke_nombor", Value::String("123".to_string())).unwrap();
        assert_eq!(result, Value::Int(123));
    }

    #[test]
    fn test_builtin_ke_nombor_invalid() {
        let result = apply_builtin("ke_nombor", Value::String("abc".to_string()));
        assert!(result.is_err());
    }

    #[test]
    fn test_builtin_panjang() {
        let result = apply_builtin("panjang", Value::String("hello".to_string())).unwrap();
        assert_eq!(result, Value::Int(5));
    }

    #[test]
    fn test_builtin_gabung_teks() {
        let arg = Value::Pair(
            Box::new(Value::String("hello".to_string())),
            Box::new(Value::String(" world".to_string())),
        );
        let result = apply_builtin("gabung_teks", arg).unwrap();
        assert_eq!(result, Value::String("hello world".to_string()));
    }

    #[test]
    fn test_builtin_cetakln() {
        // Just verify it doesn't error
        let result = apply_builtin("cetakln", Value::Int(42)).unwrap();
        assert_eq!(result, Value::Unit);
    }
}
