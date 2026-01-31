//! Built-in Functions
//!
//! Provides standard built-in functions for RIINA programs.
//! These are Rust-only extensions (not in Coq).
//!
//! Bilingual names: Bahasa Melayu and English.

pub(crate) mod teks;
pub(crate) mod senarai;
pub(crate) mod peta;
pub(crate) mod set;
pub(crate) mod matematik;
pub(crate) mod penukaran;
pub(crate) mod ujian;
pub(crate) mod masa;

use crate::value::{Env, Value};
use crate::{Error, Result};

/// Register all built-in functions into the given environment.
#[must_use]
pub fn register_builtins(env: &Env) -> Env {
    let mut e = env.clone();

    // I/O (TODO: effect gate)
    e = e.extend("cetak".to_string(), Value::Builtin("cetak".to_string()));
    e = e.extend("print".to_string(), Value::Builtin("cetak".to_string()));
    e = e.extend("cetakln".to_string(), Value::Builtin("cetakln".to_string()));
    e = e.extend("println".to_string(), Value::Builtin("cetakln".to_string()));

    // String operations (existing)
    e = e.extend("gabung_teks".to_string(), Value::Builtin("gabung_teks".to_string()));
    e = e.extend("concat".to_string(), Value::Builtin("gabung_teks".to_string()));
    e = e.extend("panjang".to_string(), Value::Builtin("panjang".to_string()));
    e = e.extend("length".to_string(), Value::Builtin("panjang".to_string()));

    // Conversion (existing, moved to penukaran)
    e = e.extend("ke_teks".to_string(), Value::Builtin("ke_teks".to_string()));
    e = e.extend("to_string".to_string(), Value::Builtin("ke_teks".to_string()));
    e = e.extend("ke_nombor".to_string(), Value::Builtin("ke_nombor".to_string()));
    e = e.extend("parse_int".to_string(), Value::Builtin("ke_nombor".to_string()));

    // New conversion builtins
    e = e.extend("ke_bool".to_string(), Value::Builtin("ke_bool".to_string()));
    e = e.extend("to_bool".to_string(), Value::Builtin("ke_bool".to_string()));
    e = e.extend("bool_ke_nombor".to_string(), Value::Builtin("bool_ke_nombor".to_string()));
    e = e.extend("bool_to_int".to_string(), Value::Builtin("bool_ke_nombor".to_string()));
    e = e.extend("nombor_ke_teks".to_string(), Value::Builtin("nombor_ke_teks".to_string()));
    e = e.extend("int_to_string".to_string(), Value::Builtin("nombor_ke_teks".to_string()));

    // String builtins (teks)
    for (bm, en, canonical) in teks::BUILTINS {
        e = e.extend(bm.to_string(), Value::Builtin(canonical.to_string()));
        e = e.extend(en.to_string(), Value::Builtin(canonical.to_string()));
    }

    // List builtins (senarai)
    for (bm, en, canonical) in senarai::BUILTINS {
        e = e.extend(bm.to_string(), Value::Builtin(canonical.to_string()));
        e = e.extend(en.to_string(), Value::Builtin(canonical.to_string()));
    }

    // Map builtins (peta)
    for (bm, en, canonical) in peta::BUILTINS {
        e = e.extend(bm.to_string(), Value::Builtin(canonical.to_string()));
        e = e.extend(en.to_string(), Value::Builtin(canonical.to_string()));
    }

    // Set builtins
    for (bm, en, canonical) in set::BUILTINS {
        e = e.extend(bm.to_string(), Value::Builtin(canonical.to_string()));
        e = e.extend(en.to_string(), Value::Builtin(canonical.to_string()));
    }

    // Math builtins (matematik)
    for (bm, en, canonical) in matematik::BUILTINS {
        e = e.extend(bm.to_string(), Value::Builtin(canonical.to_string()));
        e = e.extend(en.to_string(), Value::Builtin(canonical.to_string()));
    }

    // Test builtins (ujian)
    for (bm, en, canonical) in ujian::BUILTINS {
        e = e.extend(bm.to_string(), Value::Builtin(canonical.to_string()));
        e = e.extend(en.to_string(), Value::Builtin(canonical.to_string()));
    }

    // Time builtins (masa)
    for (bm, en, canonical) in masa::BUILTINS {
        e = e.extend(bm.to_string(), Value::Builtin(canonical.to_string()));
        e = e.extend(en.to_string(), Value::Builtin(canonical.to_string()));
    }

    e
}

/// Apply a built-in function to an argument.
pub fn apply_builtin(name: &str, arg: Value) -> Result<Value> {
    // I/O
    match name {
        "cetak" => {
            print!("{}", format_value(&arg));
            return Ok(Value::Unit);
        }
        "cetakln" => {
            println!("{}", format_value(&arg));
            return Ok(Value::Unit);
        }
        "gabung_teks" => {
            return match arg {
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
            };
        }
        "panjang" => {
            return match &arg {
                Value::String(s) => Ok(Value::Int(s.len() as u64)),
                _ => Err(Error::TypeMismatch {
                    expected: "string".to_string(),
                    found: format!("{:?}", arg),
                    context: "panjang/length".to_string(),
                }),
            };
        }
        _ => {}
    }

    // Conversion
    if let Some(result) = penukaran::apply(name, &arg)? {
        return Ok(result);
    }

    // String
    if let Some(result) = teks::apply(name, &arg)? {
        return Ok(result);
    }

    // List
    if let Some(result) = senarai::apply(name, &arg)? {
        return Ok(result);
    }

    // Map
    if let Some(result) = peta::apply(name, &arg)? {
        return Ok(result);
    }

    // Set
    if let Some(result) = set::apply(name, &arg)? {
        return Ok(result);
    }

    // Math
    if let Some(result) = matematik::apply(name, &arg)? {
        return Ok(result);
    }

    // Test
    if let Some(result) = ujian::apply(name, &arg)? {
        return Ok(result);
    }

    // Time
    if let Some(result) = masa::apply(name, &arg)? {
        return Ok(result);
    }

    Err(Error::InvalidOperation(format!("unknown builtin: {name}")))
}

/// Format a value for display (user-facing, no debug wrapping).
pub fn format_value(v: &Value) -> String {
    match v {
        Value::Unit => "()".to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Int(n) => n.to_string(),
        Value::String(s) => s.clone(),
        Value::Pair(a, b) => format!("({}, {})", format_value(a), format_value(b)),
        Value::List(items) => {
            let parts: Vec<String> = items.iter().map(format_value).collect();
            format!("[{}]", parts.join(", "))
        }
        Value::Map(entries) => {
            let parts: Vec<String> = entries
                .iter()
                .map(|(k, v)| format!("\"{}\": {}", k, format_value(v)))
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
        other => format!("{other}"),
    }
}

/// Extract string from value.
pub(crate) fn value_to_string(v: &Value) -> Result<String> {
    match v {
        Value::String(s) => Ok(s.clone()),
        _ => Err(Error::TypeMismatch {
            expected: "string".to_string(),
            found: format!("{:?}", v),
            context: "string conversion".to_string(),
        }),
    }
}

/// Check if the given builtin name is a higher-order builtin
/// that must be handled in the interpreter (needs closure evaluation).
pub fn is_higher_order_builtin(name: &str) -> bool {
    matches!(
        name,
        "senarai_peta" | "list_map" | "senarai_tapis" | "list_filter" | "senarai_lipat" | "list_fold"
    )
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
        // New builtins
        assert!(env.lookup("teks_belah").is_some());
        assert!(env.lookup("str_split").is_some());
        assert!(env.lookup("senarai_baru").is_some());
        assert!(env.lookup("list_new").is_some());
        assert!(env.lookup("peta_baru").is_some());
        assert!(env.lookup("map_new").is_some());
        assert!(env.lookup("mutlak").is_some());
        assert!(env.lookup("abs").is_some());
        assert!(env.lookup("tegaskan").is_some());
        assert!(env.lookup("assert").is_some());
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
        let result = apply_builtin("cetakln", Value::Int(42)).unwrap();
        assert_eq!(result, Value::Unit);
    }

    #[test]
    fn test_format_value_list() {
        let v = Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        assert_eq!(format_value(&v), "[1, 2, 3]");
    }

    #[test]
    fn test_format_value_map() {
        let mut m = std::collections::BTreeMap::new();
        m.insert("a".to_string(), Value::Int(1));
        let v = Value::Map(m);
        assert_eq!(format_value(&v), "{\"a\": 1}");
    }
}
