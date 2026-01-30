//! Test/assertion builtins (ujian)

use crate::value::Value;
use crate::{Error, Result};

pub static BUILTINS: &[(&str, &str, &str)] = &[
    ("tegaskan", "assert", "tegaskan"),
    ("tegaskan_sama", "assert_eq", "tegaskan_sama"),
    ("tegaskan_beza", "assert_ne", "tegaskan_beza"),
    ("tegaskan_betul", "assert_true", "tegaskan_betul"),
    ("tegaskan_salah", "assert_false", "tegaskan_salah"),
];

pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "tegaskan" | "tegaskan_betul" => {
            match arg {
                Value::Bool(true) => Ok(Some(Value::Unit)),
                Value::Bool(false) => Err(Error::InvalidOperation("assertion failed".to_string())),
                _ => Err(Error::TypeMismatch {
                    expected: "bool".to_string(),
                    found: format!("{:?}", arg),
                    context: name.to_string(),
                }),
            }
        }
        "tegaskan_salah" => {
            match arg {
                Value::Bool(false) => Ok(Some(Value::Unit)),
                Value::Bool(true) => Err(Error::InvalidOperation("assert_false failed: got true".to_string())),
                _ => Err(Error::TypeMismatch {
                    expected: "bool".to_string(),
                    found: format!("{:?}", arg),
                    context: name.to_string(),
                }),
            }
        }
        "tegaskan_sama" => {
            match arg {
                Value::Pair(a, b) => {
                    if a == b {
                        Ok(Some(Value::Unit))
                    } else {
                        Err(Error::InvalidOperation(format!(
                            "assert_eq failed: {:?} != {:?}", a, b
                        )))
                    }
                }
                _ => Err(Error::TypeMismatch {
                    expected: "(value, value)".to_string(),
                    found: format!("{:?}", arg),
                    context: name.to_string(),
                }),
            }
        }
        "tegaskan_beza" => {
            match arg {
                Value::Pair(a, b) => {
                    if a != b {
                        Ok(Some(Value::Unit))
                    } else {
                        Err(Error::InvalidOperation(format!(
                            "assert_ne failed: {:?} == {:?}", a, b
                        )))
                    }
                }
                _ => Err(Error::TypeMismatch {
                    expected: "(value, value)".to_string(),
                    found: format!("{:?}", arg),
                    context: name.to_string(),
                }),
            }
        }
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tegaskan() {
        assert_eq!(apply("tegaskan", &Value::Bool(true)).unwrap(), Some(Value::Unit));
        assert!(apply("tegaskan", &Value::Bool(false)).is_err());
    }

    #[test]
    fn test_tegaskan_betul() {
        assert_eq!(apply("tegaskan_betul", &Value::Bool(true)).unwrap(), Some(Value::Unit));
        assert!(apply("tegaskan_betul", &Value::Bool(false)).is_err());
    }

    #[test]
    fn test_tegaskan_salah() {
        assert_eq!(apply("tegaskan_salah", &Value::Bool(false)).unwrap(), Some(Value::Unit));
        assert!(apply("tegaskan_salah", &Value::Bool(true)).is_err());
    }

    #[test]
    fn test_tegaskan_sama() {
        let arg = Value::Pair(Box::new(Value::Int(42)), Box::new(Value::Int(42)));
        assert_eq!(apply("tegaskan_sama", &arg).unwrap(), Some(Value::Unit));
        let arg2 = Value::Pair(Box::new(Value::Int(1)), Box::new(Value::Int(2)));
        assert!(apply("tegaskan_sama", &arg2).is_err());
    }

    #[test]
    fn test_tegaskan_beza() {
        let arg = Value::Pair(Box::new(Value::Int(1)), Box::new(Value::Int(2)));
        assert_eq!(apply("tegaskan_beza", &arg).unwrap(), Some(Value::Unit));
        let arg2 = Value::Pair(Box::new(Value::Int(1)), Box::new(Value::Int(1)));
        assert!(apply("tegaskan_beza", &arg2).is_err());
    }
}
