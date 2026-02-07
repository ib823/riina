// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Set builtins (uses List internally with unique elements)

use crate::value::Value;
use crate::{Error, Result};

pub static BUILTINS: &[(&str, &str, &str)] = &[
    ("set_baru", "set_new", "set_baru"),
    ("set_letak", "set_insert", "set_letak"),
    ("set_buang", "set_remove", "set_buang"),
    ("set_mengandungi", "set_contains", "set_mengandungi"),
    ("set_kesatuan", "set_union", "set_kesatuan"),
    ("set_persilangan", "set_intersect", "set_persilangan"),
    ("set_panjang", "set_len", "set_panjang"),
];

pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "set_baru" => Ok(Some(Value::List(Vec::new()))),
        "set_letak" => {
            match arg {
                Value::Pair(list, val) => {
                    let items = extract_list(list, "set_letak")?;
                    let mut result = items.clone();
                    if !result.contains(val) {
                        result.push(val.as_ref().clone());
                    }
                    Ok(Some(Value::List(result)))
                }
                _ => Err(type_err("(list, value)", arg, "set_letak")),
            }
        }
        "set_buang" => {
            match arg {
                Value::Pair(list, val) => {
                    let items = extract_list(list, "set_buang")?;
                    let result: Vec<Value> = items.iter().filter(|v| *v != val.as_ref()).cloned().collect();
                    Ok(Some(Value::List(result)))
                }
                _ => Err(type_err("(list, value)", arg, "set_buang")),
            }
        }
        "set_mengandungi" => {
            match arg {
                Value::Pair(list, val) => {
                    let items = extract_list(list, "set_mengandungi")?;
                    Ok(Some(Value::Bool(items.contains(val))))
                }
                _ => Err(type_err("(list, value)", arg, "set_mengandungi")),
            }
        }
        "set_kesatuan" => {
            match arg {
                Value::Pair(a, b) => {
                    let items_a = extract_list(a, "set_kesatuan")?;
                    let items_b = extract_list(b, "set_kesatuan")?;
                    let mut result = items_a.clone();
                    for item in items_b {
                        if !result.contains(item) {
                            result.push(item.clone());
                        }
                    }
                    Ok(Some(Value::List(result)))
                }
                _ => Err(type_err("(list, list)", arg, "set_kesatuan")),
            }
        }
        "set_persilangan" => {
            match arg {
                Value::Pair(a, b) => {
                    let items_a = extract_list(a, "set_persilangan")?;
                    let items_b = extract_list(b, "set_persilangan")?;
                    let result: Vec<Value> = items_a.iter().filter(|v| items_b.contains(v)).cloned().collect();
                    Ok(Some(Value::List(result)))
                }
                _ => Err(type_err("(list, list)", arg, "set_persilangan")),
            }
        }
        "set_panjang" => {
            let items = extract_list(arg, "set_panjang")?;
            Ok(Some(Value::Int(items.len() as u64)))
        }
        _ => Ok(None),
    }
}

fn extract_list<'a>(v: &'a Value, ctx: &str) -> Result<&'a Vec<Value>> {
    match v {
        Value::List(items) => Ok(items),
        _ => Err(type_err("list", v, ctx)),
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
    fn test_set_baru() {
        assert_eq!(apply("set_baru", &Value::Unit).unwrap(), Some(Value::List(vec![])));
    }

    #[test]
    fn test_set_letak_unique() {
        let set = Value::List(vec![Value::Int(1)]);
        // Insert existing
        let arg = Value::Pair(Box::new(set.clone()), Box::new(Value::Int(1)));
        let result = apply("set_letak", &arg).unwrap().unwrap();
        assert_eq!(result, Value::List(vec![Value::Int(1)]));
        // Insert new
        let arg2 = Value::Pair(Box::new(set), Box::new(Value::Int(2)));
        let result2 = apply("set_letak", &arg2).unwrap().unwrap();
        assert_eq!(result2, Value::List(vec![Value::Int(1), Value::Int(2)]));
    }

    #[test]
    fn test_set_buang() {
        let set = Value::List(vec![Value::Int(1), Value::Int(2)]);
        let arg = Value::Pair(Box::new(set), Box::new(Value::Int(1)));
        assert_eq!(apply("set_buang", &arg).unwrap(), Some(Value::List(vec![Value::Int(2)])));
    }

    #[test]
    fn test_set_kesatuan() {
        let a = Value::List(vec![Value::Int(1), Value::Int(2)]);
        let b = Value::List(vec![Value::Int(2), Value::Int(3)]);
        let arg = Value::Pair(Box::new(a), Box::new(b));
        assert_eq!(
            apply("set_kesatuan", &arg).unwrap(),
            Some(Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]))
        );
    }

    #[test]
    fn test_set_persilangan() {
        let a = Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)]);
        let b = Value::List(vec![Value::Int(2), Value::Int(3), Value::Int(4)]);
        let arg = Value::Pair(Box::new(a), Box::new(b));
        assert_eq!(
            apply("set_persilangan", &arg).unwrap(),
            Some(Value::List(vec![Value::Int(2), Value::Int(3)]))
        );
    }
}
