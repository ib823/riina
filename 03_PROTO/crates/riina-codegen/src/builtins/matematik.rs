// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Math builtins (matematik)

use crate::value::Value;
use crate::{Error, Result};

pub static BUILTINS: &[(&str, &str, &str)] = &[
    ("mutlak", "abs", "mutlak"),
    ("minimum", "min", "minimum"),
    ("maksimum", "max", "maksimum"),
    ("kuasa", "pow", "kuasa"),
    ("punca", "sqrt", "punca"),
    ("gcd", "gcd", "gcd"),
    ("lcm", "lcm", "lcm"),
    ("baki", "rem", "baki"),
    ("log2", "log2", "log2"),
    ("rawak", "random", "rawak"),
];

pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "mutlak" => {
            // u64 is always non-negative, so abs is identity
            let n = extract_int(arg, "mutlak")?;
            Ok(Some(Value::Int(n)))
        }
        "minimum" => {
            let (a, b) = extract_pair_ints(arg, "minimum")?;
            Ok(Some(Value::Int(a.min(b))))
        }
        "maksimum" => {
            let (a, b) = extract_pair_ints(arg, "maksimum")?;
            Ok(Some(Value::Int(a.max(b))))
        }
        "kuasa" => {
            let (base, exp) = extract_pair_ints(arg, "kuasa")?;
            Ok(Some(Value::Int(base.wrapping_pow(exp as u32))))
        }
        "punca" => {
            let n = extract_int(arg, "punca")?;
            Ok(Some(Value::Int((n as f64).sqrt() as u64)))
        }
        "gcd" => {
            let (a, b) = extract_pair_ints(arg, "gcd")?;
            Ok(Some(Value::Int(gcd_impl(a, b))))
        }
        "lcm" => {
            let (a, b) = extract_pair_ints(arg, "lcm")?;
            if a == 0 && b == 0 {
                Ok(Some(Value::Int(0)))
            } else {
                Ok(Some(Value::Int(a / gcd_impl(a, b) * b)))
            }
        }
        "baki" => {
            let (a, b) = extract_pair_ints(arg, "baki")?;
            if b == 0 {
                return Err(Error::InvalidOperation("modulo by zero".to_string()));
            }
            Ok(Some(Value::Int(a % b)))
        }
        "log2" => {
            let n = extract_int(arg, "log2")?;
            if n == 0 {
                return Err(Error::InvalidOperation("log2(0) is undefined".to_string()));
            }
            Ok(Some(Value::Int(63 - n.leading_zeros() as u64)))
        }
        "rawak" => {
            // Int -> Int (0..n exclusive)
            let n = extract_int(arg, "rawak")?;
            if n == 0 {
                return Err(Error::InvalidOperation("random(0) is undefined".to_string()));
            }
            // Simple PRNG using thread-local state
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            use std::time::SystemTime;
            let seed = SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos();
            let mut h = DefaultHasher::new();
            seed.hash(&mut h);
            let r = h.finish() % n;
            Ok(Some(Value::Int(r)))
        }
        _ => Ok(None),
    }
}

fn gcd_impl(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn extract_int(v: &Value, ctx: &str) -> Result<u64> {
    match v {
        Value::Int(n) => Ok(*n),
        _ => Err(Error::TypeMismatch {
            expected: "int".to_string(),
            found: format!("{:?}", v),
            context: ctx.to_string(),
        }),
    }
}

fn extract_pair_ints(v: &Value, ctx: &str) -> Result<(u64, u64)> {
    match v {
        Value::Pair(a, b) => {
            let x = extract_int(a, ctx)?;
            let y = extract_int(b, ctx)?;
            Ok((x, y))
        }
        _ => Err(Error::TypeMismatch {
            expected: "(int, int)".to_string(),
            found: format!("{:?}", v),
            context: ctx.to_string(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pair_i(a: u64, b: u64) -> Value {
        Value::Pair(Box::new(Value::Int(a)), Box::new(Value::Int(b)))
    }

    #[test]
    fn test_mutlak() {
        assert_eq!(apply("mutlak", &Value::Int(42)).unwrap(), Some(Value::Int(42)));
    }

    #[test]
    fn test_minimum_maksimum() {
        assert_eq!(apply("minimum", &pair_i(3, 7)).unwrap(), Some(Value::Int(3)));
        assert_eq!(apply("maksimum", &pair_i(3, 7)).unwrap(), Some(Value::Int(7)));
    }

    #[test]
    fn test_kuasa() {
        assert_eq!(apply("kuasa", &pair_i(2, 10)).unwrap(), Some(Value::Int(1024)));
    }

    #[test]
    fn test_punca() {
        assert_eq!(apply("punca", &Value::Int(16)).unwrap(), Some(Value::Int(4)));
        assert_eq!(apply("punca", &Value::Int(15)).unwrap(), Some(Value::Int(3)));
    }

    #[test]
    fn test_gcd() {
        assert_eq!(apply("gcd", &pair_i(12, 8)).unwrap(), Some(Value::Int(4)));
        assert_eq!(apply("gcd", &pair_i(7, 13)).unwrap(), Some(Value::Int(1)));
    }

    #[test]
    fn test_lcm() {
        assert_eq!(apply("lcm", &pair_i(4, 6)).unwrap(), Some(Value::Int(12)));
        assert_eq!(apply("lcm", &pair_i(0, 0)).unwrap(), Some(Value::Int(0)));
    }

    #[test]
    fn test_baki() {
        assert_eq!(apply("baki", &pair_i(10, 3)).unwrap(), Some(Value::Int(1)));
        assert_eq!(apply("baki", &pair_i(9, 3)).unwrap(), Some(Value::Int(0)));
        assert!(apply("baki", &pair_i(5, 0)).is_err());
    }

    #[test]
    fn test_log2() {
        assert_eq!(apply("log2", &Value::Int(1)).unwrap(), Some(Value::Int(0)));
        assert_eq!(apply("log2", &Value::Int(8)).unwrap(), Some(Value::Int(3)));
        assert_eq!(apply("log2", &Value::Int(1024)).unwrap(), Some(Value::Int(10)));
        assert!(apply("log2", &Value::Int(0)).is_err());
    }

    #[test]
    fn test_rawak() {
        let result = apply("rawak", &Value::Int(100)).unwrap().unwrap();
        match result {
            Value::Int(n) => assert!(n < 100),
            _ => panic!("expected int"),
        }
    }
}
