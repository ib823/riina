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
}
