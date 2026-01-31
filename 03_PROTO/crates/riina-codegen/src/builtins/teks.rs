//! String builtins (teks)

use crate::value::Value;
use crate::{Error, Result};

/// (BM name, EN alias, canonical name)
pub static BUILTINS: &[(&str, &str, &str)] = &[
    ("teks_belah", "str_split", "teks_belah"),
    ("teks_cantum", "str_join", "teks_cantum"),
    ("teks_potong", "str_trim", "teks_potong"),
    ("teks_mengandungi", "str_contains", "teks_mengandungi"),
    ("teks_ganti", "str_replace", "teks_ganti"),
    ("teks_mula_dengan", "str_starts_with", "teks_mula_dengan"),
    ("teks_akhir_dengan", "str_ends_with", "teks_akhir_dengan"),
    ("teks_huruf_besar", "str_to_upper", "teks_huruf_besar"),
    ("teks_huruf_kecil", "str_to_lower", "teks_huruf_kecil"),
    ("teks_aksara_di", "str_char_at", "teks_aksara_di"),
    ("teks_sub", "str_substring", "teks_sub"),
    ("teks_indeks", "str_index_of", "teks_indeks"),
    ("teks_ulang", "str_repeat", "teks_ulang"),
    ("teks_pad_kiri", "str_pad_left", "teks_pad_kiri"),
    ("teks_pad_kanan", "str_pad_right", "teks_pad_kanan"),
    ("teks_baris", "str_lines", "teks_baris"),
];

/// Apply a string builtin. Returns Ok(None) if name doesn't match.
pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "teks_belah" => {
            // (String, String) -> List
            let (s, delim) = extract_pair_strings(arg, "teks_belah")?;
            let parts: Vec<Value> = s.split(&delim).map(|p| Value::String(p.to_string())).collect();
            Ok(Some(Value::List(parts)))
        }
        "teks_cantum" => {
            // (String, List) -> String
            match arg {
                Value::Pair(sep, list) => {
                    let sep_s = extract_string(sep, "teks_cantum")?;
                    let items = extract_list(list, "teks_cantum")?;
                    let parts: Result<Vec<String>> = items.iter().map(|v| extract_string(v, "teks_cantum")).collect();
                    Ok(Some(Value::String(parts?.join(&sep_s))))
                }
                _ => Err(type_err("(string, list)", arg, "teks_cantum")),
            }
        }
        "teks_potong" => {
            let s = extract_string(arg, "teks_potong")?;
            Ok(Some(Value::String(s.trim().to_string())))
        }
        "teks_mengandungi" => {
            let (s, sub) = extract_pair_strings(arg, "teks_mengandungi")?;
            Ok(Some(Value::Bool(s.contains(&sub))))
        }
        "teks_ganti" => {
            // (String, (String, String)) -> String
            match arg {
                Value::Pair(s, pair) => {
                    let s_str = extract_string(s, "teks_ganti")?;
                    let (from, to) = extract_pair_strings(pair, "teks_ganti")?;
                    Ok(Some(Value::String(s_str.replace(&from, &to))))
                }
                _ => Err(type_err("(string, (string, string))", arg, "teks_ganti")),
            }
        }
        "teks_mula_dengan" => {
            let (s, prefix) = extract_pair_strings(arg, "teks_mula_dengan")?;
            Ok(Some(Value::Bool(s.starts_with(&prefix))))
        }
        "teks_akhir_dengan" => {
            let (s, suffix) = extract_pair_strings(arg, "teks_akhir_dengan")?;
            Ok(Some(Value::Bool(s.ends_with(&suffix))))
        }
        "teks_huruf_besar" => {
            let s = extract_string(arg, "teks_huruf_besar")?;
            Ok(Some(Value::String(s.to_uppercase())))
        }
        "teks_huruf_kecil" => {
            let s = extract_string(arg, "teks_huruf_kecil")?;
            Ok(Some(Value::String(s.to_lowercase())))
        }
        "teks_aksara_di" => {
            // (String, Int) -> String
            match arg {
                Value::Pair(s, idx) => {
                    let s_str = extract_string(s, "teks_aksara_di")?;
                    let i = extract_int(idx, "teks_aksara_di")?;
                    match s_str.chars().nth(i as usize) {
                        Some(c) => Ok(Some(Value::String(c.to_string()))),
                        None => Err(Error::InvalidOperation(format!(
                            "index {} out of bounds for string of length {}",
                            i,
                            s_str.chars().count()
                        ))),
                    }
                }
                _ => Err(type_err("(string, int)", arg, "teks_aksara_di")),
            }
        }
        "teks_sub" => {
            // (String, (Int, Int)) -> String
            match arg {
                Value::Pair(s, range) => {
                    let s_str = extract_string(s, "teks_sub")?;
                    match range.as_ref() {
                        Value::Pair(start, end) => {
                            let st = extract_int(start, "teks_sub")? as usize;
                            let en = extract_int(end, "teks_sub")? as usize;
                            let result: String = s_str.chars().skip(st).take(en.saturating_sub(st)).collect();
                            Ok(Some(Value::String(result)))
                        }
                        _ => Err(type_err("(string, (int, int))", arg, "teks_sub")),
                    }
                }
                _ => Err(type_err("(string, (int, int))", arg, "teks_sub")),
            }
        }
        "teks_indeks" => {
            let (s, sub) = extract_pair_strings(arg, "teks_indeks")?;
            let idx = s.find(&sub).map(|i| i as u64).unwrap_or(u64::MAX);
            Ok(Some(Value::Int(idx)))
        }
        "teks_ulang" => {
            // (String, Int) -> String
            match arg {
                Value::Pair(s, n) => {
                    let text = extract_string(s, "teks_ulang")?;
                    let count = extract_int(n, "teks_ulang")? as usize;
                    Ok(Some(Value::String(text.repeat(count))))
                }
                _ => Err(type_err("(string, int)", arg, "teks_ulang")),
            }
        }
        "teks_pad_kiri" => {
            // (String, Int, String) -> String
            // Encoded as (string, (int, string))
            match arg {
                Value::Pair(s, params) => {
                    let text = extract_string(s, "teks_pad_kiri")?;
                    match params.as_ref() {
                        Value::Pair(width, pad) => {
                            let w = extract_int(width, "teks_pad_kiri")? as usize;
                            let p = extract_string(pad, "teks_pad_kiri")?;
                            let pad_char = p.chars().next().unwrap_or(' ');
                            let current = text.chars().count();
                            if current >= w {
                                Ok(Some(Value::String(text)))
                            } else {
                                let padding: String = std::iter::repeat(pad_char).take(w - current).collect();
                                Ok(Some(Value::String(format!("{}{}", padding, text))))
                            }
                        }
                        _ => Err(type_err("(string, (int, string))", arg, "teks_pad_kiri")),
                    }
                }
                _ => Err(type_err("(string, (int, string))", arg, "teks_pad_kiri")),
            }
        }
        "teks_pad_kanan" => {
            // (String, Int, String) -> String
            match arg {
                Value::Pair(s, params) => {
                    let text = extract_string(s, "teks_pad_kanan")?;
                    match params.as_ref() {
                        Value::Pair(width, pad) => {
                            let w = extract_int(width, "teks_pad_kanan")? as usize;
                            let p = extract_string(pad, "teks_pad_kanan")?;
                            let pad_char = p.chars().next().unwrap_or(' ');
                            let current = text.chars().count();
                            if current >= w {
                                Ok(Some(Value::String(text)))
                            } else {
                                let padding: String = std::iter::repeat(pad_char).take(w - current).collect();
                                Ok(Some(Value::String(format!("{}{}", text, padding))))
                            }
                        }
                        _ => Err(type_err("(string, (int, string))", arg, "teks_pad_kanan")),
                    }
                }
                _ => Err(type_err("(string, (int, string))", arg, "teks_pad_kanan")),
            }
        }
        "teks_baris" => {
            // String -> List<String>
            let s = extract_string(arg, "teks_baris")?;
            let lines: Vec<Value> = s.lines().map(|l| Value::String(l.to_string())).collect();
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

fn extract_int(v: &Value, ctx: &str) -> Result<u64> {
    match v {
        Value::Int(n) => Ok(*n),
        _ => Err(type_err("int", v, ctx)),
    }
}

fn extract_list<'a>(v: &'a Value, ctx: &str) -> Result<&'a Vec<Value>> {
    match v {
        Value::List(items) => Ok(items),
        _ => Err(type_err("list", v, ctx)),
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

    fn pair_s(a: &str, b: &str) -> Value {
        Value::Pair(
            Box::new(Value::String(a.to_string())),
            Box::new(Value::String(b.to_string())),
        )
    }

    #[test]
    fn test_teks_belah() {
        let result = apply("teks_belah", &pair_s("a,b,c", ",")).unwrap().unwrap();
        assert_eq!(result, Value::List(vec![
            Value::String("a".to_string()),
            Value::String("b".to_string()),
            Value::String("c".to_string()),
        ]));
    }

    #[test]
    fn test_teks_cantum() {
        let list = Value::List(vec![
            Value::String("a".to_string()),
            Value::String("b".to_string()),
        ]);
        let arg = Value::Pair(Box::new(Value::String(",".to_string())), Box::new(list));
        let result = apply("teks_cantum", &arg).unwrap().unwrap();
        assert_eq!(result, Value::String("a,b".to_string()));
    }

    #[test]
    fn test_teks_potong() {
        let result = apply("teks_potong", &Value::String("  hi  ".to_string())).unwrap().unwrap();
        assert_eq!(result, Value::String("hi".to_string()));
    }

    #[test]
    fn test_teks_mengandungi() {
        assert_eq!(
            apply("teks_mengandungi", &pair_s("hello world", "world")).unwrap(),
            Some(Value::Bool(true))
        );
        assert_eq!(
            apply("teks_mengandungi", &pair_s("hello", "xyz")).unwrap(),
            Some(Value::Bool(false))
        );
    }

    #[test]
    fn test_teks_ganti() {
        let arg = Value::Pair(
            Box::new(Value::String("hello world".to_string())),
            Box::new(pair_s("world", "RIINA")),
        );
        assert_eq!(
            apply("teks_ganti", &arg).unwrap(),
            Some(Value::String("hello RIINA".to_string()))
        );
    }

    #[test]
    fn test_teks_mula_akhir_dengan() {
        assert_eq!(apply("teks_mula_dengan", &pair_s("hello", "he")).unwrap(), Some(Value::Bool(true)));
        assert_eq!(apply("teks_akhir_dengan", &pair_s("hello", "lo")).unwrap(), Some(Value::Bool(true)));
    }

    #[test]
    fn test_teks_huruf() {
        assert_eq!(
            apply("teks_huruf_besar", &Value::String("hello".to_string())).unwrap(),
            Some(Value::String("HELLO".to_string()))
        );
        assert_eq!(
            apply("teks_huruf_kecil", &Value::String("HELLO".to_string())).unwrap(),
            Some(Value::String("hello".to_string()))
        );
    }

    #[test]
    fn test_teks_aksara_di() {
        let arg = Value::Pair(
            Box::new(Value::String("hello".to_string())),
            Box::new(Value::Int(1)),
        );
        assert_eq!(apply("teks_aksara_di", &arg).unwrap(), Some(Value::String("e".to_string())));
    }

    #[test]
    fn test_teks_sub() {
        let arg = Value::Pair(
            Box::new(Value::String("hello world".to_string())),
            Box::new(Value::Pair(Box::new(Value::Int(0)), Box::new(Value::Int(5)))),
        );
        assert_eq!(apply("teks_sub", &arg).unwrap(), Some(Value::String("hello".to_string())));
    }

    #[test]
    fn test_teks_indeks() {
        assert_eq!(apply("teks_indeks", &pair_s("hello", "ll")).unwrap(), Some(Value::Int(2)));
        assert_eq!(apply("teks_indeks", &pair_s("hello", "xyz")).unwrap(), Some(Value::Int(u64::MAX)));
    }

    #[test]
    fn test_teks_ulang() {
        let arg = Value::Pair(
            Box::new(Value::String("ab".to_string())),
            Box::new(Value::Int(3)),
        );
        assert_eq!(apply("teks_ulang", &arg).unwrap(), Some(Value::String("ababab".to_string())));
    }

    #[test]
    fn test_teks_pad_kiri() {
        let arg = Value::Pair(
            Box::new(Value::String("42".to_string())),
            Box::new(Value::Pair(Box::new(Value::Int(5)), Box::new(Value::String("0".to_string())))),
        );
        assert_eq!(apply("teks_pad_kiri", &arg).unwrap(), Some(Value::String("00042".to_string())));
    }

    #[test]
    fn test_teks_pad_kanan() {
        let arg = Value::Pair(
            Box::new(Value::String("hi".to_string())),
            Box::new(Value::Pair(Box::new(Value::Int(5)), Box::new(Value::String(".".to_string())))),
        );
        assert_eq!(apply("teks_pad_kanan", &arg).unwrap(), Some(Value::String("hi...".to_string())));
    }

    #[test]
    fn test_teks_baris() {
        let result = apply("teks_baris", &Value::String("a\nb\nc".to_string())).unwrap().unwrap();
        assert_eq!(result, Value::List(vec![
            Value::String("a".to_string()),
            Value::String("b".to_string()),
            Value::String("c".to_string()),
        ]));
    }
}
