// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! JSON builtins (json)
//!
//! Hand-written JSON parser/formatter. No third-party dependencies.
//! JSON maps to RIINA Value types: Object→Map, Array→List, String/Int/Bool directly.

use crate::value::Value;
use crate::{Error, Result};
use std::collections::BTreeMap;

/// (BM name, EN alias, canonical name)
pub static BUILTINS: &[(&str, &str, &str)] = &[
    ("json_urai", "json_parse", "json_urai"),
    ("json_ke_teks", "json_stringify", "json_ke_teks"),
    ("json_dapat", "json_get", "json_dapat"),
    ("json_letak", "json_set", "json_letak"),
    ("json_ada", "json_has", "json_ada"),
];

pub fn apply(name: &str, arg: &Value) -> Result<Option<Value>> {
    match name {
        "json_urai" => {
            // Teks -> Value
            let s = extract_string(arg, "json_urai")?;
            let val = parse_json(&s)?;
            Ok(Some(val))
        }
        "json_ke_teks" => {
            // Value -> Teks
            let s = stringify_value(arg);
            Ok(Some(Value::String(s)))
        }
        "json_dapat" => {
            // (Value, Teks) -> Value
            match arg {
                Value::Pair(obj, key) => {
                    let k = extract_string(key, "json_dapat")?;
                    match obj.as_ref() {
                        Value::Map(m) => m.get(&k).cloned().map(Some).ok_or_else(|| {
                            Error::InvalidOperation(format!("json_dapat: key '{}' not found", k))
                        }),
                        _ => Err(type_err("map", obj, "json_dapat")),
                    }
                }
                _ => Err(type_err("(map, string)", arg, "json_dapat")),
            }
        }
        "json_letak" => {
            // (Value, Teks, Value) -> Value
            // Encoded as (map, (key, value))
            match arg {
                Value::Pair(obj, kv) => {
                    match (obj.as_ref(), kv.as_ref()) {
                        (Value::Map(m), Value::Pair(k, v)) => {
                            let key = extract_string(k, "json_letak")?;
                            let mut new_map = m.clone();
                            new_map.insert(key, v.as_ref().clone());
                            Ok(Some(Value::Map(new_map)))
                        }
                        _ => Err(type_err("(map, (string, value))", arg, "json_letak")),
                    }
                }
                _ => Err(type_err("(map, (string, value))", arg, "json_letak")),
            }
        }
        "json_ada" => {
            // (Value, Teks) -> Bool
            match arg {
                Value::Pair(obj, key) => {
                    let k = extract_string(key, "json_ada")?;
                    match obj.as_ref() {
                        Value::Map(m) => Ok(Some(Value::Bool(m.contains_key(&k)))),
                        _ => Err(type_err("map", obj, "json_ada")),
                    }
                }
                _ => Err(type_err("(map, string)", arg, "json_ada")),
            }
        }
        _ => Ok(None),
    }
}

// ═══════════════════════════════════════════════════════════════════
// JSON PARSER (hand-written recursive descent)
// ═══════════════════════════════════════════════════════════════════

fn parse_json(s: &str) -> Result<Value> {
    let s = s.trim();
    let (val, rest) = parse_value(s)?;
    let rest = rest.trim();
    if !rest.is_empty() {
        return Err(Error::InvalidOperation(format!(
            "json_urai: unexpected trailing content: '{}'",
            &rest[..rest.len().min(20)]
        )));
    }
    Ok(val)
}

fn parse_value(s: &str) -> Result<(Value, &str)> {
    let s = s.trim_start();
    if s.is_empty() {
        return Err(json_err("unexpected end of input"));
    }
    match s.as_bytes()[0] {
        b'"' => parse_string(s),
        b'{' => parse_object(s),
        b'[' => parse_array(s),
        b't' | b'f' => parse_bool(s),
        b'n' => parse_null(s),
        b'-' | b'0'..=b'9' => parse_number(s),
        c => Err(json_err(&format!("unexpected char '{}'", c as char))),
    }
}

fn parse_string(s: &str) -> Result<(Value, &str)> {
    debug_assert!(s.starts_with('"'));
    let s = &s[1..];
    let mut result = String::new();
    let mut chars = s.chars();
    loop {
        match chars.next() {
            None => return Err(json_err("unterminated string")),
            Some('"') => {
                let rest = chars.as_str();
                return Ok((Value::String(result), rest));
            }
            Some('\\') => {
                match chars.next() {
                    Some('"') => result.push('"'),
                    Some('\\') => result.push('\\'),
                    Some('/') => result.push('/'),
                    Some('n') => result.push('\n'),
                    Some('r') => result.push('\r'),
                    Some('t') => result.push('\t'),
                    Some('b') => result.push('\u{08}'),
                    Some('f') => result.push('\u{0C}'),
                    Some('u') => {
                        // \uXXXX — parse 4 hex digits
                        let hex: String = chars.by_ref().take(4).collect();
                        if hex.len() < 4 {
                            return Err(json_err("incomplete unicode escape"));
                        }
                        let cp = u32::from_str_radix(&hex, 16).map_err(|_| {
                            json_err(&format!("invalid unicode escape: \\u{}", hex))
                        })?;
                        if let Some(c) = char::from_u32(cp) {
                            result.push(c);
                        }
                    }
                    _ => return Err(json_err("invalid escape")),
                }
            }
            Some(c) => result.push(c),
        }
    }
}

fn parse_object(s: &str) -> Result<(Value, &str)> {
    debug_assert!(s.starts_with('{'));
    let mut s = s[1..].trim_start();
    let mut map = BTreeMap::new();
    if s.starts_with('}') {
        return Ok((Value::Map(map), &s[1..]));
    }
    loop {
        let s_trimmed = s.trim_start();
        if !s_trimmed.starts_with('"') {
            return Err(json_err("expected string key in object"));
        }
        let (key_val, rest) = parse_string(s_trimmed)?;
        let key = match key_val {
            Value::String(k) => k,
            _ => unreachable!(),
        };
        let rest = rest.trim_start();
        if !rest.starts_with(':') {
            return Err(json_err("expected ':' in object"));
        }
        let (val, rest) = parse_value(&rest[1..])?;
        map.insert(key, val);
        let rest = rest.trim_start();
        if rest.starts_with('}') {
            return Ok((Value::Map(map), &rest[1..]));
        }
        if rest.starts_with(',') {
            s = &rest[1..];
        } else {
            return Err(json_err("expected ',' or '}' in object"));
        }
    }
}

fn parse_array(s: &str) -> Result<(Value, &str)> {
    debug_assert!(s.starts_with('['));
    let mut s = s[1..].trim_start();
    let mut items = Vec::new();
    if s.starts_with(']') {
        return Ok((Value::List(items), &s[1..]));
    }
    loop {
        let (val, rest) = parse_value(s)?;
        items.push(val);
        let rest = rest.trim_start();
        if rest.starts_with(']') {
            return Ok((Value::List(items), &rest[1..]));
        }
        if rest.starts_with(',') {
            s = rest[1..].trim_start();
        } else {
            return Err(json_err("expected ',' or ']' in array"));
        }
    }
}

fn parse_bool(s: &str) -> Result<(Value, &str)> {
    if s.starts_with("true") {
        Ok((Value::Bool(true), &s[4..]))
    } else if s.starts_with("false") {
        Ok((Value::Bool(false), &s[5..]))
    } else {
        Err(json_err("expected 'true' or 'false'"))
    }
}

fn parse_null(s: &str) -> Result<(Value, &str)> {
    if s.starts_with("null") {
        Ok((Value::Unit, &s[4..]))
    } else {
        Err(json_err("expected 'null'"))
    }
}

fn parse_number(s: &str) -> Result<(Value, &str)> {
    let end = s
        .find(|c: char| !c.is_ascii_digit() && c != '-' && c != '.' && c != 'e' && c != 'E' && c != '+')
        .unwrap_or(s.len());
    let num_str = &s[..end];
    // Try integer first, fall back to float→int
    if let Ok(n) = num_str.parse::<u64>() {
        Ok((Value::Int(n), &s[end..]))
    } else if let Ok(f) = num_str.parse::<f64>() {
        Ok((Value::Int(f as u64), &s[end..]))
    } else {
        Err(json_err(&format!("cannot parse number: '{}'", num_str)))
    }
}

// ═══════════════════════════════════════════════════════════════════
// JSON STRINGIFY
// ═══════════════════════════════════════════════════════════════════

fn stringify_value(v: &Value) -> String {
    match v {
        Value::Unit => "null".to_string(),
        Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
        Value::Int(n) => n.to_string(),
        Value::String(s) => format!("\"{}\"", escape_json_string(s)),
        Value::List(items) => {
            let parts: Vec<String> = items.iter().map(stringify_value).collect();
            format!("[{}]", parts.join(","))
        }
        Value::Map(entries) => {
            let parts: Vec<String> = entries
                .iter()
                .map(|(k, v)| format!("\"{}\":{}", escape_json_string(k), stringify_value(v)))
                .collect();
            format!("{{{}}}", parts.join(","))
        }
        Value::Pair(a, b) => {
            format!("[{},{}]", stringify_value(a), stringify_value(b))
        }
        _ => "null".to_string(),
    }
}

fn escape_json_string(s: &str) -> String {
    let mut r = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => r.push_str("\\\""),
            '\\' => r.push_str("\\\\"),
            '\n' => r.push_str("\\n"),
            '\r' => r.push_str("\\r"),
            '\t' => r.push_str("\\t"),
            c if c < '\u{20}' => {
                r.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => r.push(c),
        }
    }
    r
}

fn json_err(msg: &str) -> Error {
    Error::InvalidOperation(format!("json_urai: {}", msg))
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
    fn test_json_urai_simple() {
        let result = apply("json_urai", &Value::String(r#"{"name":"RIINA","version":1}"#.to_string()))
            .unwrap()
            .unwrap();
        match result {
            Value::Map(m) => {
                assert_eq!(m.get("name"), Some(&Value::String("RIINA".to_string())));
                assert_eq!(m.get("version"), Some(&Value::Int(1)));
            }
            _ => panic!("expected map"),
        }
    }

    #[test]
    fn test_json_urai_array() {
        let result = apply("json_urai", &Value::String("[1,2,3]".to_string()))
            .unwrap()
            .unwrap();
        assert_eq!(
            result,
            Value::List(vec![Value::Int(1), Value::Int(2), Value::Int(3)])
        );
    }

    #[test]
    fn test_json_urai_nested() {
        let result = apply(
            "json_urai",
            &Value::String(r#"{"a":{"b":true},"c":[1,null]}"#.to_string()),
        )
        .unwrap()
        .unwrap();
        match result {
            Value::Map(m) => {
                match m.get("a") {
                    Some(Value::Map(inner)) => {
                        assert_eq!(inner.get("b"), Some(&Value::Bool(true)));
                    }
                    _ => panic!("expected nested map"),
                }
                match m.get("c") {
                    Some(Value::List(items)) => {
                        assert_eq!(items.len(), 2);
                        assert_eq!(items[0], Value::Int(1));
                        assert_eq!(items[1], Value::Unit);
                    }
                    _ => panic!("expected list"),
                }
            }
            _ => panic!("expected map"),
        }
    }

    #[test]
    fn test_json_urai_escapes() {
        let result = apply(
            "json_urai",
            &Value::String(r#""hello\nworld""#.to_string()),
        )
        .unwrap()
        .unwrap();
        assert_eq!(result, Value::String("hello\nworld".to_string()));
    }

    #[test]
    fn test_json_ke_teks() {
        let mut m = BTreeMap::new();
        m.insert("x".to_string(), Value::Int(42));
        let result = apply("json_ke_teks", &Value::Map(m)).unwrap().unwrap();
        assert_eq!(result, Value::String("{\"x\":42}".to_string()));
    }

    #[test]
    fn test_json_ke_teks_array() {
        let result = apply(
            "json_ke_teks",
            &Value::List(vec![Value::Bool(true), Value::String("hi".to_string())]),
        )
        .unwrap()
        .unwrap();
        assert_eq!(result, Value::String("[true,\"hi\"]".to_string()));
    }

    #[test]
    fn test_json_dapat() {
        let mut m = BTreeMap::new();
        m.insert("key".to_string(), Value::Int(99));
        let arg = Value::Pair(
            Box::new(Value::Map(m)),
            Box::new(Value::String("key".to_string())),
        );
        assert_eq!(apply("json_dapat", &arg).unwrap(), Some(Value::Int(99)));
    }

    #[test]
    fn test_json_letak() {
        let m = BTreeMap::new();
        let arg = Value::Pair(
            Box::new(Value::Map(m)),
            Box::new(Value::Pair(
                Box::new(Value::String("k".to_string())),
                Box::new(Value::Int(1)),
            )),
        );
        let result = apply("json_letak", &arg).unwrap().unwrap();
        match result {
            Value::Map(m) => assert_eq!(m.get("k"), Some(&Value::Int(1))),
            _ => panic!("expected map"),
        }
    }

    #[test]
    fn test_json_ada() {
        let mut m = BTreeMap::new();
        m.insert("x".to_string(), Value::Int(1));
        let arg = Value::Pair(
            Box::new(Value::Map(m)),
            Box::new(Value::String("x".to_string())),
        );
        assert_eq!(apply("json_ada", &arg).unwrap(), Some(Value::Bool(true)));
    }

    #[test]
    fn test_roundtrip() {
        let json = r#"{"arr":[1,2],"flag":true,"name":"test"}"#;
        let parsed = apply("json_urai", &Value::String(json.to_string()))
            .unwrap()
            .unwrap();
        let stringified = apply("json_ke_teks", &parsed).unwrap().unwrap();
        assert_eq!(stringified, Value::String(json.to_string()));
    }

    #[test]
    fn test_unknown_returns_none() {
        assert_eq!(apply("unknown", &Value::Unit).unwrap(), None);
    }
}
