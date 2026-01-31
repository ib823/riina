// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Minimal JSON parser/writer for LSP.
//! Zero external dependencies.

use std::collections::BTreeMap;
use std::fmt;

/// A JSON value.
#[derive(Debug, Clone, PartialEq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<JsonValue>),
    Object(BTreeMap<String, JsonValue>),
}

impl JsonValue {
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Self::Number(n) => Some(*n as i64),
            _ => None,
        }
    }

    pub fn as_object(&self) -> Option<&BTreeMap<String, JsonValue>> {
        match self {
            Self::Object(m) => Some(m),
            _ => None,
        }
    }

    pub fn get(&self, key: &str) -> Option<&JsonValue> {
        self.as_object()?.get(key)
    }
}

impl fmt::Display for JsonValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Null => write!(f, "null"),
            Self::Bool(b) => write!(f, "{}", if *b { "true" } else { "false" }),
            Self::Number(n) => {
                if *n == (*n as i64) as f64 {
                    write!(f, "{}", *n as i64)
                } else {
                    write!(f, "{n}")
                }
            }
            Self::String(s) => {
                write!(f, "\"")?;
                for c in s.chars() {
                    match c {
                        '"' => write!(f, "\\\"")?,
                        '\\' => write!(f, "\\\\")?,
                        '\n' => write!(f, "\\n")?,
                        '\r' => write!(f, "\\r")?,
                        '\t' => write!(f, "\\t")?,
                        c => write!(f, "{c}")?,
                    }
                }
                write!(f, "\"")
            }
            Self::Array(arr) => {
                write!(f, "[")?;
                for (i, v) in arr.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{v}")?;
                }
                write!(f, "]")
            }
            Self::Object(map) => {
                write!(f, "{{")?;
                for (i, (k, v)) in map.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "\"{}\":{}", k, v)?;
                }
                write!(f, "}}")
            }
        }
    }
}

/// Parse a JSON string into a JsonValue.
pub fn parse(input: &str) -> Result<JsonValue, String> {
    let mut chars = input.trim().chars().peekable();
    let val = parse_value(&mut chars)?;
    Ok(val)
}

fn parse_value(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<JsonValue, String> {
    skip_whitespace(chars);
    match chars.peek() {
        Some('"') => parse_string(chars).map(JsonValue::String),
        Some('{') => parse_object(chars),
        Some('[') => parse_array(chars),
        Some('t') => {
            expect_str(chars, "true")?;
            Ok(JsonValue::Bool(true))
        }
        Some('f') => {
            expect_str(chars, "false")?;
            Ok(JsonValue::Bool(false))
        }
        Some('n') => {
            expect_str(chars, "null")?;
            Ok(JsonValue::Null)
        }
        Some(c) if *c == '-' || c.is_ascii_digit() => parse_number(chars),
        Some(c) => Err(format!("Unexpected char: {c}")),
        None => Err("Unexpected end of input".into()),
    }
}

fn skip_whitespace(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) {
    while let Some(c) = chars.peek() {
        if c.is_ascii_whitespace() {
            chars.next();
        } else {
            break;
        }
    }
}

fn expect_str(chars: &mut std::iter::Peekable<std::str::Chars<'_>>, s: &str) -> Result<(), String> {
    for expected in s.chars() {
        match chars.next() {
            Some(c) if c == expected => {}
            Some(c) => return Err(format!("Expected '{expected}', got '{c}'")),
            None => return Err(format!("Expected '{expected}', got EOF")),
        }
    }
    Ok(())
}

fn parse_string(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<String, String> {
    chars.next(); // consume "
    let mut s = String::new();
    loop {
        match chars.next() {
            Some('"') => return Ok(s),
            Some('\\') => match chars.next() {
                Some('"') => s.push('"'),
                Some('\\') => s.push('\\'),
                Some('/') => s.push('/'),
                Some('n') => s.push('\n'),
                Some('r') => s.push('\r'),
                Some('t') => s.push('\t'),
                Some('u') => {
                    let mut hex = String::new();
                    for _ in 0..4 {
                        hex.push(chars.next().ok_or("Unexpected EOF in unicode escape")?);
                    }
                    let cp = u32::from_str_radix(&hex, 16)
                        .map_err(|e| format!("Invalid unicode: {e}"))?;
                    s.push(char::from_u32(cp).unwrap_or('\u{FFFD}'));
                }
                Some(c) => return Err(format!("Invalid escape: \\{c}")),
                None => return Err("Unexpected EOF in string escape".into()),
            },
            Some(c) => s.push(c),
            None => return Err("Unterminated string".into()),
        }
    }
}

fn parse_number(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<JsonValue, String> {
    let mut s = String::new();
    if let Some('-') = chars.peek() {
        s.push('-');
        chars.next();
    }
    while let Some(c) = chars.peek() {
        if c.is_ascii_digit() || *c == '.' || *c == 'e' || *c == 'E' || *c == '+' || *c == '-' {
            s.push(*c);
            chars.next();
        } else {
            break;
        }
    }
    s.parse::<f64>()
        .map(JsonValue::Number)
        .map_err(|e| format!("Invalid number: {e}"))
}

fn parse_array(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<JsonValue, String> {
    chars.next(); // consume [
    let mut arr = Vec::new();
    skip_whitespace(chars);
    if let Some(']') = chars.peek() {
        chars.next();
        return Ok(JsonValue::Array(arr));
    }
    loop {
        arr.push(parse_value(chars)?);
        skip_whitespace(chars);
        match chars.peek() {
            Some(',') => { chars.next(); }
            Some(']') => { chars.next(); return Ok(JsonValue::Array(arr)); }
            _ => return Err("Expected ',' or ']'".into()),
        }
    }
}

fn parse_object(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<JsonValue, String> {
    chars.next(); // consume {
    let mut map = BTreeMap::new();
    skip_whitespace(chars);
    if let Some('}') = chars.peek() {
        chars.next();
        return Ok(JsonValue::Object(map));
    }
    loop {
        skip_whitespace(chars);
        let key = parse_string(chars)?;
        skip_whitespace(chars);
        match chars.next() {
            Some(':') => {}
            _ => return Err("Expected ':'".into()),
        }
        let val = parse_value(chars)?;
        map.insert(key, val);
        skip_whitespace(chars);
        match chars.peek() {
            Some(',') => { chars.next(); }
            Some('}') => { chars.next(); return Ok(JsonValue::Object(map)); }
            _ => return Err("Expected ',' or '}'".into()),
        }
    }
}

/// Helper to build JSON objects.
pub fn obj(entries: Vec<(&str, JsonValue)>) -> JsonValue {
    let mut map = BTreeMap::new();
    for (k, v) in entries {
        map.insert(k.to_string(), v);
    }
    JsonValue::Object(map)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_null() {
        assert_eq!(parse("null").unwrap(), JsonValue::Null);
    }

    #[test]
    fn test_parse_bool() {
        assert_eq!(parse("true").unwrap(), JsonValue::Bool(true));
        assert_eq!(parse("false").unwrap(), JsonValue::Bool(false));
    }

    #[test]
    fn test_parse_number() {
        assert_eq!(parse("42").unwrap(), JsonValue::Number(42.0));
        assert_eq!(parse("-3.14").unwrap(), JsonValue::Number(-3.14));
    }

    #[test]
    fn test_parse_string() {
        assert_eq!(parse(r#""hello""#).unwrap(), JsonValue::String("hello".into()));
        assert_eq!(parse(r#""a\nb""#).unwrap(), JsonValue::String("a\nb".into()));
    }

    #[test]
    fn test_parse_object() {
        let val = parse(r#"{"a":1,"b":"c"}"#).unwrap();
        assert_eq!(val.get("a"), Some(&JsonValue::Number(1.0)));
        assert_eq!(val.get("b"), Some(&JsonValue::String("c".into())));
    }

    #[test]
    fn test_roundtrip() {
        let val = obj(vec![
            ("id", JsonValue::Number(1.0)),
            ("method", JsonValue::String("initialize".into())),
        ]);
        let s = val.to_string();
        let parsed = parse(&s).unwrap();
        assert_eq!(val, parsed);
    }
}
