// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Parser Tests
//!
//! Comprehensive tests for RIINA parser covering:
//! - All literal types
//! - All expression forms (25 AST variants)
//! - Error recovery and error cases
//! - Edge cases and boundary conditions
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

#[allow(unused_imports)]
use crate::{ParseError, ParseErrorKind, Parser};
#[allow(unused_imports)]
use riina_types::{
    BinOp, Effect, Expr, Linearity, Program, SecurityLevel, SessionType, TopLevelDecl, Ty,
};

// =============================================================================
// LITERAL TESTS
// =============================================================================

#[test]
fn test_parse_literals() {
    let mut p = Parser::new("123");
    assert_eq!(p.parse_expr().unwrap(), Expr::Int(123));

    let mut p = Parser::new("true");
    assert_eq!(p.parse_expr().unwrap(), Expr::Bool(true));

    let mut p = Parser::new("\"hello\"");
    assert_eq!(p.parse_expr().unwrap(), Expr::String("hello".to_string()));
}

#[test]
fn test_parse_sized_int_literals() {
    // Width suffixes produce the distinct `Expr::IntN` literal (numeric tower).
    let cases = [
        ("42u8", 42, 8, false),
        ("255u8", 255, 8, false),
        ("1000u16", 1000, 16, false),
        ("7i32", 7, 32, true),
        ("9000000000i64", 9_000_000_000, 64, true),
    ];
    for (src, value, bits, signed) in cases {
        let mut p = Parser::new(src);
        assert_eq!(
            p.parse_expr().unwrap(),
            Expr::IntN {
                value,
                bits,
                signed
            },
            "{src} should parse as a sized integer literal"
        );
    }
    // Digit separators are stripped before the value is parsed.
    let mut p = Parser::new("1_000u32");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::IntN {
            value: 1000,
            bits: 32,
            signed: false
        }
    );
    // No suffix still parses as the default unsized `Expr::Int`.
    let mut p = Parser::new("42");
    assert_eq!(p.parse_expr().unwrap(), Expr::Int(42));
}

#[test]
fn test_parse_int_zero() {
    // Input: Zero integer
    // Expected: Expr::Int(0)
    // Rationale: Zero is valid integer literal
    let mut p = Parser::new("0");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Int(0),
        "Zero must parse as valid integer"
    );
}

#[test]
fn test_parse_int_large() {
    // Input: Large integer
    // Expected: Expr::Int with large value
    // Rationale: Large integers common in crypto
    let mut p = Parser::new("999999999");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Int(999_999_999),
        "Large integers must parse correctly"
    );
}

#[test]
fn test_parse_bool_false() {
    // Input: false boolean
    // Expected: Expr::Bool(false)
    // Rationale: Both boolean values must work
    let mut p = Parser::new("false");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Bool(false),
        "false must parse as Expr::Bool(false)"
    );
}

#[test]
fn test_parse_string_empty() {
    // Input: Empty string
    // Expected: Expr::String("")
    // Rationale: Empty strings are valid
    let mut p = Parser::new("\"\"");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::String("".to_string()),
        "Empty string must parse correctly"
    );
}

#[test]
fn test_parse_string_with_spaces() {
    // Input: String with spaces
    // Expected: Expr::String with spaces preserved
    // Rationale: Whitespace in strings must be preserved
    let mut p = Parser::new("\"hello world\"");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::String("hello world".to_string()),
        "Spaces in strings must be preserved"
    );
}

#[test]
fn test_parse_string_with_escapes() {
    // Input: String with escape sequences
    // Expected: Expr::String with interpreted escapes
    // Rationale: Escape sequences must be processed
    let mut p = Parser::new("\"hello\\nworld\"");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::String("hello\nworld".to_string()),
        "Escape sequences in strings must be interpreted"
    );
}

// =============================================================================
// VARIABLE TESTS
// =============================================================================

#[test]
fn test_parse_var_simple() {
    // Input: Simple variable
    // Expected: Expr::Var
    // Rationale: Basic variable parsing
    let mut p = Parser::new("x");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Var("x".to_string()),
        "Simple variable must parse"
    );
}

#[test]
fn test_parse_var_long_name() {
    // Input: Long variable name
    // Expected: Expr::Var with full name
    // Rationale: No arbitrary length limits
    let mut p = Parser::new("very_long_variable_name_here");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Var("very_long_variable_name_here".to_string()),
        "Long variable names must be preserved"
    );
}

#[test]
fn test_parse_var_with_numbers() {
    // Input: Variable with numbers
    // Expected: Expr::Var
    // Rationale: Numbers allowed after first char
    let mut p = Parser::new("x123");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Var("x123".to_string()),
        "Variables with numbers must parse"
    );
}

#[test]
fn test_parse_var_underscore_prefix() {
    // Input: Variable with underscore prefix
    // Expected: Expr::Var
    // Rationale: Underscore-prefixed vars for unused
    let mut p = Parser::new("_unused");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Var("_unused".to_string()),
        "Underscore-prefixed variables must parse"
    );
}

// =============================================================================
// UNIT AND PARENTHESES TESTS
// =============================================================================

#[test]
fn test_parse_unit() {
    // Input: Unit value ()
    // Expected: Expr::Unit
    // Rationale: Unit is fundamental type
    let mut p = Parser::new("()");
    assert_eq!(p.parse_expr().unwrap(), Expr::Unit, "() must parse as Unit");
}

#[test]
fn test_parse_parenthesized_expr() {
    // Input: Parenthesized expression
    // Expected: Inner expression (parens stripped)
    // Rationale: Parentheses for grouping
    let mut p = Parser::new("(42)");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Int(42),
        "Parenthesized expression must unwrap"
    );
}

#[test]
fn test_parse_nested_parentheses() {
    // Input: Deeply nested parentheses
    // Expected: Inner expression
    // Rationale: Arbitrary nesting allowed
    let mut p = Parser::new("(((x)))");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::Var("x".to_string()),
        "Nested parentheses must unwrap correctly"
    );
}

// =============================================================================
// PAIR TESTS
// =============================================================================

#[test]
fn test_parse_pair_simple() {
    // Input: Simple pair
    // Expected: Expr::Pair
    // Rationale: Product types fundamental
    let mut p = Parser::new("(1, 2)");
    match p.parse_expr().unwrap() {
        Expr::Pair(e1, e2) => {
            assert_eq!(*e1, Expr::Int(1));
            assert_eq!(*e2, Expr::Int(2));
        }
        other => panic!("Expected Pair, got {:?}", other),
    }
}

#[test]
fn test_parse_pair_mixed_types() {
    // Input: Pair with mixed types
    // Expected: Expr::Pair with different types
    // Rationale: Pairs can hold heterogeneous types
    let mut p = Parser::new("(true, \"hello\")");
    match p.parse_expr().unwrap() {
        Expr::Pair(e1, e2) => {
            assert_eq!(*e1, Expr::Bool(true));
            assert_eq!(*e2, Expr::String("hello".to_string()));
        }
        other => panic!("Expected Pair, got {:?}", other),
    }
}

#[test]
fn test_parse_pair_nested() {
    // Input: Nested pairs
    // Expected: Expr::Pair containing Expr::Pair
    // Rationale: Pairs can nest
    let mut p = Parser::new("((1, 2), 3)");
    match p.parse_expr().unwrap() {
        Expr::Pair(e1, e2) => {
            match *e1 {
                Expr::Pair(inner1, inner2) => {
                    assert_eq!(*inner1, Expr::Int(1));
                    assert_eq!(*inner2, Expr::Int(2));
                }
                other => panic!("Expected inner Pair, got {:?}", other),
            }
            assert_eq!(*e2, Expr::Int(3));
        }
        other => panic!("Expected Pair, got {:?}", other),
    }
}

#[test]
fn test_parse_let() {
    let mut p = Parser::new("let x = 1; 2");
    match p.parse_expr().unwrap() {
        Expr::Let(x, _, e1, e2) => {
            assert_eq!(x, "x");
            assert_eq!(*e1, Expr::Int(1));
            assert_eq!(*e2, Expr::Int(2));
        }
        _ => panic!("Expected Let"),
    }
}

#[test]
fn test_parse_if() {
    let mut p = Parser::new("if true { 1 } else { 2 }");
    match p.parse_expr().unwrap() {
        Expr::If(cond, e1, e2) => {
            assert_eq!(*cond, Expr::Bool(true));
            assert_eq!(*e1, Expr::Int(1));
            assert_eq!(*e2, Expr::Int(2));
        }
        _ => panic!("Expected If"),
    }
}

#[test]
fn test_parse_app() {
    let mut p = Parser::new("f x");
    match p.parse_expr().unwrap() {
        Expr::App(f, x) => {
            assert_eq!(*f, Expr::Var("f".to_string()));
            assert_eq!(*x, Expr::Var("x".to_string()));
        }
        _ => panic!("Expected App"),
    }
}

#[test]
fn test_parse_lam() {
    let mut p = Parser::new("fn(x: Int) x");
    match p.parse_expr().unwrap() {
        Expr::Lam(x, ty, body) => {
            assert_eq!(x, "x");
            assert_eq!(ty, Ty::Int);
            assert_eq!(*body, Expr::Var("x".to_string()));
        }
        _ => panic!("Expected Lam"),
    }
}

#[test]
fn test_parse_assignment() {
    let mut p = Parser::new("x := 1");
    match p.parse_expr().unwrap() {
        Expr::Assign(lhs, rhs) => {
            assert_eq!(*lhs, Expr::Var("x".to_string()));
            assert_eq!(*rhs, Expr::Int(1));
        }
        _ => panic!("Expected Assign"),
    }
}

#[test]
fn test_parse_ref_deref() {
    let mut p = Parser::new("!ref 1 @ Public");
    // Should parse as !(ref 1 @ Public) -> Deref(Ref(1, Public))
    match p.parse_expr().unwrap() {
        Expr::Deref(e) => match *e {
            Expr::Ref(inner, level) => {
                assert_eq!(*inner, Expr::Int(1));
                assert_eq!(level, SecurityLevel::Public);
            }
            _ => panic!("Expected Ref inside Deref"),
        },
        _ => panic!("Expected Deref"),
    }
}

#[test]
fn test_parse_match() {
    let mut p = Parser::new("match e { inl x => 1, inr y => 2 }");
    match p.parse_expr().unwrap() {
        Expr::Case(e, x, e1, y, e2) => {
            assert_eq!(*e, Expr::Var("e".to_string()));
            assert_eq!(x, "x");
            assert_eq!(*e1, Expr::Int(1));
            assert_eq!(y, "y");
            assert_eq!(*e2, Expr::Int(2));
        }
        _ => panic!("Expected Case"),
    }
}

#[test]
fn test_parse_perform_handle() {
    let mut p = Parser::new("handle perform Write \"data\" with eff => 0");
    match p.parse_expr().unwrap() {
        Expr::Handle(e, x, h) => {
            match *e {
                Expr::Perform(eff, payload) => {
                    assert_eq!(eff, Effect::Write);
                    assert_eq!(*payload, Expr::String("data".to_string()));
                }
                _ => panic!("Expected Perform inside Handle"),
            }
            assert_eq!(x, "eff");
            assert_eq!(*h, Expr::Int(0));
        }
        _ => panic!("Expected Handle"),
    }
}

#[test]
fn test_parse_security() {
    let mut p = Parser::new("classify prove 1");
    match p.parse_expr().unwrap() {
        Expr::Classify(e) => match *e {
            Expr::Prove(inner) => assert_eq!(*inner, Expr::Int(1)),
            _ => panic!("Expected Prove inside Classify"),
        },
        _ => panic!("Expected Classify"),
    }
}

#[test]
fn test_parse_classify_wraps_full_application() {
    let mut p = Parser::new("classify f x");
    match p.parse_expr().unwrap() {
        Expr::Classify(body) => match *body {
            Expr::App(f, x) => {
                assert_eq!(*f, Expr::Var("f".to_string()));
                assert_eq!(*x, Expr::Var("x".to_string()));
            }
            other => panic!("Expected App inside Classify, got {:?}", other),
        },
        other => panic!("Expected Classify, got {:?}", other),
    }
}

#[test]
fn test_parse_declassify() {
    let mut p = Parser::new("declassify x with proof");
    match p.parse_expr().unwrap() {
        Expr::Declassify(e1, e2) => {
            assert_eq!(*e1, Expr::Var("x".to_string()));
            assert_eq!(*e2, Expr::Var("proof".to_string()));
        }
        _ => panic!("Expected Declassify"),
    }
}

#[test]
fn test_parse_inl_inr() {
    let mut p = Parser::new("inl 1 : Int");
    match p.parse_expr().unwrap() {
        Expr::Inl(e, ty) => {
            assert_eq!(*e, Expr::Int(1));
            assert_eq!(ty, Ty::Int);
        }
        _ => panic!("Expected Inl"),
    }
}

// =============================================================================
// ADDITIONAL LET TESTS
// =============================================================================

#[test]
fn test_parse_let_with_var() {
    // Input: let binding a variable
    // Expected: Expr::Let with var binding
    // Rationale: Variables can be bound
    let mut p = Parser::new("let y = x; y");
    match p.parse_expr().unwrap() {
        Expr::Let(name, _, bound, body) => {
            assert_eq!(name, "y");
            assert_eq!(*bound, Expr::Var("x".to_string()));
            assert_eq!(*body, Expr::Var("y".to_string()));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_let_nested() {
    // Input: Nested let bindings
    // Expected: Nested Expr::Let
    // Rationale: Let bindings can nest
    let mut p = Parser::new("let x = 1; let y = 2; x");
    match p.parse_expr().unwrap() {
        Expr::Let(x, _, e1, body) => {
            assert_eq!(x, "x");
            assert_eq!(*e1, Expr::Int(1));
            match *body {
                Expr::Let(y, _, e2, inner) => {
                    assert_eq!(y, "y");
                    assert_eq!(*e2, Expr::Int(2));
                    assert_eq!(*inner, Expr::Var("x".to_string()));
                }
                other => panic!("Expected inner Let, got {:?}", other),
            }
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_let_with_complex_expr() {
    // Input: Let binding with complex expression
    // Expected: Let with Pair as bound value
    // Rationale: Any expression can be bound
    let mut p = Parser::new("let pair = (1, 2); pair");
    match p.parse_expr().unwrap() {
        Expr::Let(name, _, bound, body) => {
            assert_eq!(name, "pair");
            match *bound {
                Expr::Pair(e1, e2) => {
                    assert_eq!(*e1, Expr::Int(1));
                    assert_eq!(*e2, Expr::Int(2));
                }
                other => panic!("Expected Pair, got {:?}", other),
            }
            assert_eq!(*body, Expr::Var("pair".to_string()));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

// =============================================================================
// ADDITIONAL IF TESTS
// =============================================================================

#[test]
fn test_parse_if_with_var_condition() {
    // Input: If with variable condition
    // Expected: Expr::If with Var as condition
    // Rationale: Any expression can be condition
    let mut p = Parser::new("if cond { x } else { y }");
    match p.parse_expr().unwrap() {
        Expr::If(cond, e1, e2) => {
            assert_eq!(*cond, Expr::Var("cond".to_string()));
            assert_eq!(*e1, Expr::Var("x".to_string()));
            assert_eq!(*e2, Expr::Var("y".to_string()));
        }
        other => panic!("Expected If, got {:?}", other),
    }
}

#[test]
fn test_parse_if_nested() {
    // Input: Nested if expressions
    // Expected: Nested Expr::If
    // Rationale: If expressions can nest
    let mut p = Parser::new("if a { if b { 1 } else { 2 } } else { 3 }");
    match p.parse_expr().unwrap() {
        Expr::If(cond, e1, e2) => {
            assert_eq!(*cond, Expr::Var("a".to_string()));
            match *e1 {
                Expr::If(inner_cond, inner_e1, inner_e2) => {
                    assert_eq!(*inner_cond, Expr::Var("b".to_string()));
                    assert_eq!(*inner_e1, Expr::Int(1));
                    assert_eq!(*inner_e2, Expr::Int(2));
                }
                other => panic!("Expected inner If, got {:?}", other),
            }
            assert_eq!(*e2, Expr::Int(3));
        }
        other => panic!("Expected If, got {:?}", other),
    }
}

// =============================================================================
// ADDITIONAL LAMBDA TESTS
// =============================================================================

#[test]
fn test_parse_lam_bool_param() {
    // Input: Lambda with Bool parameter type
    // Expected: Expr::Lam with Ty::Bool
    // Rationale: All types should work as params
    let mut p = Parser::new("fn(b: Bool) b");
    match p.parse_expr().unwrap() {
        Expr::Lam(param, ty, body) => {
            assert_eq!(param, "b");
            assert_eq!(ty, Ty::Bool);
            assert_eq!(*body, Expr::Var("b".to_string()));
        }
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_lam_string_param() {
    // Input: Lambda with String parameter type
    // Expected: Expr::Lam with Ty::String
    // Rationale: String type parameter
    let mut p = Parser::new("fn(s: String) s");
    match p.parse_expr().unwrap() {
        Expr::Lam(param, ty, body) => {
            assert_eq!(param, "s");
            assert_eq!(ty, Ty::String);
            assert_eq!(*body, Expr::Var("s".to_string()));
        }
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_lam_unit_param() {
    // Input: Lambda with Unit parameter type
    // Expected: Expr::Lam with Ty::Unit
    // Rationale: Unit type parameter (thunk-like)
    let mut p = Parser::new("fn(u: Unit) 42");
    match p.parse_expr().unwrap() {
        Expr::Lam(param, ty, body) => {
            assert_eq!(param, "u");
            assert_eq!(ty, Ty::Unit);
            assert_eq!(*body, Expr::Int(42));
        }
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_lam_bytes_param() {
    // Input: Lambda with Bytes parameter type
    // Expected: Expr::Lam with Ty::Bytes
    // Rationale: Bytes type for crypto operations
    let mut p = Parser::new("fn(data: Bytes) data");
    match p.parse_expr().unwrap() {
        Expr::Lam(param, ty, body) => {
            assert_eq!(param, "data");
            assert_eq!(ty, Ty::Bytes);
            assert_eq!(*body, Expr::Var("data".to_string()));
        }
        other => panic!("Expected Lam, got {:?}", other),
    }
}

// =============================================================================
// APPLICATION TESTS
// =============================================================================

#[test]
fn test_parse_app_multiple() {
    // Input: Multiple applications
    // Expected: Left-associative App chain
    // Rationale: Curried function application
    let mut p = Parser::new("f x y");
    match p.parse_expr().unwrap() {
        Expr::App(outer, z) => {
            assert_eq!(*z, Expr::Var("y".to_string()));
            match *outer {
                Expr::App(f, x) => {
                    assert_eq!(*f, Expr::Var("f".to_string()));
                    assert_eq!(*x, Expr::Var("x".to_string()));
                }
                other => panic!("Expected inner App, got {:?}", other),
            }
        }
        other => panic!("Expected App, got {:?}", other),
    }
}

#[test]
fn test_parse_app_with_literal() {
    // Input: Application with literal argument
    // Expected: Expr::App with Int argument
    // Rationale: Literals can be arguments
    let mut p = Parser::new("f 42");
    match p.parse_expr().unwrap() {
        Expr::App(f, arg) => {
            assert_eq!(*f, Expr::Var("f".to_string()));
            assert_eq!(*arg, Expr::Int(42));
        }
        other => panic!("Expected App, got {:?}", other),
    }
}

#[test]
fn test_parse_app_with_parenthesized() {
    // Input: Application with parenthesized argument
    // Expected: Expr::App with grouped expression
    // Rationale: Parentheses for explicit grouping
    let mut p = Parser::new("f (x y)");
    match p.parse_expr().unwrap() {
        Expr::App(f, arg) => {
            assert_eq!(*f, Expr::Var("f".to_string()));
            match *arg {
                Expr::App(inner_f, inner_arg) => {
                    assert_eq!(*inner_f, Expr::Var("x".to_string()));
                    assert_eq!(*inner_arg, Expr::Var("y".to_string()));
                }
                other => panic!("Expected inner App, got {:?}", other),
            }
        }
        other => panic!("Expected App, got {:?}", other),
    }
}

// =============================================================================
// INL/INR TESTS
// =============================================================================

#[test]
fn test_parse_inr() {
    // Input: inr expression
    // Expected: Expr::Inr
    // Rationale: Right injection for sum types
    let mut p = Parser::new("inr true : Bool");
    match p.parse_expr().unwrap() {
        Expr::Inr(e, ty) => {
            assert_eq!(*e, Expr::Bool(true));
            assert_eq!(ty, Ty::Bool);
        }
        other => panic!("Expected Inr, got {:?}", other),
    }
}

#[test]
fn test_parse_inl_with_var() {
    // Input: inl with variable
    // Expected: Expr::Inl with Var
    // Rationale: Variables can be injected
    let mut p = Parser::new("inl x : Int");
    match p.parse_expr().unwrap() {
        Expr::Inl(e, ty) => {
            assert_eq!(*e, Expr::Var("x".to_string()));
            assert_eq!(ty, Ty::Int);
        }
        other => panic!("Expected Inl, got {:?}", other),
    }
}

// =============================================================================
// EFFECT TESTS
// =============================================================================

#[test]
fn test_parse_perform_pure() {
    // Input: perform Pure
    // Expected: Expr::Perform with Effect::Pure
    // Rationale: Pure effect annotation
    let mut p = Parser::new("perform Pure ()");
    match p.parse_expr().unwrap() {
        Expr::Perform(eff, payload) => {
            assert_eq!(eff, Effect::Pure);
            assert_eq!(*payload, Expr::Unit);
        }
        other => panic!("Expected Perform, got {:?}", other),
    }
}

#[test]
fn test_parse_perform_read() {
    // Input: perform Read
    // Expected: Expr::Perform with Effect::Read
    // Rationale: Read effect for input
    let mut p = Parser::new("perform Read x");
    match p.parse_expr().unwrap() {
        Expr::Perform(eff, payload) => {
            assert_eq!(eff, Effect::Read);
            assert_eq!(*payload, Expr::Var("x".to_string()));
        }
        other => panic!("Expected Perform, got {:?}", other),
    }
}

#[test]
fn test_parse_perform_network() {
    // Input: perform Network
    // Expected: Expr::Perform with Effect::Network
    // Rationale: Network effect for IO
    let mut p = Parser::new("perform Network \"request\"");
    match p.parse_expr().unwrap() {
        Expr::Perform(eff, payload) => {
            assert_eq!(eff, Effect::Network);
            assert_eq!(*payload, Expr::String("request".to_string()));
        }
        other => panic!("Expected Perform, got {:?}", other),
    }
}

#[test]
fn test_parse_perform_crypto() {
    // Input: perform Crypto
    // Expected: Expr::Perform with Effect::Crypto
    // Rationale: Crypto effect for cryptographic ops
    let mut p = Parser::new("perform Crypto data");
    match p.parse_expr().unwrap() {
        Expr::Perform(eff, payload) => {
            assert_eq!(eff, Effect::Crypto);
            assert_eq!(*payload, Expr::Var("data".to_string()));
        }
        other => panic!("Expected Perform, got {:?}", other),
    }
}

#[test]
fn test_parse_perform_system() {
    // Input: perform System
    // Expected: Expr::Perform with Effect::System
    // Rationale: System effect for OS calls
    let mut p = Parser::new("perform System cmd");
    match p.parse_expr().unwrap() {
        Expr::Perform(eff, payload) => {
            assert_eq!(eff, Effect::System);
            assert_eq!(*payload, Expr::Var("cmd".to_string()));
        }
        other => panic!("Expected Perform, got {:?}", other),
    }
}

#[test]
fn test_parse_handle_simple() {
    // Input: Simple handle expression
    // Expected: Expr::Handle
    // Rationale: Effect handling
    let mut p = Parser::new("handle x with e => e");
    match p.parse_expr().unwrap() {
        Expr::Handle(body, param, handler) => {
            assert_eq!(*body, Expr::Var("x".to_string()));
            assert_eq!(param, "e");
            assert_eq!(*handler, Expr::Var("e".to_string()));
        }
        other => panic!("Expected Handle, got {:?}", other),
    }
}

// =============================================================================
// REFERENCE TESTS
// =============================================================================

#[test]
fn test_parse_ref_secret() {
    // Input: Reference with Secret level
    // Expected: Expr::Ref with SecurityLevel::Secret
    // Rationale: Secret references for sensitive data
    let mut p = Parser::new("ref 42 @ Secret");
    match p.parse_expr().unwrap() {
        Expr::Ref(e, level) => {
            assert_eq!(*e, Expr::Int(42));
            assert_eq!(level, SecurityLevel::Secret);
        }
        other => panic!("Expected Ref, got {:?}", other),
    }
}

#[test]
fn test_parse_ref_public() {
    // Input: Reference with Public level
    // Expected: Expr::Ref with SecurityLevel::Public
    // Rationale: Public references for non-sensitive data
    let mut p = Parser::new("ref x @ Public");
    match p.parse_expr().unwrap() {
        Expr::Ref(e, level) => {
            assert_eq!(*e, Expr::Var("x".to_string()));
            assert_eq!(level, SecurityLevel::Public);
        }
        other => panic!("Expected Ref, got {:?}", other),
    }
}

#[test]
fn test_parse_deref_simple() {
    // Input: Dereference expression
    // Expected: Expr::Deref
    // Rationale: Dereferencing references
    let mut p = Parser::new("!r");
    match p.parse_expr().unwrap() {
        Expr::Deref(e) => {
            assert_eq!(*e, Expr::Var("r".to_string()));
        }
        other => panic!("Expected Deref, got {:?}", other),
    }
}

#[test]
fn test_parse_deref_chain() {
    // Input: Chained dereference
    // Expected: Nested Expr::Deref
    // Rationale: Multiple levels of indirection
    let mut p = Parser::new("!!r");
    match p.parse_expr().unwrap() {
        Expr::Deref(e) => match *e {
            Expr::Deref(inner) => {
                assert_eq!(*inner, Expr::Var("r".to_string()));
            }
            other => panic!("Expected inner Deref, got {:?}", other),
        },
        other => panic!("Expected Deref, got {:?}", other),
    }
}

// =============================================================================
// ASSIGNMENT TESTS
// =============================================================================

#[test]
fn test_parse_assign_to_deref() {
    // Input: Assignment to dereferenced value
    // Expected: Expr::Assign with Deref on LHS
    // Rationale: Mutable reference semantics
    let mut p = Parser::new("!r := 42");
    match p.parse_expr().unwrap() {
        Expr::Assign(lhs, rhs) => {
            match *lhs {
                Expr::Deref(inner) => {
                    assert_eq!(*inner, Expr::Var("r".to_string()));
                }
                other => panic!("Expected Deref, got {:?}", other),
            }
            assert_eq!(*rhs, Expr::Int(42));
        }
        other => panic!("Expected Assign, got {:?}", other),
    }
}

// =============================================================================
// SECURITY TESTS
// =============================================================================

#[test]
fn test_parse_classify_literal() {
    // Input: Classify a literal
    // Expected: Expr::Classify
    // Rationale: Lifting values to secret
    let mut p = Parser::new("classify 42");
    match p.parse_expr().unwrap() {
        Expr::Classify(e) => {
            assert_eq!(*e, Expr::Int(42));
        }
        other => panic!("Expected Classify, got {:?}", other),
    }
}

#[test]
fn test_parse_prove_literal() {
    // Input: Prove a literal
    // Expected: Expr::Prove
    // Rationale: Creating proofs
    let mut p = Parser::new("prove true");
    match p.parse_expr().unwrap() {
        Expr::Prove(e) => {
            assert_eq!(*e, Expr::Bool(true));
        }
        other => panic!("Expected Prove, got {:?}", other),
    }
}

#[test]
fn test_parse_declassify_with_var_proof() {
    // Input: Declassify with variable proof
    // Expected: Expr::Declassify
    // Rationale: Declassification with proof witness
    let mut p = Parser::new("declassify secret_val with my_proof");
    match p.parse_expr().unwrap() {
        Expr::Declassify(val, proof) => {
            assert_eq!(*val, Expr::Var("secret_val".to_string()));
            assert_eq!(*proof, Expr::Var("my_proof".to_string()));
        }
        other => panic!("Expected Declassify, got {:?}", other),
    }
}

// =============================================================================
// MATCH/CASE TESTS
// =============================================================================

#[test]
fn test_parse_match_without_trailing_comma() {
    // Input: Match without trailing comma
    // Expected: Expr::Case
    // Rationale: Trailing comma is optional
    let mut p = Parser::new("match x { inl a => 1, inr b => 2 }");
    match p.parse_expr().unwrap() {
        Expr::Case(e, x, e1, y, e2) => {
            assert_eq!(*e, Expr::Var("x".to_string()));
            assert_eq!(x, "a");
            assert_eq!(*e1, Expr::Int(1));
            assert_eq!(y, "b");
            assert_eq!(*e2, Expr::Int(2));
        }
        other => panic!("Expected Case, got {:?}", other),
    }
}

#[test]
fn test_parse_match_with_complex_branches() {
    // Input: Match with complex branch expressions
    // Expected: Expr::Case with Pair in branch
    // Rationale: Any expression in branches
    let mut p = Parser::new("match sum { inl x => (x, x), inr y => (y, y) }");
    match p.parse_expr().unwrap() {
        Expr::Case(e, x, e1, y, e2) => {
            assert_eq!(*e, Expr::Var("sum".to_string()));
            assert_eq!(x, "x");
            match *e1 {
                Expr::Pair(ref a, ref b) => {
                    assert_eq!(**a, Expr::Var("x".to_string()));
                    assert_eq!(**b, Expr::Var("x".to_string()));
                }
                ref other => panic!("Expected Pair in first branch, got {:?}", other),
            }
            assert_eq!(y, "y");
            match *e2 {
                Expr::Pair(ref a, ref b) => {
                    assert_eq!(**a, Expr::Var("y".to_string()));
                    assert_eq!(**b, Expr::Var("y".to_string()));
                }
                ref other => panic!("Expected Pair in second branch, got {:?}", other),
            }
        }
        other => panic!("Expected Case, got {:?}", other),
    }
}

// =============================================================================
// ERROR CASE TESTS
// =============================================================================

#[test]
fn test_error_unexpected_eof_in_let() {
    // Input: Incomplete let expression
    // Expected: ParseError::UnexpectedEof
    // Rationale: Must detect incomplete expressions
    let mut p = Parser::new("let x =");
    let result = p.parse_expr();
    assert!(result.is_err(), "Incomplete let must produce error");
}

#[test]
fn test_if_without_else_is_guard() {
    // `if c { e }` with no `else` is now valid: it is a statement-position guard
    // (e.g. `kalau c { pulang x; }`). It parses to an `If` whose branches are
    // both Unit-typed (the then-value is discarded), so the construct yields
    // Unit. (Previously an else branch was mandatory.)
    let mut p = Parser::new("if true { 1 }");
    match p.parse_expr().unwrap() {
        Expr::If(_, _, else_branch) => assert_eq!(*else_branch, Expr::Unit),
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn test_error_missing_closing_brace() {
    // Input: Missing closing brace in if
    // Expected: ParseError
    // Rationale: Must detect mismatched braces
    let mut p = Parser::new("if true { 1 else { 2 }");
    let result = p.parse_expr();
    assert!(result.is_err(), "Missing brace must produce error");
}

#[test]
fn test_error_empty_input() {
    // Input: Empty input
    // Expected: ParseError::UnexpectedEof
    // Rationale: Empty input not valid expression
    let mut p = Parser::new("");
    let result = p.parse_expr();
    assert!(result.is_err(), "Empty input must produce error");
}

#[test]
fn test_error_invalid_security_level() {
    // Input: Invalid security level name
    // Expected: ParseError::InvalidSecurityLevel
    // Rationale: Only Public/Secret are valid
    let mut p = Parser::new("ref 1 @ Invalid");
    let result = p.parse_expr();
    assert!(result.is_err(), "Invalid security level must produce error");
}

#[test]
fn test_error_invalid_effect() {
    // Input: Invalid effect name
    // Expected: ParseError::InvalidEffect
    // Rationale: Only defined effects are valid
    let mut p = Parser::new("perform Invalid 1");
    let result = p.parse_expr();
    assert!(result.is_err(), "Invalid effect must produce error");
}

#[test]
fn test_error_missing_colon_in_lambda() {
    // Input: Lambda missing colon before type
    // Expected: ParseError
    // Rationale: Type annotation requires colon
    let mut p = Parser::new("fn(x Int) x");
    let result = p.parse_expr();
    assert!(result.is_err(), "Lambda missing colon must produce error");
}

#[test]
fn test_error_missing_type_in_inl() {
    // Input: inl missing type annotation
    // Expected: ParseError
    // Rationale: Sum injections require type
    let mut p = Parser::new("inl 1");
    let result = p.parse_expr();
    assert!(result.is_err(), "inl without type must produce error");
}

#[test]
fn dedah_call_form_parses_to_the_same_ast_as_canonical() {
    // REQ-55: `dedah(e, p)` and `dedah e dengan p` are ONE AST node — the same
    // Expr::Declassify — so the mechanized T_Declassify covers both and the
    // call-form adds surface, not semantics.
    let call = Parser::new("dedah(x, bukti_x)").parse_expr().unwrap();
    let canon = Parser::new("dedah x dengan bukti_x").parse_expr().unwrap();
    assert_eq!(
        call, canon,
        "the two dedah surface forms must be indistinguishable downstream"
    );
}

#[test]
fn dedah_call_form_negative_controls() {
    // Missing comma / unclosed paren still fail loudly — the sugar must not
    // have made the parser lenient.
    assert!(Parser::new("dedah(x bukti_x)").parse_expr().is_err());
    assert!(Parser::new("dedah(x, bukti_x").parse_expr().is_err());
}

#[test]
fn test_error_missing_with_in_declassify() {
    // Input: declassify without 'with'
    // Expected: ParseError
    // Rationale: declassify requires proof
    let mut p = Parser::new("declassify x proof");
    let result = p.parse_expr();
    assert!(
        result.is_err(),
        "declassify without 'with' must produce error"
    );
}

// =============================================================================
// EDGE CASE TESTS
// =============================================================================

#[test]
fn test_parse_deeply_nested_if() {
    // Input: Deeply nested if expressions
    // Expected: Correctly nested Expr::If
    // Rationale: Arbitrary nesting depth
    let input = "if a { if b { if c { 1 } else { 2 } } else { 3 } } else { 4 }";
    let mut p = Parser::new(input);
    let result = p.parse_expr();
    assert!(result.is_ok(), "Deep nesting must parse");
}

#[test]
fn test_parse_deeply_nested_let() {
    // Input: Deeply nested let expressions
    // Expected: Correctly nested Expr::Let
    // Rationale: Arbitrary let nesting
    let input = "let a = 1; let b = 2; let c = 3; let d = 4; d";
    let mut p = Parser::new(input);
    let result = p.parse_expr();
    assert!(result.is_ok(), "Deeply nested let must parse");
}

#[test]
fn test_parse_long_application_chain() {
    // Input: Long chain of applications
    // Expected: Left-associative App chain
    // Rationale: Arbitrary application length
    let mut p = Parser::new("a b c d e f");
    let result = p.parse_expr();
    assert!(result.is_ok(), "Long application chain must parse");
}

#[test]
fn test_parse_complex_combined_expression() {
    // Input: Complex expression combining multiple forms
    // Expected: Valid Expr
    // Rationale: All forms must compose
    let input = "let f = fn(x: Int) x; f 42";
    let mut p = Parser::new(input);
    let result = p.parse_expr();
    assert!(result.is_ok(), "Complex combined expression must parse");

    match result.unwrap() {
        Expr::Let(name, _, bound, body) => {
            assert_eq!(name, "f");
            // bound should be Lam
            match *bound {
                Expr::Lam(_, _, _) => {}
                other => panic!("Expected Lam, got {:?}", other),
            }
            // body should be App
            match *body {
                Expr::App(_, _) => {}
                other => panic!("Expected App, got {:?}", other),
            }
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_unicode_identifier() {
    // Input: Unicode variable name
    // Expected: Expr::Var with unicode
    // Rationale: Unicode identifiers supported
    let mut p = Parser::new("变量");
    match p.parse_expr().unwrap() {
        Expr::Var(name) => {
            assert_eq!(name, "变量");
        }
        other => panic!("Expected Var, got {:?}", other),
    }
}

#[test]
fn test_parse_bahasa_melayu_keyword_in_context() {
    // Input: Bahasa Melayu keywords
    // Expected: Correct parsing with BM keywords
    // Rationale: Full Bahasa Melayu support
    let mut p = Parser::new("kalau betul { 1 } else { 0 }");
    match p.parse_expr().unwrap() {
        Expr::If(cond, e1, e2) => {
            assert_eq!(*cond, Expr::Bool(true));
            assert_eq!(*e1, Expr::Int(1));
            assert_eq!(*e2, Expr::Int(0));
        }
        other => panic!("Expected If, got {:?}", other),
    }
}

#[test]
fn test_parse_biar_keyword() {
    // Input: Bahasa Melayu 'biar' (let)
    // Expected: Expr::Let
    // Rationale: Native language keywords work
    let mut p = Parser::new("biar x = 1; x");
    match p.parse_expr().unwrap() {
        Expr::Let(name, _, bound, body) => {
            assert_eq!(name, "x");
            assert_eq!(*bound, Expr::Int(1));
            assert_eq!(*body, Expr::Var("x".to_string()));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_fungsi_keyword() {
    // Input: Bahasa Melayu 'fungsi' (fn)
    // Expected: Expr::Lam
    // Rationale: Native language function keyword
    let mut p = Parser::new("fungsi(x: Int) x");
    match p.parse_expr().unwrap() {
        Expr::Lam(param, ty, body) => {
            assert_eq!(param, "x");
            assert_eq!(ty, Ty::Int);
            assert_eq!(*body, Expr::Var("x".to_string()));
        }
        other => panic!("Expected Lam, got {:?}", other),
    }
}

// =============================================================================
// BINARY OPERATOR TESTS
// =============================================================================

#[test]
fn test_parse_binop_add() {
    let mut p = Parser::new("1 + 2");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::BinOp(BinOp::Add, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)))
    );
}

#[test]
fn test_parse_binop_precedence_mul_over_add() {
    // 1 + 2 * 3 => Add(1, Mul(2, 3))
    let mut p = Parser::new("1 + 2 * 3");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Int(1)),
            Box::new(Expr::BinOp(
                BinOp::Mul,
                Box::new(Expr::Int(2)),
                Box::new(Expr::Int(3))
            ))
        )
    );
}

#[test]
fn test_parse_binop_comparison() {
    let mut p = Parser::new("1 == 2");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::BinOp(BinOp::Eq, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)))
    );
}

#[test]
fn test_parse_binop_logical_precedence() {
    // a && b || c => Or(And(a, b), c)
    let mut p = Parser::new("a && b || c");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::BinOp(
            BinOp::Or,
            Box::new(Expr::BinOp(
                BinOp::And,
                Box::new(Expr::Var("a".to_string())),
                Box::new(Expr::Var("b".to_string()))
            )),
            Box::new(Expr::Var("c".to_string()))
        )
    );
}

#[test]
fn test_parse_binop_left_associative() {
    // 1 - 2 - 3 => Sub(Sub(1, 2), 3)
    let mut p = Parser::new("1 - 2 - 3");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::BinOp(
            BinOp::Sub,
            Box::new(Expr::BinOp(
                BinOp::Sub,
                Box::new(Expr::Int(1)),
                Box::new(Expr::Int(2))
            )),
            Box::new(Expr::Int(3))
        )
    );
}

#[test]
fn test_parse_binop_with_parens() {
    // (1 + 2) * 3 => Mul(Add(1, 2), 3)
    let mut p = Parser::new("(1 + 2) * 3");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::BinOp(
                BinOp::Add,
                Box::new(Expr::Int(1)),
                Box::new(Expr::Int(2))
            )),
            Box::new(Expr::Int(3))
        )
    );
}

#[test]
fn test_parse_binop_comparison_ops() {
    for (src, op) in [
        ("1 < 2", BinOp::Lt),
        ("1 > 2", BinOp::Gt),
        ("1 <= 2", BinOp::Le),
        ("1 >= 2", BinOp::Ge),
        ("1 != 2", BinOp::Ne),
    ] {
        let mut p = Parser::new(src);
        assert_eq!(
            p.parse_expr().unwrap(),
            Expr::BinOp(op, Box::new(Expr::Int(1)), Box::new(Expr::Int(2))),
            "Failed for: {}",
            src
        );
    }
}

#[test]
fn test_parse_binop_all_arithmetic() {
    for (src, op) in [
        ("1 + 2", BinOp::Add),
        ("1 - 2", BinOp::Sub),
        ("1 * 2", BinOp::Mul),
        ("1 / 2", BinOp::Div),
        ("1 % 2", BinOp::Mod),
    ] {
        let mut p = Parser::new(src);
        assert_eq!(
            p.parse_expr().unwrap(),
            Expr::BinOp(op, Box::new(Expr::Int(1)), Box::new(Expr::Int(2))),
            "Failed for: {}",
            src
        );
    }
}

#[test]
fn test_parse_binop_in_let() {
    // let x = 2 + 3; x
    let mut p = Parser::new("let x = 2 + 3; x");
    match p.parse_expr().unwrap() {
        Expr::Let(name, _, bound, body) => {
            assert_eq!(name, "x");
            assert_eq!(
                *bound,
                Expr::BinOp(BinOp::Add, Box::new(Expr::Int(2)), Box::new(Expr::Int(3)))
            );
            assert_eq!(*body, Expr::Var("x".to_string()));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

// ====================================================================
// Statement Sequence Tests (§5.3.1)
// ====================================================================

#[test]
fn test_parse_stmt_sequence_simple() {
    let mut p = Parser::new("42; 10");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Let(name, _, e1, e2) => {
            assert_eq!(name, "_");
            assert_eq!(*e1, Expr::Int(42));
            assert_eq!(*e2, Expr::Int(10));
        }
        other => panic!("Expected Let(\"_\", ...), got {:?}", other),
    }
}

#[test]
fn test_parse_stmt_sequence_multi() {
    let mut p = Parser::new("1; 2; 3");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Let(n1, _, e1, rest) => {
            assert_eq!(n1, "_");
            assert_eq!(*e1, Expr::Int(1));
            match *rest {
                Expr::Let(n2, _, e2, e3) => {
                    assert_eq!(n2, "_");
                    assert_eq!(*e2, Expr::Int(2));
                    assert_eq!(*e3, Expr::Int(3));
                }
                other => panic!("Expected inner Let, got {:?}", other),
            }
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_stmt_sequence_with_let() {
    let mut p = Parser::new("biar x = 1; biar y = 2; x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Let(n1, _, _, rest) => {
            assert_eq!(n1, "x");
            match *rest {
                Expr::Let(n2, _, _, body) => {
                    assert_eq!(n2, "y");
                    assert_eq!(*body, Expr::Var("x".to_string()));
                }
                other => panic!("Expected inner Let, got {:?}", other),
            }
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_stmt_sequence_mixed() {
    let mut p = Parser::new("biar x = 1; 42; x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Let(name, _, _, rest) => {
            assert_eq!(name, "x");
            match *rest {
                Expr::Let(n2, _, e, body) => {
                    assert_eq!(n2, "_");
                    assert_eq!(*e, Expr::Int(42));
                    assert_eq!(*body, Expr::Var("x".to_string()));
                }
                other => panic!("Expected Let(\"_\", ...), got {:?}", other),
            }
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

// ====================================================================
// Top-Level Declaration Tests (§5.3.2)
// ====================================================================

#[test]
fn test_parse_program_single_expr() {
    let mut p = Parser::new("42");
    let prog = p.parse_program().unwrap();
    assert_eq!(prog.decls.len(), 1);
    match &prog.decls[0] {
        TopLevelDecl::Expr(e) => assert_eq!(**e, Expr::Int(42)),
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_program_function_decl() {
    let mut p = Parser::new("fn f(x: Int) -> Int { x }");
    let prog = p.parse_program().unwrap();
    assert_eq!(prog.decls.len(), 1);
    match &prog.decls[0] {
        TopLevelDecl::Function {
            name,
            params,
            return_ty,
            ..
        } => {
            assert_eq!(name, "f");
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "x");
            assert_eq!(params[0].1, Ty::Int);
            assert_eq!(*return_ty, Ty::Int);
        }
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_program_multi_param_function() {
    let mut p = Parser::new("fn add(x: Int, y: Int) -> Int { x + y }");
    let prog = p.parse_program().unwrap();
    assert_eq!(prog.decls.len(), 1);
    match &prog.decls[0] {
        TopLevelDecl::Function { name, params, .. } => {
            assert_eq!(name, "add");
            assert_eq!(params.len(), 2);
        }
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_program_desugar() {
    let mut p = Parser::new("fn f(x: Int) -> Int { x } f 42");
    let prog = p.parse_program().unwrap();
    assert_eq!(prog.decls.len(), 2);
    let desugared = prog.desugar();
    // Top-level functions now form a mutually-recursive GROUP (REQ-44 forward
    // references), so a single function `f` desugars to
    // LetRecGroup([("f", .., Lam("x", Int, Var "x"))], App(Var "f", Int 42)).
    match desugared {
        Expr::LetRecGroup(bindings, body) => {
            assert_eq!(bindings.len(), 1);
            let (name, _ty, lam) = &bindings[0];
            assert_eq!(name, "f");
            match lam {
                Expr::Lam(p, ty, _) => {
                    assert_eq!(p, "x");
                    assert_eq!(*ty, Ty::Int);
                }
                other => panic!("Expected Lam, got {:?}", other),
            }
            match body.as_ref() {
                Expr::App(_, _) => {}
                other => panic!("Expected App, got {:?}", other),
            }
        }
        other => panic!("Expected LetRecGroup, got {:?}", other),
    }
}

// ====================================================================
// Extended Type Parsing Tests (§5.3.8)
// ====================================================================

#[test]
fn test_parse_ty_list() {
    let mut p = Parser::new("fn(x: List<Int>) x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Lam(_, ty, _) => assert_eq!(ty, Ty::List(Box::new(Ty::Int))),
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_ty_option() {
    let mut p = Parser::new("fn(x: Option<Bool>) x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Lam(_, ty, _) => assert_eq!(ty, Ty::Option(Box::new(Ty::Bool))),
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_ty_secret() {
    let mut p = Parser::new("fn(x: Secret<String>) x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Lam(_, ty, _) => assert_eq!(ty, Ty::Secret(Box::new(Ty::String))),
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_ty_prod() {
    let mut p = Parser::new("fn(x: (Int, Bool)) x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Lam(_, ty, _) => assert_eq!(ty, Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Bool))),
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_ty_sum() {
    let mut p = Parser::new("fn(x: Sum<Int, Bool>) x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Lam(_, ty, _) => assert_eq!(ty, Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool))),
        other => panic!("Expected Lam, got {:?}", other),
    }
}

#[test]
fn test_parse_ty_nested() {
    // Note: space before >> to avoid lexing as Shr token
    let mut p = Parser::new("fn(x: List<Option<Int> >) x");
    let result = p.parse_expr().unwrap();
    match result {
        Expr::Lam(_, ty, _) => assert_eq!(ty, Ty::List(Box::new(Ty::Option(Box::new(Ty::Int))))),
        other => panic!("Expected Lam, got {:?}", other),
    }
}

// ====================================================================
// Guard Clause Tests (§5.3.4)
// ====================================================================

#[test]
fn test_parse_guard_simple() {
    // guard x else { 0 }; 42
    // desugars to If(Var("x"), Int(42), Int(0))
    let mut p = Parser::new("guard x else { 0 }; 42");
    let result = p.parse_expr().unwrap();
    assert_eq!(
        result,
        Expr::If(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Int(42)),
            Box::new(Expr::Int(0)),
        )
    );
}

#[test]
fn test_parse_guard_bahasa() {
    // pastikan x lain { 0 }; 42
    let mut p = Parser::new("pastikan x lain { 0 }; 42");
    let result = p.parse_expr().unwrap();
    assert_eq!(
        result,
        Expr::If(
            Box::new(Expr::Var("x".to_string())),
            Box::new(Expr::Int(42)),
            Box::new(Expr::Int(0)),
        )
    );
}

// ====================================================================
// Pipe Operator Tests (§5.3.3)
// ====================================================================

#[test]
fn test_parse_pipe_simple() {
    // x |> f  desugars to App(f, x)
    let mut p = Parser::new("x |> f");
    let result = p.parse_expr().unwrap();
    assert_eq!(
        result,
        Expr::App(
            Box::new(Expr::Var("f".to_string())),
            Box::new(Expr::Var("x".to_string())),
        )
    );
}

#[test]
fn test_parse_pipe_chain() {
    // x |> f |> g  desugars to App(g, App(f, x))
    let mut p = Parser::new("x |> f |> g");
    let result = p.parse_expr().unwrap();
    assert_eq!(
        result,
        Expr::App(
            Box::new(Expr::Var("g".to_string())),
            Box::new(Expr::App(
                Box::new(Expr::Var("f".to_string())),
                Box::new(Expr::Var("x".to_string())),
            )),
        )
    );
}

#[test]
fn test_parse_pipe_with_literal() {
    // 42 |> f
    let mut p = Parser::new("42 |> f");
    let result = p.parse_expr().unwrap();
    assert_eq!(
        result,
        Expr::App(
            Box::new(Expr::Var("f".to_string())),
            Box::new(Expr::Int(42)),
        )
    );
}

#[test]
fn test_parse_program_binding() {
    let mut p = Parser::new("biar x = 42; x");
    let prog = p.parse_program().unwrap();
    assert_eq!(prog.decls.len(), 2);
    match &prog.decls[0] {
        TopLevelDecl::Binding { name, .. } => assert_eq!(name, "x"),
        other => panic!("Expected Binding, got {:?}", other),
    }
    match &prog.decls[1] {
        TopLevelDecl::Expr(e) => assert_eq!(**e, Expr::Var("x".to_string())),
        other => panic!("Expected Expr, got {:?}", other),
    }
}

// =============================================================================
// BM EFFECT NAME TESTS
// =============================================================================

#[test]
fn test_parse_bm_effect_tulis() {
    let mut p = Parser::new("fungsi cetak() -> Unit kesan Tulis { 0 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Write),
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_bm_effect_bersih() {
    let mut p = Parser::new("fungsi murni() -> Int kesan Bersih { 42 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Pure),
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_bm_effect_baca() {
    let mut p = Parser::new("fungsi baca() -> Int kesan Baca { 0 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Read),
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_bm_effect_rangkaian() {
    let mut p = Parser::new("fungsi net_test() -> Unit kesan Rangkaian { 0 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Network),
        other => panic!("Expected Function, got {:?}", other),
    }
}

// =============================================================================
// BM SECURITY LEVEL TESTS
// =============================================================================

#[test]
fn test_parse_bm_security_level_awam() {
    let mut p = Parser::new("Ref<Int>@Awam");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Ref(Box::new(Ty::Int), SecurityLevel::Public));
}

#[test]
fn test_parse_bm_security_level_rahsia() {
    let mut p = Parser::new("Ref<Bool>@Rahsia");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Ref(Box::new(Ty::Bool), SecurityLevel::Secret));
}

// =============================================================================
// NEW TYPE VARIANT TESTS
// =============================================================================

#[test]
fn test_parse_fn_type() {
    let mut p = Parser::new("Fn(Int, Bool)");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Pure)
    );
}

#[test]
fn test_parse_fn_type_with_effect() {
    let mut p = Parser::new("Fn(Int, Bool, Write)");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Write)
    );
}

#[test]
fn test_parse_labeled_type() {
    let mut p = Parser::new("Labeled<Int, Secret>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Labeled(Box::new(Ty::Int), SecurityLevel::Secret));
}

#[test]
fn test_parse_berlabel_type() {
    let mut p = Parser::new("Berlabel<Teks, Awam>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Labeled(Box::new(Ty::String), SecurityLevel::Public));
}

#[test]
fn test_parse_capability_type() {
    let mut p = Parser::new("Capability<FileRead>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Capability(riina_types::CapabilityKind::FileRead));
}

#[test]
fn test_parse_smart_contract_type_keyword() {
    let mut p = Parser::new("kontrak_pintar<Nombor>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::SmartContract(Box::new(Ty::Int)));
}

#[test]
fn test_parse_smart_contract_type_pascal_case() {
    let mut p = Parser::new("SmartContract<Int>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::SmartContract(Box::new(Ty::Int)));
}

#[test]
fn test_parse_token_type_keyword() {
    let mut p = Parser::new("token<Teks>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Token(Box::new(Ty::String)));
}

#[test]
fn test_parse_syariah_compliant_type_keyword() {
    let mut p = Parser::new("patuh_syariah<Bool>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::SyariahCompliant(Box::new(Ty::Bool)));
}

#[test]
fn test_parse_unknown_type_is_nominal_any() {
    // User-defined nominal types (e.g. `jenis`-declared records) have no nominal
    // semantics yet, so an unknown type name parses as the structural `Any` type
    // rather than erroring. This mirrors the top-level `jenis` skip.
    let mut p = Parser::new("FooBarBaz");
    assert_eq!(p.parse_ty().unwrap(), Ty::Any);
}

#[test]
fn test_parse_unknown_generic_type_is_any() {
    // Generic argument lists on unknown nominal types are consumed and discarded.
    // (Names like `Keupayaan` are *known* parameterized types with their own
    // argument grammar, so they are intentionally not covered here.)
    for src in [
        "JejakAudit<Teks>",
        "Hasil<Rahsia<Teks>, Teks>",
        "MyMap<K, List<V>>",
    ] {
        let mut p = Parser::new(src);
        assert_eq!(p.parse_ty().unwrap(), Ty::Any, "should parse `{src}` as Any");
    }
}

// =============================================================================
// PROJECTION TESTS (fst / snd)
// =============================================================================

#[test]
fn test_parse_fst() {
    let mut p = Parser::new("fst x");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Fst(Box::new(Expr::Var("x".to_string()))));
}

#[test]
fn test_parse_snd() {
    let mut p = Parser::new("snd x");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Snd(Box::new(Expr::Var("x".to_string()))));
}

#[test]
fn test_parse_fst_bm() {
    let mut p = Parser::new("pertama x");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Fst(Box::new(Expr::Var("x".to_string()))));
}

#[test]
fn test_parse_snd_bm() {
    let mut p = Parser::new("kedua x");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Snd(Box::new(Expr::Var("x".to_string()))));
}

// =============================================================================
// CAPABILITY REQUIRE/GRANT TESTS
// =============================================================================

#[test]
fn test_parse_require() {
    let mut p = Parser::new("require Write 42");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Require(Effect::Write, Box::new(Expr::Int(42))));
}

#[test]
fn test_parse_grant() {
    let mut p = Parser::new("grant Network 0");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Grant(Effect::Network, Box::new(Expr::Int(0))));
}

#[test]
fn test_parse_grant_wraps_full_application() {
    let mut p = Parser::new("grant Network f x");
    let expr = p.parse_expr().unwrap();
    assert_eq!(
        expr,
        Expr::Grant(
            Effect::Network,
            Box::new(Expr::App(
                Box::new(Expr::Var("f".to_string())),
                Box::new(Expr::Var("x".to_string())),
            )),
        )
    );
}

#[test]
fn test_parse_grant_zero_arg_call_stays_inside_body() {
    // The point of this test is SCOPE: the call sits inside the grant body, so
    // the capability covers it. The call itself is a real application to `()`
    // now that a zero-parameter function is a real function (REQ-68); it used
    // to parse to a bare `Var` because the empty parens were a no-op suffix.
    let mut p = Parser::new("grant Network f()");
    let expr = p.parse_expr().unwrap();
    assert_eq!(
        expr,
        Expr::Grant(
            Effect::Network,
            Box::new(Expr::App(
                Box::new(Expr::Var("f".to_string())),
                Box::new(Expr::Unit)
            ))
        )
    );
}

#[test]
fn test_parse_require_bm() {
    let mut p = Parser::new("perlukan Tulis 42");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Require(Effect::Write, Box::new(Expr::Int(42))));
}

#[test]
fn test_parse_grant_bm() {
    let mut p = Parser::new("beri Rangkaian 0");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::Grant(Effect::Network, Box::new(Expr::Int(0))));
}

// =============================================================================
// FFI / EXTERN BLOCK TESTS
// =============================================================================

#[test]
fn test_parse_extern_block_single() {
    let src = r#"luaran "C" { fungsi puts(s: *CChar) -> CInt; }"#;
    let mut p = Parser::new(src);
    let program = p.parse_program().unwrap();
    assert_eq!(program.decls.len(), 1);
    match &program.decls[0] {
        TopLevelDecl::ExternBlock { abi, decls } => {
            assert_eq!(abi, "C");
            assert_eq!(decls.len(), 1);
            assert_eq!(decls[0].name, "puts");
            assert_eq!(decls[0].params.len(), 1);
            assert_eq!(decls[0].params[0].0, "s");
            assert_eq!(decls[0].params[0].1, Ty::RawPtr(Box::new(Ty::CChar)));
            assert_eq!(decls[0].ret_ty, Ty::CInt);
        }
        _ => panic!("Expected ExternBlock"),
    }
}

#[test]
fn test_parse_extern_block_multiple() {
    let src = r#"luaran "C" {
        fungsi abs(x: CInt) -> CInt;
        fungsi rand() -> CInt;
    }"#;
    let mut p = Parser::new(src);
    let program = p.parse_program().unwrap();
    assert_eq!(program.decls.len(), 1);
    match &program.decls[0] {
        TopLevelDecl::ExternBlock { abi, decls } => {
            assert_eq!(abi, "C");
            assert_eq!(decls.len(), 2);
            assert_eq!(decls[0].name, "abs");
            assert_eq!(decls[1].name, "rand");
            assert_eq!(decls[1].params.len(), 0);
        }
        _ => panic!("Expected ExternBlock"),
    }
}

#[test]
fn test_parse_extern_block_english() {
    let src = r#"extern "C" { fn getpid() -> CInt; }"#;
    let mut p = Parser::new(src);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::ExternBlock { abi, decls } => {
            assert_eq!(abi, "C");
            assert_eq!(decls.len(), 1);
            assert_eq!(decls[0].name, "getpid");
        }
        _ => panic!("Expected ExternBlock"),
    }
}

#[test]
fn test_parse_raw_ptr_type() {
    let src = r#"luaran "C" { fungsi malloc(n: CInt) -> *CVoid; }"#;
    let mut p = Parser::new(src);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::ExternBlock { decls, .. } => {
            assert_eq!(decls[0].ret_ty, Ty::RawPtr(Box::new(Ty::CVoid)));
        }
        _ => panic!("Expected ExternBlock"),
    }
}

#[test]
fn test_parse_c_types() {
    let src = r#"luaran "C" { fungsi semak(a: CInt, b: CChar, c: CVoid) -> CInt; }"#;
    let mut p = Parser::new(src);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::ExternBlock { decls, .. } => {
            assert_eq!(decls[0].params[0].1, Ty::CInt);
            assert_eq!(decls[0].params[1].1, Ty::CChar);
            assert_eq!(decls[0].params[2].1, Ty::CVoid);
        }
        _ => panic!("Expected ExternBlock"),
    }
}

// =============================================================================
// EFFECT::MUT AND EFFECT::ALLOC TESTS (P5 Self-Hosting)
// =============================================================================

#[test]
fn test_parse_effect_mut_english() {
    let mut p = Parser::new("fungsi mutate() -> Int kesan Mut { 42 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Mut),
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_effect_mut_bm() {
    let mut p = Parser::new("fungsi ubah_nilai() -> Int kesan Ubah { 42 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Mut),
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_effect_alloc_english() {
    let mut p = Parser::new("fungsi allocate() -> Int kesan Alloc { 0 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Alloc),
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_effect_alloc_bm() {
    let mut p = Parser::new("fungsi peruntuk() -> Int kesan Peruntuk { 0 }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { effect, .. } => assert_eq!(*effect, Effect::Alloc),
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_fn_type_with_effect_mut() {
    let mut p = Parser::new("Fn(Int, Bool, Mut)");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Mut)
    );
}

#[test]
fn test_parse_fn_type_with_effect_alloc() {
    let mut p = Parser::new("Fn(Int, Bool, Alloc)");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Alloc)
    );
}

// ── A4: Session type parsing ──

#[test]
fn test_parse_chan_end() {
    let mut p = Parser::new("Chan<End>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Chan(SessionType::End));
}

#[test]
fn test_parse_chan_send_recv() {
    // Space-separated > to avoid >> being lexed as Shr
    let mut p = Parser::new("Chan<Send<Int, Recv<Bool, End> > >");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Chan(SessionType::Send(
            Box::new(Ty::Int),
            Box::new(SessionType::Recv(
                Box::new(Ty::Bool),
                Box::new(SessionType::End)
            ))
        ))
    );
}

#[test]
fn test_parse_secure_chan() {
    let mut p = Parser::new("SecureChan<Send<Int, End>, Secret>");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::SecureChan(
            SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End)),
            SecurityLevel::Secret
        )
    );
}

#[test]
fn test_parse_session_select_branch() {
    let mut p = Parser::new("Chan<Select<Send<Int, End>, Send<Bool, End> > >");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Chan(SessionType::Select(
            Box::new(SessionType::Send(
                Box::new(Ty::Int),
                Box::new(SessionType::End)
            )),
            Box::new(SessionType::Send(
                Box::new(Ty::Bool),
                Box::new(SessionType::End)
            ))
        ))
    );
}

#[test]
fn test_parse_session_recursive() {
    // Chan<Rec<X, Send<Int, SVar<X> > > >
    let mut p = Parser::new("Chan<Rec<X, Send<Int, SVar<X> > > >");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Chan(SessionType::Rec(
            "X".into(),
            Box::new(SessionType::Send(
                Box::new(Ty::Int),
                Box::new(SessionType::Var("X".into()))
            ))
        ))
    );
}

#[test]
fn test_parse_chan_malay_syntax() {
    // Saluran<Hantar<Nombor, Terima<Benar, Tamat> > >
    let mut p = Parser::new("Saluran<Hantar<Nombor, Terima<Benar, Tamat> > >");
    let ty = p.parse_ty().unwrap();
    assert_eq!(
        ty,
        Ty::Chan(SessionType::Send(
            Box::new(Ty::Int),
            Box::new(SessionType::Recv(
                Box::new(Ty::Bool),
                Box::new(SessionType::End)
            ))
        ))
    );
}

#[test]
fn test_parse_invalid_session_type() {
    let mut p = Parser::new("Chan<InvalidST>");
    let result = p.parse_ty();
    assert!(result.is_err());
}

#[test]
fn test_parse_let_sekali() {
    use riina_types::Linearity;
    let mut p = Parser::new("biar sekali x = 1; x");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Let(name, lin, _, _) => {
            assert_eq!(name, "x");
            assert_eq!(lin, Some(Linearity::Linear));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_let_paling() {
    use riina_types::Linearity;
    let mut p = Parser::new("biar paling y = 2; y");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Let(name, lin, _, _) => {
            assert_eq!(name, "y");
            assert_eq!(lin, Some(Linearity::Affine));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_let_mesti() {
    use riina_types::Linearity;
    let mut p = Parser::new("biar mesti z = 3; z");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Let(name, lin, _, _) => {
            assert_eq!(name, "z");
            assert_eq!(lin, Some(Linearity::Relevant));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_let_no_linearity() {
    let mut p = Parser::new("biar w = 4; w");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Let(name, lin, _, _) => {
            assert_eq!(name, "w");
            assert_eq!(lin, None);
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

// =============================================================================
// EDGE CASE TESTS — Nested, multi-function, linearity in functions
// =============================================================================

#[test]
fn test_parse_nested_if_else() {
    // Input: Nested conditional — if true { if false { 1 } else { 2 } } else { 3 }
    // Expected: Expr::If containing another Expr::If in the true branch
    // Rationale: Nested conditionals must parse correctly with proper nesting
    let mut p = Parser::new("kalau betul { kalau salah { 1 } lain { 2 } } lain { 3 }");
    match p.parse_expr().unwrap() {
        Expr::If(cond, then_br, else_br) => {
            assert_eq!(*cond, Expr::Bool(true));
            match *then_br {
                Expr::If(inner_cond, inner_then, inner_else) => {
                    assert_eq!(*inner_cond, Expr::Bool(false));
                    assert_eq!(*inner_then, Expr::Int(1));
                    assert_eq!(*inner_else, Expr::Int(2));
                }
                other => panic!("Expected nested If, got {:?}", other),
            }
            assert_eq!(*else_br, Expr::Int(3));
        }
        other => panic!("Expected If, got {:?}", other),
    }
}

#[test]
fn test_parse_nested_if_else_in_else_branch() {
    // Input: Nested conditional in else branch
    // Expected: Correct nesting of If expressions
    let mut p = Parser::new("kalau salah { 0 } lain { kalau betul { 1 } lain { 2 } }");
    match p.parse_expr().unwrap() {
        Expr::If(cond, then_br, else_br) => {
            assert_eq!(*cond, Expr::Bool(false));
            assert_eq!(*then_br, Expr::Int(0));
            match *else_br {
                Expr::If(inner_cond, inner_then, inner_else) => {
                    assert_eq!(*inner_cond, Expr::Bool(true));
                    assert_eq!(*inner_then, Expr::Int(1));
                    assert_eq!(*inner_else, Expr::Int(2));
                }
                other => panic!("Expected nested If in else, got {:?}", other),
            }
        }
        other => panic!("Expected If, got {:?}", other),
    }
}

#[test]
fn test_parse_multiple_functions() {
    // Input: Program with 3 top-level function declarations
    // Expected: 4 top-level decls (3 functions + 1 trailing expression)
    // Rationale: Multiple function definitions must parse independently
    let source = r#"
        fungsi satu() -> Nombor kesan Bersih { 1 }
        fungsi dua() -> Nombor kesan Bersih { 2 }
        fungsi tiga() -> Nombor kesan Bersih { 3 }
        satu()
    "#;
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    // 3 function decls + 1 expression
    assert!(
        program.decls.len() >= 4,
        "Expected at least 4 decls, got {}",
        program.decls.len()
    );
    // First three should be functions
    for i in 0..3 {
        match &program.decls[i] {
            TopLevelDecl::Function { .. } => {}
            other => panic!("Expected Function at index {}, got {:?}", i, other),
        }
    }
}

#[test]
fn test_parse_multiple_functions_with_params() {
    // Input: Program with functions that have parameters
    // Rationale: Parameterized functions followed by calls must parse
    let source =
        "fungsi tambah(a: Nombor, b: Nombor) -> Nombor kesan Bersih { a + b }\ntambah(1, 2)";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    assert_eq!(program.decls.len(), 2);
    match &program.decls[0] {
        TopLevelDecl::Function { name, params, .. } => {
            assert_eq!(name, "tambah");
            assert_eq!(params.len(), 2);
        }
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_linearity_in_function() {
    use riina_types::Linearity;
    // Input: Function body containing biar sekali (linear let)
    // Expected: Function with a Let(sekali) in the body
    // Rationale: Linearity qualifiers must work inside function bodies
    let source = "fungsi pakai() -> Nombor kesan Bersih { biar sekali x = 42; x }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Function { body, .. } => match body.as_ref() {
            Expr::Let(name, lin, val, _) => {
                assert_eq!(name, "x");
                assert_eq!(*lin, Some(Linearity::Linear));
                assert_eq!(**val, Expr::Int(42));
            }
            other => panic!("Expected Let in function body, got {:?}", other),
        },
        other => panic!("Expected Function, got {:?}", other),
    }
}

#[test]
fn test_parse_linearity_paling_in_function() {
    use riina_types::Linearity;
    // Input: Function body with biar paling (affine let)
    let source = "fungsi maybe() -> Nombor kesan Bersih { biar paling y = 10; y }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Function { body, .. } => match body.as_ref() {
            Expr::Let(name, lin, _, _) => {
                assert_eq!(name, "y");
                assert_eq!(*lin, Some(Linearity::Affine));
            }
            other => panic!("Expected Let in function body, got {:?}", other),
        },
        other => panic!("Expected Function, got {:?}", other),
    }
}

// =============================================================================
// JALINAN PHASE 6: CHOREOGRAPHY TESTS
// =============================================================================

#[test]
fn test_parse_choreography_basic() {
    let source = "koreografi Proto { peranan A, B; A -> B: hantar Msg; tamat; }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ChoreographyBlock {
                name,
                roles,
                protocol,
            } => {
                assert_eq!(name, "Proto");
                assert_eq!(roles, &["A".to_string(), "B".to_string()]);
                match protocol {
                    SessionType::Send(ty, cont) => {
                        assert_eq!(**ty, Ty::Any); // Msg → Any
                        assert_eq!(**cont, SessionType::End);
                    }
                    other => panic!("Expected Send, got {:?}", other),
                }
            }
            other => panic!("Expected ChoreographyBlock, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_choreography_multi_role() {
    let source = "koreografi Proto { peranan A, B, C; tamat; }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ChoreographyBlock {
                roles, protocol, ..
            } => {
                assert_eq!(roles.len(), 3);
                assert_eq!(roles[2], "C");
                assert_eq!(*protocol, SessionType::End);
            }
            other => panic!("Expected ChoreographyBlock, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_choreography_multi_interaction() {
    let source =
        "koreografi Proto { peranan A, B; A -> B: hantar Req; B -> A: hantar Resp; tamat; }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            // Viewpoint is roles[0] (A): `A -> B` is a Send, `B -> A` a Recv.
            Expr::ChoreographyBlock { protocol, .. } => match protocol {
                SessionType::Send(_, cont) => match cont.as_ref() {
                    SessionType::Recv(_, cont2) => {
                        assert_eq!(**cont2, SessionType::End);
                    }
                    other => panic!("Expected nested Recv, got {:?}", other),
                },
                other => panic!("Expected Send, got {:?}", other),
            },
            other => panic!("Expected ChoreographyBlock, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_choreography_with_choice() {
    let source = "koreografi Proto { peranan A, B; pilih { Lulus -> { A -> B: hantar Respon; tamat; }, Tolak -> { A -> B: hantar Sebab; tamat; } } }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ChoreographyBlock { protocol, .. } => match protocol {
                SessionType::Select(s1, s2) => {
                    assert!(matches!(s1.as_ref(), SessionType::Send(_, _)));
                    assert!(matches!(s2.as_ref(), SessionType::Send(_, _)));
                }
                other => panic!("Expected Select, got {:?}", other),
            },
            other => panic!("Expected ChoreographyBlock, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_choreography_known_type() {
    let source = "koreografi Proto { peranan A, B; A -> B: hantar Nombor; tamat; }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ChoreographyBlock { protocol, .. } => match protocol {
                SessionType::Send(ty, _) => {
                    assert_eq!(**ty, Ty::Int);
                }
                other => panic!("Expected Send, got {:?}", other),
            },
            other => panic!("Expected ChoreographyBlock, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_choreography_error_missing_role() {
    let source = "koreografi Proto { A -> B: hantar Msg; tamat; }";
    let mut p = Parser::new(source);
    let result = p.parse_program();
    assert!(result.is_err(), "Expected error when peranan is missing");
}

#[test]
fn test_parse_choreography_error_missing_brace() {
    let source = "koreografi Proto { peranan A, B; A -> B: hantar Msg; tamat;";
    let mut p = Parser::new(source);
    let result = p.parse_program();
    assert!(
        result.is_err(),
        "Expected error when closing brace is missing"
    );
}

// =============================================================================
// JALINAN PHASE 6: ACTOR DECLARATION TESTS
// =============================================================================

#[test]
fn test_parse_actor_basic() {
    let source = "pelaku MyActor { keadaan: Nombor kendalikan Msg(p) { p } }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ActorDecl {
                name,
                state_ty,
                message_ty,
                handler,
                ..
            } => {
                assert_eq!(name, "MyActor");
                assert_eq!(*state_ty, Ty::Int);
                assert_eq!(*message_ty, Ty::Any);
                assert!(matches!(handler.as_ref(), Expr::Lam(_, _, _)));
            }
            other => panic!("Expected ActorDecl, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_multi_handler() {
    let source =
        "pelaku MyActor { keadaan: Benar kendalikan MsgA(a) { a } kendalikan MsgB(b) { b } }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ActorDecl { name, handler, .. } => {
                assert_eq!(name, "MyActor");
                assert!(matches!(handler.as_ref(), Expr::Let(_, _, _, _)));
            }
            other => panic!("Expected ActorDecl, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_with_state_type() {
    let source = "pelaku Counter { keadaan: Nombor kendalikan Inc(x) { x } }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ActorDecl { state_ty, .. } => {
                assert_eq!(*state_ty, Ty::Int);
            }
            other => panic!("Expected ActorDecl, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_handler_body() {
    let source = "pelaku Echo { keadaan: Unit kendalikan Ping(m) { 42 } }";
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ActorDecl { handler, .. } => match handler.as_ref() {
                Expr::Lam(param, _, body) => {
                    assert_eq!(param, "m");
                    assert_eq!(**body, Expr::Int(42));
                }
                other => panic!("Expected Lam, got {:?}", other),
            },
            other => panic!("Expected ActorDecl, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_error_missing_keadaan() {
    let source = "pelaku MyActor { kendalikan Msg(p) { p } }";
    let mut p = Parser::new(source);
    let result = p.parse_program();
    assert!(result.is_err(), "Expected error when keadaan is missing");
}

#[test]
fn test_parse_actor_error_missing_brace() {
    let source = "pelaku MyActor { keadaan: Nombor kendalikan Msg(p) { p }";
    let mut p = Parser::new(source);
    let result = p.parse_program();
    assert!(
        result.is_err(),
        "Expected error when closing brace is missing"
    );
}

// =============================================================================
// JALINAN PHASE 6: SPAWN TESTS
// =============================================================================

#[test]
fn test_parse_spawn_basic() {
    let mut p = Parser::new("lahir MyActor(0)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Spawn(actor, init) => {
            assert_eq!(*actor, Expr::Var("MyActor".to_string()));
            assert_eq!(*init, Expr::Int(0));
        }
        other => panic!("Expected Spawn, got {:?}", other),
    }
}

#[test]
fn test_parse_spawn_with_var() {
    let mut p = Parser::new("lahir Counter(initial)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Spawn(actor, init) => {
            assert_eq!(*actor, Expr::Var("Counter".to_string()));
            assert_eq!(*init, Expr::Var("initial".to_string()));
        }
        other => panic!("Expected Spawn, got {:?}", other),
    }
}

#[test]
fn test_parse_spawn_with_unit() {
    let mut p = Parser::new("lahir Echo(())");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Spawn(_, init) => {
            assert_eq!(*init, Expr::Unit);
        }
        other => panic!("Expected Spawn, got {:?}", other),
    }
}

#[test]
fn test_parse_spawn_error_missing_paren() {
    let mut p = Parser::new("lahir MyActor");
    let result = p.parse_expr();
    assert!(result.is_err(), "Expected error when parens are missing");
}

// =============================================================================
// JALINAN PHASE 6: ACTOR SEND TESTS
// =============================================================================

#[test]
fn test_parse_actor_send_basic() {
    let mut p = Parser::new("hantar(sasaran, mesej)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ActorSend(a, m) => {
            assert_eq!(*a, Expr::Var("sasaran".to_string()));
            assert_eq!(*m, Expr::Var("mesej".to_string()));
        }
        other => panic!("Expected ActorSend, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_send_with_literal() {
    let mut p = Parser::new("hantar(x, 42)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ActorSend(a, m) => {
            assert_eq!(*a, Expr::Var("x".to_string()));
            assert_eq!(*m, Expr::Int(42));
        }
        other => panic!("Expected ActorSend, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_send_with_string() {
    let mut p = Parser::new("hantar(pemohon, \"hello\")");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ActorSend(a, m) => {
            assert_eq!(*a, Expr::Var("pemohon".to_string()));
            assert_eq!(*m, Expr::String("hello".to_string()));
        }
        other => panic!("Expected ActorSend, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_send_error_missing_comma() {
    let mut p = Parser::new("hantar(sasaran mesej)");
    let result = p.parse_expr();
    assert!(result.is_err(), "Expected error when comma is missing");
}

// =============================================================================
// JALINAN PHASE 6: ACTOR RECV TESTS
// =============================================================================

#[test]
fn test_parse_actor_recv_basic() {
    let mut p = Parser::new("terima(sasaran)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ActorRecv(a) => {
            assert_eq!(*a, Expr::Var("sasaran".to_string()));
        }
        other => panic!("Expected ActorRecv, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_recv_with_var() {
    let mut p = Parser::new("terima(pemohon)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ActorRecv(a) => {
            assert_eq!(*a, Expr::Var("pemohon".to_string()));
        }
        other => panic!("Expected ActorRecv, got {:?}", other),
    }
}

#[test]
fn test_parse_actor_recv_error_missing_paren() {
    let mut p = Parser::new("terima pelaku)");
    let result = p.parse_expr();
    assert!(
        result.is_err(),
        "Expected error when opening paren is missing"
    );
}

// =============================================================================
// JALINAN PHASE 6: CRDT MERGE TESTS
// =============================================================================

#[test]
fn test_parse_crdt_merge_basic() {
    let mut p = Parser::new("gabung(a, b)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::CRDTMerge(x, y) => {
            assert_eq!(*x, Expr::Var("a".to_string()));
            assert_eq!(*y, Expr::Var("b".to_string()));
        }
        other => panic!("Expected CRDTMerge, got {:?}", other),
    }
}

#[test]
fn test_parse_crdt_merge_with_exprs() {
    let mut p = Parser::new("gabung(x, y)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::CRDTMerge(a, b) => {
            assert_eq!(*a, Expr::Var("x".to_string()));
            assert_eq!(*b, Expr::Var("y".to_string()));
        }
        other => panic!("Expected CRDTMerge, got {:?}", other),
    }
}

#[test]
fn test_parse_crdt_merge_error_missing_arg() {
    let mut p = Parser::new("gabung(a)");
    let result = p.parse_expr();
    assert!(result.is_err(), "Expected error when second arg is missing");
}

// =============================================================================
// JALINAN PHASE 6: CONTENT HASH TESTS
// =============================================================================

#[test]
fn test_parse_content_hash_basic() {
    let mut p = Parser::new("cincang(x)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ContentHash(e) => {
            assert_eq!(*e, Expr::Var("x".to_string()));
        }
        other => panic!("Expected ContentHash, got {:?}", other),
    }
}

#[test]
fn test_parse_content_hash_with_literal() {
    let mut p = Parser::new("cincang(42)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ContentHash(e) => {
            assert_eq!(*e, Expr::Int(42));
        }
        other => panic!("Expected ContentHash, got {:?}", other),
    }
}

#[test]
fn test_parse_content_hash_error_missing_paren() {
    let mut p = Parser::new("cincang x");
    let result = p.parse_expr();
    assert!(result.is_err(), "Expected error when parens are missing");
}

#[test]
fn test_parse_content_verify_basic() {
    let mut p = Parser::new("sahkan(cincang(x), x)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ContentVerify(expected_hash, value) => {
            assert!(matches!(*expected_hash, Expr::ContentHash(_)));
            assert_eq!(*value, Expr::Var("x".to_string()));
        }
        other => panic!("Expected ContentVerify, got {:?}", other),
    }
}

#[test]
fn test_parse_content_verify_error_missing_comma() {
    let mut p = Parser::new("sahkan(cincang(x) x)");
    let result = p.parse_expr();
    assert!(result.is_err(), "Expected error when comma is missing");
}

#[test]
fn test_parse_contract_deploy_basic() {
    let mut p = Parser::new("kontrak_pintar(42)");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::ContractDeploy(Box::new(Expr::Int(42))));
}

#[test]
fn test_parse_contract_deploy_braced_form() {
    let mut p = Parser::new("kontrak_pintar { 42 }");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::ContractDeploy(Box::new(Expr::Int(42))));
}

#[test]
fn test_parse_contract_deploy_english_alias() {
    let mut p = Parser::new("smart_contract(account)");
    let expr = p.parse_expr().unwrap();
    assert_eq!(
        expr,
        Expr::ContractDeploy(Box::new(Expr::Var("account".to_string())))
    );
}

#[test]
fn test_parse_token_transfer_basic() {
    let mut p = Parser::new("token(alice, bob, 25)");
    let expr = p.parse_expr().unwrap();
    assert_eq!(
        expr,
        Expr::TokenTransfer {
            from: Box::new(Expr::Var("alice".to_string())),
            to: Box::new(Expr::Var("bob".to_string())),
            amount: Box::new(Expr::Int(25)),
        }
    );
}

#[test]
fn test_parse_token_transfer_path_form() {
    let mut p = Parser::new("token::pindah(alice, bob, 25)");
    let expr = p.parse_expr().unwrap();
    assert_eq!(
        expr,
        Expr::TokenTransfer {
            from: Box::new(Expr::Var("alice".to_string())),
            to: Box::new(Expr::Var("bob".to_string())),
            amount: Box::new(Expr::Int(25)),
        }
    );
}

#[test]
fn test_parse_token_transfer_english_method_alias() {
    let mut p = Parser::new("token::transfer(alice, bob, 25)");
    let expr = p.parse_expr().unwrap();
    assert_eq!(
        expr,
        Expr::TokenTransfer {
            from: Box::new(Expr::Var("alice".to_string())),
            to: Box::new(Expr::Var("bob".to_string())),
            amount: Box::new(Expr::Int(25)),
        }
    );
}

#[test]
fn test_parse_token_transfer_error_missing_amount() {
    let mut p = Parser::new("token(alice, bob)");
    assert!(p.parse_expr().is_err());
}

#[test]
fn test_parse_token_transfer_error_unknown_method() {
    let mut p = Parser::new("token::bakar(alice, bob, 25)");
    assert!(p.parse_expr().is_err());
}

#[test]
fn test_parse_zakat_calculate_basic() {
    let mut p = Parser::new("zakat(1000)");
    let expr = p.parse_expr().unwrap();
    assert_eq!(expr, Expr::ZakatCalculate(Box::new(Expr::Int(1000))));
}

#[test]
fn test_parse_zakat_calculate_nested_hash() {
    let mut p = Parser::new("zakat(cincang(data))");
    let expr = p.parse_expr().unwrap();
    assert_eq!(
        expr,
        Expr::ZakatCalculate(Box::new(Expr::ContentHash(Box::new(Expr::Var(
            "data".to_string()
        )))))
    );
}

// =============================================================================
// JALINAN PHASE 6: INTEGRATION TESTS
// =============================================================================

#[test]
fn test_parse_jalinan_spawn_send_recv_chain() {
    let source = "biar a = lahir MyActor(0); hantar(a, 1); terima(a)";
    let mut p = Parser::new(source);
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Let(name, _, val, cont) => {
            assert_eq!(name, "a");
            assert!(matches!(*val, Expr::Spawn(_, _)));
            match *cont {
                Expr::Let(_, _, send_expr, recv_cont) => {
                    assert!(matches!(*send_expr, Expr::ActorSend(_, _)));
                    assert!(matches!(*recv_cont, Expr::ActorRecv(_)));
                }
                other => panic!("Expected Let chain, got {:?}", other),
            }
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_jalinan_content_hash_of_merge() {
    let mut p = Parser::new("cincang(gabung(a, b))");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ContentHash(inner) => {
            assert!(matches!(*inner, Expr::CRDTMerge(_, _)));
        }
        other => panic!("Expected ContentHash, got {:?}", other),
    }
}

#[test]
fn test_parse_jalinan_send_to_spawned() {
    let mut p = Parser::new("hantar(lahir Echo(0), 42)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::ActorSend(actor, msg) => {
            assert!(matches!(*actor, Expr::Spawn(_, _)));
            assert_eq!(*msg, Expr::Int(42));
        }
        other => panic!("Expected ActorSend, got {:?}", other),
    }
}

#[test]
fn test_parse_jalinan_choreography_program() {
    let source = r#"koreografi Beli {
        peranan Pembeli, Penjual;
        Pembeli -> Penjual: hantar Pesanan;
        Penjual -> Pembeli: hantar Pengesahan;
        tamat;
    }"#;
    let mut p = Parser::new(source);
    let program = p.parse_program().unwrap();
    assert_eq!(program.decls.len(), 1);
    match &program.decls[0] {
        TopLevelDecl::Expr(e) => match e.as_ref() {
            Expr::ChoreographyBlock {
                name,
                roles,
                protocol,
            } => {
                assert_eq!(name, "Beli");
                assert_eq!(roles.len(), 2);
                // Viewpoint is roles[0] (Pembeli): the send to Penjual is a
                // `Send`, the reply back is a `Recv`.
                match protocol {
                    SessionType::Send(_, cont) => match cont.as_ref() {
                        SessionType::Recv(_, cont2) => {
                            assert_eq!(**cont2, SessionType::End);
                        }
                        other => panic!("Expected inner Recv, got {:?}", other),
                    },
                    other => panic!("Expected Send, got {:?}", other),
                }
            }
            other => panic!("Expected ChoreographyBlock, got {:?}", other),
        },
        other => panic!("Expected Expr, got {:?}", other),
    }
}

#[test]
fn test_parse_jalinan_bm_keywords_spawn() {
    let mut p = Parser::new("lahir Pelaku(0)");
    let expr = p.parse_expr().unwrap();
    assert!(matches!(expr, Expr::Spawn(_, _)));
}

#[test]
fn test_parse_jalinan_merge_and_hash_composition() {
    let source = "biar merged = gabung(x, y); cincang(merged)";
    let mut p = Parser::new(source);
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Let(name, _, val, cont) => {
            assert_eq!(name, "merged");
            assert!(matches!(*val, Expr::CRDTMerge(_, _)));
            assert!(matches!(*cont, Expr::ContentHash(_)));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

#[test]
fn test_parse_jalinan_hash_verify_composition() {
    let source = "biar hash = cincang(data); sahkan(hash, data)";
    let mut p = Parser::new(source);
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::Let(name, _, val, cont) => {
            assert_eq!(name, "hash");
            assert!(matches!(*val, Expr::ContentHash(_)));
            assert!(matches!(*cont, Expr::ContentVerify(_, _)));
        }
        other => panic!("Expected Let, got {:?}", other),
    }
}

// =============================================================================
// CAHAYA PHASE J5: UI PRIMITIVE TESTS
// =============================================================================

#[test]
fn test_parse_display_basic() {
    let mut p = Parser::new("paparan { 42 }");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIDisplay(elems) => {
            assert_eq!(elems.len(), 1);
            assert_eq!(elems[0], Expr::Int(42));
        }
        other => panic!("Expected UIDisplay, got {:?}", other),
    }
}

#[test]
fn test_parse_display_multiple_elements() {
    let mut p = Parser::new("paparan { 1; 2; 3 }");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIDisplay(elems) => {
            assert_eq!(elems.len(), 3);
        }
        other => panic!("Expected UIDisplay, got {:?}", other),
    }
}

#[test]
fn test_parse_row_basic() {
    let mut p = Parser::new("baris { 1; 2 }");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIRow(elems) => {
            assert_eq!(elems.len(), 2);
        }
        other => panic!("Expected UIRow, got {:?}", other),
    }
}

#[test]
fn test_parse_column_basic() {
    let mut p = Parser::new("lajur { 1; 2 }");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIColumn(elems) => {
            assert_eq!(elems.len(), 2);
        }
        other => panic!("Expected UIColumn, got {:?}", other),
    }
}

#[test]
fn test_parse_color_basic() {
    let mut p = Parser::new("warna(255, 128, 0)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIColor(r, g, b) => {
            assert_eq!(r, 255);
            assert_eq!(g, 128);
            assert_eq!(b, 0);
        }
        other => panic!("Expected UIColor, got {:?}", other),
    }
}

#[test]
fn test_parse_color_english() {
    let mut p = Parser::new("color(0, 0, 0)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIColor(r, g, b) => {
            assert_eq!(r, 0);
            assert_eq!(g, 0);
            assert_eq!(b, 0);
        }
        other => panic!("Expected UIColor, got {:?}", other),
    }
}

#[test]
fn test_parse_text_basic() {
    let mut p = Parser::new("tulisan(\"hello\", warna(0, 0, 0))");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIText(content, color) => {
            assert_eq!(*content, Expr::String("hello".to_string()));
            assert!(matches!(*color, Expr::UIColor(0, 0, 0)));
        }
        other => panic!("Expected UIText, got {:?}", other),
    }
}

#[test]
fn test_parse_button_basic() {
    let mut p = Parser::new("butang(\"Click\", handler)");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIButton(label, handler) => {
            assert_eq!(*label, Expr::String("Click".to_string()));
            assert_eq!(*handler, Expr::Var("handler".to_string()));
        }
        other => panic!("Expected UIButton, got {:?}", other),
    }
}

#[test]
fn test_parse_contrast_basic() {
    let mut p = Parser::new("kontras(warna(0, 0, 0), warna(255, 255, 255))");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIContrastCheck(fg, bg) => {
            assert!(matches!(*fg, Expr::UIColor(0, 0, 0)));
            assert!(matches!(*bg, Expr::UIColor(255, 255, 255)));
        }
        other => panic!("Expected UIContrastCheck, got {:?}", other),
    }
}

#[test]
fn test_parse_style_decl() {
    let mut p = Parser::new("gaya { pelapik: 16, saiz_fon: 14 }");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIStyleDecl { padding, font_size } => {
            assert_eq!(padding, Some(16));
            assert_eq!(font_size, Some(14));
        }
        other => panic!("Expected UIStyleDecl, got {:?}", other),
    }
}

#[test]
fn test_parse_style_decl_partial() {
    let mut p = Parser::new("style { padding: 8 }");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIStyleDecl { padding, font_size } => {
            assert_eq!(padding, Some(8));
            assert_eq!(font_size, None);
        }
        other => panic!("Expected UIStyleDecl, got {:?}", other),
    }
}

#[test]
fn test_parse_display_nested() {
    let mut p = Parser::new("paparan { baris { 1; 2 }; lajur { 3; 4 } }");
    let expr = p.parse_expr().unwrap();
    match expr {
        Expr::UIDisplay(elems) => {
            assert_eq!(elems.len(), 2);
            assert!(matches!(elems[0], Expr::UIRow(_)));
            assert!(matches!(elems[1], Expr::UIColumn(_)));
        }
        other => panic!("Expected UIDisplay, got {:?}", other),
    }
}

// -- Grammar extensions: type annotations, trailing semicolons, `jenis` decls --

#[test]
fn test_parse_biar_type_annotation() {
    // `biar x: T = e` — the annotation is accepted (and discarded).
    let mut p = Parser::new("biar n: Nombor = 42; n");
    let expr = p.parse_expr().unwrap();
    assert!(matches!(expr, Expr::Let(ref name, _, _, _) if name == "n"));
}

#[test]
fn test_parse_trailing_semicolon_in_block() {
    // A trailing `;` before a block close `}` is allowed; `pulang x;` as the
    // final statement returns `x`.
    let mut p =
        Parser::new("fungsi f(x: Nombor) -> Nombor {\n  biar a = x;\n  pulang a;\n}\n1");
    let prog = p.parse_program();
    assert!(prog.is_ok(), "trailing `;` before `}}` should parse: {prog:?}");
}

#[test]
fn test_parse_jenis_record_decl() {
    let mut p = Parser::new("jenis Titik { x: Nombor, y: Nombor, }\n1");
    let prog = p.parse_program();
    assert!(prog.is_ok(), "jenis record decl should parse: {prog:?}");
}

#[test]
fn test_parse_jenis_generic_and_alias_and_marker() {
    // Generic record, alias, and marker forms all parse.
    for src in [
        "jenis Box<T> { nilai: T, }\n1",
        "jenis Umur = Nombor;\n1",
        "jenis Penanda\n1",
    ] {
        let mut p = Parser::new(src);
        assert!(p.parse_program().is_ok(), "should parse: {src}");
    }
}

#[test]
fn test_parse_top_level_biar_type_annotation() {
    let mut p = Parser::new("biar n: Nombor = 42;\nn");
    assert!(p.parse_program().is_ok());
}

// -- Grammar extensions round 2: nominal types, mut bindings, multi-effects --

#[test]
fn test_parse_biar_ubah_mut_binding() {
    // `biar ubah x = e` binds a real mutable SLOT, not a plain `Let`, and a read
    // of the name goes through `SlotGet`. Before 2026-08 `ubah` was parsed and
    // discarded, so a write inside a nested block vanished at the closing brace.
    let mut p = Parser::new("biar ubah i = 0; i");
    match p.parse_expr().unwrap() {
        Expr::LetMut(name, init, body) => {
            assert_eq!(name, "i");
            assert_eq!(*init, Expr::Int(0));
            assert_eq!(*body, Expr::SlotGet("i".to_string()));
        }
        other => panic!("expected LetMut, got {other:?}"),
    }
}

#[test]
fn test_biar_without_ubah_is_still_immutable() {
    // No `ubah` — an ordinary `Let`, and the name reads as a plain `Var`.
    let mut p = Parser::new("biar i = 0; i");
    match p.parse_expr().unwrap() {
        Expr::Let(name, _, _, body) => {
            assert_eq!(name, "i");
            assert_eq!(*body, Expr::Var("i".to_string()));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_assignment_to_a_slot_is_a_slot_write() {
    // `x = e;` on a `biar ubah` name is a slot WRITE, so what follows is
    // sequenced after it rather than nested inside a shadowing rebind.
    let mut p = Parser::new("biar ubah i = 0; i = 1; i");
    let Expr::LetMut(_, _, body) = p.parse_expr().unwrap() else {
        panic!("expected LetMut");
    };
    let Expr::Let(_, _, write, rest) = *body else {
        panic!("expected the write to be sequenced");
    };
    assert_eq!(*write, Expr::SlotSet("i".to_string(), Box::new(Expr::Int(1))));
    assert_eq!(*rest, Expr::SlotGet("i".to_string()));
}

#[test]
fn test_inner_immutable_binding_shadows_an_outer_slot() {
    // An inner `biar x` hides an outer `biar ubah x`, so the inner read must be
    // a plain `Var` — reading it as a slot would look through to the wrong cell.
    let mut p = Parser::new("biar ubah x = 0; biar x = 9; x");
    let Expr::LetMut(_, _, body) = p.parse_expr().unwrap() else {
        panic!("expected LetMut");
    };
    let Expr::Let(_, _, _, inner) = *body else {
        panic!("expected the shadowing Let");
    };
    assert_eq!(*inner, Expr::Var("x".to_string()));
}

#[test]
fn test_selagi_parses_as_a_real_loop() {
    // `selagi` is a loop node. It used to desugar to `if cond { body; () }`,
    // which ran the body at most ONCE while presenting itself as a loop.
    let mut p = Parser::new("selagi betul { 1 }");
    assert!(matches!(p.parse_expr().unwrap(), Expr::While(_, _)));
}

#[test]
fn test_ulang_parses_as_an_unbounded_loop() {
    let mut p = Parser::new("ulang { 1 }");
    match p.parse_expr().unwrap() {
        Expr::While(cond, _) => assert_eq!(*cond, Expr::Bool(true)),
        other => panic!("expected While, got {other:?}"),
    }
}

#[test]
fn test_putus_and_lanjut_inside_a_loop() {
    // Both are real control flow now, not the no-op `()` they used to be.
    let mut p = Parser::new("ulang { putus }");
    match p.parse_expr().unwrap() {
        Expr::While(_, body) => assert_eq!(*body, Expr::Break),
        other => panic!("expected While, got {other:?}"),
    }
    let mut p = Parser::new("ulang { lanjut }");
    match p.parse_expr().unwrap() {
        Expr::While(_, body) => assert_eq!(*body, Expr::Continue),
        other => panic!("expected While, got {other:?}"),
    }
}

#[test]
fn test_ubah_with_a_linearity_qualifier_is_rejected() {
    // Silently dropping the qualifier is the failure mode being avoided.
    let mut p = Parser::new("biar ubah sekali x = 0; x");
    let err = p
        .parse_expr()
        .expect_err("`biar ubah sekali` must not parse");
    assert!(matches!(err.kind, ParseErrorKind::MutWithLinearity));
}

#[test]
fn test_putus_outside_a_loop_is_rejected() {
    // Silently ignoring it (the old behaviour) hid a real mistake.
    let mut p = Parser::new("putus");
    let err = p.parse_expr().expect_err("`putus` outside a loop must not parse");
    assert!(matches!(
        err.kind,
        ParseErrorKind::LoopControlOutsideLoop("putus")
    ));
    let mut p = Parser::new("lanjut");
    let err = p.parse_expr().expect_err("`lanjut` outside a loop must not parse");
    assert!(matches!(
        err.kind,
        ParseErrorKind::LoopControlOutsideLoop("lanjut")
    ));
}

#[test]
fn test_parse_multi_effect_annotation() {
    // `kesan (E1, E2)` parses; effects are joined into the dominant one.
    let mut p = Parser::new("fungsi f() -> Nombor kesan (Kripto, MasaTetap) {\n  0\n}\n0");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_parse_masatetap_as_effect() {
    // MasaTetap (constant-time) is accepted in effect position.
    let mut p = Parser::new("fungsi f() -> Nombor kesan MasaTetap {\n  0\n}\n0");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_parse_list_literal() {
    let mut p = Parser::new("[1, 2, 3]");
    match p.parse_expr().unwrap() {
        Expr::ListLit(elems) => assert_eq!(elems.len(), 3),
        other => panic!("expected ListLit, got {other:?}"),
    }
}

#[test]
fn test_parse_empty_and_nested_list() {
    let mut p = Parser::new("[]");
    assert!(matches!(p.parse_expr().unwrap(), Expr::ListLit(ref v) if v.is_empty()));
    let mut p2 = Parser::new("[[1, 2], [3, 4]]");
    match p2.parse_expr().unwrap() {
        Expr::ListLit(elems) => {
            assert_eq!(elems.len(), 2);
            assert!(matches!(elems[0], Expr::ListLit(_)));
        }
        other => panic!("expected nested ListLit, got {other:?}"),
    }
}

#[test]
fn test_parse_record_literal() {
    let mut p = Parser::new("Titik { x: 1, y: 2 }");
    match p.parse_expr().unwrap() {
        Expr::RecordLit(name, fields) => {
            assert_eq!(name, "Titik");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "x");
        }
        other => panic!("expected RecordLit, got {other:?}"),
    }
}

#[test]
fn test_parse_empty_record() {
    let mut p = Parser::new("Kosong {}");
    assert!(matches!(p.parse_expr().unwrap(), Expr::RecordLit(ref n, ref f) if n == "Kosong" && f.is_empty()));
}

#[test]
fn test_parse_field_access() {
    let mut p = Parser::new("p.x");
    match p.parse_expr().unwrap() {
        Expr::FieldAccess(_, field) => assert_eq!(field, "x"),
        other => panic!("expected FieldAccess, got {other:?}"),
    }
}

#[test]
fn test_parse_tuple_index_access() {
    // `.0`/`.1` desugar to Fst/Snd.
    let mut p = Parser::new("pair.0");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Fst(_)));
    let mut p2 = Parser::new("pair.1");
    assert!(matches!(p2.parse_expr().unwrap(), Expr::Snd(_)));
}

#[test]
fn test_record_not_confused_with_if_block() {
    // `kalau x { 1 } lain { 2 }` must NOT parse `x { 1 }` as a record literal.
    let mut p = Parser::new("kalau benar { 1 } lain { 2 }");
    assert!(matches!(p.parse_expr().unwrap(), Expr::If(_, _, _)));
}

#[test]
fn test_parse_option_result_constructors() {
    // Some/Ok -> Inl; Err/None -> Inr.
    let mut p = Parser::new("Some(5)");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Inl(_, _)));
    let mut p = Parser::new("Ok(42)");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Inl(_, _)));
    let mut p = Parser::new("Err(\"bad\")");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Inr(_, _)));
    let mut p = Parser::new("None");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Inr(_, _)));
}

#[test]
fn test_parse_constructor_in_let() {
    let mut p = Parser::new("biar x = Some(5); x");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_parse_module_path_lowercase() {
    // lowercase module -> module_function
    let mut p = Parser::new("teks::mengandungi");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Var(n) if n == "teks_mengandungi"));
}

#[test]
fn test_parse_module_path_capitalized() {
    // capitalized module -> bare function name
    let mut p = Parser::new("Masa::masa_unix");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Var(n) if n == "masa_unix"));
}

#[test]
fn test_parse_module_path_drops_std() {
    let mut p = Parser::new("std::teks::mengandungi");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Var(n) if n == "teks_mengandungi"));
}

#[test]
fn test_parse_module_path_call() {
    // qualified call composes with application
    let mut p = Parser::new("teks::mengandungi(\"a\", \"b\")");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_parse_logical_not_desugars_to_if() {
    // `bukan e` / `not e` -> If(e, false, true)
    let mut p = Parser::new("bukan betul");
    match p.parse_expr().unwrap() {
        Expr::If(_, t, f) => {
            assert_eq!(*t, Expr::Bool(false));
            assert_eq!(*f, Expr::Bool(true));
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn test_parse_deref_still_bang() {
    let mut p = Parser::new("!x");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Deref(_)));
}

// =============================================================================
// PADAN (pattern matching) COMPILATION TESTS
// =============================================================================

#[test]
fn test_padan_arrow_literal_desugars_to_if() {
    // `padan x { 0 -> 1, _ -> 2 }` compiles to a let-bound If chain.
    let mut p = Parser::new("padan x { 0 -> 1, _ -> 2 }");
    // Should parse without error and produce a Let (scrutinee binding).
    assert!(matches!(p.parse_expr().unwrap(), Expr::Let(_, _, _, _)));
}

#[test]
fn test_padan_constructor_desugars_to_case() {
    // Ada/Tidak constructor arms compile to a Case (sum elimination) with the
    // payload variable used directly as the binder.
    let mut p = Parser::new("padan m { Ada(n) -> n, Tidak -> 0 }");
    match p.parse_expr().unwrap() {
        Expr::Case(_, l, _, _, _) => assert_eq!(l, "n"),
        other => panic!("expected Case, got {other:?}"),
    }
}

#[test]
fn test_padan_legacy_inl_inr_still_case() {
    // Backward compatibility: `inl x => .. , inr y => ..` with FatArrow.
    let mut p = Parser::new("padan e { inl x => 1, inr y => 2 }");
    match p.parse_expr().unwrap() {
        Expr::Case(_, x, _, y, _) => {
            assert_eq!(x, "x");
            assert_eq!(y, "y");
        }
        other => panic!("expected Case, got {other:?}"),
    }
}

#[test]
fn test_padan_guard_parses() {
    // `kalau` guard on an arm.
    let mut p = Parser::new("padan x { n kalau n > 5 -> 1, n -> 0 }");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_padan_tuple_pattern_parses() {
    let mut p = Parser::new("padan p { (0, 0) -> 1, (a, b) -> 2 }");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Let(_, _, _, _)));
}

#[test]
fn test_padan_block_body_parses() {
    let mut p = Parser::new("padan x { 1 -> { biar y = 2; y }, _ -> 0 }");
    assert!(p.parse_expr().is_ok());
}

// =============================================================================
// GENERIC FUNCTION PARAMS + FUNCTION-TYPE ARROW SYNTAX
// =============================================================================

#[test]
fn test_parse_generic_fn_decl_single() {
    // `fungsi f<T>(x: T) -> T` — generic params are skipped (monomorphic layer).
    let mut p = Parser::new("fungsi identiti<T>(x: T) -> T kesan Bersih { x }");
    let prog = p.parse_program().unwrap();
    assert_eq!(prog.decls.len(), 1);
}

#[test]
fn test_parse_generic_fn_decl_multi() {
    let mut p = Parser::new("fungsi pasang<E, T>(x: T) -> T kesan Bersih { x }");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_parse_fn_decl_bare_effect_return() {
    // `-> kesan Bersih` with no return type means a Unit return.
    let mut p = Parser::new("fungsi tetapkan(k: Teks) -> kesan Bersih { () }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { return_ty, .. } => assert_eq!(*return_ty, Ty::Unit),
        other => panic!("expected Function, got {other:?}"),
    }
}

#[test]
fn test_parse_fn_type_arrow_form() {
    // `Fn(A) -> B` arrow form.
    let mut p = Parser::new("Fn(Nombor) -> Teks");
    assert_eq!(
        p.parse_ty().unwrap(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::String), Effect::Pure)
    );
}

#[test]
fn test_parse_fn_type_arrow_empty_params() {
    // `Fn() -> B`: argument type defaults to Unit.
    let mut p = Parser::new("Fn() -> Nombor");
    assert_eq!(
        p.parse_ty().unwrap(),
        Ty::Fn(Box::new(Ty::Unit), Box::new(Ty::Int), Effect::Pure)
    );
}

#[test]
fn test_parse_fn_type_arrow_with_effect() {
    // `Fn(A) -> B kesan Tulis`.
    let mut p = Parser::new("Fn(Nombor) -> Nombor kesan Tulis");
    assert_eq!(
        p.parse_ty().unwrap(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Write)
    );
}

#[test]
fn test_parse_fn_type_legacy_comma_still_works() {
    // Backward compatibility: `Fn(A, B, Eff)` comma form.
    let mut p = Parser::new("Fn(Int, Bool, Write)");
    assert_eq!(
        p.parse_ty().unwrap(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Write)
    );
}

// =============================================================================
// IF-WITHOUT-ELSE GUARDS + ELSE-IF CHAINS + BLOCK-FORM STATEMENT SEQUENCING
// =============================================================================

#[test]
fn test_parse_else_if_chain() {
    // `lain kalau` chains parse as nested If.
    let mut p = Parser::new("kalau salah { 1 } lain kalau betul { 2 } lain { 3 }");
    match p.parse_expr().unwrap() {
        Expr::If(_, _, else_branch) => {
            assert!(matches!(*else_branch, Expr::If(_, _, _)));
        }
        other => panic!("expected If, got {other:?}"),
    }
}

#[test]
fn test_parse_guard_then_statement() {
    // A block-form guard with no trailing `;` can be followed by more
    // statements: `kalau c { pulang x; } pulang y;`.
    let mut p = Parser::new("kalau betul { pulang 0; } pulang 9;");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_parse_plain_if_else_still_works() {
    let mut p = Parser::new("kalau betul { 1 } lain { 2 }");
    assert!(matches!(p.parse_expr().unwrap(), Expr::If(_, _, _)));
}

// =============================================================================
// NESTED (LOCAL) FUNCTION DECLARATIONS
// =============================================================================

#[test]
fn test_parse_nested_function_desugars_to_letrec() {
    // A `fungsi` in statement position becomes a LetRec binding.
    let mut p = Parser::new(
        "fungsi luar(n: Nombor) -> Nombor kesan Bersih { fungsi tokok(x: Nombor) -> Nombor { x } tokok(n) }",
    );
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { body, .. } => {
            assert!(matches!(**body, Expr::LetRec(_, _, _, _)));
        }
        other => panic!("expected Function, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_not_treated_as_nested_fn() {
    // `fn(x: T) body` (lambda, no name) must still parse as Lam, not a decl.
    let mut p = Parser::new("fn(x: Nombor) x");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Lam(_, _, _)));
}

// =============================================================================
// LIST INDEXING e[i]
// =============================================================================

#[test]
fn test_parse_index_desugars_to_list_get() {
    // `e[i]` -> App(Var("senarai_dapat"), Pair(e, i)).
    let mut p = Parser::new("s[0]");
    match p.parse_expr().unwrap() {
        Expr::App(f, arg) => {
            assert_eq!(*f, Expr::Var("senarai_dapat".to_string()));
            assert!(matches!(*arg, Expr::Pair(_, _)));
        }
        other => panic!("expected App, got {other:?}"),
    }
}

#[test]
fn test_parse_index_chains_with_field() {
    // `s[0].0` parses (index then projection).
    let mut p = Parser::new("s[0].0");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Fst(_)));
}

// =============================================================================
// ANONYMOUS (BRACED) RECORD LITERALS
// =============================================================================

#[test]
fn test_parse_anonymous_record_literal() {
    // `{ field: e, ... }` with no type name -> RecordLit("", fields).
    let mut p = Parser::new("{ x: 1, y: 2 }");
    match p.parse_expr().unwrap() {
        Expr::RecordLit(name, fields) => {
            assert_eq!(name, "");
            assert_eq!(fields.len(), 2);
        }
        other => panic!("expected RecordLit, got {other:?}"),
    }
}

#[test]
fn test_parse_anonymous_empty_record() {
    let mut p = Parser::new("{}");
    assert!(matches!(p.parse_expr().unwrap(), Expr::RecordLit(_, _)));
}

#[test]
fn test_parse_named_record_still_works() {
    let mut p = Parser::new("Titik { x: 1 }");
    match p.parse_expr().unwrap() {
        Expr::RecordLit(name, _) => assert_eq!(name, "Titik"),
        other => panic!("expected RecordLit, got {other:?}"),
    }
}

// =============================================================================
// STATEMENT-POSITION REASSIGNMENT (rebinding)
// =============================================================================

#[test]
fn test_parse_reassignment_desugars_to_let() {
    // `i = e;` in statement position rebinds `i`.
    let mut p = Parser::new("biar i = 0; i = i + 1; i");
    // Outer is the `biar i = 0` Let; its body is the rebinding Let.
    match p.parse_expr().unwrap() {
        Expr::Let(name, _, _, body) => {
            assert_eq!(name, "i");
            assert!(matches!(*body, Expr::Let(_, _, _, _)));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_equality_not_treated_as_assignment() {
    // `x == 5` must remain a comparison, not a reassignment.
    let mut p = Parser::new("biar x = 5; x == 5");
    match p.parse_expr().unwrap() {
        Expr::Let(_, _, _, body) => {
            assert!(matches!(*body, Expr::BinOp(BinOp::Eq, _, _)));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

#[test]
fn test_parse_bare_return_is_unit() {
    // `pulang;` (no operand) returns Unit.
    let mut p = Parser::new("pulang;");
    match p.parse_expr().unwrap() {
        Expr::Return(e) => assert_eq!(*e, Expr::Unit),
        other => panic!("expected Return, got {other:?}"),
    }
}

#[test]
fn test_parse_return_with_value() {
    let mut p = Parser::new("pulang 5");
    match p.parse_expr().unwrap() {
        Expr::Return(e) => assert_eq!(*e, Expr::Int(5)),
        other => panic!("expected Return, got {other:?}"),
    }
}

#[test]
fn test_parse_return_in_match_arm() {
    // A bare match-arm body may be a control-flow expr like `pulang e`.
    let mut p = Parser::new("padan x { 0 -> pulang 99, _ -> 1 }");
    // Compiles to a Case/If; just assert it parses without error.
    assert!(p.parse_expr().is_ok());
}

// =============================================================================
// NESTED GENERIC TYPES via `>>` (Shr) splitting
// =============================================================================

#[test]
fn test_parse_nested_generic_double() {
    let mut p = Parser::new("Mungkin<Senarai<Nombor>>");
    assert!(p.parse_ty().is_ok());
}

#[test]
fn test_parse_nested_generic_triple_unknown_inner() {
    // Innermost `Peta<..>` is an unknown nominal type (uses the skip path);
    // the `>>>` must close all three levels without over-consuming.
    let mut p = Parser::new("Mungkin<Senarai<Peta<Teks, Nombor>>>");
    assert!(p.parse_ty().is_ok());
}

#[test]
fn test_parse_single_generic_unaffected() {
    let mut p = Parser::new("Senarai<Nombor>");
    assert!(p.parse_ty().is_ok());
}

// =============================================================================
// format!(...) MACRO
// =============================================================================

#[test]
fn test_parse_format_macro_desugars_to_concat() {
    // `format!("x={}", a)` -> ("x=" + ke_teks(a)) + "".
    let mut p = Parser::new("format!(\"x={}\", 5)");
    assert!(matches!(p.parse_expr().unwrap(), Expr::BinOp(BinOp::Add, _, _)));
}

#[test]
fn test_parse_format_macro_no_args() {
    let mut p = Parser::new("format!(\"hello\")");
    assert_eq!(p.parse_expr().unwrap(), Expr::String("hello".to_string()));
}

#[test]
fn test_parse_format_macro_escapes() {
    // `{{`/`}}` unescape to `{`/`}`.
    let mut p = Parser::new("format!(\"{{literal}}\")");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::String("{literal}".to_string())
    );
}

#[test]
fn test_parse_effect_union_pipe() {
    // `kesan (A | B)` parses the same as `kesan (A, B)` — joined effect.
    let mut p = Parser::new("fungsi f() -> Nombor kesan (Bersih | SistemFail) { 0 }");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_parse_qualified_fn_def_name() {
    // `fungsi Type::method(..)` is accepted and resolves to a flat name.
    let mut p = Parser::new("fungsi teks::mengandungi(t: Teks, c: Teks) -> Benar kesan Bersih { betul }");
    let prog = p.parse_program().unwrap();
    match &prog.decls[0] {
        TopLevelDecl::Function { name, .. } => assert_eq!(name, "teks_mengandungi"),
        other => panic!("expected Function, got {other:?}"),
    }
}

// =============================================================================
// EXTENDED LAMBDA SYNTAX (multi-param, return type, block body)
// =============================================================================

#[test]
fn test_parse_lambda_typed_return_block_body() {
    // `fungsi(x: T) -> R { body }`
    let mut p = Parser::new("fungsi(x: Nombor) -> Nombor { x + 1 }");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Lam(_, _, _)));
}

#[test]
fn test_parse_lambda_multi_param_curries() {
    // `fungsi(a, b) ...` curries into nested Lam.
    let mut p = Parser::new("fungsi(a: Nombor, b: Nombor) -> Nombor { a + b }");
    match p.parse_expr().unwrap() {
        Expr::Lam(_, _, inner) => assert!(matches!(*inner, Expr::Lam(_, _, _))),
        other => panic!("expected curried Lam, got {other:?}"),
    }
}

#[test]
fn test_parse_lambda_bare_body_still_works() {
    let mut p = Parser::new("fungsi(x: Nombor) x");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Lam(_, _, _)));
}

// =============================================================================
// RANGE EXPRESSIONS a..b / a..=b
// =============================================================================

#[test]
fn test_parse_range_exclusive() {
    // `a..b` -> julat((a, b)).
    let mut p = Parser::new("0..5");
    match p.parse_expr().unwrap() {
        Expr::App(f, _) => assert_eq!(*f, Expr::Var("julat".to_string())),
        other => panic!("expected App(julat), got {other:?}"),
    }
}

#[test]
fn test_parse_range_inclusive() {
    let mut p = Parser::new("0..=5");
    match p.parse_expr().unwrap() {
        Expr::App(f, _) => assert_eq!(*f, Expr::Var("julat_inklusif".to_string())),
        other => panic!("expected App(julat_inklusif), got {other:?}"),
    }
}

#[test]
fn test_parse_for_over_range_uses_list_map() {
    // `untuk i dalam 0..n { .. }` -> senarai_peta((0..n, fn)).
    let mut p = Parser::new("untuk i dalam 0..3 { i }");
    match p.parse_expr().unwrap() {
        Expr::App(f, _) => assert_eq!(*f, Expr::Var("senarai_peta".to_string())),
        other => panic!("expected App(senarai_peta), got {other:?}"),
    }
}

// =============================================================================
// ENUM-VARIANT ACCESS Type.Variant
// =============================================================================

#[test]
fn test_parse_enum_variant_value_is_tag_string() {
    // `Type.Variant` (both uppercase) -> string tag "Type.Variant".
    let mut p = Parser::new("ArasKeselamatan.Awam");
    assert_eq!(
        p.parse_expr().unwrap(),
        Expr::String("ArasKeselamatan.Awam".to_string())
    );
}

#[test]
fn test_parse_struct_field_access_still_works() {
    // Lowercase field is still a FieldAccess, not an enum tag.
    let mut p = Parser::new("rekod.medan");
    assert!(matches!(p.parse_expr().unwrap(), Expr::FieldAccess(_, _)));
}

#[test]
fn test_parse_enum_variant_pattern() {
    // `Type.Variant` works as a `padan` pattern (compiles without error).
    let mut p = Parser::new("padan x { Taint.Bersih -> 1, _ -> 0 }");
    assert!(p.parse_expr().is_ok());
}

// =============================================================================
// TUPLE DESTRUCTURING `biar (a, b) = e` + n-TUPLES
// =============================================================================

#[test]
fn test_parse_tuple_destructuring_let() {
    // `biar (a, b) = e; body` desugars to a temp Let + Fst/Snd projections.
    let mut p = Parser::new("fungsi f() -> Nombor kesan Bersih { biar (a, b) = (1, 2); a + b }");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_parse_three_tuple_construction() {
    // `(a, b, c)` builds a right-nested pair chain.
    let mut p = Parser::new("(1, 2, 3)");
    match p.parse_expr().unwrap() {
        Expr::Pair(_, rest) => assert!(matches!(*rest, Expr::Pair(_, _))),
        other => panic!("expected nested Pair, got {other:?}"),
    }
}

// =============================================================================
// SOFT KEYWORDS AS NAMES (tahap/keadaan/jenis/... used as identifiers)
// =============================================================================

#[test]
fn test_soft_keyword_as_binding_and_use() {
    let mut p = Parser::new("biar tahap = 7; tahap");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_soft_keyword_as_param_name() {
    let mut p =
        Parser::new("fungsi f(tahap: Teks, keadaan: Nombor) -> Nombor kesan Bersih { keadaan }");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_soft_keyword_as_record_field() {
    let mut p = Parser::new("{ tahap: 3, keadaan: 4 }");
    match p.parse_expr().unwrap() {
        Expr::RecordLit(_, fields) => {
            assert_eq!(fields[0].0, "tahap");
            assert_eq!(fields[1].0, "keadaan");
        }
        other => panic!("expected RecordLit, got {other:?}"),
    }
}

#[test]
fn test_jenis_still_a_decl_keyword() {
    // `jenis` is a soft keyword as a name, but still a struct-decl keyword,
    // including as the final declaration in a file (EOF-safe recursion).
    let mut p = Parser::new("jenis Titik { x: Nombor }");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_parse_for_tuple_pattern() {
    // `untuk (a, b) dalam iter { .. }` destructures each element.
    let mut p = Parser::new("untuk (a, b) dalam xs { a }");
    match p.parse_expr().unwrap() {
        Expr::App(f, _) => assert_eq!(*f, Expr::Var("senarai_peta".to_string())),
        other => panic!("expected App(senarai_peta), got {other:?}"),
    }
}

#[test]
fn test_parse_fn_type_multi_param_arrow() {
    // `Fn(A, B) -> C` (multi-param arrow form).
    let mut p = Parser::new("Fn(Nombor, Nombor) -> Nombor");
    match p.parse_ty().unwrap() {
        Ty::Fn(a, r, _) => {
            assert_eq!(*a, Ty::Int);
            assert_eq!(*r, Ty::Int);
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn test_parse_guard_assertion_form() {
    // `pastikan cond "msg"; rest` (assertion guard with message).
    let mut p = Parser::new("fungsi f(x: Nombor) -> Nombor kesan Bersih { pastikan x >= 0 \"msg\"; pulang x; }");
    assert!(p.parse_program().is_ok());
}

#[test]
fn test_literal_not_applied_to_following_atom() {
    // `0 "msg"` must not parse as application of `0` to `"msg"`.
    let mut p = Parser::new("0 \"msg\"");
    // Parses as just `0` (the string is left for the caller / sequence).
    assert_eq!(p.parse_expr().unwrap(), Expr::Int(0));
}

#[test]
fn test_parse_pipe_lambda_target() {
    // `x |> fungsi(y) { .. }` — a lambda as pipe target.
    let mut p = Parser::new("5 |> fungsi(x: Nombor) -> Nombor { x + 5 }");
    match p.parse_expr().unwrap() {
        Expr::App(f, _) => assert!(matches!(*f, Expr::Lam(_, _, _))),
        other => panic!("expected App(Lam), got {other:?}"),
    }
}

#[test]
fn test_parse_chained_method_calls() {
    // `m.peta(..).peta(..)` — multi-step method chain (call then call).
    let mut p = Parser::new("m.f(1).g(2)");
    // Outer is App(App(FieldAccess(App(App(FieldAccess(m,f),1)),g),2)) — just
    // assert it parses to a nested App without error.
    assert!(matches!(p.parse_expr().unwrap(), Expr::App(_, _)));
}

// =============================================================================
// LIST PATTERNS  [] / [x] / [x, y] / [x, ..rest]
// =============================================================================

#[test]
fn test_parse_list_pattern_empty() {
    let mut p = Parser::new("padan s { [] -> 0, _ -> 1 }");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_parse_list_pattern_fixed_and_rest() {
    let mut p = Parser::new("padan s { [x] -> x, [x, y] -> y, [h, ..t] -> h, _ -> 0 }");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_parse_list_concat() {
    // `+` over lists.
    let mut p = Parser::new("[1] + akum");
    assert!(matches!(p.parse_expr().unwrap(), Expr::BinOp(BinOp::Add, _, _)));
}

#[test]
fn test_parse_nested_ctor_in_tuple_pattern() {
    // `(Ada(a), Ada(b))` — constructor patterns nested in a tuple pattern.
    let mut p = Parser::new("padan p { (Ada(a), Ada(b)) -> a + b, _ -> 0 }");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_parse_ref_pattern() {
    // `ruj(p)` reference pattern — deref + inner pattern.
    let mut p = Parser::new("padan r { ruj(0) -> 1, ruj(x) -> x }");
    assert!(p.parse_expr().is_ok());
}

// =============================================================================
// NAMED (NOMINAL-ENUM) CONSTRUCTORS  C(args) / nullary C
// =============================================================================

#[test]
fn test_parse_named_ctor_construction() {
    // `Bulatan(5)` -> Pair(String("Bulatan"), Int(5)).
    let mut p = Parser::new("Bulatan(5)");
    match p.parse_expr().unwrap() {
        Expr::Pair(tag, payload) => {
            assert_eq!(*tag, Expr::String("Bulatan".to_string()));
            assert_eq!(*payload, Expr::Int(5));
        }
        other => panic!("expected Pair, got {other:?}"),
    }
}

#[test]
fn test_parse_named_ctor_multi_arg() {
    // `Segi(4, 5)` -> Pair("Segi", Pair(4, 5)).
    let mut p = Parser::new("Segi(4, 5)");
    assert!(matches!(p.parse_expr().unwrap(), Expr::Pair(_, _)));
}

#[test]
fn test_parse_nullary_ctor_is_tag() {
    // Bare uppercase `Tamat` -> String("Tamat").
    let mut p = Parser::new("Tamat");
    assert_eq!(p.parse_expr().unwrap(), Expr::String("Tamat".to_string()));
}

#[test]
fn test_parse_named_ctor_match() {
    // Multi-variant enum match parses and compiles.
    let mut p = Parser::new("padan b { Bulatan(r) -> r, Segi(p, l) -> p, Segitiga(a, x, c) -> a }");
    assert!(p.parse_expr().is_ok());
}

#[test]
fn test_lowercase_ident_still_var() {
    // Lowercase identifiers are NOT constructors.
    let mut p = Parser::new("bulatan");
    assert_eq!(p.parse_expr().unwrap(), Expr::Var("bulatan".to_string()));
}

#[test]
fn test_prefix_not_binds_call() {
    // REQ (examples parse-gap): `!f(x)` is `Deref(f(x))` and `bukan f(x)` is
    // `If(f(x), false, true)` — the prefix operand must include the postfix
    // call, not stop before `(x)` (which raised "Unexpected token: LParen").
    let mut p = Parser::new("!ada_fail(nama)");
    match p.parse_expr().expect("!f(x) must parse") {
        Expr::Deref(inner) => assert!(matches!(*inner, Expr::App(_, _)), "operand is the call"),
        other => panic!("expected Deref(App), got {other:?}"),
    }

    let mut p = Parser::new("bukan ada_fail(nama)");
    match p.parse_expr().expect("bukan f(x) must parse") {
        Expr::If(cond, _, _) => assert!(matches!(*cond, Expr::App(_, _)), "condition is the call"),
        other => panic!("expected If(App, ..), got {other:?}"),
    }

    // Inside `kalau`, the original failing shape.
    let mut p = Parser::new("kalau !ada_fail(nama) { 1 } lain { 0 }");
    assert!(p.parse_expr().is_ok(), "kalau !f(x) {{..}} must parse");
}

#[test]
fn test_modul_block_flattens_functions_to_prefixed_top_level() {
    // `modul M { fungsi f(...) }` must flatten to a top-level `M_f` function so
    // the existing `M::f` -> `M_f` qualified-call resolution finds the user
    // definition (previously the module body was skipped/dropped entirely).
    let src = "modul teks { fungsi pecah(s: Teks, d: Teks) -> Senarai<Teks> kesan Bersih { pulang []; } }\nfungsi utama() -> Nombor kesan Bersih { 0 }";
    let prog = Parser::new(src).parse_program().expect("module program must parse");
    let names: Vec<&str> = prog
        .decls
        .iter()
        .filter_map(|d| match d {
            TopLevelDecl::Function { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        names.contains(&"teks_pecah"),
        "module function must flatten to teks_pecah; got {names:?}"
    );
    assert!(names.contains(&"utama"), "main must still be present; got {names:?}");
}
