// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

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
use crate::{Parser, ParseError, ParseErrorKind};
#[allow(unused_imports)]
use riina_types::{BinOp, Expr, Ty, SecurityLevel, Effect, TopLevelDecl, Program};

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
fn test_parse_int_zero() {
    // Input: Zero integer
    // Expected: Expr::Int(0)
    // Rationale: Zero is valid integer literal
    let mut p = Parser::new("0");
    assert_eq!(p.parse_expr().unwrap(), Expr::Int(0),
        "Zero must parse as valid integer");
}

#[test]
fn test_parse_int_large() {
    // Input: Large integer
    // Expected: Expr::Int with large value
    // Rationale: Large integers common in crypto
    let mut p = Parser::new("999999999");
    assert_eq!(p.parse_expr().unwrap(), Expr::Int(999_999_999),
        "Large integers must parse correctly");
}

#[test]
fn test_parse_bool_false() {
    // Input: false boolean
    // Expected: Expr::Bool(false)
    // Rationale: Both boolean values must work
    let mut p = Parser::new("false");
    assert_eq!(p.parse_expr().unwrap(), Expr::Bool(false),
        "false must parse as Expr::Bool(false)");
}

#[test]
fn test_parse_string_empty() {
    // Input: Empty string
    // Expected: Expr::String("")
    // Rationale: Empty strings are valid
    let mut p = Parser::new("\"\"");
    assert_eq!(p.parse_expr().unwrap(), Expr::String("".to_string()),
        "Empty string must parse correctly");
}

#[test]
fn test_parse_string_with_spaces() {
    // Input: String with spaces
    // Expected: Expr::String with spaces preserved
    // Rationale: Whitespace in strings must be preserved
    let mut p = Parser::new("\"hello world\"");
    assert_eq!(p.parse_expr().unwrap(), Expr::String("hello world".to_string()),
        "Spaces in strings must be preserved");
}

#[test]
fn test_parse_string_with_escapes() {
    // Input: String with escape sequences
    // Expected: Expr::String with interpreted escapes
    // Rationale: Escape sequences must be processed
    let mut p = Parser::new("\"hello\\nworld\"");
    assert_eq!(p.parse_expr().unwrap(), Expr::String("hello\nworld".to_string()),
        "Escape sequences in strings must be interpreted");
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
    assert_eq!(p.parse_expr().unwrap(), Expr::Var("x".to_string()),
        "Simple variable must parse");
}

#[test]
fn test_parse_var_long_name() {
    // Input: Long variable name
    // Expected: Expr::Var with full name
    // Rationale: No arbitrary length limits
    let mut p = Parser::new("very_long_variable_name_here");
    assert_eq!(p.parse_expr().unwrap(),
        Expr::Var("very_long_variable_name_here".to_string()),
        "Long variable names must be preserved");
}

#[test]
fn test_parse_var_with_numbers() {
    // Input: Variable with numbers
    // Expected: Expr::Var
    // Rationale: Numbers allowed after first char
    let mut p = Parser::new("x123");
    assert_eq!(p.parse_expr().unwrap(), Expr::Var("x123".to_string()),
        "Variables with numbers must parse");
}

#[test]
fn test_parse_var_underscore_prefix() {
    // Input: Variable with underscore prefix
    // Expected: Expr::Var
    // Rationale: Underscore-prefixed vars for unused
    let mut p = Parser::new("_unused");
    assert_eq!(p.parse_expr().unwrap(), Expr::Var("_unused".to_string()),
        "Underscore-prefixed variables must parse");
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
    assert_eq!(p.parse_expr().unwrap(), Expr::Unit,
        "() must parse as Unit");
}

#[test]
fn test_parse_parenthesized_expr() {
    // Input: Parenthesized expression
    // Expected: Inner expression (parens stripped)
    // Rationale: Parentheses for grouping
    let mut p = Parser::new("(42)");
    assert_eq!(p.parse_expr().unwrap(), Expr::Int(42),
        "Parenthesized expression must unwrap");
}

#[test]
fn test_parse_nested_parentheses() {
    // Input: Deeply nested parentheses
    // Expected: Inner expression
    // Rationale: Arbitrary nesting allowed
    let mut p = Parser::new("(((x)))");
    assert_eq!(p.parse_expr().unwrap(), Expr::Var("x".to_string()),
        "Nested parentheses must unwrap correctly");
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
        Expr::Let(x, e1, e2) => {
            assert_eq!(x, "x");
            assert_eq!(*e1, Expr::Int(1));
            assert_eq!(*e2, Expr::Int(2));
        },
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
        },
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
        },
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
        },
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
        },
        _ => panic!("Expected Assign"),
    }
}

#[test]
fn test_parse_ref_deref() {
    let mut p = Parser::new("!ref 1 @ Public");
    // Should parse as !(ref 1 @ Public) -> Deref(Ref(1, Public))
    match p.parse_expr().unwrap() {
        Expr::Deref(e) => {
            match *e {
                Expr::Ref(inner, level) => {
                    assert_eq!(*inner, Expr::Int(1));
                    assert_eq!(level, SecurityLevel::Public);
                },
                _ => panic!("Expected Ref inside Deref"),
            }
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
        },
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
                },
                _ => panic!("Expected Perform inside Handle"),
            }
            assert_eq!(x, "eff");
            assert_eq!(*h, Expr::Int(0));
        },
        _ => panic!("Expected Handle"),
    }
}

#[test]
fn test_parse_security() {
    let mut p = Parser::new("classify prove 1");
    match p.parse_expr().unwrap() {
        Expr::Classify(e) => {
            match *e {
                Expr::Prove(inner) => assert_eq!(*inner, Expr::Int(1)),
                _ => panic!("Expected Prove inside Classify"),
            }
        },
        _ => panic!("Expected Classify"),
    }
}

#[test]
fn test_parse_declassify() {
    let mut p = Parser::new("declassify x with proof");
    match p.parse_expr().unwrap() {
        Expr::Declassify(e1, e2) => {
            assert_eq!(*e1, Expr::Var("x".to_string()));
            assert_eq!(*e2, Expr::Var("proof".to_string()));
        },
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
        },
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
        Expr::Let(name, bound, body) => {
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
        Expr::Let(x, e1, body) => {
            assert_eq!(x, "x");
            assert_eq!(*e1, Expr::Int(1));
            match *body {
                Expr::Let(y, e2, inner) => {
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
        Expr::Let(name, bound, body) => {
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
        Expr::Deref(e) => {
            match *e {
                Expr::Deref(inner) => {
                    assert_eq!(*inner, Expr::Var("r".to_string()));
                }
                other => panic!("Expected inner Deref, got {:?}", other),
            }
        }
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
fn test_error_unexpected_token_in_if() {
    // Input: If without else
    // Expected: ParseError::UnexpectedToken
    // Rationale: Must require else branch
    let mut p = Parser::new("if true { 1 }");
    let result = p.parse_expr();
    assert!(result.is_err(), "If without else must produce error");
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
fn test_error_missing_with_in_declassify() {
    // Input: declassify without 'with'
    // Expected: ParseError
    // Rationale: declassify requires proof
    let mut p = Parser::new("declassify x proof");
    let result = p.parse_expr();
    assert!(result.is_err(), "declassify without 'with' must produce error");
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
        Expr::Let(name, bound, body) => {
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
        Expr::Let(name, bound, body) => {
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
            Box::new(Expr::BinOp(BinOp::Mul, Box::new(Expr::Int(2)), Box::new(Expr::Int(3))))
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
            Box::new(Expr::BinOp(BinOp::Sub, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)))),
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
            Box::new(Expr::BinOp(BinOp::Add, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)))),
            Box::new(Expr::Int(3))
        )
    );
}

#[test]
fn test_parse_binop_comparison_ops() {
    for (src, op) in [
        ("1 < 2", BinOp::Lt), ("1 > 2", BinOp::Gt),
        ("1 <= 2", BinOp::Le), ("1 >= 2", BinOp::Ge),
        ("1 != 2", BinOp::Ne),
    ] {
        let mut p = Parser::new(src);
        assert_eq!(
            p.parse_expr().unwrap(),
            Expr::BinOp(op, Box::new(Expr::Int(1)), Box::new(Expr::Int(2))),
            "Failed for: {}", src
        );
    }
}

#[test]
fn test_parse_binop_all_arithmetic() {
    for (src, op) in [
        ("1 + 2", BinOp::Add), ("1 - 2", BinOp::Sub),
        ("1 * 2", BinOp::Mul), ("1 / 2", BinOp::Div),
        ("1 % 2", BinOp::Mod),
    ] {
        let mut p = Parser::new(src);
        assert_eq!(
            p.parse_expr().unwrap(),
            Expr::BinOp(op, Box::new(Expr::Int(1)), Box::new(Expr::Int(2))),
            "Failed for: {}", src
        );
    }
}

#[test]
fn test_parse_binop_in_let() {
    // let x = 2 + 3; x
    let mut p = Parser::new("let x = 2 + 3; x");
    match p.parse_expr().unwrap() {
        Expr::Let(name, bound, body) => {
            assert_eq!(name, "x");
            assert_eq!(*bound, Expr::BinOp(BinOp::Add, Box::new(Expr::Int(2)), Box::new(Expr::Int(3))));
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
        Expr::Let(name, e1, e2) => {
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
        Expr::Let(n1, e1, rest) => {
            assert_eq!(n1, "_");
            assert_eq!(*e1, Expr::Int(1));
            match *rest {
                Expr::Let(n2, e2, e3) => {
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
        Expr::Let(n1, _, rest) => {
            assert_eq!(n1, "x");
            match *rest {
                Expr::Let(n2, _, body) => {
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
        Expr::Let(name, _, rest) => {
            assert_eq!(name, "x");
            match *rest {
                Expr::Let(n2, e, body) => {
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
        TopLevelDecl::Function { name, params, return_ty, .. } => {
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
    // Should be LetRec("f", ..., Lam("x", Int, Var("x")), App(Var("f"), Int(42)))
    match desugared {
        Expr::LetRec(name, _ty, lam, body) => {
            assert_eq!(name, "f");
            match *lam {
                Expr::Lam(p, ty, _) => {
                    assert_eq!(p, "x");
                    assert_eq!(ty, Ty::Int);
                }
                other => panic!("Expected Lam, got {:?}", other),
            }
            match *body {
                Expr::App(_, _) => {}
                other => panic!("Expected App, got {:?}", other),
            }
        }
        other => panic!("Expected LetRec, got {:?}", other),
    }
}

#[test]
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
    assert_eq!(result, Expr::If(
        Box::new(Expr::Var("x".to_string())),
        Box::new(Expr::Int(42)),
        Box::new(Expr::Int(0)),
    ));
}

#[test]
fn test_parse_guard_bahasa() {
    // pastikan x lain { 0 }; 42
    let mut p = Parser::new("pastikan x lain { 0 }; 42");
    let result = p.parse_expr().unwrap();
    assert_eq!(result, Expr::If(
        Box::new(Expr::Var("x".to_string())),
        Box::new(Expr::Int(42)),
        Box::new(Expr::Int(0)),
    ));
}

// ====================================================================
// Pipe Operator Tests (§5.3.3)
// ====================================================================

#[test]
fn test_parse_pipe_simple() {
    // x |> f  desugars to App(f, x)
    let mut p = Parser::new("x |> f");
    let result = p.parse_expr().unwrap();
    assert_eq!(result, Expr::App(
        Box::new(Expr::Var("f".to_string())),
        Box::new(Expr::Var("x".to_string())),
    ));
}

#[test]
fn test_parse_pipe_chain() {
    // x |> f |> g  desugars to App(g, App(f, x))
    let mut p = Parser::new("x |> f |> g");
    let result = p.parse_expr().unwrap();
    assert_eq!(result, Expr::App(
        Box::new(Expr::Var("g".to_string())),
        Box::new(Expr::App(
            Box::new(Expr::Var("f".to_string())),
            Box::new(Expr::Var("x".to_string())),
        )),
    ));
}

#[test]
fn test_parse_pipe_with_literal() {
    // 42 |> f
    let mut p = Parser::new("42 |> f");
    let result = p.parse_expr().unwrap();
    assert_eq!(result, Expr::App(
        Box::new(Expr::Var("f".to_string())),
        Box::new(Expr::Int(42)),
    ));
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
    assert_eq!(ty, Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Pure));
}

#[test]
fn test_parse_fn_type_with_effect() {
    let mut p = Parser::new("Fn(Int, Bool, Write)");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Write));
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
fn test_parse_unknown_type_errors() {
    let mut p = Parser::new("FooBarBaz");
    let result = p.parse_ty();
    assert!(result.is_err(), "Unknown type name should return error, not Unit");
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
    let src = r#"luaran "C" { fungsi test(a: CInt, b: CChar, c: CVoid) -> CInt; }"#;
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
    assert_eq!(ty, Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Mut));
}

#[test]
fn test_parse_fn_type_with_effect_alloc() {
    let mut p = Parser::new("Fn(Int, Bool, Alloc)");
    let ty = p.parse_ty().unwrap();
    assert_eq!(ty, Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Alloc));
}
