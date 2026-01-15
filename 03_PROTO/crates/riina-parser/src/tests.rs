
use crate::Parser;
use riina_types::{Expr, Ty, SecurityLevel, Effect};

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
