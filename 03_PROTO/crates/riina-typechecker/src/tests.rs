// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

#[cfg(test)]
mod tests {
    use crate::{Context, type_check, TypeError};
    use riina_types::{Expr, Ty, Effect, SecurityLevel};

    #[test]
    fn test_literals() {
        let ctx = Context::new();
        assert_eq!(type_check(&ctx, &Expr::Int(42)).unwrap(), (Ty::Int, Effect::Pure));
        assert_eq!(type_check(&ctx, &Expr::Bool(true)).unwrap(), (Ty::Bool, Effect::Pure));
        assert_eq!(type_check(&ctx, &Expr::Unit).unwrap(), (Ty::Unit, Effect::Pure));
    }

    #[test]
    fn test_lam_app() {
        let ctx = Context::new();
        // fn(x: Int) x
        let id_int = Expr::Lam("x".to_string(), Ty::Int, Box::new(Expr::Var("x".to_string())));
        
        let (ty, _eff) = type_check(&ctx, &id_int).unwrap();
        match ty {
            Ty::Fn(arg, ret, fn_eff) => {
                assert_eq!(*arg, Ty::Int);
                assert_eq!(*ret, Ty::Int);
                assert_eq!(fn_eff, Effect::Pure);
            },
            _ => panic!("Expected Fn type"),
        }

        // (fn(x: Int) x) 42
        let app = Expr::App(Box::new(id_int), Box::new(Expr::Int(42)));
        assert_eq!(type_check(&ctx, &app).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_type_mismatch() {
        let ctx = Context::new();
        // if true { 1 } else { "no" }
        let if_err = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::String("no".to_string()))
        );
        match type_check(&ctx, &if_err) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Int);
                assert_eq!(found, Ty::String);
            },
            _ => panic!("Expected TypeMismatch"),
        }
    }

    #[test]
    fn test_effect_join() {
        // Mock effect test using Perform
        let ctx = Context::new();
        // perform Write 1
        let perf = Expr::Perform(Effect::Write, Box::new(Expr::Int(1)));
        let (ty, eff) = type_check(&ctx, &perf).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Write);
    }
    
    #[test]
    fn test_ref_deref() {
        let ctx = Context::new();
        // ref 1 @ Public
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public);
        let (ty, eff) = type_check(&ctx, &r).unwrap();
        match ty {
            Ty::Ref(inner, l) => {
                assert_eq!(*inner, Ty::Int);
                assert_eq!(l, SecurityLevel::Public);
            }
            _ => panic!("Expected Ref"),
        }
        assert_eq!(eff, Effect::Write); // Allocation is effectful?

        // !ref 1 @ Public
        let deref = Expr::Deref(Box::new(r));
        let (ty, eff) = type_check(&ctx, &deref).unwrap();
        assert_eq!(ty, Ty::Int);
        // Effect join: Write (from ref) + Read (from deref) = Write (since Write > Read)
        // Check levels: Pure(0) < Read(1) < Write(2)
        assert_eq!(eff, Effect::Write); 
    }
}
