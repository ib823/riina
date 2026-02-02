// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

#[cfg(test)]
mod tests {
    use crate::{Context, type_check, TypeError};
    use riina_types::{BinOp, Expr, Ty, Effect, SecurityLevel};

    // ── Literals ──

    #[test]
    fn test_literals() {
        let ctx = Context::new();
        assert_eq!(type_check(&ctx, &Expr::Int(42)).unwrap(), (Ty::Int, Effect::Pure));
        assert_eq!(type_check(&ctx, &Expr::Bool(true)).unwrap(), (Ty::Bool, Effect::Pure));
        assert_eq!(type_check(&ctx, &Expr::Unit).unwrap(), (Ty::Unit, Effect::Pure));
    }

    #[test]
    fn test_string_literal() {
        let ctx = Context::new();
        assert_eq!(type_check(&ctx, &Expr::String("hello".into())).unwrap(), (Ty::String, Effect::Pure));
    }

    // ── Variables ──

    #[test]
    fn test_var_found() {
        let ctx = Context::new().extend("x".into(), Ty::Int);
        assert_eq!(type_check(&ctx, &Expr::Var("x".into())).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_var_not_found() {
        let ctx = Context::new();
        match type_check(&ctx, &Expr::Var("missing".into())) {
            Err(TypeError::VarNotFound(name)) => assert_eq!(name, "missing"),
            other => panic!("Expected VarNotFound, got {:?}", other),
        }
    }

    // ── Functions ──

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
    fn test_app_arg_mismatch() {
        let ctx = Context::new();
        let f = Expr::Lam("x".into(), Ty::Int, Box::new(Expr::Var("x".into())));
        let app = Expr::App(Box::new(f), Box::new(Expr::Bool(true)));
        match type_check(&ctx, &app) {
            Err(TypeError::TypeMismatch { expected: Ty::Int, found: Ty::Bool }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_app_non_function() {
        let ctx = Context::new();
        let app = Expr::App(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        match type_check(&ctx, &app) {
            Err(TypeError::ExpectedFunction(Ty::Int)) => {},
            other => panic!("Expected ExpectedFunction, got {:?}", other),
        }
    }

    // ── Products (Pair, Fst, Snd) ──

    #[test]
    fn test_pair() {
        let ctx = Context::new();
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Bool(true)));
        let (ty, eff) = type_check(&ctx, &pair).unwrap();
        assert_eq!(ty, Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Bool)));
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_fst() {
        let ctx = Context::new();
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Bool(true)));
        let fst = Expr::Fst(Box::new(pair));
        assert_eq!(type_check(&ctx, &fst).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_snd() {
        let ctx = Context::new();
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Bool(true)));
        let snd = Expr::Snd(Box::new(pair));
        assert_eq!(type_check(&ctx, &snd).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_fst_non_product() {
        let ctx = Context::new();
        let fst = Expr::Fst(Box::new(Expr::Int(1)));
        match type_check(&ctx, &fst) {
            Err(TypeError::ExpectedProduct(Ty::Int)) => {},
            other => panic!("Expected ExpectedProduct, got {:?}", other),
        }
    }

    #[test]
    fn test_snd_non_product() {
        let ctx = Context::new();
        let snd = Expr::Snd(Box::new(Expr::Bool(false)));
        match type_check(&ctx, &snd) {
            Err(TypeError::ExpectedProduct(Ty::Bool)) => {},
            other => panic!("Expected ExpectedProduct, got {:?}", other),
        }
    }

    // ── Sums (Inl, Inr, Case) ──

    #[test]
    fn test_inl() {
        let ctx = Context::new();
        let sum_ty = Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool));
        let inl = Expr::Inl(Box::new(Expr::Int(42)), sum_ty.clone());
        let (ty, eff) = type_check(&ctx, &inl).unwrap();
        assert_eq!(ty, sum_ty);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_inr() {
        let ctx = Context::new();
        let sum_ty = Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool));
        let inr = Expr::Inr(Box::new(Expr::Bool(true)), sum_ty.clone());
        let (ty, eff) = type_check(&ctx, &inr).unwrap();
        assert_eq!(ty, sum_ty);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_inl_type_mismatch() {
        let ctx = Context::new();
        let sum_ty = Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool));
        // Inject Bool into left (expects Int)
        let inl = Expr::Inl(Box::new(Expr::Bool(true)), sum_ty);
        match type_check(&ctx, &inl) {
            Err(TypeError::TypeMismatch { expected: Ty::Int, found: Ty::Bool }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_inr_type_mismatch() {
        let ctx = Context::new();
        let sum_ty = Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool));
        // Inject Int into right (expects Bool)
        let inr = Expr::Inr(Box::new(Expr::Int(1)), sum_ty);
        match type_check(&ctx, &inr) {
            Err(TypeError::TypeMismatch { expected: Ty::Bool, found: Ty::Int }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_inl_non_sum_annotation() {
        let ctx = Context::new();
        let inl = Expr::Inl(Box::new(Expr::Int(1)), Ty::Int);
        match type_check(&ctx, &inl) {
            Err(TypeError::ExpectedSum(Ty::Int)) => {},
            other => panic!("Expected ExpectedSum, got {:?}", other),
        }
    }

    #[test]
    fn test_case() {
        let ctx = Context::new();
        let sum_ty = Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool));
        let scrutinee = Expr::Inl(Box::new(Expr::Int(1)), sum_ty);
        // case scrutinee of inl x => x | inr y => 0
        let case_expr = Expr::Case(
            Box::new(scrutinee),
            "x".into(), Box::new(Expr::Var("x".into())),
            "y".into(), Box::new(Expr::Int(0)),
        );
        let (ty, eff) = type_check(&ctx, &case_expr).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_case_branch_mismatch() {
        let ctx = Context::new();
        let sum_ty = Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool));
        let scrutinee = Expr::Inl(Box::new(Expr::Int(1)), sum_ty);
        // Branches return different types
        let case_expr = Expr::Case(
            Box::new(scrutinee),
            "x".into(), Box::new(Expr::Var("x".into())),  // Int
            "y".into(), Box::new(Expr::Var("y".into())),  // Bool
        );
        match type_check(&ctx, &case_expr) {
            Err(TypeError::TypeMismatch { expected: Ty::Int, found: Ty::Bool }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_case_non_sum() {
        let ctx = Context::new();
        let case_expr = Expr::Case(
            Box::new(Expr::Int(1)),
            "x".into(), Box::new(Expr::Unit),
            "y".into(), Box::new(Expr::Unit),
        );
        match type_check(&ctx, &case_expr) {
            Err(TypeError::ExpectedSum(Ty::Int)) => {},
            other => panic!("Expected ExpectedSum, got {:?}", other),
        }
    }

    // ── If expressions ──

    #[test]
    fn test_if_ok() {
        let ctx = Context::new();
        let if_expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        assert_eq!(type_check(&ctx, &if_expr).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_if_non_bool_condition() {
        let ctx = Context::new();
        let if_expr = Expr::If(
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
            Box::new(Expr::Int(3)),
        );
        match type_check(&ctx, &if_expr) {
            Err(TypeError::TypeMismatch { expected: Ty::Bool, found: Ty::Int }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
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

    // ── Let ──

    #[test]
    fn test_let() {
        let ctx = Context::new();
        // let x = 1 in x
        let let_expr = Expr::Let(
            "x".into(),
            Box::new(Expr::Int(42)),
            Box::new(Expr::Var("x".into())),
        );
        assert_eq!(type_check(&ctx, &let_expr).unwrap(), (Ty::Int, Effect::Pure));
    }

    // ── LetRec ──

    #[test]
    fn test_letrec() {
        let ctx = Context::new();
        let fn_ty = Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure);
        // let rec f : Int -> Int = fn(x: Int) x in f
        let letrec = Expr::LetRec(
            "f".into(),
            fn_ty.clone(),
            Box::new(Expr::Lam("x".into(), Ty::Int, Box::new(Expr::Var("x".into())))),
            Box::new(Expr::Var("f".into())),
        );
        let (ty, eff) = type_check(&ctx, &letrec).unwrap();
        assert_eq!(ty, fn_ty);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_letrec_annotation_mismatch() {
        let ctx = Context::new();
        // Annotated as Int -> Bool but body is Int -> Int
        let letrec = Expr::LetRec(
            "f".into(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Pure),
            Box::new(Expr::Lam("x".into(), Ty::Int, Box::new(Expr::Var("x".into())))),
            Box::new(Expr::Unit),
        );
        match type_check(&ctx, &letrec) {
            Err(TypeError::AnnotationMismatch { .. }) => {},
            other => panic!("Expected AnnotationMismatch, got {:?}", other),
        }
    }

    // ── References (Ref, Deref, Assign) ──

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
        assert_eq!(eff, Effect::Write);

        // !ref 1 @ Public
        let deref = Expr::Deref(Box::new(r));
        let (ty, eff) = type_check(&ctx, &deref).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Write);
    }

    #[test]
    fn test_deref_non_ref() {
        let ctx = Context::new();
        let deref = Expr::Deref(Box::new(Expr::Int(1)));
        match type_check(&ctx, &deref) {
            Err(TypeError::ExpectedRef(Ty::Int)) => {},
            other => panic!("Expected ExpectedRef, got {:?}", other),
        }
    }

    #[test]
    fn test_assign() {
        let ctx = Context::new();
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public);
        let assign = Expr::Assign(Box::new(r), Box::new(Expr::Int(2)));
        let (ty, eff) = type_check(&ctx, &assign).unwrap();
        assert_eq!(ty, Ty::Unit);
        assert_eq!(eff, Effect::Write);
    }

    #[test]
    fn test_assign_type_mismatch() {
        let ctx = Context::new();
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public);
        let assign = Expr::Assign(Box::new(r), Box::new(Expr::Bool(true)));
        match type_check(&ctx, &assign) {
            Err(TypeError::TypeMismatch { expected: Ty::Int, found: Ty::Bool }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_assign_non_ref() {
        let ctx = Context::new();
        let assign = Expr::Assign(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        match type_check(&ctx, &assign) {
            Err(TypeError::ExpectedRef(Ty::Int)) => {},
            other => panic!("Expected ExpectedRef, got {:?}", other),
        }
    }

    // ── Security (Classify, Declassify) ──

    #[test]
    fn test_classify() {
        let ctx = Context::new();
        let classify = Expr::Classify(Box::new(Expr::Int(42)));
        let (ty, eff) = type_check(&ctx, &classify).unwrap();
        assert_eq!(ty, Ty::Secret(Box::new(Ty::Int)));
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_declassify_secret() {
        let ctx = Context::new();
        let classified = Expr::Classify(Box::new(Expr::Int(42)));
        let declassify = Expr::Declassify(Box::new(classified), Box::new(Expr::Unit));
        let (ty, eff) = type_check(&ctx, &declassify).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_declassify_non_secret_is_identity() {
        let ctx = Context::new();
        let declassify = Expr::Declassify(Box::new(Expr::Int(1)), Box::new(Expr::Unit));
        let (ty, eff) = type_check(&ctx, &declassify).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    // ── Prove ──

    #[test]
    fn test_prove() {
        let ctx = Context::new();
        let prove = Expr::Prove(Box::new(Expr::Bool(true)));
        let (ty, eff) = type_check(&ctx, &prove).unwrap();
        assert_eq!(ty, Ty::Proof(Box::new(Ty::Bool)));
        assert_eq!(eff, Effect::Pure);
    }

    // ── Effects (Perform, Handle) ──

    #[test]
    fn test_effect_join() {
        let ctx = Context::new();
        // perform Write 1
        let perf = Expr::Perform(Effect::Write, Box::new(Expr::Int(1)));
        let (ty, eff) = type_check(&ctx, &perf).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Write);
    }

    #[test]
    fn test_perform_network() {
        let ctx = Context::new();
        let perf = Expr::Perform(Effect::Network, Box::new(Expr::String("data".into())));
        let (ty, eff) = type_check(&ctx, &perf).unwrap();
        assert_eq!(ty, Ty::String);
        assert_eq!(eff, Effect::Network);
    }

    #[test]
    fn test_handle() {
        let ctx = Context::new();
        let body = Expr::Perform(Effect::Write, Box::new(Expr::Int(1)));
        let handler = Expr::Int(0);
        let handle = Expr::Handle(Box::new(body), "x".into(), Box::new(handler));
        let (ty, eff) = type_check(&ctx, &handle).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    // ── Capabilities (Require, Grant) ──

    #[test]
    fn test_require() {
        let ctx = Context::new();
        let require = Expr::Require(Effect::FileSystem, Box::new(Expr::Int(1)));
        let (ty, eff) = type_check(&ctx, &require).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::FileSystem);
    }

    #[test]
    fn test_grant() {
        let ctx = Context::new();
        let grant = Expr::Grant(Effect::Network, Box::new(Expr::Int(1)));
        let (ty, eff) = type_check(&ctx, &grant).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    // ── Loc (runtime locations) ──

    #[test]
    fn test_loc() {
        let ctx = Context::new();
        let (ty, eff) = type_check(&ctx, &Expr::Loc(0)).unwrap();
        assert_eq!(ty, Ty::Ref(Box::new(Ty::Unit), SecurityLevel::Public));
        assert_eq!(eff, Effect::Pure);
    }

    // ── BinOp ──

    #[test]
    fn test_binop_add_int() {
        let ctx = Context::new();
        let add = Expr::BinOp(BinOp::Add, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        assert_eq!(type_check(&ctx, &add).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_binop_add_string() {
        let ctx = Context::new();
        let add = Expr::BinOp(BinOp::Add, Box::new(Expr::String("a".into())), Box::new(Expr::String("b".into())));
        assert_eq!(type_check(&ctx, &add).unwrap(), (Ty::String, Effect::Pure));
    }

    #[test]
    fn test_binop_add_mismatch() {
        let ctx = Context::new();
        let add = Expr::BinOp(BinOp::Add, Box::new(Expr::Int(1)), Box::new(Expr::Bool(true)));
        assert!(type_check(&ctx, &add).is_err());
    }

    #[test]
    fn test_binop_sub() {
        let ctx = Context::new();
        let sub = Expr::BinOp(BinOp::Sub, Box::new(Expr::Int(5)), Box::new(Expr::Int(3)));
        assert_eq!(type_check(&ctx, &sub).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_binop_mul() {
        let ctx = Context::new();
        let mul = Expr::BinOp(BinOp::Mul, Box::new(Expr::Int(2)), Box::new(Expr::Int(3)));
        assert_eq!(type_check(&ctx, &mul).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_binop_div() {
        let ctx = Context::new();
        let div = Expr::BinOp(BinOp::Div, Box::new(Expr::Int(6)), Box::new(Expr::Int(2)));
        assert_eq!(type_check(&ctx, &div).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_binop_mod() {
        let ctx = Context::new();
        let modop = Expr::BinOp(BinOp::Mod, Box::new(Expr::Int(7)), Box::new(Expr::Int(3)));
        assert_eq!(type_check(&ctx, &modop).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_binop_arith_non_int_lhs() {
        let ctx = Context::new();
        let sub = Expr::BinOp(BinOp::Sub, Box::new(Expr::Bool(true)), Box::new(Expr::Int(1)));
        match type_check(&ctx, &sub) {
            Err(TypeError::TypeMismatch { expected: Ty::Int, found: Ty::Bool }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_binop_arith_non_int_rhs() {
        let ctx = Context::new();
        let mul = Expr::BinOp(BinOp::Mul, Box::new(Expr::Int(1)), Box::new(Expr::String("x".into())));
        match type_check(&ctx, &mul) {
            Err(TypeError::TypeMismatch { expected: Ty::Int, found: Ty::String }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_binop_eq() {
        let ctx = Context::new();
        let eq = Expr::BinOp(BinOp::Eq, Box::new(Expr::Int(1)), Box::new(Expr::Int(1)));
        assert_eq!(type_check(&ctx, &eq).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_ne_bool() {
        let ctx = Context::new();
        let ne = Expr::BinOp(BinOp::Ne, Box::new(Expr::Bool(true)), Box::new(Expr::Bool(false)));
        assert_eq!(type_check(&ctx, &ne).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_eq_string() {
        let ctx = Context::new();
        let eq = Expr::BinOp(BinOp::Eq, Box::new(Expr::String("a".into())), Box::new(Expr::String("b".into())));
        assert_eq!(type_check(&ctx, &eq).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_eq_type_mismatch() {
        let ctx = Context::new();
        let eq = Expr::BinOp(BinOp::Eq, Box::new(Expr::Int(1)), Box::new(Expr::Bool(true)));
        assert!(type_check(&ctx, &eq).is_err());
    }

    #[test]
    fn test_binop_lt() {
        let ctx = Context::new();
        let lt = Expr::BinOp(BinOp::Lt, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        assert_eq!(type_check(&ctx, &lt).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_le() {
        let ctx = Context::new();
        let le = Expr::BinOp(BinOp::Le, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        assert_eq!(type_check(&ctx, &le).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_gt() {
        let ctx = Context::new();
        let gt = Expr::BinOp(BinOp::Gt, Box::new(Expr::Int(3)), Box::new(Expr::Int(1)));
        assert_eq!(type_check(&ctx, &gt).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_ge() {
        let ctx = Context::new();
        let ge = Expr::BinOp(BinOp::Ge, Box::new(Expr::Int(3)), Box::new(Expr::Int(1)));
        assert_eq!(type_check(&ctx, &ge).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_comparison_non_int() {
        let ctx = Context::new();
        let lt = Expr::BinOp(BinOp::Lt, Box::new(Expr::Bool(true)), Box::new(Expr::Int(1)));
        match type_check(&ctx, &lt) {
            Err(TypeError::TypeMismatch { expected: Ty::Int, found: Ty::Bool }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_binop_and() {
        let ctx = Context::new();
        let and = Expr::BinOp(BinOp::And, Box::new(Expr::Bool(true)), Box::new(Expr::Bool(false)));
        assert_eq!(type_check(&ctx, &and).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_or() {
        let ctx = Context::new();
        let or = Expr::BinOp(BinOp::Or, Box::new(Expr::Bool(false)), Box::new(Expr::Bool(true)));
        assert_eq!(type_check(&ctx, &or).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_and_non_bool() {
        let ctx = Context::new();
        let and = Expr::BinOp(BinOp::And, Box::new(Expr::Int(1)), Box::new(Expr::Bool(true)));
        match type_check(&ctx, &and) {
            Err(TypeError::TypeMismatch { expected: Ty::Bool, found: Ty::Int }) => {},
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    // ── FFICall ──

    #[test]
    fn test_ffi_call() {
        let ctx = Context::new();
        let ffi = Expr::FFICall {
            name: "c_printf".into(),
            args: vec![Expr::String("hello".into())],
            ret_ty: Ty::Int,
        };
        let (ty, eff) = type_check(&ctx, &ffi).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::System);
    }

    #[test]
    fn test_ffi_call_no_args() {
        let ctx = Context::new();
        let ffi = Expr::FFICall {
            name: "c_getpid".into(),
            args: vec![],
            ret_ty: Ty::Int,
        };
        let (ty, eff) = type_check(&ctx, &ffi).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::System);
    }

    // ── Ref with Secret level ──

    #[test]
    fn test_ref_secret_level() {
        let ctx = Context::new();
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Secret);
        let (ty, _eff) = type_check(&ctx, &r).unwrap();
        assert_eq!(ty, Ty::Ref(Box::new(Ty::Int), SecurityLevel::Secret));
    }

    // ── Effect accumulation ──

    #[test]
    fn test_effect_accumulation_in_pair() {
        let ctx = Context::new();
        let left = Expr::Perform(Effect::Read, Box::new(Expr::Int(1)));
        let right = Expr::Perform(Effect::Write, Box::new(Expr::Int(2)));
        let pair = Expr::Pair(Box::new(left), Box::new(right));
        let (_ty, eff) = type_check(&ctx, &pair).unwrap();
        // Write > Read, so join should be Write
        assert_eq!(eff, Effect::Write);
    }

    #[test]
    fn test_effect_accumulation_in_app() {
        let ctx = Context::new();
        // fn with System effect applied to a Read-effectful arg
        let f = Expr::Lam("x".into(), Ty::Int, Box::new(
            Expr::Perform(Effect::System, Box::new(Expr::Var("x".into())))
        ));
        let arg = Expr::Perform(Effect::Read, Box::new(Expr::Int(1)));
        let app = Expr::App(Box::new(f), Box::new(arg));
        let (_ty, eff) = type_check(&ctx, &app).unwrap();
        assert_eq!(eff, Effect::System);
    }

    // ── Nested expressions ──

    #[test]
    fn test_nested_let_in_if() {
        let ctx = Context::new();
        // let x = 1 in if true then x else 0
        let expr = Expr::Let(
            "x".into(),
            Box::new(Expr::Int(1)),
            Box::new(Expr::If(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Var("x".into())),
                Box::new(Expr::Int(0)),
            )),
        );
        assert_eq!(type_check(&ctx, &expr).unwrap(), (Ty::Int, Effect::Pure));
    }

    #[test]
    fn test_classify_then_prove() {
        let ctx = Context::new();
        let expr = Expr::Prove(Box::new(Expr::Classify(Box::new(Expr::Int(1)))));
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Proof(Box::new(Ty::Secret(Box::new(Ty::Int)))));
        assert_eq!(eff, Effect::Pure);
    }
}
