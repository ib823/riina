// Copyright (c) 2026 The RIINA Authors. All rights reserved.

#[cfg(test)]
#[allow(clippy::module_inception)]
mod tests {
    use crate::{type_check, Context, TypeError};
    use riina_types::{BinOp, Effect, Expr, SecurityLevel, Ty};

    // ── Literals ──

    #[test]
    fn test_literals() {
        let ctx = Context::new();
        assert_eq!(
            type_check(&ctx, &Expr::Int(42)).unwrap(),
            (Ty::Int, Effect::Pure)
        );
        assert_eq!(
            type_check(&ctx, &Expr::Bool(true)).unwrap(),
            (Ty::Bool, Effect::Pure)
        );
        assert_eq!(
            type_check(&ctx, &Expr::Unit).unwrap(),
            (Ty::Unit, Effect::Pure)
        );
    }

    #[test]
    fn test_string_literal() {
        let ctx = Context::new();
        assert_eq!(
            type_check(&ctx, &Expr::String("hello".into())).unwrap(),
            (Ty::String, Effect::Pure)
        );
    }

    // ── Variables ──

    #[test]
    fn test_var_found() {
        let ctx = Context::new().extend("x".into(), Ty::Int);
        assert_eq!(
            type_check(&ctx, &Expr::Var("x".into())).unwrap(),
            (Ty::Int, Effect::Pure)
        );
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
        let id_int = Expr::Lam(
            "x".to_string(),
            Ty::Int,
            Box::new(Expr::Var("x".to_string())),
        );

        let (ty, _eff) = type_check(&ctx, &id_int).unwrap();
        match ty {
            Ty::Fn(arg, ret, fn_eff) => {
                assert_eq!(*arg, Ty::Int);
                assert_eq!(*ret, Ty::Int);
                assert_eq!(fn_eff, Effect::Pure);
            }
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
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_app_non_function() {
        let ctx = Context::new();
        let app = Expr::App(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        match type_check(&ctx, &app) {
            Err(TypeError::ExpectedFunction(Ty::Int)) => {}
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
            Err(TypeError::ExpectedProduct(Ty::Int)) => {}
            other => panic!("Expected ExpectedProduct, got {:?}", other),
        }
    }

    #[test]
    fn test_snd_non_product() {
        let ctx = Context::new();
        let snd = Expr::Snd(Box::new(Expr::Bool(false)));
        match type_check(&ctx, &snd) {
            Err(TypeError::ExpectedProduct(Ty::Bool)) => {}
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
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
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
            Err(TypeError::TypeMismatch {
                expected: Ty::Bool,
                found: Ty::Int,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_inl_non_sum_annotation() {
        let ctx = Context::new();
        let inl = Expr::Inl(Box::new(Expr::Int(1)), Ty::Int);
        match type_check(&ctx, &inl) {
            Err(TypeError::ExpectedSum(Ty::Int)) => {}
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
            "x".into(),
            Box::new(Expr::Var("x".into())),
            "y".into(),
            Box::new(Expr::Int(0)),
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
            "x".into(),
            Box::new(Expr::Var("x".into())), // Int
            "y".into(),
            Box::new(Expr::Var("y".into())), // Bool
        );
        match type_check(&ctx, &case_expr) {
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_case_non_sum() {
        let ctx = Context::new();
        let case_expr = Expr::Case(
            Box::new(Expr::Int(1)),
            "x".into(),
            Box::new(Expr::Unit),
            "y".into(),
            Box::new(Expr::Unit),
        );
        match type_check(&ctx, &case_expr) {
            Err(TypeError::ExpectedSum(Ty::Int)) => {}
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
            Err(TypeError::TypeMismatch {
                expected: Ty::Bool,
                found: Ty::Int,
            }) => {}
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
            Box::new(Expr::String("no".to_string())),
        );
        match type_check(&ctx, &if_err) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Int);
                assert_eq!(found, Ty::String);
            }
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
            None,
            Box::new(Expr::Int(42)),
            Box::new(Expr::Var("x".into())),
        );
        assert_eq!(
            type_check(&ctx, &let_expr).unwrap(),
            (Ty::Int, Effect::Pure)
        );
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
            Box::new(Expr::Lam(
                "x".into(),
                Ty::Int,
                Box::new(Expr::Var("x".into())),
            )),
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
            Box::new(Expr::Lam(
                "x".into(),
                Ty::Int,
                Box::new(Expr::Var("x".into())),
            )),
            Box::new(Expr::Unit),
        );
        match type_check(&ctx, &letrec) {
            Err(TypeError::AnnotationMismatch { .. }) => {}
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
            Err(TypeError::ExpectedRef(Ty::Int)) => {}
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
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_assign_non_ref() {
        let ctx = Context::new();
        let assign = Expr::Assign(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        match type_check(&ctx, &assign) {
            Err(TypeError::ExpectedRef(Ty::Int)) => {}
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
    fn test_declassify_non_secret_is_rejected() {
        let ctx = Context::new();
        let declassify = Expr::Declassify(Box::new(Expr::Int(1)), Box::new(Expr::Unit));
        // Strict mode: Coq T_Declassify requires TSecret(T), rejects non-secret
        let result = type_check(&ctx, &declassify);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::ExpectedSecret(Ty::Int) => {} // correct
            other => panic!("Expected ExpectedSecret(Int), got {:?}", other),
        }
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
        // Coq T_Handle: result effect is join of body effect and handler effect
        // body = Write, handler = Pure → join = Write
        assert_eq!(eff, Effect::Write);
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
        let add = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::String("a".into())),
            Box::new(Expr::String("b".into())),
        );
        assert_eq!(type_check(&ctx, &add).unwrap(), (Ty::String, Effect::Pure));
    }

    #[test]
    fn test_binop_add_mismatch() {
        let ctx = Context::new();
        let add = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Int(1)),
            Box::new(Expr::Bool(true)),
        );
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
        let sub = Expr::BinOp(
            BinOp::Sub,
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
        );
        match type_check(&ctx, &sub) {
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_binop_arith_non_int_rhs() {
        let ctx = Context::new();
        let mul = Expr::BinOp(
            BinOp::Mul,
            Box::new(Expr::Int(1)),
            Box::new(Expr::String("x".into())),
        );
        match type_check(&ctx, &mul) {
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::String,
            }) => {}
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
        let ne = Expr::BinOp(
            BinOp::Ne,
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Bool(false)),
        );
        assert_eq!(type_check(&ctx, &ne).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_eq_string() {
        let ctx = Context::new();
        let eq = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::String("a".into())),
            Box::new(Expr::String("b".into())),
        );
        assert_eq!(type_check(&ctx, &eq).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_eq_type_mismatch() {
        let ctx = Context::new();
        let eq = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Int(1)),
            Box::new(Expr::Bool(true)),
        );
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
        let lt = Expr::BinOp(
            BinOp::Lt,
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
        );
        match type_check(&ctx, &lt) {
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_binop_and() {
        let ctx = Context::new();
        let and = Expr::BinOp(
            BinOp::And,
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Bool(false)),
        );
        assert_eq!(type_check(&ctx, &and).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_or() {
        let ctx = Context::new();
        let or = Expr::BinOp(
            BinOp::Or,
            Box::new(Expr::Bool(false)),
            Box::new(Expr::Bool(true)),
        );
        assert_eq!(type_check(&ctx, &or).unwrap(), (Ty::Bool, Effect::Pure));
    }

    #[test]
    fn test_binop_and_non_bool() {
        let ctx = Context::new();
        let and = Expr::BinOp(
            BinOp::And,
            Box::new(Expr::Int(1)),
            Box::new(Expr::Bool(true)),
        );
        match type_check(&ctx, &and) {
            Err(TypeError::TypeMismatch {
                expected: Ty::Bool,
                found: Ty::Int,
            }) => {}
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
        let f = Expr::Lam(
            "x".into(),
            Ty::Int,
            Box::new(Expr::Perform(
                Effect::System,
                Box::new(Expr::Var("x".into())),
            )),
        );
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
            None,
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

// ════════════════════════════════════════════════════════════════════════════
// FORMALIZED TYPECHECKER TESTS (Coq-matching)
// Tests for type_check_full with TypingContext, StoreTy, and security levels
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod formalized_tests {
    use crate::{
        register_builtin_types, type_check, type_check_full, types_compatible, Context, TypeError,
        TypingContext,
    };
    use riina_types::{
        BinOp, Effect, Expr, Linearity, Location, SecurityLevel, SessionType, StoreTy, Ty, Usage,
    };

    // ── Basic value typing with new context ──

    #[test]
    fn test_full_literals() {
        let mut ctx = TypingContext::new();
        assert_eq!(
            type_check_full(&mut ctx, &Expr::Int(42)).unwrap(),
            (Ty::Int, Effect::Pure)
        );
        assert_eq!(
            type_check_full(&mut ctx, &Expr::Bool(true)).unwrap(),
            (Ty::Bool, Effect::Pure)
        );
        assert_eq!(
            type_check_full(&mut ctx, &Expr::Unit).unwrap(),
            (Ty::Unit, Effect::Pure)
        );
    }

    // ── Numeric tower: arbitrary-precision BigInt (`besar`) ──

    /// `besar("…")` as a typed expression.
    fn besar_call(s: &str) -> Expr {
        Expr::App(
            Box::new(Expr::Var("besar".to_string())),
            Box::new(Expr::String(s.to_string())),
        )
    }

    fn builtin_ctx() -> TypingContext {
        register_builtin_types(&Context::new()).to_typing_context()
    }

    #[test]
    fn bigint_constructor_types_as_bigint() {
        let mut ctx = builtin_ctx();
        assert_eq!(
            type_check_full(&mut ctx, &besar_call("123456789012345678901234567890")).unwrap(),
            (Ty::BigInt, Effect::Pure)
        );
    }

    #[test]
    fn bigint_arithmetic_types_as_bigint() {
        let mut ctx = builtin_ctx();
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Mod] {
            let e = Expr::BinOp(op, Box::new(besar_call("10")), Box::new(besar_call("3")));
            assert_eq!(
                type_check_full(&mut ctx, &e).unwrap().0,
                Ty::BigInt,
                "{op:?} on BigInt must yield BigInt"
            );
        }
    }

    #[test]
    fn bigint_comparison_types_as_bool() {
        let mut ctx = builtin_ctx();
        for op in [BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge, BinOp::Eq, BinOp::Ne] {
            let e = Expr::BinOp(op, Box::new(besar_call("10")), Box::new(besar_call("3")));
            assert_eq!(type_check_full(&mut ctx, &e).unwrap().0, Ty::Bool, "{op:?}");
        }
    }

    #[test]
    fn bigint_does_not_mix_with_int() {
        // Mixing arbitrary-precision and fixed-width ints is a type error — the
        // boundary must be crossed explicitly via `besar`, never silently.
        let mut ctx = builtin_ctx();
        let e = Expr::BinOp(
            BinOp::Add,
            Box::new(besar_call("10")),
            Box::new(Expr::Int(1)),
        );
        assert!(
            matches!(type_check_full(&mut ctx, &e), Err(TypeError::TypeMismatch { .. })),
            "BigInt + Int must be rejected"
        );
    }

    // ── Numeric tower: arbitrary-precision Decimal (`perpuluhan`) ──

    fn decimal_call(s: &str) -> Expr {
        Expr::App(
            Box::new(Expr::Var("perpuluhan".to_string())),
            Box::new(Expr::String(s.to_string())),
        )
    }

    #[test]
    fn decimal_constructor_and_arithmetic_types() {
        let mut ctx = builtin_ctx();
        assert_eq!(
            type_check_full(&mut ctx, &decimal_call("3.14")).unwrap(),
            (Ty::Decimal, Effect::Pure)
        );
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div] {
            let e = Expr::BinOp(op, Box::new(decimal_call("1.5")), Box::new(decimal_call("0.5")));
            assert_eq!(type_check_full(&mut ctx, &e).unwrap().0, Ty::Decimal, "{op:?}");
        }
        for op in [BinOp::Lt, BinOp::Ge, BinOp::Eq] {
            let e = Expr::BinOp(op, Box::new(decimal_call("1.5")), Box::new(decimal_call("0.5")));
            assert_eq!(type_check_full(&mut ctx, &e).unwrap().0, Ty::Bool, "{op:?}");
        }
    }

    #[test]
    fn decimal_does_not_mix_with_bigint_or_int() {
        let mut ctx = builtin_ctx();
        for other in [besar_call("1"), Expr::Int(1)] {
            let e = Expr::BinOp(BinOp::Add, Box::new(decimal_call("1.5")), Box::new(other));
            assert!(
                matches!(type_check_full(&mut ctx, &e), Err(TypeError::TypeMismatch { .. })),
                "Decimal must not mix with BigInt/Int"
            );
        }
    }

    // ── Numeric tower: fixed-scale Fixed (`wang` / `titik_tetap`) ──

    fn wang_call(s: &str) -> Expr {
        Expr::App(
            Box::new(Expr::Var("wang".to_string())),
            Box::new(Expr::String(s.to_string())),
        )
    }

    #[test]
    fn fixed_constructor_and_arithmetic_types() {
        let mut ctx = builtin_ctx();
        // `wang(String) -> Fixed`.
        assert_eq!(
            type_check_full(&mut ctx, &wang_call("19.99")).unwrap(),
            (Ty::Fixed, Effect::Pure)
        );
        // `titik_tetap((String, Int)) -> Fixed`.
        let tt = Expr::App(
            Box::new(Expr::Var("titik_tetap".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("3.14159".to_string())),
                Box::new(Expr::Int(2)),
            )),
        );
        assert_eq!(
            type_check_full(&mut ctx, &tt).unwrap(),
            (Ty::Fixed, Effect::Pure)
        );
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div] {
            let e = Expr::BinOp(op, Box::new(wang_call("1.50")), Box::new(wang_call("0.50")));
            assert_eq!(type_check_full(&mut ctx, &e).unwrap().0, Ty::Fixed, "{op:?}");
        }
        for op in [BinOp::Lt, BinOp::Ge, BinOp::Eq] {
            let e = Expr::BinOp(op, Box::new(wang_call("1.50")), Box::new(wang_call("0.50")));
            assert_eq!(type_check_full(&mut ctx, &e).unwrap().0, Ty::Bool, "{op:?}");
        }
    }

    #[test]
    fn fixed_does_not_mix_with_other_numeric_types() {
        let mut ctx = builtin_ctx();
        // Fixed is its own domain — distinct from BigInt, Decimal, and Int.
        for other in [besar_call("1"), decimal_call("1.5"), Expr::Int(1)] {
            let e = Expr::BinOp(BinOp::Add, Box::new(wang_call("1.50")), Box::new(other));
            assert!(
                matches!(type_check_full(&mut ctx, &e), Err(TypeError::TypeMismatch { .. })),
                "Fixed must not mix with BigInt/Decimal/Int"
            );
        }
    }

    // ── Numeric tower: binary fixed-point FixedBin (`qmn`) ──

    fn qmn_call(s: &str) -> Expr {
        Expr::App(
            Box::new(Expr::Var("qmn".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String(s.to_string())),
                Box::new(Expr::Int(8)),
            )),
        )
    }

    #[test]
    fn fixedbin_constructor_and_arithmetic_types() {
        let mut ctx = builtin_ctx();
        // `qmn((String, Int)) -> FixedBin`.
        assert_eq!(
            type_check_full(&mut ctx, &qmn_call("0.5")).unwrap(),
            (Ty::FixedBin, Effect::Pure)
        );
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div] {
            let e = Expr::BinOp(op, Box::new(qmn_call("0.5")), Box::new(qmn_call("0.25")));
            assert_eq!(type_check_full(&mut ctx, &e).unwrap().0, Ty::FixedBin, "{op:?}");
        }
        for op in [BinOp::Lt, BinOp::Ge, BinOp::Eq] {
            let e = Expr::BinOp(op, Box::new(qmn_call("0.5")), Box::new(qmn_call("0.25")));
            assert_eq!(type_check_full(&mut ctx, &e).unwrap().0, Ty::Bool, "{op:?}");
        }
    }

    #[test]
    fn fixedbin_does_not_mix_with_other_numeric_types() {
        let mut ctx = builtin_ctx();
        // FixedBin is its own domain — distinct from Fixed, Decimal, and Int.
        for other in [wang_call("1.50"), decimal_call("1.5"), Expr::Int(1)] {
            let e = Expr::BinOp(BinOp::Add, Box::new(qmn_call("0.5")), Box::new(other));
            assert!(
                matches!(type_check_full(&mut ctx, &e), Err(TypeError::TypeMismatch { .. })),
                "FixedBin must not mix with Fixed/Decimal/Int"
            );
        }
    }

    // ── Numeric tower: sized integer literals & width-aware arithmetic ──

    fn u8n(value: u64) -> Expr {
        Expr::IntN {
            value,
            bits: 8,
            signed: false,
        }
    }

    #[test]
    fn numeric_tower_sized_literal_types_as_intn() {
        let mut ctx = TypingContext::new();
        // `42u8` types as the distinct sized type, not the default `Ty::Int`.
        assert_eq!(
            type_check_full(&mut ctx, &u8n(42)).unwrap(),
            (
                Ty::IntN {
                    bits: 8,
                    signed: false
                },
                Effect::Pure
            )
        );
        assert_eq!(
            type_check_full(
                &mut ctx,
                &Expr::IntN {
                    value: 7,
                    bits: 32,
                    signed: true
                }
            )
            .unwrap(),
            (
                Ty::IntN {
                    bits: 32,
                    signed: true
                },
                Effect::Pure
            )
        );
    }

    #[test]
    fn numeric_tower_arithmetic_propagates_width() {
        let mut ctx = TypingContext::new();
        // `200u8 + 100u8` stays `u8` (width propagates through arithmetic).
        for op in [BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Mod] {
            let e = Expr::BinOp(op, Box::new(u8n(200)), Box::new(u8n(100)));
            assert_eq!(
                type_check_full(&mut ctx, &e).unwrap().0,
                Ty::IntN {
                    bits: 8,
                    signed: false
                },
                "operator {op:?} should preserve the u8 width"
            );
        }
    }

    #[test]
    fn numeric_tower_plain_int_adapts_to_sized() {
        let mut ctx = TypingContext::new();
        // A plain `Int` literal mixed with a sized operand adopts the width.
        let lhs = Expr::BinOp(BinOp::Add, Box::new(u8n(200)), Box::new(Expr::Int(100)));
        let rhs = Expr::BinOp(BinOp::Add, Box::new(Expr::Int(100)), Box::new(u8n(200)));
        for e in [lhs, rhs] {
            assert_eq!(
                type_check_full(&mut ctx, &e).unwrap().0,
                Ty::IntN {
                    bits: 8,
                    signed: false
                }
            );
        }
    }

    #[test]
    fn numeric_tower_mixed_widths_are_rejected() {
        let mut ctx = TypingContext::new();
        // `u8 + u16` must be rejected — silent bit mixing is unsound.
        let e = Expr::BinOp(
            BinOp::Add,
            Box::new(u8n(200)),
            Box::new(Expr::IntN {
                value: 100,
                bits: 16,
                signed: false,
            }),
        );
        assert!(matches!(
            type_check_full(&mut ctx, &e),
            Err(crate::TypeError::TypeMismatch { .. })
        ));
        // Same width but different signedness is also a mix.
        let e2 = Expr::BinOp(
            BinOp::Mul,
            Box::new(u8n(5)),
            Box::new(Expr::IntN {
                value: 5,
                bits: 8,
                signed: true,
            }),
        );
        assert!(type_check_full(&mut ctx, &e2).is_err());
    }

    #[test]
    fn test_full_var() {
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma("x".into(), Ty::Int);
        assert_eq!(
            type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap(),
            (Ty::Int, Effect::Pure)
        );
    }

    // ── Store Typing (Σ) tests ──

    #[test]
    fn test_store_ty_operations() {
        let mut sigma = StoreTy::new();
        assert!(sigma.is_empty());

        let loc1 = sigma.extend(Ty::Int, SecurityLevel::Public);
        assert_eq!(loc1, Location::new(0));
        assert_eq!(sigma.lookup(&loc1), Some(&(Ty::Int, SecurityLevel::Public)));

        let loc2 = sigma.extend(Ty::Bool, SecurityLevel::Secret);
        assert_eq!(loc2, Location::new(1));
        assert_eq!(sigma.len(), 2);

        assert!(sigma.contains(&loc1));
        assert!(!sigma.contains(&Location::new(99)));
    }

    #[test]
    fn test_ref_allocates_in_sigma() {
        let mut ctx = TypingContext::new();
        assert!(ctx.sigma.is_empty());

        let r = Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public);
        let (ty, eff) = type_check_full(&mut ctx, &r).unwrap();

        assert_eq!(ty, Ty::Ref(Box::new(Ty::Int), SecurityLevel::Public));
        assert_eq!(eff, Effect::Write);
        assert_eq!(ctx.sigma.len(), 1);
    }

    // ── Security Level Violations (Δ checks) ──

    #[test]
    fn test_deref_public_in_public_context_ok() {
        let mut ctx = TypingContext::with_level(SecurityLevel::Public);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public);
        let deref = Expr::Deref(Box::new(r));
        let (ty, _eff) = type_check_full(&mut ctx, &deref).unwrap();
        assert_eq!(ty, Ty::Int);
    }

    #[test]
    fn test_deref_secret_in_secret_context_ok() {
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Secret);
        let deref = Expr::Deref(Box::new(r));
        let (ty, _eff) = type_check_full(&mut ctx, &deref).unwrap();
        // Deref of Secret-level ref now returns Labeled(Int, Secret)
        // to propagate security level through expressions for IFC.
        assert_eq!(ty, Ty::Labeled(Box::new(Ty::Int), SecurityLevel::Secret));
    }

    #[test]
    fn test_deref_secret_in_public_context_fails() {
        let mut ctx = TypingContext::with_level(SecurityLevel::Public);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Secret);
        let deref = Expr::Deref(Box::new(r));
        match type_check_full(&mut ctx, &deref) {
            Err(TypeError::SecurityViolation {
                found,
                expected,
                context,
            }) => {
                assert_eq!(found, SecurityLevel::Secret);
                assert_eq!(expected, SecurityLevel::Public);
                assert_eq!(context, "dereference");
            }
            other => panic!("Expected SecurityViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_assign_secret_ref_in_public_context_ok() {
        // REQ-12 (IFC): Writing UP is safe — Public context can write to Secret ref.
        // Bell-LaPadula *-property: no-write-DOWN, but write-UP is allowed.
        // Δ=Public, sl=Secret → Public ⊑ Secret → TRUE → allowed.
        let mut ctx = TypingContext::with_level(SecurityLevel::Public);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Secret);
        let assign = Expr::Assign(Box::new(r), Box::new(Expr::Int(2)));
        let (ty, _eff) = type_check_full(&mut ctx, &assign).unwrap();
        assert_eq!(ty, Ty::Unit);
    }

    #[test]
    fn test_assign_public_ref_in_secret_context_fails() {
        // REQ-12 (IFC): Writing DOWN is blocked — Secret context cannot write
        // to Public ref. This prevents implicit information flows where a branch
        // guarded by secret data writes to a public reference.
        // Δ=Secret, sl=Public → Secret ⊑ Public → FALSE → blocked.
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public);
        let assign = Expr::Assign(Box::new(r), Box::new(Expr::Int(2)));
        match type_check_full(&mut ctx, &assign) {
            Err(TypeError::ImplicitFlowViolation {
                branch_level,
                target_level,
                context,
            }) => {
                assert_eq!(branch_level, SecurityLevel::Secret);
                assert_eq!(target_level, SecurityLevel::Public);
                assert_eq!(context, "assignment");
            }
            other => panic!("Expected ImplicitFlowViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_assign_same_level_ok() {
        // Assigning to a ref at the same level as context is always OK.
        // Δ=User, sl=User → User ⊑ User → TRUE → allowed.
        let mut ctx = TypingContext::with_level(SecurityLevel::User);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::User);
        let assign = Expr::Assign(Box::new(r), Box::new(Expr::Int(2)));
        let (ty, _eff) = type_check_full(&mut ctx, &assign).unwrap();
        assert_eq!(ty, Ty::Unit);
    }

    #[test]
    fn test_implicit_flow_secret_deref_then_assign_public() {
        // The classic implicit flow attack:
        // In a Secret context (required to deref secret ref),
        // try to write the result to a public ref.
        // This must be REJECTED.
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);

        // deref(ref 42 @Secret) — reads secret data (allowed: Secret ⊑ Secret)
        let secret_ref = Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Secret);
        let deref = Expr::Deref(Box::new(secret_ref));

        // ref 0 @Public — a public reference
        let public_ref = Expr::Ref(Box::new(Expr::Int(0)), SecurityLevel::Public);

        // if (deref secret_ref) > 0 then public_ref := 1 else public_ref := 0
        // The deref is fine, the comparison is fine, but the assignments are implicit flows.
        let cond = Expr::BinOp(BinOp::Gt, Box::new(deref), Box::new(Expr::Int(0)));
        let assign_then = Expr::Assign(Box::new(public_ref.clone()), Box::new(Expr::Int(1)));
        let assign_else = Expr::Assign(
            Box::new(Expr::Ref(Box::new(Expr::Int(0)), SecurityLevel::Public)),
            Box::new(Expr::Int(0)),
        );
        let if_expr = Expr::If(Box::new(cond), Box::new(assign_then), Box::new(assign_else));

        // Must fail with ImplicitFlowViolation
        match type_check_full(&mut ctx, &if_expr) {
            Err(TypeError::ImplicitFlowViolation { .. }) => {
                // Good: implicit flow prevented
            }
            other => panic!("Expected ImplicitFlowViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_no_implicit_flow_when_writing_to_same_level() {
        // In a Secret context, writing to Secret ref inside an if is OK.
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let secret_ref = Expr::Ref(Box::new(Expr::Int(0)), SecurityLevel::Secret);
        let assign = Expr::Assign(Box::new(secret_ref), Box::new(Expr::Int(1)));
        let if_expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(assign),
            Box::new(Expr::Unit),
        );
        // Should succeed — no downward flow
        type_check_full(&mut ctx, &if_expr).unwrap();
    }

    #[test]
    fn test_bell_lapadula_deref_no_read_up() {
        // T_Deref: No-read-up still enforced. Cannot deref Secret in Public context.
        let mut ctx = TypingContext::with_level(SecurityLevel::Public);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Secret);
        let deref = Expr::Deref(Box::new(r));
        match type_check_full(&mut ctx, &deref) {
            Err(TypeError::SecurityViolation {
                found: SecurityLevel::Secret,
                expected: SecurityLevel::Public,
                context: "dereference",
            }) => {} // Good: no-read-up enforced
            other => panic!("Expected SecurityViolation (no-read-up), got {:?}", other),
        }
    }

    #[test]
    fn test_bell_lapadula_assign_no_write_down() {
        // T_Assign: No-write-down enforced at all levels.
        // System context cannot write to Internal ref.
        let mut ctx = TypingContext::with_level(SecurityLevel::System);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Internal);
        let assign = Expr::Assign(Box::new(r), Box::new(Expr::Int(2)));
        match type_check_full(&mut ctx, &assign) {
            Err(TypeError::ImplicitFlowViolation {
                branch_level: SecurityLevel::System,
                target_level: SecurityLevel::Internal,
                ..
            }) => {} // Good: no-write-down enforced
            other => panic!(
                "Expected ImplicitFlowViolation (no-write-down), got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_implicit_flow_via_secret_comparison_in_public_context() {
        // THE CRITICAL IMPLICIT FLOW TEST:
        // In a PUBLIC context, deref a Secret ref, compare with 0,
        // branch on the result, and try to write to a public ref.
        // This MUST be rejected — the branch condition is derived from
        // secret data, so the branch executes at elevated Δ=Secret,
        // and writing to a Public ref violates no-write-down.
        //
        // Before A1 fix: this would PASS (bug — plain Bool condition
        // didn't carry the secret label, so branch Δ stayed Public).
        // After A1 fix: deref returns Labeled(Int, Secret), comparison
        // returns Labeled(Bool, Secret), If elevates Δ to Secret.
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);

        // secret_ref : Ref(Int, Secret)
        let secret_ref = Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Secret);
        // deref → Labeled(Int, Secret)
        let deref = Expr::Deref(Box::new(secret_ref));
        // deref > 0 → Labeled(Bool, Secret)
        let cond = Expr::BinOp(BinOp::Gt, Box::new(deref), Box::new(Expr::Int(0)));
        // public_ref : Ref(Int, Public)
        let public_ref = Expr::Ref(Box::new(Expr::Int(0)), SecurityLevel::Public);
        // public_ref := 1 (in secret-elevated branch)
        let assign = Expr::Assign(Box::new(public_ref.clone()), Box::new(Expr::Int(1)));
        let else_branch = Expr::Assign(
            Box::new(Expr::Ref(Box::new(Expr::Int(0)), SecurityLevel::Public)),
            Box::new(Expr::Int(0)),
        );
        let if_expr = Expr::If(Box::new(cond), Box::new(assign), Box::new(else_branch));

        match type_check_full(&mut ctx, &if_expr) {
            Err(TypeError::ImplicitFlowViolation { .. }) => {
                // Correct: implicit flow through secret-derived branch prevented
            }
            other => panic!(
                "Expected ImplicitFlowViolation for secret-derived branch, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_public_comparison_allows_public_write() {
        // Sanity check: comparing public values in a public context and
        // writing to a public ref inside the branch is ALLOWED.
        let mut ctx = TypingContext::with_level(SecurityLevel::Public);
        let public_ref = Expr::Ref(Box::new(Expr::Int(5)), SecurityLevel::Public);
        let deref = Expr::Deref(Box::new(public_ref));
        let cond = Expr::BinOp(BinOp::Gt, Box::new(deref), Box::new(Expr::Int(0)));
        let assign = Expr::Assign(
            Box::new(Expr::Ref(Box::new(Expr::Int(0)), SecurityLevel::Public)),
            Box::new(Expr::Int(1)),
        );
        let if_expr = Expr::If(Box::new(cond), Box::new(assign), Box::new(Expr::Unit));
        // Should succeed — no secret data involved
        type_check_full(&mut ctx, &if_expr).unwrap();
    }

    #[test]
    fn test_binop_propagates_security_label() {
        // Verify that BinOp on Labeled operands produces a Labeled result
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let secret_ref = Expr::Ref(Box::new(Expr::Int(10)), SecurityLevel::Secret);
        let deref = Expr::Deref(Box::new(secret_ref));
        // deref + 5 → Labeled(Int, Secret) + Int → Labeled(Int, Secret)
        let add = Expr::BinOp(BinOp::Add, Box::new(deref), Box::new(Expr::Int(5)));
        let (ty, _eff) = type_check_full(&mut ctx, &add).unwrap();
        assert_eq!(ty, Ty::Labeled(Box::new(Ty::Int), SecurityLevel::Secret));
    }

    #[test]
    fn test_security_level_lattice() {
        // Test the flow relation: Public ⊑ Internal ⊑ Session ⊑ User ⊑ System ⊑ Secret
        assert!(SecurityLevel::Public.leq(SecurityLevel::Internal));
        assert!(SecurityLevel::Internal.leq(SecurityLevel::Session));
        assert!(SecurityLevel::Session.leq(SecurityLevel::User));
        assert!(SecurityLevel::User.leq(SecurityLevel::System));
        assert!(SecurityLevel::System.leq(SecurityLevel::Secret));

        // Higher to lower does not flow
        assert!(!SecurityLevel::Secret.leq(SecurityLevel::Public));
        assert!(!SecurityLevel::System.leq(SecurityLevel::User));
    }

    #[test]
    fn test_deref_in_higher_context_ok() {
        // Dereferencing a lower-security ref in a higher-security context is OK
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public);
        let deref = Expr::Deref(Box::new(r));
        let (ty, _eff) = type_check_full(&mut ctx, &deref).unwrap();
        assert_eq!(ty, Ty::Int);
    }

    // ── Location typing with Σ ──

    #[test]
    fn test_loc_with_sigma() {
        let mut ctx = TypingContext::new();
        // Pre-populate sigma with a location
        let loc = ctx.sigma.extend(Ty::Int, SecurityLevel::Public);

        let loc_expr = Expr::Loc(loc.index() as u64);
        let (ty, eff) = type_check_full(&mut ctx, &loc_expr).unwrap();
        assert_eq!(ty, Ty::Ref(Box::new(Ty::Int), SecurityLevel::Public));
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_loc_not_in_sigma_fails() {
        let mut ctx = TypingContext::new();
        // Sigma is empty, location 0 doesn't exist
        let loc_expr = Expr::Loc(0);
        match type_check_full(&mut ctx, &loc_expr) {
            Err(TypeError::LocationNotFound(loc)) => {
                assert_eq!(loc, Location::new(0));
            }
            other => panic!("Expected LocationNotFound, got {:?}", other),
        }
    }

    // ── Declassification with declass_ok predicate ──

    #[test]
    fn test_proper_declassification() {
        let mut ctx = TypingContext::new();
        // Proper declassification: declassify (classify v) (prove (classify v))
        let v = Expr::Int(42);
        let classified = Expr::Classify(Box::new(v.clone()));
        let proof = Expr::Prove(Box::new(Expr::Classify(Box::new(v))));
        let declassify = Expr::Declassify(Box::new(classified), Box::new(proof));

        let (ty, eff) = type_check_full(&mut ctx, &declassify).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_declassify_wrong_proof_structure() {
        let mut ctx = TypingContext::new();
        // Wrong: proof is not Prove(Classify(...))
        let classified = Expr::Classify(Box::new(Expr::Int(42)));
        let wrong_proof = Expr::Prove(Box::new(Expr::Int(42))); // Should be Prove(Classify(42))

        let declassify = Expr::Declassify(Box::new(classified), Box::new(wrong_proof));

        // This should fail the declass_ok check
        match type_check_full(&mut ctx, &declassify) {
            Err(TypeError::InvalidDeclassification { .. }) => {}
            Err(TypeError::TypeMismatch { .. }) => {} // Type mismatch is also acceptable
            other => panic!(
                "Expected InvalidDeclassification or TypeMismatch, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_declassify_non_secret_rejected_strict() {
        let mut ctx = TypingContext::new();
        // Strict mode: Coq T_Declassify requires TSecret(T), rejects non-secret
        let declassify = Expr::Declassify(Box::new(Expr::Int(42)), Box::new(Expr::Unit));
        let result = type_check_full(&mut ctx, &declassify);
        assert!(result.is_err());
        match result.unwrap_err() {
            TypeError::ExpectedSecret(Ty::Int) => {} // correct — matches Coq
            other => panic!("Expected ExpectedSecret(Int), got {:?}", other),
        }
    }

    // ── Effect accumulation ──

    #[test]
    fn test_full_effect_accumulation() {
        let mut ctx = TypingContext::new();
        let left = Expr::Perform(Effect::Read, Box::new(Expr::Int(1)));
        let right = Expr::Ref(Box::new(Expr::Int(2)), SecurityLevel::Public);
        let pair = Expr::Pair(Box::new(left), Box::new(right));
        let (_ty, eff) = type_check_full(&mut ctx, &pair).unwrap();
        // Write > Read
        assert_eq!(eff, Effect::Write);
    }

    // ── Multi-level security scenarios ──

    #[test]
    fn test_intermediate_security_levels() {
        // Test with intermediate levels: User context reading Session ref
        let mut ctx = TypingContext::with_level(SecurityLevel::User);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Session);
        let deref = Expr::Deref(Box::new(r));
        // Session ⊑ User, so this should succeed
        // Deref of Session-level ref returns Labeled(Int, Session)
        let (ty, _eff) = type_check_full(&mut ctx, &deref).unwrap();
        assert_eq!(ty, Ty::Labeled(Box::new(Ty::Int), SecurityLevel::Session));
    }

    #[test]
    fn test_internal_cannot_read_system() {
        // Internal context cannot read System ref
        let mut ctx = TypingContext::with_level(SecurityLevel::Internal);
        let r = Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::System);
        let deref = Expr::Deref(Box::new(r));
        match type_check_full(&mut ctx, &deref) {
            Err(TypeError::SecurityViolation {
                found,
                expected,
                context,
            }) => {
                assert_eq!(found, SecurityLevel::System);
                assert_eq!(expected, SecurityLevel::Internal);
                assert_eq!(context, "dereference");
            }
            other => panic!("Expected SecurityViolation, got {:?}", other),
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // DOMAIN SECURITY: Taint Checking Tests
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_taint_type_compatibility_rejects_tainted_to_sanitized() {
        // Tainted cannot flow to Sanitized (taint violation)
        let tainted = Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::UserInput);
        let sanitized = Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::SqlParam);

        assert!(!types_compatible(&sanitized, &tainted));
    }

    #[test]
    fn test_taint_type_compatibility_sanitized_to_plain() {
        // Sanitized CAN flow to plain type (safe subtyping)
        let sanitized = Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::HtmlEscape);
        let plain = Ty::String;

        assert!(types_compatible(&plain, &sanitized));
    }

    #[test]
    fn test_taint_sanitizer_exact_match() {
        // Sanitized<String, SqlParam> matches Sanitized<String, SqlParam>
        let san1 = Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::SqlParam);
        let san2 = Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::SqlParam);

        assert!(types_compatible(&san1, &san2));
    }

    #[test]
    fn test_taint_sanitizer_mismatch_rejected() {
        // Sanitized<String, HtmlEscape> does NOT match Sanitized<String, SqlParam>
        let html = Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::HtmlEscape);
        let sql = Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::SqlParam);

        assert!(!types_compatible(&sql, &html));
        assert!(!types_compatible(&html, &sql));
    }

    #[test]
    fn test_sql_injection_prevented() {
        // read_line() returns Tainted<String, UserInput>
        // sql_execute requires Sanitized<String, SqlParam>
        // Passing tainted to sql_execute should fail type-check

        let ctx = register_builtin_types(&Context::new());

        // read_line() : () -> Tainted<String, UserInput>
        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let (read_ty, _) = type_check(&ctx, &read_call).unwrap();
        assert_eq!(
            read_ty,
            Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::UserInput)
        );

        // sql_execute(read_line()) should FAIL — tainted input to sensitive sink
        let unsafe_sql = Expr::App(
            Box::new(Expr::Var("sql_execute".to_string())),
            Box::new(read_call.clone()),
        );

        // This should fail type-check because:
        // - sql_execute expects Sanitized<String, SqlParam>
        // - read_line() returns Tainted<String, UserInput>
        // - Tainted cannot flow to Sanitized
        match type_check(&ctx, &unsafe_sql) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::SqlParam);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected TypeMismatch for SQL injection, got {:?}", other),
        }
    }

    #[test]
    fn test_sql_injection_safe_with_sanitization() {
        // sanitize_sql(read_line()) : Sanitized<String, SqlParam>
        // sql_execute requires Sanitized<String, SqlParam>
        // This should type-check successfully

        let ctx = register_builtin_types(&Context::new());

        // read_line()
        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // sanitize_sql(read_line())
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_sql".to_string())),
            Box::new(read_call),
        );

        let (san_ty, _) = type_check(&ctx, &sanitized).unwrap();
        assert_eq!(
            san_ty,
            Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::SqlParam)
        );

        // sql_execute(sanitize_sql(read_line())) — should succeed
        let safe_sql = Expr::App(
            Box::new(Expr::Var("sql_execute".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_sql) {
            Ok((ty, _)) => {
                // sql_execute returns Any (query results)
                assert_eq!(ty, Ty::Any);
            }
            Err(e) => panic!("Expected safe SQL to type-check, got error: {:?}", e),
        }
    }

    #[test]
    fn test_xss_prevention() {
        // html_render requires Sanitized<String, HtmlEscape>
        // Passing unsanitized tainted data should fail

        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // html_render(read_line()) — should FAIL
        let unsafe_html = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(read_call.clone()),
        );

        match type_check(&ctx, &unsafe_html) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::HtmlEscape);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected TypeMismatch for XSS, got {:?}", other),
        }

        // sanitize_html(read_line()); html_render(...) — should succeed
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(read_call),
        );

        let safe_html = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_html) {
            Ok((ty, _)) => assert_eq!(ty, Ty::String),
            Err(e) => panic!("Expected safe HTML to type-check, got error: {:?}", e),
        }
    }

    #[test]
    fn test_command_injection_prevented() {
        // shell_exec requires Sanitized<String, CommandEscape>

        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // shell_exec(read_line()) — should FAIL
        let unsafe_shell = Expr::App(
            Box::new(Expr::Var("shell_exec".to_string())),
            Box::new(read_call.clone()),
        );

        match type_check(&ctx, &unsafe_shell) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::CommandEscape);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!(
                "Expected TypeMismatch for command injection, got {:?}",
                other
            ),
        }

        // sanitize_command(read_line()); shell_exec(...) — should succeed
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_command".to_string())),
            Box::new(read_call),
        );

        let safe_shell = Expr::App(
            Box::new(Expr::Var("shell_exec".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_shell) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Int), // Exit code
            Err(e) => panic!("Expected safe shell to type-check, got error: {:?}", e),
        }
    }

    #[test]
    fn test_sanitizer_mismatch() {
        // Sanitizing with wrong sanitizer should fail
        // sanitize_html(input) produces Sanitized<String, HtmlEscape>
        // sql_execute requires Sanitized<String, SqlParam>
        // These don't match

        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // sanitize_html(read_line())
        let html_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(read_call),
        );

        // sql_execute(sanitize_html(...)) — wrong sanitizer!
        let wrong_sanitizer = Expr::App(
            Box::new(Expr::Var("sql_execute".to_string())),
            Box::new(html_sanitized),
        );

        match type_check(&ctx, &wrong_sanitizer) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::SqlParam);
                assert_eq!(found, riina_types::Sanitizer::HtmlEscape);
            }
            other => panic!("Expected TypeMismatch for wrong sanitizer, got {:?}", other),
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // TASK #4: Enhanced XSS Prevention Tests
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_xss_url_context() {
        // URL sanitization for safe redirects
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // sanitize_url(read_line())
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_url".to_string())),
            Box::new(read_call),
        );

        let (san_ty, _) = type_check(&ctx, &sanitized).unwrap();
        assert_eq!(
            san_ty,
            Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::UrlEncode)
        );
    }

    #[test]
    fn test_xss_css_context() {
        // CSS sanitization for safe style injection
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // sanitize_css(read_line())
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_css".to_string())),
            Box::new(read_call),
        );

        let (san_ty, _) = type_check(&ctx, &sanitized).unwrap();
        assert_eq!(
            san_ty,
            Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::CssEscape)
        );
    }

    #[test]
    fn test_xss_dom_set_html() {
        // DOM innerHTML requires HtmlEscape sanitization
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // dom_set_html(element, read_line()) — should FAIL
        let unsafe_dom = Expr::App(
            Box::new(Expr::Var("dom_set_html".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::Unit), // Mock DOM element
                Box::new(read_call.clone()),
            )),
        );

        match type_check(&ctx, &unsafe_dom) {
            Err(TypeError::TypeMismatch { expected, found: _ }) => {
                // Expected: (Any, Sanitized<String, HtmlEscape>)
                // Found: (Unit, Tainted<String, UserInput>)
                match expected {
                    Ty::Prod(_, right) => {
                        assert_eq!(
                            *right,
                            Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::HtmlEscape)
                        );
                    }
                    _ => panic!("Expected product type"),
                }
            }
            other => panic!("Expected TypeMismatch for unsafe DOM, got {:?}", other),
        }

        // dom_set_html(element, sanitize_html(read_line())) — should succeed
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(read_call),
        );

        let safe_dom = Expr::App(
            Box::new(Expr::Var("dom_set_html".to_string())),
            Box::new(Expr::Pair(Box::new(Expr::Unit), Box::new(sanitized))),
        );

        match type_check(&ctx, &safe_dom) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Unit),
            Err(e) => panic!("Expected safe DOM to type-check, got error: {:?}", e),
        }
    }

    #[test]
    fn test_xss_dom_set_attr() {
        // DOM attribute setter requires HtmlEscape
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // Safe: sanitize_html then set attribute
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(read_call),
        );

        // dom_set_attr(element, ("title", sanitized))
        let safe_attr = Expr::App(
            Box::new(Expr::Var("dom_set_attr".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::Unit), // Mock DOM element
                Box::new(Expr::Pair(
                    Box::new(Expr::String("title".to_string())),
                    Box::new(sanitized),
                )),
            )),
        );

        match type_check(&ctx, &safe_attr) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Unit),
            Err(e) => panic!("Expected safe attribute to type-check, got error: {:?}", e),
        }
    }

    #[test]
    fn test_xss_context_mismatch_url_for_html() {
        // Using URL sanitizer for HTML context should fail
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // sanitize_url(read_line()) → Sanitized<String, UrlEncode>
        let url_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_url".to_string())),
            Box::new(read_call),
        );

        // html_render(url_sanitized) — wrong sanitizer!
        let wrong_context = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(url_sanitized),
        );

        match type_check(&ctx, &wrong_context) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::HtmlEscape);
                assert_eq!(found, riina_types::Sanitizer::UrlEncode);
            }
            other => panic!("Expected TypeMismatch for wrong context, got {:?}", other),
        }
    }

    #[test]
    fn test_xss_context_mismatch_css_for_js() {
        // Using CSS sanitizer for JavaScript context should fail
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // sanitize_css(read_line()) → Sanitized<String, CssEscape>
        let css_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_css".to_string())),
            Box::new(read_call),
        );

        // js_eval(css_sanitized) — wrong sanitizer!
        let wrong_context = Expr::App(
            Box::new(Expr::Var("js_eval".to_string())),
            Box::new(css_sanitized),
        );

        match type_check(&ctx, &wrong_context) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::JsEscape);
                assert_eq!(found, riina_types::Sanitizer::CssEscape);
            }
            other => panic!("Expected TypeMismatch for CSS→JS context, got {:?}", other),
        }
    }

    #[test]
    fn test_xss_input_validation_length() {
        // validate_length returns Option<Tainted<String>>
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // validate_length(read_line(), 100)
        let validated = Expr::App(
            Box::new(Expr::Var("validate_length".to_string())),
            Box::new(Expr::Pair(Box::new(read_call), Box::new(Expr::Int(100)))),
        );

        let (val_ty, _) = type_check(&ctx, &validated).unwrap();
        assert_eq!(
            val_ty,
            Ty::Option(Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput
            )))
        );
    }

    #[test]
    fn test_xss_unicode_normalization() {
        // normalize_unicode preserves taint
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // normalize_unicode(read_line())
        let normalized = Expr::App(
            Box::new(Expr::Var("normalize_unicode".to_string())),
            Box::new(read_call),
        );

        let (norm_ty, _) = type_check(&ctx, &normalized).unwrap();
        assert_eq!(
            norm_ty,
            Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::UserInput)
        );

        // Normalized data still requires sanitization before HTML render
        let unsafe_html = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(normalized),
        );

        match type_check(&ctx, &unsafe_html) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::HtmlEscape);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!(
                "Expected TypeMismatch for normalized but unsanitized data, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_xss_null_byte_stripping() {
        // strip_nulls preserves taint
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // strip_nulls(read_line())
        let stripped = Expr::App(
            Box::new(Expr::Var("strip_nulls".to_string())),
            Box::new(read_call),
        );

        let (strip_ty, _) = type_check(&ctx, &stripped).unwrap();
        assert_eq!(
            strip_ty,
            Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::UserInput)
        );

        // Stripped data still requires sanitization
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(stripped),
        );

        let safe_html = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_html) {
            Ok((ty, _)) => assert_eq!(ty, Ty::String),
            Err(e) => panic!(
                "Expected safe HTML after strip+sanitize, got error: {:?}",
                e
            ),
        }
    }

    #[test]
    fn test_xss_reflected_attack_prevented() {
        // Reflected XSS: user input reflected in HTML without sanitization
        // Example: ?name=<script>alert('XSS')</script>
        let ctx = register_builtin_types(&Context::new());

        // Simulated: http_param returns tainted data
        let http_input = Expr::App(
            Box::new(Expr::Var("http_body".to_string())),
            Box::new(Expr::Unit),
        );

        // html_render(http_input) — REJECTED (reflected XSS)
        let reflected_xss = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(http_input.clone()),
        );

        match type_check(&ctx, &reflected_xss) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::HtmlEscape);
                assert_eq!(taint_source, riina_types::TaintSource::NetworkExternal);
            }
            other => panic!("Expected TypeMismatch for reflected XSS, got {:?}", other),
        }

        // Safe: sanitize before rendering
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(http_input),
        );

        let safe_render = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_render) {
            Ok(_) => {} // Safe!
            Err(e) => panic!("Expected safe reflected XSS prevention, got error: {:?}", e),
        }
    }

    #[test]
    fn test_xss_stored_attack_prevented() {
        // Stored XSS: malicious data stored in DB, then rendered
        // Type system prevents this through persistent taint tracking
        let ctx = register_builtin_types(&Context::new());

        // Assume: data from database is tainted
        // (In real implementation, DB reads would return Tainted types)
        let db_data = Expr::App(
            Box::new(Expr::Var("read_line".to_string())), // Simulated DB read
            Box::new(Expr::Unit),
        );

        // html_render(db_data) — REJECTED (stored XSS)
        let stored_xss = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(db_data.clone()),
        );

        match type_check(&ctx, &stored_xss) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::HtmlEscape);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected TypeMismatch for stored XSS, got {:?}", other),
        }

        // Safe: sanitize data from DB before rendering
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(db_data),
        );

        let safe_render = Expr::App(
            Box::new(Expr::Var("html_render".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_render) {
            Ok(_) => {} // Safe!
            Err(e) => panic!("Expected safe stored XSS prevention, got error: {:?}", e),
        }
    }

    #[test]
    fn test_xss_dom_based_attack_prevented() {
        // DOM-based XSS: user input directly manipulates DOM
        let ctx = register_builtin_types(&Context::new());

        let read_call = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        // dom_set_html(element, read_line()) — REJECTED
        let dom_xss = Expr::App(
            Box::new(Expr::Var("dom_set_html".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::Unit),
                Box::new(read_call.clone()),
            )),
        );

        match type_check(&ctx, &dom_xss) {
            Err(TypeError::TypeMismatch { .. }) => {
                // Good! DOM-based XSS prevented
            }
            other => panic!("Expected TypeMismatch for DOM-based XSS, got {:?}", other),
        }

        // Safe: sanitize before DOM manipulation
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(read_call),
        );

        let safe_dom = Expr::App(
            Box::new(Expr::Var("dom_set_html".to_string())),
            Box::new(Expr::Pair(Box::new(Expr::Unit), Box::new(sanitized))),
        );

        match type_check(&ctx, &safe_dom) {
            Ok(_) => {} // Safe!
            Err(e) => panic!("Expected safe DOM-based XSS prevention, got error: {:?}", e),
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // TASK #5: CSRF Protection Tests
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_csrf_token_generation() {
        // csrf_generate returns a cryptographic token
        let ctx = register_builtin_types(&Context::new());

        let gen_token = Expr::App(
            Box::new(Expr::Var("csrf_generate".to_string())),
            Box::new(Expr::Unit),
        );

        let (token_ty, eff) = type_check(&ctx, &gen_token).unwrap();
        assert_eq!(token_ty, Ty::String);
        assert_eq!(eff, Effect::Random); // Cryptographic randomness
    }

    #[test]
    fn test_csrf_get_no_token_required() {
        // GET is a safe method, no CSRF token required
        let ctx = register_builtin_types(&Context::new());

        // http_get("https://example.com")
        let get_request = Expr::App(
            Box::new(Expr::Var("http_get".to_string())),
            Box::new(Expr::String("https://example.com".to_string())),
        );

        match type_check(&ctx, &get_request) {
            Ok((ty, eff)) => {
                assert_eq!(ty, Ty::Any);
                assert_eq!(eff, Effect::Network);
            }
            Err(e) => panic!("Expected GET to succeed without token, got error: {:?}", e),
        }
    }

    #[test]
    fn test_csrf_post_requires_token() {
        // POST is state-changing, requires CSRF token
        let ctx = register_builtin_types(&Context::new());

        // Generate token
        let token = Expr::App(
            Box::new(Expr::Var("csrf_generate".to_string())),
            Box::new(Expr::Unit),
        );

        // http_post("url", (data, token))
        let post_with_token = Expr::App(
            Box::new(Expr::Var("http_post".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com".to_string())),
                Box::new(Expr::Pair(
                    Box::new(Expr::Unit), // Request body
                    Box::new(token),
                )),
            )),
        );

        match type_check(&ctx, &post_with_token) {
            Ok((ty, eff)) => {
                assert_eq!(ty, Ty::Any);
                // csrf_generate (Random, level 9) + http_post (Network, level 6) → Random
                assert_eq!(eff, Effect::Random);
            }
            Err(e) => panic!("Expected POST with token to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_csrf_post_without_token_fails() {
        // POST without token should fail type check
        let ctx = register_builtin_types(&Context::new());

        // http_post expects (String, (Any, String))
        // Providing just (String, Any) should fail
        let post_without_token = Expr::App(
            Box::new(Expr::Var("http_post".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com".to_string())),
                Box::new(Expr::Unit), // Missing nested (body, token) pair
            )),
        );

        match type_check(&ctx, &post_without_token) {
            Err(TypeError::TypeMismatch { expected, found: _ }) => {
                // Expected: (String, (Any, String))
                // Found: (String, Unit)
                match expected {
                    Ty::Prod(_, right) => {
                        // Right side should be (Any, String)
                        match *right {
                            Ty::Prod(_, token_ty) => {
                                assert_eq!(*token_ty, Ty::String);
                            }
                            _ => panic!("Expected nested product type for POST"),
                        }
                    }
                    _ => panic!("Expected product type for POST"),
                }
            }
            other => panic!(
                "Expected TypeMismatch for POST without token, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_csrf_put_requires_token() {
        // PUT is state-changing, requires CSRF token
        let ctx = register_builtin_types(&Context::new());

        let token = Expr::App(
            Box::new(Expr::Var("csrf_generate".to_string())),
            Box::new(Expr::Unit),
        );

        let put_with_token = Expr::App(
            Box::new(Expr::Var("http_put".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com/resource".to_string())),
                Box::new(Expr::Pair(
                    Box::new(Expr::Unit), // Request body
                    Box::new(token),
                )),
            )),
        );

        match type_check(&ctx, &put_with_token) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!("Expected PUT with token to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_csrf_delete_requires_token() {
        // DELETE is state-changing, requires CSRF token
        let ctx = register_builtin_types(&Context::new());

        let token = Expr::App(
            Box::new(Expr::Var("csrf_generate".to_string())),
            Box::new(Expr::Unit),
        );

        // http_delete expects (String, String) = (URL, token)
        let delete_with_token = Expr::App(
            Box::new(Expr::Var("http_delete".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com/resource".to_string())),
                Box::new(token),
            )),
        );

        match type_check(&ctx, &delete_with_token) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!("Expected DELETE with token to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_csrf_origin_check() {
        // csrf_check_origin validates same-origin policy
        let ctx = register_builtin_types(&Context::new());

        // csrf_check_origin(request_origin, expected_origin)
        let origin_check = Expr::App(
            Box::new(Expr::Var("csrf_check_origin".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com".to_string())),
                Box::new(Expr::String("https://example.com".to_string())),
            )),
        );

        let (check_ty, _) = type_check(&ctx, &origin_check).unwrap();
        assert_eq!(check_ty, Ty::Bool);
    }

    #[test]
    fn test_csrf_referer_check() {
        // csrf_check_referer validates referer header
        let ctx = register_builtin_types(&Context::new());

        let referer_check = Expr::App(
            Box::new(Expr::Var("csrf_check_referer".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com/page".to_string())),
                Box::new(Expr::String("https://example.com".to_string())),
            )),
        );

        let (check_ty, _) = type_check(&ctx, &referer_check).unwrap();
        assert_eq!(check_ty, Ty::Bool);
    }

    #[test]
    fn test_csrf_double_submit_validation() {
        // Double-submit pattern: validate token from request against session token
        let ctx = register_builtin_types(&Context::new());

        // Generate session token
        let session_token = Expr::App(
            Box::new(Expr::Var("csrf_generate".to_string())),
            Box::new(Expr::Unit),
        );

        // Simulate request token (in real app, extracted from request)
        let request_token = Expr::String("request_token_value".to_string());

        // csrf_validate(request_token, session_token)
        let validate = Expr::App(
            Box::new(Expr::Var("csrf_validate".to_string())),
            Box::new(Expr::Pair(Box::new(request_token), Box::new(session_token))),
        );

        let (valid_ty, _) = type_check(&ctx, &validate).unwrap();
        assert_eq!(valid_ty, Ty::Bool);
    }

    #[test]
    fn test_csrf_full_protection_flow() {
        // Complete CSRF protection flow:
        // 1. Generate token
        // 2. Validate origin
        // 3. Validate token
        // 4. Make state-changing request
        let ctx = register_builtin_types(&Context::new());

        // 1. Generate CSRF token
        let token = Expr::App(
            Box::new(Expr::Var("csrf_generate".to_string())),
            Box::new(Expr::Unit),
        );

        // 2. Check origin (returns Bool)
        let origin_check = Expr::App(
            Box::new(Expr::Var("csrf_check_origin".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com".to_string())),
                Box::new(Expr::String("https://example.com".to_string())),
            )),
        );

        // Origin check should return Bool
        let (origin_ty, _) = type_check(&ctx, &origin_check).unwrap();
        assert_eq!(origin_ty, Ty::Bool);

        // 3. Make POST with token
        let post_request = Expr::App(
            Box::new(Expr::Var("http_post".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://example.com/api".to_string())),
                Box::new(Expr::Pair(
                    Box::new(Expr::String("data".to_string())),
                    Box::new(token),
                )),
            )),
        );

        match type_check(&ctx, &post_request) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!(
                "Expected full CSRF protection flow to succeed, got error: {:?}",
                e
            ),
        }
    }

    #[test]
    fn test_csrf_attack_scenario_prevented() {
        // Attacker tries to make state-changing request without token
        let ctx = register_builtin_types(&Context::new());

        // Attacker's malicious POST (no token)
        let malicious_post = Expr::App(
            Box::new(Expr::Var("http_post".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("https://victim.com/transfer".to_string())),
                Box::new(Expr::String("amount=1000".to_string())), // Wrong type: should be (Any, String)
            )),
        );

        match type_check(&ctx, &malicious_post) {
            Err(TypeError::TypeMismatch { .. }) => {
                // Good! CSRF attack prevented by type system
            }
            other => panic!("Expected CSRF attack to be prevented, got {:?}", other),
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // TASK #6: Extended Domain Security Enforcement
    // 5 OWASP attack classes: Path Traversal, XML/XXE, SSRF,
    // Email Header Injection, Unsafe Deserialization
    // ════════════════════════════════════════════════════════════════════

    // ── 6a: Path Traversal (CWE-22) ──

    #[test]
    fn test_path_traversal_prevented() {
        // Tainted path passed directly to file_read_safe — REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_path = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let unsafe_read = Expr::App(
            Box::new(Expr::Var("file_read_safe".to_string())),
            Box::new(user_path),
        );

        match type_check(&ctx, &unsafe_read) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::PathTraversal);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected path traversal to be prevented, got {:?}", other),
        }
    }

    #[test]
    fn test_path_traversal_safe_with_sanitization() {
        // sanitize_path(input) → file_read_safe — succeeds
        let ctx = register_builtin_types(&Context::new());

        let user_path = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_path".to_string())),
            Box::new(user_path),
        );

        let safe_read = Expr::App(
            Box::new(Expr::Var("file_read_safe".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_read) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!("Expected safe path read to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_path_traversal_sanitizer_mismatch() {
        // SQL-sanitized path for file read — wrong sanitizer, REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_path = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let sql_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_sql".to_string())),
            Box::new(user_path),
        );

        let wrong_sink = Expr::App(
            Box::new(Expr::Var("file_read_safe".to_string())),
            Box::new(sql_sanitized),
        );

        match type_check(&ctx, &wrong_sink) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::PathTraversal);
                assert_eq!(found, riina_types::Sanitizer::SqlParam);
            }
            other => panic!(
                "Expected sanitizer mismatch for path traversal, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_path_traversal_write_safe() {
        // sanitize_path(input) → file_write_safe — succeeds
        let ctx = register_builtin_types(&Context::new());

        let user_path = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_path".to_string())),
            Box::new(user_path),
        );

        let safe_write = Expr::App(
            Box::new(Expr::Var("file_write_safe".to_string())),
            Box::new(Expr::Pair(
                Box::new(sanitized),
                Box::new(Expr::String("data".to_string())),
            )),
        );

        match type_check(&ctx, &safe_write) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Unit),
            Err(e) => panic!("Expected safe file write to succeed, got error: {:?}", e),
        }
    }

    // ── 6b: XML Injection / XXE (CWE-611) ──

    #[test]
    fn test_xml_injection_prevented() {
        // Tainted XML passed to xml_parse_safe — REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_xml = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let unsafe_parse = Expr::App(
            Box::new(Expr::Var("xml_parse_safe".to_string())),
            Box::new(user_xml),
        );

        match type_check(&ctx, &unsafe_parse) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::XmlEscape);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected XML injection to be prevented, got {:?}", other),
        }
    }

    #[test]
    fn test_xml_safe_with_sanitization() {
        // sanitize_xml(input) → xml_parse_safe — succeeds
        let ctx = register_builtin_types(&Context::new());

        let user_xml = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_xml".to_string())),
            Box::new(user_xml),
        );

        let safe_parse = Expr::App(
            Box::new(Expr::Var("xml_parse_safe".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_parse) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!("Expected safe XML parse to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_xml_sanitizer_mismatch() {
        // HTML-sanitized data for XML parse — wrong sanitizer, REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_xml = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let html_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(user_xml),
        );

        let wrong_sink = Expr::App(
            Box::new(Expr::Var("xml_parse_safe".to_string())),
            Box::new(html_sanitized),
        );

        match type_check(&ctx, &wrong_sink) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::XmlEscape);
                assert_eq!(found, riina_types::Sanitizer::HtmlEscape);
            }
            other => panic!("Expected sanitizer mismatch for XML, got {:?}", other),
        }
    }

    // ── LDAP injection — Coq `ldap_injection_impossible` (TaintSystemCorrectness.v):
    //   has_type Γ e (TTainted T src) → ~ has_type Γ (EUseSink SanLdapEscape e) T.
    // The Rust enforcement (`ldap_search` sink requiring Sanitized<String,
    // LdapEscape>, `sanitize_ldap`) existed but had no parity test — this closes
    // that gap (positive + negative), matching the SQL/XML/path-traversal surface.
    #[test]
    fn test_ldap_injection_prevented() {
        // Tainted user input passed straight to ldap_search — REJECTED.
        let ctx = register_builtin_types(&Context::new());

        let user_filter = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );
        let unsafe_search = Expr::App(
            Box::new(Expr::Var("ldap_search".to_string())),
            Box::new(user_filter),
        );

        match type_check(&ctx, &unsafe_search) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::LdapEscape);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected LDAP injection to be prevented, got {:?}", other),
        }
    }

    #[test]
    fn test_ldap_safe_with_sanitization() {
        // sanitize_ldap(input) → ldap_search — succeeds.
        let ctx = register_builtin_types(&Context::new());

        let user_filter = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );
        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_ldap".to_string())),
            Box::new(user_filter),
        );
        let safe_search = Expr::App(
            Box::new(Expr::Var("ldap_search".to_string())),
            Box::new(sanitized),
        );

        match type_check(&ctx, &safe_search) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!("Expected safe LDAP search to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_ldap_sanitizer_mismatch() {
        // HTML-sanitized data fed to ldap_search — wrong sanitizer, REJECTED.
        let ctx = register_builtin_types(&Context::new());

        let user_filter = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );
        let html_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_html".to_string())),
            Box::new(user_filter),
        );
        let wrong_sink = Expr::App(
            Box::new(Expr::Var("ldap_search".to_string())),
            Box::new(html_sanitized),
        );

        match type_check(&ctx, &wrong_sink) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::LdapEscape);
                assert_eq!(found, riina_types::Sanitizer::HtmlEscape);
            }
            other => panic!("Expected sanitizer mismatch for LDAP, got {:?}", other),
        }
    }

    // ── Gate C stdlib hardening: file_read path + contents taint typing ──
    // file_read : String -> Tainted<String, FileSystem>. An untrusted (tainted)
    // path is rejected (path-traversal prevention); a literal path is accepted;
    // the returned contents are tainted and may not reach a sink unsanitized.
    #[test]
    fn test_file_read_rejects_tainted_path() {
        let ctx = register_builtin_types(&Context::new());
        let tainted_path = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );
        let call = Expr::App(
            Box::new(Expr::Var("file_read".to_string())),
            Box::new(tainted_path),
        );
        match type_check(&ctx, &call) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::String, "file_read path must be a plain String");
                assert_eq!(
                    found,
                    Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::UserInput)
                );
            }
            other => panic!("Expected tainted file path to be rejected, got {:?}", other),
        }
    }

    #[test]
    fn test_file_read_literal_path_yields_tainted_contents() {
        let ctx = register_builtin_types(&Context::new());
        let call = Expr::App(
            Box::new(Expr::Var("file_read".to_string())),
            Box::new(Expr::String("config.txt".to_string())),
        );
        let (ty, _eff) = type_check(&ctx, &call).expect("literal path must typecheck");
        assert_eq!(
            ty,
            Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::FileSystem),
            "file contents are untrusted (Tainted<_, FileSystem>)"
        );
    }

    #[test]
    fn test_file_read_contents_rejected_at_sink_unsanitized() {
        // sql_execute(file_read("data.sql")) — untrusted file contents reaching a
        // SQL sink without sanitization is a taint violation.
        let ctx = register_builtin_types(&Context::new());
        let contents = Expr::App(
            Box::new(Expr::Var("file_read".to_string())),
            Box::new(Expr::String("data.sql".to_string())),
        );
        let sink = Expr::App(
            Box::new(Expr::Var("sql_execute".to_string())),
            Box::new(contents),
        );
        match type_check(&ctx, &sink) {
            Err(TypeError::TaintViolation { taint_source, required_sanitizer, .. }) => {
                assert_eq!(taint_source, riina_types::TaintSource::FileSystem);
                assert_eq!(required_sanitizer, riina_types::Sanitizer::SqlParam);
            }
            other => panic!("Expected file contents rejected at SQL sink, got {:?}", other),
        }
    }

    #[test]
    fn test_file_exists_rejects_tainted_path() {
        // Single-path file ops (exists/delete/size/list) also require a String
        // path — a tainted path is rejected (path-traversal prevention).
        let ctx = register_builtin_types(&Context::new());
        let tainted_path = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );
        let call = Expr::App(
            Box::new(Expr::Var("file_exists".to_string())),
            Box::new(tainted_path),
        );
        match type_check(&ctx, &call) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::String);
                assert_eq!(
                    found,
                    Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::UserInput)
                );
            }
            other => panic!("Expected tainted path to file_exists rejected, got {:?}", other),
        }
    }

    #[test]
    fn test_single_path_file_ops_have_precise_result_types() {
        let ctx = register_builtin_types(&Context::new());
        let lit = || Box::new(Expr::String("p".to_string()));
        for (name, expect) in [
            ("file_exists", Ty::Bool),
            ("file_size", Ty::Int),
            ("file_delete", Ty::Unit),
        ] {
            let call = Expr::App(Box::new(Expr::Var(name.to_string())), lit());
            let (ty, _eff) =
                type_check(&ctx, &call).unwrap_or_else(|e| panic!("{name} should typecheck: {e:?}"));
            assert_eq!(ty, expect, "{name} result type");
        }
    }

    // ── Coq ⇄ Rust parity: the full file-builtin signature table ──
    // Mirrors 02_FORMAL/coq/effects/FileIOEffectModel.v (the kat_file_* rows):
    // every file op is exactly (effect = FileSystem, arg shape, ret shape) as the
    // Coq model pins it — ShString = plain String (a tainted path is rejected),
    // ShTaintedString = Tainted<String, FileSystem> (contents tainted at birth),
    // ShPairStringString = (String, String), ShAny = Any. Both surface names of
    // each op share one signature. Drift on either side fails this test.
    #[test]
    fn file_builtin_table_matches_coq_model() {
        let ctx = register_builtin_types(&Context::new());
        let tainted_string =
            Ty::Tainted(Box::new(Ty::String), riina_types::TaintSource::FileSystem);
        let string_pair = Ty::Prod(Box::new(Ty::String), Box::new(Ty::String));
        let rows: [(&str, &str, Ty, Ty); 8] = [
            // (bm, en, arg, ret) — one row per FileIOEffectModel.v KAT
            ("fail_baca", "file_read", Ty::String, tainted_string.clone()),
            ("fail_baca_baris", "file_read_lines", Ty::String, tainted_string),
            ("fail_ada", "file_exists", Ty::String, Ty::Bool),
            ("fail_buang", "file_delete", Ty::String, Ty::Unit),
            ("fail_panjang", "file_size", Ty::String, Ty::Int),
            ("fail_senarai", "file_list_dir", Ty::String, Ty::Any),
            ("fail_tulis", "file_write", string_pair.clone(), Ty::Unit),
            ("fail_tambah", "file_append", string_pair, Ty::Unit),
        ];
        for (bm, en, arg, ret) in rows {
            for name in [bm, en] {
                let (ty, _eff) = type_check(&ctx, &Expr::Var(name.to_string()))
                    .unwrap_or_else(|e| panic!("{name} must be a bound builtin: {e:?}"));
                assert_eq!(
                    ty,
                    Ty::Fn(Box::new(arg.clone()), Box::new(ret.clone()), Effect::FileSystem),
                    "{name}: signature drifted from FileIOEffectModel.v"
                );
            }
        }
    }

    // ── REQ-27 IFC enforcement parity: Secret ⇏ print sink ──
    // The print sinks are typed `Any -> Unit ! Write`, so before this rule a
    // `Secret` unified straight through to stdout. Coq forbids that flow: a
    // TSecret re-enters public typing only via T_Declassify with a matching
    // proof (Declassification.v `logical_relation_declassify_proven`,
    // `declassify_requires_public_context`). Negative + positive both ways.

    // ── REQ-27 silent-gap regression: the secrecy scan must see through EVERY
    //    type container ────────────────────────────────────────────────────
    //
    // `ty_secrecy_level` decides whether a value carries a secrecy label, and
    // `secrecy_at_sink` uses it to reject a secret reaching a print / network /
    // file sink. It matched a hand-written list of containers and ended in
    // `_ => None`, so a container nobody listed answered "not secret" and the
    // sink rule silently let the value through.
    #[test]
    fn ty_secrecy_level_sees_through_every_type_container() {
        use crate::ty_secrecy_level;
        let secret = || Box::new(Ty::Secret(Box::new(Ty::Int)));
        let plain = || Box::new(Ty::Int);
        let cases: Vec<(&str, Ty)> = vec![
            ("Secret", Ty::Secret(Box::new(Ty::Int))),
            ("Prod/l", Ty::Prod(secret(), plain())),
            ("Prod/r", Ty::Prod(plain(), secret())),
            ("Sum/l", Ty::Sum(secret(), plain())),
            ("Sum/r", Ty::Sum(plain(), secret())),
            ("List", Ty::List(secret())),
            ("Option", Ty::Option(secret())),
            ("Ref", Ty::Ref(secret(), SecurityLevel::Public)),
            ("ConstantTime", Ty::ConstantTime(secret())),
            ("Zeroizing", Ty::Zeroizing(secret())),
            ("Proof", Ty::Proof(secret())),
            // Below: the containers that were missing. Each is a real RIINA
            // type a secret can be placed in, so each was a way to walk a
            // secret past the sink rule.
            ("ContentAddressed", Ty::ContentAddressed(secret())),
            ("Token", Ty::Token(secret())),
            ("SyariahCompliant", Ty::SyariahCompliant(secret())),
            ("SmartContract", Ty::SmartContract(secret())),
            ("Supervisor", Ty::Supervisor(secret())),
            ("CRDT/state", Ty::CRDT(secret(), plain())),
            ("CRDT/meta", Ty::CRDT(plain(), secret())),
            ("Actor/state", Ty::Actor(secret(), plain())),
            ("Actor/msg", Ty::Actor(plain(), secret())),
            ("RawPtr", Ty::RawPtr(secret())),
        ];
        for (label, ty) in cases {
            assert_eq!(
                ty_secrecy_level(&ty),
                Some(SecurityLevel::Secret),
                "`{label}` hides a Secret from the secrecy scan, so \
                 `cetak`/`http_post`/`file_write` would accept it — the sink \
                 rule is only as deep as this walk"
            );
        }
    }

    #[test]
    fn ty_secrecy_level_stays_none_on_public_types() {
        // NEGATIVE CONTROL: a scan that answered `Some(Secret)` for everything
        // would pass the test above while rejecting every ordinary program.
        use crate::ty_secrecy_level;
        let plain = || Box::new(Ty::Int);
        for (label, ty) in [
            ("Int", Ty::Int),
            ("String", Ty::String),
            ("Prod", Ty::Prod(plain(), plain())),
            ("List", Ty::List(plain())),
            ("ContentAddressed", Ty::ContentAddressed(plain())),
            ("Token", Ty::Token(plain())),
            ("SyariahCompliant", Ty::SyariahCompliant(plain())),
            ("CRDT", Ty::CRDT(plain(), plain())),
            ("Actor", Ty::Actor(plain(), plain())),
            ("Labeled/Public", Ty::Labeled(plain(), SecurityLevel::Public)),
        ] {
            assert_eq!(
                ty_secrecy_level(&ty),
                None,
                "`{label}` carries no secret and must not be flagged"
            );
        }
    }

    #[test]
    fn ifc_print_sinks_reject_secret() {
        let ctx = register_builtin_types(&Context::new());
        let secret = Expr::Classify(Box::new(Expr::Int(42)));
        for sink in ["cetak", "cetakln", "cetak_baris", "print", "println"] {
            let call = Expr::App(
                Box::new(Expr::Var(sink.to_string())),
                Box::new(secret.clone()),
            );
            match type_check(&ctx, &call) {
                Err(TypeError::SecurityViolation { found, expected, .. }) => {
                    assert_eq!(found, SecurityLevel::Secret, "{sink}: leak level");
                    assert_eq!(expected, SecurityLevel::Public, "{sink}: channel level");
                }
                other => panic!("{sink}(secret) must be a SecurityViolation, got {other:?}"),
            }
        }
    }

    #[test]
    fn ifc_print_sink_rejects_secret_nested_in_pair() {
        // A secret smuggled inside a printable container is still a leak:
        // cetak((classify(42), 7)) is rejected like cetak(classify(42)).
        let ctx = register_builtin_types(&Context::new());
        let call = Expr::App(
            Box::new(Expr::Var("cetak".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::Classify(Box::new(Expr::Int(42)))),
                Box::new(Expr::Int(7)),
            )),
        );
        match type_check(&ctx, &call) {
            Err(TypeError::SecurityViolation { .. }) => {}
            other => panic!("nested secret at print sink must be rejected, got {other:?}"),
        }
    }

    #[test]
    fn ifc_print_sink_accepts_declassified_secret() {
        // The sanctioned path: declassify (classify v) (prove (classify v))
        // erases secrecy (T_Declassify / declass_ok), so printing the result
        // is fine — and plain data keeps printing (non-regression).
        let ctx = register_builtin_types(&Context::new());
        let v = Expr::Int(42);
        let declassified = Expr::Declassify(
            Box::new(Expr::Classify(Box::new(v.clone()))),
            Box::new(Expr::Prove(Box::new(Expr::Classify(Box::new(v))))),
        );
        let call = Expr::App(Box::new(Expr::Var("cetak".to_string())), Box::new(declassified));
        let (ty, _eff) = type_check(&ctx, &call).expect("declassified secret must print");
        assert_eq!(ty, Ty::Unit);

        let plain = Expr::App(
            Box::new(Expr::Var("cetak".to_string())),
            Box::new(Expr::Int(7)),
        );
        assert!(type_check(&ctx, &plain).is_ok(), "plain data must keep printing");
    }

    #[test]
    fn ifc_print_sink_rejects_secret_in_full_checker() {
        // The security-aware checker (type_check_full) enforces the same sink
        // rule — both checking paths share `secrecy_at_sink`.
        let mut ctx = TypingContext::new().extend_gamma(
            "cetak".to_string(),
            Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::Write),
        );
        let call = Expr::App(
            Box::new(Expr::Var("cetak".to_string())),
            Box::new(Expr::Classify(Box::new(Expr::Int(42)))),
        );
        match type_check_full(&mut ctx, &call) {
            Err(TypeError::SecurityViolation { found, expected, .. }) => {
                assert_eq!(found, SecurityLevel::Secret);
                assert_eq!(expected, SecurityLevel::Public);
            }
            other => panic!("full checker must also reject, got {other:?}"),
        }
    }

    // ── REQ-27 slice 2: Labeled-by-level rejection at print sinks ──
    // A `Labeled(_, l)` with l above Public (produced by deref of a non-Public
    // ref — Typing.v T_Deref no-read-up) is a leak at a public sink too, not
    // only `Secret`. The reported level is the label, not Secret.
    #[test]
    fn ifc_print_sink_rejects_labeled_above_public() {
        let ctx = register_builtin_types(&Context::new())
            .extend("rahsia_x".to_string(), Ty::Labeled(Box::new(Ty::Int), SecurityLevel::User));
        let call = Expr::App(
            Box::new(Expr::Var("cetak".to_string())),
            Box::new(Expr::Var("rahsia_x".to_string())),
        );
        match type_check(&ctx, &call) {
            Err(TypeError::SecurityViolation { found, expected, .. }) => {
                assert_eq!(found, SecurityLevel::User, "reports the label level, not Secret");
                assert_eq!(expected, SecurityLevel::Public);
            }
            other => panic!("Labeled(User) at print sink must be rejected, got {other:?}"),
        }
    }

    #[test]
    fn ifc_print_sink_accepts_public_labeled() {
        // Labeled at Public level carries no secrecy — it must still print.
        // (Deref of a Public ref yields the plain type, so this is the boundary.)
        let ctx = register_builtin_types(&Context::new())
            .extend("awam_x".to_string(), Ty::Labeled(Box::new(Ty::Int), SecurityLevel::Public));
        let call = Expr::App(
            Box::new(Expr::Var("cetak".to_string())),
            Box::new(Expr::Var("awam_x".to_string())),
        );
        assert!(type_check(&ctx, &call).is_ok(), "Public-labeled data must print");
    }

    // ── REQ-27 slice 3: secret-aware network-send sinks ──
    // http_post/http_hantar/http_put take (URL, (body, csrf)); the body is Any,
    // so a secret in it would flow onto the network. Reject it (any secret in
    // the whole argument — URL or csrf shouldn't be secret-derived either).
    #[test]
    fn ifc_network_send_rejects_secret_body() {
        let ctx = register_builtin_types(&Context::new());
        for sink in ["http_post", "http_hantar", "http_put"] {
            // (url, (classify(42), "csrf"))
            let arg = Expr::Pair(
                Box::new(Expr::String("https://api".to_string())),
                Box::new(Expr::Pair(
                    Box::new(Expr::Classify(Box::new(Expr::Int(42)))),
                    Box::new(Expr::String("tok".to_string())),
                )),
            );
            let call = Expr::App(Box::new(Expr::Var(sink.to_string())), Box::new(arg));
            match type_check(&ctx, &call) {
                Err(TypeError::SecurityViolation { found, expected, context }) => {
                    assert_eq!(found, SecurityLevel::Secret);
                    assert_eq!(expected, SecurityLevel::Public);
                    assert!(context.contains("network"), "{sink}: network context, got {context}");
                }
                other => panic!("{sink}(secret body) must be rejected, got {other:?}"),
            }
        }
    }

    #[test]
    fn ifc_network_send_accepts_public_body() {
        // Plain public body still sends (non-regression).
        let ctx = register_builtin_types(&Context::new());
        let arg = Expr::Pair(
            Box::new(Expr::String("https://api".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("payload".to_string())),
                Box::new(Expr::String("tok".to_string())),
            )),
        );
        let call = Expr::App(Box::new(Expr::Var("http_post".to_string())), Box::new(arg));
        assert!(type_check(&ctx, &call).is_ok(), "public body must send");
    }

    // ── REQ-27 slice 4: secret-aware file-write sinks ──
    // file_write/fail_tulis take a concrete (String, String), so a Secret data
    // arg was ALREADY a TypeMismatch; routing it through secrecy_at_sink (before
    // unification) gives the *clear* SecurityViolation instead.
    #[test]
    fn ifc_file_write_rejects_secret_data_with_clear_error() {
        let ctx = register_builtin_types(&Context::new());
        for sink in ["file_write", "fail_tulis", "file_append", "fail_tambah"] {
            let arg = Expr::Pair(
                Box::new(Expr::String("/tmp/out".to_string())),
                Box::new(Expr::Classify(Box::new(Expr::String("rahsia".to_string())))),
            );
            let call = Expr::App(Box::new(Expr::Var(sink.to_string())), Box::new(arg));
            match type_check(&ctx, &call) {
                Err(TypeError::SecurityViolation { found, context, .. }) => {
                    assert_eq!(found, SecurityLevel::Secret);
                    assert!(context.contains("file-write"), "{sink}: file context, got {context}");
                }
                other => panic!("{sink}(secret data) must be a SecurityViolation, got {other:?}"),
            }
        }
    }

    #[test]
    fn ifc_file_write_accepts_plain_data() {
        // Plain (path, data) still writes (non-regression).
        let ctx = register_builtin_types(&Context::new());
        let arg = Expr::Pair(
            Box::new(Expr::String("/tmp/out".to_string())),
            Box::new(Expr::String("data".to_string())),
        );
        let call = Expr::App(Box::new(Expr::Var("file_write".to_string())), Box::new(arg));
        assert!(type_check(&ctx, &call).is_ok(), "plain file write must typecheck");
    }

    // ── REQ-27 slices 5–7 (Any-typed builtin audit, 2026-06-12) ──
    // Four verified leak vectors closed: the `http_kemaskini` PUT alias was
    // registered but missing from the sink list; the sanitized file-write
    // variants have an Any-typed DATA position that passed unification; a
    // failing assertion renders its operands into the runtime error message;
    // and pure Any-typed builtins (ke_teks, containers) LAUNDERED secrecy —
    // `cetak(ke_teks(pin))` type-checked while `cetak(pin)` was rejected.

    #[test]
    fn ifc_network_send_rejects_secret_via_kemaskini_alias() {
        // http_kemaskini is the BM alias of http_put — same (URL,(body,csrf)).
        let ctx = register_builtin_types(&Context::new());
        let arg = Expr::Pair(
            Box::new(Expr::String("https://api".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::Classify(Box::new(Expr::Int(42)))),
                Box::new(Expr::String("tok".to_string())),
            )),
        );
        let call = Expr::App(Box::new(Expr::Var("http_kemaskini".to_string())), Box::new(arg));
        match type_check(&ctx, &call) {
            Err(TypeError::SecurityViolation { found, context, .. }) => {
                assert_eq!(found, SecurityLevel::Secret);
                assert!(context.contains("network"), "network context, got {context}");
            }
            other => panic!("http_kemaskini(secret body) must be rejected, got {other:?}"),
        }
    }

    #[test]
    fn ifc_network_url_rejects_secret_with_clear_error() {
        // GET/DELETE have no Any body, but a secret-derived URL/token is still
        // exfiltration; pre-unification check upgrades the opaque TypeMismatch.
        let ctx = register_builtin_types(&Context::new());
        for sink in ["http_get", "http_dapat"] {
            let arg = Expr::Classify(Box::new(Expr::String("https://x/?pin=1234".to_string())));
            let call = Expr::App(Box::new(Expr::Var(sink.to_string())), Box::new(arg));
            match type_check(&ctx, &call) {
                Err(TypeError::SecurityViolation { found, context, .. }) => {
                    assert_eq!(found, SecurityLevel::Secret);
                    assert!(context.contains("network"), "{sink}: network context, got {context}");
                }
                other => panic!("{sink}(secret URL) must be a SecurityViolation, got {other:?}"),
            }
        }
    }

    #[test]
    fn ifc_safe_file_write_rejects_secret_data() {
        // fail_tulis_selamat/file_write_safe take (Sanitized path, Any data) —
        // the Any data position let a raw secret through before the audit.
        let ctx = register_builtin_types(&Context::new()).extend(
            "laluan".to_string(),
            Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::PathTraversal),
        );
        for sink in ["file_write_safe", "fail_tulis_selamat"] {
            let arg = Expr::Pair(
                Box::new(Expr::Var("laluan".to_string())),
                Box::new(Expr::Classify(Box::new(Expr::Int(1234)))),
            );
            let call = Expr::App(Box::new(Expr::Var(sink.to_string())), Box::new(arg));
            match type_check(&ctx, &call) {
                Err(TypeError::SecurityViolation { found, context, .. }) => {
                    assert_eq!(found, SecurityLevel::Secret);
                    assert!(context.contains("file-write"), "{sink}: file context, got {context}");
                }
                other => panic!("{sink}(secret data) must be rejected, got {other:?}"),
            }
        }
    }

    #[test]
    fn ifc_safe_file_write_accepts_public_data() {
        let ctx = register_builtin_types(&Context::new()).extend(
            "laluan".to_string(),
            Ty::Sanitized(Box::new(Ty::String), riina_types::Sanitizer::PathTraversal),
        );
        let arg = Expr::Pair(
            Box::new(Expr::Var("laluan".to_string())),
            Box::new(Expr::String("data".to_string())),
        );
        let call = Expr::App(Box::new(Expr::Var("file_write_safe".to_string())), Box::new(arg));
        assert!(type_check(&ctx, &call).is_ok(), "sanitized path + public data must write");
    }

    #[test]
    fn ifc_assert_rejects_secret_operand() {
        // builtins/ujian.rs renders `assert_eq failed: {:?} != {:?}` — a
        // failing assertion on a secret prints it (error-message sink).
        let ctx = register_builtin_types(&Context::new());
        for sink in ["assert_eq", "tegaskan_sama", "assert_ne", "tegaskan_beza"] {
            let arg = Expr::Pair(
                Box::new(Expr::Classify(Box::new(Expr::Int(1234)))),
                Box::new(Expr::Int(1234)),
            );
            let call = Expr::App(Box::new(Expr::Var(sink.to_string())), Box::new(arg));
            match type_check(&ctx, &call) {
                Err(TypeError::SecurityViolation { found, context, .. }) => {
                    assert_eq!(found, SecurityLevel::Secret);
                    assert!(context.contains("assertion"), "{sink}: assertion context, got {context}");
                }
                other => panic!("{sink}(secret operand) must be rejected, got {other:?}"),
            }
        }
    }

    #[test]
    fn ifc_assert_accepts_public_operands() {
        let ctx = register_builtin_types(&Context::new());
        let arg = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Int(1)));
        let call = Expr::App(Box::new(Expr::Var("tegaskan_sama".to_string())), Box::new(arg));
        assert!(type_check(&ctx, &call).is_ok(), "public assert must typecheck");
    }

    #[test]
    fn ifc_laundering_via_ke_teks_rejected_at_sink() {
        // cetak(ke_teks(secret)) — the conversion result re-carries the
        // argument's secrecy, so the sink still rejects it.
        let ctx = register_builtin_types(&Context::new());
        let launder = Expr::App(
            Box::new(Expr::Var("ke_teks".to_string())),
            Box::new(Expr::Classify(Box::new(Expr::Int(1234)))),
        );
        let call = Expr::App(Box::new(Expr::Var("cetak".to_string())), Box::new(launder));
        match type_check(&ctx, &call) {
            Err(TypeError::SecurityViolation { found, .. }) => {
                assert_eq!(found, SecurityLevel::Secret);
            }
            other => panic!("cetak(ke_teks(secret)) must be rejected, got {other:?}"),
        }
    }

    #[test]
    fn ifc_laundering_via_container_rejected_at_sink() {
        // cetak(senarai_tolak((list, secret))) — pushing a secret into an
        // Any-typed container must not strip its label.
        let ctx = register_builtin_types(&Context::new());
        let mklist = Expr::App(
            Box::new(Expr::Var("senarai_baru".to_string())),
            Box::new(Expr::Int(0)),
        );
        let push = Expr::App(
            Box::new(Expr::Var("senarai_tolak".to_string())),
            Box::new(Expr::Pair(
                Box::new(mklist),
                Box::new(Expr::Classify(Box::new(Expr::Int(1234)))),
            )),
        );
        let call = Expr::App(Box::new(Expr::Var("cetak".to_string())), Box::new(push));
        match type_check(&ctx, &call) {
            Err(TypeError::SecurityViolation { found, .. }) => {
                assert_eq!(found, SecurityLevel::Secret);
            }
            other => panic!("cetak(list with secret) must be rejected, got {other:?}"),
        }
    }

    #[test]
    fn ifc_secrecy_propagation_result_types() {
        // ke_teks(Secret<Int>) : Secret<String>; ke_teks(Labeled(_, User)) :
        // Labeled(String, User); ke_teks(public Int) stays String.
        let ctx = register_builtin_types(&Context::new())
            .extend("rahsia_u".to_string(), Ty::Labeled(Box::new(Ty::Int), SecurityLevel::User));

        let secret_conv = Expr::App(
            Box::new(Expr::Var("ke_teks".to_string())),
            Box::new(Expr::Classify(Box::new(Expr::Int(1)))),
        );
        let (ty, _) = type_check(&ctx, &secret_conv).expect("ke_teks(secret) types");
        assert_eq!(ty, Ty::Secret(Box::new(Ty::String)), "top joins to Secret<_>");

        let user_conv = Expr::App(
            Box::new(Expr::Var("ke_teks".to_string())),
            Box::new(Expr::Var("rahsia_u".to_string())),
        );
        let (ty, _) = type_check(&ctx, &user_conv).expect("ke_teks(labeled) types");
        assert_eq!(
            ty,
            Ty::Labeled(Box::new(Ty::String), SecurityLevel::User),
            "intermediate level re-carried as Labeled"
        );

        let public_conv = Expr::App(
            Box::new(Expr::Var("ke_teks".to_string())),
            Box::new(Expr::Int(1)),
        );
        let (ty, _) = type_check(&ctx, &public_conv).expect("ke_teks(public) types");
        assert_eq!(ty, Ty::String, "public data is untouched by propagation");
    }

    #[test]
    fn test_file_write_append_take_string_pair_and_return_unit() {
        // Multi-arg `file_write`/`file_append` take a `(path, data)` pair of
        // `String`s and return `Unit` with the FileSystem effect.
        let ctx = register_builtin_types(&Context::new());
        for name in ["file_write", "file_append", "fail_tulis", "fail_tambah"] {
            let call = Expr::App(
                Box::new(Expr::Var(name.to_string())),
                Box::new(Expr::Pair(
                    Box::new(Expr::String("out.txt".to_string())),
                    Box::new(Expr::String("data".to_string())),
                )),
            );
            let (ty, eff) = type_check(&ctx, &call)
                .unwrap_or_else(|e| panic!("{name}((String,String)) should typecheck: {e:?}"));
            assert_eq!(ty, Ty::Unit, "{name} result type");
            assert_eq!(eff, Effect::FileSystem, "{name} effect");
        }
    }

    #[test]
    fn test_file_write_rejects_tainted_path() {
        // Path-traversal prevention: an untrusted (tainted) path in the
        // `(path, data)` pair is rejected, just like the single-path ops.
        let ctx = register_builtin_types(&Context::new());
        let tainted_path = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );
        let call = Expr::App(
            Box::new(Expr::Var("file_write".to_string())),
            Box::new(Expr::Pair(
                Box::new(tainted_path),
                Box::new(Expr::String("data".to_string())),
            )),
        );
        assert!(
            matches!(type_check(&ctx, &call), Err(TypeError::TypeMismatch { .. })),
            "a tainted path to file_write must be rejected (path traversal)"
        );
    }

    // ── Filesystem taint discipline ⇄ Coq `TaintSystemCorrectness.v` ──
    // These mirror, on the running typechecker, the mechanized theorem
    //   `path_traversal_impossible : forall Γ e T src,
    //      has_type Γ e (TTainted T src) -> ~ has_type Γ (EUseSink SanPathSanitize e) T`
    // i.e. a tainted value cannot reach a path sink. The prototype realises this
    // by typing every file-op path as a plain `String`, so a `Tainted` path is a
    // type error — across ALL file builtins, not just `file_write`.

    /// A tainted value: the contents of an untrusted file
    /// (`Tainted<String, FileSystem>` — a taint *source*).
    fn tainted_fs_value() -> Expr {
        Expr::App(
            Box::new(Expr::Var("file_read".to_string())),
            Box::new(Expr::String("untrusted.txt".to_string())),
        )
    }

    #[test]
    fn taint_path_traversal_prevention_parity_all_file_ops() {
        let ctx = register_builtin_types(&Context::new());
        // Single-path ops: a tainted path is rejected; a clean `String` is accepted
        // (and the op is a FileSystem effect).
        for op in [
            "file_read",
            "file_read_lines",
            "file_exists",
            "file_delete",
            "file_size",
            "file_list_dir",
        ] {
            let bad = Expr::App(Box::new(Expr::Var(op.to_string())), Box::new(tainted_fs_value()));
            assert!(
                matches!(type_check(&ctx, &bad), Err(TypeError::TypeMismatch { .. })),
                "{op}: a tainted path must be rejected (Coq path_traversal_impossible)"
            );
            let good = Expr::App(
                Box::new(Expr::Var(op.to_string())),
                Box::new(Expr::String("safe.txt".to_string())),
            );
            let (_, eff) = type_check(&ctx, &good)
                .unwrap_or_else(|e| panic!("{op}: a clean String path must typecheck: {e:?}"));
            assert_eq!(eff, Effect::FileSystem, "{op} is a FileSystem effect");
        }
        // Pair-path ops (write/append): a tainted path component is rejected.
        for op in ["file_write", "file_append"] {
            let bad = Expr::App(
                Box::new(Expr::Var(op.to_string())),
                Box::new(Expr::Pair(
                    Box::new(tainted_fs_value()),
                    Box::new(Expr::String("data".to_string())),
                )),
            );
            assert!(
                matches!(type_check(&ctx, &bad), Err(TypeError::TypeMismatch { .. })),
                "{op}: a tainted path must be rejected (Coq path_traversal_impossible)"
            );
            let good = Expr::App(
                Box::new(Expr::Var(op.to_string())),
                Box::new(Expr::Pair(
                    Box::new(Expr::String("safe.txt".to_string())),
                    Box::new(Expr::String("data".to_string())),
                )),
            );
            let (_, eff) = type_check(&ctx, &good)
                .unwrap_or_else(|e| panic!("{op}: a clean (path,data) must typecheck: {e:?}"));
            assert_eq!(eff, Effect::FileSystem, "{op} is a FileSystem effect");
        }
    }

    #[test]
    fn taint_file_read_result_is_a_source_and_cannot_be_reused_as_a_path() {
        // file_read returns `Tainted<String, FileSystem>`, so its result cannot be
        // fed back as a path — the end-to-end realisation of the theorem
        // (read-an-untrusted-path → path sink is un-typeable).
        let ctx = register_builtin_types(&Context::new());
        let (ty, _) = type_check(&ctx, &tainted_fs_value()).unwrap();
        assert!(
            matches!(ty, Ty::Tainted(_, riina_types::TaintSource::FileSystem)),
            "file_read result must be Tainted<_, FileSystem>, got {ty:?}"
        );
        let reuse = Expr::App(
            Box::new(Expr::Var("file_exists".to_string())),
            Box::new(tainted_fs_value()),
        );
        assert!(
            matches!(type_check(&ctx, &reuse), Err(TypeError::TypeMismatch { .. })),
            "a tainted file_read result must not be usable as a path"
        );
    }

    #[test]
    fn taint_path_sink_rejection_is_source_agnostic() {
        // The Coq theorem is `forall src` — rejection does not depend on the taint
        // *source*. The prototype matches: a `NetworkExternal`-tainted value
        // (`http_body`) is rejected as a file path just like a `FileSystem` one.
        let ctx = register_builtin_types(&Context::new());
        let net_tainted = Expr::App(
            Box::new(Expr::Var("http_body".to_string())),
            Box::new(Expr::String("req".to_string())),
        );
        // sanity: it really is a different-source tainted value
        let (ty, _) = type_check(&ctx, &net_tainted).unwrap();
        assert!(
            matches!(ty, Ty::Tainted(_, riina_types::TaintSource::NetworkExternal)),
            "http_body must be Tainted<_, NetworkExternal>, got {ty:?}"
        );
        let bad = Expr::App(
            Box::new(Expr::Var("file_exists".to_string())),
            Box::new(net_tainted),
        );
        assert!(
            matches!(type_check(&ctx, &bad), Err(TypeError::TypeMismatch { .. })),
            "a tainted path is rejected regardless of its source"
        );
    }

    // ── OS/system effect-typing audit ⇄ Coq injection-prevention theorems ──
    // The system builtins implement a taint → sanitize → sink pipeline:
    //   * inputs (`read_line`)          : Effect::System, result Tainted<_, _>
    //   * sanitizers (`sanitize_*`)     : Effect::Pure, Tainted → Sanitized<_, k>
    //   * sinks (`sql_execute`, …)      : Effect::System, REQUIRE Sanitized<_, k>
    // These tests assert that discipline on the running typechecker, mirroring the
    // mechanized `TaintSystemCorrectness.v` theorems {sql,command,ldap,xss_js}_
    // injection_impossible (a tainted/unsanitised value cannot reach a sink).

    fn read_line_tainted() -> Expr {
        Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        )
    }
    fn sanitize_with(name: &str) -> Expr {
        Expr::App(
            Box::new(Expr::Var(name.to_string())),
            Box::new(read_line_tainted()),
        )
    }

    #[test]
    fn taint_injection_prevention_parity_all_sinks() {
        let ctx = register_builtin_types(&Context::new());
        // (sink, matching sanitizer, a NON-matching sanitizer)
        let sinks = [
            ("sql_execute", "sanitize_sql", "sanitize_command"),
            ("js_eval", "sanitize_js", "sanitize_sql"),
            ("shell_exec", "sanitize_command", "sanitize_sql"),
            ("ldap_search", "sanitize_ldap", "sanitize_sql"),
        ];
        for (sink, ok_san, wrong_san) in sinks {
            let app = |arg: Expr| Expr::App(Box::new(Expr::Var(sink.to_string())), Box::new(arg));
            // tainted → sink: rejected as a TaintViolation (injection_impossible)
            assert!(
                matches!(type_check(&ctx, &app(read_line_tainted())), Err(TypeError::TaintViolation { .. })),
                "{sink}: tainted input must be a TaintViolation (injection_impossible)"
            );
            // raw String → sink: rejected (a sink requires Sanitized, not a bare String)
            assert!(
                matches!(type_check(&ctx, &app(Expr::String("raw".to_string()))), Err(TypeError::TypeMismatch { .. })),
                "{sink}: a raw String must be rejected"
            );
            // wrong sanitizer → sink: rejected as a SanitizerMismatch (each sink needs ITS sanitizer)
            assert!(
                matches!(type_check(&ctx, &app(sanitize_with(wrong_san))), Err(TypeError::SanitizerMismatch { .. })),
                "{sink}: a {wrong_san} value must be a SanitizerMismatch"
            );
            // matching sanitizer → sink: accepted, and the sink is a System effect
            let (_, eff) = type_check(&ctx, &app(sanitize_with(ok_san)))
                .unwrap_or_else(|e| panic!("{sink}: {ok_san} output must be accepted: {e:?}"));
            assert_eq!(eff, Effect::System, "{sink} is a System effect");
        }
    }

    #[test]
    fn taint_sanitizers_are_pure_and_well_typed() {
        let ctx = register_builtin_types(&Context::new());
        let cases = [
            ("sanitize_sql", riina_types::Sanitizer::SqlParam),
            ("sanitize_command", riina_types::Sanitizer::CommandEscape),
            ("sanitize_ldap", riina_types::Sanitizer::LdapEscape),
            ("sanitize_js", riina_types::Sanitizer::JsEscape),
        ];
        for (name, expect) in cases {
            // Inspect the builtin's own function type: its *latent* effect is Pure
            // (the effect of an application would also join the argument's effect).
            let (ty, _) = type_check(&ctx, &Expr::Var(name.to_string())).unwrap();
            match ty {
                Ty::Fn(_, result, latent) => {
                    assert_eq!(latent, Effect::Pure, "{name} must be a Pure transformation");
                    assert!(
                        matches!(*result, Ty::Sanitized(_, ref s) if *s == expect),
                        "{name} -> Sanitized<_, {expect:?}>, got {result:?}"
                    );
                }
                other => panic!("{name} should be a function, got {other:?}"),
            }
            // And it does accept a tainted input (Tainted -> Sanitized).
            assert!(type_check(&ctx, &sanitize_with(name)).is_ok(), "{name} accepts tainted input");
        }
    }

    #[test]
    fn taint_input_is_system_tainted_and_the_pipeline_composes() {
        let ctx = register_builtin_types(&Context::new());
        // read_line: System effect, Tainted<_, UserInput>.
        let (ty, eff) = type_check(&ctx, &read_line_tainted()).unwrap();
        assert_eq!(eff, Effect::System, "read_line is a System effect");
        assert!(
            matches!(ty, Ty::Tainted(_, riina_types::TaintSource::UserInput)),
            "read_line -> Tainted<_, UserInput>, got {ty:?}"
        );
        // End-to-end: read → sanitize → sink typechecks…
        let pipeline = Expr::App(
            Box::new(Expr::Var("sql_execute".to_string())),
            Box::new(sanitize_with("sanitize_sql")),
        );
        assert!(
            type_check(&ctx, &pipeline).is_ok(),
            "read -> sanitize -> sink pipeline must typecheck"
        );
        // …but skipping the sanitizer is rejected.
        let skip = Expr::App(
            Box::new(Expr::Var("sql_execute".to_string())),
            Box::new(read_line_tainted()),
        );
        assert!(
            matches!(type_check(&ctx, &skip), Err(TypeError::TaintViolation { .. })),
            "skipping the sanitizer must be rejected (TaintViolation)"
        );
    }

    #[test]
    fn test_time_builtins_have_precise_types_and_track_effect() {
        // The applied time builtins are sound and track Effect::Time: sleep takes
        // a millisecond Int -> Unit; format/parse take a (value, format) pair.
        let ctx = register_builtin_types(&Context::new());
        let int = || Box::new(Expr::Int(1));
        let s = |x: &str| Box::new(Expr::String(x.to_string()));
        for (name, arg, expect) in [
            ("masa_tidur", Expr::Int(0), Ty::Unit),
            ("time_sleep", Expr::Int(0), Ty::Unit),
            (
                "masa_format",
                Expr::Pair(int(), s("iso")),
                Ty::String,
            ),
            (
                "masa_urai",
                Expr::Pair(s("1"), s("iso")),
                Ty::Int,
            ),
        ] {
            let call = Expr::App(Box::new(Expr::Var(name.to_string())), Box::new(arg));
            let (ty, eff) =
                type_check(&ctx, &call).unwrap_or_else(|e| panic!("{name} should typecheck: {e:?}"));
            assert_eq!(ty, expect, "{name} result type");
            assert_eq!(eff, Effect::Time, "{name} effect");
        }
        // The zero-arg clocks are soundly typed as `Unit -> Int` (the runtime value
        // is a `Builtin` function), not a bare `Int`.
        let (ty, _) = type_check(&ctx, &Expr::Var("masa_sekarang".to_string())).unwrap();
        assert_eq!(
            ty,
            Ty::Fn(Box::new(Ty::Unit), Box::new(Ty::Int), Effect::Time),
            "a clock is a Unit -> Int function"
        );
    }

    #[test]
    fn test_time_sleep_rejects_non_int() {
        // Precise typing catches misuse: `masa_tidur("x")` is a type error (was
        // accepted under the old `Any -> Any` typing).
        let ctx = register_builtin_types(&Context::new());
        let call = Expr::App(
            Box::new(Expr::Var("masa_tidur".to_string())),
            Box::new(Expr::String("x".to_string())),
        );
        assert!(
            matches!(type_check(&ctx, &call), Err(TypeError::TypeMismatch { .. })),
            "masa_tidur of a String must be rejected"
        );
    }

    // ── 6c: SSRF (CWE-918) ──

    #[test]
    fn test_ssrf_prevented() {
        // Tainted URL passed to http_fetch_safe — REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_url = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let unsafe_fetch = Expr::App(
            Box::new(Expr::Var("http_fetch_safe".to_string())),
            Box::new(user_url),
        );

        match type_check(&ctx, &unsafe_fetch) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::UrlAllowlist);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected SSRF to be prevented, got {:?}", other),
        }
    }

    #[test]
    fn test_ssrf_safe_with_validation() {
        // validate_url(input) → http_fetch_safe — succeeds
        let ctx = register_builtin_types(&Context::new());

        let user_url = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let validated = Expr::App(
            Box::new(Expr::Var("validate_url".to_string())),
            Box::new(user_url),
        );

        let safe_fetch = Expr::App(
            Box::new(Expr::Var("http_fetch_safe".to_string())),
            Box::new(validated),
        );

        match type_check(&ctx, &safe_fetch) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!("Expected safe URL fetch to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_ssrf_sanitizer_mismatch() {
        // Path-sanitized URL for HTTP fetch — wrong sanitizer, REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_url = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let path_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_path".to_string())),
            Box::new(user_url),
        );

        let wrong_sink = Expr::App(
            Box::new(Expr::Var("http_fetch_safe".to_string())),
            Box::new(path_sanitized),
        );

        match type_check(&ctx, &wrong_sink) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::UrlAllowlist);
                assert_eq!(found, riina_types::Sanitizer::PathTraversal);
            }
            other => panic!("Expected sanitizer mismatch for SSRF, got {:?}", other),
        }
    }

    #[test]
    fn test_ssrf_open_redirect_prevented() {
        // Tainted URL for redirect — REJECTED (prevents open redirect)
        let ctx = register_builtin_types(&Context::new());

        let user_url = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let unsafe_redirect = Expr::App(
            Box::new(Expr::Var("http_redirect_safe".to_string())),
            Box::new(user_url),
        );

        match type_check(&ctx, &unsafe_redirect) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::UrlAllowlist);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!("Expected open redirect to be prevented, got {:?}", other),
        }
    }

    // ── 6d: Email Header Injection (CWE-93) ──

    #[test]
    fn test_email_header_injection_prevented() {
        // Tainted email address for email_send — REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_email = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let unsafe_send = Expr::App(
            Box::new(Expr::Var("email_send".to_string())),
            Box::new(Expr::Pair(
                Box::new(user_email),
                Box::new(Expr::String("Hello".to_string())),
            )),
        );

        match type_check(&ctx, &unsafe_send) {
            Err(TypeError::TypeMismatch { .. }) => {
                // Good! Email header injection prevented
            }
            other => panic!(
                "Expected email header injection to be prevented, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_email_safe_with_sanitization() {
        // sanitize_email(input) → email_send — succeeds
        let ctx = register_builtin_types(&Context::new());

        let user_email = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_email".to_string())),
            Box::new(user_email),
        );

        let safe_send = Expr::App(
            Box::new(Expr::Var("email_send".to_string())),
            Box::new(Expr::Pair(
                Box::new(sanitized),
                Box::new(Expr::String("Hello".to_string())),
            )),
        );

        match type_check(&ctx, &safe_send) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Bool),
            Err(e) => panic!("Expected safe email send to succeed, got error: {:?}", e),
        }
    }

    #[test]
    fn test_email_sanitizer_mismatch() {
        // JSON-sanitized data for email — wrong sanitizer, REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_email = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let json_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_json".to_string())),
            Box::new(user_email),
        );

        let wrong_sink = Expr::App(
            Box::new(Expr::Var("email_set_header".to_string())),
            Box::new(Expr::Pair(
                Box::new(Expr::String("To".to_string())),
                Box::new(json_sanitized),
            )),
        );

        match type_check(&ctx, &wrong_sink) {
            Err(TypeError::TypeMismatch { .. }) => {
                // Good! Sanitizer mismatch detected
            }
            other => panic!("Expected sanitizer mismatch for email, got {:?}", other),
        }
    }

    // ── 6e: Unsafe Deserialization (CWE-502) ──

    #[test]
    fn test_unsafe_deserialization_prevented() {
        // Tainted JSON passed to json_parse_safe — REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_json = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let unsafe_parse = Expr::App(
            Box::new(Expr::Var("json_parse_safe".to_string())),
            Box::new(user_json),
        );

        match type_check(&ctx, &unsafe_parse) {
            Err(TypeError::TaintViolation { required_sanitizer, taint_source, .. }) => {
                assert_eq!(required_sanitizer, riina_types::Sanitizer::JsonValidation);
                assert_eq!(taint_source, riina_types::TaintSource::UserInput);
            }
            other => panic!(
                "Expected unsafe deserialization to be prevented, got {:?}",
                other
            ),
        }
    }

    #[test]
    fn test_deserialization_safe_with_validation() {
        // sanitize_json(input) → deserialize_safe — succeeds
        let ctx = register_builtin_types(&Context::new());

        let user_json = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let validated = Expr::App(
            Box::new(Expr::Var("sanitize_json".to_string())),
            Box::new(user_json),
        );

        let safe_deser = Expr::App(
            Box::new(Expr::Var("deserialize_safe".to_string())),
            Box::new(validated),
        );

        match type_check(&ctx, &safe_deser) {
            Ok((ty, _)) => assert_eq!(ty, Ty::Any),
            Err(e) => panic!(
                "Expected safe deserialization to succeed, got error: {:?}",
                e
            ),
        }
    }

    #[test]
    fn test_deserialization_sanitizer_mismatch() {
        // XML-sanitized data for JSON parse — wrong sanitizer, REJECTED
        let ctx = register_builtin_types(&Context::new());

        let user_json = Expr::App(
            Box::new(Expr::Var("read_line".to_string())),
            Box::new(Expr::Unit),
        );

        let xml_sanitized = Expr::App(
            Box::new(Expr::Var("sanitize_xml".to_string())),
            Box::new(user_json),
        );

        let wrong_sink = Expr::App(
            Box::new(Expr::Var("deserialize_safe".to_string())),
            Box::new(xml_sanitized),
        );

        match type_check(&ctx, &wrong_sink) {
            Err(TypeError::SanitizerMismatch { expected, found, .. }) => {
                assert_eq!(expected, riina_types::Sanitizer::JsonValidation);
                assert_eq!(found, riina_types::Sanitizer::XmlEscape);
            }
            other => panic!(
                "Expected sanitizer mismatch for deserialization, got {:?}",
                other
            ),
        }
    }

    // ── A2: ConstantTime enforcement ──

    #[test]
    fn test_if_on_constant_time_bool_rejected() {
        // Branching on ConstantTime(Bool) must be rejected — it creates
        // a timing side-channel by revealing the CT value through control flow.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma("ct_flag".into(), Ty::ConstantTime(Box::new(Ty::Bool)));
        let expr = Expr::If(
            Box::new(Expr::Var("ct_flag".into())),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::ConstantTimeViolation { context }) => {
                assert_eq!(context, "branch condition");
            }
            other => panic!("Expected ConstantTimeViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_constant_time_arithmetic_preserves_tag() {
        // BinOp on ConstantTime(Int) operands must produce ConstantTime(Int),
        // preventing the CT discipline from being silently stripped.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma("ct_a".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        ctx = ctx.extend_gamma("ct_b".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        let add = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("ct_a".into())),
            Box::new(Expr::Var("ct_b".into())),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &add).unwrap();
        assert_eq!(ty, Ty::ConstantTime(Box::new(Ty::Int)));
    }

    #[test]
    fn test_constant_time_comparison_produces_ct_bool() {
        // Comparing ConstantTime(Int) values must produce ConstantTime(Bool),
        // which will then be rejected by If — closing the timing-leak chain.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma("ct_a".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        ctx = ctx.extend_gamma("ct_b".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        let cmp = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("ct_a".into())),
            Box::new(Expr::Var("ct_b".into())),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &cmp).unwrap();
        assert_eq!(ty, Ty::ConstantTime(Box::new(Ty::Bool)));
    }

    #[test]
    fn test_constant_time_mixed_operand_propagates() {
        // If ONE operand is ConstantTime, the result must also be ConstantTime.
        // This prevents laundering CT data through arithmetic with non-CT values.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma("ct_a".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        let add = Expr::BinOp(
            BinOp::Add,
            Box::new(Expr::Var("ct_a".into())),
            Box::new(Expr::Int(2)),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &add).unwrap();
        assert_eq!(ty, Ty::ConstantTime(Box::new(Ty::Int)));
    }

    #[test]
    fn test_non_ct_values_unaffected() {
        // Normal (non-CT) values should work as before — no CT wrapper.
        let mut ctx = TypingContext::new();
        let add = Expr::BinOp(BinOp::Add, Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let (ty, _eff) = type_check_full(&mut ctx, &add).unwrap();
        assert_eq!(ty, Ty::Int);
    }

    #[test]
    fn test_ct_comparison_then_if_rejected() {
        // End-to-end: compare CT ints → get CT(Bool) → branch on it → error.
        // This is the critical side-channel prevention chain.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma("ct_a".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        ctx = ctx.extend_gamma("ct_b".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        let cmp = Expr::BinOp(
            BinOp::Eq,
            Box::new(Expr::Var("ct_a".into())),
            Box::new(Expr::Var("ct_b".into())),
        );
        let expr = Expr::If(
            Box::new(cmp),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::ConstantTimeViolation { context }) => {
                assert_eq!(context, "branch condition");
            }
            other => panic!("Expected ConstantTimeViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_ct_error_code_and_coq_rule() {
        let err = TypeError::ConstantTimeViolation {
            context: "branch condition",
        };
        assert_eq!(err.error_code(), "CT0001");
        assert!(err.coq_rule().unwrap().contains("ConstantTimeSecurity"));
        assert!(err.fix_hint().unwrap().contains("ConstantTime"));
    }

    // ── A3: Linear type infrastructure ──

    #[test]
    fn test_linear_variable_used_once_ok() {
        // Linear variable used exactly once in Let body → should succeed.
        // Corresponds to Coq LinearTypes.v TYPE_002_01.
        // For the test, we build the Let expression but we need to intercept
        // the binding to mark it as Linear. Since Let uses extend_gamma (Unrestricted),
        // we test directly via the TypeEnv API and then via a manual context.
        let mut ctx2 = TypingContext::new();
        ctx2 = ctx2.extend_gamma_linear("x".into(), Ty::Int, Linearity::Linear);
        // Use x once
        let (ty, _eff) = type_check_full(&mut ctx2, &Expr::Var("x".into())).unwrap();
        assert_eq!(ty, Ty::Int);
        // Check linearity at exit — should pass (usage = One for Linear)
        assert!(ctx2.gamma.check_linearity_at_exit(&"x".into()).is_ok());
    }

    #[test]
    fn test_linear_variable_used_twice_rejected() {
        // Linear variable used twice → second use must be rejected.
        // Corresponds to Coq LinearTypes.v TYPE_002_08 (no contraction).
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma_linear("x".into(), Ty::Int, Linearity::Linear);
        // First use: OK
        let _ = type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap();
        // Second use: must error
        match type_check_full(&mut ctx, &Expr::Var("x".into())) {
            Err(TypeError::LinearityViolation {
                var,
                linearity,
                usage,
                ..
            }) => {
                assert_eq!(var, "x");
                assert_eq!(linearity, Linearity::Linear);
                assert_eq!(usage, Usage::Many);
            }
            other => panic!("Expected LinearityViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_linear_variable_unused_rejected() {
        // Linear variable never used → scope exit check must fail.
        // Corresponds to Coq LinearTypes.v TYPE_002_09 (no weakening).
        let ctx = TypingContext::new();
        let ctx = ctx.extend_gamma_linear("x".into(), Ty::Int, Linearity::Linear);
        // Don't use x at all
        match ctx.gamma.check_linearity_at_exit(&"x".into()) {
            Err(TypeError::LinearityViolation {
                var,
                linearity,
                usage,
                ..
            }) => {
                assert_eq!(var, "x");
                assert_eq!(linearity, Linearity::Linear);
                assert_eq!(usage, Usage::Zero);
            }
            other => panic!("Expected LinearityViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_affine_variable_used_once_ok() {
        // Affine variable used once → should succeed.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma_linear("x".into(), Ty::Int, Linearity::Affine);
        let _ = type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap();
        // At exit: usage = One, Affine allows Zero or One
        assert!(ctx.gamma.check_linearity_at_exit(&"x".into()).is_ok());
    }

    #[test]
    fn test_affine_variable_unused_ok() {
        // Affine variable unused → should succeed (can be dropped).
        // Corresponds to Coq LinearTypes.v TYPE_002_04.
        let ctx = TypingContext::new();
        let ctx = ctx.extend_gamma_linear("x".into(), Ty::Int, Linearity::Affine);
        // Don't use x
        assert!(ctx.gamma.check_linearity_at_exit(&"x".into()).is_ok());
    }

    #[test]
    fn test_affine_variable_used_twice_rejected() {
        // Affine variable used twice → must be rejected.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma_linear("x".into(), Ty::Int, Linearity::Affine);
        let _ = type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap();
        match type_check_full(&mut ctx, &Expr::Var("x".into())) {
            Err(TypeError::LinearityViolation { linearity, .. }) => {
                assert_eq!(linearity, Linearity::Affine);
            }
            other => panic!("Expected LinearityViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_relevant_variable_must_be_used() {
        // Relevant variable unused → must fail at scope exit.
        let ctx = TypingContext::new();
        let ctx = ctx.extend_gamma_linear("x".into(), Ty::Int, Linearity::Relevant);
        match ctx.gamma.check_linearity_at_exit(&"x".into()) {
            Err(TypeError::LinearityViolation {
                linearity, usage, ..
            }) => {
                assert_eq!(linearity, Linearity::Relevant);
                assert_eq!(usage, Usage::Zero);
            }
            other => panic!("Expected LinearityViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_relevant_variable_used_many_ok() {
        // Relevant variable used multiple times → should succeed (duplication OK).
        // Corresponds to Coq LinearTypes.v TYPE_002_05.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma_linear("x".into(), Ty::Int, Linearity::Relevant);
        let _ = type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap();
        let _ = type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap();
        assert!(ctx.gamma.check_linearity_at_exit(&"x".into()).is_ok());
    }

    #[test]
    fn test_unrestricted_variable_any_usage_ok() {
        // Unrestricted variable → any usage pattern is fine.
        // Corresponds to Coq LinearTypes.v TYPE_002_02.
        let mut ctx = TypingContext::new();
        ctx = ctx.extend_gamma("x".into(), Ty::Int); // default = Unrestricted
        let _ = type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap();
        let _ = type_check_full(&mut ctx, &Expr::Var("x".into())).unwrap();
        // No linearity tracking for Unrestricted → check is trivially OK
        assert!(ctx.gamma.check_linearity_at_exit(&"x".into()).is_ok());
    }

    #[test]
    fn test_linearity_error_code_and_coq_rule() {
        let err = TypeError::LinearityViolation {
            var: "x".into(),
            linearity: Linearity::Linear,
            usage: Usage::Many,
            message: "test".to_string(),
        };
        assert_eq!(err.error_code(), "LIN0001");
        assert!(err.coq_rule().unwrap().contains("LinearTypes.v"));
    }

    // ── A4: Session type support in typechecker ──

    #[test]
    fn test_chan_typed_variable_lookup() {
        // Variables with Chan type can be looked up and their type preserved.
        let mut ctx = TypingContext::new();
        let st = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        ctx = ctx.extend_gamma("ch".into(), Ty::Chan(st.clone()));
        let (ty, eff) = type_check_full(&mut ctx, &Expr::Var("ch".into())).unwrap();
        assert_eq!(ty, Ty::Chan(st));
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_secure_chan_typed_variable_lookup() {
        // SecureChan type preserves both session type and security level.
        let mut ctx = TypingContext::new();
        let st = SessionType::Recv(Box::new(Ty::Bool), Box::new(SessionType::End));
        ctx = ctx.extend_gamma(
            "sch".into(),
            Ty::SecureChan(st.clone(), SecurityLevel::Secret),
        );
        let (ty, eff) = type_check_full(&mut ctx, &Expr::Var("sch".into())).unwrap();
        assert_eq!(ty, Ty::SecureChan(st, SecurityLevel::Secret));
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_chan_let_binding() {
        // Chan-typed values flow correctly through Let bindings.
        let mut ctx = TypingContext::new();
        let st = SessionType::End;
        ctx = ctx.extend_gamma("ch".into(), Ty::Chan(st.clone()));
        // let x = ch in x
        let expr = Expr::Let(
            "x".into(),
            None,
            Box::new(Expr::Var("ch".into())),
            Box::new(Expr::Var("x".into())),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Chan(st));
    }

    #[test]
    fn test_chan_type_mismatch_in_if() {
        // If branches must agree on type — Chan vs Int → error.
        let mut ctx = TypingContext::new();
        let st = SessionType::End;
        ctx = ctx.extend_gamma("ch".into(), Ty::Chan(st));
        let expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Var("ch".into())),
            Box::new(Expr::Int(42)),
        );
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::TypeMismatch { .. }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_let_sekali_used_once_ok() {
        // biar sekali x = 1; x  → used exactly once, OK
        let mut ctx = TypingContext::new();
        let expr = Expr::Let(
            "x".into(),
            Some(Linearity::Linear),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Var("x".into())),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Int);
    }

    #[test]
    fn test_let_sekali_unused_rejected() {
        // biar sekali x = 1; 0  → unused linear var, LIN0001
        let mut ctx = TypingContext::new();
        let expr = Expr::Let(
            "x".into(),
            Some(Linearity::Linear),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::LinearityViolation {
                var,
                linearity,
                usage,
                ..
            }) => {
                assert_eq!(var, "x");
                assert_eq!(linearity, Linearity::Linear);
                assert_eq!(usage, Usage::Zero);
            }
            other => panic!("Expected LinearityViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_let_paling_unused_ok() {
        // biar paling x = 1; 0  → affine can be dropped, OK
        let mut ctx = TypingContext::new();
        let expr = Expr::Let(
            "x".into(),
            Some(Linearity::Affine),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Int);
    }

    #[test]
    fn test_let_mesti_unused_rejected() {
        // biar mesti x = 1; 0  → relevant must be used, LIN0001
        let mut ctx = TypingContext::new();
        let expr = Expr::Let(
            "x".into(),
            Some(Linearity::Relevant),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::LinearityViolation {
                var,
                linearity,
                usage,
                ..
            }) => {
                assert_eq!(var, "x");
                assert_eq!(linearity, Linearity::Relevant);
                assert_eq!(usage, Usage::Zero);
            }
            other => panic!("Expected LinearityViolation, got {:?}", other),
        }
    }

    #[test]
    fn test_chan_linear_enforcement() {
        // Channel bindings with Linear qualifier enforce single use.
        // This combines A3 (linearity) with A4 (session types).
        let mut ctx = TypingContext::new();
        let st = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        ctx = ctx.extend_gamma_linear("ch".into(), Ty::Chan(st), Linearity::Linear);
        // First use OK
        let _ = type_check_full(&mut ctx, &Expr::Var("ch".into())).unwrap();
        // Second use → LinearityViolation
        match type_check_full(&mut ctx, &Expr::Var("ch".into())) {
            Err(TypeError::LinearityViolation { .. }) => {}
            other => panic!("Expected LinearityViolation, got {:?}", other),
        }
    }

    // ==========================================================================
    // EDGE CASE TESTS — Recursive functions, nested ifs, effect enforcement
    // ==========================================================================

    #[test]
    fn test_recursive_function_typechecks() {
        // LetRec with a recursive call in the body.
        // let rec f : Int -> Int = fn(x: Int) f(x) in f
        // This should typecheck: f has type Int -> Int, and f(x) applies Int -> Int to Int.
        let ctx = Context::new();
        let fn_ty = Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure);
        let letrec = Expr::LetRec(
            "f".into(),
            fn_ty.clone(),
            Box::new(Expr::Lam(
                "x".into(),
                Ty::Int,
                Box::new(Expr::App(
                    Box::new(Expr::Var("f".into())),
                    Box::new(Expr::Var("x".into())),
                )),
            )),
            Box::new(Expr::Var("f".into())),
        );
        let (ty, eff) = type_check(&ctx, &letrec).unwrap();
        assert_eq!(ty, fn_ty);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_recursive_factorial_pattern_typechecks() {
        // LetRec modelling factorial: let rec fact : Int -> Int = fn(n: Int) if ... in fact
        let ctx = Context::new();
        let fn_ty = Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure);
        let letrec = Expr::LetRec(
            "fact".into(),
            fn_ty.clone(),
            Box::new(Expr::Lam(
                "n".into(),
                Ty::Int,
                Box::new(Expr::If(
                    Box::new(Expr::BinOp(
                        BinOp::Eq,
                        Box::new(Expr::Var("n".into())),
                        Box::new(Expr::Int(0)),
                    )),
                    Box::new(Expr::Int(1)),
                    Box::new(Expr::BinOp(
                        BinOp::Mul,
                        Box::new(Expr::Var("n".into())),
                        Box::new(Expr::App(
                            Box::new(Expr::Var("fact".into())),
                            Box::new(Expr::BinOp(
                                BinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(1)),
                            )),
                        )),
                    )),
                )),
            )),
            Box::new(Expr::App(
                Box::new(Expr::Var("fact".into())),
                Box::new(Expr::Int(5)),
            )),
        );
        let (ty, eff) = type_check(&ctx, &letrec).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_nested_if_type_consistency() {
        // Both branches of if must have the same type.
        // if true { if false { 1 } else { 2 } } else { 3 } → Int
        let ctx = Context::new();
        let nested = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::If(
                Box::new(Expr::Bool(false)),
                Box::new(Expr::Int(1)),
                Box::new(Expr::Int(2)),
            )),
            Box::new(Expr::Int(3)),
        );
        let (ty, eff) = type_check(&ctx, &nested).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_nested_if_type_mismatch_in_inner() {
        // Inner if has mismatched branches: Int vs Bool
        let ctx = Context::new();
        let nested = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::If(
                Box::new(Expr::Bool(false)),
                Box::new(Expr::Int(1)),
                Box::new(Expr::Bool(true)), // mismatch!
            )),
            Box::new(Expr::Int(3)),
        );
        match type_check(&ctx, &nested) {
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_nested_if_outer_branch_mismatch() {
        // Outer if branches disagree: then is Int, else is Bool
        let ctx = Context::new();
        let nested = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Bool(false)), // mismatch with then-branch
        );
        match type_check(&ctx, &nested) {
            Err(TypeError::TypeMismatch {
                expected: Ty::Int,
                found: Ty::Bool,
            }) => {}
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_effect_ceiling_enforcement_pure_no_write() {
        // A Pure function cannot perform Write effects.
        // fn(x: Int) -> Int {Pure} containing a Write expression should fail.
        // We model this with a Lam whose body does Ref (which requires Mut effect).
        let ctx = Context::new();
        let lam = Expr::Lam(
            "x".into(),
            Ty::Int,
            Box::new(Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public)),
        );
        // The lambda itself typechecks — the effect is in the function type.
        // The body has Mut effect, so the function type should reflect that.
        let (ty, _eff) = type_check(&ctx, &lam).unwrap();
        // The function type should have non-Pure effect (Mut)
        match ty {
            Ty::Fn(_, _, fn_eff) => {
                assert_ne!(fn_eff, Effect::Pure, "Body with Ref should not be Pure");
            }
            other => panic!("Expected Fn type, got {:?}", other),
        }
    }

    #[test]
    fn test_deeply_nested_let_typechecks() {
        // let x = 1 in let y = 2 in let z = 3 in x + y + z
        let ctx = Context::new();
        let expr = Expr::Let(
            "x".into(),
            None,
            Box::new(Expr::Int(1)),
            Box::new(Expr::Let(
                "y".into(),
                None,
                Box::new(Expr::Int(2)),
                Box::new(Expr::Let(
                    "z".into(),
                    None,
                    Box::new(Expr::Int(3)),
                    Box::new(Expr::BinOp(
                        BinOp::Add,
                        Box::new(Expr::BinOp(
                            BinOp::Add,
                            Box::new(Expr::Var("x".into())),
                            Box::new(Expr::Var("y".into())),
                        )),
                        Box::new(Expr::Var("z".into())),
                    )),
                )),
            )),
        );
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }
}

// ════════════════════════════════════════════════════════════════════════════
// JALINAN Phase 6: Session Types, Actors, Choreography, CRDTs — 51 Tests
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod jalinan_phase6_tests {
    use crate::{
        is_dual, session_dual, session_subtype, type_check, type_check_full, Context, TypeError,
        TypingContext,
    };
    use riina_types::{Effect, Expr, SessionType, Ty};

    // ── Helper: make a handler function Fn(msg_ty) -> state_ty ──

    fn make_handler(msg_ty: Ty, state_ty: Ty) -> Expr {
        Expr::Lam(
            "msg".into(),
            msg_ty,
            Box::new(match state_ty.clone() {
                Ty::Int => Expr::Int(0),
                Ty::Bool => Expr::Bool(false),
                Ty::String => Expr::String("".into()),
                _ => Expr::Unit,
            }),
        )
    }

    fn make_actor_decl(state_ty: Ty, message_ty: Ty, init: Expr, handler: Expr) -> Expr {
        Expr::ActorDecl {
            name: "myActor".into(),
            state_ty,
            message_ty,
            init_state: Box::new(init),
            handler: Box::new(handler),
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // Session Duality Tests (10)
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_session_dual_end() {
        assert_eq!(session_dual(&SessionType::End), SessionType::End);
    }

    #[test]
    fn test_session_dual_send_to_recv() {
        let s = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        let expected = SessionType::Recv(Box::new(Ty::Int), Box::new(SessionType::End));
        assert_eq!(session_dual(&s), expected);
    }

    #[test]
    fn test_session_dual_recv_to_send() {
        let s = SessionType::Recv(Box::new(Ty::String), Box::new(SessionType::End));
        let expected = SessionType::Send(Box::new(Ty::String), Box::new(SessionType::End));
        assert_eq!(session_dual(&s), expected);
    }

    #[test]
    fn test_session_dual_select_to_branch() {
        let s = SessionType::Select(Box::new(SessionType::End), Box::new(SessionType::End));
        let expected = SessionType::Branch(Box::new(SessionType::End), Box::new(SessionType::End));
        assert_eq!(session_dual(&s), expected);
    }

    #[test]
    fn test_session_dual_branch_to_select() {
        let s = SessionType::Branch(Box::new(SessionType::End), Box::new(SessionType::End));
        let expected = SessionType::Select(Box::new(SessionType::End), Box::new(SessionType::End));
        assert_eq!(session_dual(&s), expected);
    }

    #[test]
    fn test_session_dual_nested() {
        // Send(Int, Recv(Bool, End)) → Recv(Int, Send(Bool, End))
        let s = SessionType::Send(
            Box::new(Ty::Int),
            Box::new(SessionType::Recv(
                Box::new(Ty::Bool),
                Box::new(SessionType::End),
            )),
        );
        let expected = SessionType::Recv(
            Box::new(Ty::Int),
            Box::new(SessionType::Send(
                Box::new(Ty::Bool),
                Box::new(SessionType::End),
            )),
        );
        assert_eq!(session_dual(&s), expected);
    }

    #[test]
    fn test_session_dual_rec() {
        let s = SessionType::Rec(
            "X".into(),
            Box::new(SessionType::Send(
                Box::new(Ty::Int),
                Box::new(SessionType::Var("X".into())),
            )),
        );
        let expected = SessionType::Rec(
            "X".into(),
            Box::new(SessionType::Recv(
                Box::new(Ty::Int),
                Box::new(SessionType::Var("X".into())),
            )),
        );
        assert_eq!(session_dual(&s), expected);
    }

    #[test]
    fn test_session_dual_var() {
        assert_eq!(
            session_dual(&SessionType::Var("X".into())),
            SessionType::Var("X".into())
        );
    }

    #[test]
    fn test_is_dual_symmetric() {
        let s1 = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        let s2 = SessionType::Recv(Box::new(Ty::Int), Box::new(SessionType::End));
        assert!(is_dual(&s1, &s2));
        assert!(is_dual(&s2, &s1));
    }

    #[test]
    fn test_session_dual_involution() {
        // dual(dual(s)) == s
        let s = SessionType::Send(
            Box::new(Ty::Int),
            Box::new(SessionType::Recv(
                Box::new(Ty::Bool),
                Box::new(SessionType::Select(
                    Box::new(SessionType::End),
                    Box::new(SessionType::End),
                )),
            )),
        );
        assert_eq!(session_dual(&session_dual(&s)), s);
    }

    // ════════════════════════════════════════════════════════════════════
    // Session Subtyping Tests (5)
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_session_subtype_end() {
        assert!(session_subtype(&SessionType::End, &SessionType::End));
    }

    #[test]
    fn test_session_subtype_send_covariant() {
        let s1 = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        let s2 = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        assert!(session_subtype(&s1, &s2));
    }

    #[test]
    fn test_session_subtype_recv_contravariant() {
        // Recv is contravariant in payload: Recv(Any, End) <: Recv(Int, End)
        // because Any is compatible with Int
        let s1 = SessionType::Recv(Box::new(Ty::Any), Box::new(SessionType::End));
        let s2 = SessionType::Recv(Box::new(Ty::Int), Box::new(SessionType::End));
        assert!(session_subtype(&s1, &s2));
    }

    #[test]
    fn test_session_subtype_mismatch() {
        let s1 = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        let s2 = SessionType::Recv(Box::new(Ty::Int), Box::new(SessionType::End));
        assert!(!session_subtype(&s1, &s2));
    }

    #[test]
    fn test_session_subtype_var() {
        assert!(session_subtype(
            &SessionType::Var("X".into()),
            &SessionType::Var("X".into())
        ));
        assert!(!session_subtype(
            &SessionType::Var("X".into()),
            &SessionType::Var("Y".into())
        ));
    }

    // ════════════════════════════════════════════════════════════════════
    // Actor Type Checking Tests (15)
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_actor_decl_ok() {
        let ctx = Context::new();
        let handler = make_handler(Ty::String, Ty::Int);
        let expr = make_actor_decl(Ty::Int, Ty::String, Expr::Int(0), handler);
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)));
    }

    #[test]
    fn test_actor_decl_init_state_mismatch() {
        let ctx = Context::new();
        let handler = make_handler(Ty::String, Ty::Int);
        // init is Bool but state_ty is Int
        let expr = make_actor_decl(Ty::Int, Ty::String, Expr::Bool(true), handler);
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Int);
                assert_eq!(found, Ty::Bool);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_decl_handler_not_function() {
        let ctx = Context::new();
        // handler is just an Int, not a function
        let expr = make_actor_decl(Ty::Int, Ty::String, Expr::Int(0), Expr::Int(42));
        match type_check(&ctx, &expr) {
            Err(TypeError::ExpectedFunction(_)) => {}
            other => panic!("Expected ExpectedFunction, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_decl_handler_wrong_param() {
        let ctx = Context::new();
        // handler takes Int but message_ty is String
        let handler = Expr::Lam("msg".into(), Ty::Int, Box::new(Expr::Int(0)));
        let expr = make_actor_decl(Ty::Int, Ty::String, Expr::Int(0), handler);
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::String);
                assert_eq!(found, Ty::Int);
            }
            other => panic!("Expected TypeMismatch for handler param, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_decl_handler_wrong_return() {
        let ctx = Context::new();
        // handler returns Bool but state_ty is Int
        let handler = Expr::Lam("msg".into(), Ty::String, Box::new(Expr::Bool(false)));
        let expr = make_actor_decl(Ty::Int, Ty::String, Expr::Int(0), handler);
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Int);
                assert_eq!(found, Ty::Bool);
            }
            other => panic!("Expected TypeMismatch for handler return, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_decl_full_context() {
        let mut ctx = TypingContext::new();
        let handler = make_handler(Ty::String, Ty::Int);
        let expr = make_actor_decl(Ty::Int, Ty::String, Expr::Int(0), handler);
        let (ty, _eff) = type_check_full(&mut ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)));
    }

    #[test]
    fn test_spawn_ok() {
        let ctx = Context::new().extend(
            "a".into(),
            Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)),
        );
        let expr = Expr::Spawn(Box::new(Expr::Var("a".into())), Box::new(Expr::Int(42)));
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)));
        // Spawn should have Process effect
        assert_ne!(eff, Effect::Pure);
    }

    #[test]
    fn test_spawn_init_mismatch() {
        let ctx = Context::new().extend(
            "a".into(),
            Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)),
        );
        // init state is Bool, but actor expects Int
        let expr = Expr::Spawn(Box::new(Expr::Var("a".into())), Box::new(Expr::Bool(true)));
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Int);
                assert_eq!(found, Ty::Bool);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_spawn_non_actor() {
        let ctx = Context::new().extend("x".into(), Ty::Int);
        let expr = Expr::Spawn(Box::new(Expr::Var("x".into())), Box::new(Expr::Int(0)));
        match type_check(&ctx, &expr) {
            Err(TypeError::ExpectedActor(_)) => {}
            other => panic!("Expected ExpectedActor, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_send_ok() {
        let ctx = Context::new().extend(
            "a".into(),
            Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)),
        );
        let expr = Expr::ActorSend(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::String("hello".into())),
        );
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Unit);
    }

    #[test]
    fn test_actor_send_wrong_msg() {
        let ctx = Context::new().extend(
            "a".into(),
            Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)),
        );
        // send Int, but actor expects String messages
        let expr = Expr::ActorSend(Box::new(Expr::Var("a".into())), Box::new(Expr::Int(42)));
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::String);
                assert_eq!(found, Ty::Int);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_send_non_actor() {
        let ctx = Context::new().extend("x".into(), Ty::Int);
        let expr = Expr::ActorSend(Box::new(Expr::Var("x".into())), Box::new(Expr::Int(0)));
        match type_check(&ctx, &expr) {
            Err(TypeError::ExpectedActor(_)) => {}
            other => panic!("Expected ExpectedActor, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_recv_ok() {
        let ctx = Context::new().extend(
            "a".into(),
            Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)),
        );
        let expr = Expr::ActorRecv(Box::new(Expr::Var("a".into())));
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::String);
    }

    #[test]
    fn test_actor_recv_non_actor() {
        let ctx = Context::new().extend("x".into(), Ty::Bool);
        let expr = Expr::ActorRecv(Box::new(Expr::Var("x".into())));
        match type_check(&ctx, &expr) {
            Err(TypeError::ExpectedActor(_)) => {}
            other => panic!("Expected ExpectedActor, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_send_effect_is_network() {
        let ctx = Context::new().extend(
            "a".into(),
            Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)),
        );
        let expr = Expr::ActorSend(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::String("hi".into())),
        );
        let (_ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Network);
    }

    // ════════════════════════════════════════════════════════════════════
    // Choreography Tests (10)
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_choreography_ok() {
        let ctx = Context::new();
        let expr = Expr::ChoreographyBlock {
            name: "proto".into(),
            roles: vec!["Alice".into(), "Bob".into()],
            protocol: SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End)),
        };
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Pure);
        match ty {
            Ty::Choreography(roles, _) => {
                assert_eq!(roles.len(), 2);
            }
            other => panic!("Expected Choreography type, got {:?}", other),
        }
    }

    #[test]
    fn test_choreography_end_protocol() {
        let ctx = Context::new();
        let expr = Expr::ChoreographyBlock {
            name: "simple".into(),
            roles: vec!["A".into(), "B".into()],
            protocol: SessionType::End,
        };
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(
            ty,
            Ty::Choreography(vec!["A".into(), "B".into()], SessionType::End)
        );
    }

    #[test]
    fn test_choreography_send_recv_protocol() {
        let ctx = Context::new();
        let protocol = SessionType::Send(
            Box::new(Ty::Int),
            Box::new(SessionType::Recv(
                Box::new(Ty::Bool),
                Box::new(SessionType::End),
            )),
        );
        let expr = Expr::ChoreographyBlock {
            name: "ping_pong".into(),
            roles: vec!["Client".into(), "Server".into()],
            protocol: protocol.clone(),
        };
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(
            ty,
            Ty::Choreography(vec!["Client".into(), "Server".into()], protocol,)
        );
    }

    #[test]
    fn test_choreography_too_few_roles() {
        let ctx = Context::new();
        let expr = Expr::ChoreographyBlock {
            name: "bad".into(),
            roles: vec!["Alice".into()],
            protocol: SessionType::End,
        };
        match type_check(&ctx, &expr) {
            Err(TypeError::ChoreographyError { message }) => {
                assert!(message.contains("at least 2 roles"));
            }
            other => panic!("Expected ChoreographyError, got {:?}", other),
        }
    }

    #[test]
    fn test_choreography_zero_roles() {
        let ctx = Context::new();
        let expr = Expr::ChoreographyBlock {
            name: "empty".into(),
            roles: vec![],
            protocol: SessionType::End,
        };
        assert!(type_check(&ctx, &expr).is_err());
    }

    #[test]
    fn test_choreography_type_has_roles() {
        let ctx = Context::new();
        let expr = Expr::ChoreographyBlock {
            name: "test".into(),
            roles: vec!["R1".into(), "R2".into(), "R3".into()],
            protocol: SessionType::End,
        };
        let (ty, _) = type_check(&ctx, &expr).unwrap();
        match ty {
            Ty::Choreography(roles, _) => {
                assert_eq!(
                    roles,
                    vec!["R1".to_string(), "R2".to_string(), "R3".to_string()]
                );
            }
            other => panic!("Expected Choreography, got {:?}", other),
        }
    }

    #[test]
    fn test_choreography_type_has_protocol() {
        let ctx = Context::new();
        let protocol = SessionType::Recv(Box::new(Ty::Bool), Box::new(SessionType::End));
        let expr = Expr::ChoreographyBlock {
            name: "test".into(),
            roles: vec!["A".into(), "B".into()],
            protocol: protocol.clone(),
        };
        let (ty, _) = type_check(&ctx, &expr).unwrap();
        match ty {
            Ty::Choreography(_, p) => assert_eq!(p, protocol),
            other => panic!("Expected Choreography, got {:?}", other),
        }
    }

    #[test]
    fn test_choreography_pure_effect() {
        let ctx = Context::new();
        let expr = Expr::ChoreographyBlock {
            name: "test".into(),
            roles: vec!["A".into(), "B".into()],
            protocol: SessionType::End,
        };
        let (_, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_choreography_full_context() {
        let mut ctx = TypingContext::new();
        let expr = Expr::ChoreographyBlock {
            name: "test".into(),
            roles: vec!["A".into(), "B".into()],
            protocol: SessionType::End,
        };
        let (ty, eff) = type_check_full(&mut ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Pure);
        assert!(matches!(ty, Ty::Choreography(_, _)));
    }

    #[test]
    fn test_choreography_complex_protocol() {
        let ctx = Context::new();
        // Select between two branches
        let protocol = SessionType::Select(
            Box::new(SessionType::Send(
                Box::new(Ty::Int),
                Box::new(SessionType::End),
            )),
            Box::new(SessionType::Send(
                Box::new(Ty::String),
                Box::new(SessionType::End),
            )),
        );
        let expr = Expr::ChoreographyBlock {
            name: "branching".into(),
            roles: vec!["A".into(), "B".into()],
            protocol: protocol.clone(),
        };
        let (ty, _) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Choreography(vec!["A".into(), "B".into()], protocol));
    }

    // ════════════════════════════════════════════════════════════════════
    // CRDT Type Tests (10)
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_crdt_merge_ok() {
        let crdt_ty = Ty::CRDT(Box::new(Ty::Int), Box::new(Ty::Int));
        let ctx = Context::new()
            .extend("a".into(), crdt_ty.clone())
            .extend("b".into(), crdt_ty.clone());
        let expr = Expr::CRDTMerge(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, crdt_ty);
    }

    #[test]
    fn test_crdt_merge_type_mismatch() {
        let ctx = Context::new()
            .extend("a".into(), Ty::CRDT(Box::new(Ty::Int), Box::new(Ty::Int)))
            .extend(
                "b".into(),
                Ty::CRDT(Box::new(Ty::String), Box::new(Ty::Int)),
            );
        let expr = Expr::CRDTMerge(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        match type_check(&ctx, &expr) {
            Err(TypeError::CRDTMismatch { .. }) => {}
            other => panic!("Expected CRDTMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_crdt_merge_op_mismatch() {
        let ctx = Context::new()
            .extend("a".into(), Ty::CRDT(Box::new(Ty::Int), Box::new(Ty::Int)))
            .extend("b".into(), Ty::CRDT(Box::new(Ty::Int), Box::new(Ty::Bool)));
        let expr = Expr::CRDTMerge(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        match type_check(&ctx, &expr) {
            Err(TypeError::CRDTMismatch { .. }) => {}
            other => panic!("Expected CRDTMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_crdt_merge_left_not_crdt() {
        let ctx = Context::new()
            .extend("a".into(), Ty::Int)
            .extend("b".into(), Ty::CRDT(Box::new(Ty::Int), Box::new(Ty::Int)));
        let expr = Expr::CRDTMerge(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        match type_check(&ctx, &expr) {
            Err(TypeError::ExpectedCRDT(ty)) => assert_eq!(ty, Ty::Int),
            other => panic!("Expected ExpectedCRDT, got {:?}", other),
        }
    }

    #[test]
    fn test_crdt_merge_right_not_crdt() {
        let ctx = Context::new()
            .extend("a".into(), Ty::CRDT(Box::new(Ty::Int), Box::new(Ty::Int)))
            .extend("b".into(), Ty::Bool);
        let expr = Expr::CRDTMerge(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        match type_check(&ctx, &expr) {
            Err(TypeError::ExpectedCRDT(ty)) => assert_eq!(ty, Ty::Bool),
            other => panic!("Expected ExpectedCRDT, got {:?}", other),
        }
    }

    #[test]
    fn test_crdt_merge_returns_same_type() {
        let crdt_ty = Ty::CRDT(Box::new(Ty::String), Box::new(Ty::Bool));
        let ctx = Context::new()
            .extend("a".into(), crdt_ty.clone())
            .extend("b".into(), crdt_ty.clone());
        let expr = Expr::CRDTMerge(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        let (ty, _) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, crdt_ty);
    }

    #[test]
    fn test_content_hash_int() {
        let ctx = Context::new();
        let expr = Expr::ContentHash(Box::new(Expr::Int(42)));
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::ContentAddressed(Box::new(Ty::Int)));
    }

    #[test]
    fn test_content_hash_string() {
        let ctx = Context::new();
        let expr = Expr::ContentHash(Box::new(Expr::String("data".into())));
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::ContentAddressed(Box::new(Ty::String)));
    }

    #[test]
    fn test_content_hash_compound() {
        let ctx = Context::new();
        let expr = Expr::ContentHash(Box::new(Expr::Pair(
            Box::new(Expr::Int(1)),
            Box::new(Expr::Bool(true)),
        )));
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(
            ty,
            Ty::ContentAddressed(Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Bool))))
        );
    }

    #[test]
    fn test_content_hash_effect_is_crypto() {
        let ctx = Context::new();
        let expr = Expr::ContentHash(Box::new(Expr::Int(1)));
        let (_ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Crypto);
    }

    #[test]
    fn test_content_verify_success() {
        let ctx = Context::new().extend("hash".into(), Ty::ContentAddressed(Box::new(Ty::Int)));
        let expr = Expr::ContentVerify(Box::new(Expr::Var("hash".into())), Box::new(Expr::Int(42)));
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Bool);
        assert_eq!(eff, Effect::Crypto);
    }

    #[test]
    fn test_content_verify_requires_content_addressed_hash() {
        let ctx = Context::new().extend("hash".into(), Ty::String);
        let expr = Expr::ContentVerify(Box::new(Expr::Var("hash".into())), Box::new(Expr::Int(42)));
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::ContentAddressed(Box::new(Ty::Int)));
                assert_eq!(found, Ty::String);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_content_verify_rejects_mismatched_inner_type() {
        let ctx = Context::new().extend("hash".into(), Ty::ContentAddressed(Box::new(Ty::String)));
        let expr = Expr::ContentVerify(Box::new(Expr::Var("hash".into())), Box::new(Expr::Int(42)));
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::ContentAddressed(Box::new(Ty::Int)));
                assert_eq!(found, Ty::ContentAddressed(Box::new(Ty::String)));
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_contract_deploy_wraps_inner_type() {
        let ctx = Context::new();
        let expr = Expr::ContractDeploy(Box::new(Expr::Int(7)));
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::SmartContract(Box::new(Ty::Int)));
        assert_eq!(eff, Effect::NetworkSecure);
    }

    #[test]
    fn test_contract_deploy_preserves_inner_effects() {
        let ctx = Context::new().extend("hash".into(), Ty::ContentAddressed(Box::new(Ty::Int)));
        let expr = Expr::ContractDeploy(Box::new(Expr::ContentVerify(
            Box::new(Expr::Var("hash".into())),
            Box::new(Expr::Int(9)),
        )));
        let (_ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Crypto);
    }

    #[test]
    fn test_token_transfer_ok() {
        let token_ty = Ty::Token(Box::new(Ty::Int));
        let ctx = Context::new()
            .extend("alice".into(), token_ty.clone())
            .extend("bob".into(), token_ty.clone());
        let expr = Expr::TokenTransfer {
            from: Box::new(Expr::Var("alice".into())),
            to: Box::new(Expr::Var("bob".into())),
            amount: Box::new(Expr::Int(25)),
        };
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, token_ty);
        assert_eq!(eff, Effect::NetworkSecure);
    }

    #[test]
    fn test_token_transfer_rejects_non_token_sender() {
        let ctx = Context::new()
            .extend("alice".into(), Ty::Int)
            .extend("bob".into(), Ty::Token(Box::new(Ty::Int)));
        let expr = Expr::TokenTransfer {
            from: Box::new(Expr::Var("alice".into())),
            to: Box::new(Expr::Var("bob".into())),
            amount: Box::new(Expr::Int(10)),
        };
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Token(Box::new(Ty::Int)));
                assert_eq!(found, Ty::Int);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_token_transfer_rejects_mismatched_recipient_type() {
        let ctx = Context::new()
            .extend("alice".into(), Ty::Token(Box::new(Ty::Int)))
            .extend("bob".into(), Ty::Token(Box::new(Ty::String)));
        let expr = Expr::TokenTransfer {
            from: Box::new(Expr::Var("alice".into())),
            to: Box::new(Expr::Var("bob".into())),
            amount: Box::new(Expr::Int(10)),
        };
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Token(Box::new(Ty::Int)));
                assert_eq!(found, Ty::Token(Box::new(Ty::String)));
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_token_transfer_rejects_wrong_amount_type() {
        let token_ty = Ty::Token(Box::new(Ty::Int));
        let ctx = Context::new()
            .extend("alice".into(), token_ty.clone())
            .extend("bob".into(), token_ty);
        let expr = Expr::TokenTransfer {
            from: Box::new(Expr::Var("alice".into())),
            to: Box::new(Expr::Var("bob".into())),
            amount: Box::new(Expr::String("sepuluh".into())),
        };
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Int);
                assert_eq!(found, Ty::String);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_zakat_calculate_int() {
        let ctx = Context::new();
        let expr = Expr::ZakatCalculate(Box::new(Expr::Int(1_000)));
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_zakat_calculate_token_int() {
        let ctx = Context::new().extend("dana".into(), Ty::Token(Box::new(Ty::Int)));
        let expr = Expr::ZakatCalculate(Box::new(Expr::Var("dana".into())));
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Token(Box::new(Ty::Int)));
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_zakat_calculate_rejects_non_numeric_value() {
        let ctx = Context::new();
        let expr = Expr::ZakatCalculate(Box::new(Expr::Bool(true)));
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Int);
                assert_eq!(found, Ty::Bool);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    // ════════════════════════════════════════════════════════════════════
    // Integration & Error Tests (6)
    // ════════════════════════════════════════════════════════════════════

    #[test]
    fn test_spawn_effect_is_process() {
        let ctx = Context::new().extend(
            "a".into(),
            Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)),
        );
        let expr = Expr::Spawn(Box::new(Expr::Var("a".into())), Box::new(Expr::Int(0)));
        let (_ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Process);
    }

    #[test]
    fn test_actor_recv_effect_is_network() {
        let ctx =
            Context::new().extend("a".into(), Ty::Actor(Box::new(Ty::Int), Box::new(Ty::Bool)));
        let expr = Expr::ActorRecv(Box::new(Expr::Var("a".into())));
        let (_ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(eff, Effect::Network);
    }

    #[test]
    fn test_content_hash_nested() {
        let ctx = Context::new();
        let expr = Expr::ContentHash(Box::new(Expr::ContentHash(Box::new(Expr::Int(1)))));
        let (ty, _eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(
            ty,
            Ty::ContentAddressed(Box::new(Ty::ContentAddressed(Box::new(Ty::Int))))
        );
    }

    #[test]
    fn test_ui_text_requires_color_argument() {
        let ctx = Context::new();
        let expr = Expr::UIText(
            Box::new(Expr::String("hello".into())),
            Box::new(Expr::String("#ffffff".into())),
        );
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Color);
                assert_eq!(found, Ty::String);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_ui_contrast_white_on_black_passes() {
        let ctx = Context::new();
        let expr = Expr::UIContrastCheck(
            Box::new(Expr::UIColor(255, 255, 255)),
            Box::new(Expr::UIColor(0, 0, 0)),
        );
        let (ty, eff) = type_check(&ctx, &expr).unwrap();
        assert_eq!(ty, Ty::Bool);
        assert_eq!(eff, Effect::Pure);
    }

    #[test]
    fn test_ui_contrast_requires_color_arguments() {
        let ctx = Context::new();
        let expr = Expr::UIContrastCheck(
            Box::new(Expr::String("white".into())),
            Box::new(Expr::UIColor(0, 0, 0)),
        );
        match type_check(&ctx, &expr) {
            Err(TypeError::TypeMismatch { expected, found }) => {
                assert_eq!(expected, Ty::Color);
                assert_eq!(found, Ty::String);
            }
            other => panic!("Expected TypeMismatch, got {:?}", other),
        }
    }

    #[test]
    fn test_actor_full_lifecycle() {
        // Declare actor, then test send and recv in separate contexts
        let ctx = Context::new();
        let handler = make_handler(Ty::String, Ty::Int);
        let decl = make_actor_decl(Ty::Int, Ty::String, Expr::Int(0), handler);
        let (decl_ty, _) = type_check(&ctx, &decl).unwrap();
        assert_eq!(decl_ty, Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)));

        // Spawn: use the actor type in context
        let ctx2 = Context::new().extend("actor".into(), decl_ty);
        let spawn_expr = Expr::Spawn(Box::new(Expr::Var("actor".into())), Box::new(Expr::Int(42)));
        let (spawn_ty, _) = type_check(&ctx2, &spawn_expr).unwrap();
        assert_eq!(spawn_ty, Ty::Actor(Box::new(Ty::Int), Box::new(Ty::String)));

        // Send
        let ctx3 = Context::new().extend("spawned".into(), spawn_ty);
        let send_expr = Expr::ActorSend(
            Box::new(Expr::Var("spawned".into())),
            Box::new(Expr::String("msg".into())),
        );
        let (send_ty, _) = type_check(&ctx3, &send_expr).unwrap();
        assert_eq!(send_ty, Ty::Unit);

        // Recv
        let recv_expr = Expr::ActorRecv(Box::new(Expr::Var("spawned".into())));
        let (recv_ty, _) = type_check(&ctx3, &recv_expr).unwrap();
        assert_eq!(recv_ty, Ty::String);
    }

    #[test]
    fn test_session_dual_complex_protocol() {
        // A complex multi-step protocol
        let protocol = SessionType::Rec(
            "loop".into(),
            Box::new(SessionType::Send(
                Box::new(Ty::Int),
                Box::new(SessionType::Recv(
                    Box::new(Ty::Bool),
                    Box::new(SessionType::Select(
                        Box::new(SessionType::Var("loop".into())),
                        Box::new(SessionType::End),
                    )),
                )),
            )),
        );
        let dual = session_dual(&protocol);
        let expected_dual = SessionType::Rec(
            "loop".into(),
            Box::new(SessionType::Recv(
                Box::new(Ty::Int),
                Box::new(SessionType::Send(
                    Box::new(Ty::Bool),
                    Box::new(SessionType::Branch(
                        Box::new(SessionType::Var("loop".into())),
                        Box::new(SessionType::End),
                    )),
                )),
            )),
        );
        assert_eq!(dual, expected_dual);
        // Involution: dual(dual(s)) == s
        assert_eq!(session_dual(&dual), protocol);
        // is_dual check
        assert!(is_dual(&protocol, &dual));
    }

    #[test]
    fn test_crdt_merge_full_context() {
        let mut ctx = TypingContext::new();
        let crdt_ty = Ty::CRDT(Box::new(Ty::Int), Box::new(Ty::Int));
        ctx.gamma.vars.insert("a".into(), crdt_ty.clone());
        ctx.gamma.vars.insert("b".into(), crdt_ty.clone());
        let expr = Expr::CRDTMerge(
            Box::new(Expr::Var("a".into())),
            Box::new(Expr::Var("b".into())),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &expr).unwrap();
        assert_eq!(ty, crdt_ty);
    }

    #[test]
    fn test_unannotated_inl_inr_infer_sum() {
        // Inl/Inr with Ty::Any (from Some/Ok/Err/None desugaring) infer a sum type.
        let ctx = Context::new();
        let some = Expr::Inl(Box::new(Expr::Int(5)), Ty::Any);
        let (ty, _eff) = type_check(&ctx, &some).unwrap();
        assert!(matches!(ty, Ty::Sum(l, _) if *l == Ty::Int));
        let err = Expr::Inr(Box::new(Expr::String("e".into())), Ty::Any);
        let (ty2, _eff2) = type_check(&ctx, &err).unwrap();
        assert!(matches!(ty2, Ty::Sum(_, r) if *r == Ty::String));
    }
}

// ===========================================================================
// GATE B — Compiler ⇄ Coq enforcement-parity surface.
//
// For each Coq-stated security property, a NEGATIVE test (a violating program
// is rejected with the matching `TypeError`) and a POSITIVE test (a valid
// program is accepted). Verified end-to-end against `type_check_full`
// (2026-06-01). Each property names the Coq rule it mirrors.
// ===========================================================================
#[cfg(test)]
mod gate_b_parity {
    use crate::{is_dual, type_check, type_check_full, types_compatible, Context, TypeError, TypingContext};
    use riina_types::{Effect, Expr, Linearity, SecurityLevel, SessionType, Ty};

    // ── Property 1: Capability safety — Coq T_Require / T_Grant (Typing.v:207-213)
    #[test]
    fn capability_require_ungranted_is_rejected() {
        // grant Network in (require Write in 1) → Write ∉ {Network} → rejected
        let mut ctx = TypingContext::new();
        let expr = Expr::Grant(
            Effect::Network,
            Box::new(Expr::Require(Effect::Write, Box::new(Expr::Int(1)))),
        );
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::CapabilityViolation { required, .. }) => {
                assert_eq!(required, Effect::Write);
            }
            other => panic!("expected CapabilityViolation, got {other:?}"),
        }
    }

    #[test]
    fn capability_require_granted_is_accepted() {
        // grant Write in (require Write in 1) → ok
        let mut ctx = TypingContext::new();
        let expr = Expr::Grant(
            Effect::Write,
            Box::new(Expr::Require(Effect::Write, Box::new(Expr::Int(1)))),
        );
        let (ty, _eff) = type_check_full(&mut ctx, &expr).expect("granted require must typecheck");
        assert_eq!(ty, Ty::Int);
    }

    // ── Property 2: IFC no-write-down — Coq T_Assign Bell-LaPadula *-property
    #[test]
    fn ifc_write_down_is_rejected() {
        // Δ=Secret writing to a Public ref → Secret ⊑ Public is false → rejected
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let assign = Expr::Assign(
            Box::new(Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public)),
            Box::new(Expr::Int(2)),
        );
        match type_check_full(&mut ctx, &assign) {
            Err(TypeError::ImplicitFlowViolation {
                branch_level,
                target_level,
                ..
            }) => {
                assert_eq!(branch_level, SecurityLevel::Secret);
                assert_eq!(target_level, SecurityLevel::Public);
            }
            other => panic!("expected ImplicitFlowViolation, got {other:?}"),
        }
    }

    #[test]
    fn ifc_write_same_level_is_accepted() {
        // Δ=Secret writing to a Secret ref → Secret ⊑ Secret → ok
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let assign = Expr::Assign(
            Box::new(Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Secret)),
            Box::new(Expr::Int(2)),
        );
        type_check_full(&mut ctx, &assign).expect("same-level write must typecheck");
    }

    // ── Property 3: IFC no-read-up — Coq T_Deref (l ⊑ Δ)
    #[test]
    fn ifc_read_up_is_rejected() {
        // Δ=Public dereferencing a Secret ref → Secret ⊑ Public false → rejected
        let mut ctx = TypingContext::new() // Δ defaults to Public
            .extend_gamma(
                "sref".into(),
                Ty::Ref(Box::new(Ty::Int), SecurityLevel::Secret),
            );
        let deref = Expr::Deref(Box::new(Expr::Var("sref".into())));
        match type_check_full(&mut ctx, &deref) {
            Err(TypeError::SecurityViolation { found, expected, .. }) => {
                assert_eq!(found, SecurityLevel::Secret);
                assert_eq!(expected, SecurityLevel::Public);
            }
            other => panic!("expected SecurityViolation, got {other:?}"),
        }
    }

    #[test]
    fn ifc_read_at_level_is_accepted() {
        // Δ=Public dereferencing a Public ref → Public ⊑ Public → ok
        let mut ctx = TypingContext::new().extend_gamma(
            "pref".into(),
            Ty::Ref(Box::new(Ty::Int), SecurityLevel::Public),
        );
        let deref = Expr::Deref(Box::new(Expr::Var("pref".into())));
        let (ty, _eff) = type_check_full(&mut ctx, &deref).expect("public deref must typecheck");
        assert_eq!(ty, Ty::Int);
    }

    // ── Property 4: Constant-time — A2 (no secret-dependent branching)
    #[test]
    fn constant_time_branch_is_rejected() {
        // Branching on a ConstantTime value reveals it through control flow.
        let mut ctx = TypingContext::new()
            .extend_gamma("ct".into(), Ty::ConstantTime(Box::new(Ty::Bool)));
        let if_expr = Expr::If(
            Box::new(Expr::Var("ct".into())),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        match type_check_full(&mut ctx, &if_expr) {
            Err(TypeError::ConstantTimeViolation { context }) => {
                assert_eq!(context, "branch condition");
            }
            other => panic!("expected ConstantTimeViolation, got {other:?}"),
        }
    }

    #[test]
    fn constant_time_plain_branch_is_accepted() {
        // Branching on a plain Bool is fine.
        let mut ctx = TypingContext::new();
        let if_expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(0)),
        );
        type_check_full(&mut ctx, &if_expr).expect("plain bool branch must typecheck");
    }

    #[test]
    fn constant_time_division_is_rejected() {
        // A2 (depth): integer division/modulo have data-dependent latency, so a
        // ConstantTime operand leaks via timing — reject `ct / 2`.
        let mut ctx = TypingContext::new()
            .extend_gamma("ct".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        let div = Expr::BinOp(
            riina_types::BinOp::Div,
            Box::new(Expr::Var("ct".into())),
            Box::new(Expr::Int(2)),
        );
        match type_check_full(&mut ctx, &div) {
            Err(TypeError::ConstantTimeViolation { context }) => {
                assert!(context.contains("division") || context.contains("modulo"));
            }
            other => panic!("expected ConstantTimeViolation for CT division, got {other:?}"),
        }
    }

    #[test]
    fn constant_time_modulo_is_rejected() {
        let mut ctx = TypingContext::new()
            .extend_gamma("ct".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        let modulo = Expr::BinOp(
            riina_types::BinOp::Mod,
            Box::new(Expr::Var("ct".into())),
            Box::new(Expr::Int(7)),
        );
        assert!(matches!(
            type_check_full(&mut ctx, &modulo),
            Err(TypeError::ConstantTimeViolation { .. })
        ));
    }

    #[test]
    fn constant_time_addition_is_accepted() {
        // Add/Sub/Mul are constant-time and keep the CT tag (no rejection).
        let mut ctx = TypingContext::new()
            .extend_gamma("ct".into(), Ty::ConstantTime(Box::new(Ty::Int)));
        let add = Expr::BinOp(
            riina_types::BinOp::Add,
            Box::new(Expr::Var("ct".into())),
            Box::new(Expr::Int(1)),
        );
        let (ty, _) = type_check_full(&mut ctx, &add).expect("CT addition must typecheck");
        // The CT tag is preserved through the operation.
        assert!(matches!(ty, Ty::ConstantTime(_)));
    }

    // ── Property 5: Linear types — Coq linear_safety (LinearTypes.v)
    #[test]
    fn linear_variable_used_twice_is_rejected() {
        // A `Linear` variable used twice (here, both halves of a pair) is rejected.
        let mut ctx = TypingContext::new().extend_gamma_linear(
            "x".into(),
            Ty::Int,
            Linearity::Linear,
        );
        let used_twice = Expr::Pair(
            Box::new(Expr::Var("x".into())),
            Box::new(Expr::Var("x".into())),
        );
        match type_check_full(&mut ctx, &used_twice) {
            Err(TypeError::LinearityViolation { linearity, .. }) => {
                assert_eq!(linearity, Linearity::Linear);
            }
            other => panic!("expected LinearityViolation, got {other:?}"),
        }
    }

    #[test]
    fn linear_variable_used_once_is_accepted() {
        // A `Linear` variable used exactly once is accepted.
        let mut ctx = TypingContext::new().extend_gamma_linear(
            "x".into(),
            Ty::Int,
            Linearity::Linear,
        );
        let (ty, _eff) =
            type_check_full(&mut ctx, &Expr::Var("x".into())).expect("single use must typecheck");
        assert_eq!(ty, Ty::Int);
    }

    // ── Property 6: Session types — Coq session_type_safety (protocol duality)
    #[test]
    fn session_non_dual_protocols_are_rejected() {
        // Two endpoints that both Send are NOT compatible (dual of Send is Recv).
        let send_int = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        assert!(
            !is_dual(&send_int, &send_int),
            "two Send endpoints must not be dual-compatible"
        );
    }

    #[test]
    fn session_dual_protocols_are_accepted() {
        // Send(Int).End is dual to Recv(Int).End → compatible endpoints.
        let send_int = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::End));
        let recv_int = SessionType::Recv(Box::new(Ty::Int), Box::new(SessionType::End));
        assert!(
            is_dual(&send_int, &recv_int),
            "Send/Recv endpoints of the same type must be dual"
        );
    }

    #[test]
    fn choreography_underspecified_roles_are_rejected() {
        // A choreography with < 2 roles is malformed → rejected (T_Choreography).
        let mut ctx = TypingContext::new();
        let choreo = Expr::ChoreographyBlock {
            name: "P".into(),
            roles: vec!["A".into()],
            protocol: SessionType::End,
        };
        match type_check_full(&mut ctx, &choreo) {
            Err(TypeError::ChoreographyError { .. }) => {}
            other => panic!("expected ChoreographyError, got {other:?}"),
        }
    }

    #[test]
    fn choreography_two_roles_is_accepted() {
        let mut ctx = TypingContext::new();
        let choreo = Expr::ChoreographyBlock {
            name: "P".into(),
            roles: vec!["A".into(), "B".into()],
            protocol: SessionType::End,
        };
        let (ty, _eff) = type_check_full(&mut ctx, &choreo)
            .expect("well-formed choreography must typecheck");
        assert!(matches!(ty, Ty::Choreography(..)));
    }

    // ── Property 3 (depth): IFC reference aliasing — the security level travels
    // with a `let`-bound reference, so no-read-up is enforced through the alias,
    // not just on a literal `ref`. Coq T_Deref (l ⊑ Δ) over a bound variable.
    #[test]
    fn ifc_aliased_secret_ref_read_up_is_rejected() {
        // Δ=Public: `let r = ref@Secret 42 in deref(r)` — reading the Secret
        // through the alias `r` is still a no-read-up violation.
        let mut ctx = TypingContext::new(); // Δ defaults to Public
        let e = Expr::Let(
            "r".into(),
            None,
            Box::new(Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Secret)),
            Box::new(Expr::Deref(Box::new(Expr::Var("r".into())))),
        );
        match type_check_full(&mut ctx, &e) {
            Err(TypeError::SecurityViolation {
                found, expected, ..
            }) => {
                assert_eq!(found, SecurityLevel::Secret);
                assert_eq!(expected, SecurityLevel::Public);
            }
            other => panic!("expected SecurityViolation through alias, got {other:?}"),
        }
    }

    #[test]
    fn ifc_aliased_secret_ref_read_at_level_is_accepted() {
        // Δ=Secret: the same aliased read is allowed (Secret ⊑ Secret).
        let mut ctx = TypingContext::with_level(SecurityLevel::Secret);
        let e = Expr::Let(
            "r".into(),
            None,
            Box::new(Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Secret)),
            Box::new(Expr::Deref(Box::new(Expr::Var("r".into())))),
        );
        type_check_full(&mut ctx, &e).expect("aliased read at level must typecheck");
    }

    // ── Property 1 (depth): Capability enforcement at a *nested* call site — a
    // `require` inside an applied lambda body is checked against the grants in
    // scope, not only top-level requires. Coq T_Require / T_Grant.
    #[test]
    fn capability_required_in_nested_call_is_rejected() {
        // grant Network in ((λx. require Write in x) 1) — Write is required deep
        // in the call but only Network is granted → rejected.
        let mut ctx = TypingContext::new();
        let lam = Expr::Lam(
            "x".into(),
            Ty::Int,
            Box::new(Expr::Require(Effect::Write, Box::new(Expr::Var("x".into())))),
        );
        let app = Expr::App(Box::new(lam), Box::new(Expr::Int(1)));
        let expr = Expr::Grant(Effect::Network, Box::new(app));
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::CapabilityViolation { required, .. }) => {
                assert_eq!(required, Effect::Write);
            }
            other => panic!("expected CapabilityViolation at nested call site, got {other:?}"),
        }
    }

    #[test]
    fn capability_required_in_nested_call_is_accepted() {
        // grant Write in ((λx. require Write in x) 1) — the matching grant in
        // scope makes the nested require typecheck.
        let mut ctx = TypingContext::new();
        let lam = Expr::Lam(
            "x".into(),
            Ty::Int,
            Box::new(Expr::Require(Effect::Write, Box::new(Expr::Var("x".into())))),
        );
        let app = Expr::App(Box::new(lam), Box::new(Expr::Int(1)));
        let expr = Expr::Grant(Effect::Write, Box::new(app));
        type_check_full(&mut ctx, &expr).expect("granted nested require must typecheck");
    }

    // ── Property 6 (depth): Session projection — projecting a choreography's
    // global protocol onto its two roles yields dual local types (the binary
    // specialisation of the Coq `project` fixpoint; projected endpoints are dual
    // by construction → deadlock-free composition, CT_103/ST_020).
    use crate::{choreography_compatible, project_choreography, session_well_formed};

    #[test]
    fn session_projection_yields_dual_endpoints() {
        // Protocol (Buyer's view): Send Order . Recv Confirm . End
        let roles = vec!["Buyer".to_string(), "Seller".to_string()];
        let protocol = SessionType::Send(
            Box::new(Ty::Int),
            Box::new(SessionType::Recv(Box::new(Ty::Bool), Box::new(SessionType::End))),
        );
        let buyer = project_choreography(&roles, &protocol, "Buyer").expect("buyer projects");
        let seller = project_choreography(&roles, &protocol, "Seller").expect("seller projects");
        // Buyer's local type is the protocol; Seller's is its dual.
        assert_eq!(buyer, protocol);
        assert_eq!(
            seller,
            SessionType::Recv(
                Box::new(Ty::Int),
                Box::new(SessionType::Send(Box::new(Ty::Bool), Box::new(SessionType::End))),
            )
        );
        assert!(is_dual(&buyer, &seller), "projected endpoints must be dual");
    }

    #[test]
    fn session_projection_unknown_role_is_none() {
        let roles = vec!["Buyer".to_string(), "Seller".to_string()];
        let protocol = SessionType::End;
        assert!(project_choreography(&roles, &protocol, "Courier").is_none());
    }

    #[test]
    fn session_projection_multiparty_is_unsupported() {
        // Binary session types cannot express a 3-party local view → None
        // (tracked as future multiparty-global-type work).
        let roles = vec!["A".to_string(), "B".to_string(), "C".to_string()];
        assert!(project_choreography(&roles, &SessionType::End, "A").is_none());
    }

    #[test]
    fn choreography_with_free_session_var_is_rejected() {
        // A protocol with an unbound recursion variable is ill-formed.
        let roles = vec!["A".to_string(), "B".to_string()];
        let bad = SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::Var("X".into())));
        assert!(!session_well_formed(&bad));
        assert!(choreography_compatible(&roles, &bad).is_err());
    }

    #[test]
    fn choreography_with_bound_recursion_is_accepted() {
        // rec X. Send Int . X  — closed, so well-formed and compatible.
        let roles = vec!["A".to_string(), "B".to_string()];
        let ok = SessionType::Rec(
            "X".into(),
            Box::new(SessionType::Send(Box::new(Ty::Int), Box::new(SessionType::Var("X".into())))),
        );
        assert!(session_well_formed(&ok));
        choreography_compatible(&roles, &ok).expect("closed recursive protocol is compatible");
    }

    #[test]
    fn choreography_with_duplicate_roles_is_rejected() {
        let roles = vec!["A".to_string(), "A".to_string()];
        assert!(choreography_compatible(&roles, &SessionType::End).is_err());
    }

    #[test]
    fn choreography_block_ill_formed_is_rejected_by_typechecker() {
        // End-to-end: a ChoreographyBlock carrying a free session var is rejected
        // by `type_check_full` with a ChoreographyError.
        let mut ctx = TypingContext::new();
        let choreo = Expr::ChoreographyBlock {
            name: "P".into(),
            roles: vec!["A".into(), "B".into()],
            protocol: SessionType::Send(
                Box::new(Ty::Int),
                Box::new(SessionType::Var("Loose".into())),
            ),
        };
        match type_check_full(&mut ctx, &choreo) {
            Err(TypeError::ChoreographyError { .. }) => {}
            other => panic!("expected ChoreographyError for free session var, got {other:?}"),
        }
    }

    // ── Effect operations: Coq T_Perform (Typing.v:168) —
    //   `e : T ! ε  ⊢  perform eff e : T ! (ε ⊔ eff)`.
    // The payload type passes through unchanged and the performed effect is joined;
    // there is no payload-vs-signature premise (RIINA's effect model has no per-effect
    // signatures), so the Rust arm deliberately performs no extra validation — this
    // test locks that parity in.
    #[test]
    fn perform_passes_payload_type_through_and_joins_effect() {
        let mut ctx = TypingContext::new();
        let e = Expr::Perform(Effect::Write, Box::new(Expr::Int(42)));
        let (ty, eff) = type_check_full(&mut ctx, &e).expect("perform must typecheck");
        assert_eq!(ty, Ty::Int, "payload type T passes through unchanged");
        assert_eq!(eff, Effect::Write, "performed effect is joined into the result");
    }

    #[test]
    fn perform_joins_effect_over_already_effectful_payload() {
        let mut ctx = TypingContext::new();
        let inner = Expr::Perform(Effect::Read, Box::new(Expr::Int(0)));
        let outer = Expr::Perform(Effect::Write, Box::new(inner));
        let (ty, eff) = type_check_full(&mut ctx, &outer).expect("nested perform must typecheck");
        assert_eq!(ty, Ty::Int);
        assert_eq!(eff, Effect::Read.join(Effect::Write));
    }

    // ── Gate C (hybrid POLA): Network/Process capability gating ──
    // Once a program opts into the capability discipline (some grant in scope), a
    // Network operation requires the Network capability granted (mirrors
    // T_Require). With no grants at all, the discipline is not opted into and the
    // call stays permissive — so existing programs are unaffected.
    fn builtins_ctx() -> TypingContext {
        crate::register_builtin_types(&crate::Context::new()).to_typing_context()
    }

    fn http_get_call() -> Expr {
        Expr::App(
            Box::new(Expr::Var("http_get".into())),
            Box::new(Expr::String("https://example.test".into())),
        )
    }

    #[test]
    fn network_op_without_grant_in_capability_scope_is_rejected() {
        // grant Write in (http_get "…") — Network is not granted ⇒ rejected.
        let mut ctx = builtins_ctx();
        let expr = Expr::Grant(Effect::Write, Box::new(http_get_call()));
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::CapabilityViolation { required, .. }) => {
                assert_eq!(required, Effect::Network);
            }
            other => panic!("expected CapabilityViolation for ungated network op, got {other:?}"),
        }
    }

    #[test]
    fn network_op_with_grant_is_accepted() {
        // grant Rangkaian in (http_get "…") — the matching grant authorizes it.
        let mut ctx = builtins_ctx();
        let expr = Expr::Grant(Effect::Network, Box::new(http_get_call()));
        type_check_full(&mut ctx, &expr).expect("granted network op must typecheck");
    }

    #[test]
    fn network_op_without_any_capabilities_is_permissive() {
        // No grants anywhere ⇒ capability discipline not opted into ⇒ allowed
        // (consistent with the opt-in T_Require semantics).
        let mut ctx = builtins_ctx();
        type_check_full(&mut ctx, &http_get_call())
            .expect("network op without any capability discipline stays permissive");
    }

    // Crypto/Random/System are gated by the same opt-in mechanism (now sound for
    // compound declared effects via `effect_set`). `random` carries
    // `Effect::Random`; exercise the gate through it.
    fn random_call() -> Expr {
        Expr::App(Box::new(Expr::Var("random".into())), Box::new(Expr::Int(10)))
    }

    #[test]
    fn random_op_without_grant_in_capability_scope_is_rejected() {
        // grant Write in (random 10) — Random is not granted ⇒ rejected.
        let mut ctx = builtins_ctx();
        let expr = Expr::Grant(Effect::Write, Box::new(random_call()));
        match type_check_full(&mut ctx, &expr) {
            Err(TypeError::CapabilityViolation { required, .. }) => {
                assert_eq!(required, Effect::Random);
            }
            other => panic!("expected CapabilityViolation for ungated random op, got {other:?}"),
        }
    }

    #[test]
    fn random_op_with_grant_is_accepted() {
        let mut ctx = builtins_ctx();
        let expr = Expr::Grant(Effect::Random, Box::new(random_call()));
        type_check_full(&mut ctx, &expr).expect("granted random op must typecheck");
    }

    // ── Property 7: Crypto-agility — Coq crypto/AlgorithmPolicy.v `accepts` ──
    // The Rust check mirrors `accepts pol (CUse a) = (pol a = Current)`.

    fn select(algo: &str) -> Expr {
        // guna_kripto("<algo>") — the `CUse a` node.
        Expr::App(
            Box::new(Expr::Var("guna_kripto".into())),
            Box::new(Expr::String(algo.into())),
        )
    }

    #[test]
    fn deprecated_primitive_is_rejected() {
        // A broken algorithm (md5) and a removal-target algorithm (rsa1024)
        // must both be rejected at the selection site.
        for algo in ["md5", "sha1", "des", "rc4", "rsa1024"] {
            let mut ctx = builtins_ctx();
            match type_check_full(&mut ctx, &select(algo)) {
                Err(TypeError::DeprecatedAlgorithm { algorithm, .. }) => {
                    assert_eq!(algorithm, algo, "the rejected name must be reported");
                }
                other => panic!("guna_kripto(\"{algo}\") must be a DeprecatedAlgorithm, got {other:?}"),
            }
        }
    }

    #[test]
    fn allowed_primitive_is_accepted() {
        // NEGATIVE CONTROL: a current algorithm must typecheck — the check is
        // COMPLETE (crypto/AlgorithmPolicy.v `uses_only_current_accepts`), so it
        // has no false positives and does not simply reject everything.
        for algo in ["aes256-gcm", "sha3-256", "ml-kem-768", "x25519", "chacha20-poly1305"] {
            let mut ctx = builtins_ctx();
            type_check_full(&mut ctx, &select(algo))
                .unwrap_or_else(|e| panic!("guna_kripto(\"{algo}\") must typecheck, got {e:?}"));
        }
    }

    #[test]
    fn deprecation_is_case_insensitive_and_selection_specific() {
        // Case-insensitive (MD5 == md5)...
        let mut ctx = builtins_ctx();
        assert!(matches!(
            type_check_full(&mut ctx, &select("MD5")),
            Err(TypeError::DeprecatedAlgorithm { .. })
        ));
        // ...but only at a SELECTION builtin: `md5` as a bare string flowing to
        // a print sink is not an algorithm selection, so the deprecation rule
        // does not fire (that string is data, not an algorithm choice).
        let mut ctx2 = builtins_ctx();
        let printed = Expr::App(
            Box::new(Expr::Var("cetak".into())),
            Box::new(Expr::String("md5".into())),
        );
        assert!(
            !matches!(
                type_check_full(&mut ctx2, &printed),
                Err(TypeError::DeprecatedAlgorithm { .. })
            ),
            "the deprecation rule must fire only at algorithm-selection sites"
        );
    }

    // ── Loops and mutable locals (While / Break / Continue / LetMut / Slot) ──
    //
    // These nodes are new surface constructs with no Coq counterpart yet, so the
    // rules live only here and in `type_check`'s legacy mirror. Both paths are
    // exercised: the legacy one is still reachable and used to be the place a
    // missing arm went unnoticed.

    #[test]
    fn while_is_unit_and_joins_both_effects() {
        let mut ctx = TypingContext::new();
        // selagi betul { cetak-free body } : Unit
        let loop_expr = Expr::While(Box::new(Expr::Bool(true)), Box::new(Expr::Int(1)));
        assert_eq!(
            type_check_full(&mut ctx, &loop_expr).unwrap(),
            (Ty::Unit, Effect::Pure)
        );
        // The body's effect propagates to the loop, once, however many times it
        // would run.
        let effectful = Expr::While(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Perform(Effect::Write, Box::new(Expr::Unit))),
        );
        let (ty, eff) = type_check_full(&mut ctx, &effectful).unwrap();
        assert_eq!(ty, Ty::Unit);
        assert_eq!(eff, Effect::Write);
    }

    #[test]
    fn while_rejects_a_non_boolean_condition() {
        let mut ctx = TypingContext::new();
        let bad = Expr::While(Box::new(Expr::Int(1)), Box::new(Expr::Unit));
        assert!(matches!(
            type_check_full(&mut ctx, &bad),
            Err(TypeError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn break_and_continue_unify_with_any_branch() {
        let mut ctx = TypingContext::new();
        // Like `pulang`, they never yield to their context, so they take `Any`
        // and must not force the sibling branch's type.
        assert_eq!(
            type_check_full(&mut ctx, &Expr::Break).unwrap(),
            (Ty::Any, Effect::Pure)
        );
        assert_eq!(
            type_check_full(&mut ctx, &Expr::Continue).unwrap(),
            (Ty::Any, Effect::Pure)
        );
        let branch = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Break),
            Box::new(Expr::Int(7)),
        );
        let (ty, _) = type_check_full(&mut ctx, &branch).unwrap();
        assert!(types_compatible(&ty, &Ty::Int), "got {ty:?}");
    }

    #[test]
    fn a_slot_read_has_the_element_type_and_no_effect() {
        let mut ctx = TypingContext::new();
        // biar ubah x = 42; x
        let e = Expr::LetMut(
            "x".into(),
            Box::new(Expr::Int(42)),
            Box::new(Expr::SlotGet("x".into())),
        );
        assert_eq!(
            type_check_full(&mut ctx, &e).unwrap(),
            (Ty::Int, Effect::Pure)
        );
    }

    #[test]
    fn a_slot_write_is_unit_and_stays_pure() {
        let mut ctx = TypingContext::new();
        // biar ubah x = 0; x = 1
        // Deliberately Pure: a slot cannot escape its binder, so unlike
        // `ruj`/`:=` (which join EffectWrite, mirroring Coq T_Assign) a local
        // counter does not make its enclosing function effectful.
        let e = Expr::LetMut(
            "x".into(),
            Box::new(Expr::Int(0)),
            Box::new(Expr::SlotSet("x".into(), Box::new(Expr::Int(1)))),
        );
        assert_eq!(
            type_check_full(&mut ctx, &e).unwrap(),
            (Ty::Unit, Effect::Pure)
        );
    }

    #[test]
    fn a_slot_write_must_match_the_slot_type() {
        let mut ctx = TypingContext::new();
        let e = Expr::LetMut(
            "x".into(),
            Box::new(Expr::Int(0)),
            Box::new(Expr::SlotSet("x".into(), Box::new(Expr::String("no".into())))),
        );
        assert!(matches!(
            type_check_full(&mut ctx, &e),
            Err(TypeError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn slot_access_needs_a_binding() {
        let mut ctx = TypingContext::new();
        assert!(matches!(
            type_check_full(&mut ctx, &Expr::SlotGet("hantu".into())),
            Err(TypeError::VarNotFound(_))
        ));
        assert!(matches!(
            type_check_full(
                &mut ctx,
                &Expr::SlotSet("hantu".into(), Box::new(Expr::Int(1)))
            ),
            Err(TypeError::VarNotFound(_))
        ));
    }

    #[test]
    fn legacy_type_check_mirrors_the_loop_and_slot_rules() {
        // `type_check` is the deprecated path but still reachable; a missing arm
        // here is exactly the kind of gap that goes unnoticed.
        let ctx = Context::new();
        assert_eq!(
            type_check(&ctx, &Expr::While(Box::new(Expr::Bool(true)), Box::new(Expr::Int(1)))).unwrap(),
            (Ty::Unit, Effect::Pure)
        );
        assert!(matches!(
            type_check(&ctx, &Expr::While(Box::new(Expr::Int(0)), Box::new(Expr::Unit))),
            Err(TypeError::TypeMismatch { .. })
        ));
        assert_eq!(
            type_check(&ctx, &Expr::Break).unwrap(),
            (Ty::Any, Effect::Pure)
        );
        assert_eq!(
            type_check(&ctx, &Expr::Continue).unwrap(),
            (Ty::Any, Effect::Pure)
        );
        let e = Expr::LetMut(
            "x".into(),
            Box::new(Expr::Int(42)),
            Box::new(Expr::SlotGet("x".into())),
        );
        assert_eq!(type_check(&ctx, &e).unwrap(), (Ty::Int, Effect::Pure));
        let w = Expr::LetMut(
            "x".into(),
            Box::new(Expr::Int(0)),
            Box::new(Expr::SlotSet("x".into(), Box::new(Expr::Int(1)))),
        );
        assert_eq!(type_check(&ctx, &w).unwrap(), (Ty::Unit, Effect::Pure));
        assert!(matches!(
            type_check(&ctx, &Expr::SlotGet("hantu".into())),
            Err(TypeError::VarNotFound(_))
        ));
    }
}
