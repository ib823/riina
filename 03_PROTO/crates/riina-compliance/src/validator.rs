// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! AST walker for compliance validation.

use riina_types::Expr;

use crate::rules::ComplianceRule;
use crate::ComplianceViolation;

/// Walk the expression tree, applying each rule at every node.
pub fn walk(expr: &Expr, rules: &[ComplianceRule]) -> Vec<ComplianceViolation> {
    let mut violations = Vec::new();
    walk_inner(expr, rules, &mut violations);
    violations
}

fn walk_inner(expr: &Expr, rules: &[ComplianceRule], out: &mut Vec<ComplianceViolation>) {
    // Apply all rules to the current node
    for rule in rules {
        if let Some(v) = (rule.check)(expr) {
            out.push(v);
        }
    }

    // Recurse into children
    match expr {
        Expr::Unit | Expr::Bool(_) | Expr::Int(_) | Expr::String(_)
        | Expr::Var(_) | Expr::Loc(_) => {}

        Expr::Lam(_, _, body)
        | Expr::Fst(body)
        | Expr::Snd(body)
        | Expr::Inl(body, _)
        | Expr::Inr(body, _)
        | Expr::Ref(body, _)
        | Expr::Deref(body)
        | Expr::Classify(body)
        | Expr::Prove(body)
        | Expr::Require(_, body)
        | Expr::Grant(_, body)
        | Expr::Perform(_, body) => {
            walk_inner(body, rules, out);
        }

        Expr::App(f, a)
        | Expr::Pair(f, a)
        | Expr::Assign(f, a)
        | Expr::Declassify(f, a)
        | Expr::BinOp(_, f, a) => {
            walk_inner(f, rules, out);
            walk_inner(a, rules, out);
        }

        Expr::Let(_, v, b) | Expr::LetRec(_, _, v, b) | Expr::Handle(v, _, b) => {
            walk_inner(v, rules, out);
            walk_inner(b, rules, out);
        }

        Expr::If(c, t, e) | Expr::Case(c, _, t, _, e) => {
            walk_inner(c, rules, out);
            walk_inner(t, rules, out);
            walk_inner(e, rules, out);
        }

        Expr::FFICall { args, .. } => {
            for arg in args {
                walk_inner(arg, rules, out);
            }
        }
    }
}
