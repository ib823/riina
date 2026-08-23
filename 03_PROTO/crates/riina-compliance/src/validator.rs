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
        Expr::Unit
        | Expr::Bool(_)
        | Expr::Int(_)
        | Expr::IntN { .. }
        | Expr::String(_)
        | Expr::Var(_)
        | Expr::SlotGet(_)
        | Expr::Break
        | Expr::Continue
        | Expr::Loc(_) => {}

        Expr::Lam(_, _, body)
        | Expr::Fst(body)
        | Expr::Snd(body)
        | Expr::Inl(body, _)
        | Expr::Inr(body, _)
        | Expr::Ref(body, _)
        | Expr::Deref(body)
        | Expr::Classify(body)
        | Expr::Prove(body)
        | Expr::Return(body)
        | Expr::Require(_, body)
        | Expr::Grant(_, body)
        | Expr::SlotSet(_, body)
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

        Expr::Let(_, _, v, b)
        | Expr::LetMut(_, v, b)
        | Expr::While(v, b)
        | Expr::LetRec(_, _, v, b)
        | Expr::Handle(v, _, b) => {
            walk_inner(v, rules, out);
            walk_inner(b, rules, out);
        }

        Expr::LetRecGroup(bindings, cont) => {
            // REQ-44: many rules are written as `if let Expr::LetRec(name, ..)`
            // to fire once per named function. Top-level functions are now
            // GROUP members, so those rules would silently never fire again.
            // Re-present each member as the equivalent single-binding LetRec so
            // every existing per-function rule keeps working unchanged — and so
            // future rules can keep being written against LetRec.
            for (name, ty, e) in bindings {
                let as_letrec = Expr::LetRec(
                    name.clone(),
                    ty.clone(),
                    Box::new(e.clone()),
                    Box::new(Expr::Unit),
                );
                for rule in rules.iter() {
                    if let Some(v) = (rule.check)(&as_letrec) {
                        out.push(v);
                    }
                }
                walk_inner(e, rules, out);
            }
            walk_inner(cont, rules, out);
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

        // JALINAN Phase 6: recurse into sub-expressions so compliance rules
        // apply inside actor / content-addressed constructs (previously an
        // unfinished stub that panicked on these variants).
        Expr::ActorDecl {
            init_state, handler, ..
        } => {
            walk_inner(init_state, rules, out);
            walk_inner(handler, rules, out);
        }
        // ChoreographyBlock carries only a name, roles, and a SessionType —
        // no value sub-expressions to walk.
        Expr::ChoreographyBlock { .. } => {}
        Expr::Spawn(a, b)
        | Expr::ActorSend(a, b)
        | Expr::CRDTMerge(a, b)
        | Expr::ContentVerify(a, b) => {
            walk_inner(a, rules, out);
            walk_inner(b, rules, out);
        }
        Expr::ActorRecv(e) | Expr::ContentHash(e) => {
            walk_inner(e, rules, out);
        }
        Expr::ContractDeploy(expr) | Expr::ZakatCalculate(expr) => {
            walk_inner(expr, rules, out);
        }
        Expr::TokenTransfer { from, to, amount } => {
            walk_inner(from, rules, out);
            walk_inner(to, rules, out);
            walk_inner(amount, rules, out);
        }

        // CAHAYA Phase J5
        Expr::ListLit(elems)
        | Expr::UIDisplay(elems)
        | Expr::UIRow(elems)
        | Expr::UIColumn(elems) => {
            for e in elems {
                walk_inner(e, rules, out);
            }
        }
        Expr::RecordLit(_, fields) => {
            for (_f, e) in fields {
                walk_inner(e, rules, out);
            }
        }
        Expr::FieldAccess(base, _) => walk_inner(base, rules, out),
        Expr::UIText(a, b) | Expr::UIButton(a, b) | Expr::UIContrastCheck(a, b) => {
            walk_inner(a, rules, out);
            walk_inner(b, rules, out);
        }
        Expr::UIColor(_, _, _) | Expr::UIStyleDecl { .. } => {}
    }
}
