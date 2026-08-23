// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Whole-program RIINA frontend checks shared by CLI, LSP, and WASM.
//!
//! This keeps all shipped user-facing surfaces on the same parser-to-checker
//! path, including program-level effect and capability validation that cannot
//! be expressed by expression typing alone.

use crate::{
    register_builtin_types, type_check_full, types_compatible, Context, TypeError, TypingContext,
};
use riina_types::{Effect, Expr, Program, TopLevelDecl, Ty};
use std::collections::{HashMap, HashSet};

fn builtin_typing_context() -> TypingContext {
    register_builtin_types(&Context::new()).to_typing_context()
}

/// The declared type of a function, re-exported from `riina_types` so the
/// typechecker and desugaring cannot disagree about arity (they did: this used
/// to compute a bare return type for a zero-parameter function while
/// desugaring built a `Unit -> R` lambda, so every zero-arg call failed to
/// type-check).
use riina_types::declared_fn_ty as declared_function_type;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ExecSummary {
    required: HashSet<Effect>,
    grants: HashSet<Effect>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CallableSummary {
    remaining_arity: usize,
    required: HashSet<Effect>,
    grants: HashSet<Effect>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ExprSummary {
    exec: ExecSummary,
    callable: Option<CallableSummary>,
}

type CapabilityEnv = HashMap<String, CallableSummary>;

fn compose_exec(first: &ExecSummary, second: &ExecSummary) -> ExecSummary {
    let mut required = first.required.clone();
    for eff in &second.required {
        if !first.grants.contains(eff) {
            required.insert(*eff);
        }
    }

    let mut grants = first.grants.clone();
    grants.extend(second.grants.iter().copied());

    ExecSummary { required, grants }
}

fn shadow_callable(env: &CapabilityEnv, name: &str) -> CapabilityEnv {
    let mut shadowed = env.clone();
    shadowed.remove(name);
    shadowed
}

fn summarize_lambda(expr: &Expr, env: &CapabilityEnv) -> CallableSummary {
    let mut remaining_arity = 0usize;
    let mut body = expr;
    let mut body_env = env.clone();

    while let Expr::Lam(param, _ty, inner) = body {
        body_env.remove(param);
        remaining_arity += 1;
        body = inner;
    }

    let body_summary = summarize_expr(body, &body_env);
    CallableSummary {
        remaining_arity,
        required: body_summary.exec.required,
        grants: body_summary.exec.grants,
    }
}

fn summarize_seq(left: &Expr, right: &Expr, env: &CapabilityEnv) -> ExprSummary {
    let left_summary = summarize_expr(left, env);
    let right_summary = summarize_expr(right, env);

    ExprSummary {
        exec: compose_exec(&left_summary.exec, &right_summary.exec),
        callable: None,
    }
}

fn summarize_branching(
    guard: &Expr,
    left: &Expr,
    right: &Expr,
    left_env: &CapabilityEnv,
    right_env: &CapabilityEnv,
) -> ExprSummary {
    let guard_summary = summarize_expr(guard, left_env);
    let left_summary = summarize_expr(left, left_env);
    let right_summary = summarize_expr(right, right_env);

    let mut required = guard_summary.exec.required.clone();
    for eff in &left_summary.exec.required {
        if !guard_summary.exec.grants.contains(eff) {
            required.insert(*eff);
        }
    }
    for eff in &right_summary.exec.required {
        if !guard_summary.exec.grants.contains(eff) {
            required.insert(*eff);
        }
    }

    let grants = left_summary
        .exec
        .grants
        .intersection(&right_summary.exec.grants)
        .copied()
        .collect::<HashSet<_>>();
    let mut grants_after = guard_summary.exec.grants.clone();
    grants_after.extend(grants);

    ExprSummary {
        exec: ExecSummary {
            required,
            grants: grants_after,
        },
        callable: None,
    }
}

fn summarize_expr(expr: &Expr, env: &CapabilityEnv) -> ExprSummary {
    match expr {
        Expr::Unit
        | Expr::Bool(_)
        | Expr::Int(_)
        | Expr::IntN { .. }
        | Expr::String(_)
        | Expr::Loc(_) => ExprSummary::default(),
        Expr::Var(name) => match env.get(name) {
            Some(callable) if callable.remaining_arity == 0 => ExprSummary {
                exec: ExecSummary {
                    required: callable.required.clone(),
                    grants: callable.grants.clone(),
                },
                callable: None,
            },
            Some(callable) => ExprSummary {
                exec: ExecSummary::default(),
                callable: Some(callable.clone()),
            },
            None => ExprSummary::default(),
        },
        Expr::Lam(_, _, _) => ExprSummary {
            exec: ExecSummary::default(),
            callable: Some(summarize_lambda(expr, env)),
        },
        Expr::App(fun, arg) => {
            let fun_summary = summarize_expr(fun, env);
            let arg_summary = summarize_expr(arg, env);
            let mut exec = compose_exec(&fun_summary.exec, &arg_summary.exec);
            let callable = match fun_summary.callable {
                Some(callable) if callable.remaining_arity == 1 => {
                    exec = compose_exec(
                        &exec,
                        &ExecSummary {
                            required: callable.required,
                            grants: callable.grants,
                        },
                    );
                    None
                }
                Some(mut callable) if callable.remaining_arity > 1 => {
                    callable.remaining_arity -= 1;
                    Some(callable)
                }
                _ => None,
            };

            ExprSummary { exec, callable }
        }
        Expr::Pair(left, right) | Expr::Assign(left, right) | Expr::BinOp(_, left, right) => {
            summarize_seq(left, right, env)
        }
        Expr::Fst(inner)
        | Expr::Snd(inner)
        | Expr::Ref(inner, _)
        | Expr::Deref(inner)
        | Expr::Classify(inner)
        | Expr::Prove(inner)
        | Expr::Perform(_, inner)
        | Expr::Return(inner)
        | Expr::ContractDeploy(inner)
        | Expr::ZakatCalculate(inner) => ExprSummary {
            exec: summarize_expr(inner, env).exec,
            callable: None,
        },
        Expr::Inl(inner, _) | Expr::Inr(inner, _) => ExprSummary {
            exec: summarize_expr(inner, env).exec,
            callable: None,
        },
        Expr::Case(sum, left_name, left_body, right_name, right_body) => summarize_branching(
            sum,
            left_body,
            right_body,
            &shadow_callable(env, left_name),
            &shadow_callable(env, right_name),
        ),
        Expr::If(cond, then_branch, else_branch) => {
            summarize_branching(cond, then_branch, else_branch, env, env)
        }
        // A loop's capability demand is its condition's plus its body's — a loop
        // requires nothing a single pass would not, only possibly more often.
        Expr::While(cond, body) => ExprSummary {
            exec: summarize_seq(cond, body, env).exec,
            callable: None,
        },
        Expr::Break | Expr::Continue => ExprSummary::default(),
        Expr::SlotGet(_) => ExprSummary::default(),
        Expr::SlotSet(_, value) => ExprSummary {
            exec: summarize_expr(value, env).exec,
            callable: None,
        },
        Expr::LetMut(name, value, body) => {
            let value_summary = summarize_expr(value, env);
            let body_summary = summarize_expr(body, &shadow_callable(env, name));
            ExprSummary {
                exec: compose_exec(&value_summary.exec, &body_summary.exec),
                callable: body_summary.callable,
            }
        }
        Expr::Let(name, _, value, body) => {
            let value_summary = summarize_expr(value, env);
            let mut body_env = shadow_callable(env, name);
            if let Some(callable) = value_summary.callable.clone() {
                body_env.insert(name.clone(), callable);
            }
            let body_summary = summarize_expr(body, &body_env);

            ExprSummary {
                exec: compose_exec(&value_summary.exec, &body_summary.exec),
                callable: body_summary.callable,
            }
        }
        Expr::Handle(handled, name, handler) => {
            let handled_summary = summarize_expr(handled, env);
            let handler_summary = summarize_expr(handler, &shadow_callable(env, name));
            let mut required = handled_summary.exec.required.clone();
            for eff in &handler_summary.exec.required {
                if !handled_summary.exec.grants.contains(eff) {
                    required.insert(*eff);
                }
            }

            ExprSummary {
                exec: ExecSummary {
                    required,
                    grants: handled_summary.exec.grants,
                },
                callable: None,
            }
        }
        Expr::Declassify(secret, proof) => {
            let secret_summary = summarize_expr(secret, env);
            let proof_summary = summarize_expr(proof, env);

            ExprSummary {
                exec: compose_exec(&secret_summary.exec, &proof_summary.exec),
                callable: None,
            }
        }
        Expr::Require(effect, body) => {
            let body_summary = summarize_expr(body, env);
            let mut required = body_summary.exec.required.clone();
            required.insert(*effect);

            ExprSummary {
                exec: ExecSummary {
                    required,
                    grants: body_summary.exec.grants,
                },
                callable: body_summary.callable,
            }
        }
        Expr::Grant(effect, body) => {
            let body_summary = summarize_expr(body, env);
            let mut required = body_summary.exec.required.clone();
            required.remove(effect);

            let mut grants = body_summary.exec.grants.clone();
            grants.insert(*effect);

            ExprSummary {
                exec: ExecSummary { required, grants },
                callable: body_summary.callable,
            }
        }
        Expr::LetRec(name, _ty, value, body) => {
            let value_summary = summarize_expr(value, env);
            let mut body_env = shadow_callable(env, name);
            if let Some(callable) = value_summary.callable.clone() {
                body_env.insert(name.clone(), callable);
            }
            let body_summary = summarize_expr(body, &body_env);

            ExprSummary {
                exec: compose_exec(&value_summary.exec, &body_summary.exec),
                callable: body_summary.callable,
            }
        }
        Expr::LetRecGroup(bindings, body) => {
            // Capability summary of a mutually-recursive group equals that of the
            // equivalent nested LetRec chain — reuse the LetRec logic (REQ-44).
            let mut chain = (**body).clone();
            for (name, ty, value) in bindings.iter().rev() {
                chain = Expr::LetRec(
                    name.clone(),
                    ty.clone(),
                    Box::new(value.clone()),
                    Box::new(chain),
                );
            }
            summarize_expr(&chain, env)
        }
        Expr::FFICall { .. } => ExprSummary::default(),
        Expr::ActorDecl { .. }
        | Expr::ChoreographyBlock { .. }
        | Expr::Spawn(_, _)
        | Expr::ActorSend(_, _)
        | Expr::ActorRecv(_)
        | Expr::CRDTMerge(_, _)
        | Expr::ContentHash(_)
        | Expr::ContentVerify(_, _) => ExprSummary::default(),
        Expr::TokenTransfer { from, to, amount } => {
            let from_summary = summarize_expr(from, env);
            let to_summary = summarize_expr(to, env);
            let amount_summary = summarize_expr(amount, env);
            ExprSummary {
                exec: compose_exec(
                    &compose_exec(&from_summary.exec, &to_summary.exec),
                    &amount_summary.exec,
                ),
                callable: None,
            }
        }
        // CAHAYA Phase J5
        // Field access summarizes its base expression.
        Expr::FieldAccess(base, _) => summarize_expr(base, env),
        // Record literals and list literals carry no capability requirements of
        // their own (element/field summaries are conservatively ignored, as for
        // the UI/collection group).
        Expr::RecordLit(_, _)
        | Expr::ListLit(_)
        | Expr::UIDisplay(_)
        | Expr::UIRow(_)
        | Expr::UIColumn(_)
        | Expr::UIText(_, _)
        | Expr::UIButton(_, _)
        | Expr::UIColor(_, _, _)
        | Expr::UIStyleDecl { .. }
        | Expr::UIContrastCheck(_, _) => ExprSummary::default(),
    }
}

fn summarize_function(
    name: &str,
    params: &[(String, Ty)],
    body: &Expr,
    env: &CapabilityEnv,
) -> CallableSummary {
    let mut summary = CallableSummary {
        remaining_arity: params.len(),
        required: HashSet::new(),
        grants: HashSet::new(),
    };

    loop {
        let mut body_env = env.clone();
        body_env.insert(name.to_string(), summary.clone());
        for (param_name, _) in params {
            body_env.remove(param_name);
        }

        let body_summary = summarize_expr(body, &body_env);
        let next = CallableSummary {
            remaining_arity: params.len(),
            required: body_summary.exec.required,
            grants: body_summary.exec.grants,
        };

        if next == summary {
            return next;
        }

        summary = next;
    }
}

fn first_required_capability(required: &HashSet<Effect>) -> Option<Effect> {
    required.iter().copied().min_by_key(|effect| effect.level())
}

fn validate_capabilities(program: &Program) -> Result<(), TypeError> {
    let mut env = CapabilityEnv::new();
    let mut program_exec = ExecSummary::default();

    for decl in &program.decls {
        match decl {
            TopLevelDecl::Function {
                name, params, body, ..
            } => {
                let summary = summarize_function(name, params, body, &env);
                env.insert(name.clone(), summary);
            }
            TopLevelDecl::Binding { name, value, .. } => {
                let value_summary = summarize_expr(value, &env);
                program_exec = compose_exec(&program_exec, &value_summary.exec);

                env.remove(name);
                if let Some(callable) = value_summary.callable {
                    env.insert(name.clone(), callable);
                }
            }
            TopLevelDecl::ExternBlock { decls, .. } => {
                for decl in decls {
                    env.insert(
                        decl.name.clone(),
                        CallableSummary {
                            remaining_arity: decl.params.len(),
                            required: HashSet::new(),
                            grants: HashSet::new(),
                        },
                    );
                }
            }
            TopLevelDecl::Expr(expr) => {
                let expr_summary = summarize_expr(expr, &env);
                program_exec = compose_exec(&program_exec, &expr_summary.exec);
            }
            TopLevelDecl::Test { .. } => {}
        }
    }

    if let Some(required) = first_required_capability(&program_exec.required) {
        return Err(TypeError::CapabilityViolation {
            required,
            message: format!(
                "compile-time capability analysis found '{}' without a prior or enclosing 'beri {:?}'",
                match required {
                    Effect::Pure => "perlu Bersih",
                    Effect::Read => "perlu Baca",
                    Effect::Write => "perlu Tulis",
                    Effect::Mut => "perlu Ubah",
                    Effect::Alloc => "perlu Alok",
                    Effect::FileSystem => "perlu SistemFail",
                    Effect::Network => "perlu Rangkaian",
                    Effect::NetworkSecure => "perlu RangkaianSelamat",
                    Effect::Crypto => "perlu Kripto",
                    Effect::Random => "perlu Rawak",
                    Effect::System => "perlu Sistem",
                    Effect::Time => "perlu Masa",
                    Effect::Process => "perlu Proses",
                    Effect::Panel => "perlu Panel",
                    Effect::Zirah => "perlu Zirah",
                    Effect::Benteng => "perlu Benteng",
                    Effect::Sandi => "perlu Sandi",
                    Effect::Menara => "perlu Menara",
                    Effect::Gapura => "perlu Gapura",
                },
                required
            ),
        });
    }

    Ok(())
}

fn validate_top_level_decls(program: &Program) -> Result<(), TypeError> {
    // Pass 1 (REQ-44 forward references): pre-collect EVERY top-level function
    // signature, extern decl, and actor name so a body can reference a callable
    // defined later in the file (the natural top-down style + modules). Recursion
    // soundness is mechanized in `foundations/RecursionSafety.v`; the effect ≤
    // declared discipline and return-type compatibility are still enforced
    // per-body in pass 2, so pre-binding signatures never falsely accepts.
    let mut ctx = builtin_typing_context();
    for decl in &program.decls {
        match decl {
            TopLevelDecl::Function {
                name,
                params,
                return_ty,
                effect,
                ..
            } => {
                let fn_ty = declared_function_type(params, return_ty, *effect);
                ctx = ctx.extend_gamma(name.clone(), fn_ty);
            }
            TopLevelDecl::ExternBlock { decls, .. } => {
                for d in decls {
                    let fn_ty = declared_function_type(&d.params, &d.ret_ty, d.effect);
                    ctx = ctx.extend_gamma(d.name.clone(), fn_ty);
                }
            }
            TopLevelDecl::Expr(e) => {
                if let Expr::ActorDecl {
                    name,
                    state_ty,
                    message_ty,
                    ..
                } = e.as_ref()
                {
                    let actor_ty =
                        Ty::Actor(Box::new(state_ty.clone()), Box::new(message_ty.clone()));
                    ctx = ctx.extend_gamma(name.clone(), actor_ty);
                }
            }
            _ => {}
        }
    }

    // Pass 2: check each body/binding with all signatures already in scope.
    for decl in &program.decls {
        match decl {
            TopLevelDecl::Function {
                params,
                return_ty,
                effect,
                effect_set,
                body,
                ..
            } => {
                // Signature already bound in pass 1 (forward refs); just add params.
                let mut body_ctx = ctx.clone();
                for (param_name, param_ty) in params {
                    body_ctx = body_ctx.extend_gamma(param_name.clone(), param_ty.clone());
                }
                // The function's declared effect grants capabilities within its
                // body (a function with `kesan Rangkaian` can use `require
                // Rangkaian`). Grant *every* declared component, not just the
                // lossy lattice join: a compound `kesan (A, B, C)` grants all of
                // A, B, C, which is what makes capability-gating sound for
                // compound-effect functions.
                for e in effect_set {
                    body_ctx = body_ctx.with_grant(*e);
                }

                let (body_ty, body_eff) = type_check_full(&mut body_ctx, body)?;
                if !types_compatible(return_ty, &body_ty) {
                    return Err(TypeError::AnnotationMismatch {
                        expected: return_ty.clone(),
                        found: body_ty,
                    });
                }
                if body_eff.level() > effect.level() {
                    return Err(TypeError::EffectViolation {
                        allowed: *effect,
                        found: body_eff,
                    });
                }
                // Signature already in ctx from pass 1.
            }
            TopLevelDecl::Binding { name, value, is_mut } => {
                let mut binding_ctx = ctx.clone();
                let (ty, eff) = type_check_full(&mut binding_ctx, value)?;
                // Top-level bindings: reject side effects except actor operations
                if eff.level() > Effect::Pure.level()
                    && eff != Effect::Process
                    && eff != Effect::Network
                {
                    return Err(TypeError::EffectViolation {
                        allowed: Effect::Pure,
                        found: eff,
                    });
                }
                // A `biar ubah` top-level binding is a mutable SLOT, so it is
                // recorded at the slot's type (`Ref`) — that is what
                // `SlotGet`/`SlotSet` look for. Without this a top-level
                // counter would not type-check against its own writes.
                ctx = if *is_mut {
                    ctx.extend_gamma(name.clone(), Ty::Ref(Box::new(ty), riina_types::SecurityLevel::Public))
                } else {
                    ctx.extend_gamma(name.clone(), ty)
                };
            }
            TopLevelDecl::ExternBlock { decls, .. } => {
                for decl in decls {
                    let fn_ty = declared_function_type(&decl.params, &decl.ret_ty, decl.effect);
                    ctx = ctx.extend_gamma(decl.name.clone(), fn_ty);
                }
            }
            TopLevelDecl::Expr(e) => {
                // Actor declarations bind the actor name in the type context
                if let Expr::ActorDecl {
                    name,
                    state_ty,
                    message_ty,
                    ..
                } = e.as_ref()
                {
                    let actor_ty =
                        Ty::Actor(Box::new(state_ty.clone()), Box::new(message_ty.clone()));
                    ctx = ctx.extend_gamma(name.clone(), actor_ty);
                }
            }
            TopLevelDecl::Test { .. } => {}
        }
    }

    validate_capabilities(program)?;

    Ok(())
}

pub fn check_program(program: &Program) -> Result<(Expr, Ty, Effect), TypeError> {
    validate_top_level_decls(program)?;
    let expr = program.clone().desugar();

    // Seed the capability grants with EVERY effect declared by a top-level
    // function (REQ-77).
    //
    // Why this is needed: `Expr::LetRecGroup` recovers grants from each
    // binding's `Ty::Fn(_, _, eff)` annotation, but a ZERO-PARAMETER function
    // (`fungsi utama() -> Nombor kesan Rangkaian`) desugars to its bare return
    // type, not a `Ty::Fn`, so its declared effect is invisible there. The
    // capability gate is opt-in on "granted set non-empty", so a program whose
    // `utama` is zero-arg and which has ANY other function had the gate
    // switched on by that other function while `utama`'s own effect was
    // missing — rejecting a correct program with
    // `Capability violation for Network`. A single-function program happened to
    // work only because nothing switched the gate on.
    //
    // Over-granting here is the documented design of the LetRecGroup rule: the
    // real per-function discipline (body effect <= declared effect, with only
    // that function's own components granted) is enforced above in
    // `validate_top_level_decls`, so this admits more programs without ever
    // weakening a function's own check.
    let mut ctx = builtin_typing_context();
    for decl in &program.decls {
        if let TopLevelDecl::Function { effect_set, .. } = decl {
            for e in effect_set {
                ctx = ctx.with_grant(*e);
            }
        }
    }
    let (ty, eff) = type_check_full(&mut ctx, &expr)?;
    Ok((expr, ty, eff))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TypeError;
    use riina_parser::Parser;
    use riina_types::SecurityLevel;

    fn parse_program(source: &str) -> Program {
        let mut parser = Parser::new(source);
        parser.parse_program().expect("program should parse")
    }

    /// REQ-77 regression: a ZERO-PARAMETER `utama` declaring a gated effect
    /// desugars to a bare return type, not a `Ty::Fn`, so `LetRecGroup` cannot
    /// see its declared effect. Any OTHER top-level function then switched the
    /// opt-in capability gate on with `utama`'s own effect missing, rejecting a
    /// correct program with `Capability violation for Network`. A one-function
    /// program happened to pass only because nothing switched the gate on.
    #[test]
    fn zero_arg_main_keeps_its_own_capability_alongside_other_functions() {
        let src = "fungsi bantu(x: Nombor) -> Nombor kesan Bersih { x }\n\
                   fungsi utama() -> Nombor kesan Rangkaian { biar l = jaring_dengar(\"127.0.0.1:1\"); 0 }";
        assert!(
            check_program(&parse_program(src)).is_ok(),
            "a zero-arg networked `utama` must keep its Network capability when \
             another function is present"
        );
    }

    /// The fix must not disable the gate: a Network operation inside a function
    /// that does NOT declare it is still rejected.
    #[test]
    fn ungranted_network_operation_is_still_rejected() {
        let src = "fungsi bantu(x: Nombor) -> Nombor kesan Bersih { x }\n\
                   fungsi utama() -> Nombor kesan Bersih { biar l = jaring_dengar(\"127.0.0.1:1\"); 0 }";
        assert!(
            check_program(&parse_program(src)).is_err(),
            "a Network op in a `kesan Bersih` function must still be rejected"
        );
    }

    #[test]
    fn check_program_allows_forward_reference() {
        // REQ-44: a function may call one defined LATER in the file (utama calls
        // bantu; bantu is declared after). Single-pass checking rejected this.
        let src = "fungsi utama() -> Nombor kesan Bersih { biar x = bantu(5); x }\n                   fungsi bantu(n: Nombor) -> Nombor kesan Bersih { pulang n + 1; }";
        assert!(check_program(&parse_program(src)).is_ok(), "forward reference must typecheck");
    }

    #[test]
    fn check_program_allows_mutual_recursion() {
        // REQ-44: genap/ganjil are mutually recursive; each references the other.
        let src = "fungsi genap(n: Nombor) -> Benar kesan Bersih { kalau n == 0 { betul } lain { ganjil(n - 1) } }\n                   fungsi ganjil(n: Nombor) -> Benar kesan Bersih { kalau n == 0 { salah } lain { genap(n - 1) } }\n                   fungsi utama() -> Benar kesan Bersih { genap(10) }";
        assert!(check_program(&parse_program(src)).is_ok(), "mutual recursion must typecheck");
    }

    #[test]
    fn check_program_still_rejects_undefined_name() {
        // Forward references must NOT weaken scoping: a genuinely-undefined name
        // is still rejected.
        let src = "fungsi utama() -> Nombor kesan Bersih { tiada_fungsi_sebegini(1) }";
        assert!(check_program(&parse_program(src)).is_err(), "undefined name must still be rejected");
    }

    #[test]
    fn check_program_rejects_secret_deref_in_public_context() {
        let err = check_program(&parse_program("!ref 42 @ Secret")).unwrap_err();
        match err {
            TypeError::SecurityViolation {
                found,
                expected,
                context,
            } => {
                assert_eq!(found, SecurityLevel::Secret);
                assert_eq!(expected, SecurityLevel::Public);
                assert_eq!(context, "dereference");
            }
            other => panic!("expected SecurityViolation, got {other:?}"),
        }
    }

    #[test]
    fn check_program_rejects_invalid_declassification_proof() {
        let err = check_program(&parse_program(
            "declassify classify 42 with prove classify 7",
        ))
        .unwrap_err();
        match err {
            TypeError::InvalidDeclassification { .. } => {}
            other => panic!("expected InvalidDeclassification, got {other:?}"),
        }
    }

    #[test]
    fn check_program_rejects_zero_arg_pure_function_with_write_effect() {
        // `print`/`cetak` carry the Write effect, so using one inside a `kesan
        // Bersih` (pure) function is an effect violation.
        let err = check_program(&parse_program(
            "fungsi bocor() -> Unit kesan Bersih { print 1 }",
        ))
        .unwrap_err();
        match err {
            TypeError::EffectViolation { allowed, found } => {
                assert_eq!(allowed, Effect::Pure);
                assert_eq!(found, Effect::Write);
            }
            other => panic!("expected EffectViolation, got {other:?}"),
        }
    }

    #[test]
    fn check_program_rejects_missing_top_level_capability() {
        let err = check_program(&parse_program("require Rangkaian 1")).unwrap_err();
        match err {
            TypeError::CapabilityViolation { required, .. } => {
                assert_eq!(required, Effect::Network);
            }
            other => panic!("expected CapabilityViolation, got {other:?}"),
        }
    }

    #[test]
    fn check_program_allows_granted_top_level_capability() {
        check_program(&parse_program("grant Rangkaian require Rangkaian 1"))
            .expect("matching grant should satisfy top-level capability");
    }

    #[test]
    fn check_program_rejects_zero_arg_function_call_without_grant() {
        let err = check_program(&parse_program(
            "fungsi perlu_rangkaian() -> Nombor kesan Rangkaian { require Rangkaian 1 }\nperlu_rangkaian()",
        ))
        .unwrap_err();
        match err {
            TypeError::CapabilityViolation { required, .. } => {
                assert_eq!(required, Effect::Network);
            }
            other => panic!("expected CapabilityViolation, got {other:?}"),
        }
    }

    #[test]
    fn check_program_allows_function_call_after_grant() {
        check_program(&parse_program(
            "fungsi perlu_rangkaian(x: Nombor) -> Nombor kesan Rangkaian { require Rangkaian x }\ngrant Rangkaian perlu_rangkaian(1)",
        ))
        .expect("grant should authorize capability-gated function call");
    }

    #[test]
    fn check_program_allows_zero_arg_function_call_after_grant() {
        check_program(&parse_program(
            "fungsi perlu_rangkaian() -> Nombor kesan Rangkaian { require Rangkaian 1 }\ngrant Rangkaian perlu_rangkaian()",
        ))
        .expect("grant should authorize zero-arg capability-gated function call");
    }

    #[test]
    fn check_program_tracks_prior_grants_across_bindings() {
        check_program(&parse_program(
            "biar tiket = grant Rangkaian 0;\nfungsi perlu_rangkaian() -> Nombor kesan Rangkaian { require Rangkaian 1 }\nperlu_rangkaian()",
        ))
        .expect("prior top-level grant should satisfy later capability-gated call");
    }

    // ── Effect Gate parity (Coq effect-soundness: a term's evaluation performs
    // only effects in its declared set). `EffectViolation` has two distinct
    // enforcement sites; the function-effect-discipline site is covered by
    // `check_program_rejects_zero_arg_pure_function_with_write_effect`, but the
    // *top-level binding purity* site (module-level `biar` must be pure — no
    // declared-effect annotation exists for bindings) was untested.
    #[test]
    fn check_program_rejects_effectful_top_level_binding() {
        // A module-level binding whose initializer carries the Write effect
        // (`print`) must be rejected — module initialization is implicitly pure.
        let err = check_program(&parse_program("biar bocor = print 1;\nbocor")).unwrap_err();
        match err {
            TypeError::EffectViolation { allowed, found } => {
                assert_eq!(allowed, Effect::Pure);
                assert_eq!(found, Effect::Write);
            }
            other => panic!("expected EffectViolation for effectful binding, got {other:?}"),
        }
    }

    #[test]
    fn check_program_allows_pure_top_level_binding() {
        // A pure module-level binding is accepted (the purity guard does not fire).
        check_program(&parse_program("biar selamat = 1;\nselamat"))
            .expect("a pure top-level binding must typecheck");
    }

    // ── Effect-set: a compound declared effect grants ALL its components ──
    #[test]
    fn check_program_compound_effect_grants_all_components() {
        // Regression for the effect-set fix: a function declaring `kesan (Rawak,
        // Tulis)` grants BOTH Random and Write, so the capability-gated `rawak`
        // (Effect::Random) call inside it is authorized. Before the fix the
        // compound collapsed to a single effect and this was a false-positive
        // CapabilityViolation.
        check_program(&parse_program(
            "fungsi hitung() -> Nombor kesan (Rawak, Tulis) { random(10) }\nhitung()",
        ))
        .expect("a compound-effect function may call its declared ambient op");
    }

    // ── Numeric tower: distinct sized integer types ──
    #[test]
    fn check_program_sized_int_function_typechecks() {
        // A function with a sized-integer (u8) parameter and return type
        // type-checks; a plain integer literal is an accepted argument
        // (IntN ↔ Int compatibility), and the program's type is the sized type.
        let (_, ty, _) =
            check_program(&parse_program("fungsi id8(x: u8) -> u8 { x }\nid8(5)")).unwrap();
        assert_eq!(ty, riina_types::Ty::IntN { bits: 8, signed: false });
    }

    #[test]
    fn check_program_distinct_int_widths_are_incompatible() {
        // u8 and u16 are *distinct* types — a u8 body cannot satisfy a u16 return.
        let err =
            check_program(&parse_program("fungsi bad(x: u8) -> u16 { x }\nbad(5)")).unwrap_err();
        assert!(matches!(err, TypeError::AnnotationMismatch { .. }));
    }
}
